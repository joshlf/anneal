//! Milestone 3: Shared MIR-Guided, Layout-Aware Input & Environment Schedule Generator.
//!
//! Provides:
//! - [`MirInputDictionary`]: extracts `switchInt` branch literals
//!   (`c -> {c.saturating_sub(1), c, c.saturating_add(1)}`), binary comparison/shift
//!   constants, and [`ScalarLayout`] validity bounds (`{0, 1, start, end, MAX - 1, MAX, MIN, -1}`)
//!   from Lean MIR, JSON, and Rust AST sources.
//! - [`LayoutAwareByteBuilder`]: materializes byte buffers for arbitrary [`LayoutSpec`]s
//!   with an 80% dictionary-boundary / 20% uniform [`arbitrary::Unstructured`] bias,
//!   deterministic non-zero padding noise (`0xA5`, `0x5A`, `0xFF`, or seeded non-zero PRNG),
//!   and configurable `validity_fault_rate_pct` (a nonzero rate injects invalid
//!   bit patterns; 0% keeps every value valid).
//! - [`EnvScheduleGenerator`]: synthesizes reactive `inputs-over-time` [`EnvSchedule`]s
//!   per external callee (constant, monotonic counter, alternating `Ok`/`Err`,
//!   dictionary-drawn values, and `PanicOnCall(k)` unwinding injection).
//! - [`MirObsPathSet`]: deduplicates native trace executions by
//!   `(fn_name, branch_tags, ext_call_sequence_shape, is_panic)` and retains the minimal
//!   input byte seed for each distinct execution path.

use std::collections::{BTreeMap, BTreeSet};

use arbitrary::Unstructured;
use syn::visit::{self, Visit};
use syn::{BinOp, Expr, ExprBinary, ExprField, ExprLit, ExprMatch, ExprMethodCall, Lit, Member, Pat};

use crate::instrument::{EnvSchedule, FromScheduleBytes, ScheduleError, TraceRecorder};

/// Bitmask covering the lowest `bit_width` bits (`1..=128`).
#[inline]
pub fn width_mask(bit_width: u32) -> u128 {
    if bit_width >= 128 {
        u128::MAX
    } else if bit_width == 0 {
        0
    } else {
        (1u128 << bit_width) - 1
    }
}

/// Scalar ABI and bit-validity descriptor corresponding to Anneal's `ScalarLayout`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarLayout {
    /// Width of the scalar in bytes (`1`, `2`, `4`, `8`, or `16`).
    pub size_bytes: usize,
    /// Whether the scalar is two's-complement signed.
    pub signed: bool,
    /// Inclusive lower bound of the valid unsigned bit-pattern range.
    pub valid_start: u128,
    /// Inclusive upper bound of the valid unsigned bit-pattern range.
    pub valid_end: u128,
    /// Whether this scalar has Rust `bool` validity (`0` or `1`).
    pub is_bool: bool,
    /// Whether this scalar has Rust `char` validity (`0..=0xD7FF` or `0xE000..=0x10FFFF`).
    pub is_char: bool,
}

impl ScalarLayout {
    /// Unsigned integer layout of `size_bytes` bytes with full bit validity.
    pub fn unsigned(size_bytes: usize) -> Self {
        let bits = (size_bytes * 8) as u32;
        Self {
            size_bytes,
            signed: false,
            valid_start: 0,
            valid_end: width_mask(bits),
            is_bool: false,
            is_char: false,
        }
    }

    /// Signed integer layout of `size_bytes` bytes with full two's-complement validity.
    pub fn signed(size_bytes: usize) -> Self {
        let bits = (size_bytes * 8) as u32;
        Self {
            size_bytes,
            signed: true,
            valid_start: 0,
            valid_end: width_mask(bits),
            is_bool: false,
            is_char: false,
        }
    }

    pub fn u8() -> Self {
        Self::unsigned(1)
    }

    pub fn u16() -> Self {
        Self::unsigned(2)
    }

    pub fn u32() -> Self {
        Self::unsigned(4)
    }

    pub fn u64() -> Self {
        Self::unsigned(8)
    }

    pub fn u128() -> Self {
        Self::unsigned(16)
    }

    pub fn i8() -> Self {
        Self::signed(1)
    }

    pub fn i16() -> Self {
        Self::signed(2)
    }

    pub fn i32() -> Self {
        Self::signed(4)
    }

    pub fn i64() -> Self {
        Self::signed(8)
    }

    pub fn i128() -> Self {
        Self::signed(16)
    }

    /// Rust `bool` layout (1 byte, valid bit patterns `0..=1`).
    pub fn bool_layout() -> Self {
        Self {
            size_bytes: 1,
            signed: false,
            valid_start: 0,
            valid_end: 1,
            is_bool: true,
            is_char: false,
        }
    }

    /// Rust `char` layout (4 bytes, Unicode scalar value excluding UTF-16 surrogates).
    pub fn char_layout() -> Self {
        Self {
            size_bytes: 4,
            signed: false,
            valid_start: 0,
            valid_end: 0x10_FFFF,
            is_bool: false,
            is_char: true,
        }
    }

    /// Scalar with an explicit inclusive validity sub-range (e.g. `NonZeroU32` = `1..=u32::MAX`).
    pub fn with_valid_range(
        size_bytes: usize,
        signed: bool,
        valid_start: u128,
        valid_end: u128,
    ) -> Self {
        Self {
            size_bytes,
            signed,
            valid_start,
            valid_end,
            is_bool: false,
            is_char: false,
        }
    }

    /// Bit width (`size_bytes * 8`).
    #[inline]
    pub fn bit_width(&self) -> u32 {
        (self.size_bytes * 8) as u32
    }

    /// Maps an arbitrary `u128` bit pattern into a valid bit pattern for `self`
    /// (`0..=1` for `bool`, a valid Unicode scalar value for `char`, and within
    /// `valid_start..=valid_end` for ranged integers).
    pub fn clamp_to_valid_bits(&self, raw: u128) -> u128 {
        if self.is_bool {
            return raw & 1;
        }
        if self.is_char {
            const CHARS: [u32; 6] = [0, b'A' as u32, b'0' as u32, 0x00FF, 0xD7FF, 0x10_FFFF];
            return CHARS[(raw as usize) % CHARS.len()] as u128;
        }
        let masked = raw & width_mask(self.bit_width());
        if masked < self.valid_start || masked > self.valid_end {
            let span = self.valid_end.saturating_sub(self.valid_start);
            if span == 0 {
                self.valid_start
            } else {
                self.valid_start + (masked % span.saturating_add(1))
            }
        } else {
            masked
        }
    }
}

/// Struct field descriptor with explicit byte offset inside its enclosing struct.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldLayout {
    pub name: String,
    pub offset: usize,
    pub layout: LayoutSpec,
}

/// Enum variant descriptor with explicit tag value and optional payload layout.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumVariantLayout {
    pub name: String,
    pub discriminant: u128,
    pub payload_offset: usize,
    pub payload: Option<Box<LayoutSpec>>,
}

/// Recursive memory layout descriptor preserving exact byte offsets and inter-field padding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LayoutSpec {
    Scalar(ScalarLayout),
    Struct {
        name: String,
        total_size: usize,
        fields: Vec<FieldLayout>,
    },
    Tuple {
        total_size: usize,
        elements: Vec<(usize, LayoutSpec)>,
    },
    Array {
        elem: Box<LayoutSpec>,
        elem_stride: usize,
        len: usize,
    },
    Enum {
        name: String,
        total_size: usize,
        tag_offset: usize,
        tag_size: usize,
        variants: Vec<EnumVariantLayout>,
    },
}

impl LayoutSpec {
    /// Total byte size of this layout in memory (including all inter-field and trailing padding).
    pub fn total_size(&self) -> usize {
        match self {
            Self::Scalar(s) => s.size_bytes,
            Self::Struct { total_size, .. } => *total_size,
            Self::Tuple { total_size, .. } => *total_size,
            Self::Array {
                elem_stride, len, ..
            } => elem_stride.saturating_mul(*len),
            Self::Enum { total_size, .. } => *total_size,
        }
    }

    /// Computes the exact sorted list of byte offsets within `0..self.total_size()` that are
    /// inter-field or trailing padding bytes (for structs, tuples, and arrays of structs/tuples).
    pub fn padding_offsets(&self) -> Vec<usize> {
        let total = self.total_size();
        let mut occupied = vec![false; total];
        self.mark_occupied(0, &mut occupied);
        occupied
            .iter()
            .enumerate()
            .filter_map(|(idx, &is_data)| if !is_data { Some(idx) } else { None })
            .collect()
    }

    /// Masks all inter-field and trailing padding positions in `raw` as `None`
    /// (unknown / uninitialized) while preserving occupied field bytes as
    /// `Some(byte)`.
    pub fn mask_padding_as_unknown(&self, raw: &[u8]) -> Result<Vec<Option<u8>>, ScheduleError> {
        let total = self.total_size();
        if raw.len() != total {
            return Err(ScheduleError::PayloadSizeMismatch {
                context: "LayoutSpec::mask_padding_as_unknown".to_string(),
                expected: total,
                actual: raw.len(),
            });
        }
        let mut occupied = vec![false; total];
        self.mark_occupied(0, &mut occupied);
        Ok(raw
            .iter()
            .zip(occupied.iter())
            .map(|(&b, &is_data)| if is_data { Some(b) } else { None })
            .collect())
    }

    /// Validates that `raw` has length `self.total_size()` and that all scalar
    /// fields and enum tags satisfy their bit-validity invariants.
    pub fn validate_bytes(&self, raw: &[u8]) -> Result<(), ScheduleError> {
        let total = self.total_size();
        if raw.len() != total {
            return Err(ScheduleError::PayloadSizeMismatch {
                context: "LayoutSpec::validate_bytes".to_string(),
                expected: total,
                actual: raw.len(),
            });
        }
        self.validate_at(0, raw)
    }

    fn validate_at(&self, base_offset: usize, raw: &[u8]) -> Result<(), ScheduleError> {
        match self {
            Self::Scalar(scalar) => {
                let n = scalar.size_bytes.min(16);
                let mut le = [0u8; 16];
                le[..n].copy_from_slice(&raw[base_offset..base_offset + n]);
                let val = u128::from_le_bytes(le) & width_mask(scalar.bit_width());
                if scalar.is_bool && val > 1 {
                    return Err(ScheduleError::InvalidBitPattern {
                        context: "bool".to_string(),
                        reason: format!("expected 0 or 1 at offset {base_offset}, got {val:#x}"),
                    });
                }
                if scalar.is_char {
                    let Ok(code) = u32::try_from(val) else {
                        return Err(ScheduleError::InvalidBitPattern {
                            context: "char".to_string(),
                            reason: format!("out-of-range char bits {val:#x}"),
                        });
                    };
                    if char::from_u32(code).is_none() {
                        return Err(ScheduleError::InvalidBitPattern {
                            context: "char".to_string(),
                            reason: format!(
                                "invalid Unicode scalar value {code:#x} at offset {base_offset}"
                            ),
                        });
                    }
                }
                if val < scalar.valid_start || val > scalar.valid_end {
                    return Err(ScheduleError::InvalidBitPattern {
                        context: "ScalarLayout".to_string(),
                        reason: format!(
                            "scalar bits {val:#x} at offset {base_offset} outside valid range \
                             [{:#x}, {:#x}]",
                            scalar.valid_start, scalar.valid_end
                        ),
                    });
                }
                Ok(())
            }
            Self::Struct { fields, .. } => {
                for field in fields {
                    field.layout.validate_at(base_offset + field.offset, raw)?;
                }
                Ok(())
            }
            Self::Tuple { elements, .. } => {
                for (off, elem) in elements {
                    elem.validate_at(base_offset + *off, raw)?;
                }
                Ok(())
            }
            Self::Array {
                elem,
                elem_stride,
                len,
            } => {
                for i in 0..*len {
                    elem.validate_at(base_offset + i * (*elem_stride), raw)?;
                }
                Ok(())
            }
            Self::Enum {
                tag_offset,
                tag_size,
                variants,
                ..
            } => {
                let n = (*tag_size).min(16);
                let mut le = [0u8; 16];
                le[..n].copy_from_slice(&raw[base_offset + *tag_offset..base_offset + *tag_offset + n]);
                let tag = u128::from_le_bytes(le) & width_mask((n * 8) as u32);
                let Some(variant) = variants.iter().find(|v| v.discriminant == tag) else {
                    return Err(ScheduleError::InvalidBitPattern {
                        context: "EnumLayout".to_string(),
                        reason: format!(
                            "discriminant {tag:#x} at offset {} does not match any variant",
                            base_offset + *tag_offset
                        ),
                    });
                };
                if let Some(payload) = &variant.payload {
                    payload.validate_at(base_offset + variant.payload_offset, raw)?;
                }
                Ok(())
            }
        }
    }

    fn mark_occupied(&self, base_offset: usize, occupied: &mut [bool]) {
        match self {
            Self::Scalar(s) => {
                for slot in occupied
                    .iter_mut()
                    .skip(base_offset)
                    .take(s.size_bytes)
                {
                    *slot = true;
                }
            }
            Self::Struct { fields, .. } => {
                for field in fields {
                    field.layout.mark_occupied(base_offset + field.offset, occupied);
                }
            }
            Self::Tuple { elements, .. } => {
                for (off, elem) in elements {
                    elem.mark_occupied(base_offset + *off, occupied);
                }
            }
            Self::Array {
                elem,
                elem_stride,
                len,
            } => {
                for i in 0..*len {
                    elem.mark_occupied(base_offset + i * (*elem_stride), occupied);
                }
            }
            Self::Enum {
                total_size,
                tag_offset,
                tag_size,
                variants,
                ..
            } => {
                for slot in occupied
                    .iter_mut()
                    .skip(base_offset + *tag_offset)
                    .take(*tag_size)
                {
                    *slot = true;
                }
                for v in variants {
                    if let Some(payload) = &v.payload {
                        payload.mark_occupied(base_offset + v.payload_offset, occupied);
                    }
                }
                let _ = total_size;
            }
        }
    }
}

/// Deterministic dictionary of branch literals, comparison constants, shift amounts,
/// and `ScalarLayout` boundary values extracted from MIR, JSON, or Rust AST sources.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct MirInputDictionary {
    /// Exact branch / comparison constants `c` indexed by bit width (`8`, `16`, `32`, `64`, `128`).
    pub primary_by_width: BTreeMap<u32, Vec<u128>>,
    /// Neighboring `{c - 1, c, c + 1}` and `ScalarLayout` boundary constants indexed by bit width.
    pub boundary_by_width: BTreeMap<u32, Vec<u128>>,
    /// Field- or variable-specific exact candidate constants extracted from expressions such as
    /// `hdr.magic == 0x414E_4E4C` or `hdr.offset.saturating_add(payload_len) > 1024`.
    pub field_hints: BTreeMap<String, Vec<u128>>,
    /// Deduplicated set of all raw unsigned constants observed across all sources.
    pub all_constants: BTreeSet<u128>,
}

impl MirInputDictionary {
    /// Creates an empty [`MirInputDictionary`].
    pub fn new() -> Self {
        Self::default()
    }

    fn insert_unique(vec: &mut Vec<u128>, val: u128) {
        if !vec.contains(&val) {
            vec.push(val);
        }
    }

    /// Registers a `switchInt` branch literal `c` at `bit_width`, automatically recording
    /// `c` as a primary literal and `{c.saturating_sub(1), c, c.saturating_add(1)}` in the
    /// boundary set.
    pub fn add_switch_int_literal(&mut self, c: u128, bit_width: u32) {
        let mask = width_mask(bit_width);
        let masked_c = c & mask;
        let sub1 = c.saturating_sub(1) & mask;
        let add1 = c.saturating_add(1) & mask;

        self.all_constants.insert(masked_c);
        self.all_constants.insert(sub1);
        self.all_constants.insert(add1);

        let primary = self.primary_by_width.entry(bit_width).or_default();
        Self::insert_unique(primary, 0);
        Self::insert_unique(primary, masked_c);

        let boundary = self.boundary_by_width.entry(bit_width).or_default();
        Self::insert_unique(boundary, masked_c);
        Self::insert_unique(boundary, sub1);
        Self::insert_unique(boundary, add1);
    }

    /// Registers a binary comparison constant `c` along with `{c.saturating_sub(1), c, c.saturating_add(1)}`.
    pub fn add_comparison_const(&mut self, c: u128, bit_width: u32) {
        self.add_switch_int_literal(c, bit_width);
    }

    /// Registers a shift amount constant `shift` (`0`, `shift - 1`, `shift`, `shift + 1`, `bit_width - 1`, `bit_width`).
    pub fn add_shift_const(&mut self, shift: u32, bit_width: u32) {
        self.add_switch_int_literal(shift as u128, bit_width);
        let boundary = self.boundary_by_width.entry(bit_width).or_default();
        Self::insert_unique(boundary, 0);
        Self::insert_unique(boundary, (bit_width.saturating_sub(1)) as u128);
        Self::insert_unique(boundary, bit_width as u128);
    }

    /// Associates a field or parameter identifier with an exact candidate literal while
    /// also placing `{value.saturating_sub(1), value, value.saturating_add(1)}` in the
    /// width-indexed boundary pools.
    pub fn add_field_hint(&mut self, field_name: &str, value: u128) {
        let hints = self.field_hints.entry(field_name.to_string()).or_default();
        Self::insert_unique(hints, value);
        let bits = infer_bit_width(value, "");
        self.add_switch_int_literal(value, bits);
    }

    /// Populates the full set of `ScalarLayout` validity boundary constants
    /// `{0, 1, start, end, MAX - 1, MAX, MIN, -1}` for `layout`.
    pub fn add_scalar_layout_bounds(&mut self, layout: &ScalarLayout) {
        let bits = layout.bit_width();
        let mask = width_mask(bits);
        let max_unsigned = mask;
        let max_minus_1 = max_unsigned.saturating_sub(1);
        let signed_min = if bits > 0 && bits <= 128 {
            1u128 << (bits - 1)
        } else {
            0
        };
        let signed_max = signed_min.saturating_sub(1);
        let neg_one_bits = (-1i128 as u128) & mask;

        let boundary = self.boundary_by_width.entry(bits).or_default();
        for candidate in [
            0u128,
            1u128 & mask,
            layout.valid_start & mask,
            layout.valid_end & mask,
            max_minus_1,
            max_unsigned,
            signed_min,
            signed_max,
            neg_one_bits,
        ] {
            self.all_constants.insert(candidate);
            Self::insert_unique(boundary, candidate);
        }
    }

    /// Merges all entries from `other` into `self`.
    pub fn merge(&mut self, other: &MirInputDictionary) {
        for (&width, vals) in &other.primary_by_width {
            let dst = self.primary_by_width.entry(width).or_default();
            for &v in vals {
                Self::insert_unique(dst, v);
            }
        }
        for (&width, vals) in &other.boundary_by_width {
            let dst = self.boundary_by_width.entry(width).or_default();
            for &v in vals {
                Self::insert_unique(dst, v);
            }
        }
        for (name, vals) in &other.field_hints {
            let dst = self.field_hints.entry(name.clone()).or_default();
            for &v in vals {
                Self::insert_unique(dst, v);
            }
        }
        for &c in &other.all_constants {
            self.all_constants.insert(c);
        }
    }

    /// Zero-allocation slice lookup into the pre-deduplicated boundary pool for `bit_width`.
    #[inline]
    pub fn boundary_slice_for_width(&self, bit_width: u32) -> &[u128] {
        self.boundary_by_width
            .get(&bit_width)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Returns the deduplicated list of dictionary candidate bit patterns for a scalar of
    /// `bit_width` bits, placing exact extracted primary literals first followed by boundary
    /// constants `{c - 1, c + 1, 0, 1, start, end, MAX - 1, MAX, MIN, -1}`.
    pub fn candidates_for_width(&self, bit_width: u32) -> Vec<u128> {
        let mask = width_mask(bit_width);
        let mut out = Vec::new();
        if let Some(primary) = self.primary_by_width.get(&bit_width) {
            for &v in primary {
                Self::insert_unique(&mut out, v & mask);
            }
        }
        if let Some(boundary) = self.boundary_by_width.get(&bit_width) {
            for &v in boundary {
                Self::insert_unique(&mut out, v & mask);
            }
        }
        if out.is_empty() {
            for &c in &self.all_constants {
                if c <= mask {
                    Self::insert_unique(&mut out, c & mask);
                }
            }
        }
        // Always include standard edge values if nothing was registered yet.
        for fallback in [0u128, 1u128 & mask, mask.saturating_sub(1), mask] {
            Self::insert_unique(&mut out, fallback);
        }
        out
    }

    /// Extracts branch, comparison, shift, and field-associated constants from a Rust source
    /// string using `syn::parse_file` and `syn::visit::Visit`.
    pub fn from_rust_source(source: &str) -> Result<Self, String> {
        let file = syn::parse_str::<syn::File>(source).map_err(|e| e.to_string())?;
        let mut visitor = RustDictVisitor {
            dict: MirInputDictionary::new(),
        };
        visitor.visit_file(&file);
        Ok(visitor.dict)
    }

    /// Extracts `switchInt` targets, comparison constants, shift amounts, and `ScalarLayout`
    /// bounds from a Lean 4 MIR source module (`Mir.<Crate>.<Item>.lean`).
    pub fn from_lean_mir(lean_src: &str) -> Self {
        let mut dict = MirInputDictionary::new();
        dict.scan_structured_text(lean_src);
        dict
    }

    /// Extracts `switchInt` targets, comparison constants, and `ScalarLayout` validity bounds
    /// from a JSON MIR / obligation summary document.
    pub fn from_json(json_str: &str) -> Self {
        let mut dict = MirInputDictionary::new();
        dict.scan_structured_text(json_str);
        dict
    }

    /// Shared lexical extractor for Lean 4 MIR and JSON representations. Recognizes decimal
    /// and hexadecimal (`0x...`) integer literals, field names adjacent to literals, and
    /// `ScalarLayout` byte widths (`sizeBytes := 1/2/4/8/16`, `"size_bytes": 4`).
    fn scan_structured_text(&mut self, text: &str) {
        // Record default scalar layout bounds for common widths.
        for width_bytes in [1usize, 2, 4, 8] {
            self.add_scalar_layout_bounds(&ScalarLayout::unsigned(width_bytes));
        }

        let bytes = text.as_bytes();
        let mut i = 0usize;
        let mut recent_ident: Option<String> = None;

        while i < bytes.len() {
            let b = bytes[i];
            if b.is_ascii_alphabetic() || b == b'_' {
                let start = i;
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
                let ident = &text[start..i];
                if !matches!(
                    ident,
                    "switchInt"
                        | "ConstScalar"
                        | "ScalarLayout"
                        | "sizeBytes"
                        | "size_bytes"
                        | "validRange"
                        | "valid_start"
                        | "valid_end"
                        | "u8"
                        | "u16"
                        | "u32"
                        | "u64"
                        | "i8"
                        | "i16"
                        | "i32"
                        | "i64"
                        | "true"
                        | "false"
                ) {
                    recent_ident = Some(ident.to_string());
                }
            } else if b.is_ascii_digit() {
                let start = i;
                let parsed = if b == b'0'
                    && i + 1 < bytes.len()
                    && (bytes[i + 1] == b'x' || bytes[i + 1] == b'X')
                {
                    i += 2;
                    let hex_start = i;
                    while i < bytes.len()
                        && (bytes[i].is_ascii_hexdigit() || bytes[i] == b'_')
                    {
                        i += 1;
                    }
                    let clean: String = text[hex_start..i]
                        .chars()
                        .filter(|&c| c != '_')
                        .collect();
                    u128::from_str_radix(&clean, 16).ok()
                } else {
                    while i < bytes.len() && (bytes[i].is_ascii_digit() || bytes[i] == b'_') {
                        i += 1;
                    }
                    let clean: String = text[start..i].chars().filter(|&c| c != '_').collect();
                    clean.parse::<u128>().ok()
                };

                // Optional integer suffix (`u8`, `u32`, etc.).
                let suffix_start = i;
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
                let suffix = &text[suffix_start..i];

                if let Some(val) = parsed {
                    let inferred_bits = infer_bit_width(val, suffix);
                    self.add_switch_int_literal(val, inferred_bits);
                    if val <= u8::MAX as u128 && inferred_bits != 8 {
                        self.add_switch_int_literal(val, 8);
                    }
                    if val <= u32::MAX as u128 && inferred_bits != 32 {
                        self.add_switch_int_literal(val, 32);
                    }
                    if let Some(ref field) = recent_ident {
                        self.add_field_hint(field, val);
                    }
                }
            } else {
                i += 1;
            }
        }
    }
}

fn infer_bit_width(val: u128, suffix: &str) -> u32 {
    match suffix {
        "u8" | "i8" => 8,
        "u16" | "i16" => 16,
        "u32" | "i32" => 32,
        "u64" | "i64" | "usize" | "isize" => 64,
        "u128" | "i128" => 128,
        _ => {
            if val <= u8::MAX as u128 {
                8
            } else if val <= u16::MAX as u128 {
                16
            } else if val <= u32::MAX as u128 {
                32
            } else if val <= u64::MAX as u128 {
                64
            } else {
                128
            }
        }
    }
}

struct RustDictVisitor {
    dict: MirInputDictionary,
}

impl RustDictVisitor {
    fn extract_int_lit(expr: &Expr) -> Option<(u128, u32)> {
        match expr {
            Expr::Lit(ExprLit {
                lit: Lit::Int(lit_int),
                ..
            }) => {
                let val = lit_int.base10_parse::<u128>().ok()?;
                let bits = infer_bit_width(val, lit_int.suffix());
                Some((val, bits))
            }
            Expr::Unary(un) if matches!(un.op, syn::UnOp::Neg(_)) => {
                if let Expr::Lit(ExprLit {
                    lit: Lit::Int(lit_int),
                    ..
                }) = un.expr.as_ref()
                {
                    let mag = lit_int.base10_parse::<i128>().ok()?;
                    let neg = (-mag) as u128;
                    let bits = infer_bit_width(mag.unsigned_abs(), lit_int.suffix());
                    Some((neg & width_mask(bits), bits))
                } else {
                    None
                }
            }
            Expr::Paren(p) => Self::extract_int_lit(&p.expr),
            _ => None,
        }
    }

    fn collect_ident_names(expr: &Expr, out: &mut Vec<String>) {
        match expr {
            Expr::Field(ExprField {
                member: Member::Named(id),
                base,
                ..
            }) => {
                out.push(id.to_string());
                Self::collect_ident_names(base, out);
            }
            Expr::Path(p) => {
                if let Some(last) = p.path.segments.last() {
                    out.push(last.ident.to_string());
                }
            }
            Expr::MethodCall(ExprMethodCall { receiver, args, .. }) => {
                Self::collect_ident_names(receiver, out);
                for arg in args {
                    Self::collect_ident_names(arg, out);
                }
            }
            Expr::Binary(b) => {
                Self::collect_ident_names(&b.left, out);
                Self::collect_ident_names(&b.right, out);
            }
            Expr::Paren(p) => Self::collect_ident_names(&p.expr, out),
            _ => {}
        }
    }
}

impl<'ast> Visit<'ast> for RustDictVisitor {
    fn visit_expr_binary(&mut self, node: &'ast ExprBinary) {
        let is_shift = matches!(node.op, BinOp::Shl(_) | BinOp::Shr(_));
        let mut lhs_names = Vec::new();
        let mut rhs_names = Vec::new();
        Self::collect_ident_names(&node.left, &mut lhs_names);
        Self::collect_ident_names(&node.right, &mut rhs_names);

        if let Some((val, bits)) = Self::extract_int_lit(&node.right) {
            if is_shift {
                self.dict.add_shift_const(val as u32, bits);
            } else {
                self.dict.add_comparison_const(val, bits);
                if val <= u8::MAX as u128 {
                    self.dict.add_comparison_const(val, 8);
                }
                if val <= u32::MAX as u128 {
                    self.dict.add_comparison_const(val, 32);
                }
            }
            for name in &lhs_names {
                self.dict.add_field_hint(name, val);
            }
        }

        if let Some((val, bits)) = Self::extract_int_lit(&node.left) {
            self.dict.add_comparison_const(val, bits);
            for name in &rhs_names {
                self.dict.add_field_hint(name, val);
            }
        }

        visit::visit_expr_binary(self, node);
    }

    fn visit_expr_match(&mut self, node: &'ast ExprMatch) {
        let mut scrutinee_names = Vec::new();
        Self::collect_ident_names(&node.expr, &mut scrutinee_names);
        for arm in &node.arms {
            if let Pat::Lit(pat_lit) = &arm.pat
                && let Lit::Int(lit_int) = &pat_lit.lit
                && let Ok(val) = lit_int.base10_parse::<u128>()
            {
                let bits = infer_bit_width(val, lit_int.suffix());
                self.dict.add_switch_int_literal(val, bits);
                for name in &scrutinee_names {
                    self.dict.add_field_hint(name, val);
                }
            }
        }
        visit::visit_expr_match(self, node);
    }

    fn visit_lit_int(&mut self, node: &'ast syn::LitInt) {
        if let Ok(val) = node.base10_parse::<u128>() {
            // Skip tiny structural indices (0, 1) as primary literals so actual magic numbers
            // and branch constants stay high priority.
            if val >= 2 {
                let bits = infer_bit_width(val, node.suffix());
                self.dict.add_switch_int_literal(val, bits);
            }
        }
        visit::visit_lit_int(self, node);
    }
}

/// Strategy used by [`LayoutAwareByteBuilder`] to fill inter-field and trailing padding bytes.
/// Guarantees non-zero poison values so accidental padding reads are immediately exposed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PaddingFillPattern {
    /// Fill every padding byte with the fixed non-zero byte (if `0` is passed, uses `0xA5`).
    Fixed(u8),
    /// Alternate `0xA5` and `0x5A` across successive padding bytes.
    AlternatingA55A,
    /// Fill every padding byte with deterministic non-zero SplitMix64 PRNG bytes derived from seed.
    PrngNonZero(u64),
}

impl PaddingFillPattern {
    /// Returns a deterministic non-zero byte for padding position `byte_offset`.
    #[inline]
    pub fn byte_at(self, byte_offset: usize, extra_entropy: u64) -> u8 {
        match self {
            Self::Fixed(b) => {
                if b == 0 {
                    0xA5
                } else {
                    b
                }
            }
            Self::AlternatingA55A => {
                if byte_offset.is_multiple_of(2) {
                    0xA5
                } else {
                    0x5A
                }
            }
            Self::PrngNonZero(seed) => {
                let mut z = seed
                    .wrapping_add(extra_entropy)
                    .wrapping_add((byte_offset as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15));
                z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
                z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
                let raw = ((z ^ (z >> 31)) & 0xFF) as u8;
                if raw == 0 { 0xA5 } else { raw }
            }
        }
    }
}

/// Fast deterministic PRNG helper that draws entropy from `Unstructured` when available
/// and mixes in a SplitMix64 state so even short `Unstructured` slices never stall or repeat.
struct EntropyStream<'a, 'u> {
    u: &'a mut Unstructured<'u>,
    state: u64,
}

impl<'a, 'u> EntropyStream<'a, 'u> {
    fn new(u: &'a mut Unstructured<'u>, salt: u64) -> Self {
        let seed_byte = u.arbitrary::<u8>().unwrap_or(0x5A) as u64;
        Self {
            u,
            state: salt
                .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                .wrapping_add(seed_byte),
        }
    }

    fn next_u64(&mut self) -> u64 {
        let from_u = self.u.arbitrary::<u16>().unwrap_or(0) as u64;
        self.state = self
            .state
            .wrapping_add(0x9E37_79B9_7F4A_7C15)
            .wrapping_add(from_u);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn next_u128(&mut self) -> u128 {
        ((self.next_u64() as u128) << 64) | (self.next_u64() as u128)
    }

    fn choose_index(&mut self, len: usize) -> usize {
        if len <= 1 {
            0
        } else {
            (self.next_u64() as usize) % len
        }
    }

    fn roll_percent(&mut self) -> u8 {
        (self.next_u64() % 100) as u8
    }
}

/// Layout-aware byte builder backed by a [`MirInputDictionary`].
#[derive(Debug, Clone)]
pub struct LayoutAwareByteBuilder<'a> {
    pub dict: &'a MirInputDictionary,
    /// Probability (`0..=100`) of drawing a scalar from `MirInputDictionary` boundary/primary
    /// constants vs. uniform `Unstructured` bytes. Defaults to `80` (80% dictionary, 20% uniform).
    pub dictionary_bias_pct: u8,
    /// Probability (`0..=100`) of injecting an invalid niche/discriminant bit pattern (`bool = 2`,
    /// surrogate `char = 0xD800`, out-of-range scalar validity, invalid enum tag).
    /// `0` keeps every generated value valid.
    pub validity_fault_rate_pct: u8,
    /// Non-zero fill pattern written to all inter-field and trailing padding bytes.
    pub padding_pattern: PaddingFillPattern,
}

impl<'a> LayoutAwareByteBuilder<'a> {
    /// Creates a new [`LayoutAwareByteBuilder`] with the standard 80% dictionary bias,
    /// 0% validity fault injection (safe default), and non-zero PRNG padding noise.
    pub fn new(dict: &'a MirInputDictionary) -> Self {
        Self {
            dict,
            dictionary_bias_pct: 80,
            validity_fault_rate_pct: 0,
            padding_pattern: PaddingFillPattern::PrngNonZero(0xA55A_CAFE_D00D_BEEF),
        }
    }

    /// Configures `validity_fault_rate_pct` (clamped to `0..=100`).
    pub fn with_validity_fault_rate_pct(mut self, pct: u8) -> Self {
        self.validity_fault_rate_pct = pct.min(100);
        self
    }

    /// Configures `dictionary_bias_pct` (clamped to `0..=100`).
    pub fn with_dictionary_bias_pct(mut self, pct: u8) -> Self {
        self.dictionary_bias_pct = pct.min(100);
        self
    }

    /// Configures the deterministic non-zero [`PaddingFillPattern`].
    pub fn with_padding_pattern(mut self, pattern: PaddingFillPattern) -> Self {
        self.padding_pattern = pattern;
        self
    }

    /// Builds a complete byte buffer of length `spec.total_size()` with all padding bytes
    /// pre-populated with deterministic non-zero noise and all fields serialized at their
    /// exact byte offsets.
    pub fn build_bytes(&self, spec: &LayoutSpec, u: &mut Unstructured<'_>) -> Vec<u8> {
        let mut rng = EntropyStream::new(u, 0x1234_5678_9ABC_DEF0);
        let salt = rng.next_u64();
        let total = spec.total_size();
        // Pre-fill the entire allocation with deterministic non-zero padding poison bytes;
        // subsequent field writes overwrite only occupied field bytes, leaving every single
        // inter-field and trailing padding byte strictly non-zero!
        let mut buf: Vec<u8> = (0..total)
            .map(|off| self.padding_pattern.byte_at(off, salt))
            .collect();
        self.fill_layout(spec, None, 0, &mut buf, &mut rng);
        buf
    }

    /// Materializes both the raw byte buffer (including non-zero padding bytes)
    /// and a validated `T: FromScheduleBytes` value without `unsafe` or
    /// `MaybeUninit::assume_init`.
    pub fn materialize_checked<T: FromScheduleBytes>(
        &self,
        spec: &LayoutSpec,
        u: &mut Unstructured<'_>,
    ) -> Result<(Vec<u8>, T), ScheduleError> {
        let bytes = self.build_bytes(spec, u);
        spec.validate_bytes(&bytes)?;
        let val = T::from_schedule_bytes(&bytes)?;
        Ok((bytes, val))
    }

    /// Materializes both the raw byte buffer (including non-zero padding bytes)
    /// and an owned `T: Copy + FromScheduleBytes` value using safe field-by-field
    /// decoding.
    ///
    /// # Panics
    ///
    /// Panics if `spec.total_size() != size_of::<T>()` or if the generated
    /// bytes fail `LayoutSpec` or `T::from_schedule_bytes` bit-validity checks.
    pub fn materialize_copy<T: Copy + FromScheduleBytes>(
        &self,
        spec: &LayoutSpec,
        u: &mut Unstructured<'_>,
    ) -> (Vec<u8>, T) {
        self.materialize_checked::<T>(spec, u)
            .unwrap_or_else(|err| panic!("materialize_copy failed validation: {err}"))
    }

    /// Draws a single `u32` scalar using the configured dictionary bias and optional field hint.
    pub fn draw_u32(
        &self,
        field_hint: Option<&str>,
        u: &mut Unstructured<'_>,
    ) -> u32 {
        let spec = LayoutSpec::Scalar(ScalarLayout::u32());
        let mut rng = EntropyStream::new(u, 0x7788_99AA_BBCC_DDEE);
        let mut buf = [0u8; 4];
        self.fill_layout(&spec, field_hint, 0, &mut buf, &mut rng);
        u32::from_le_bytes(buf)
    }

    fn fill_layout(
        &self,
        spec: &LayoutSpec,
        field_name: Option<&str>,
        base_offset: usize,
        buf: &mut [u8],
        rng: &mut EntropyStream<'_, '_>,
    ) {
        match spec {
            LayoutSpec::Scalar(scalar) => {
                let raw_val = self.draw_scalar_bits(scalar, field_name, rng);
                let le = raw_val.to_le_bytes();
                let n = scalar.size_bytes.min(16);
                buf[base_offset..base_offset + n].copy_from_slice(&le[..n]);
            }
            LayoutSpec::Struct { fields, .. } => {
                for field in fields {
                    self.fill_layout(
                        &field.layout,
                        Some(field.name.as_str()),
                        base_offset + field.offset,
                        buf,
                        rng,
                    );
                }
            }
            LayoutSpec::Tuple { elements, .. } => {
                for (off, elem) in elements {
                    self.fill_layout(elem, None, base_offset + *off, buf, rng);
                }
            }
            LayoutSpec::Array {
                elem,
                elem_stride,
                len,
            } => {
                for i in 0..*len {
                    self.fill_layout(elem, field_name, base_offset + i * (*elem_stride), buf, rng);
                }
            }
            LayoutSpec::Enum {
                tag_offset,
                tag_size,
                variants,
                ..
            } => {
                let inject_fault = self.validity_fault_rate_pct > 0
                    && rng.roll_percent() < self.validity_fault_rate_pct;
                if inject_fault || variants.is_empty() {
                    // Inject an invalid enum discriminant not equal to any declared variant tag.
                    let mut bad_tag: u128 = 0xFE;
                    while variants.iter().any(|v| v.discriminant == bad_tag) {
                        bad_tag = bad_tag.wrapping_add(1);
                    }
                    let le = bad_tag.to_le_bytes();
                    let n = (*tag_size).min(16);
                    buf[base_offset + *tag_offset..base_offset + *tag_offset + n]
                        .copy_from_slice(&le[..n]);
                } else {
                    let chosen = &variants[rng.choose_index(variants.len())];
                    let le = chosen.discriminant.to_le_bytes();
                    let n = (*tag_size).min(16);
                    buf[base_offset + *tag_offset..base_offset + *tag_offset + n]
                        .copy_from_slice(&le[..n]);
                    if let Some(payload) = &chosen.payload {
                        self.fill_layout(
                            payload,
                            None,
                            base_offset + chosen.payload_offset,
                            buf,
                            rng,
                        );
                    }
                }
            }
        }
    }

    fn draw_scalar_bits(
        &self,
        scalar: &ScalarLayout,
        field_name: Option<&str>,
        rng: &mut EntropyStream<'_, '_>,
    ) -> u128 {
        let bits = scalar.bit_width();
        let mask = width_mask(bits);

        // Optional bit-validity fault injection.
        if self.validity_fault_rate_pct > 0 && rng.roll_percent() < self.validity_fault_rate_pct {
            if scalar.is_bool {
                // Invalid `bool` bit pattern (`2`..=`255`).
                return 2 + (rng.next_u64() % 253) as u128;
            }
            if scalar.is_char {
                // UTF-16 surrogate code point (`0xD800..=0xDFFF`) or `0x110000` (UB for `char`).
                return if rng.next_u64().is_multiple_of(2) {
                    0xD800
                } else {
                    0x11_0000
                };
            }
            if scalar.valid_start > 0 {
                return 0;
            }
            if scalar.valid_end < mask {
                return (scalar.valid_end + 1) & mask;
            }
        }

        // Safe `bool` and `char` fast paths when validity faults are not injected.
        if scalar.is_bool {
            return (rng.next_u64() & 1) as u128;
        }
        if scalar.is_char {
            let candidates: [u32; 6] = [0, b'A' as u32, b'0' as u32, 0x00FF, 0xD7FF, 0x10_FFFF];
            return candidates[rng.choose_index(candidates.len())] as u128;
        }

        // 80% dictionary-boundary bias vs. 20% uniform `Unstructured` draw.
        let use_dict = rng.roll_percent() < self.dictionary_bias_pct;
        let raw = if use_dict {
            // If we have field-specific hints for this exact field name, prefer them 70% of the
            // time so multi-field magic/version/flags guards converge in a handful of trials.
            if let Some(name) = field_name
                && let Some(hints) = self.dict.field_hints.get(name)
                && !hints.is_empty()
                && rng.roll_percent() < 75
            {
                hints[rng.choose_index(hints.len())] & mask
            } else if let Some(primary) = self.dict.primary_by_width.get(&bits)
                && !primary.is_empty()
                && rng.roll_percent() < 60
            {
                primary[rng.choose_index(primary.len())] & mask
            } else {
                let slice = self.dict.boundary_slice_for_width(bits);
                if !slice.is_empty() {
                    slice[rng.choose_index(slice.len())] & mask
                } else {
                    let fallbacks = [0u128, 1u128 & mask, mask.saturating_sub(1), mask];
                    fallbacks[rng.choose_index(fallbacks.len())]
                }
            }
        } else {
            rng.next_u128() & mask
        };

        // Clamp to `[valid_start, valid_end]` when validity fault injection did not fire.
        if raw < scalar.valid_start || raw > scalar.valid_end {
            let span = scalar.valid_end.saturating_sub(scalar.valid_start);
            if span == 0 {
                scalar.valid_start
            } else {
                scalar.valid_start + (raw % (span.saturating_add(1)))
            }
        } else {
            raw
        }
    }
}

/// Strategy used by [`EnvScheduleGenerator`] to synthesize per-callee environment schedules.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvStrategy {
    /// Always return the same byte sequence on every call.
    Constant(Vec<u8>),
    /// Return a monotonically advancing counter (`start + k * step`) encoded as little-endian bytes.
    MonotonicCounter {
        start: u64,
        step: u64,
        width_bytes: usize,
    },
    /// Alternate between an `Ok` byte payload and an `Err` byte payload across calls.
    AlternatingOkErr {
        ok_bytes: Vec<u8>,
        err_bytes: Vec<u8>,
    },
    /// Draw a sequence of return values from `MirInputDictionary` boundary constants.
    DictionaryDrawn {
        width_bytes: usize,
    },
    /// Deterministically unwind with a panic on call index `k` (`PanicOnCall(k)`).
    PanicOnCall(usize),
}

/// Reactive `inputs-over-time` environment schedule generator for external callees.
#[derive(Debug, Clone)]
pub struct EnvScheduleGenerator<'a> {
    pub dict: &'a MirInputDictionary,
    /// Number of pre-materialized steps pushed per callee queue (default `8`).
    pub horizon_steps: usize,
    /// Percentage of generated schedules that inject `PanicOnCall(k)` (default `25%`).
    pub panic_injection_pct: u8,
    /// Per-callee expected return [`LayoutSpec`]s used to validate schedule
    /// payload sizes and bit-validity invariants at generation time. Callees
    /// not explicitly registered default to a 4-byte `u32` scalar layout.
    pub callee_return_layouts: BTreeMap<String, LayoutSpec>,
}

impl<'a> EnvScheduleGenerator<'a> {
    /// Creates a new [`EnvScheduleGenerator`] backed by `dict`.
    pub fn new(dict: &'a MirInputDictionary) -> Self {
        Self {
            dict,
            horizon_steps: 8,
            panic_injection_pct: 25,
            callee_return_layouts: BTreeMap::new(),
        }
    }

    /// Configures the number of pre-scheduled steps per callee queue.
    pub fn with_horizon_steps(mut self, steps: usize) -> Self {
        self.horizon_steps = steps.max(1);
        self
    }

    /// Configures the probability (`0..=100`) of injecting `PanicOnCall(k)`.
    pub fn with_panic_injection_pct(mut self, pct: u8) -> Self {
        self.panic_injection_pct = pct.min(100);
        self
    }

    /// Registers the expected return [`LayoutSpec`] for `callee` and returns `self`.
    pub fn with_callee_return_layout(mut self, callee: &str, layout: LayoutSpec) -> Self {
        self.set_callee_return_layout(callee, layout);
        self
    }

    /// Registers the expected return [`LayoutSpec`] for `callee`.
    pub fn set_callee_return_layout(&mut self, callee: &str, layout: LayoutSpec) {
        self.callee_return_layouts
            .insert(callee.to_string(), layout);
    }

    /// Returns the expected return [`LayoutSpec`] for `callee`, defaulting to
    /// `LayoutSpec::Scalar(ScalarLayout::u32())` (4 bytes) when not explicitly
    /// registered.
    pub fn expected_callee_layout(&self, callee: &str) -> LayoutSpec {
        if let Some(spec) = self.callee_return_layouts.get(callee) {
            return spec.clone();
        }
        if let Some((_, short)) = callee.rsplit_once("::")
            && let Some(spec) = self.callee_return_layouts.get(short)
        {
            return spec.clone();
        }
        LayoutSpec::Scalar(ScalarLayout::u32())
    }

    /// Validates at schedule generation time that `strategy` produces payloads
    /// whose byte size and bit-validity invariants match `callee`'s expected
    /// return [`LayoutSpec`].
    pub fn validate_strategy(
        &self,
        callee: &str,
        strategy: &EnvStrategy,
    ) -> Result<usize, ScheduleError> {
        let layout = self.expected_callee_layout(callee);
        let expected_size = layout.total_size();
        match strategy {
            EnvStrategy::Constant(bytes) => {
                if bytes.len() != expected_size {
                    return Err(ScheduleError::PayloadSizeMismatch {
                        context: callee.to_string(),
                        expected: expected_size,
                        actual: bytes.len(),
                    });
                }
                layout.validate_bytes(bytes)?;
            }
            EnvStrategy::MonotonicCounter {
                start,
                step,
                width_bytes,
            } => {
                if *width_bytes != expected_size {
                    return Err(ScheduleError::PayloadSizeMismatch {
                        context: callee.to_string(),
                        expected: expected_size,
                        actual: *width_bytes,
                    });
                }
                let steps = self.horizon_steps.max(1);
                let w = *width_bytes;
                for k in 0..steps {
                    let raw = start.wrapping_add((k as u64).wrapping_mul(*step)) as u128;
                    let val = if let LayoutSpec::Scalar(ref scalar) = layout {
                        scalar.clamp_to_valid_bits(raw)
                    } else {
                        raw
                    };
                    let le = val.to_le_bytes();
                    let mut payload = vec![0u8; w];
                    let copy_len = w.min(le.len());
                    payload[..copy_len].copy_from_slice(&le[..copy_len]);
                    layout.validate_bytes(&payload)?;
                }
            }
            EnvStrategy::AlternatingOkErr {
                ok_bytes,
                err_bytes,
            } => {
                if ok_bytes.len() != expected_size {
                    return Err(ScheduleError::PayloadSizeMismatch {
                        context: callee.to_string(),
                        expected: expected_size,
                        actual: ok_bytes.len(),
                    });
                }
                if err_bytes.len() != expected_size {
                    return Err(ScheduleError::PayloadSizeMismatch {
                        context: callee.to_string(),
                        expected: expected_size,
                        actual: err_bytes.len(),
                    });
                }
                layout.validate_bytes(ok_bytes)?;
                layout.validate_bytes(err_bytes)?;
            }
            EnvStrategy::DictionaryDrawn { width_bytes } => {
                if *width_bytes != expected_size {
                    return Err(ScheduleError::PayloadSizeMismatch {
                        context: callee.to_string(),
                        expected: expected_size,
                        actual: *width_bytes,
                    });
                }
                let LayoutSpec::Scalar(ref scalar) = layout else {
                    return Err(ScheduleError::InvalidBitPattern {
                        context: callee.to_string(),
                        reason: "DictionaryDrawn requires a scalar return layout".to_string(),
                    });
                };
                let w = *width_bytes;
                let slice = self.dict.boundary_slice_for_width((w * 8) as u32);
                if slice.is_empty() {
                    let chosen = scalar.clamp_to_valid_bits(0);
                    let le = chosen.to_le_bytes();
                    let mut payload = vec![0u8; w];
                    let copy_len = w.min(le.len());
                    payload[..copy_len].copy_from_slice(&le[..copy_len]);
                    layout.validate_bytes(&payload)?;
                } else {
                    for &raw in slice {
                        let chosen = scalar.clamp_to_valid_bits(raw);
                        let le = chosen.to_le_bytes();
                        let mut payload = vec![0u8; w];
                        let copy_len = w.min(le.len());
                        payload[..copy_len].copy_from_slice(&le[..copy_len]);
                        layout.validate_bytes(&payload)?;
                    }
                }
            }
            EnvStrategy::PanicOnCall(_) => {}
        }
        Ok(expected_size)
    }

    /// Applies an explicit [`EnvStrategy`] for `callee` onto `schedule`,
    /// rejecting any strategy whose payload size or bit pattern does not match
    /// `callee`'s expected return layout.
    pub fn apply_strategy_checked(
        &self,
        schedule: &mut EnvSchedule,
        callee: &str,
        strategy: &EnvStrategy,
        u: &mut Unstructured<'_>,
    ) -> Result<(), ScheduleError> {
        let layout = self.expected_callee_layout(callee);
        let expected_size = self.validate_strategy(callee, strategy)?;
        schedule.register_callee_return_size(callee, expected_size);
        let mut rng = EntropyStream::new(u, 0xFACE_B00C_1234_5678);
        match strategy {
            EnvStrategy::Constant(bytes) => {
                for _ in 0..self.horizon_steps {
                    schedule.push_callee_response_checked(callee, bytes.clone())?;
                }
                schedule.set_callee_default_checked(callee, bytes.clone())?;
            }
            EnvStrategy::MonotonicCounter {
                start,
                step,
                width_bytes,
            } => {
                let w = *width_bytes;
                for k in 0..self.horizon_steps {
                    let raw = start.wrapping_add((k as u64).wrapping_mul(*step)) as u128;
                    let val = if let LayoutSpec::Scalar(ref scalar) = layout {
                        scalar.clamp_to_valid_bits(raw)
                    } else {
                        raw
                    };
                    let le = val.to_le_bytes();
                    let mut payload = vec![0u8; w];
                    let copy_len = w.min(le.len());
                    payload[..copy_len].copy_from_slice(&le[..copy_len]);
                    layout.validate_bytes(&payload)?;
                    schedule.push_callee_response_checked(callee, payload)?;
                }
            }
            EnvStrategy::AlternatingOkErr {
                ok_bytes,
                err_bytes,
            } => {
                for k in 0..self.horizon_steps {
                    if k.is_multiple_of(2) {
                        schedule.push_callee_response_checked(callee, ok_bytes.clone())?;
                    } else {
                        schedule.push_callee_response_checked(callee, err_bytes.clone())?;
                    }
                }
            }
            EnvStrategy::DictionaryDrawn { width_bytes } => {
                let w = *width_bytes;
                let slice = self.dict.boundary_slice_for_width((w * 8) as u32);
                for _ in 0..self.horizon_steps {
                    let raw = if !slice.is_empty() {
                        slice[rng.choose_index(slice.len())]
                    } else {
                        0
                    };
                    let chosen = if let LayoutSpec::Scalar(ref scalar) = layout {
                        scalar.clamp_to_valid_bits(raw)
                    } else {
                        raw
                    };
                    let le = chosen.to_le_bytes();
                    let mut payload = vec![0u8; w];
                    let copy_len = w.min(le.len());
                    payload[..copy_len].copy_from_slice(&le[..copy_len]);
                    layout.validate_bytes(&payload)?;
                    schedule.push_callee_response_checked(callee, payload)?;
                }
            }
            EnvStrategy::PanicOnCall(call_idx) => {
                schedule.set_callee_panic_on_call(callee, *call_idx);
            }
        }
        Ok(())
    }

    /// Applies an explicit [`EnvStrategy`] for `callee` onto `schedule`.
    ///
    /// # Panics
    ///
    /// Panics if `strategy` produces payloads whose byte length or bit pattern
    /// does not match `callee`'s expected return layout.
    pub fn apply_strategy(
        &self,
        schedule: &mut EnvSchedule,
        callee: &str,
        strategy: &EnvStrategy,
        u: &mut Unstructured<'_>,
    ) {
        self.apply_strategy_checked(schedule, callee, strategy, u)
            .unwrap_or_else(|err| panic!("invalid EnvStrategy for `{callee}`: {err}"));
    }

    /// Generates a complete multi-callee [`EnvSchedule`] by selecting one of the 5 reactive
    /// environment strategies per callee from `u`, validating every payload against the
    /// callee's expected return layout.
    pub fn generate_schedule(&self, callees: &[&str], u: &mut Unstructured<'_>) -> EnvSchedule {
        let mut schedule = EnvSchedule::new();
        let mut chosen_strategies = Vec::with_capacity(callees.len());
        let builder = LayoutAwareByteBuilder::new(self.dict);

        {
            let mut rng = EntropyStream::new(u, 0xCAFE_F00D_0123_4567);
            for &callee in callees {
                let layout = self.expected_callee_layout(callee);
                let expected_size = layout.total_size();
                schedule.register_callee_return_size(callee, expected_size);
                let roll = rng.roll_percent();
                let strategy = if roll < self.panic_injection_pct {
                    EnvStrategy::PanicOnCall(0)
                } else if !matches!(layout, LayoutSpec::Scalar(_)) {
                    match rng.next_u64() % 2 {
                        0 => {
                            let seed = rng.next_u64().to_le_bytes();
                            let mut sub_u = Unstructured::new(&seed);
                            let bytes = builder.build_bytes(&layout, &mut sub_u);
                            EnvStrategy::Constant(bytes)
                        }
                        _ => {
                            let seed_ok = rng.next_u64().to_le_bytes();
                            let seed_err = rng.next_u64().to_le_bytes();
                            let mut u_ok = Unstructured::new(&seed_ok);
                            let mut u_err = Unstructured::new(&seed_err);
                            EnvStrategy::AlternatingOkErr {
                                ok_bytes: builder.build_bytes(&layout, &mut u_ok),
                                err_bytes: builder.build_bytes(&layout, &mut u_err),
                            }
                        }
                    }
                } else {
                    match rng.next_u64() % 4 {
                        0 => {
                            let seed = rng.next_u64().to_le_bytes();
                            let mut sub_u = Unstructured::new(&seed);
                            let bytes = builder.build_bytes(&layout, &mut sub_u);
                            EnvStrategy::Constant(bytes)
                        }
                        1 => EnvStrategy::MonotonicCounter {
                            start: (rng.next_u64() % 16),
                            step: 1 + (rng.next_u64() % 8),
                            width_bytes: expected_size,
                        },
                        2 => {
                            let mut ok_bytes = vec![0u8; expected_size];
                            let mut err_bytes = vec![0u8; expected_size];
                            if !ok_bytes.is_empty() {
                                ok_bytes[0] = 1;
                            }
                            if layout.validate_bytes(&ok_bytes).is_err() {
                                let seed = rng.next_u64().to_le_bytes();
                                let mut sub_u = Unstructured::new(&seed);
                                ok_bytes = builder.build_bytes(&layout, &mut sub_u);
                            }
                            if layout.validate_bytes(&err_bytes).is_err() {
                                err_bytes = ok_bytes.clone();
                            }
                            EnvStrategy::AlternatingOkErr {
                                ok_bytes,
                                err_bytes,
                            }
                        }
                        _ => EnvStrategy::DictionaryDrawn {
                            width_bytes: expected_size,
                        },
                    }
                };
                chosen_strategies.push((callee, strategy));
            }
        }

        for (callee, strategy) in &chosen_strategies {
            self.apply_strategy(&mut schedule, callee, strategy, u);
        }

        schedule
    }
}

/// Canonical equivalence class key for an observed execution path in [`MirObsPathSet`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MirObsPathKey {
    /// Name of the executed target function.
    pub fn_name: String,
    /// Ordered sequence of basic-block / branch decision tags taken along the run.
    pub branch_tags: Vec<u32>,
    /// Ordered sequence of external calls `(callee_name, call_index)` performed along the run.
    pub ext_call_sequence_shape: Vec<(String, usize)>,
    /// `true` if the execution unwound via panic rather than returning normally.
    pub is_panic: bool,
}

/// Coverage-guided path corpus deduplicating native trace executions by [`MirObsPathKey`]
/// and retaining the minimal input byte seed for each distinct feasible path.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct MirObsPathSet {
    minimal_seeds: BTreeMap<MirObsPathKey, Vec<u8>>,
}

impl MirObsPathSet {
    /// Creates an empty [`MirObsPathSet`].
    pub fn new() -> Self {
        Self::default()
    }

    /// Records a path key and its raw input `seed`. Returns `true` if `key` is a newly
    /// discovered execution path, or `false` if `key` was already known (updating the stored
    /// seed if `seed` is strictly shorter, or equal length and lexicographically smaller).
    pub fn record_execution(&mut self, key: MirObsPathKey, seed: Vec<u8>) -> bool {
        match self.minimal_seeds.get_mut(&key) {
            None => {
                self.minimal_seeds.insert(key, seed);
                true
            }
            Some(existing) => {
                if seed.len() < existing.len()
                    || (seed.len() == existing.len() && seed.as_slice() < existing.as_slice())
                {
                    *existing = seed;
                }
                false
            }
        }
    }

    /// Extracts a [`MirObsPathKey`] directly from a completed [`TraceRecorder`] and records it.
    pub fn record_trace(&mut self, fn_name: &str, rec: &TraceRecorder, seed: Vec<u8>) -> bool {
        let key = MirObsPathKey {
            fn_name: fn_name.to_string(),
            branch_tags: rec.branch_tags.clone(),
            ext_call_sequence_shape: rec.ext_call_sequence_shape(),
            is_panic: rec.is_panic(),
        };
        self.record_execution(key, seed)
    }

    /// Number of distinct execution paths discovered so far.
    pub fn len(&self) -> usize {
        self.minimal_seeds.len()
    }

    /// Returns `true` if no execution paths have been recorded yet.
    pub fn is_empty(&self) -> bool {
        self.minimal_seeds.is_empty()
    }

    /// Looks up the minimal input seed retained for `key`.
    pub fn minimal_seed_for(&self, key: &MirObsPathKey) -> Option<&[u8]> {
        self.minimal_seeds.get(key).map(Vec::as_slice)
    }

    /// Returns the map of all discovered path keys to their minimal input byte seeds.
    pub fn entries(&self) -> &BTreeMap<MirObsPathKey, Vec<u8>> {
        &self.minimal_seeds
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mir_dictionary_extracts_from_rust_lean_and_json() {
        let rust_src = r#"
            pub fn check(x: u32, flag: u8) -> bool {
                if x == 0xDEAD_BEEF && flag == 0x80 {
                    true
                } else {
                    false
                }
            }
        "#;
        let dict_rust = MirInputDictionary::from_rust_source(rust_src).expect("valid rust");
        assert!(dict_rust.all_constants.contains(&0xDEAD_BEEF));
        assert!(dict_rust.all_constants.contains(&0xDEAD_BEEE));
        assert!(dict_rust.all_constants.contains(&0xDEAD_BEF0));
        assert!(dict_rust.all_constants.contains(&0x80));

        let lean_mir = r#"
            def bb0 : BasicBlock := {
              terminator := Terminator.switchInt (Operand.copy 1) [0x414E4E4C, 1024]
            }
        "#;
        let dict_lean = MirInputDictionary::from_lean_mir(lean_mir);
        assert!(dict_lean.all_constants.contains(&0x414E_4E4C));
        assert!(dict_lean.all_constants.contains(&1024));
        assert!(dict_lean.all_constants.contains(&1023));
        assert!(dict_lean.all_constants.contains(&1025));

        let json_doc = r#"{"switch_targets": [42, 255], "size_bytes": 4}"#;
        let dict_json = MirInputDictionary::from_json(json_doc);
        assert!(dict_json.all_constants.contains(&42));
        assert!(dict_json.all_constants.contains(&255));
    }

    #[test]
    fn layout_aware_builder_fills_all_padding_bytes_nonzero_and_supports_faults() {
        let spec = LayoutSpec::Struct {
            name: "Demo".to_string(),
            total_size: 12,
            fields: vec![
                FieldLayout {
                    name: "a".to_string(),
                    offset: 0,
                    layout: LayoutSpec::Scalar(ScalarLayout::u8()),
                },
                // offsets 1, 2, 3 are inter-field padding!
                FieldLayout {
                    name: "b".to_string(),
                    offset: 4,
                    layout: LayoutSpec::Scalar(ScalarLayout::u32()),
                },
                FieldLayout {
                    name: "c".to_string(),
                    offset: 8,
                    layout: LayoutSpec::Scalar(ScalarLayout::bool_layout()),
                },
                // offsets 9, 10, 11 are trailing padding!
            ],
        };
        let pad_offsets = spec.padding_offsets();
        assert_eq!(pad_offsets, vec![1, 2, 3, 9, 10, 11]);

        let dict = MirInputDictionary::new();
        let safe_builder = LayoutAwareByteBuilder::new(&dict);
        let raw_entropy = [0xABu8; 64];
        let mut u = Unstructured::new(&raw_entropy);
        let bytes = safe_builder.build_bytes(&spec, &mut u);
        assert_eq!(bytes.len(), 12);
        for &pad_idx in &pad_offsets {
            assert_ne!(bytes[pad_idx], 0, "padding byte at offset {pad_idx} must be non-zero");
        }
        assert!(bytes[8] <= 1, "safe mode must emit valid bool (0 or 1)");

        // Negative fault mode at 100% rate must inject invalid `bool >= 2`.
        let fault_builder = LayoutAwareByteBuilder::new(&dict).with_validity_fault_rate_pct(100);
        let mut u2 = Unstructured::new(&raw_entropy);
        let fault_bytes = fault_builder.build_bytes(&spec, &mut u2);
        assert!(fault_bytes[8] >= 2, "100% fault rate must inject invalid bool >= 2");
        assert!(
            spec.validate_bytes(&fault_bytes).is_err(),
            "LayoutSpec::validate_bytes must reject injected invalid bool bit pattern"
        );
        let masked = spec
            .mask_padding_as_unknown(&bytes)
            .expect("mask_padding_as_unknown must succeed on matching size");
        for &pad_idx in &pad_offsets {
            assert_eq!(masked[pad_idx], None);
        }
        assert_eq!(masked[0], Some(bytes[0]));
        assert_eq!(masked[8], Some(bytes[8]));
    }

    #[test]
    fn env_schedule_generator_rejects_mismatched_payload_sizes_at_generation_time() {
        let dict = MirInputDictionary::new();
        let env_gen = EnvScheduleGenerator::new(&dict)
            .with_horizon_steps(4)
            .with_panic_injection_pct(0)
            .with_callee_return_layout("ext_u32", LayoutSpec::Scalar(ScalarLayout::u32()))
            .with_callee_return_layout("ext_bool", LayoutSpec::Scalar(ScalarLayout::bool_layout()));

        let mut sched = EnvSchedule::new();
        let mut u = Unstructured::new(&[0x11, 0x22, 0x33, 0x44]);

        // 5-byte payload for 4-byte `ext_u32` must be rejected at generation time.
        let bad_alt = EnvStrategy::AlternatingOkErr {
            ok_bytes: vec![0, 0x42, 0, 0, 0],
            err_bytes: vec![1, 0, 0, 0, 0],
        };
        assert_eq!(
            env_gen.apply_strategy_checked(&mut sched, "ext_u32", &bad_alt, &mut u),
            Err(ScheduleError::PayloadSizeMismatch {
                context: "ext_u32".to_string(),
                expected: 4,
                actual: 5,
            })
        );

        // 2-byte counter for 4-byte `ext_u32` must be rejected at generation time.
        let bad_counter = EnvStrategy::MonotonicCounter {
            start: 0,
            step: 1,
            width_bytes: 2,
        };
        assert_eq!(
            env_gen.apply_strategy_checked(&mut sched, "ext_u32", &bad_counter, &mut u),
            Err(ScheduleError::PayloadSizeMismatch {
                context: "ext_u32".to_string(),
                expected: 4,
                actual: 2,
            })
        );

        // Invalid `bool = 2` constant for `ext_bool` must be rejected at generation time.
        let bad_bool = EnvStrategy::Constant(vec![2]);
        assert!(
            env_gen
                .apply_strategy_checked(&mut sched, "ext_bool", &bad_bool, &mut u)
                .is_err()
        );

        // `validate_strategy` must also reject `MonotonicCounter` and `DictionaryDrawn`
        // when applied to an enum layout whose valid discriminant range is violated.
        let env_gen_enum = env_gen.clone().with_callee_return_layout(
            "ext_enum",
            LayoutSpec::Enum {
                name: "TwoWay".to_string(),
                total_size: 1,
                tag_offset: 0,
                tag_size: 1,
                variants: vec![
                    EnumVariantLayout {
                        name: "A".to_string(),
                        discriminant: 0,
                        payload_offset: 1,
                        payload: None,
                    },
                    EnumVariantLayout {
                        name: "B".to_string(),
                        discriminant: 1,
                        payload_offset: 1,
                        payload: None,
                    },
                ],
            },
        );
        assert!(
            env_gen_enum
                .validate_strategy(
                    "ext_enum",
                    &EnvStrategy::MonotonicCounter {
                        start: 0,
                        step: 1,
                        width_bytes: 1,
                    },
                )
                .is_err()
        );
        assert!(
            env_gen_enum
                .validate_strategy("ext_enum", &EnvStrategy::DictionaryDrawn { width_bytes: 1 })
                .is_err()
        );

        // Generated schedules across arbitrary seeds must always emit exact-size valid payloads.
        for seed in 0..32u64 {
            let bytes = seed.to_le_bytes();
            let mut u_seed = Unstructured::new(&bytes);
            let generated = env_gen.generate_schedule(&["ext_u32", "ext_bool"], &mut u_seed);
            if let Some(q) = generated.callee_queues.get("ext_u32") {
                for item in q {
                    assert_eq!(item.len(), 4);
                }
            }
            if let Some(q) = generated.callee_queues.get("ext_bool") {
                for item in q {
                    assert_eq!(item.len(), 1);
                    assert!(item[0] <= 1);
                }
            }
        }
    }

    #[test]
    fn mir_obs_path_set_retains_strictly_minimal_seed_per_path() {
        let mut set = MirObsPathSet::new();
        let key = MirObsPathKey {
            fn_name: "demo".to_string(),
            branch_tags: vec![1, 3],
            ext_call_sequence_shape: vec![("ext_io".to_string(), 0)],
            is_panic: false,
        };
        assert!(set.record_execution(key.clone(), vec![9, 9, 9, 9]));
        assert!(!set.record_execution(key.clone(), vec![5, 6]));
        assert!(!set.record_execution(key.clone(), vec![1, 2]));
        assert_eq!(set.len(), 1);
        assert_eq!(set.minimal_seed_for(&key), Some(&[1, 2][..]));
    }
}
