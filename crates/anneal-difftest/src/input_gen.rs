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

    /// Synthesizes up to `max_trials` deduplicated concolic trial plans from an
    /// initial concrete execution (`base_fields`, `guards`, `pins`), prioritizing
    /// external-call argument-pin negation (`neg_arg_pin_term`) under preserved
    /// prefix branch guards (`0..pin.before_guard_idx`) and earlier full call pins
    /// (`0..pin_idx`) before exploring pure oracle return-value perturbations or
    /// branch-guard flips.
    pub fn synthesize_concolic_trials(
        &self,
        base_fields: &BTreeMap<String, u128>,
        guards: &[ConcolicBranchGuard],
        pins: &[ArgPinConstraint],
        max_trials: usize,
        u: &mut Unstructured<'_>,
    ) -> Vec<ConcolicTrialPlan> {
        if max_trials == 0 {
            return Vec::new();
        }
        let mut working_pins: Vec<ArgPinConstraint> = pins.to_vec();
        let mut out: Vec<ConcolicTrialPlan> = Vec::with_capacity(max_trials);
        let mut seen_keys: BTreeSet<(Vec<(String, u128)>, Vec<(String, Vec<Vec<u8>>)>, Option<usize>)> =
            BTreeSet::new();

        let record_plan = |out: &mut Vec<ConcolicTrialPlan>,
                           seen: &mut BTreeSet<(
                               Vec<(String, u128)>,
                               Vec<(String, Vec<Vec<u8>>)>,
                               Option<usize>,
                           )>,
                           plan: ConcolicTrialPlan|
         -> bool {
            let field_key: Vec<(String, u128)> = plan
                .input_fields
                .iter()
                .map(|(k, &v)| (k.clone(), v))
                .collect();
            let sched_key: Vec<(String, Vec<Vec<u8>>)> = plan
                .schedule
                .callee_queues
                .iter()
                .map(|(k, q)| (k.clone(), q.iter().cloned().collect()))
                .collect();
            let panic_key = plan.schedule.global_panic_on_call;
            if seen.insert((field_key, sched_key, panic_key)) {
                out.push(plan);
                true
            } else {
                false
            }
        };

        // Seed the seen set with the initial concrete run so every synthesized trial is new.
        {
            let mut init_sched = EnvSchedule::new();
            for p in &working_pins {
                init_sched.push_callee_response(&p.callee, p.ret_bytes.clone());
            }
            let init_fields: Vec<(String, u128)> =
                base_fields.iter().map(|(k, &v)| (k.clone(), v)).collect();
            let init_sched_key: Vec<(String, Vec<Vec<u8>>)> = init_sched
                .callee_queues
                .iter()
                .map(|(k, q)| (k.clone(), q.iter().cloned().collect()))
                .collect();
            seen_keys.insert((init_fields, init_sched_key, None));
        }

        // Phase 1: Relax external-call argument pins (`neg_arg_pin_term`) across all call
        // sites in round-robin rounds while keeping prefix branch guards and earlier call
        // pins fixed. Capped at `ceil(max_trials / 2)` rounds so a call with a large
        // (`u16` / `u32` / `u64`) argument domain cannot starve Phase 2 (oracle return
        // perturbation) and Phase 3 (branch flips).
        let arg_round_cap = max_trials.div_ceil(2).max(1);
        let mut exhaust_reasons: Vec<Option<ArgPinFallbackReason>> =
            vec![None; working_pins.len()];
        let mut round = 0usize;
        while out.len() < max_trials
            && !working_pins.is_empty()
            && exhaust_reasons.iter().any(Option::is_none)
            && round < arg_round_cap
        {
            let mut made_progress = false;
            for pin_idx in 0..working_pins.len() {
                if out.len() >= max_trials {
                    break;
                }
                if exhaust_reasons[pin_idx].is_some() {
                    continue;
                }
                match relax_pin_constraint_with_generator(
                    self,
                    base_fields,
                    guards,
                    &working_pins,
                    pin_idx,
                    round,
                ) {
                    Some(RelaxPinResult::RelaxedArgPin {
                        callee,
                        prefix_guards,
                        prefix_pins,
                        new_arg_tuple,
                        input_field_overrides,
                        schedule,
                        ..
                    }) => {
                        working_pins[pin_idx].record_excluded_arg_tuple(new_arg_tuple.clone());
                        let mut merged_fields = base_fields.clone();
                        for (k, v) in input_field_overrides {
                            merged_fields.insert(k, v);
                        }
                        let plan = ConcolicTrialPlan {
                            phase: ConcolicTrialPhase::NegateCallArg {
                                pin_idx,
                                callee,
                                new_arg_tuple,
                            },
                            prefix_guards,
                            prefix_pins,
                            input_fields: merged_fields,
                            schedule,
                        };
                        if record_plan(&mut out, &mut seen_keys, plan) {
                            made_progress = true;
                        }
                        if working_pins[pin_idx].is_arg_domain_exhausted() {
                            exhaust_reasons[pin_idx] = Some(ArgPinFallbackReason::DomainExhausted);
                        }
                    }
                    Some(RelaxPinResult::FallbackReturnPerturbation { reason, .. }) => {
                        exhaust_reasons[pin_idx] = Some(reason);
                    }
                    None => {
                        exhaust_reasons[pin_idx] = Some(ArgPinFallbackReason::PrefixLocked);
                    }
                }
            }
            if !made_progress {
                break;
            }
            round += 1;
        }
        for reason_slot in &mut exhaust_reasons {
            if reason_slot.is_none() {
                *reason_slot = Some(ArgPinFallbackReason::NegationRoundCapReached);
            }
        }

        // Phase 2: Once distinct external-call arguments under the current prefix have been
        // explored (or for 0-arg / domain-exhausted call sites), explore oracle return-value
        // perturbations while preserving prefix branch guards and earlier call pins.
        let mut ret_round = 0usize;
        while out.len() < max_trials
            && !working_pins.is_empty()
            && ret_round < 4
        {
            let mut any_added = false;
            for pin_idx in 0..working_pins.len() {
                if out.len() >= max_trials {
                    break;
                }
                let fallback = build_return_perturbation_fallback(
                    self,
                    base_fields,
                    guards,
                    &working_pins,
                    pin_idx,
                    ret_round,
                );
                if let Some(RelaxPinResult::FallbackReturnPerturbation {
                    callee,
                    reason: default_reason,
                    prefix_guards,
                    prefix_pins,
                    input_field_overrides,
                    schedule,
                    ..
                }) = fallback
                {
                    let reason = exhaust_reasons[pin_idx].unwrap_or(default_reason);
                    let mut merged_fields = base_fields.clone();
                    for (k, v) in input_field_overrides {
                        merged_fields.insert(k, v);
                    }
                    let plan = ConcolicTrialPlan {
                        phase: ConcolicTrialPhase::PerturbOracleReturn {
                            pin_idx,
                            callee,
                            reason,
                        },
                        prefix_guards,
                        prefix_pins,
                        input_fields: merged_fields,
                        schedule,
                    };
                    if record_plan(&mut out, &mut seen_keys, plan) {
                        any_added = true;
                    }
                }
            }
            if !any_added {
                break;
            }
            ret_round += 1;
        }

        // Phase 3: Flip branch guards (`flip_branch_guard`) to steer execution into
        // sibling control-flow arms while preserving earlier guards and earlier pins.
        for guard_idx in (0..guards.len()).rev() {
            if out.len() >= max_trials {
                break;
            }
            for attempt in 0..4 {
                if out.len() >= max_trials {
                    break;
                }
                if let Some(flipped) = flip_branch_guard_with_generator(
                    self,
                    base_fields,
                    guards,
                    &working_pins,
                    guard_idx,
                    attempt,
                ) {
                    let plan = ConcolicTrialPlan {
                        phase: ConcolicTrialPhase::FlipBranchGuard {
                            guard_idx,
                            flipped_bits: flipped.flipped_bits,
                        },
                        prefix_guards: flipped.prefix_guards,
                        prefix_pins: flipped.prefix_pins,
                        input_fields: flipped.input_fields,
                        schedule: flipped.schedule,
                    };
                    let _ = record_plan(&mut out, &mut seen_keys, plan);
                }
            }
        }

        let _ = u;
        out
    }
}

/// Unsigned comparison operator of a [`ConcolicBranchGuard`] condition
/// `field <op> target_bits` (`condTerm`).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum ConcolicGuardOp {
    /// `field == target_bits`.
    #[default]
    Eq,
    /// `field != target_bits`.
    Ne,
    /// `field < target_bits` (unsigned).
    Lt,
    /// `field <= target_bits` (unsigned).
    Le,
    /// `field > target_bits` (unsigned).
    Gt,
    /// `field >= target_bits` (unsigned).
    Ge,
}

impl ConcolicGuardOp {
    /// Evaluates the unsigned comparison `lhs <op> rhs`.
    pub fn eval(self, lhs: u128, rhs: u128) -> bool {
        match self {
            Self::Eq => lhs == rhs,
            Self::Ne => lhs != rhs,
            Self::Lt => lhs < rhs,
            Self::Le => lhs <= rhs,
            Self::Gt => lhs > rhs,
            Self::Ge => lhs >= rhs,
        }
    }

    /// Returns all distinct `bit_width`-bit boundary witnesses `v` with
    /// `(v <op> target) == want`.
    pub fn witnesses(self, target: u128, want: bool, bit_width: u32) -> Vec<u128> {
        let mask = width_mask(bit_width);
        let t = target & mask;
        let mut out = Vec::new();
        for cand in [
            Some(t),
            t.checked_sub(1),
            t.checked_add(1).filter(|&v| v <= mask),
            t.checked_sub(2),
            t.checked_add(2).filter(|&v| v <= mask),
            Some(0),
            Some(1).filter(|&v| v <= mask),
            Some(mask),
        ]
        .into_iter()
        .flatten()
        {
            if self.eval(cand, t) == want && !out.contains(&cand) {
                out.push(cand);
            }
        }
        out
    }

    /// Returns a `bit_width`-bit witness `v` with `(v <op> target) == want`, or
    /// `None` when no such value exists (e.g. `v < 0` or `v > u32::MAX`).
    pub fn witness(self, target: u128, want: bool, bit_width: u32) -> Option<u128> {
        self.witnesses(target, want, bit_width).into_iter().next()
    }
}

/// Symbolic/concolic branch decision recorded at a `switchInt` / `if` / `match`
/// node along a concrete execution trace (modeled on `Nightowl.MultiInterp.BranchGuard`).
///
/// The raw condition is `condTerm := field <op> target_bits`; `taken` records
/// its concrete truth value, so [`Self::effective_term`] is `condTerm` when
/// `taken` and `¬ condTerm` otherwise (exactly `BranchGuard.effectiveTerm`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConcolicBranchGuard {
    /// Static or trace-order identifier of the branch guard.
    pub branch_id: usize,
    /// Concrete truth value of `condTerm` along the trace (`true` for the then/matched arm).
    pub taken: bool,
    /// Concrete `switchInt` arm tag recorded along the trace (`1` for true, `0` for false, or arm index).
    pub taken_tag: u32,
    /// Optional root input field or parameter name constrained by this branch guard (e.g. `"magic"`).
    pub field_name: Option<String>,
    /// Concrete scalar value of the guarded field along the trace (always satisfies
    /// [`Self::effective_term`] for guards built by [`Self::new_equality`] /
    /// [`Self::new_comparison`]).
    pub concrete_bits: u128,
    /// Target constant literal compared at this branch guard.
    pub target_bits: u128,
    /// Bit width of the guarded scalar (`1`, `8`, `16`, `32`, `64`, or `128`).
    pub bit_width: u32,
    /// Unsigned comparison operator of `condTerm` (`field <op> target_bits`).
    pub op: ConcolicGuardOp,
}

impl ConcolicBranchGuard {
    /// Constructs a branch guard for an equality comparison `field == target_bits`.
    pub fn new_equality(
        branch_id: usize,
        field_name: Option<String>,
        concrete_bits: u128,
        target_bits: u128,
        bit_width: u32,
    ) -> Self {
        Self::new_comparison(
            branch_id,
            field_name,
            ConcolicGuardOp::Eq,
            concrete_bits,
            target_bits,
            bit_width,
        )
    }

    /// Constructs a branch guard for `field <op> target_bits` whose concrete
    /// direction `taken` is the truth value of the comparison on `concrete_bits`.
    pub fn new_comparison(
        branch_id: usize,
        field_name: Option<String>,
        op: ConcolicGuardOp,
        concrete_bits: u128,
        target_bits: u128,
        bit_width: u32,
    ) -> Self {
        let mask = width_mask(bit_width);
        let c = concrete_bits & mask;
        let t = target_bits & mask;
        let taken = op.eval(c, t);
        Self {
            branch_id,
            taken,
            taken_tag: u32::from(taken),
            field_name,
            concrete_bits: c,
            target_bits: t,
            bit_width,
            op,
        }
    }

    /// Raw condition `condTerm` (`candidate <op> target_bits`) on `candidate_bits`.
    pub fn cond_term(&self, candidate_bits: u128) -> bool {
        let masked = candidate_bits & width_mask(self.bit_width);
        self.op.eval(masked, self.target_bits)
    }

    /// Polarity-adjusted path predicate (`condTerm` when `taken == true`, `¬ condTerm` when `false`).
    pub fn effective_term(&self, candidate_bits: u128) -> bool {
        let cond = self.cond_term(candidate_bits);
        if self.taken { cond } else { !cond }
    }

    /// Negated path predicate (`¬ condTerm` when `taken == true`, `condTerm` when `false`)
    /// asserted by [`flip_branch_guard`].
    pub fn flipped_term(&self, candidate_bits: u128) -> bool {
        !self.effective_term(candidate_bits)
    }

    /// The unique field value admitted by [`Self::effective_term`], if any
    /// (`field == t` taken or `field != t` not taken); inequality guards only
    /// constrain their field and never pin it to a single value.
    pub fn pinned_value(&self) -> Option<u128> {
        match (self.op, self.taken) {
            (ConcolicGuardOp::Eq, true) | (ConcolicGuardOp::Ne, false) => Some(self.target_bits),
            _ => None,
        }
    }
}

/// Symbolic/concolic equality pin recorded for an external call along a concrete trace,
/// separating argument-only pinning (`arg_pin_term` / `neg_arg_pin_term`) from full
/// `(arg, ret)` call pinning (`pin_term`), following `Nightowl.MultiInterp.PinConstraint`
/// (`cl/1022312290`).
///
/// - `arg_pin_term` (`argSym == argConc`): evaluates to `true` for 0-argument external
///   calls (`arg_tuple.is_empty()`), so `neg_arg_pin_term` (`¬ arg_pin_term`) is `false`
///   (unsatisfiable) on 0-argument calls.
/// - `pin_term` (`argSym == argConc && retSym == retConc`): asserted on earlier prefix calls
///   `0..pin_idx` during [`relax_pin_constraint`] so concrete replay reaches call `pin_idx`
///   along the exact same prefix with different arguments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArgPinConstraint {
    /// Zero-based slot identifier of the external call along the trace.
    pub slot_id: usize,
    /// External callee name (`fn`).
    pub callee: String,
    /// Number of [`ConcolicBranchGuard`]s recorded prior to this call along the trace (`beforeGuardIdx`).
    pub before_guard_idx: usize,
    /// Concrete argument tuple byte vectors passed to the external call (empty for 0-arg calls).
    pub arg_tuple: Vec<Vec<u8>>,
    /// Concrete return value bytes returned by the oracle on this call.
    pub ret_bytes: Vec<u8>,
    /// Per-argument scalar layouts defining the valid bit-pattern domain of each argument.
    pub arg_layouts: Vec<ScalarLayout>,
    /// Optional mapping from each argument index to the root input field name flowing into it.
    pub arg_field_sources: Vec<Option<String>>,
    /// Additional previously exercised argument tuples at this call site under the same prefix
    /// that [`ArgPinConstraint::neg_arg_pin_term`] excludes so successive relaxations discover
    /// distinct argument tuples.
    pub excluded_arg_tuples: Vec<Vec<Vec<u8>>>,
}

impl ArgPinConstraint {
    /// Creates an [`ArgPinConstraint`] for `callee` at `slot_id` preceded by `before_guard_idx`
    /// branch guards, inferring default unsigned scalar layouts from each argument's byte width.
    pub fn new(
        slot_id: usize,
        callee: impl Into<String>,
        before_guard_idx: usize,
        arg_tuple: Vec<Vec<u8>>,
        ret_bytes: Vec<u8>,
    ) -> Self {
        let arg_layouts = arg_tuple
            .iter()
            .map(|bytes| ScalarLayout::unsigned(bytes.len().max(1)))
            .collect();
        let arg_field_sources = vec![None; arg_tuple.len()];
        Self {
            slot_id,
            callee: callee.into(),
            before_guard_idx,
            arg_tuple,
            ret_bytes,
            arg_layouts,
            arg_field_sources,
            excluded_arg_tuples: Vec::new(),
        }
    }

    /// Sets explicit per-argument [`ScalarLayout`] domains (e.g. `bool_layout`, `u8`, or ranged integers).
    pub fn with_arg_layouts(mut self, layouts: Vec<ScalarLayout>) -> Self {
        self.arg_layouts = layouts;
        self
    }

    /// Associates root input field names with each argument position.
    pub fn with_arg_field_sources(mut self, sources: Vec<Option<String>>) -> Self {
        self.arg_field_sources = sources;
        self
    }

    /// Records an already-exercised argument tuple so future `neg_arg_pin_term` evaluations
    /// require a tuple distinct from both `self.arg_tuple` and all `excluded_arg_tuples`.
    pub fn record_excluded_arg_tuple(&mut self, tuple: Vec<Vec<u8>>) {
        if tuple != self.arg_tuple && !self.excluded_arg_tuples.contains(&tuple) {
            self.excluded_arg_tuples.push(tuple);
        }
    }

    /// Returns `true` when the external call takes 0 arguments (`arg_tuple.is_empty()`).
    #[inline]
    pub fn is_zero_arg(&self) -> bool {
        self.arg_tuple.is_empty()
    }

    /// Shifts `before_guard_idx` by `delta` when lifting pins out of a branch arm or
    /// continuation (`PinConstraint.shiftGuardIdx`), preserving `arg_pin_term`,
    /// `neg_arg_pin_term`, and `pin_term`.
    pub fn shift_guard_idx(&self, delta: usize) -> Self {
        let mut shifted = self.clone();
        shifted.before_guard_idx = self.before_guard_idx.saturating_add(delta);
        shifted
    }

    /// Argument-only equality conjunction `argSym₁ == argConc₁ ∧ ... ∧ true`
    /// (`mkExternArgPinTerm` in `Concolic.lean`).
    ///
    /// For a 0-argument call (`self.arg_tuple.is_empty()`), this is constantly `true`
    /// on the empty argument tuple `&[]`.
    pub fn arg_pin_term(&self, candidate_args: &[Vec<u8>]) -> bool {
        if self.arg_tuple.is_empty() {
            return candidate_args.is_empty();
        }
        candidate_args == self.arg_tuple.as_slice()
    }

    /// Negated argument pin constraint `¬ arg_pin_term` (plus exclusion of previously
    /// exercised argument tuples in `self.excluded_arg_tuples`), asserted by
    /// [`relax_pin_constraint`].
    ///
    /// For a 0-argument call, `arg_pin_term(&[])` is `true`, so `neg_arg_pin_term(&[])`
    /// is `false` (unsatisfiable).
    pub fn neg_arg_pin_term(&self, candidate_args: &[Vec<u8>]) -> bool {
        if self.arg_tuple.is_empty() || candidate_args.len() != self.arg_tuple.len() {
            return false;
        }
        !self.arg_pin_term(candidate_args)
            && !self
                .excluded_arg_tuples
                .iter()
                .any(|prev| prev.as_slice() == candidate_args)
    }

    /// Full call pin conjunction `argSym == argConc ∧ retSym == retConc`
    /// (`mkExternPinTerm` in `Concolic.lean`).
    pub fn pin_term(&self, candidate_args: &[Vec<u8>], candidate_ret: &[u8]) -> bool {
        self.arg_pin_term(candidate_args) && candidate_ret == self.ret_bytes.as_slice()
    }

    /// Exact cardinality of the valid argument-tuple domain when finite and representable
    /// in `u128` (`Some(1)` for 0-argument calls, `Some(2)` for a single `bool` argument,
    /// `Some(256)` for a single `u8` argument, etc.).
    pub fn domain_cardinality(&self) -> Option<u128> {
        if self.arg_tuple.is_empty() {
            return Some(1);
        }
        if self.arg_layouts.len() != self.arg_tuple.len() {
            return None;
        }
        let mut total: u128 = 1;
        for layout in &self.arg_layouts {
            let card: u128 = if layout.is_bool {
                2
            } else if layout.is_char {
                // Valid Unicode scalar values: 0..=0xD7FF and 0xE000..=0x10FFFF.
                0x10_FFFF - 0x800 + 1
            } else {
                let mask = width_mask(layout.bit_width());
                let start = layout.valid_start & mask;
                let end = (layout.valid_end & mask).max(start);
                end.checked_sub(start)?.checked_add(1)?
            };
            total = total.checked_mul(card)?;
        }
        Some(total)
    }

    /// Count of distinct valid argument tuples already pinned (`{self.arg_tuple} ∪ excluded_arg_tuples`).
    pub fn distinct_pinned_arg_tuples_count(&self) -> usize {
        if self.arg_tuple.is_empty() {
            return 1;
        }
        let mut seen: BTreeSet<&[Vec<u8>]> = BTreeSet::new();
        seen.insert(self.arg_tuple.as_slice());
        for t in &self.excluded_arg_tuples {
            if t.len() == self.arg_tuple.len() {
                seen.insert(t.as_slice());
            }
        }
        seen.len()
    }

    /// Returns `true` if `self` is a 0-argument call or if all valid argument tuples
    /// in `self.arg_layouts` have already been exercised.
    pub fn is_arg_domain_exhausted(&self) -> bool {
        if self.is_zero_arg() {
            return true;
        }
        if let Some(cap) = self.domain_cardinality() {
            (self.distinct_pinned_arg_tuples_count() as u128) >= cap
        } else {
            false
        }
    }

    /// Synthesizes a concrete argument tuple satisfying [`Self::neg_arg_pin_term`] and
    /// all `self.arg_layouts` bit-validity invariants while keeping any argument position
    /// whose source field is locked in `locked_fields` fixed (unless `self` has multiple
    /// arguments and another argument position is unlocked).
    ///
    /// Returns `None` without looping if the call takes 0 arguments, if all argument
    /// positions are locked by prefix constraints, or if the valid argument domain is
    /// exhausted.
    pub fn negate_arg_pin(
        &self,
        dict: &MirInputDictionary,
        locked_fields: &BTreeMap<String, u128>,
        attempt: usize,
    ) -> Option<Vec<Vec<u8>>> {
        self.negate_arg_pin_under_guards(dict, locked_fields, &[], attempt)
    }

    /// [`Self::negate_arg_pin`] that additionally asserts every prefix branch guard
    /// in `prefix_guards` (`guards.take beforeGuardIdx`): a value proposed for an
    /// argument sourced from field `f` must satisfy the `effective_term` of every
    /// guard on `f`, so inequality guards such as `payload_len > 1024` constrain
    /// (rather than pin) the argument.
    ///
    /// Argument positions that read the same source field always receive the same
    /// value (a tuple such as `(x, y)` with `x != y` is unrealizable when both
    /// positions read `payload_len`).
    pub fn negate_arg_pin_under_guards(
        &self,
        dict: &MirInputDictionary,
        locked_fields: &BTreeMap<String, u128>,
        prefix_guards: &[ConcolicBranchGuard],
        attempt: usize,
    ) -> Option<Vec<Vec<u8>>> {
        if self.is_zero_arg() || self.is_arg_domain_exhausted() {
            return None;
        }
        let arity = self.arg_tuple.len();
        let layout_of = |i: usize| {
            self.arg_layouts
                .get(i)
                .cloned()
                .unwrap_or_else(|| ScalarLayout::unsigned(self.arg_tuple[i].len().max(1)))
        };

        let valid_for_pos = |pos: usize, bits: u128| -> bool {
            let layout = layout_of(pos);
            let clamped = layout.clamp_to_valid_bits(bits);
            let encoded = encode_scalar_le_bytes(clamped, layout.size_bytes);
            clamped == bits && LayoutSpec::Scalar(layout).validate_bytes(&encoded).is_ok()
        };
        let valid_for_shared_field = |fname: &str, bits: u128| -> bool {
            let guards_ok = prefix_guards
                .iter()
                .filter(|g| g.field_name.as_deref() == Some(fname))
                .all(|g| g.effective_term(bits));
            guards_ok
                && (0..arity)
                    .filter(|&k| self.arg_field_sources.get(k).and_then(Option::as_deref) == Some(fname))
                    .all(|k| valid_for_pos(k, bits))
        };

        // One enumeration variable per distinct source field (shared by every position
        // reading it) plus one per unsourced position; each variable holds candidate
        // bit patterns (not yet encoded).
        let mut var_of_pos: Vec<usize> = Vec::with_capacity(arity);
        let mut var_values: Vec<Vec<u128>> = Vec::new();
        let mut var_by_field: BTreeMap<&str, usize> = BTreeMap::new();
        for i in 0..arity {
            let layout = layout_of(i);
            let field_source = self.arg_field_sources.get(i).and_then(Option::as_deref);
            if let Some(fname) = field_source
                && let Some(&v) = var_by_field.get(fname)
            {
                var_of_pos.push(v);
                continue;
            }
            let values: Vec<u128> = if let Some(fname) = field_source
                && let Some(&locked_bits) = locked_fields.get(fname)
            {
                // Locked by a prefix branch guard or an earlier call pin: verify that
                // `locked_bits` is valid for every position reading `fname` and satisfies
                // every prefix guard on `fname`.
                if valid_for_shared_field(fname, locked_bits) {
                    vec![locked_bits]
                } else {
                    Vec::new()
                }
            } else {
                let mut raw_cands: Vec<u128> =
                    candidate_arg_bytes_for_layout(&layout, field_source, &self.arg_tuple[i], dict)
                        .iter()
                        .map(|b| decode_scalar_le_bytes(b))
                        .collect();
                if let Some(fname) = field_source {
                    for g in prefix_guards
                        .iter()
                        .filter(|g| g.field_name.as_deref() == Some(fname))
                    {
                        if !raw_cands.contains(&g.concrete_bits) {
                            raw_cands.push(g.concrete_bits);
                        }
                        for w in g.op.witnesses(g.target_bits, g.taken, g.bit_width) {
                            if !raw_cands.contains(&w) {
                                raw_cands.push(w);
                            }
                        }
                    }
                }
                raw_cands
                    .into_iter()
                    .filter(|&bits| match field_source {
                        Some(fname) => valid_for_shared_field(fname, bits),
                        None => valid_for_pos(i, bits),
                    })
                    .collect()
            };
            if values.is_empty() {
                return None;
            }
            let v = var_values.len();
            var_values.push(values);
            if let Some(fname) = field_source {
                var_by_field.insert(fname, v);
            }
            var_of_pos.push(v);
        }

        // Enumerate variable assignments in deterministic mixed-radix order starting at
        // `attempt`, returning the first realizable tuple that satisfies `neg_arg_pin_term`.
        let total_combinations: usize = var_values
            .iter()
            .fold(1usize, |acc, v| acc.saturating_mul(v.len()).min(4096));
        for step in 0..total_combinations {
            let mut rem = step.wrapping_add(attempt);
            let assignment: Vec<u128> = var_values
                .iter()
                .map(|vals| {
                    let pick = vals[rem % vals.len()];
                    rem /= vals.len();
                    pick
                })
                .collect();
            let tuple: Vec<Vec<u8>> = (0..arity)
                .map(|i| {
                    let layout = layout_of(i);
                    encode_scalar_le_bytes(
                        layout.clamp_to_valid_bits(assignment[var_of_pos[i]]),
                        layout.size_bytes,
                    )
                })
                .collect();
            if self.neg_arg_pin_term(&tuple) {
                return Some(tuple);
            }
        }
        None
    }
}

fn decode_scalar_le_bytes(bytes: &[u8]) -> u128 {
    let n = bytes.len().min(16);
    let mut le = [0u8; 16];
    le[..n].copy_from_slice(&bytes[..n]);
    u128::from_le_bytes(le) & width_mask((n * 8) as u32)
}

fn encode_scalar_le_bytes(bits: u128, size_bytes: usize) -> Vec<u8> {
    let n = size_bytes.clamp(1, 16);
    let masked = bits & width_mask((n * 8) as u32);
    let le = masked.to_le_bytes();
    le[..n].to_vec()
}

fn candidate_arg_bytes_for_layout(
    layout: &ScalarLayout,
    field_source: Option<&str>,
    cur_bytes: &[u8],
    dict: &MirInputDictionary,
) -> Vec<Vec<u8>> {
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut push_unique = |bits: u128| {
        let valid = layout.clamp_to_valid_bits(bits);
        let bytes = encode_scalar_le_bytes(valid, layout.size_bytes);
        if LayoutSpec::Scalar(layout.clone()).validate_bytes(&bytes).is_ok()
            && !out.contains(&bytes)
        {
            out.push(bytes);
        }
    };

    let cur_bits = decode_scalar_le_bytes(cur_bytes);
    if layout.is_bool {
        push_unique(cur_bits ^ 1);
        push_unique(0);
        push_unique(1);
        return out;
    }

    if let Some(fname) = field_source
        && let Some(hints) = dict.field_hints.get(fname)
    {
        for &h in hints {
            push_unique(h);
            push_unique(h.saturating_sub(1));
            push_unique(h.saturating_add(1));
        }
    }

    let bits = layout.bit_width();
    for cand in dict.candidates_for_width(bits) {
        push_unique(cand);
    }

    for delta in [
        cur_bits ^ 1,
        cur_bits.wrapping_add(1),
        cur_bits.wrapping_sub(1),
        cur_bits.wrapping_add(2),
        cur_bits.wrapping_add(16),
        cur_bits.wrapping_add(0x80),
        cur_bits.wrapping_add(0x401),
        cur_bits ^ 0x55AA,
        cur_bits ^ 0x414E_4E4C,
    ] {
        push_unique(delta);
    }

    let span = layout.valid_end.saturating_sub(layout.valid_start);
    if span <= 256 {
        for v in layout.valid_start..=layout.valid_end {
            push_unique(v);
        }
    }
    out
}

/// Evaluates [`ArgPinConstraint::arg_pin_term`] on `candidate_args`.
#[inline]
pub fn arg_pin_term(pin: &ArgPinConstraint, candidate_args: &[Vec<u8>]) -> bool {
    pin.arg_pin_term(candidate_args)
}

/// Evaluates [`ArgPinConstraint::neg_arg_pin_term`] on `candidate_args`.
#[inline]
pub fn neg_arg_pin_term(pin: &ArgPinConstraint, candidate_args: &[Vec<u8>]) -> bool {
    pin.neg_arg_pin_term(candidate_args)
}

/// Evaluates [`ArgPinConstraint::pin_term`] on `(candidate_args, candidate_ret)`.
#[inline]
pub fn pin_term(
    pin: &ArgPinConstraint,
    candidate_args: &[Vec<u8>],
    candidate_ret: &[u8],
) -> bool {
    pin.pin_term(candidate_args, candidate_ret)
}

/// Synthesizes a new concrete argument tuple satisfying [`ArgPinConstraint::neg_arg_pin_term`].
#[inline]
pub fn negate_arg_pin(
    pin: &ArgPinConstraint,
    dict: &MirInputDictionary,
    locked_fields: &BTreeMap<String, u128>,
    attempt: usize,
) -> Option<Vec<Vec<u8>>> {
    pin.negate_arg_pin(dict, locked_fields, attempt)
}

/// Reason why [`relax_pin_constraint`] fell back from argument-pin negation to
/// oracle return-value perturbation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArgPinFallbackReason {
    /// The external call has 0 arguments (`arg_pin_term == true`, so `neg_arg_pin_term == false`).
    ZeroArgCall,
    /// Every valid argument tuple in the call's [`ScalarLayout`] domain has already been exercised.
    DomainExhausted,
    /// No argument tuple satisfying `neg_arg_pin_term` is reachable under the prefix: every
    /// field feeding the call's arguments is locked by a prefix branch guard or an earlier
    /// call pin, or no candidate input steers the arguments while preserving the prefix.
    PrefixLocked,
    /// The call's argument domain is not exhausted, but its argument-negation rounds were
    /// capped so the remaining trial budget can also explore oracle return values.
    NegationRoundCapReached,
}

/// Outcome of [`relax_pin_constraint`] (modeled on `Nightowl.MultiInterp.relaxPinConstraint`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RelaxPinResult {
    /// Successfully negated `target_pin.arg_pin_term` (`new_arg_tuple != target_pin.arg_tuple`)
    /// while holding all prefix branch guards `0..target_pin.before_guard_idx` and earlier
    /// full call pins `0..pin_idx` fixed. The target call's return value is left
    /// unconstrained (`relaxPinConstraint` asserts only `negArgPinTerm` on the target), so
    /// `schedule` pins only the prefix calls' returns and the target call passes through
    /// to the real callee on its new arguments.
    RelaxedArgPin {
        pin_idx: usize,
        callee: String,
        prefix_guards: Vec<ConcolicBranchGuard>,
        prefix_pins: Vec<ArgPinConstraint>,
        new_arg_tuple: Vec<Vec<u8>>,
        input_field_overrides: BTreeMap<String, u128>,
        schedule: EnvSchedule,
    },
    /// `neg_arg_pin_term` is unsatisfiable (0-arg call, exhausted argument domain, or
    /// prefix-locked fields): preserves prefix branch guards and earlier call pins while
    /// perturbing the oracle return value for call `pin_idx`.
    FallbackReturnPerturbation {
        pin_idx: usize,
        callee: String,
        reason: ArgPinFallbackReason,
        prefix_guards: Vec<ConcolicBranchGuard>,
        prefix_pins: Vec<ArgPinConstraint>,
        input_field_overrides: BTreeMap<String, u128>,
        schedule: EnvSchedule,
    },
}

/// Trial synthesized by [`flip_branch_guard`] (modeled on `Nightowl.MultiInterp.flipBranchGuard`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FlippedBranchTrial {
    pub guard_idx: usize,
    pub flipped_bits: u128,
    pub prefix_guards: Vec<ConcolicBranchGuard>,
    pub prefix_pins: Vec<ArgPinConstraint>,
    pub input_fields: BTreeMap<String, u128>,
    pub schedule: EnvSchedule,
}

/// Exploration phase that produced a [`ConcolicTrialPlan`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConcolicTrialPhase {
    /// Negated external-call argument pin `pin_idx` (`arg != prev_arg`) under fixed prefix guards/pins.
    NegateCallArg {
        pin_idx: usize,
        callee: String,
        new_arg_tuple: Vec<Vec<u8>>,
    },
    /// Perturbed external-call oracle return value at `pin_idx` after argument pins were covered or exhausted.
    PerturbOracleReturn {
        pin_idx: usize,
        callee: String,
        reason: ArgPinFallbackReason,
    },
    /// Flipped `switchInt` branch guard `guard_idx` while keeping earlier guards and pins fixed.
    FlipBranchGuard {
        guard_idx: usize,
        flipped_bits: u128,
    },
}

/// Complete concolic trial plan produced by [`EnvScheduleGenerator::synthesize_concolic_trials`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConcolicTrialPlan {
    pub phase: ConcolicTrialPhase,
    pub prefix_guards: Vec<ConcolicBranchGuard>,
    pub prefix_pins: Vec<ArgPinConstraint>,
    pub input_fields: BTreeMap<String, u128>,
    pub schedule: EnvSchedule,
}

/// Fields fixed to a single value by the prefix: guards whose `effective_term`
/// admits exactly one value ([`ConcolicBranchGuard::pinned_value`]) and every
/// source field of an earlier full call pin (`pinTerm` fixes its arguments).
///
/// Returns `None` when two prefix constraints lock the same field to different
/// values, or when a locked value violates any prefix guard on that field.
fn collect_prefix_locked_fields_checked(
    base_fields: &BTreeMap<String, u128>,
    prefix_guards: &[ConcolicBranchGuard],
    prefix_pins: &[ArgPinConstraint],
) -> Option<BTreeMap<String, u128>> {
    let mut locked = BTreeMap::new();
    for g in prefix_guards {
        if let Some(ref fname) = g.field_name
            && let Some(v) = g.pinned_value()
        {
            if let Some(&prev) = locked.get(fname) {
                if prev != v {
                    return None;
                }
            } else {
                locked.insert(fname.clone(), v);
            }
        }
    }
    for p in prefix_pins {
        for (arg_idx, src) in p.arg_field_sources.iter().enumerate() {
            if let Some(fname) = src {
                let pin_val = if let Some(arg_bytes) = p.arg_tuple.get(arg_idx) {
                    decode_scalar_le_bytes(arg_bytes)
                } else if let Some(&val) = base_fields.get(fname) {
                    val
                } else {
                    continue;
                };
                if let Some(&prev) = locked.get(fname) {
                    if prev != pin_val {
                        return None;
                    }
                } else {
                    locked.insert(fname.clone(), pin_val);
                }
            }
        }
    }
    // Verify that every locked field value satisfies all prefix guards on that field.
    for (fname, &val) in &locked {
        if !prefix_guards
            .iter()
            .filter(|g| g.field_name.as_ref() == Some(fname))
            .all(|g| g.effective_term(val))
        {
            return None;
        }
    }
    Some(locked)
}

/// Locked prefix fields plus, for every field merely *constrained* by a prefix
/// guard (e.g. `payload_len > 1024`) and absent from `base_fields`, a concrete
/// witness satisfying all prefix guards on that field, so a trial built from
/// these overrides alone still follows the prefix. Returns `None` if a
/// constrained field has mutually unsatisfiable prefix guards.
fn collect_prefix_field_overrides_checked(
    base_fields: &BTreeMap<String, u128>,
    prefix_guards: &[ConcolicBranchGuard],
    locked: &BTreeMap<String, u128>,
) -> Option<BTreeMap<String, u128>> {
    let mut overrides = locked.clone();
    for g in prefix_guards {
        let Some(ref fname) = g.field_name else {
            continue;
        };
        if let Some(&existing) = overrides.get(fname).or_else(|| base_fields.get(fname)) {
            if prefix_guards
                .iter()
                .filter(|pg| pg.field_name.as_ref() == Some(fname))
                .all(|pg| pg.effective_term(existing))
            {
                overrides.entry(fname.clone()).or_insert(existing);
                continue;
            }
            if locked.contains_key(fname) {
                return None;
            }
        }
        let mut candidates = Vec::new();
        for pg in prefix_guards
            .iter()
            .filter(|pg| pg.field_name.as_ref() == Some(fname))
        {
            if !candidates.contains(&pg.concrete_bits) {
                candidates.push(pg.concrete_bits);
            }
            for w in pg.op.witnesses(pg.target_bits, pg.taken, pg.bit_width) {
                if !candidates.contains(&w) {
                    candidates.push(w);
                }
            }
        }
        let valid = candidates.into_iter().find(|&c| {
            prefix_guards
                .iter()
                .filter(|pg| pg.field_name.as_ref() == Some(fname))
                .all(|pg| pg.effective_term(c))
        })?;
        overrides.insert(fname.clone(), valid);
    }
    Some(overrides)
}

fn prefix_pin_schedule(
    sched_gen: &EnvScheduleGenerator<'_>,
    prefix_pins: &[ArgPinConstraint],
) -> EnvSchedule {
    let mut schedule = EnvSchedule::new();
    for p in prefix_pins {
        let size = if p.ret_bytes.is_empty() {
            sched_gen.expected_callee_layout(&p.callee).total_size()
        } else {
            p.ret_bytes.len()
        };
        schedule.register_callee_return_size(&p.callee, size);
        schedule.push_callee_response(&p.callee, p.ret_bytes.clone());
    }
    schedule
}

fn build_return_perturbation_fallback(
    sched_gen: &EnvScheduleGenerator<'_>,
    base_fields: &BTreeMap<String, u128>,
    guards: &[ConcolicBranchGuard],
    pins: &[ArgPinConstraint],
    pin_idx: usize,
    attempt: usize,
) -> Option<RelaxPinResult> {
    let target_pin = pins.get(pin_idx)?;
    let guard_bound = target_pin.before_guard_idx.min(guards.len());
    let prefix_guards = guards[..guard_bound].to_vec();
    let prefix_pins = pins[..pin_idx].to_vec();
    let locked_fields =
        collect_prefix_locked_fields_checked(base_fields, &prefix_guards, &prefix_pins)?;
    let overrides =
        collect_prefix_field_overrides_checked(base_fields, &prefix_guards, &locked_fields)?;

    let reason = if target_pin.is_zero_arg() {
        ArgPinFallbackReason::ZeroArgCall
    } else if target_pin.is_arg_domain_exhausted() {
        ArgPinFallbackReason::DomainExhausted
    } else {
        ArgPinFallbackReason::PrefixLocked
    };

    let mut schedule = prefix_pin_schedule(sched_gen, &prefix_pins);
    let ret_layout = sched_gen.expected_callee_layout(&target_pin.callee);
    let ret_size = if target_pin.ret_bytes.is_empty() {
        ret_layout.total_size()
    } else {
        target_pin.ret_bytes.len()
    };
    if ret_size == 0 {
        return None;
    }
    schedule.register_callee_return_size(&target_pin.callee, ret_size);

    let scalar_ret = match &ret_layout {
        LayoutSpec::Scalar(s) if s.size_bytes == ret_size => s.clone(),
        _ => ScalarLayout::unsigned(ret_size.max(1)),
    };
    let ret_candidates = candidate_arg_bytes_for_layout(
        &scalar_ret,
        None,
        &target_pin.ret_bytes,
        sched_gen.dict,
    );
    let perturbed_ret = ret_candidates
        .iter()
        .cycle()
        .skip(attempt)
        .take(ret_candidates.len().max(1))
        .find(|cand| cand.as_slice() != target_pin.ret_bytes.as_slice())
        .cloned()?;
    schedule.push_callee_response(&target_pin.callee, perturbed_ret);

    Some(RelaxPinResult::FallbackReturnPerturbation {
        pin_idx,
        callee: target_pin.callee.clone(),
        reason,
        prefix_guards,
        prefix_pins,
        input_field_overrides: overrides,
        schedule,
    })
}

fn relax_pin_constraint_with_generator(
    sched_gen: &EnvScheduleGenerator<'_>,
    base_fields: &BTreeMap<String, u128>,
    guards: &[ConcolicBranchGuard],
    pins: &[ArgPinConstraint],
    pin_idx: usize,
    attempt: usize,
) -> Option<RelaxPinResult> {
    let target_pin = pins.get(pin_idx)?;
    let guard_bound = target_pin.before_guard_idx.min(guards.len());
    let prefix_guards = guards[..guard_bound].to_vec();
    let prefix_pins = pins[..pin_idx].to_vec();
    let locked_fields =
        collect_prefix_locked_fields_checked(base_fields, &prefix_guards, &prefix_pins)?;
    let base_overrides =
        collect_prefix_field_overrides_checked(base_fields, &prefix_guards, &locked_fields)?;

    if let Some(new_arg_tuple) = target_pin.negate_arg_pin_under_guards(
        sched_gen.dict,
        &locked_fields,
        &prefix_guards,
        attempt,
    ) {
        let mut overrides = base_overrides;
        for (arg_idx, bytes) in new_arg_tuple.iter().enumerate() {
            if let Some(Some(fname)) = target_pin.arg_field_sources.get(arg_idx)
                && !locked_fields.contains_key(fname)
            {
                overrides.insert(fname.clone(), decode_scalar_le_bytes(bytes));
            }
        }
        // Only the prefix pins' returns are scheduled: the target call's return is
        // unconstrained under `negArgPinTerm`, so it passes through to the real callee.
        let mut schedule = prefix_pin_schedule(sched_gen, &prefix_pins);
        let target_layout = sched_gen.expected_callee_layout(&target_pin.callee);
        let target_ret_size = if target_pin.ret_bytes.is_empty() {
            target_layout.total_size()
        } else {
            target_pin.ret_bytes.len()
        };
        schedule.register_callee_return_size(&target_pin.callee, target_ret_size);
        return Some(RelaxPinResult::RelaxedArgPin {
            pin_idx,
            callee: target_pin.callee.clone(),
            prefix_guards,
            prefix_pins,
            new_arg_tuple,
            input_field_overrides: overrides,
            schedule,
        });
    }

    build_return_perturbation_fallback(sched_gen, base_fields, guards, pins, pin_idx, attempt)
}

/// Relaxes the `pin_idx`-th external call pin in `pins` by asserting
/// `target_pin.neg_arg_pin_term` while holding all prior branch guards
/// (`guards[..target_pin.before_guard_idx]`) and earlier full call pins
/// (`pins[..pin_idx]`) fixed (modeled on `Nightowl.MultiInterp.relaxPinConstraint`).
pub fn relax_pin_constraint(
    guards: &[ConcolicBranchGuard],
    pins: &[ArgPinConstraint],
    pin_idx: usize,
    dict: &MirInputDictionary,
    attempt: usize,
) -> Option<RelaxPinResult> {
    let sched_gen = EnvScheduleGenerator::new(dict).with_panic_injection_pct(0);
    let base_fields = BTreeMap::new();
    relax_pin_constraint_with_generator(&sched_gen, &base_fields, guards, pins, pin_idx, attempt)
}

fn flip_branch_guard_with_generator(
    sched_gen: &EnvScheduleGenerator<'_>,
    base_fields: &BTreeMap<String, u128>,
    guards: &[ConcolicBranchGuard],
    pins: &[ArgPinConstraint],
    guard_idx: usize,
    attempt: usize,
) -> Option<FlippedBranchTrial> {
    let target_guard = guards.get(guard_idx)?;
    let prefix_guards = guards[..guard_idx].to_vec();
    let prefix_pins: Vec<ArgPinConstraint> = pins
        .iter()
        .filter(|p| p.before_guard_idx <= guard_idx)
        .cloned()
        .collect();
    let pin_locked = collect_prefix_locked_fields_checked(base_fields, &[], &prefix_pins)?;
    let locked = collect_prefix_locked_fields_checked(base_fields, &prefix_guards, &prefix_pins)?;
    let mut input_fields = base_fields.clone();
    for (k, v) in collect_prefix_field_overrides_checked(base_fields, &prefix_guards, &locked)? {
        input_fields.insert(k, v);
    }

    let satisfies_prefix = |bits: u128| -> bool {
        target_guard.flipped_term(bits)
            && target_guard.field_name.as_ref().is_none_or(|fname| {
                prefix_guards
                    .iter()
                    .filter(|g| g.field_name.as_ref() == Some(fname))
                    .all(|g| g.effective_term(bits))
                    && pin_locked.get(fname).is_none_or(|&lv| lv == bits)
            })
    };

    let layout = ScalarLayout::unsigned((target_guard.bit_width / 8).max(1) as usize);
    let cur_bytes = encode_scalar_le_bytes(target_guard.concrete_bits, layout.size_bytes);
    let mut cands: Vec<u128> = Vec::new();
    // The operator's own witnesses for the flipped polarity come first (e.g. `x = t`
    // and `x = t + 1` for an untaken `x >= t`, so an earlier `x != t` guard does not
    // block the flip), followed by prefix-guard boundary witnesses.
    for w in target_guard.op.witnesses(
        target_guard.target_bits,
        !target_guard.taken,
        target_guard.bit_width,
    ) {
        if !cands.contains(&w) {
            cands.push(w);
        }
    }
    if let Some(ref fname) = target_guard.field_name {
        for pg in prefix_guards
            .iter()
            .filter(|pg| pg.field_name.as_ref() == Some(fname))
        {
            for w in pg.op.witnesses(pg.target_bits, pg.taken, pg.bit_width) {
                if !cands.contains(&w) {
                    cands.push(w);
                }
            }
        }
    }
    for b in candidate_arg_bytes_for_layout(
        &layout,
        target_guard.field_name.as_deref(),
        &cur_bytes,
        sched_gen.dict,
    ) {
        let bits = decode_scalar_le_bytes(&b);
        if !cands.contains(&bits) {
            cands.push(bits);
        }
    }
    let flipped_bits = cands
        .iter()
        .cycle()
        .skip(attempt)
        .take(cands.len())
        .copied()
        .find(|&bits| satisfies_prefix(bits))?;

    if let Some(ref fname) = target_guard.field_name {
        input_fields.insert(fname.clone(), flipped_bits);
    }

    let schedule = prefix_pin_schedule(sched_gen, &prefix_pins);

    Some(FlippedBranchTrial {
        guard_idx,
        flipped_bits,
        prefix_guards,
        prefix_pins,
        input_fields,
        schedule,
    })
}

/// Flips the `guard_idx`-th branch guard in `guards` by asserting
/// `target_guard.flipped_term` while preserving all earlier branch guards
/// (`guards[..guard_idx]`) and all external call pins recorded up to `guard_idx`
/// (`pins.iter().filter(|p| p.before_guard_idx <= guard_idx)`), modeled on
/// `Nightowl.MultiInterp.flipBranchGuard`.
///
/// Returns `None` when the flip is unsatisfiable under that prefix: no candidate
/// value satisfies the flipped term together with every earlier guard on the same
/// field, or the guarded field feeds an earlier pinned call (whose `pinTerm`
/// fixes the field).
pub fn flip_branch_guard(
    base_fields: &BTreeMap<String, u128>,
    guards: &[ConcolicBranchGuard],
    pins: &[ArgPinConstraint],
    guard_idx: usize,
    dict: &MirInputDictionary,
    attempt: usize,
) -> Option<FlippedBranchTrial> {
    let sched_gen = EnvScheduleGenerator::new(dict).with_panic_injection_pct(0);
    flip_branch_guard_with_generator(&sched_gen, base_fields, guards, pins, guard_idx, attempt)
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

// ============================================================================
// Episode 2: Verus `#3539`-Style External `#[spec]` Postcondition Oracle
// Harnesses & Guo et al. (`arXiv:2611.11899`) Write-Chain Walk Coverage Bounds
// ============================================================================

/// Parameter descriptor for [`SpecContractOracleProbe`], binding a typed Rust
/// parameter (by value or `&mut T`) to its [`LayoutSpec`] and optional
/// frame-preserved fields.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecParamBinding {
    /// Parameter identifier in the target function and contract expressions.
    pub name: String,
    /// Pointee / value Rust type syntax (e.g. `"u32"`, `"[u32; 4]"`, `"CounterPair"`).
    /// When `is_mut_ref` is `true`, the target function signature receives `&mut <rust_ty>`.
    pub rust_ty: String,
    /// Exact layout specification used to validate and decode schedule bytes.
    pub layout: LayoutSpec,
    /// Whether this parameter is passed as `&mut <rust_ty>` so post-state
    /// mutations and `frame_preserved_fields` are checked after execution.
    pub is_mut_ref: bool,
    /// Struct field names on an `is_mut_ref` parameter that the contract
    /// frames as unmodified (`post.<field> == old(pre.<field>)` on occupied
    /// non-padding bytes).
    pub frame_preserved_fields: Vec<String>,
}

impl SpecParamBinding {
    /// Creates a by-value parameter binding.
    pub fn by_value(name: impl Into<String>, rust_ty: impl Into<String>, layout: LayoutSpec) -> Self {
        Self {
            name: name.into(),
            rust_ty: rust_ty.into(),
            layout,
            is_mut_ref: false,
            frame_preserved_fields: Vec::new(),
        }
    }

    /// Creates a mutable-reference (`&mut T`) parameter binding.
    pub fn mut_ref(name: impl Into<String>, rust_ty: impl Into<String>, layout: LayoutSpec) -> Self {
        Self {
            name: name.into(),
            rust_ty: rust_ty.into(),
            layout,
            is_mut_ref: true,
            frame_preserved_fields: Vec::new(),
        }
    }

    /// Declares struct field names on an `&mut Struct` parameter whose occupied
    /// bytes must remain identical between pre-state and post-state.
    pub fn with_frame_preserved_fields<I, S>(mut self, fields: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.frame_preserved_fields = fields.into_iter().map(Into::into).collect();
        self
    }
}

/// A single `requires(...)` or `ensures(...)` Boolean contract clause in a
/// [`SpecContractOracleProbe`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecContractAssertion {
    /// Human-readable label / diagnostic identifier for this clause.
    pub label: String,
    /// Rust Boolean expression evaluated in both [`SpecContractOracleProbe::synthesize_rust_probe`]
    /// and [`SpecContractOracleProbe::verify_spec_postcondition_against_schedule`].
    /// `ensures` expressions may reference `result` and `old(<expr>)`.
    pub rust_expr: String,
}

impl SpecContractAssertion {
    /// Constructs a new contract assertion with `label` and Boolean `rust_expr`.
    pub fn new(label: impl Into<String>, rust_expr: impl Into<String>) -> Self {
        Self {
            label: label.into(),
            rust_expr: rust_expr.into(),
        }
    }
}

/// Execution phase in which a runtime trap, overflow, UB guard, or panic occurred.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecExecPhase {
    /// Trap occurred while evaluating a `requires(...)` clause.
    Requires,
    /// Trap occurred while executing the target callee body or an `EnvSchedule` call.
    Body,
    /// Trap occurred while evaluating an `ensures(...)` clause.
    Ensures,
}

/// Kind of postcondition or frame violation detected after normal return.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpecViolationKind {
    /// An explicit `ensures(...)` Boolean predicate evaluated to `false`.
    EnsuresClause {
        clause_index: usize,
        label: String,
    },
    /// A framed field on an `&mut` parameter was mutated (`post != old`).
    FrameCondition {
        param: String,
        field: String,
    },
}

/// Concrete outcome of checking a [`SpecContractOracleProbe`] on one scheduled trial.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpecPostconditionVerdict {
    /// A `requires(...)` precondition evaluated to `false`; the callee was not
    /// executed and this trial is vacuously filtered (never counted as a hold).
    VacuouslyFiltered {
        failed_requires_index: usize,
        failed_requires_label: String,
    },
    /// `requires` held, the body returned normally, all framed fields were
    /// preserved, and every `ensures` predicate evaluated to `true`.
    VerifiedHold,
    /// The body returned normally, but an `ensures` clause or frame condition
    /// was violated (unsound spec or buggy implementation mutant killed).
    PostconditionViolation {
        kind: SpecViolationKind,
        detail: String,
    },
    /// Checked arithmetic overflow, shift-width UB (`shift >= bit_width`),
    /// division by zero, out-of-bounds index, assertion failure, or scheduled
    /// panic occurred while `requires` held (unsound/incomplete spec mutant killed).
    PanicOrTrap {
        phase: SpecExecPhase,
        detail: String,
    },
}

impl SpecPostconditionVerdict {
    /// Whether this trial exposed a postcondition violation, frame violation,
    /// or unguarded trap/panic (`PostconditionViolation` or `PanicOrTrap`).
    pub fn is_mutant_killed(&self) -> bool {
        matches!(
            self,
            Self::PostconditionViolation { .. } | Self::PanicOrTrap { .. }
        )
    }

    /// Whether this trial genuinely exercised the body and verified all
    /// postconditions and frame invariants (`VerifiedHold`).
    pub fn is_verified_hold(&self) -> bool {
        matches!(self, Self::VerifiedHold)
    }
}

/// Aggregated report across a batch of concrete schedule evaluations for a
/// [`SpecContractOracleProbe`].
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SpecBatchVerificationReport {
    pub total_trials: usize,
    pub verified_hold_count: usize,
    pub vacuously_filtered_count: usize,
    pub postcondition_violation_count: usize,
    pub panic_or_trap_count: usize,
    pub verdicts: Vec<SpecPostconditionVerdict>,
}

impl SpecBatchVerificationReport {
    /// Returns `true` iff zero violations/traps occurred AND at least one trial
    /// satisfied `requires` and reached `VerifiedHold` (preventing vacuous
    /// `requires(false)` specs from passing certification).
    pub fn is_sound_and_non_vacuous(&self) -> bool {
        self.postcondition_violation_count == 0
            && self.panic_or_trap_count == 0
            && self.verified_hold_count > 0
    }

    /// Returns `true` iff at least one trial killed the spec/implementation
    /// via `PostconditionViolation` or `PanicOrTrap`.
    pub fn is_mutant_killed(&self) -> bool {
        self.postcondition_violation_count > 0 || self.panic_or_trap_count > 0
    }
}

fn is_valid_rust_ident(s: &str) -> bool {
    syn::parse_str::<syn::Ident>(s).is_ok()
}

fn contains_old_call(expr: &Expr) -> bool {
    struct OldFinder(bool);
    impl<'ast> Visit<'ast> for OldFinder {
        fn visit_expr_call(&mut self, node: &'ast syn::ExprCall) {
            if let Expr::Path(ep) = &*node.func
                && ep.qself.is_none()
                && ep.path.leading_colon.is_none()
                && ep.path.segments.len() == 1
                && ep.path.segments[0].ident == "old"
            {
                self.0 = true;
                return;
            }
            visit::visit_expr_call(self, node);
        }
    }
    let mut finder = OldFinder(false);
    finder.visit_expr(expr);
    finder.0
}

fn validate_old_calls_in_ensures(expr: &Expr) -> Result<(), String> {
    struct OldValidator {
        in_old: bool,
        err: Option<String>,
    }
    impl<'ast> Visit<'ast> for OldValidator {
        fn visit_expr_path(&mut self, node: &'ast syn::ExprPath) {
            if self.err.is_some() {
                return;
            }
            if self.in_old
                && node.qself.is_none()
                && node.path.leading_colon.is_none()
                && node.path.segments.len() == 1
                && node.path.segments[0].ident == "result"
            {
                self.err = Some(
                    "`result` cannot be referenced inside `old(...)` because `result` does not exist in the pre-state"
                        .to_string(),
                );
                return;
            }
            visit::visit_expr_path(self, node);
        }

        fn visit_expr_call(&mut self, node: &'ast syn::ExprCall) {
            if self.err.is_some() {
                return;
            }
            if let Expr::Path(ep) = &*node.func
                && ep.qself.is_none()
                && ep.path.leading_colon.is_none()
                && ep.path.segments.len() == 1
                && ep.path.segments[0].ident == "old"
            {
                if self.in_old {
                    self.err = Some("nested `old(old(...))` is not permitted".to_string());
                    return;
                }
                if node.args.len() != 1 {
                    self.err = Some(format!(
                        "`old(...)` expects exactly 1 argument, got {}",
                        node.args.len()
                    ));
                    return;
                }
                self.in_old = true;
                visit::visit_expr(self, &node.args[0]);
                self.in_old = false;
                return;
            }
            visit::visit_expr_call(self, node);
        }
    }
    let mut v = OldValidator {
        in_old: false,
        err: None,
    };
    v.visit_expr(expr);
    match v.err {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

fn collect_pat_bound_idents(pat: &Pat, out: &mut BTreeSet<String>) {
    match pat {
        Pat::Ident(pi) => {
            out.insert(pi.ident.to_string());
            if let Some((_, sub)) = &pi.subpat {
                collect_pat_bound_idents(sub, out);
            }
        }
        Pat::Type(pt) => collect_pat_bound_idents(&pt.pat, out),
        Pat::Tuple(pt) => {
            for el in &pt.elems {
                collect_pat_bound_idents(el, out);
            }
        }
        Pat::Paren(pp) => collect_pat_bound_idents(&pp.pat, out),
        Pat::Reference(pr) => collect_pat_bound_idents(&pr.pat, out),
        _ => {}
    }
}

fn rewrite_old_expressions_for_rust(
    expr: &mut Expr,
    params: &[SpecParamBinding],
    needed_pre_params: &mut BTreeSet<String>,
    lazy_old_closures: &mut Vec<(String, String)>,
) {
    use quote::ToTokens;
    use syn::visit_mut::VisitMut;

    struct PreParamRewriter<'a> {
        params: &'a [SpecParamBinding],
        needed_pre_params: &'a mut BTreeSet<String>,
        shadowed: Vec<BTreeSet<String>>,
    }
    impl VisitMut for PreParamRewriter<'_> {
        fn visit_block_mut(&mut self, block: &mut syn::Block) {
            self.shadowed.push(BTreeSet::new());
            for stmt in &mut block.stmts {
                if let syn::Stmt::Local(loc) = stmt {
                    if let Some(init) = &mut loc.init {
                        self.visit_expr_mut(&mut init.expr);
                    }
                    if let Some(frame) = self.shadowed.last_mut() {
                        collect_pat_bound_idents(&loc.pat, frame);
                    }
                } else {
                    self.visit_stmt_mut(stmt);
                }
            }
            self.shadowed.pop();
        }

        fn visit_expr_mut(&mut self, node: &mut Expr) {
            if let Expr::Path(ep) = node
                && ep.qself.is_none()
                && ep.path.leading_colon.is_none()
                && ep.path.segments.len() == 1
            {
                let id_str = ep.path.segments[0].ident.to_string();
                let is_shadowed = self.shadowed.iter().any(|s| s.contains(&id_str));
                if !is_shadowed
                    && let Some(param) = self.params.iter().find(|p| p.name == id_str)
                {
                    self.needed_pre_params.insert(param.name.clone());
                    let pre_ident = syn::Ident::new(
                        &format!("__anneal_pre_{}", param.name),
                        proc_macro2::Span::call_site(),
                    );
                    if param.is_mut_ref {
                        *node = syn::parse_quote!((&#pre_ident));
                    } else {
                        *node = syn::parse_quote!(#pre_ident.clone());
                    }
                    return;
                }
            }
            syn::visit_mut::visit_expr_mut(self, node);
        }
    }

    struct Hoister<'a> {
        params: &'a [SpecParamBinding],
        needed_pre_params: &'a mut BTreeSet<String>,
        lazy_old_closures: &'a mut Vec<(String, String)>,
    }
    impl VisitMut for Hoister<'_> {
        fn visit_expr_mut(&mut self, node: &mut Expr) {
            if let Expr::Call(call) = node
                && let Expr::Path(ep) = &*call.func
                && ep.qself.is_none()
                && ep.path.leading_colon.is_none()
                && ep.path.segments.len() == 1
                && ep.path.segments[0].ident == "old"
                && call.args.len() == 1
            {
                let mut inner = call.args[0].clone();
                PreParamRewriter {
                    params: self.params,
                    needed_pre_params: self.needed_pre_params,
                    shadowed: Vec::new(),
                }
                .visit_expr_mut(&mut inner);
                let inner_tokens = inner.to_token_stream().to_string();
                let var_name = if let Some((existing, _)) = self
                    .lazy_old_closures
                    .iter()
                    .find(|(_, src)| src == &inner_tokens)
                {
                    existing.clone()
                } else {
                    let fresh = format!("__anneal_old_expr_{}", self.lazy_old_closures.len());
                    self.lazy_old_closures.push((fresh.clone(), inner_tokens));
                    fresh
                };
                let ident = syn::Ident::new(&var_name, proc_macro2::Span::call_site());
                *node = syn::parse_quote!(#ident());
                return;
            }
            syn::visit_mut::visit_expr_mut(self, node);
        }
    }
    Hoister {
        params,
        needed_pre_params,
        lazy_old_closures,
    }
    .visit_expr_mut(expr);
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum SpecEvalValue {
    Unit,
    Bool(bool),
    Char(char),
    Int {
        bits: u128,
        size_bytes: usize,
        signed: bool,
        untyped_lit: bool,
    },
    Struct {
        name: String,
        layout: LayoutSpec,
        raw_bytes: Vec<u8>,
        fields: BTreeMap<String, SpecEvalValue>,
    },
    Tuple {
        layout: LayoutSpec,
        raw_bytes: Vec<u8>,
        elems: Vec<SpecEvalValue>,
    },
    Array {
        layout: LayoutSpec,
        elem_layout: LayoutSpec,
        elem_stride: usize,
        raw_bytes: Vec<u8>,
        elems: Vec<SpecEvalValue>,
    },
}

impl SpecEvalValue {
    fn from_layout_bytes(layout: &LayoutSpec, raw: &[u8]) -> Result<Self, ScheduleError> {
        layout.validate_bytes(raw)?;
        Self::decode_validated(layout, raw)
    }

    fn decode_validated(layout: &LayoutSpec, raw: &[u8]) -> Result<Self, ScheduleError> {
        match layout {
            LayoutSpec::Scalar(s) => {
                if s.size_bytes == 0 {
                    return Ok(Self::Unit);
                }
                let bits = decode_scalar_le_bytes(&raw[..s.size_bytes]);
                if s.is_bool {
                    Ok(Self::Bool(bits != 0))
                } else if s.is_char {
                    let ch = char::from_u32(bits as u32).ok_or_else(|| {
                        ScheduleError::InvalidBitPattern {
                            context: "SpecEvalValue::Char".to_string(),
                            reason: format!("invalid Unicode scalar {bits:#x}"),
                        }
                    })?;
                    Ok(Self::Char(ch))
                } else {
                    Ok(Self::Int {
                        bits: bits & width_mask(s.bit_width()),
                        size_bytes: s.size_bytes,
                        signed: s.signed,
                        untyped_lit: false,
                    })
                }
            }
            LayoutSpec::Struct { name, fields, .. } => {
                let mut map = BTreeMap::new();
                for f in fields {
                    let end = f.offset + f.layout.total_size();
                    let v = Self::decode_validated(&f.layout, &raw[f.offset..end])?;
                    map.insert(f.name.clone(), v);
                }
                Ok(Self::Struct {
                    name: name.clone(),
                    layout: layout.clone(),
                    raw_bytes: raw.to_vec(),
                    fields: map,
                })
            }
            LayoutSpec::Tuple { elements, .. } => {
                let mut elems = Vec::with_capacity(elements.len());
                for (off, el_layout) in elements {
                    let end = *off + el_layout.total_size();
                    elems.push(Self::decode_validated(el_layout, &raw[*off..end])?);
                }
                Ok(Self::Tuple {
                    layout: layout.clone(),
                    raw_bytes: raw.to_vec(),
                    elems,
                })
            }
            LayoutSpec::Array {
                elem,
                elem_stride,
                len,
            } => {
                let mut elems = Vec::with_capacity(*len);
                let el_sz = elem.total_size();
                for i in 0..*len {
                    let start = i * (*elem_stride);
                    elems.push(Self::decode_validated(elem, &raw[start..start + el_sz])?);
                }
                Ok(Self::Array {
                    layout: layout.clone(),
                    elem_layout: (**elem).clone(),
                    elem_stride: *elem_stride,
                    raw_bytes: raw.to_vec(),
                    elems,
                })
            }
            LayoutSpec::Enum { .. } => Err(ScheduleError::InvalidBitPattern {
                context: "SpecEvalValue::Enum".to_string(),
                reason: "enum decoding in SpecContractOracleProbe requires struct/scalar/array/tuple layouts".to_string(),
            }),
        }
    }

    fn to_layout_bytes(&self) -> Vec<u8> {
        match self {
            Self::Unit => Vec::new(),
            Self::Bool(b) => vec![u8::from(*b)],
            Self::Char(c) => (*c as u32).to_le_bytes().to_vec(),
            Self::Int {
                bits, size_bytes, ..
            } => encode_scalar_le_bytes(*bits, *size_bytes),
            Self::Struct {
                layout: LayoutSpec::Struct { fields, .. },
                raw_bytes,
                fields: map,
                ..
            } => {
                let mut out = raw_bytes.clone();
                for f in fields {
                    if let Some(fv) = map.get(&f.name) {
                        let fb = fv.to_layout_bytes();
                        let end = f.offset + fb.len();
                        if end <= out.len() {
                            out[f.offset..end].copy_from_slice(&fb);
                        }
                    }
                }
                out
            }
            Self::Tuple {
                layout: LayoutSpec::Tuple { elements, .. },
                raw_bytes,
                elems,
            } => {
                let mut out = raw_bytes.clone();
                for ((off, _), ev) in elements.iter().zip(elems) {
                    let eb = ev.to_layout_bytes();
                    let end = *off + eb.len();
                    if end <= out.len() {
                        out[*off..end].copy_from_slice(&eb);
                    }
                }
                out
            }
            Self::Array {
                elem_stride,
                raw_bytes,
                elems,
                ..
            } => {
                let mut out = raw_bytes.clone();
                for (i, ev) in elems.iter().enumerate() {
                    let eb = ev.to_layout_bytes();
                    let start = i * (*elem_stride);
                    let end = start + eb.len();
                    if end <= out.len() {
                        out[start..end].copy_from_slice(&eb);
                    }
                }
                out
            }
            _ => Vec::new(),
        }
    }

    fn to_signed_i128(&self) -> Result<i128, String> {
        let Self::Int {
            bits,
            size_bytes,
            signed,
            ..
        } = self
        else {
            return Err(format!("expected integer value, got {self:?}"));
        };
        let bw = (*size_bytes * 8) as u32;
        let masked = *bits & width_mask(bw);
        if *signed {
            if bw >= 128 {
                Ok(masked as i128)
            } else {
                let sign_bit = 1u128 << (bw - 1);
                if (masked & sign_bit) != 0 {
                    let ext = masked | (!width_mask(bw));
                    Ok(ext as i128)
                } else {
                    Ok(masked as i128)
                }
            }
        } else if masked > i128::MAX as u128 {
            Err(format!(
                "unsigned 128-bit integer {masked} exceeds i128::MAX"
            ))
        } else {
            Ok(masked as i128)
        }
    }

    fn semantic_eq(&self, other: &Self) -> Result<bool, String> {
        let (lhs, rhs) = coerce_untyped_int_pair(self.clone(), other.clone())?;
        match (&lhs, &rhs) {
            (Self::Unit, Self::Unit) => Ok(true),
            (Self::Bool(a), Self::Bool(b)) => Ok(a == b),
            (Self::Char(a), Self::Char(b)) => Ok(a == b),
            (
                Self::Int {
                    bits: a,
                    size_bytes: sa,
                    signed: sga,
                    ..
                },
                Self::Int {
                    bits: b,
                    size_bytes: sb,
                    signed: sgb,
                    ..
                },
            ) => {
                if sa != sb || sga != sgb {
                    return Err(format!(
                        "mismatched integer types in equality: ({sa}B, signed={sga}) vs ({sb}B, signed={sgb})"
                    ));
                }
                let mask = width_mask((*sa * 8) as u32);
                Ok((a & mask) == (b & mask))
            }
            (
                Self::Struct {
                    name: na,
                    fields: fa,
                    ..
                },
                Self::Struct {
                    name: nb,
                    fields: fb,
                    ..
                },
            ) => {
                if na != nb || fa.len() != fb.len() {
                    return Err(format!(
                        "mismatched struct types in equality: `{na}` vs `{nb}`"
                    ));
                }
                for (k, va) in fa {
                    let Some(vb) = fb.get(k) else {
                        return Ok(false);
                    };
                    if !va.semantic_eq(vb)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (Self::Tuple { elems: ea, .. }, Self::Tuple { elems: eb, .. }) => {
                if ea.len() != eb.len() {
                    return Err(format!(
                        "mismatched tuple arities in equality: {} vs {}",
                        ea.len(),
                        eb.len()
                    ));
                }
                for (va, vb) in ea.iter().zip(eb.iter()) {
                    if !va.semantic_eq(vb)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (Self::Array { elems: ea, .. }, Self::Array { elems: eb, .. }) => {
                if ea.len() != eb.len() {
                    return Err(format!(
                        "mismatched array lengths in equality: {} vs {}",
                        ea.len(),
                        eb.len()
                    ));
                }
                for (va, vb) in ea.iter().zip(eb.iter()) {
                    if !va.semantic_eq(vb)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Err(format!(
                "mismatched value kinds in equality: {lhs:?} vs {rhs:?}"
            )),
        }
    }

    fn inferred_layout(&self) -> LayoutSpec {
        match self {
            Self::Unit => LayoutSpec::Tuple {
                total_size: 0,
                elements: Vec::new(),
            },
            Self::Bool(_) => LayoutSpec::Scalar(ScalarLayout::bool_layout()),
            Self::Char(_) => LayoutSpec::Scalar(ScalarLayout::char_layout()),
            Self::Int {
                size_bytes, signed, ..
            } => {
                if *signed {
                    LayoutSpec::Scalar(ScalarLayout::signed(*size_bytes))
                } else {
                    LayoutSpec::Scalar(ScalarLayout::unsigned(*size_bytes))
                }
            }
            Self::Struct { layout, .. }
            | Self::Tuple { layout, .. }
            | Self::Array { layout, .. } => layout.clone(),
        }
    }

    fn rust_literal(&self, rust_ty: &str) -> String {
        match self {
            Self::Unit => "()".to_string(),
            Self::Bool(b) => b.to_string(),
            Self::Char(c) => format!("{c:?}"),
            Self::Int {
                bits,
                size_bytes,
                signed,
                ..
            } => {
                let ty = rust_ty.trim();
                if *signed {
                    let bw = (*size_bytes * 8) as u32;
                    let min_v = if bw >= 128 {
                        i128::MIN
                    } else {
                        -(1i128 << (bw - 1))
                    };
                    let v = self.to_signed_i128().unwrap_or(0);
                    if v == min_v {
                        format!("{ty}::MIN")
                    } else {
                        format!("{v}{ty}")
                    }
                } else {
                    let masked = *bits & width_mask((*size_bytes * 8) as u32);
                    format!("{masked}{ty}")
                }
            }
            Self::Struct {
                name,
                layout: LayoutSpec::Struct { fields, .. },
                fields: map,
                ..
            } => {
                let mut parts = Vec::with_capacity(fields.len());
                for f in fields {
                    if let Some(v) = map.get(&f.name) {
                        let fty = default_rust_ty_for_layout(&f.layout);
                        parts.push(format!("{}: {}", f.name, v.rust_literal(&fty)));
                    }
                }
                format!("{name} {{ {} }}", parts.join(", "))
            }
            Self::Tuple {
                layout: LayoutSpec::Tuple { elements, .. },
                elems,
                ..
            } => {
                if elems.is_empty() {
                    return "()".to_string();
                }
                let parts: Vec<String> = elements
                    .iter()
                    .zip(elems)
                    .map(|((_, l), v)| v.rust_literal(&default_rust_ty_for_layout(l)))
                    .collect();
                format!("({},)", parts.join(", "))
            }
            Self::Array {
                elem_layout, elems, ..
            } => {
                let ety = default_rust_ty_for_layout(elem_layout);
                let parts: Vec<String> = elems.iter().map(|v| v.rust_literal(&ety)).collect();
                format!("[{}]", parts.join(", "))
            }
            _ => "()".to_string(),
        }
    }
}

fn default_rust_ty_for_layout(layout: &LayoutSpec) -> String {
    match layout {
        LayoutSpec::Scalar(s) => {
            if s.is_bool {
                "bool".to_string()
            } else if s.is_char {
                "char".to_string()
            } else {
                match (s.signed, s.size_bytes) {
                    (false, 1) => "u8".to_string(),
                    (false, 2) => "u16".to_string(),
                    (false, 4) => "u32".to_string(),
                    (false, 8) => "u64".to_string(),
                    (false, 16) => "u128".to_string(),
                    (true, 1) => "i8".to_string(),
                    (true, 2) => "i16".to_string(),
                    (true, 4) => "i32".to_string(),
                    (true, 8) => "i64".to_string(),
                    (true, 16) => "i128".to_string(),
                    _ => "u32".to_string(),
                }
            }
        }
        LayoutSpec::Struct { name, .. } => name.clone(),
        LayoutSpec::Array { elem, len, .. } => {
            format!("[{}; {}]", default_rust_ty_for_layout(elem), len)
        }
        LayoutSpec::Tuple { elements, .. } => {
            if elements.is_empty() {
                "()".to_string()
            } else {
                let inner: Vec<String> = elements
                    .iter()
                    .map(|(_, l)| default_rust_ty_for_layout(l))
                    .collect();
                format!("({},)", inner.join(", "))
            }
        }
        LayoutSpec::Enum { name, .. } => name.clone(),
    }
}

fn parse_scalar_type_spec(ty_name: &str) -> Option<(usize, bool)> {
    match ty_name.trim() {
        "u8" => Some((1, false)),
        "u16" => Some((2, false)),
        "u32" => Some((4, false)),
        "u64" | "usize" => Some((8, false)),
        "u128" => Some((16, false)),
        "i8" => Some((1, true)),
        "i16" => Some((2, true)),
        "i32" => Some((4, true)),
        "i64" | "isize" => Some((8, true)),
        "i128" => Some((16, true)),
        _ => None,
    }
}

fn coerce_untyped_int_pair(
    lhs: SpecEvalValue,
    rhs: SpecEvalValue,
) -> Result<(SpecEvalValue, SpecEvalValue), String> {
    match (&lhs, &rhs) {
        (
            SpecEvalValue::Int {
                size_bytes: ls,
                signed: lsig,
                untyped_lit: false,
                ..
            },
            SpecEvalValue::Int {
                bits: rb,
                signed: rsig,
                untyped_lit: true,
                ..
            },
        ) => {
            let coerced = coerce_lit_to_int(*rb, *rsig, *ls, *lsig)?;
            Ok((lhs, coerced))
        }
        (
            SpecEvalValue::Int {
                bits: lb,
                signed: lsig,
                untyped_lit: true,
                ..
            },
            SpecEvalValue::Int {
                size_bytes: rs,
                signed: rsig,
                untyped_lit: false,
                ..
            },
        ) => {
            let coerced = coerce_lit_to_int(*lb, *lsig, *rs, *rsig)?;
            Ok((coerced, rhs))
        }
        _ => Ok((lhs, rhs)),
    }
}

fn coerce_lit_to_int(
    raw_bits: u128,
    raw_signed: bool,
    target_size: usize,
    target_signed: bool,
) -> Result<SpecEvalValue, String> {
    let bw = (target_size * 8) as u32;
    let mask = width_mask(bw);
    if target_signed {
        let sval = if raw_signed {
            raw_bits as i128
        } else if raw_bits <= i128::MAX as u128 {
            raw_bits as i128
        } else {
            return Err(format!("integer literal {raw_bits} overflows signed {bw}-bit type"));
        };
        let min_v = if bw >= 128 { i128::MIN } else { -(1i128 << (bw - 1)) };
        let max_v = if bw >= 128 {
            i128::MAX
        } else {
            (1i128 << (bw - 1)) - 1
        };
        if sval < min_v || sval > max_v {
            return Err(format!(
                "integer literal {sval} out of range for signed {bw}-bit type"
            ));
        }
        Ok(SpecEvalValue::Int {
            bits: (sval as u128) & mask,
            size_bytes: target_size,
            signed: true,
            untyped_lit: false,
        })
    } else {
        if raw_signed && (raw_bits as i128) < 0 {
            return Err("negative integer literal coerced to unsigned type".to_string());
        }
        if raw_bits > mask {
            return Err(format!(
                "integer literal {raw_bits} overflows unsigned {bw}-bit type"
            ));
        }
        Ok(SpecEvalValue::Int {
            bits: raw_bits & mask,
            size_bytes: target_size,
            signed: false,
            untyped_lit: false,
        })
    }
}

struct SpecEvalContext<'a> {
    env: BTreeMap<String, SpecEvalValue>,
    pre_env: Option<&'a BTreeMap<String, SpecEvalValue>>,
    struct_layouts: &'a BTreeMap<String, LayoutSpec>,
    external_callees: &'a BTreeMap<String, LayoutSpec>,
    helper_fns: &'a BTreeMap<String, syn::ItemFn>,
    schedule: Option<&'a mut EnvSchedule>,
    call_index: usize,
    early_return: Option<SpecEvalValue>,
}

impl<'a> SpecEvalContext<'a> {
    fn eval_block(&mut self, block: &syn::Block) -> Result<SpecEvalValue, String> {
        let mut shadowed: Vec<(String, Option<SpecEvalValue>)> = Vec::new();
        let res = self.eval_block_inner(block, &mut shadowed);
        for (name, prev) in shadowed.into_iter().rev() {
            match prev {
                Some(v) => {
                    self.env.insert(name, v);
                }
                None => {
                    self.env.remove(&name);
                }
            }
        }
        res
    }

    fn eval_block_inner(
        &mut self,
        block: &syn::Block,
        shadowed: &mut Vec<(String, Option<SpecEvalValue>)>,
    ) -> Result<SpecEvalValue, String> {
        let mut last = SpecEvalValue::Unit;
        for stmt in &block.stmts {
            if let Some(ret) = &self.early_return {
                return Ok(ret.clone());
            }
            match stmt {
                syn::Stmt::Local(loc) => {
                    let init_expr = loc
                        .init
                        .as_ref()
                        .ok_or_else(|| "uninitialized local `let` binding in spec probe".to_string())?;
                    let val = self.eval_expr(&init_expr.expr)?;
                    self.bind_local_pattern(&loc.pat, None, val, shadowed)?;
                    last = SpecEvalValue::Unit;
                }
                syn::Stmt::Expr(e, semi) => {
                    let v = self.eval_expr(e)?;
                    if let Some(ret) = &self.early_return {
                        return Ok(ret.clone());
                    }
                    last = if semi.is_some() { SpecEvalValue::Unit } else { v };
                }
                syn::Stmt::Macro(m) => {
                    let m_name = m
                        .mac
                        .path
                        .segments
                        .last()
                        .map(|s| s.ident.to_string())
                        .unwrap_or_default();
                    self.eval_macro(&m_name, &m.mac.tokens)?;
                    last = SpecEvalValue::Unit;
                }
                syn::Stmt::Item(_) => {}
            }
        }
        if let Some(ret) = &self.early_return {
            return Ok(ret.clone());
        }
        Ok(last)
    }

    fn eval_macro(
        &mut self,
        m_name: &str,
        tokens: &proc_macro2::TokenStream,
    ) -> Result<SpecEvalValue, String> {
        match m_name {
            "panic" | "unreachable" | "todo" | "unimplemented" => {
                Err(format!("explicit `{m_name}!` panic: {tokens}"))
            }
            "assert" | "debug_assert" => {
                let parser = syn::punctuated::Punctuated::<Expr, syn::Token![,]>::parse_terminated;
                let args = syn::parse::Parser::parse2(parser, tokens.clone())
                    .map_err(|e| format!("invalid `{m_name}!` syntax: {e}"))?;
                let cond = args
                    .first()
                    .ok_or_else(|| format!("empty `{m_name}!()` invocation"))?;
                match self.eval_expr(cond)? {
                    SpecEvalValue::Bool(true) => Ok(SpecEvalValue::Unit),
                    SpecEvalValue::Bool(false) => Err(format!("assertion failed: `{tokens}`")),
                    other => Err(format!("non-boolean `{m_name}!` condition: {other:?}")),
                }
            }
            "assert_eq" | "debug_assert_eq" | "assert_ne" | "debug_assert_ne" => {
                let parser = syn::punctuated::Punctuated::<Expr, syn::Token![,]>::parse_terminated;
                let args = syn::parse::Parser::parse2(parser, tokens.clone())
                    .map_err(|e| format!("invalid `{m_name}!` syntax: {e}"))?;
                if args.len() < 2 {
                    return Err(format!("`{m_name}!` requires 2 arguments"));
                }
                let l = self.eval_expr(&args[0])?;
                let r = self.eval_expr(&args[1])?;
                let eq = l.semantic_eq(&r)?;
                let expect_eq = matches!(m_name, "assert_eq" | "debug_assert_eq");
                if eq == expect_eq {
                    Ok(SpecEvalValue::Unit)
                } else {
                    Err(format!("`{m_name}!` failed: {l:?} vs {r:?}"))
                }
            }
            other => Err(format!("unsupported macro `{other}!` in spec probe")),
        }
    }

    fn bind_local_pattern(
        &mut self,
        pat: &Pat,
        ty_hint: Option<&syn::Type>,
        val: SpecEvalValue,
        shadowed: &mut Vec<(String, Option<SpecEvalValue>)>,
    ) -> Result<(), String> {
        use quote::ToTokens;
        match pat {
            Pat::Wild(_) => {
                if let Some(ty) = ty_hint {
                    let _ = coerce_value_to_syn_type(val, ty)?;
                }
                Ok(())
            }
            Pat::Paren(pp) => self.bind_local_pattern(&pp.pat, ty_hint, val, shadowed),
            Pat::Type(pt) => self.bind_local_pattern(&pt.pat, Some(&pt.ty), val, shadowed),
            Pat::Ident(pi) => {
                let coerced = match ty_hint {
                    Some(ty) => coerce_value_to_syn_type(val, ty)?,
                    None => val,
                };
                let bind_name = pi.ident.to_string();
                if bind_name != "_" {
                    let prev = self.env.insert(bind_name.clone(), coerced);
                    shadowed.push((bind_name, prev));
                }
                Ok(())
            }
            Pat::Tuple(pt) => {
                let coerced = match ty_hint {
                    Some(ty) => coerce_value_to_syn_type(val, ty)?,
                    None => val,
                };
                if pt.elems.is_empty() {
                    return match coerced {
                        SpecEvalValue::Unit => Ok(()),
                        SpecEvalValue::Tuple { elems, .. } if elems.is_empty() => Ok(()),
                        other => Err(format!("expected unit `()` in tuple pattern, got {other:?}")),
                    };
                }
                let SpecEvalValue::Tuple { elems, .. } = coerced else {
                    return Err(format!(
                        "cannot destructure non-tuple value with `{}`",
                        pat.to_token_stream()
                    ));
                };
                if elems.len() != pt.elems.len() {
                    return Err(format!(
                        "tuple pattern arity mismatch: expected {}, got {}",
                        pt.elems.len(),
                        elems.len()
                    ));
                }
                let elem_tys: Option<Vec<&syn::Type>> = match ty_hint {
                    Some(syn::Type::Tuple(tt)) if tt.elems.len() == pt.elems.len() => {
                        Some(tt.elems.iter().collect())
                    }
                    _ => None,
                };
                for (idx, (sub_pat, sub_val)) in pt.elems.iter().zip(elems).enumerate() {
                    let sub_ty = elem_tys.as_ref().map(|v| v[idx]);
                    self.bind_local_pattern(sub_pat, sub_ty, sub_val, shadowed)?;
                }
                Ok(())
            }
            other => Err(format!(
                "unsupported local binding pattern `{}`",
                other.to_token_stream()
            )),
        }
    }

    fn resolve_place_path(&mut self, lhs: &Expr) -> Result<(String, Vec<SpecPlaceStep>), String> {
        use quote::ToTokens;
        match lhs {
            Expr::Paren(p) => self.resolve_place_path(&p.expr),
            Expr::Group(g) => self.resolve_place_path(&g.expr),
            Expr::Unary(un) if matches!(un.op, syn::UnOp::Deref(_)) => {
                self.resolve_place_path(&un.expr)
            }
            Expr::Path(ep) if ep.qself.is_none() && ep.path.segments.len() == 1 => {
                Ok((ep.path.segments[0].ident.to_string(), Vec::new()))
            }
            Expr::Field(ef) => {
                let (root, mut steps) = self.resolve_place_path(&ef.base)?;
                match &ef.member {
                    Member::Named(field_ident) => {
                        steps.push(SpecPlaceStep::StructField(field_ident.to_string()));
                    }
                    Member::Unnamed(idx) => {
                        steps.push(SpecPlaceStep::TupleField(idx.index as usize));
                    }
                }
                Ok((root, steps))
            }
            Expr::Index(ix) => {
                let (root, mut steps) = self.resolve_place_path(&ix.expr)?;
                let idx_val = self.eval_expr(&ix.index)?;
                let idx = match idx_val {
                    SpecEvalValue::Int {
                        bits, signed: false, ..
                    } => bits as usize,
                    _ => return Err("array index must be an unsigned integer".to_string()),
                };
                steps.push(SpecPlaceStep::ArrayIndex(idx));
                Ok((root, steps))
            }
            other => Err(format!(
                "unsupported assignment left-hand side `{}`",
                other.to_token_stream()
            )),
        }
    }

    fn assign_place(&mut self, lhs: &Expr, rhs: SpecEvalValue) -> Result<(), String> {
        let (root_name, steps) = self.resolve_place_path(lhs)?;
        let cur_root = self
            .env
            .get(&root_name)
            .cloned()
            .ok_or_else(|| format!("unknown assignment target `{root_name}`"))?;
        let next_root = write_at_place_steps(cur_root, &steps, rhs)?;
        self.env.insert(root_name, next_root);
        Ok(())
    }

    fn eval_expr(&mut self, expr: &Expr) -> Result<SpecEvalValue, String> {
        use quote::ToTokens;
        match expr {
            Expr::Paren(p) => self.eval_expr(&p.expr),
            Expr::Group(g) => self.eval_expr(&g.expr),
            Expr::Block(b) => self.eval_block(&b.block),
            Expr::Unsafe(u) => self.eval_block(&u.block),
            Expr::Return(r) => {
                let val = match &r.expr {
                    Some(e) => self.eval_expr(e)?,
                    None => SpecEvalValue::Unit,
                };
                self.early_return = Some(val.clone());
                Ok(val)
            }
            Expr::Tuple(t) => {
                if t.elems.is_empty() {
                    return Ok(SpecEvalValue::Unit);
                }
                let mut elems = Vec::with_capacity(t.elems.len());
                let mut layout_elems = Vec::with_capacity(t.elems.len());
                let mut offset = 0usize;
                for el_expr in &t.elems {
                    let ev = self.eval_expr(el_expr)?;
                    let el_layout = ev.inferred_layout();
                    let sz = el_layout.total_size();
                    layout_elems.push((offset, el_layout));
                    offset += sz;
                    elems.push(ev);
                }
                let layout = LayoutSpec::Tuple {
                    total_size: offset,
                    elements: layout_elems,
                };
                let provisional = SpecEvalValue::Tuple {
                    layout: layout.clone(),
                    raw_bytes: vec![0u8; offset],
                    elems: elems.clone(),
                };
                let raw_bytes = provisional.to_layout_bytes();
                Ok(SpecEvalValue::Tuple {
                    layout,
                    raw_bytes,
                    elems,
                })
            }
            Expr::Array(arr) => {
                let mut elems = Vec::with_capacity(arr.elems.len());
                for el_expr in &arr.elems {
                    elems.push(self.eval_expr(el_expr)?);
                }
                if let Some(typed_proto) = elems.iter().find(|v| {
                    !matches!(
                        v,
                        SpecEvalValue::Int {
                            untyped_lit: true,
                            ..
                        }
                    )
                }) {
                    let proto = typed_proto.clone();
                    for ev in &mut elems {
                        let (_, coerced) = coerce_untyped_int_pair(proto.clone(), ev.clone())?;
                        *ev = coerced;
                    }
                }
                let elem_layout = elems
                    .first()
                    .map(SpecEvalValue::inferred_layout)
                    .unwrap_or_else(|| LayoutSpec::Scalar(ScalarLayout::u32()));
                let elem_stride = elem_layout.total_size();
                let total_bytes = elem_stride.saturating_mul(elems.len());
                let layout = LayoutSpec::Array {
                    elem: Box::new(elem_layout.clone()),
                    elem_stride,
                    len: elems.len(),
                };
                let provisional = SpecEvalValue::Array {
                    layout: layout.clone(),
                    elem_layout: elem_layout.clone(),
                    elem_stride,
                    raw_bytes: vec![0u8; total_bytes],
                    elems: elems.clone(),
                };
                let raw_bytes = provisional.to_layout_bytes();
                Ok(SpecEvalValue::Array {
                    layout,
                    elem_layout,
                    elem_stride,
                    raw_bytes,
                    elems,
                })
            }
            Expr::Repeat(rep) => {
                let elem_val = self.eval_expr(&rep.expr)?;
                let len_val = self.eval_expr(&rep.len)?;
                let len = match len_val {
                    SpecEvalValue::Int {
                        bits, signed: false, ..
                    } if bits <= 4096 => bits as usize,
                    other => {
                        return Err(format!(
                            "unsupported repeat length `{other:?}` in array literal"
                        ));
                    }
                };
                let elem_layout = elem_val.inferred_layout();
                let elem_stride = elem_layout.total_size();
                let elems = vec![elem_val; len];
                let layout = LayoutSpec::Array {
                    elem: Box::new(elem_layout.clone()),
                    elem_stride,
                    len,
                };
                let provisional = SpecEvalValue::Array {
                    layout: layout.clone(),
                    elem_layout: elem_layout.clone(),
                    elem_stride,
                    raw_bytes: vec![0u8; elem_stride.saturating_mul(len)],
                    elems: elems.clone(),
                };
                let raw_bytes = provisional.to_layout_bytes();
                Ok(SpecEvalValue::Array {
                    layout,
                    elem_layout,
                    elem_stride,
                    raw_bytes,
                    elems,
                })
            }
            Expr::While(ew) => {
                const MAX_SPEC_LOOP_ITERS: usize = 10_000;
                let mut iters = 0usize;
                loop {
                    if let Some(ret) = &self.early_return {
                        return Ok(ret.clone());
                    }
                    match self.eval_expr(&ew.cond)? {
                        SpecEvalValue::Bool(false) => break,
                        SpecEvalValue::Bool(true) => {}
                        other => return Err(format!("non-boolean `while` condition: {other:?}")),
                    }
                    iters += 1;
                    if iters > MAX_SPEC_LOOP_ITERS {
                        return Err(format!(
                            "`while` loop exceeded bounded step budget ({MAX_SPEC_LOOP_ITERS} iterations)"
                        ));
                    }
                    let _ = self.eval_block(&ew.body)?;
                }
                Ok(SpecEvalValue::Unit)
            }
            Expr::Lit(el) => match &el.lit {
                Lit::Bool(b) => Ok(SpecEvalValue::Bool(b.value)),
                Lit::Char(c) => Ok(SpecEvalValue::Char(c.value())),
                Lit::Int(li) => {
                    let suffix = li.suffix();
                    if suffix.is_empty() {
                        let v = li
                            .base10_parse::<u128>()
                            .map_err(|e| format!("invalid int literal `{li}`: {e}"))?;
                        Ok(SpecEvalValue::Int {
                            bits: v,
                            size_bytes: 4,
                            signed: false,
                            untyped_lit: true,
                        })
                    } else if let Some((sz, sig)) = parse_scalar_type_spec(suffix) {
                        if sig {
                            let v = li
                                .base10_parse::<i128>()
                                .map_err(|e| format!("invalid signed int literal `{li}`: {e}"))?;
                            coerce_lit_to_int(v as u128, true, sz, true)
                        } else {
                            let v = li
                                .base10_parse::<u128>()
                                .map_err(|e| format!("invalid unsigned int literal `{li}`: {e}"))?;
                            coerce_lit_to_int(v, false, sz, false)
                        }
                    } else {
                        Err(format!("unsupported integer literal suffix `{suffix}`"))
                    }
                }
                other => Err(format!(
                    "unsupported literal `{}`",
                    other.to_token_stream()
                )),
            },
            Expr::Path(ep) if ep.qself.is_none() => {
                if ep.path.segments.len() == 1 {
                    let id = ep.path.segments[0].ident.to_string();
                    self.env
                        .get(&id)
                        .cloned()
                        .ok_or_else(|| format!("unknown variable `{id}`"))
                } else if ep.path.segments.len() == 2 {
                    let ty = ep.path.segments[0].ident.to_string();
                    let assoc = ep.path.segments[1].ident.to_string();
                    eval_assoc_int_const(&ty, &assoc)
                } else {
                    Err(format!("unsupported path `{}`", ep.to_token_stream()))
                }
            }
            Expr::Reference(r) => self.eval_expr(&r.expr),
            Expr::Unary(un) => match un.op {
                syn::UnOp::Deref(_) => self.eval_expr(&un.expr),
                syn::UnOp::Not(_) => match self.eval_expr(&un.expr)? {
                    SpecEvalValue::Bool(b) => Ok(SpecEvalValue::Bool(!b)),
                    SpecEvalValue::Int {
                        bits,
                        size_bytes,
                        signed,
                        untyped_lit,
                    } => {
                        let mask = width_mask((size_bytes * 8) as u32);
                        Ok(SpecEvalValue::Int {
                            bits: (!bits) & mask,
                            size_bytes,
                            signed,
                            untyped_lit,
                        })
                    }
                    other => Err(format!("cannot apply `!` to {other:?}")),
                },
                syn::UnOp::Neg(_) => {
                    if let Expr::Lit(ExprLit {
                        lit: Lit::Int(li), ..
                    }) = &*un.expr
                    {
                        let suffix = li.suffix();
                        let mag = li
                            .base10_parse::<u128>()
                            .map_err(|e| format!("invalid negated literal: {e}"))?;
                        if suffix.is_empty() {
                            if mag > (i128::MAX as u128) + 1 {
                                return Err("negated integer literal overflows i128".to_string());
                            }
                            let neg = (-(mag as i128)) as u128;
                            return Ok(SpecEvalValue::Int {
                                bits: neg,
                                size_bytes: 4,
                                signed: true,
                                untyped_lit: true,
                            });
                        } else if let Some((sz, true)) = parse_scalar_type_spec(suffix) {
                            let bw = (sz * 8) as u32;
                            let min_mag = if bw >= 128 {
                                1u128 << 127
                            } else {
                                1u128 << (bw - 1)
                            };
                            if mag > min_mag {
                                return Err(format!("negated literal `-{li}` overflows `{suffix}`"));
                            }
                            let neg = 0u128.wrapping_sub(mag) & width_mask(bw);
                            return Ok(SpecEvalValue::Int {
                                bits: neg,
                                size_bytes: sz,
                                signed: true,
                                untyped_lit: false,
                            });
                        }
                    }
                    let inner = self.eval_expr(&un.expr)?;
                    match inner {
                        SpecEvalValue::Int {
                            bits,
                            size_bytes,
                            signed,
                            ..
                        } => {
                            if !signed {
                                if bits == 0 {
                                    Ok(inner)
                                } else {
                                    Err("attempt to negate unsigned non-zero integer with overflow"
                                        .to_string())
                                }
                            } else {
                                let bw = (size_bytes * 8) as u32;
                                let sval = inner.to_signed_i128()?;
                                let min_v =
                                    if bw >= 128 { i128::MIN } else { -(1i128 << (bw - 1)) };
                                if sval == min_v {
                                    Err("attempt to negate with overflow".to_string())
                                } else {
                                    Ok(SpecEvalValue::Int {
                                        bits: ((-sval) as u128) & width_mask(bw),
                                        size_bytes,
                                        signed: true,
                                        untyped_lit: false,
                                    })
                                }
                            }
                        }
                        other => Err(format!("cannot negate {other:?}")),
                    }
                }
                _ => Err("unsupported unary operator".to_string()),
            },
            Expr::Field(ef) => {
                let base = self.eval_expr(&ef.base)?;
                match (&base, &ef.member) {
                    (SpecEvalValue::Struct { name, fields, .. }, Member::Named(id)) => fields
                        .get(&id.to_string())
                        .cloned()
                        .ok_or_else(|| format!("unknown field `{id}` on struct `{name}`")),
                    (SpecEvalValue::Tuple { elems, .. }, Member::Unnamed(idx)) => elems
                        .get(idx.index as usize)
                        .cloned()
                        .ok_or_else(|| format!("tuple index {} out of bounds", idx.index)),
                    _ => Err("invalid field projection".to_string()),
                }
            }
            Expr::Index(ix) => {
                let base = self.eval_expr(&ix.expr)?;
                let idx_val = self.eval_expr(&ix.index)?;
                let idx = match idx_val {
                    SpecEvalValue::Int {
                        bits, signed: false, ..
                    } => bits as usize,
                    _ => return Err("slice/array index must be unsigned".to_string()),
                };
                let SpecEvalValue::Array { elems, .. } = base else {
                    return Err("indexing requires array value".to_string());
                };
                if idx >= elems.len() {
                    return Err(format!(
                        "index out of bounds: the len is {} but the index is {idx}",
                        elems.len()
                    ));
                }
                Ok(elems[idx].clone())
            }
            Expr::Struct(es) => {
                let sname = es
                    .path
                    .segments
                    .last()
                    .map(|s| s.ident.to_string())
                    .unwrap_or_default();
                let layout = self
                    .struct_layouts
                    .get(&sname)
                    .cloned()
                    .ok_or_else(|| format!("unknown struct layout `{sname}`"))?;
                let LayoutSpec::Struct {
                    total_size,
                    fields: field_specs,
                    ..
                } = &layout
                else {
                    return Err(format!("`{sname}` layout is not a struct"));
                };
                let mut fvals = BTreeMap::new();
                let mut base_raw = vec![0u8; *total_size];
                for fv in &es.fields {
                    let Member::Named(fid) = &fv.member else {
                        return Err("unnamed struct literal field".to_string());
                    };
                    let fname = fid.to_string();
                    let fspec = field_specs
                        .iter()
                        .find(|f| f.name == fname)
                        .ok_or_else(|| format!("unknown field `{fname}` on struct `{sname}`"))?;
                    let val = coerce_value_to_layout(self.eval_expr(&fv.expr)?, &fspec.layout)?;
                    fvals.insert(fname, val);
                }
                if let Some(rest_expr) = &es.rest {
                    let rest_val = self.eval_expr(rest_expr)?;
                    let SpecEvalValue::Struct {
                        name: rest_name,
                        raw_bytes: rest_raw,
                        fields: rest_fields,
                        ..
                    } = rest_val
                    else {
                        return Err(format!(
                            "struct update `..` on `{sname}` requires a `{sname}` base"
                        ));
                    };
                    if rest_name != sname {
                        return Err(format!(
                            "struct update `..` base `{rest_name}` does not match `{sname}`"
                        ));
                    }
                    base_raw = rest_raw;
                    for (k, v) in rest_fields {
                        fvals.entry(k).or_insert(v);
                    }
                }
                for fspec in field_specs {
                    if !fvals.contains_key(&fspec.name) {
                        return Err(format!(
                            "missing field `{}` in struct literal `{sname}`",
                            fspec.name
                        ));
                    }
                }
                let provisional = SpecEvalValue::Struct {
                    name: sname.clone(),
                    layout: layout.clone(),
                    raw_bytes: base_raw,
                    fields: fvals.clone(),
                };
                let bytes = provisional.to_layout_bytes();
                Ok(SpecEvalValue::Struct {
                    name: sname,
                    layout,
                    raw_bytes: bytes,
                    fields: fvals,
                })
            }
            Expr::Assign(ea) => {
                let rhs = self.eval_expr(&ea.right)?;
                self.assign_place(&ea.left, rhs)?;
                Ok(SpecEvalValue::Unit)
            }
            Expr::If(ei) => {
                let cond = self.eval_expr(&ei.cond)?;
                let SpecEvalValue::Bool(taken) = cond else {
                    return Err(format!("non-boolean `if` condition: {cond:?}"));
                };
                if taken {
                    self.eval_block(&ei.then_branch)
                } else if let Some((_, else_expr)) = &ei.else_branch {
                    self.eval_expr(else_expr)
                } else {
                    Ok(SpecEvalValue::Unit)
                }
            }
            Expr::Cast(ec) => {
                let inner = self.eval_expr(&ec.expr)?;
                let ty_str = ec.ty.to_token_stream().to_string().replace(' ', "");
                let Some((target_sz, target_sig)) = parse_scalar_type_spec(&ty_str) else {
                    return Err(format!("unsupported cast target `{ty_str}`"));
                };
                let target_mask = width_mask((target_sz * 8) as u32);
                let raw_u128 = match inner {
                    SpecEvalValue::Bool(b) => u128::from(b),
                    SpecEvalValue::Char(c) => c as u32 as u128,
                    ref iv @ SpecEvalValue::Int { signed, bits, .. } => {
                        if signed {
                            (iv.to_signed_i128()? as u128) & target_mask
                        } else {
                            bits & target_mask
                        }
                    }
                    other => return Err(format!("cannot cast {other:?} to `{ty_str}`")),
                };
                Ok(SpecEvalValue::Int {
                    bits: raw_u128 & target_mask,
                    size_bytes: target_sz,
                    signed: target_sig,
                    untyped_lit: false,
                })
            }
            Expr::Binary(eb) => self.eval_binary(eb),
            Expr::MethodCall(mc) => self.eval_method_call(mc),
            Expr::Call(ec) => self.eval_call(ec),
            Expr::Macro(em) => {
                let m_name = em
                    .mac
                    .path
                    .segments
                    .last()
                    .map(|s| s.ident.to_string())
                    .unwrap_or_default();
                self.eval_macro(&m_name, &em.mac.tokens)
            }
            other => Err(format!(
                "unsupported expression `{}` in spec probe",
                other.to_token_stream()
            )),
        }
    }

    fn eval_binary(&mut self, eb: &ExprBinary) -> Result<SpecEvalValue, String> {
        // Short-circuit boolean `&&` and `||` identically to Rust!
        if matches!(eb.op, BinOp::And(_)) {
            return match self.eval_expr(&eb.left)? {
                SpecEvalValue::Bool(false) => Ok(SpecEvalValue::Bool(false)),
                SpecEvalValue::Bool(true) => match self.eval_expr(&eb.right)? {
                    SpecEvalValue::Bool(b) => Ok(SpecEvalValue::Bool(b)),
                    other => Err(format!("non-boolean rhs of `&&`: {other:?}")),
                },
                other => Err(format!("non-boolean lhs of `&&`: {other:?}")),
            };
        }
        if matches!(eb.op, BinOp::Or(_)) {
            return match self.eval_expr(&eb.left)? {
                SpecEvalValue::Bool(true) => Ok(SpecEvalValue::Bool(true)),
                SpecEvalValue::Bool(false) => match self.eval_expr(&eb.right)? {
                    SpecEvalValue::Bool(b) => Ok(SpecEvalValue::Bool(b)),
                    other => Err(format!("non-boolean rhs of `||`: {other:?}")),
                },
                other => Err(format!("non-boolean lhs of `||`: {other:?}")),
            };
        }

        // Compound assignment operators (`+=`, `-=`, `*=`, `/=`, `%=`, `<<=`, `>>=`, `^=`, `|=`, `&=`).
        let compound_bin = match eb.op {
            BinOp::AddAssign(_) => Some(BinOp::Add(Default::default())),
            BinOp::SubAssign(_) => Some(BinOp::Sub(Default::default())),
            BinOp::MulAssign(_) => Some(BinOp::Mul(Default::default())),
            BinOp::DivAssign(_) => Some(BinOp::Div(Default::default())),
            BinOp::RemAssign(_) => Some(BinOp::Rem(Default::default())),
            BinOp::BitXorAssign(_) => Some(BinOp::BitXor(Default::default())),
            BinOp::BitAndAssign(_) => Some(BinOp::BitAnd(Default::default())),
            BinOp::BitOrAssign(_) => Some(BinOp::BitOr(Default::default())),
            BinOp::ShlAssign(_) => Some(BinOp::Shl(Default::default())),
            BinOp::ShrAssign(_) => Some(BinOp::Shr(Default::default())),
            _ => None,
        };
        if let Some(op) = compound_bin {
            let rhs = self.eval_expr(&eb.right)?;
            let (root_name, steps) = self.resolve_place_path(&eb.left)?;
            let cur_root = self
                .env
                .get(&root_name)
                .cloned()
                .ok_or_else(|| format!("unknown assignment target `{root_name}`"))?;
            let cur_lhs = read_at_place_steps(&cur_root, &steps)?;
            let next = eval_pure_binary(&op, cur_lhs, rhs)?;
            let next_root = write_at_place_steps(cur_root, &steps, next)?;
            self.env.insert(root_name, next_root);
            return Ok(SpecEvalValue::Unit);
        }

        let lhs = self.eval_expr(&eb.left)?;
        let rhs = self.eval_expr(&eb.right)?;
        eval_pure_binary(&eb.op, lhs, rhs)
    }

    fn eval_method_call(&mut self, mc: &ExprMethodCall) -> Result<SpecEvalValue, String> {
        let recv = self.eval_expr(&mc.receiver)?;
        let m_name = mc.method.to_string();
        if m_name == "len" && mc.args.is_empty() {
            if let SpecEvalValue::Array { elems, .. } = recv {
                return Ok(SpecEvalValue::Int {
                    bits: elems.len() as u128,
                    size_bytes: 8,
                    signed: false,
                    untyped_lit: false,
                });
            }
        }
        let mut args = Vec::with_capacity(mc.args.len());
        for a in &mc.args {
            args.push(self.eval_expr(a)?);
        }
        eval_int_method(&m_name, recv, &args)
    }

    fn eval_call(&mut self, ec: &syn::ExprCall) -> Result<SpecEvalValue, String> {
        use quote::ToTokens;
        let callee_name = match &*ec.func {
            Expr::Path(ep) if ep.qself.is_none() => ep
                .path
                .segments
                .iter()
                .map(|s| s.ident.to_string())
                .collect::<Vec<_>>()
                .join("::"),
            other => {
                return Err(format!(
                    "unsupported call target `{}`",
                    other.to_token_stream()
                ));
            }
        };
        if callee_name == "old" {
            let Some(pre) = self.pre_env else {
                return Err("`old(...)` is only valid inside `ensures` postconditions".to_string());
            };
            if ec.args.len() != 1 {
                return Err("`old(...)` requires exactly 1 argument".to_string());
            }
            let mut sub_ctx = SpecEvalContext {
                env: pre.clone(),
                pre_env: None,
                struct_layouts: self.struct_layouts,
                external_callees: self.external_callees,
                helper_fns: self.helper_fns,
                schedule: None,
                call_index: 0,
                early_return: None,
            };
            return sub_ctx.eval_expr(&ec.args[0]);
        }

        // Helper function defined inside `type_defs_rust` (supports `&mut T` place writeback)!
        if let Some(helper_fn) = self.helper_fns.get(&callee_name) {
            if helper_fn.sig.inputs.len() != ec.args.len() {
                return Err(format!(
                    "helper `{callee_name}` expects {} argument(s), got {}",
                    helper_fn.sig.inputs.len(),
                    ec.args.len()
                ));
            }
            let mut fn_env = BTreeMap::new();
            let mut mut_writebacks: Vec<(String, String, Vec<SpecPlaceStep>)> = Vec::new();
            for (fn_arg, call_arg_expr) in helper_fn.sig.inputs.iter().zip(ec.args.iter()) {
                let syn::FnArg::Typed(pat_ty) = fn_arg else {
                    return Err(format!("unsupported `self` receiver in helper `{callee_name}`"));
                };
                let (pname, _) = extract_local_pat_and_ty(&pat_ty.pat)?;
                let (is_mut_ref, inner_ty): (bool, &syn::Type) = match &*pat_ty.ty {
                    syn::Type::Reference(tr) => (tr.mutability.is_some(), &tr.elem),
                    other => (false, other),
                };
                let arg_val = if is_mut_ref {
                    let place_expr = match call_arg_expr {
                        Expr::Reference(er) if er.mutability.is_some() => &*er.expr,
                        other => other,
                    };
                    let (root_name, steps) = self.resolve_place_path(place_expr)?;
                    let cur_root = self
                        .env
                        .get(&root_name)
                        .ok_or_else(|| format!("unknown `&mut` argument `{root_name}`"))?;
                    let cur_val = read_at_place_steps(cur_root, &steps)?;
                    if pname != "_" {
                        mut_writebacks.push((pname.clone(), root_name, steps));
                    }
                    cur_val
                } else {
                    self.eval_expr(call_arg_expr)?
                };
                let coerced = coerce_value_to_syn_type(arg_val, inner_ty)?;
                fn_env.insert(pname, coerced);
            }
            let mut sub_ctx = SpecEvalContext {
                env: fn_env,
                pre_env: None,
                struct_layouts: self.struct_layouts,
                external_callees: self.external_callees,
                helper_fns: self.helper_fns,
                schedule: self.schedule.as_deref_mut(),
                call_index: self.call_index,
                early_return: None,
            };
            let mut out_val = sub_ctx.eval_block(&helper_fn.block)?;
            self.call_index = sub_ctx.call_index;
            for (pname, root_name, steps) in mut_writebacks {
                if let Some(updated_param) = sub_ctx.env.remove(&pname) {
                    let cur_root = self
                        .env
                        .get(&root_name)
                        .cloned()
                        .ok_or_else(|| format!("missing caller binding `{root_name}` on writeback"))?;
                    let next_root = write_at_place_steps(cur_root, &steps, updated_param)?;
                    self.env.insert(root_name, next_root);
                }
            }
            if let syn::ReturnType::Type(_, ret_ty) = &helper_fn.sig.output {
                out_val = coerce_value_to_syn_type(out_val, ret_ty)?;
            }
            return Ok(out_val);
        }

        let mut evaled_args = Vec::with_capacity(ec.args.len());
        for a in &ec.args {
            evaled_args.push(self.eval_expr(a)?);
        }

        // Built-in unchecked intrinsics mirror Rust / Miri UB traps!
        let short_callee = callee_name
            .rsplit("::")
            .next()
            .unwrap_or(callee_name.as_str());
        if matches!(
            short_callee,
            "unchecked_shl"
                | "unchecked_shr"
                | "unchecked_add"
                | "unchecked_sub"
                | "unchecked_mul"
                | "wrapping_add"
                | "wrapping_sub"
                | "wrapping_mul"
                | "saturating_add"
                | "saturating_sub"
        ) && evaled_args.len() == 2
        {
            return match short_callee {
                "unchecked_shl" => {
                    eval_pure_binary(&BinOp::Shl(Default::default()), evaled_args[0].clone(), evaled_args[1].clone())
                }
                "unchecked_shr" => {
                    eval_pure_binary(&BinOp::Shr(Default::default()), evaled_args[0].clone(), evaled_args[1].clone())
                }
                "unchecked_add" => {
                    eval_pure_binary(&BinOp::Add(Default::default()), evaled_args[0].clone(), evaled_args[1].clone())
                }
                "unchecked_sub" => {
                    eval_pure_binary(&BinOp::Sub(Default::default()), evaled_args[0].clone(), evaled_args[1].clone())
                }
                "unchecked_mul" => {
                    eval_pure_binary(&BinOp::Mul(Default::default()), evaled_args[0].clone(), evaled_args[1].clone())
                }
                "wrapping_add" | "wrapping_sub" | "wrapping_mul" | "saturating_add" | "saturating_sub" => {
                    eval_int_method(short_callee, evaled_args[0].clone(), &[evaled_args[1].clone()])
                }
                _ => unreachable!(),
            };
        }

        // External boundary call dispatched against `EnvSchedule`!
        let Some(sched_ref) = self.schedule.as_deref_mut() else {
            return Err(format!(
                "call to external function `{callee_name}` without an active EnvSchedule"
            ));
        };
        let idx = self.call_index;
        self.call_index += 1;
        let declared_ret_layout = self.external_callees.get(&callee_name);
        let expected_sz = declared_ret_layout
            .map(LayoutSpec::total_size)
            .or_else(|| sched_ref.expected_return_size(&callee_name));
        match sched_ref.next_action(&callee_name, idx) {
            crate::instrument::EnvAction::PanicOnCall(p_idx) => {
                Err(format!("scheduled panic on `{callee_name}` at call {p_idx}"))
            }
            crate::instrument::EnvAction::ReturnBytes(bytes) => {
                let sz = expected_sz.unwrap_or(bytes.len());
                if bytes.len() != sz {
                    return Err(format!(
                        "EnvSchedule payload size mismatch for `{callee_name}`: expected {sz}, got {}",
                        bytes.len()
                    ));
                }
                if sz == 0 {
                    Ok(SpecEvalValue::Unit)
                } else if let Some(ext_layout) = declared_ret_layout {
                    SpecEvalValue::from_layout_bytes(ext_layout, &bytes)
                        .map_err(|e| format!("invalid EnvSchedule return bytes for `{callee_name}`: {e}"))
                } else {
                    let layout = LayoutSpec::Scalar(ScalarLayout::unsigned(sz));
                    SpecEvalValue::from_layout_bytes(&layout, &bytes)
                        .map_err(|e| format!("invalid EnvSchedule return bytes for `{callee_name}`: {e}"))
                }
            }
            crate::instrument::EnvAction::PassThrough => Err(format!(
                "EnvSchedule returned PassThrough (no scheduled payload) for external call `{callee_name}`"
            )),
        }
    }
}

fn extract_local_pat_and_ty(pat: &Pat) -> Result<(String, Option<String>), String> {
    use quote::ToTokens;
    match pat {
        Pat::Wild(_) => Ok(("_".to_string(), None)),
        Pat::Ident(pi) => Ok((pi.ident.to_string(), None)),
        Pat::Type(pt) => {
            let (name, _) = extract_local_pat_and_ty(&pt.pat)?;
            let ty_str = pt.ty.to_token_stream().to_string().replace(' ', "");
            Ok((name, Some(ty_str)))
        }
        other => Err(format!(
            "unsupported local binding pattern `{}`",
            other.to_token_stream()
        )),
    }
}

#[derive(Debug, Clone)]
enum SpecPlaceStep {
    StructField(String),
    TupleField(usize),
    ArrayIndex(usize),
}

fn read_at_place_steps(cur: &SpecEvalValue, steps: &[SpecPlaceStep]) -> Result<SpecEvalValue, String> {
    let Some((first, rest)) = steps.split_first() else {
        return Ok(cur.clone());
    };
    match (cur, first) {
        (SpecEvalValue::Struct { name, fields, .. }, SpecPlaceStep::StructField(fname)) => {
            let sub = fields
                .get(fname)
                .ok_or_else(|| format!("unknown field `{fname}` on `{name}`"))?;
            read_at_place_steps(sub, rest)
        }
        (SpecEvalValue::Tuple { elems, .. }, SpecPlaceStep::TupleField(tidx)) => {
            let sub = elems
                .get(*tidx)
                .ok_or_else(|| format!("tuple index {tidx} out of bounds"))?;
            read_at_place_steps(sub, rest)
        }
        (SpecEvalValue::Array { elems, .. }, SpecPlaceStep::ArrayIndex(aidx)) => {
            if *aidx >= elems.len() {
                return Err(format!(
                    "index out of bounds: the len is {} but the index is {aidx}",
                    elems.len()
                ));
            }
            read_at_place_steps(&elems[*aidx], rest)
        }
        _ => Err(format!("invalid place projection `{first:?}` on {cur:?}")),
    }
}

fn write_at_place_steps(
    cur: SpecEvalValue,
    steps: &[SpecPlaceStep],
    rhs: SpecEvalValue,
) -> Result<SpecEvalValue, String> {
    let Some((first, rest)) = steps.split_first() else {
        let (_, coerced) = coerce_untyped_int_pair(cur.clone(), rhs)?;
        return coerce_value_to_layout(coerced, &cur.inferred_layout());
    };
    match (cur, first) {
        (
            SpecEvalValue::Struct {
                name,
                layout,
                raw_bytes,
                mut fields,
            },
            SpecPlaceStep::StructField(fname),
        ) => {
            let prev = fields
                .get(fname)
                .cloned()
                .ok_or_else(|| format!("unknown field `{fname}` on `{name}`"))?;
            let next_field = write_at_place_steps(prev, rest, rhs)?;
            fields.insert(fname.clone(), next_field);
            let provisional = SpecEvalValue::Struct {
                name: name.clone(),
                layout: layout.clone(),
                raw_bytes,
                fields: fields.clone(),
            };
            let new_raw = provisional.to_layout_bytes();
            Ok(SpecEvalValue::Struct {
                name,
                layout,
                raw_bytes: new_raw,
                fields,
            })
        }
        (
            SpecEvalValue::Tuple {
                layout,
                raw_bytes,
                mut elems,
            },
            SpecPlaceStep::TupleField(tidx),
        ) => {
            if *tidx >= elems.len() {
                return Err(format!("tuple index {tidx} out of bounds"));
            }
            let next_el = write_at_place_steps(elems[*tidx].clone(), rest, rhs)?;
            elems[*tidx] = next_el;
            let provisional = SpecEvalValue::Tuple {
                layout: layout.clone(),
                raw_bytes,
                elems: elems.clone(),
            };
            let new_raw = provisional.to_layout_bytes();
            Ok(SpecEvalValue::Tuple {
                layout,
                raw_bytes: new_raw,
                elems,
            })
        }
        (
            SpecEvalValue::Array {
                layout,
                elem_layout,
                elem_stride,
                raw_bytes,
                mut elems,
            },
            SpecPlaceStep::ArrayIndex(aidx),
        ) => {
            if *aidx >= elems.len() {
                return Err(format!(
                    "index out of bounds: the len is {} but the index is {aidx}",
                    elems.len()
                ));
            }
            let next_el = write_at_place_steps(elems[*aidx].clone(), rest, rhs)?;
            elems[*aidx] = next_el;
            let provisional = SpecEvalValue::Array {
                layout: layout.clone(),
                elem_layout: elem_layout.clone(),
                elem_stride,
                raw_bytes,
                elems: elems.clone(),
            };
            let new_raw = provisional.to_layout_bytes();
            Ok(SpecEvalValue::Array {
                layout,
                elem_layout,
                elem_stride,
                raw_bytes: new_raw,
                elems,
            })
        }
        (other, step) => Err(format!(
            "cannot assign through `{step:?}` on value {other:?}"
        )),
    }
}

fn coerce_value_to_layout(val: SpecEvalValue, layout: &LayoutSpec) -> Result<SpecEvalValue, String> {
    match (val, layout) {
        (
            SpecEvalValue::Int {
                bits,
                signed: rsig,
                untyped_lit: true,
                ..
            },
            LayoutSpec::Scalar(sc),
        ) if !sc.is_bool && !sc.is_char && sc.size_bytes > 0 => {
            coerce_lit_to_int(bits, rsig, sc.size_bytes, sc.signed)
        }
        (
            SpecEvalValue::Tuple { elems, .. },
            LayoutSpec::Tuple {
                total_size,
                elements,
            },
        ) if elems.len() == elements.len() => {
            let mut coerced_elems = Vec::with_capacity(elems.len());
            for (ev, (_, el_layout)) in elems.into_iter().zip(elements.iter()) {
                coerced_elems.push(coerce_value_to_layout(ev, el_layout)?);
            }
            let provisional = SpecEvalValue::Tuple {
                layout: layout.clone(),
                raw_bytes: vec![0u8; *total_size],
                elems: coerced_elems.clone(),
            };
            let raw_bytes = provisional.to_layout_bytes();
            Ok(SpecEvalValue::Tuple {
                layout: layout.clone(),
                raw_bytes,
                elems: coerced_elems,
            })
        }
        (
            SpecEvalValue::Array { elems, .. },
            LayoutSpec::Array {
                elem,
                elem_stride,
                len,
            },
        ) if elems.len() == *len => {
            let mut coerced_elems = Vec::with_capacity(elems.len());
            for ev in elems {
                coerced_elems.push(coerce_value_to_layout(ev, elem)?);
            }
            let provisional = SpecEvalValue::Array {
                layout: layout.clone(),
                elem_layout: (**elem).clone(),
                elem_stride: *elem_stride,
                raw_bytes: vec![0u8; elem_stride.saturating_mul(*len)],
                elems: coerced_elems.clone(),
            };
            let raw_bytes = provisional.to_layout_bytes();
            Ok(SpecEvalValue::Array {
                layout: layout.clone(),
                elem_layout: (**elem).clone(),
                elem_stride: *elem_stride,
                raw_bytes,
                elems: coerced_elems,
            })
        }
        (other, _) => Ok(other),
    }
}

fn coerce_value_to_syn_type(val: SpecEvalValue, ty: &syn::Type) -> Result<SpecEvalValue, String> {
    use quote::ToTokens;
    match ty {
        syn::Type::Paren(tp) => coerce_value_to_syn_type(val, &tp.elem),
        syn::Type::Group(tg) => coerce_value_to_syn_type(val, &tg.elem),
        syn::Type::Reference(tr) => coerce_value_to_syn_type(val, &tr.elem),
        syn::Type::Tuple(tt) => {
            if tt.elems.is_empty() {
                return Ok(val);
            }
            let SpecEvalValue::Tuple { elems, .. } = val else {
                return Ok(val);
            };
            if elems.len() != tt.elems.len() {
                return Err(format!(
                    "tuple type arity mismatch: expected {}, got {}",
                    tt.elems.len(),
                    elems.len()
                ));
            }
            let mut coerced_elems = Vec::with_capacity(elems.len());
            let mut layout_elems = Vec::with_capacity(elems.len());
            let mut offset = 0usize;
            for (ev, el_ty) in elems.into_iter().zip(tt.elems.iter()) {
                let cv = coerce_value_to_syn_type(ev, el_ty)?;
                let el_layout = cv.inferred_layout();
                let sz = el_layout.total_size();
                layout_elems.push((offset, el_layout));
                offset += sz;
                coerced_elems.push(cv);
            }
            let layout = LayoutSpec::Tuple {
                total_size: offset,
                elements: layout_elems,
            };
            let provisional = SpecEvalValue::Tuple {
                layout: layout.clone(),
                raw_bytes: vec![0u8; offset],
                elems: coerced_elems.clone(),
            };
            let raw_bytes = provisional.to_layout_bytes();
            Ok(SpecEvalValue::Tuple {
                layout,
                raw_bytes,
                elems: coerced_elems,
            })
        }
        syn::Type::Array(ta) => {
            let SpecEvalValue::Array { elems, .. } = val else {
                return Ok(val);
            };
            let mut coerced_elems = Vec::with_capacity(elems.len());
            for ev in elems {
                coerced_elems.push(coerce_value_to_syn_type(ev, &ta.elem)?);
            }
            let elem_layout = coerced_elems
                .first()
                .map(SpecEvalValue::inferred_layout)
                .unwrap_or_else(|| LayoutSpec::Scalar(ScalarLayout::u32()));
            let elem_stride = elem_layout.total_size();
            let len = coerced_elems.len();
            let layout = LayoutSpec::Array {
                elem: Box::new(elem_layout.clone()),
                elem_stride,
                len,
            };
            let provisional = SpecEvalValue::Array {
                layout: layout.clone(),
                elem_layout: elem_layout.clone(),
                elem_stride,
                raw_bytes: vec![0u8; elem_stride.saturating_mul(len)],
                elems: coerced_elems.clone(),
            };
            let raw_bytes = provisional.to_layout_bytes();
            Ok(SpecEvalValue::Array {
                layout,
                elem_layout,
                elem_stride,
                raw_bytes,
                elems: coerced_elems,
            })
        }
        other => {
            let ty_str = other.to_token_stream().to_string().replace(' ', "");
            if let Some((sz, sig)) = parse_scalar_type_spec(&ty_str)
                && let SpecEvalValue::Int {
                    bits,
                    signed: rsig,
                    untyped_lit: true,
                    ..
                } = val
            {
                coerce_lit_to_int(bits, rsig, sz, sig)
            } else {
                Ok(val)
            }
        }
    }
}

fn eval_assoc_int_const(ty: &str, assoc: &str) -> Result<SpecEvalValue, String> {
    let Some((sz, sig)) = parse_scalar_type_spec(ty) else {
        return Err(format!("unknown integer type `{ty}` for `{ty}::{assoc}`"));
    };
    let bw = (sz * 8) as u32;
    let mask = width_mask(bw);
    match (sig, assoc) {
        (false, "MIN") => Ok(SpecEvalValue::Int {
            bits: 0,
            size_bytes: sz,
            signed: false,
            untyped_lit: false,
        }),
        (false, "MAX") => Ok(SpecEvalValue::Int {
            bits: mask,
            size_bytes: sz,
            signed: false,
            untyped_lit: false,
        }),
        (true, "MIN") => {
            let min_bits = if bw >= 128 {
                1u128 << 127
            } else {
                1u128 << (bw - 1)
            };
            Ok(SpecEvalValue::Int {
                bits: min_bits,
                size_bytes: sz,
                signed: true,
                untyped_lit: false,
            })
        }
        (true, "MAX") => {
            let max_bits = if bw >= 128 {
                (1u128 << 127) - 1
            } else {
                (1u128 << (bw - 1)) - 1
            };
            Ok(SpecEvalValue::Int {
                bits: max_bits,
                size_bytes: sz,
                signed: true,
                untyped_lit: false,
            })
        }
        (_, "BITS") => Ok(SpecEvalValue::Int {
            bits: bw as u128,
            size_bytes: 4,
            signed: false,
            untyped_lit: false,
        }),
        _ => Err(format!("unsupported associated constant `{ty}::{assoc}`")),
    }
}

fn eval_pure_binary(
    op: &BinOp,
    lhs: SpecEvalValue,
    rhs: SpecEvalValue,
) -> Result<SpecEvalValue, String> {
    if matches!(op, BinOp::Shl(_) | BinOp::Shr(_)) {
        let SpecEvalValue::Int {
            bits: lb,
            size_bytes: lsz,
            signed: lsig,
            ..
        } = lhs
        else {
            return Err("shift lhs must be an integer".to_string());
        };
        let bw = (lsz * 8) as u32;
        let mask = width_mask(bw);
        let shift_amt: u32 = match &rhs {
            SpecEvalValue::Int { signed: true, .. } => {
                let sv = rhs.to_signed_i128()?;
                if sv < 0 || (sv as u128) >= (bw as u128) {
                    return Err(format!(
                        "attempt to shift with overflow (shift={sv}, bit_width={bw})"
                    ));
                }
                sv as u32
            }
            SpecEvalValue::Int {
                bits: rb,
                signed: false,
                ..
            } => {
                if *rb >= (bw as u128) {
                    return Err(format!(
                        "attempt to shift with overflow (shift={rb}, bit_width={bw})"
                    ));
                }
                *rb as u32
            }
            _ => return Err("shift rhs must be an integer".to_string()),
        };
        let out_bits = match op {
            BinOp::Shl(_) => (lb << shift_amt) & mask,
            BinOp::Shr(_) => {
                if lsig {
                    let sv = lhs.to_signed_i128()?;
                    ((sv >> shift_amt) as u128) & mask
                } else {
                    (lb & mask) >> shift_amt
                }
            }
            _ => unreachable!(),
        };
        return Ok(SpecEvalValue::Int {
            bits: out_bits,
            size_bytes: lsz,
            signed: lsig,
            untyped_lit: false,
        });
    }

    let (lhs, rhs) = coerce_untyped_int_pair(lhs, rhs)?;
    if matches!(op, BinOp::Eq(_) | BinOp::Ne(_)) {
        let eq = lhs.semantic_eq(&rhs)?;
        return Ok(SpecEvalValue::Bool(if matches!(op, BinOp::Eq(_)) {
            eq
        } else {
            !eq
        }));
    }

    let (
        SpecEvalValue::Int {
            bits: lb,
            size_bytes: lsz,
            signed: lsig,
            untyped_lit: l_untyped,
        },
        SpecEvalValue::Int {
            bits: rb,
            size_bytes: rsz,
            signed: rsig,
            untyped_lit: r_untyped,
        },
    ) = (&lhs, &rhs)
    else {
        return Err(format!("invalid binary operands {lhs:?} and {rhs:?}"));
    };
    if lsz != rsz || lsig != rsig {
        return Err(format!(
            "mismatched integer types in binary op: ({lsz}B, signed={lsig}) vs ({rsz}B, signed={rsig})"
        ));
    }
    let bw = (*lsz * 8) as u32;
    let mask = width_mask(bw);
    let both_untyped = *l_untyped && *r_untyped;

    if *lsig {
        let la = lhs.to_signed_i128()?;
        let ra = rhs.to_signed_i128()?;
        let min_v = if bw >= 128 { i128::MIN } else { -(1i128 << (bw - 1)) };
        let max_v = if bw >= 128 {
            i128::MAX
        } else {
            (1i128 << (bw - 1)) - 1
        };
        let check_range = |v: Option<i128>, label: &str| -> Result<SpecEvalValue, String> {
            let val = v.ok_or_else(|| format!("attempt to {label} with overflow"))?;
            if val < min_v || val > max_v {
                return Err(format!("attempt to {label} with overflow"));
            }
            Ok(SpecEvalValue::Int {
                bits: (val as u128) & mask,
                size_bytes: *lsz,
                signed: true,
                untyped_lit: both_untyped,
            })
        };
        match op {
            BinOp::Add(_) => check_range(la.checked_add(ra), "add"),
            BinOp::Sub(_) => check_range(la.checked_sub(ra), "subtract"),
            BinOp::Mul(_) => check_range(la.checked_mul(ra), "multiply"),
            BinOp::Div(_) => {
                if ra == 0 {
                    return Err("attempt to divide by zero".to_string());
                }
                if la == min_v && ra == -1 {
                    return Err("attempt to divide with overflow".to_string());
                }
                check_range(la.checked_div(ra), "divide")
            }
            BinOp::Rem(_) => {
                if ra == 0 {
                    return Err("attempt to calculate the remainder with a divisor of zero".to_string());
                }
                if la == min_v && ra == -1 {
                    return Err("attempt to calculate the remainder with overflow".to_string());
                }
                check_range(la.checked_rem(ra), "rem")
            }
            BinOp::BitXor(_) => Ok(SpecEvalValue::Int {
                bits: (lb ^ rb) & mask,
                size_bytes: *lsz,
                signed: true,
                untyped_lit: both_untyped,
            }),
            BinOp::BitAnd(_) => Ok(SpecEvalValue::Int {
                bits: (lb & rb) & mask,
                size_bytes: *lsz,
                signed: true,
                untyped_lit: both_untyped,
            }),
            BinOp::BitOr(_) => Ok(SpecEvalValue::Int {
                bits: (lb | rb) & mask,
                size_bytes: *lsz,
                signed: true,
                untyped_lit: both_untyped,
            }),
            BinOp::Lt(_) => Ok(SpecEvalValue::Bool(la < ra)),
            BinOp::Le(_) => Ok(SpecEvalValue::Bool(la <= ra)),
            BinOp::Gt(_) => Ok(SpecEvalValue::Bool(la > ra)),
            BinOp::Ge(_) => Ok(SpecEvalValue::Bool(la >= ra)),
            _ => Err("unsupported signed binary operator".to_string()),
        }
    } else {
        let la = *lb & mask;
        let ra = *rb & mask;
        let check_u = |v: Option<u128>, label: &str| -> Result<SpecEvalValue, String> {
            let val = v.ok_or_else(|| format!("attempt to {label} with overflow"))?;
            if val > mask {
                return Err(format!("attempt to {label} with overflow"));
            }
            Ok(SpecEvalValue::Int {
                bits: val & mask,
                size_bytes: *lsz,
                signed: false,
                untyped_lit: both_untyped,
            })
        };
        match op {
            BinOp::Add(_) => check_u(la.checked_add(ra), "add"),
            BinOp::Sub(_) => check_u(la.checked_sub(ra), "subtract"),
            BinOp::Mul(_) => check_u(la.checked_mul(ra), "multiply"),
            BinOp::Div(_) => {
                if ra == 0 {
                    return Err("attempt to divide by zero".to_string());
                }
                Ok(SpecEvalValue::Int {
                    bits: la / ra,
                    size_bytes: *lsz,
                    signed: false,
                    untyped_lit: both_untyped,
                })
            }
            BinOp::Rem(_) => {
                if ra == 0 {
                    return Err("attempt to calculate the remainder with a divisor of zero".to_string());
                }
                Ok(SpecEvalValue::Int {
                    bits: la % ra,
                    size_bytes: *lsz,
                    signed: false,
                    untyped_lit: both_untyped,
                })
            }
            BinOp::BitXor(_) => Ok(SpecEvalValue::Int {
                bits: (la ^ ra) & mask,
                size_bytes: *lsz,
                signed: false,
                untyped_lit: both_untyped,
            }),
            BinOp::BitAnd(_) => Ok(SpecEvalValue::Int {
                bits: (la & ra) & mask,
                size_bytes: *lsz,
                signed: false,
                untyped_lit: both_untyped,
            }),
            BinOp::BitOr(_) => Ok(SpecEvalValue::Int {
                bits: (la | ra) & mask,
                size_bytes: *lsz,
                signed: false,
                untyped_lit: both_untyped,
            }),
            BinOp::Lt(_) => Ok(SpecEvalValue::Bool(la < ra)),
            BinOp::Le(_) => Ok(SpecEvalValue::Bool(la <= ra)),
            BinOp::Gt(_) => Ok(SpecEvalValue::Bool(la > ra)),
            BinOp::Ge(_) => Ok(SpecEvalValue::Bool(la >= ra)),
            _ => Err("unsupported unsigned binary operator".to_string()),
        }
    }
}

fn eval_int_method(
    m_name: &str,
    recv: SpecEvalValue,
    args: &[SpecEvalValue],
) -> Result<SpecEvalValue, String> {
    let SpecEvalValue::Int {
        bits: lb,
        size_bytes: lsz,
        signed: lsig,
        ..
    } = recv
    else {
        return Err(format!("method `{m_name}` called on non-integer {recv:?}"));
    };
    let bw = (lsz * 8) as u32;
    let mask = width_mask(bw);
    let la = lb & mask;

    if args.is_empty() {
        return match m_name {
            "wrapping_neg" => Ok(SpecEvalValue::Int {
                bits: 0u128.wrapping_sub(la) & mask,
                size_bytes: lsz,
                signed: lsig,
                untyped_lit: false,
            }),
            "count_ones" => Ok(SpecEvalValue::Int {
                bits: la.count_ones() as u128,
                size_bytes: 4,
                signed: false,
                untyped_lit: false,
            }),
            "leading_zeros" => Ok(SpecEvalValue::Int {
                bits: (la.leading_zeros() - (128 - bw)) as u128,
                size_bytes: 4,
                signed: false,
                untyped_lit: false,
            }),
            "trailing_zeros" => Ok(SpecEvalValue::Int {
                bits: if la == 0 {
                    bw as u128
                } else {
                    la.trailing_zeros() as u128
                },
                size_bytes: 4,
                signed: false,
                untyped_lit: false,
            }),
            _ => Err(format!("unsupported 0-arg integer method `{m_name}`")),
        };
    }

    if args.len() == 1 {
        if matches!(m_name, "wrapping_shl" | "wrapping_shr") {
            let SpecEvalValue::Int { bits: rb, .. } = args[0] else {
                return Err(format!("`{m_name}` expects integer shift count"));
            };
            let sh = (rb as u32) & (bw - 1);
            let out_bits = if m_name == "wrapping_shl" {
                (la << sh) & mask
            } else if lsig {
                let sv = recv.to_signed_i128()?;
                ((sv >> sh) as u128) & mask
            } else {
                la >> sh
            };
            return Ok(SpecEvalValue::Int {
                bits: out_bits,
                size_bytes: lsz,
                signed: lsig,
                untyped_lit: false,
            });
        }

        let (lhs_c, rhs_c) = coerce_untyped_int_pair(recv, args[0].clone())?;
        let (
            SpecEvalValue::Int { bits: l_bits, .. },
            SpecEvalValue::Int { bits: r_bits, .. },
        ) = (&lhs_c, &rhs_c)
        else {
            return Err(format!("`{m_name}` expects matching integer argument"));
        };
        let lu = *l_bits & mask;
        let ru = *r_bits & mask;
        return match m_name {
            "wrapping_add" => Ok(SpecEvalValue::Int {
                bits: lu.wrapping_add(ru) & mask,
                size_bytes: lsz,
                signed: lsig,
                untyped_lit: false,
            }),
            "wrapping_sub" => Ok(SpecEvalValue::Int {
                bits: lu.wrapping_sub(ru) & mask,
                size_bytes: lsz,
                signed: lsig,
                untyped_lit: false,
            }),
            "wrapping_mul" => Ok(SpecEvalValue::Int {
                bits: lu.wrapping_mul(ru) & mask,
                size_bytes: lsz,
                signed: lsig,
                untyped_lit: false,
            }),
            "saturating_add" => {
                if lsig {
                    let a = lhs_c.to_signed_i128()?;
                    let b = rhs_c.to_signed_i128()?;
                    let min_v = if bw >= 128 { i128::MIN } else { -(1i128 << (bw - 1)) };
                    let max_v = if bw >= 128 {
                        i128::MAX
                    } else {
                        (1i128 << (bw - 1)) - 1
                    };
                    let sat = a.saturating_add(b).clamp(min_v, max_v);
                    Ok(SpecEvalValue::Int {
                        bits: (sat as u128) & mask,
                        size_bytes: lsz,
                        signed: true,
                        untyped_lit: false,
                    })
                } else {
                    let sat = lu.saturating_add(ru).min(mask);
                    Ok(SpecEvalValue::Int {
                        bits: sat,
                        size_bytes: lsz,
                        signed: false,
                        untyped_lit: false,
                    })
                }
            }
            "saturating_sub" => {
                if lsig {
                    let a = lhs_c.to_signed_i128()?;
                    let b = rhs_c.to_signed_i128()?;
                    let min_v = if bw >= 128 { i128::MIN } else { -(1i128 << (bw - 1)) };
                    let max_v = if bw >= 128 {
                        i128::MAX
                    } else {
                        (1i128 << (bw - 1)) - 1
                    };
                    let sat = a.saturating_sub(b).clamp(min_v, max_v);
                    Ok(SpecEvalValue::Int {
                        bits: (sat as u128) & mask,
                        size_bytes: lsz,
                        signed: true,
                        untyped_lit: false,
                    })
                } else {
                    Ok(SpecEvalValue::Int {
                        bits: lu.saturating_sub(ru),
                        size_bytes: lsz,
                        signed: false,
                        untyped_lit: false,
                    })
                }
            }
            "min" => {
                let pick = if lsig {
                    if lhs_c.to_signed_i128()? <= rhs_c.to_signed_i128()? {
                        lu
                    } else {
                        ru
                    }
                } else if lu <= ru {
                    lu
                } else {
                    ru
                };
                Ok(SpecEvalValue::Int {
                    bits: pick,
                    size_bytes: lsz,
                    signed: lsig,
                    untyped_lit: false,
                })
            }
            "max" => {
                let pick = if lsig {
                    if lhs_c.to_signed_i128()? >= rhs_c.to_signed_i128()? {
                        lu
                    } else {
                        ru
                    }
                } else if lu >= ru {
                    lu
                } else {
                    ru
                };
                Ok(SpecEvalValue::Int {
                    bits: pick,
                    size_bytes: lsz,
                    signed: lsig,
                    untyped_lit: false,
                })
            }
            "abs_diff" => {
                let diff = if lsig {
                    lhs_c.to_signed_i128()?.abs_diff(rhs_c.to_signed_i128()?)
                } else {
                    lu.abs_diff(ru)
                };
                Ok(SpecEvalValue::Int {
                    bits: diff & mask,
                    size_bytes: lsz,
                    signed: false,
                    untyped_lit: false,
                })
            }
            _ => Err(format!("unsupported 1-arg integer method `{m_name}`")),
        };
    }

    Err(format!("unsupported integer method `{m_name}`"))
}

/// Descriptor for an `EnvSchedule`-backed external callee invoked inside a
/// [`SpecContractOracleProbe`] body so both [`SpecContractOracleProbe::synthesize_rust_probe`]
/// and [`SpecContractOracleProbe::verify_spec_postcondition_against_schedule`]
/// enforce identical signatures, return layouts, and scheduled actions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecExternalCallee {
    /// External callee identifier invoked by `callee_body_rust`.
    pub name: String,
    /// Rust parameter types of the external callee (e.g. `vec!["u32".into()]`).
    pub param_tys: Vec<String>,
    /// Rust return type syntax (e.g. `"u32"`, `"i32"`, `"bool"`).
    pub ret_rust_ty: String,
    /// Return value layout used to validate/decode `EnvAction::ReturnBytes`.
    pub ret_layout: LayoutSpec,
}

impl SpecExternalCallee {
    /// Constructs a new [`SpecExternalCallee`] descriptor.
    pub fn new<I, S>(
        name: impl Into<String>,
        param_tys: I,
        ret_rust_ty: impl Into<String>,
        ret_layout: LayoutSpec,
    ) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Self {
            name: name.into(),
            param_tys: param_tys.into_iter().map(Into::into).collect(),
            ret_rust_ty: ret_rust_ty.into(),
            ret_layout,
        }
    }
}

/// Verus `#3539` (`tools/vstd-kani`)-inspired external `#[anneal_spec::spec]`
/// postcondition oracle harness builder and schedule-backed contract evaluator.
///
/// Synthesizes standalone, warning-free (`rustc -D warnings`) safe Rust
/// contract-checking harnesses (`__anneal_spec_check_<fn_name>`) AND evaluates
/// the exact same AST contract (`requires`, `old(...)` snapshots, framed `&mut`
/// fields, and `ensures`) directly against concrete [`LayoutAwareByteBuilder`] /
/// [`EnvSchedule`] inputs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecContractOracleProbe {
    /// Name of the target function under specification test.
    pub fn_name: String,
    /// Optional auxiliary Rust `struct` / `type` / `fn` items required by the
    /// signature or body (e.g. `#[repr(C)] #[derive(Copy, Clone, Debug, PartialEq, Eq)] pub struct CounterPair { ... }`).
    pub type_defs_rust: String,
    /// Ordered parameter bindings (by-value and `&mut T`).
    pub params: Vec<SpecParamBinding>,
    /// Return type syntax in Rust (`"u32"`, `"bool"`, `"()"`, etc.).
    pub ret_rust_ty: String,
    /// Return value layout (`LayoutSpec::Tuple { total_size: 0, elements: vec![] }` for `()`).
    pub ret_layout: LayoutSpec,
    /// Optional external environment callees dispatched through [`EnvSchedule`].
    pub external_callees: Vec<SpecExternalCallee>,
    /// Ordered `requires(...)` preconditions guarding execution.
    pub requires: Vec<SpecContractAssertion>,
    /// Ordered `ensures(...)` postconditions checked on `result` and post-state
    /// parameters (with `old(<expr>)` denoting pre-state values).
    pub ensures: Vec<SpecContractAssertion>,
    /// Rust statements/tail-expression of the target implementation body.
    pub callee_body_rust: String,
}

impl SpecContractOracleProbe {
    /// Creates a new [`SpecContractOracleProbe`] for `fn_name`.
    pub fn new(
        fn_name: impl Into<String>,
        params: Vec<SpecParamBinding>,
        ret_rust_ty: impl Into<String>,
        ret_layout: LayoutSpec,
        callee_body_rust: impl Into<String>,
    ) -> Self {
        Self {
            fn_name: fn_name.into(),
            type_defs_rust: String::new(),
            params,
            ret_rust_ty: ret_rust_ty.into(),
            ret_layout,
            external_callees: Vec::new(),
            requires: Vec::new(),
            ensures: Vec::new(),
            callee_body_rust: callee_body_rust.into(),
        }
    }

    /// Attaches auxiliary Rust type/helper definitions emitted ahead of the probe.
    pub fn with_type_defs(mut self, type_defs_rust: impl Into<String>) -> Self {
        self.type_defs_rust = type_defs_rust.into();
        self
    }

    /// Registers an `EnvSchedule`-backed external callee so both
    /// [`Self::synthesize_rust_probe`] and [`Self::verify_spec_postcondition_against_schedule`]
    /// dispatch it with matching return type and layout.
    pub fn with_external_callee(mut self, callee: SpecExternalCallee) -> Self {
        self.external_callees.push(callee);
        self
    }

    /// Appends a `requires(...)` precondition assertion.
    pub fn with_requires(
        mut self,
        label: impl Into<String>,
        rust_expr: impl Into<String>,
    ) -> Self {
        self.requires
            .push(SpecContractAssertion::new(label, rust_expr));
        self
    }

    /// Appends an `ensures(...)` postcondition assertion.
    pub fn with_ensures(
        mut self,
        label: impl Into<String>,
        rust_expr: impl Into<String>,
    ) -> Self {
        self.ensures
            .push(SpecContractAssertion::new(label, rust_expr));
        self
    }

    /// Validates identifier hygiene, parameter uniqueness, frame field existence,
    /// `requires` / `ensures` expression syntax, `old(...)` placement, and body syntax.
    pub fn validate(&self) -> Result<(), String> {
        if !is_valid_rust_ident(&self.fn_name) {
            return Err(format!(
                "invalid target function identifier `{}`",
                self.fn_name
            ));
        }
        if !self.type_defs_rust.trim().is_empty() {
            syn::parse_file(&self.type_defs_rust)
                .map_err(|e| format!("invalid `type_defs_rust`: {e}"))?;
        }
        let mut seen_params = BTreeSet::new();
        for p in &self.params {
            if !is_valid_rust_ident(&p.name) || p.name == "result" {
                return Err(format!(
                    "invalid or reserved parameter name `{}` (note: `result` is reserved for postconditions)",
                    p.name
                ));
            }
            if !seen_params.insert(p.name.clone()) {
                return Err(format!("duplicate parameter name `{}`", p.name));
            }
            syn::parse_str::<syn::Type>(&p.rust_ty)
                .map_err(|e| format!("invalid parameter type `{}`: {e}", p.rust_ty))?;
            if !p.frame_preserved_fields.is_empty() {
                if !p.is_mut_ref {
                    return Err(format!(
                        "`frame_preserved_fields` specified on non-`&mut` parameter `{}`",
                        p.name
                    ));
                }
                let LayoutSpec::Struct { fields, .. } = &p.layout else {
                    return Err(format!(
                        "`frame_preserved_fields` requires a `LayoutSpec::Struct` on `{}`",
                        p.name
                    ));
                };
                for ff in &p.frame_preserved_fields {
                    if !fields.iter().any(|f| &f.name == ff) {
                        return Err(format!(
                            "unknown framed field `{ff}` on parameter `{}`",
                            p.name
                        ));
                    }
                }
            }
        }
        let mut seen_ext = BTreeSet::new();
        for ext in &self.external_callees {
            if !is_valid_rust_ident(&ext.name) || ext.name == self.fn_name || ext.name == "old" {
                return Err(format!(
                    "invalid or colliding external callee identifier `{}`",
                    ext.name
                ));
            }
            if !seen_ext.insert(ext.name.clone()) {
                return Err(format!("duplicate external callee `{}`", ext.name));
            }
            for pty in &ext.param_tys {
                syn::parse_str::<syn::Type>(pty).map_err(|e| {
                    format!(
                        "invalid parameter type `{pty}` on external callee `{}`: {e}",
                        ext.name
                    )
                })?;
            }
            syn::parse_str::<syn::Type>(&ext.ret_rust_ty).map_err(|e| {
                format!(
                    "invalid return type `{}` on external callee `{}`: {e}",
                    ext.ret_rust_ty, ext.name
                )
            })?;
        }
        syn::parse_str::<syn::Type>(&self.ret_rust_ty)
            .map_err(|e| format!("invalid return type `{}`: {e}", self.ret_rust_ty))?;

        for req in &self.requires {
            let parsed = syn::parse_str::<Expr>(&req.rust_expr).map_err(|e| {
                format!(
                    "invalid `requires` expression `{}` ({}): {e}",
                    req.rust_expr, req.label
                )
            })?;
            if contains_old_call(&parsed) {
                return Err(format!(
                    "`old(...)` is not allowed in `requires` clause `{}`",
                    req.label
                ));
            }
        }
        for ens in &self.ensures {
            let parsed = syn::parse_str::<Expr>(&ens.rust_expr).map_err(|e| {
                format!(
                    "invalid `ensures` expression `{}` ({}): {e}",
                    ens.rust_expr, ens.label
                )
            })?;
            validate_old_calls_in_ensures(&parsed)?;
        }

        let wrapped_body = format!("{{\n{}\n}}", self.callee_body_rust);
        syn::parse_str::<syn::Block>(&wrapped_body)
            .map_err(|e| format!("invalid `callee_body_rust` syntax: {e}"))?;
        Ok(())
    }

    /// Combined input [`LayoutSpec::Tuple`] packing all parameters sequentially
    /// at contiguous offsets so [`LayoutAwareByteBuilder::build_bytes`] can
    /// materialize complete argument tuples directly.
    pub fn combined_input_layout(&self) -> LayoutSpec {
        let mut offset = 0usize;
        let mut elements = Vec::with_capacity(self.params.len());
        for p in &self.params {
            elements.push((offset, p.layout.clone()));
            offset += p.layout.total_size();
        }
        LayoutSpec::Tuple {
            total_size: offset,
            elements,
        }
    }

    /// Synthesizes a standalone, self-contained, `#![allow(dead_code)]` safe Rust
    /// library module containing:
    /// - `SpecProbeOutcome`,
    /// - any `type_defs_rust`,
    /// - the target function `pub fn <fn_name>(...) -> <ret_rust_ty>`,
    /// - non-panicking `pub fn __anneal_spec_check_<fn_name>(...) -> SpecProbeOutcome`, and
    /// - asserting `pub fn __anneal_spec_assert_<fn_name>(...) -> bool` (which
    ///   panics on `PostconditionViolation` / `FrameViolation`).
    ///
    /// Compiles cleanly with `rustc --edition=2024 --crate-type=lib -D warnings`.
    pub fn synthesize_rust_probe(&self) -> Result<String, String> {
        use quote::ToTokens;
        self.validate()?;

        let mut needed_pre_params = BTreeSet::new();
        let mut lazy_old_closures: Vec<(String, String)> = Vec::new();
        let mut rewritten_ensures: Vec<(String, String)> = Vec::with_capacity(self.ensures.len());
        for ens in &self.ensures {
            let mut expr = syn::parse_str::<Expr>(&ens.rust_expr)
                .map_err(|e| format!("invalid ensures `{}`: {e}", ens.rust_expr))?;
            rewrite_old_expressions_for_rust(
                &mut expr,
                &self.params,
                &mut needed_pre_params,
                &mut lazy_old_closures,
            );
            rewritten_ensures.push((ens.label.clone(), expr.to_token_stream().to_string()));
        }

        let mut sig_params = Vec::with_capacity(self.params.len());
        let mut check_params = Vec::with_capacity(self.params.len());
        let mut call_args = Vec::with_capacity(self.params.len());
        let mut touch_params = Vec::with_capacity(self.params.len());
        for p in &self.params {
            if p.is_mut_ref {
                sig_params.push(format!("{}: &mut {}", p.name, p.rust_ty));
                check_params.push(format!("{}: &mut {}", p.name, p.rust_ty));
                call_args.push(format!("&mut *{}", p.name));
            } else {
                sig_params.push(format!("{}: {}", p.name, p.rust_ty));
                check_params.push(format!("{}: {}", p.name, p.rust_ty));
                call_args.push(p.name.clone());
            }
            touch_params.push(format!("let _ = &{};", p.name));
        }

        let mut out = String::from(
            "#![allow(dead_code)]\n\n\
             #[derive(Debug, Clone, Copy, PartialEq, Eq)]\n\
             pub enum SpecProbeOutcome {\n    \
                 VacuouslyFiltered,\n    \
                 VerifiedHold,\n    \
                 PostconditionViolation(&'static str),\n    \
                 FrameViolation(&'static str),\n\
             }\n\n",
        );

        if !self.type_defs_rust.trim().is_empty() {
            out.push_str(self.type_defs_rust.trim());
            out.push_str("\n\n");
        }

        if !self.external_callees.is_empty() {
            out.push_str(
                "std::thread_local! {\n    \
                     static __ANNEAL_GLOBAL_CALL_IDX: std::cell::Cell<usize> = \
                         const { std::cell::Cell::new(0) };\n    \
                     static __ANNEAL_GLOBAL_PANIC_ON_CALL: std::cell::Cell<Option<usize>> = \
                         const { std::cell::Cell::new(None) };\n\
                 }\n\
                 pub fn __anneal_reset_global_schedule(global_panic_on_call: Option<usize>) {\n    \
                     __ANNEAL_GLOBAL_CALL_IDX.with(|c| c.set(0));\n    \
                     __ANNEAL_GLOBAL_PANIC_ON_CALL.with(|p| p.set(global_panic_on_call));\n\
                 }\n\n",
            );
            for ext in &self.external_callees {
                let upper = ext.name.to_ascii_uppercase();
                let queue_static = format!("__ANNEAL_SCHED_{upper}");
                let default_static = format!("__ANNEAL_DEFAULT_{upper}");
                let panic_static = format!("__ANNEAL_PANIC_IDX_{upper}");
                let count_static = format!("__ANNEAL_CALL_COUNT_{upper}");
                out.push_str(&format!(
                    "std::thread_local! {{\n    \
                         static {queue_static}: std::cell::RefCell<std::collections::VecDeque<Option<{}>>> = \
                             const {{ std::cell::RefCell::new(std::collections::VecDeque::new()) }};\n    \
                         static {default_static}: std::cell::RefCell<Option<Option<{}>>> = \
                             const {{ std::cell::RefCell::new(None) }};\n    \
                         static {panic_static}: std::cell::Cell<Option<usize>> = \
                             const {{ std::cell::Cell::new(None) }};\n    \
                         static {count_static}: std::cell::Cell<usize> = \
                             const {{ std::cell::Cell::new(0) }};\n\
                     }}\n\
                     pub fn __anneal_reset_schedule_{}() {{\n    \
                         {queue_static}.with(|q| q.borrow_mut().clear());\n    \
                         {default_static}.with(|d| *d.borrow_mut() = None);\n    \
                         {panic_static}.with(|p| p.set(None));\n    \
                         {count_static}.with(|c| c.set(0));\n\
                     }}\n\
                     pub fn __anneal_push_schedule_{}(item: Option<{}>) {{\n    \
                         {queue_static}.with(|q| q.borrow_mut().push_back(item));\n\
                     }}\n\
                     pub fn __anneal_set_default_{}(item: Option<Option<{}>>) {{\n    \
                         {default_static}.with(|d| *d.borrow_mut() = item);\n\
                     }}\n\
                     pub fn __anneal_set_callee_panic_{}(call_idx: Option<usize>) {{\n    \
                         {panic_static}.with(|p| p.set(call_idx));\n\
                     }}\n",
                    ext.ret_rust_ty,
                    ext.ret_rust_ty,
                    ext.name,
                    ext.name,
                    ext.ret_rust_ty,
                    ext.name,
                    ext.ret_rust_ty,
                    ext.name
                ));
                let ext_params: Vec<String> = ext
                    .param_tys
                    .iter()
                    .enumerate()
                    .map(|(i, ty)| format!("_arg_{i}: {ty}"))
                    .collect();
                out.push_str(&format!(
                    "pub fn {}({}) -> {} {{\n    \
                         let global_idx = __ANNEAL_GLOBAL_CALL_IDX.with(|c| {{\n        \
                             let cur = c.get();\n        \
                             c.set(cur + 1);\n        \
                             cur\n    \
                         }});\n    \
                         let callee_idx = {count_static}.with(|c| {{\n        \
                             let cur = c.get();\n        \
                             c.set(cur + 1);\n        \
                             cur\n    \
                         }});\n    \
                         if __ANNEAL_GLOBAL_PANIC_ON_CALL.with(|p| p.get()) == Some(global_idx)\n        \
                             || {panic_static}.with(|p| p.get()) == Some(callee_idx)\n    \
                         {{\n        \
                             panic!(\"scheduled panic on `{}`\");\n    \
                         }}\n    \
                         if let Some(queued) = {queue_static}.with(|q| q.borrow_mut().pop_front()) {{\n        \
                             return match queued {{\n            \
                                 Some(val) => val,\n            \
                                 None => panic!(\"invalid scheduled payload on `{}`\"),\n        \
                             }};\n    \
                         }}\n    \
                         if let Some(def_opt) = {default_static}.with(|d| d.borrow().clone()) {{\n        \
                             return match def_opt {{\n            \
                                 Some(val) => val,\n            \
                                 None => panic!(\"invalid default payload on `{}`\"),\n        \
                             }};\n    \
                         }}\n    \
                         panic!(\"unscheduled PassThrough call to `{}`\")\n\
                     }}\n\n",
                    ext.name,
                    ext_params.join(", "),
                    ext.ret_rust_ty,
                    ext.name,
                    ext.name,
                    ext.name,
                    ext.name
                ));
            }
        }

        out.push_str(&format!(
            "#[allow(unused_variables, unused_mut)]\n\
             pub fn {}({}) -> {} {{\n{}\n}}\n\n",
            self.fn_name,
            sig_params.join(", "),
            self.ret_rust_ty,
            self.callee_body_rust.trim()
        ));

        out.push_str(&format!(
            "pub fn __anneal_spec_check_{}({}) -> SpecProbeOutcome {{\n",
            self.fn_name,
            check_params.join(", ")
        ));
        for t in &touch_params {
            out.push_str("    ");
            out.push_str(t);
            out.push('\n');
        }
        for (req_idx, req) in self.requires.iter().enumerate() {
            out.push_str(&format!(
                "    let __anneal_req_{req_idx}: bool = {};\n    \
                 if !__anneal_req_{req_idx} {{\n        \
                     return SpecProbeOutcome::VacuouslyFiltered;\n    \
                 }}\n",
                req.rust_expr
            ));
        }
        for p in &self.params {
            if needed_pre_params.contains(&p.name) {
                if p.is_mut_ref {
                    out.push_str(&format!(
                        "    let __anneal_pre_{}: {} = (*{}).clone();\n    \
                         let _ = &__anneal_pre_{};\n",
                        p.name, p.rust_ty, p.name, p.name
                    ));
                } else {
                    out.push_str(&format!(
                        "    let __anneal_pre_{}: {} = {}.clone();\n    \
                         let _ = &__anneal_pre_{};\n",
                        p.name, p.rust_ty, p.name, p.name
                    ));
                }
            }
        }
        for p in &self.params {
            if p.is_mut_ref {
                for ff in &p.frame_preserved_fields {
                    out.push_str(&format!(
                        "    let __anneal_frame_old_{}_{ff} = {}.{ff}.clone();\n",
                        p.name, p.name
                    ));
                }
            }
        }
        out.push_str(&format!(
            "    let result: {} = {}({});\n    let _ = &result;\n",
            self.ret_rust_ty,
            self.fn_name,
            call_args.join(", ")
        ));
        for p in &self.params {
            if p.is_mut_ref {
                for ff in &p.frame_preserved_fields {
                    let tag = format!("{}.{ff}", p.name);
                    out.push_str(&format!(
                        "    if {}.{} != __anneal_frame_old_{}_{ff} {{\n        \
                             return SpecProbeOutcome::FrameViolation({tag:?});\n    \
                         }}\n",
                        p.name, ff, p.name
                    ));
                }
            }
        }
        for (old_var, inner_src) in &lazy_old_closures {
            out.push_str(&format!("    let {old_var} = || {{ {inner_src} }};\n"));
        }
        for (ens_idx, (label, expr_src)) in rewritten_ensures.iter().enumerate() {
            out.push_str(&format!(
                "    let __anneal_ens_{ens_idx}: bool = {expr_src};\n    \
                 if !__anneal_ens_{ens_idx} {{\n        \
                     return SpecProbeOutcome::PostconditionViolation({label:?});\n    \
                 }}\n"
            ));
        }
        out.push_str("    SpecProbeOutcome::VerifiedHold\n}\n\n");

        let assert_fwd_args: Vec<String> = self
            .params
            .iter()
            .map(|p| {
                if p.is_mut_ref {
                    format!("&mut *{}", p.name)
                } else {
                    p.name.clone()
                }
            })
            .collect();
        out.push_str(&format!(
            "pub fn __anneal_spec_assert_{}({}) -> bool {{\n    \
                 match __anneal_spec_check_{}({}) {{\n        \
                     SpecProbeOutcome::VacuouslyFiltered => false,\n        \
                     SpecProbeOutcome::VerifiedHold => true,\n        \
                     SpecProbeOutcome::PostconditionViolation(lbl) => {{\n            \
                         panic!(\"SpecPostconditionViolation in `{}`: {{lbl}}\");\n        \
                     }}\n        \
                     SpecProbeOutcome::FrameViolation(field) => {{\n            \
                         panic!(\"SpecFrameViolation in `{}`: {{field}}\");\n        \
                     }}\n    \
                 }}\n\
             }}\n",
            self.fn_name,
            check_params.join(", "),
            self.fn_name,
            assert_fwd_args.join(", "),
            self.fn_name,
            self.fn_name,
        ));

        Ok(out)
    }

    /// Synthesizes a complete executable Rust binary (`fn main()`) that runs
    /// `__anneal_spec_check_<fn_name>` across `packed_trials` (catching panics
    /// via `std::panic::catch_unwind`) and prints one canonical tag line per
    /// trial (`HOLD`, `FILTERED`, `VIOLATION:<detail>`, `FRAME:<field>`, or `TRAP`),
    /// enabling end-to-end native `rustc -D warnings` parity tests.
    pub fn synthesize_rust_executable_harness(
        &self,
        packed_trials: &[Vec<u8>],
    ) -> Result<String, String> {
        let scheduled: Vec<(Vec<u8>, Option<EnvSchedule>)> = packed_trials
            .iter()
            .map(|b| (b.clone(), None))
            .collect();
        self.synthesize_rust_executable_harness_with_schedules(&scheduled)
    }

    /// Synthesizes a complete executable Rust binary (`fn main()`) over
    /// `(packed_arg_bytes, optional_schedule)` trials, staging each trial's
    /// declared external callee actions from [`EnvSchedule`] before running
    /// `__anneal_spec_check_<fn_name>`.
    pub fn synthesize_rust_executable_harness_with_schedules(
        &self,
        trials: &[(Vec<u8>, Option<EnvSchedule>)],
    ) -> Result<String, String> {
        let mut src = self.synthesize_rust_probe()?;
        src.push_str("\nfn main() {\n");
        for (t_idx, (raw_trial, opt_sched)) in trials.iter().enumerate() {
            let expected_len: usize = self.params.iter().map(|p| p.layout.total_size()).sum();
            if raw_trial.len() != expected_len {
                return Err(format!(
                    "trial {t_idx} byte length mismatch: expected {expected_len}, got {}",
                    raw_trial.len()
                ));
            }
            let mut cursor = 0usize;
            let mut bindings_code = String::new();
            if !self.external_callees.is_empty() {
                let global_panic_lit = match opt_sched.as_ref().and_then(|s| s.global_panic_on_call)
                {
                    Some(idx) => format!("Some({idx}usize)"),
                    None => "None".to_string(),
                };
                bindings_code.push_str(&format!(
                    "        __anneal_reset_global_schedule({global_panic_lit});\n"
                ));
            }
            for ext in &self.external_callees {
                bindings_code.push_str(&format!(
                    "        __anneal_reset_schedule_{}();\n",
                    ext.name
                ));
            }
            if let Some(sched) = opt_sched {
                for ext in &self.external_callees {
                    let decode_opt_lit = |bytes: &[u8]| -> String {
                        if bytes.len() == ext.ret_layout.total_size()
                            && let Ok(val) =
                                SpecEvalValue::from_layout_bytes(&ext.ret_layout, bytes)
                        {
                            format!("Some({})", val.rust_literal(&ext.ret_rust_ty))
                        } else {
                            "None".to_string()
                        }
                    };
                    if let Some(&c_panic) = sched.callee_panic_on_call.get(&ext.name) {
                        bindings_code.push_str(&format!(
                            "        __anneal_set_callee_panic_{}(Some({c_panic}usize));\n",
                            ext.name
                        ));
                    }
                    if let Some(queue) = sched.callee_queues.get(&ext.name) {
                        for item_bytes in queue {
                            bindings_code.push_str(&format!(
                                "        __anneal_push_schedule_{}({});\n",
                                ext.name,
                                decode_opt_lit(item_bytes)
                            ));
                        }
                    }
                    if let Some(def_bytes) = sched.callee_defaults.get(&ext.name) {
                        bindings_code.push_str(&format!(
                            "        __anneal_set_default_{}(Some({}));\n",
                            ext.name,
                            decode_opt_lit(def_bytes)
                        ));
                    }
                }
            }
            let mut call_args = Vec::with_capacity(self.params.len());
            for p in &self.params {
                let sz = p.layout.total_size();
                let val = SpecEvalValue::from_layout_bytes(&p.layout, &raw_trial[cursor..cursor + sz])
                    .map_err(|e| format!("trial {t_idx} param `{}` invalid: {e}", p.name))?;
                cursor += sz;
                let lit = val.rust_literal(&p.rust_ty);
                if p.is_mut_ref {
                    bindings_code.push_str(&format!(
                        "        let mut __arg_{}: {} = {};\n",
                        p.name, p.rust_ty, lit
                    ));
                    call_args.push(format!("&mut __arg_{}", p.name));
                } else {
                    bindings_code.push_str(&format!(
                        "        let __arg_{}: {} = {};\n",
                        p.name, p.rust_ty, lit
                    ));
                    call_args.push(format!("__arg_{}", p.name));
                }
            }
            src.push_str(&format!(
                "    let __trial_{t_idx} = std::panic::catch_unwind(|| {{\n\
                 {bindings_code}\
                         __anneal_spec_check_{}({})\n    \
                 }});\n    \
                 match __trial_{t_idx} {{\n        \
                     Ok(SpecProbeOutcome::VerifiedHold) => println!(\"TRIAL:{t_idx}:HOLD\"),\n        \
                     Ok(SpecProbeOutcome::VacuouslyFiltered) => println!(\"TRIAL:{t_idx}:FILTERED\"),\n        \
                     Ok(SpecProbeOutcome::PostconditionViolation(lbl)) => println!(\"TRIAL:{t_idx}:VIOLATION:{{lbl}}\"),\n        \
                     Ok(SpecProbeOutcome::FrameViolation(fld)) => println!(\"TRIAL:{t_idx}:FRAME:{{fld}}\"),\n        \
                     Err(_) => println!(\"TRIAL:{t_idx}:TRAP\"),\n    \
                 }}\n",
                self.fn_name,
                call_args.join(", ")
            ));
        }
        src.push_str("}\n");
        Ok(src)
    }

    /// Evaluates this contract against a single packed input byte slice (such as
    /// one generated by [`LayoutAwareByteBuilder::build_bytes`] on
    /// [`Self::combined_input_layout`]) and an optional [`EnvSchedule`].
    ///
    /// Distinguishes:
    /// 1. `VacuouslyFiltered` when any `requires` clause evaluates to `false`,
    /// 2. `PostconditionViolation` when an `ensures` clause or framed `&mut`
    ///    field invariant fails on normal return,
    /// 3. `PanicOrTrap` when checked overflow, shift-width UB, OOB indexing,
    ///    explicit `panic!` / `assert!`, or `EnvAction::PanicOnCall` fires, and
    /// 4. `VerifiedHold` when `requires`, body execution, frame conditions, and
    ///    `ensures` all succeed.
    pub fn verify_spec_postcondition_against_schedule(
        &self,
        packed_arg_bytes: &[u8],
        schedule: Option<&mut EnvSchedule>,
    ) -> Result<SpecPostconditionVerdict, ScheduleError> {
        self.validate().map_err(|reason| ScheduleError::InvalidBitPattern {
            context: self.fn_name.clone(),
            reason,
        })?;

        let expected_total: usize = self.params.iter().map(|p| p.layout.total_size()).sum();
        if packed_arg_bytes.len() != expected_total {
            return Err(ScheduleError::PayloadSizeMismatch {
                context: format!("SpecContractOracleProbe({})", self.fn_name),
                expected: expected_total,
                actual: packed_arg_bytes.len(),
            });
        }

        let mut struct_layouts = BTreeMap::new();
        let mut external_callees = BTreeMap::new();
        for ext in &self.external_callees {
            collect_named_struct_layouts(&ext.ret_layout, &mut struct_layouts);
            external_callees.insert(ext.name.clone(), ext.ret_layout.clone());
        }
        let mut helper_fns = BTreeMap::new();
        if !self.type_defs_rust.trim().is_empty()
            && let Ok(parsed_defs) = syn::parse_file(&self.type_defs_rust)
        {
            for item in parsed_defs.items {
                if let syn::Item::Fn(f) = item {
                    helper_fns.insert(f.sig.ident.to_string(), f);
                }
            }
        }
        let mut pre_env = BTreeMap::new();
        let mut pre_raw_by_param: BTreeMap<String, Vec<u8>> = BTreeMap::new();
        let mut cursor = 0usize;
        for p in &self.params {
            collect_named_struct_layouts(&p.layout, &mut struct_layouts);
            let sz = p.layout.total_size();
            let slice = &packed_arg_bytes[cursor..cursor + sz];
            cursor += sz;
            let val = SpecEvalValue::from_layout_bytes(&p.layout, slice)?;
            pre_raw_by_param.insert(p.name.clone(), slice.to_vec());
            pre_env.insert(p.name.clone(), val);
        }
        collect_named_struct_layouts(&self.ret_layout, &mut struct_layouts);

        // Phase 1: Evaluate `requires` preconditions in order BEFORE executing the body.
        {
            let mut req_ctx = SpecEvalContext {
                env: pre_env.clone(),
                pre_env: None,
                struct_layouts: &struct_layouts,
                external_callees: &external_callees,
                helper_fns: &helper_fns,
                schedule: None,
                call_index: 0,
                early_return: None,
            };
            for (idx, req) in self.requires.iter().enumerate() {
                let expr = syn::parse_str::<Expr>(&req.rust_expr).map_err(|e| {
                    ScheduleError::InvalidBitPattern {
                        context: req.label.clone(),
                        reason: e.to_string(),
                    }
                })?;
                match req_ctx.eval_expr(&expr) {
                    Ok(SpecEvalValue::Bool(true)) => {}
                    Ok(SpecEvalValue::Bool(false)) => {
                        return Ok(SpecPostconditionVerdict::VacuouslyFiltered {
                            failed_requires_index: idx,
                            failed_requires_label: req.label.clone(),
                        });
                    }
                    Ok(other) => {
                        return Ok(SpecPostconditionVerdict::PanicOrTrap {
                            phase: SpecExecPhase::Requires,
                            detail: format!(
                                "`requires` clause `{}` returned non-bool {other:?}",
                                req.label
                            ),
                        });
                    }
                    Err(trap) => {
                        return Ok(SpecPostconditionVerdict::PanicOrTrap {
                            phase: SpecExecPhase::Requires,
                            detail: trap,
                        });
                    }
                }
            }
        }

        // Phase 2: Execute callee body against `schedule`.
        let wrapped_body = format!("{{\n{}\n}}", self.callee_body_rust);
        let body_block = syn::parse_str::<syn::Block>(&wrapped_body).map_err(|e| {
            ScheduleError::InvalidBitPattern {
                context: self.fn_name.clone(),
                reason: e.to_string(),
            }
        })?;
        let mut body_ctx = SpecEvalContext {
            env: pre_env.clone(),
            pre_env: None,
            struct_layouts: &struct_layouts,
            external_callees: &external_callees,
            helper_fns: &helper_fns,
            schedule,
            call_index: 0,
            early_return: None,
        };
        let mut result_val = match body_ctx.eval_block(&body_block) {
            Ok(v) => v,
            Err(trap) => {
                return Ok(SpecPostconditionVerdict::PanicOrTrap {
                    phase: SpecExecPhase::Body,
                    detail: trap,
                });
            }
        };
        result_val = match coerce_value_to_layout(result_val, &self.ret_layout) {
            Ok(coerced) => coerced,
            Err(trap) => {
                return Ok(SpecPostconditionVerdict::PanicOrTrap {
                    phase: SpecExecPhase::Body,
                    detail: trap,
                });
            }
        };

        // Phase 3: Check frame conditions on `&mut` parameters using
        // `LayoutSpec::mask_padding_as_unknown` so padding bytes never cause
        // false alarms while every occupied data byte of framed fields is checked!
        for p in &self.params {
            if !p.is_mut_ref || p.frame_preserved_fields.is_empty() {
                continue;
            }
            let Some(post_val) = body_ctx.env.get(&p.name) else {
                continue;
            };
            let post_bytes = post_val.to_layout_bytes();
            let pre_bytes = &pre_raw_by_param[&p.name];
            if let LayoutSpec::Struct { fields, .. } = &p.layout {
                for ff in &p.frame_preserved_fields {
                    if let Some(fspec) = fields.iter().find(|f| &f.name == ff) {
                        let start = fspec.offset;
                        let end = start + fspec.layout.total_size();
                        let pre_masked = fspec
                            .layout
                            .mask_padding_as_unknown(&pre_bytes[start..end])?;
                        let post_masked = fspec
                            .layout
                            .mask_padding_as_unknown(&post_bytes[start..end])?;
                        if pre_masked != post_masked {
                            return Ok(SpecPostconditionVerdict::PostconditionViolation {
                                kind: SpecViolationKind::FrameCondition {
                                    param: p.name.clone(),
                                    field: ff.clone(),
                                },
                                detail: format!(
                                    "framed field `{}.{ff}` mutated from {:?} to {:?}",
                                    p.name,
                                    &pre_bytes[start..end],
                                    &post_bytes[start..end]
                                ),
                            });
                        }
                    }
                }
            }
        }

        // Phase 4: Evaluate `ensures` postconditions over post-state + `result` + `old(pre_env)`.
        let mut post_env = BTreeMap::new();
        for p in &self.params {
            if p.is_mut_ref {
                if let Some(v) = body_ctx.env.get(&p.name) {
                    post_env.insert(p.name.clone(), v.clone());
                }
            } else if let Some(v) = pre_env.get(&p.name) {
                // Non-`&mut` parameters are observed at their caller-visible value.
                post_env.insert(p.name.clone(), v.clone());
            }
        }
        post_env.insert("result".to_string(), result_val);

        let mut ens_ctx = SpecEvalContext {
            env: post_env,
            pre_env: Some(&pre_env),
            struct_layouts: &struct_layouts,
            external_callees: &external_callees,
            helper_fns: &helper_fns,
            schedule: None,
            call_index: 0,
            early_return: None,
        };
        for (idx, ens) in self.ensures.iter().enumerate() {
            let expr = syn::parse_str::<Expr>(&ens.rust_expr).map_err(|e| {
                ScheduleError::InvalidBitPattern {
                    context: ens.label.clone(),
                    reason: e.to_string(),
                }
            })?;
            match ens_ctx.eval_expr(&expr) {
                Ok(SpecEvalValue::Bool(true)) => {}
                Ok(SpecEvalValue::Bool(false)) => {
                    return Ok(SpecPostconditionVerdict::PostconditionViolation {
                        kind: SpecViolationKind::EnsuresClause {
                            clause_index: idx,
                            label: ens.label.clone(),
                        },
                        detail: format!(
                            "`ensures` clause `{}` (`{}`) evaluated to false",
                            ens.label, ens.rust_expr
                        ),
                    });
                }
                Ok(other) => {
                    return Ok(SpecPostconditionVerdict::PanicOrTrap {
                        phase: SpecExecPhase::Ensures,
                        detail: format!(
                            "`ensures` clause `{}` returned non-bool {other:?}",
                            ens.label
                        ),
                    });
                }
                Err(trap) => {
                    return Ok(SpecPostconditionVerdict::PanicOrTrap {
                        phase: SpecExecPhase::Ensures,
                        detail: trap,
                    });
                }
            }
        }

        Ok(SpecPostconditionVerdict::VerifiedHold)
    }

    /// Evaluates `self` across a batch of `(packed_arg_bytes, optional_schedule)`
    /// trials and aggregates counts into a [`SpecBatchVerificationReport`].
    pub fn verify_spec_postcondition_batch(
        &self,
        trials: &[(Vec<u8>, Option<EnvSchedule>)],
    ) -> Result<SpecBatchVerificationReport, ScheduleError> {
        let mut report = SpecBatchVerificationReport {
            total_trials: trials.len(),
            ..SpecBatchVerificationReport::default()
        };
        for (arg_bytes, opt_sched) in trials {
            let mut sched_clone = opt_sched.clone();
            let verdict = self
                .verify_spec_postcondition_against_schedule(arg_bytes, sched_clone.as_mut())?;
            match &verdict {
                SpecPostconditionVerdict::VerifiedHold => report.verified_hold_count += 1,
                SpecPostconditionVerdict::VacuouslyFiltered { .. } => {
                    report.vacuously_filtered_count += 1;
                }
                SpecPostconditionVerdict::PostconditionViolation { .. } => {
                    report.postcondition_violation_count += 1;
                }
                SpecPostconditionVerdict::PanicOrTrap { .. } => report.panic_or_trap_count += 1,
            }
            report.verdicts.push(verdict);
        }
        Ok(report)
    }
}

fn collect_named_struct_layouts(layout: &LayoutSpec, out: &mut BTreeMap<String, LayoutSpec>) {
    match layout {
        LayoutSpec::Struct { name, fields, .. } => {
            out.insert(name.clone(), layout.clone());
            for f in fields {
                collect_named_struct_layouts(&f.layout, out);
            }
        }
        LayoutSpec::Tuple { elements, .. } => {
            for (_, el) in elements {
                collect_named_struct_layouts(el, out);
            }
        }
        LayoutSpec::Array { elem, .. } => collect_named_struct_layouts(elem, out),
        LayoutSpec::Enum { variants, .. } => {
            for v in variants {
                if let Some(p) = &v.payload {
                    collect_named_struct_layouts(p, out);
                }
            }
        }
        LayoutSpec::Scalar(_) => {}
    }
}

/// Convenience free-function entry point delegating to
/// [`SpecContractOracleProbe::verify_spec_postcondition_against_schedule`].
pub fn verify_spec_postcondition_against_schedule(
    probe: &SpecContractOracleProbe,
    packed_arg_bytes: &[u8],
    schedule: Option<&mut EnvSchedule>,
) -> Result<SpecPostconditionVerdict, ScheduleError> {
    probe.verify_spec_postcondition_against_schedule(packed_arg_bytes, schedule)
}

/// One write or read-modify-write (RMW) transition observed by [`WriteChainCoverageBound`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WriteChainStep {
    /// Mutable variable / place / channel written in this step.
    pub written_slot: String,
    /// Source slots read to compute the value written in this step.
    pub read_slots: Vec<String>,
    /// Optional external environment callee mediating this step.
    pub env_callee: Option<String>,
    /// When `env_callee.is_some()`, whether the scheduled environment call
    /// delivered a valid payload (`false` indicates a gap/panic breaking the chain).
    pub env_link_satisfied: bool,
}

impl WriteChainStep {
    /// Local write `written_slot := const_or_initial(...)` with zero causal slot dependencies.
    pub fn local_write(written_slot: impl Into<String>) -> Self {
        Self {
            written_slot: written_slot.into(),
            read_slots: Vec::new(),
            env_callee: None,
            env_link_satisfied: true,
        }
    }

    /// Causal write / RMW `written_slot := f(read_slots...)`.
    pub fn dependent_write<I, S>(written_slot: impl Into<String>, read_slots: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Self {
            written_slot: written_slot.into(),
            read_slots: read_slots.into_iter().map(Into::into).collect(),
            env_callee: None,
            env_link_satisfied: true,
        }
    }

    /// Environment-mediated write / RMW crossing external `callee`.
    pub fn env_dependent_write<I, S>(
        written_slot: impl Into<String>,
        read_slots: I,
        callee: impl Into<String>,
        env_link_satisfied: bool,
    ) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Self {
            written_slot: written_slot.into(),
            read_slots: read_slots.into_iter().map(Into::into).collect(),
            env_callee: Some(callee.into()),
            env_link_satisfied,
        }
    }
}

/// Planned environment-scheduled write/RMW transition evaluated against an
/// [`EnvSchedule`] via [`WriteChainCoverageBound::observe_env_schedule`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnvScheduledWriteStep {
    /// External callee queried at this schedule step.
    pub callee: String,
    /// Target mutable slot updated using `callee`'s response and `read_slots`.
    pub written_slot: String,
    /// Previously written slots fed into `callee` or combined with its response.
    pub read_slots: Vec<String>,
}

impl EnvScheduledWriteStep {
    /// Constructs a planned environment-scheduled write/RMW step.
    pub fn new<I, S>(
        callee: impl Into<String>,
        written_slot: impl Into<String>,
        read_slots: I,
    ) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Self {
            callee: callee.into(),
            written_slot: written_slot.into(),
            read_slots: read_slots.into_iter().map(Into::into).collect(),
        }
    }
}

/// Structured diagnostic explaining why [`WriteChainCoverageBound::is_depth_certified`]
/// is `false`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnderExplorationReason {
    /// `min_walk_length == 0` is invalid (a causal write chain requires $d \ge 1$).
    InvalidTargetDepth { min_walk_length: usize },
    /// `num_slots == 0` is invalid (at least $m \ge 1$ mutable slot is required).
    InvalidSlotCount { num_slots: usize },
    /// Zero valid writes have been observed so far.
    NoWritesObserved { required_depth: usize },
    /// An `EnvSchedule` call panicked, failed payload validation, or lacked a
    /// scheduled response (`PassThrough`), breaking the cross-boundary RMW chain.
    BrokenEnvScheduleLink {
        max_observed_depth: usize,
        required_depth: usize,
        broken_links: usize,
    },
    /// One or more writes were observed, but every write was an independent
    /// depth-1 local write (`x = 1; y = 2; z = 3`) with zero write-to-read-to-write
    /// composition ($k = 1 < d$).
    OnlyDepthOneLocalWrites {
        steps_observed: usize,
        distinct_slots_written: usize,
        required_depth: usize,
    },
    /// Some multi-step RMW/write-read-write progress occurred ($2 \le k < d$),
    /// but the maximum contiguous causal chain depth $k$ is still below $d$.
    InsufficientChainDepth {
        max_observed_depth: usize,
        required_depth: usize,
        steps_observed: usize,
        recommended_walk_steps: usize,
    },
}

impl std::fmt::Display for UnderExplorationReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidTargetDepth { min_walk_length } => write!(
                f,
                "invalid target write-chain depth min_walk_length={min_walk_length} (must be >= 1)"
            ),
            Self::InvalidSlotCount { num_slots } => write!(
                f,
                "invalid mutable slot count num_slots={num_slots} (must be >= 1)"
            ),
            Self::NoWritesObserved { required_depth } => write!(
                f,
                "0 valid writes observed; causal write-chain depth {required_depth} required"
            ),
            Self::BrokenEnvScheduleLink {
                max_observed_depth,
                required_depth,
                broken_links,
            } => write!(
                f,
                "broken EnvSchedule boundary link ({broken_links} gap/panic step(s)): max chain depth {max_observed_depth} < {required_depth}"
            ),
            Self::OnlyDepthOneLocalWrites {
                steps_observed,
                distinct_slots_written,
                required_depth,
            } => write!(
                f,
                "only independent depth-1 local writes observed ({steps_observed} step(s) across {distinct_slots_written} slot(s)); required causal RMW depth is {required_depth}"
            ),
            Self::InsufficientChainDepth {
                max_observed_depth,
                required_depth,
                steps_observed,
                recommended_walk_steps,
            } => write!(
                f,
                "max observed causal write-chain depth {max_observed_depth} < {required_depth} after {steps_observed} step(s) (recommended random-walk horizon >= {recommended_walk_steps})"
            ),
        }
    }
}

/// Bounded write-chain / read-modify-write (RMW) walk coverage tracker modeled
/// on Guo et al. (*"How Far Must a Test Explore? Certifying Composable
/// Read-Write Interfaces from Their Own Random Edits"*, arXiv:2611.11899).
///
/// Tracks Lamport-style causal write depth per mutable slot (`slot_depth`):
/// - Unwritten slots have causal depth `0`.
/// - A write `w := f(r_1, ..., r_k)` updates `slot_depth[w] = 1 + max_i slot_depth[r_i]`
///   (overwriting `w`'s previous live depth so a constant overwrite `w := c`
///   resets `slot_depth[w]` to `1` rather than falsely extending an overwritten chain!).
/// - A broken environment-boundary step (`env_callee.is_some() && !env_link_satisfied`)
///   clears `slot_depth[w]` (`0`) and increments `broken_env_links` so gapped
///   schedules cannot bridge causal depth across missing/panicking calls.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WriteChainCoverageBound {
    num_slots: usize,
    min_walk_length: usize,
    live_slot_depths: BTreeMap<String, usize>,
    ever_written_slots: BTreeSet<String>,
    max_observed_depth: usize,
    steps_observed: usize,
    rmw_transitions_observed: usize,
    broken_env_links: usize,
}

impl WriteChainCoverageBound {
    /// Creates a new [`WriteChainCoverageBound`] over `num_slots` ($m$) mutable
    /// variables/channels requiring causal write-chain depth `min_walk_length` ($d$).
    pub fn new(num_slots: usize, min_walk_length: usize) -> Self {
        Self {
            num_slots,
            min_walk_length,
            live_slot_depths: BTreeMap::new(),
            ever_written_slots: BTreeSet::new(),
            max_observed_depth: 0,
            steps_observed: 0,
            rmw_transitions_observed: 0,
            broken_env_links: 0,
        }
    }

    /// Convenience constructor for single-pool causal depth tracking (`num_slots = 1`).
    pub fn with_target_depth(min_walk_length: usize) -> Self {
        Self::new(1, min_walk_length)
    }

    /// Configured number of mutable slots $m$.
    #[inline]
    pub fn num_slots(&self) -> usize {
        self.num_slots
    }

    /// Required causal write-chain / RMW depth $d$.
    #[inline]
    pub fn min_walk_length(&self) -> usize {
        self.min_walk_length
    }

    /// Computes the coupon-collector random-walk step bound
    /// $\ell(m, d) = \lceil d \cdot m \cdot H_m \rceil$ required in expectation
    /// for uniform random edits over $m$ mutable slots to witness a causal
    /// read-modify-write chain of depth $d$ (`0` when $m = 0$ or $d = 0$, and
    /// exact $d$ when $m = 1$).
    pub fn compute_random_walk_step_bound(num_slots: usize, min_walk_length: usize) -> usize {
        if num_slots == 0 || min_walk_length == 0 {
            return 0;
        }
        if num_slots == 1 {
            return min_walk_length;
        }
        fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
            while b != 0 {
                let r = a % b;
                a = b;
                b = r;
            }
            a
        }

        let m_u128 = num_slots as u128;
        let d_u128 = min_walk_length as u128;

        // Exact reduced rational harmonic sum H_m = numer / denom in u128
        // (lcm(1..=88) < 2^128, eliminating +1 ceiling drift on exact integer
        // products such as m=3, d=2 -> 11 and m=6, d=10 -> 147).
        let mut exact_rational: Option<(u128, u128)> = Some((0u128, 1u128));
        for k in 1..=num_slots {
            let Some((numer, denom)) = exact_rational else {
                break;
            };
            let ku = k as u128;
            let g = gcd_u128(denom, ku);
            let ku_div_g = ku / g;
            let denom_div_g = denom / g;
            if let Some(next_denom) = denom.checked_mul(ku_div_g)
                && let Some(scaled_num) = numer.checked_mul(ku_div_g)
                && let Some(raw_num) = scaled_num.checked_add(denom_div_g)
            {
                let g2 = gcd_u128(raw_num, next_denom);
                exact_rational = Some((raw_num / g2, next_denom / g2));
            } else {
                exact_rational = None;
                break;
            }
        }

        if let Some((numer, mut denom)) = exact_rational {
            let gm = gcd_u128(m_u128, denom);
            let m_red = m_u128 / gm;
            denom /= gm;
            let gd = gcd_u128(d_u128, denom);
            let d_red = d_u128 / gd;
            denom /= gd;
            if let Some(total_num) = d_red
                .checked_mul(m_red)
                .and_then(|x| x.checked_mul(numer))
            {
                let q = total_num / denom;
                let r = total_num % denom;
                let exact_ceil = q.saturating_add(u128::from(r != 0));
                return exact_ceil.min(usize::MAX as u128) as usize;
            }
        }

        // High-precision ceiling fallback when `m > 88` overflows `u128` rational lcm.
        const SCALE: u128 = 1_000_000_000_000_000_000;
        let mut harmonic_scaled: u128 = 0;
        for k in 1..=num_slots {
            let ku = k as u128;
            harmonic_scaled = harmonic_scaled.saturating_add((SCALE + ku - 1) / ku);
        }
        let prod = d_u128
            .saturating_mul(m_u128)
            .saturating_mul(harmonic_scaled);
        let ceil_steps = (prod + SCALE - 1) / SCALE;
        ceil_steps.min(usize::MAX as u128) as usize
    }

    /// Minimum random-walk step horizon $\ell(m, d)$ for `(self.num_slots, self.min_walk_length)`.
    #[inline]
    pub fn random_walk_step_bound(&self) -> usize {
        Self::compute_random_walk_step_bound(self.num_slots, self.min_walk_length)
    }

    /// Clears live per-slot causal depths at a trial/trace boundary while
    /// preserving cumulative campaign counters (`max_observed_depth`,
    /// `steps_observed`, `distinct_slots_written`, `broken_env_links`) so an
    /// independent subsequent trial cannot chain onto stale live writes.
    pub fn reset_live_slots(&mut self) {
        self.live_slot_depths.clear();
    }

    /// Maximum contiguous causal write-chain depth observed so far.
    #[inline]
    pub fn max_observed_depth(&self) -> usize {
        self.max_observed_depth
    }

    /// Current live causal depth of `slot` (`0` if unwritten, overwritten by a
    /// broken env step, or unknown).
    #[inline]
    pub fn current_slot_depth(&self, slot: &str) -> usize {
        self.live_slot_depths.get(slot).copied().unwrap_or(0)
    }

    /// Total valid write steps observed.
    #[inline]
    pub fn steps_observed(&self) -> usize {
        self.steps_observed
    }

    /// Count of distinct mutable slots written at least once.
    #[inline]
    pub fn distinct_slots_written(&self) -> usize {
        self.ever_written_slots.len()
    }

    /// Count of broken environment-boundary links encountered.
    #[inline]
    pub fn broken_env_links(&self) -> usize {
        self.broken_env_links
    }

    /// Records a single [`WriteChainStep`], updating live per-slot causal depth
    /// and returning the newly assigned live causal depth of `step.written_slot`
    /// (`0` if `written_slot` is empty, configuration is invalid, or `env_link_satisfied` is `false`).
    pub fn observe_step(&mut self, step: &WriteChainStep) -> usize {
        if self.num_slots == 0 || self.min_walk_length == 0 || step.written_slot.trim().is_empty() {
            return 0;
        }
        if !step.env_link_satisfied {
            self.broken_env_links += 1;
            self.live_slot_depths.remove(&step.written_slot);
            return 0;
        }

        let max_dep = step
            .read_slots
            .iter()
            .filter_map(|src| self.live_slot_depths.get(src).copied())
            .max()
            .unwrap_or(0);
        let new_depth = 1usize.saturating_add(max_dep);
        if max_dep >= 1 {
            self.rmw_transitions_observed += 1;
        }
        self.steps_observed += 1;
        self.ever_written_slots.insert(step.written_slot.clone());
        self.live_slot_depths
            .insert(step.written_slot.clone(), new_depth);
        if new_depth > self.max_observed_depth {
            self.max_observed_depth = new_depth;
        }
        new_depth
    }

    /// Observes an ordered sequence of [`WriteChainStep`]s and returns the
    /// maximum causal chain depth reached across all observations so far.
    pub fn observe_write_chain(&mut self, steps: &[WriteChainStep]) -> usize {
        for s in steps {
            self.observe_step(s);
        }
        self.max_observed_depth
    }

    /// Simulates `planned_steps` against a clone of `schedule`: a step's
    /// environment link is satisfied iff `schedule.next_action` yields
    /// [`crate::instrument::EnvAction::ReturnBytes`] passing
    /// `schedule.validate_callee_payload` (accepting empty payloads only when
    /// `schedule.expected_return_size` explicitly registers a `0`-byte `()` return).
    /// Panicking or unscheduled (`PassThrough`) calls break the causal chain at
    /// `step.written_slot`.
    pub fn observe_env_schedule(
        &mut self,
        schedule: &EnvSchedule,
        planned_steps: &[EnvScheduledWriteStep],
    ) -> usize {
        let mut sim = schedule.clone();
        for (call_idx, planned) in planned_steps.iter().enumerate() {
            let link_ok = match sim.next_action(&planned.callee, call_idx) {
                crate::instrument::EnvAction::ReturnBytes(bytes) => {
                    let non_empty_or_zst = !bytes.is_empty()
                        || sim.expected_return_size(&planned.callee) == Some(0);
                    non_empty_or_zst
                        && sim.validate_callee_payload(&planned.callee, &bytes).is_ok()
                }
                crate::instrument::EnvAction::PanicOnCall(_)
                | crate::instrument::EnvAction::PassThrough => false,
            };
            self.observe_step(&WriteChainStep {
                written_slot: planned.written_slot.clone(),
                read_slots: planned.read_slots.clone(),
                env_callee: Some(planned.callee.clone()),
                env_link_satisfied: link_ok,
            });
        }
        self.max_observed_depth
    }

    /// Returns `true` iff configuration is valid (`num_slots >= 1` and
    /// `min_walk_length >= 1`) AND an unbroken causal write/RMW chain of length
    /// `>= self.min_walk_length` has been observed.
    pub fn is_depth_certified(&self) -> bool {
        self.num_slots >= 1
            && self.min_walk_length >= 1
            && self.max_observed_depth >= self.min_walk_length
    }

    /// Returns `None` iff [`Self::is_depth_certified`] holds, or a structured
    /// [`UnderExplorationReason`] pinpointing why depth $d$ is not yet certified.
    pub fn under_exploration_reason(&self) -> Option<UnderExplorationReason> {
        if self.min_walk_length == 0 {
            return Some(UnderExplorationReason::InvalidTargetDepth {
                min_walk_length: 0,
            });
        }
        if self.num_slots == 0 {
            return Some(UnderExplorationReason::InvalidSlotCount { num_slots: 0 });
        }
        if self.max_observed_depth >= self.min_walk_length {
            return None;
        }
        if self.broken_env_links > 0 {
            return Some(UnderExplorationReason::BrokenEnvScheduleLink {
                max_observed_depth: self.max_observed_depth,
                required_depth: self.min_walk_length,
                broken_links: self.broken_env_links,
            });
        }
        if self.steps_observed == 0 || self.max_observed_depth == 0 {
            return Some(UnderExplorationReason::NoWritesObserved {
                required_depth: self.min_walk_length,
            });
        }
        if self.max_observed_depth == 1 {
            return Some(UnderExplorationReason::OnlyDepthOneLocalWrites {
                steps_observed: self.steps_observed,
                distinct_slots_written: self.ever_written_slots.len(),
                required_depth: self.min_walk_length,
            });
        }
        Some(UnderExplorationReason::InsufficientChainDepth {
            max_observed_depth: self.max_observed_depth,
            required_depth: self.min_walk_length,
            steps_observed: self.steps_observed,
            recommended_walk_steps: self.random_walk_step_bound(),
        })
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

    #[test]
    fn arg_pin_constraint_separates_arg_pin_from_ret_pin_and_handles_zero_arg_calls() {
        let dict = MirInputDictionary::new();
        let locked = BTreeMap::new();

        // 1. 0-arg external call: `arg_pin_term` is `true` on `&[]`, so `neg_arg_pin_term`
        //    is `false` (unsatisfiable), while `pin_term` still compares `ret_bytes`.
        let zero_arg = ArgPinConstraint::new(0, "ext_tick", 1, Vec::new(), vec![7, 0, 0, 0]);
        assert!(zero_arg.is_zero_arg());
        assert!(arg_pin_term(&zero_arg, &[]));
        assert!(!neg_arg_pin_term(&zero_arg, &[]));
        assert!(pin_term(&zero_arg, &[], &[7, 0, 0, 0]));
        assert!(!pin_term(&zero_arg, &[], &[8, 0, 0, 0]));
        assert_eq!(zero_arg.domain_cardinality(), Some(1));
        assert!(zero_arg.is_arg_domain_exhausted());
        assert_eq!(negate_arg_pin(&zero_arg, &dict, &locked, 0), None);

        let guard = ConcolicBranchGuard::new_equality(
            0,
            Some("magic".to_string()),
            0x414E_4E4C,
            0x414E_4E4C,
            32,
        );
        match relax_pin_constraint(&[guard.clone()], &[zero_arg.clone()], 0, &dict, 0) {
            Some(RelaxPinResult::FallbackReturnPerturbation {
                pin_idx,
                reason,
                prefix_guards,
                schedule,
                ..
            }) => {
                assert_eq!(pin_idx, 0);
                assert_eq!(reason, ArgPinFallbackReason::ZeroArgCall);
                assert_eq!(prefix_guards, vec![guard]);
                let q = schedule.callee_queues.get("ext_tick").expect("ext_tick queue");
                assert_ne!(q[0].as_slice(), &[7, 0, 0, 0]);
            }
            other => panic!("expected FallbackReturnPerturbation for 0-arg call, got {other:?}"),
        }

        // 2. Shifting `before_guard_idx` preserves `arg_pin_term`, `neg_arg_pin_term`, and `pin_term`.
        let one_arg = ArgPinConstraint::new(
            1,
            "ext_oracle",
            2,
            vec![1025u32.to_le_bytes().to_vec()],
            42u32.to_le_bytes().to_vec(),
        );
        let shifted = one_arg.shift_guard_idx(3);
        assert_eq!(shifted.before_guard_idx, 5);
        for cand_arg in [1025u32, 2048u32] {
            let args = vec![cand_arg.to_le_bytes().to_vec()];
            assert_eq!(shifted.arg_pin_term(&args), one_arg.arg_pin_term(&args));
            assert_eq!(
                shifted.neg_arg_pin_term(&args),
                one_arg.neg_arg_pin_term(&args)
            );
            for cand_ret in [42u32, 99u32] {
                let ret = cand_ret.to_le_bytes();
                assert_eq!(shifted.pin_term(&args, &ret), one_arg.pin_term(&args, &ret));
            }
        }
        // Mutating only the oracle return value satisfies `¬ pin_term` but NOT `neg_arg_pin_term`.
        let same_arg = vec![1025u32.to_le_bytes().to_vec()];
        let diff_ret = 99u32.to_le_bytes();
        assert!(!one_arg.pin_term(&same_arg, &diff_ret));
        assert!(!one_arg.neg_arg_pin_term(&same_arg));
    }

    #[test]
    fn relax_pin_constraint_preserves_prefix_guards_and_earlier_call_pins_across_multi_call_chains() {
        let mut dict = MirInputDictionary::new();
        dict.add_field_hint("payload_len", 2048);
        dict.add_field_hint("payload_len", 4096);
        dict.add_field_hint("step_arg", 77);

        let g0 = ConcolicBranchGuard::new_equality(
            0,
            Some("magic".to_string()),
            0x414E_4E4C,
            0x414E_4E4C,
            32,
        );
        let g1 = ConcolicBranchGuard::new_equality(
            1,
            Some("mode".to_string()),
            2,
            2,
            32,
        );
        let g2 = ConcolicBranchGuard::new_equality(
            2,
            Some("post_flag".to_string()),
            1,
            1,
            32,
        );

        let pin0 = ArgPinConstraint::new(
            0,
            "ext_stage1",
            1,
            vec![100u32.to_le_bytes().to_vec()],
            500u32.to_le_bytes().to_vec(),
        )
        .with_arg_field_sources(vec![Some("payload_len".to_string())]);

        let pin1 = ArgPinConstraint::new(
            1,
            "ext_stage2",
            2,
            vec![
                100u32.to_le_bytes().to_vec(),
                10u32.to_le_bytes().to_vec(),
            ],
            900u32.to_le_bytes().to_vec(),
        )
        .with_arg_field_sources(vec![
            Some("payload_len".to_string()),
            Some("step_arg".to_string()),
        ]);

        // Relaxing `pin_idx = 1` (the second call) must:
        // - preserve `guards[..pin1.before_guard_idx]` = `[g0, g1]` (NOT `g2`),
        // - preserve `pins[..1]` = `[pin0]` (keeping `payload_len == 100` and pushing
        //   `pin0.ret_bytes = 500` into `ext_stage1`'s schedule),
        // - negate `pin1`'s argument tuple by varying `"step_arg"` (`!= 10`) while
        //   keeping `pin1`'s first argument (`"payload_len" == 100`) locked!
        let relaxed = relax_pin_constraint(
            &[g0.clone(), g1.clone(), g2],
            &[pin0.clone(), pin1.clone()],
            1,
            &dict,
            0,
        )
        .expect("relax pin 1");

        match relaxed {
            RelaxPinResult::RelaxedArgPin {
                pin_idx,
                callee,
                prefix_guards,
                prefix_pins,
                new_arg_tuple,
                input_field_overrides,
                schedule,
            } => {
                assert_eq!(pin_idx, 1);
                assert_eq!(callee, "ext_stage2");
                assert_eq!(prefix_guards, vec![g0, g1]);
                assert_eq!(prefix_pins, vec![pin0.clone()]);
                assert!(pin1.neg_arg_pin_term(&new_arg_tuple));
                // First argument of pin1 (`payload_len`) stays locked to pin0's concrete argument `100`.
                assert_eq!(new_arg_tuple[0], 100u32.to_le_bytes().to_vec());
                assert_ne!(new_arg_tuple[1], 10u32.to_le_bytes().to_vec());
                assert_eq!(input_field_overrides.get("magic"), Some(&0x414E_4E4C));
                assert_eq!(input_field_overrides.get("mode"), Some(&2));
                assert_eq!(input_field_overrides.get("payload_len"), Some(&100));
                assert!(!input_field_overrides.contains_key("post_flag"));
                // Prefix call `ext_stage1` has its exact return value `500` pinned in `schedule`.
                assert_eq!(
                    schedule.callee_queues.get("ext_stage1").unwrap()[0],
                    500u32.to_le_bytes().to_vec()
                );
                // The target call's return is unconstrained under `negArgPinTerm`
                // (`relaxPinConstraint` asserts no `pinTerm` on the target), so it is
                // not scheduled: the call passes through on its new arguments.
                assert!(!schedule.callee_queues.contains_key("ext_stage2"));
                assert_eq!(schedule.expected_return_size("ext_stage2"), Some(4));
            }
            other => panic!("expected RelaxedArgPin for pin 1, got {other:?}"),
        }
    }

    #[test]
    fn synthesize_concolic_trials_exhausts_bool_and_bounded_u8_domains_without_loops_or_duplicates() {
        let dict = MirInputDictionary::new();
        let sched_gen = EnvScheduleGenerator::new(&dict)
            .with_horizon_steps(4)
            .with_panic_injection_pct(0)
            .with_callee_return_layout("ext_bool", LayoutSpec::Scalar(ScalarLayout::u8()));

        let g0 = ConcolicBranchGuard::new_equality(
            0,
            Some("magic".to_string()),
            0x414E_4E4C,
            0x414E_4E4C,
            32,
        );
        // `flag` has `bool` layout (cardinality 2: `{0, 1}`), starting at `0`.
        let bool_pin = ArgPinConstraint::new(
            0,
            "ext_bool",
            1,
            vec![vec![0u8]],
            vec![10u8],
        )
        .with_arg_layouts(vec![ScalarLayout::bool_layout()])
        .with_arg_field_sources(vec![Some("flag".to_string())]);

        assert_eq!(bool_pin.domain_cardinality(), Some(2));
        assert!(!bool_pin.is_arg_domain_exhausted());

        let base_fields = BTreeMap::from([
            ("magic".to_string(), 0x414E_4E4C),
            ("flag".to_string(), 0),
        ]);
        let mut u = Unstructured::new(&[0x55; 32]);
        let plans = sched_gen.synthesize_concolic_trials(
            &base_fields,
            std::slice::from_ref(&g0),
            std::slice::from_ref(&bool_pin),
            8,
            &mut u,
        );

        // Exactly 1 `NegateCallArg` trial is possible for `bool` (`flag = 1`), after which
        // the generator must gracefully fall back to `PerturbOracleReturn` and `FlipBranchGuard`
        // without emitting duplicate `(input_fields, schedule)` plans.
        let arg_neg_plans: Vec<_> = plans
            .iter()
            .filter(|p| matches!(p.phase, ConcolicTrialPhase::NegateCallArg { .. }))
            .collect();
        assert_eq!(
            arg_neg_plans.len(),
            1,
            "bool domain {{0, 1}} has exactly 1 distinct alternative argument: {arg_neg_plans:?}"
        );
        assert_eq!(arg_neg_plans[0].input_fields.get("magic"), Some(&0x414E_4E4C));
        assert_eq!(arg_neg_plans[0].input_fields.get("flag"), Some(&1));

        assert!(
            plans.iter().any(|p| matches!(
                p.phase,
                ConcolicTrialPhase::PerturbOracleReturn {
                    reason: ArgPinFallbackReason::DomainExhausted,
                    ..
                }
            )),
            "must fall back to PerturbOracleReturn(DomainExhausted) once bool domain is exhausted: {plans:?}"
        );
        assert!(
            plans
                .iter()
                .any(|p| matches!(p.phase, ConcolicTrialPhase::FlipBranchGuard { .. })),
            "must also explore FlipBranchGuard after argument & return phases: {plans:?}"
        );

        // Bounded `u8` sub-range `10..=12` (cardinality 3: `{10, 11, 12}`):
        let mut u8_pin = ArgPinConstraint::new(
            0,
            "ext_u8_range",
            1,
            vec![vec![10u8]],
            vec![1u8],
        )
        .with_arg_layouts(vec![ScalarLayout::with_valid_range(1, false, 10, 12)])
        .with_arg_field_sources(vec![Some("code".to_string())]);
        assert_eq!(u8_pin.domain_cardinality(), Some(3));
        let mut seen_u8 = BTreeSet::from([10u8]);
        for step in 0..5 {
            if let Some(next_tuple) = u8_pin.negate_arg_pin(&dict, &BTreeMap::new(), step) {
                let b = next_tuple[0][0];
                assert!((10..=12).contains(&b), "out-of-range u8 arg {b}");
                assert!(seen_u8.insert(b), "duplicate u8 arg {b}");
                u8_pin.record_excluded_arg_tuple(next_tuple);
            } else {
                break;
            }
        }
        assert_eq!(seen_u8, BTreeSet::from([10u8, 11, 12]));
        assert!(u8_pin.is_arg_domain_exhausted());
        assert_eq!(u8_pin.negate_arg_pin(&dict, &BTreeMap::new(), 0), None);
    }

    #[test]
    fn relax_and_flip_respect_inequality_guards_pin_locks_and_shared_field_sources() {
        let dict = MirInputDictionary::new();
        let le = |v: u32| v.to_le_bytes().to_vec();
        let field = |name: &str| Some(name.to_string());

        // `payload_len > 1024`: the else polarity is `payload_len <= 1024`, so a
        // concrete witness such as `1026` (which takes the then-branch) can never
        // satisfy it; inequality guards constrain but never pin their field.
        let gt = |concrete: u128| {
            ConcolicBranchGuard::new_comparison(
                0,
                field("payload_len"),
                ConcolicGuardOp::Gt,
                concrete,
                1024,
                32,
            )
        };
        let g_then = gt(2048);
        assert!(g_then.taken && g_then.effective_term(1025) && !g_then.effective_term(1024));
        assert_eq!(g_then.pinned_value(), None);
        let g_else = gt(64);
        assert!(!g_else.taken && g_else.effective_term(64) && !g_else.effective_term(1026));
        assert_eq!(
            ConcolicBranchGuard::new_equality(1, field("magic"), 7, 7, 32).pinned_value(),
            Some(7)
        );
        assert_eq!(
            ConcolicBranchGuard::new_comparison(1, field("magic"), ConcolicGuardOp::Ne, 7, 7, 32)
                .pinned_value(),
            Some(7)
        );
        assert_eq!(ConcolicGuardOp::Lt.witness(0, true, 32), None);
        assert_eq!(ConcolicGuardOp::Gt.witness(u32::MAX as u128, true, 32), None);
        assert_eq!(ConcolicGuardOp::Ge.witness(1024, false, 32), Some(1023));

        // `relaxPinConstraint` keeps the argument inside the prefix guard's region.
        for (guard, cur, inside) in [
            (&g_then, 2048u32, (|v: u128| v > 1024) as fn(u128) -> bool),
            (&g_else, 65u32, (|v: u128| v <= 1024) as fn(u128) -> bool),
        ] {
            let pin = ArgPinConstraint::new(0, "ext_oracle", 1, vec![le(cur)], le(1))
                .with_arg_field_sources(vec![field("payload_len")]);
            let mut seen = BTreeSet::new();
            for attempt in 0..6 {
                let guards = std::slice::from_ref(guard);
                match relax_pin_constraint(guards, &[pin.clone()], 0, &dict, attempt) {
                    Some(RelaxPinResult::RelaxedArgPin {
                        new_arg_tuple,
                        input_field_overrides,
                        ..
                    }) => {
                        let v = decode_scalar_le_bytes(&new_arg_tuple[0]);
                        assert!(inside(v), "argument {v} left the prefix guard region");
                        assert_ne!(v, u128::from(cur));
                        assert_eq!(input_field_overrides.get("payload_len"), Some(&v));
                        seen.insert(v);
                    }
                    other => panic!("expected RelaxedArgPin, got {other:?}"),
                }
            }
            assert!(seen.len() > 1, "successive attempts explore distinct arguments");
        }

        // `flipBranchGuard` lands on the opposite region and refuses to move a
        // field that an earlier pinned call reads.
        let no_fields = BTreeMap::new();
        let f = flip_branch_guard(&no_fields, std::slice::from_ref(&g_then), &[], 0, &dict, 0)
            .expect("flip then-branch");
        assert!(f.flipped_bits <= 1024 && f.input_fields["payload_len"] == f.flipped_bits);
        let f = flip_branch_guard(&no_fields, std::slice::from_ref(&g_else), &[], 0, &dict, 0)
            .expect("flip else-branch");
        assert!(f.flipped_bits > 1024);
        let earlier_pin = ArgPinConstraint::new(0, "ext_first", 0, vec![le(2048)], le(9))
            .with_arg_field_sources(vec![field("payload_len")]);
        assert!(
            flip_branch_guard(&no_fields, &[g_then.clone()], &[earlier_pin], 0, &dict, 0).is_none()
        );

        // Argument positions reading the same field always receive the same value.
        let twin = ArgPinConstraint::new(0, "ext_two", 0, vec![le(5), le(5)], le(0))
            .with_arg_field_sources(vec![field("payload_len"), field("payload_len")]);
        for attempt in 0..8 {
            let t = twin
                .negate_arg_pin(&dict, &BTreeMap::new(), attempt)
                .expect("negate twin pin");
            assert_eq!(t[0], t[1]);
            assert_ne!(t[0], le(5));
        }

        // `synthesize_concolic_trials` on a `u32` pin caps Phase 1 at `ceil(max_trials / 2)`
        // so Phase 2 (`PerturbOracleReturn` with `NegationRoundCapReached`) and Phase 3
        // (`FlipBranchGuard` with registered return sizes) also run.
        let sched_gen = EnvScheduleGenerator::new(&dict)
            .with_panic_injection_pct(0)
            .with_callee_return_layout("ext_u32", LayoutSpec::Scalar(ScalarLayout::u32()));
        let u32_pin = ArgPinConstraint::new(0, "ext_u32", 1, vec![le(2048)], le(99))
            .with_arg_field_sources(vec![field("payload_len")]);
        let base_fields = BTreeMap::from([("payload_len".to_string(), 2048u128)]);
        let mut u = Unstructured::new(&[0x33; 32]);
        let plans = sched_gen.synthesize_concolic_trials(
            &base_fields,
            std::slice::from_ref(&g_then),
            std::slice::from_ref(&u32_pin),
            6,
            &mut u,
        );
        assert!(plans.iter().any(|p| matches!(
            p.phase,
            ConcolicTrialPhase::PerturbOracleReturn {
                reason: ArgPinFallbackReason::NegationRoundCapReached,
                ..
            }
        )));
        let flip_after_pin = flip_branch_guard(
            &base_fields,
            &[
                g_then.clone(),
                ConcolicBranchGuard::new_equality(1, field("magic"), 7, 7, 32),
            ],
            std::slice::from_ref(&u32_pin),
            1,
            &dict,
            0,
        )
        .expect("flip second guard after pin");
        assert_eq!(
            flip_after_pin.schedule.expected_return_size("ext_u32"),
            Some(4)
        );

        // Conflicting prefix locks (e.g., `payload_len > 1024` AND an earlier pin locking
        // `payload_len = 50`) or singleton return domains (`valid_start == valid_end`) are
        // rejected instead of emitting invalid or duplicate trials.
        let bad_prefix_pin = ArgPinConstraint::new(0, "ext_first", 0, vec![le(50)], le(1))
            .with_arg_field_sources(vec![field("payload_len")]);
        let second_pin = ArgPinConstraint::new(1, "ext_second", 1, vec![le(10)], le(2))
            .with_arg_field_sources(vec![field("magic")]);
        assert!(
            relax_pin_constraint(
                std::slice::from_ref(&g_then),
                &[bad_prefix_pin, second_pin],
                1,
                &dict,
                0,
            )
            .is_none()
        );
        let singleton_gen = EnvScheduleGenerator::new(&dict)
            .with_panic_injection_pct(0)
            .with_callee_return_layout(
                "ext_const",
                LayoutSpec::Scalar(ScalarLayout::with_valid_range(1, false, 7, 7)),
            );
        let zero_pin = ArgPinConstraint::new(0, "ext_const", 0, Vec::new(), vec![7u8]);
        assert!(
            relax_pin_constraint_with_generator(&singleton_gen, &no_fields, &[], &[zero_pin], 0, 0)
                .is_none()
        );

        // Two argument positions sharing a single field source with different scalar
        // widths (`u32` and `u8`) must never clamp only the narrower position to produce
        // an inconsistent `(1000, 255)` tuple; every synthesized tuple must use a value
        // that fits both layouts without clamping.
        let mixed_twin = ArgPinConstraint::new(0, "ext_mixed", 0, vec![le(5), vec![5u8]], le(0))
            .with_arg_layouts(vec![ScalarLayout::u32(), ScalarLayout::u8()])
            .with_arg_field_sources(vec![field("payload_len"), field("payload_len")]);
        for attempt in 0..8 {
            let t = mixed_twin
                .negate_arg_pin(&dict, &BTreeMap::new(), attempt)
                .expect("negate mixed-width twin pin");
            assert_eq!(decode_scalar_le_bytes(&t[0]), decode_scalar_le_bytes(&t[1]));
            assert!(decode_scalar_le_bytes(&t[0]) <= 255);
        }

        // Flipping `x >= 50_000` from false (`x = 50`) to true when an earlier guard
        // requires `x != 50_000` uses `ConcolicGuardOp::witnesses`'s `t + 1 = 50_001`
        // witness even with an empty dictionary.
        let g_ne = ConcolicBranchGuard::new_comparison(
            0,
            field("payload_len"),
            ConcolicGuardOp::Ne,
            50,
            50_000,
            32,
        );
        let g_ge = ConcolicBranchGuard::new_comparison(
            1,
            field("payload_len"),
            ConcolicGuardOp::Ge,
            50,
            50_000,
            32,
        );
        let flipped_ge =
            flip_branch_guard(&no_fields, &[g_ne, g_ge], &[], 1, &MirInputDictionary::new(), 0)
                .expect("flip x >= 50_000 under x != 50_000");
        assert!(flipped_ge.flipped_bits > 50_000);
    }

    #[test]
    fn spec_contract_oracle_probe_validation_and_verdict_classification() {
        let u32_layout = LayoutSpec::Scalar(ScalarLayout::u32());
        let unit_layout = LayoutSpec::Tuple {
            total_size: 0,
            elements: Vec::new(),
        };

        // Invalid identifiers, reserved `result` parameter, `old(...)` in `requires`,
        // nested `old(old(...))`, and unknown/non-`&mut` framed fields are rejected cleanly.
        let bad_fn = SpecContractOracleProbe::new(
            "not-an-ident",
            vec![SpecParamBinding::by_value("x", "u32", u32_layout.clone())],
            "u32",
            u32_layout.clone(),
            "x",
        );
        assert!(bad_fn.validate().is_err());

        let reserved_param = SpecContractOracleProbe::new(
            "foo",
            vec![SpecParamBinding::by_value(
                "result",
                "u32",
                u32_layout.clone(),
            )],
            "u32",
            u32_layout.clone(),
            "0u32",
        );
        assert!(reserved_param.validate().is_err());

        let old_in_requires = SpecContractOracleProbe::new(
            "foo",
            vec![SpecParamBinding::by_value("x", "u32", u32_layout.clone())],
            "u32",
            u32_layout.clone(),
            "x",
        )
        .with_requires("bad_old", "old(x) < 10u32");
        assert!(old_in_requires.validate().is_err());

        let nested_old = SpecContractOracleProbe::new(
            "foo",
            vec![SpecParamBinding::by_value("x", "u32", u32_layout.clone())],
            "u32",
            u32_layout.clone(),
            "x",
        )
        .with_ensures("nested", "result == old(old(x))");
        assert!(nested_old.validate().is_err());

        let non_mut_framed = SpecContractOracleProbe::new(
            "foo",
            vec![
                SpecParamBinding::by_value("x", "u32", u32_layout.clone())
                    .with_frame_preserved_fields(["f"]),
            ],
            "()",
            unit_layout.clone(),
            "()",
        );
        assert!(non_mut_framed.validate().is_err());

        // Sound padded struct contract with `&mut`, `old(...)`, framed field, and `EnvSchedule`.
        let padded_pair_layout = LayoutSpec::Struct {
            name: "PaddedPair".to_string(),
            total_size: 12,
            fields: vec![
                FieldLayout {
                    name: "tag".to_string(),
                    offset: 0,
                    layout: LayoutSpec::Scalar(ScalarLayout::u8()),
                },
                FieldLayout {
                    name: "active".to_string(),
                    offset: 4,
                    layout: u32_layout.clone(),
                },
                FieldLayout {
                    name: "framed".to_string(),
                    offset: 8,
                    layout: u32_layout.clone(),
                },
            ],
        };
        let sound_probe = SpecContractOracleProbe::new(
            "step_active_with_env",
            vec![
                SpecParamBinding::mut_ref("pair", "PaddedPair", padded_pair_layout.clone())
                    .with_frame_preserved_fields(["tag", "framed"]),
            ],
            "u32",
            u32_layout.clone(),
            "let delta: u32 = ext_delta(pair.active);\n\
             let bounded: u32 = delta & 7u32;\n\
             pair.active = pair.active + bounded;\n\
             pair.active",
        )
        .with_type_defs(
            "#[repr(C)]\n\
             #[derive(Copy, Clone, Debug, PartialEq, Eq)]\n\
             pub struct PaddedPair { pub tag: u8, pub active: u32, pub framed: u32 }",
        )
        .with_external_callee(SpecExternalCallee::new(
            "ext_delta",
            ["u32"],
            "u32",
            u32_layout.clone(),
        ))
        .with_requires("room_for_delta", "pair.active <= u32::MAX - 7u32")
        .with_ensures("ge_old", "pair.active >= old(pair.active)")
        .with_ensures("bounded_step", "result <= old(pair.active) + 7u32");

        let synthesized = sound_probe
            .synthesize_rust_probe()
            .expect("synthesize sound probe");
        assert!(synthesized.contains("pub fn __anneal_spec_check_step_active_with_env"));
        assert!(synthesized.contains("__anneal_old_expr_0"));
        assert!(synthesized.contains("__anneal_frame_old_pair_framed"));

        // Non-zero poison padding bytes at offsets `1..4` must NOT trigger a false
        // frame violation when `tag` and `framed` preserve their occupied bytes.
        let mut raw_ok = vec![0xAAu8; 12];
        raw_ok[0] = 5u8;
        raw_ok[4..8].copy_from_slice(&100u32.to_le_bytes());
        raw_ok[8..12].copy_from_slice(&777u32.to_le_bytes());

        let dict = MirInputDictionary::new();
        let sched_gen = EnvScheduleGenerator::new(&dict)
            .with_horizon_steps(2)
            .with_panic_injection_pct(0)
            .with_callee_return_layout("ext_delta", u32_layout.clone());
        let mut u = Unstructured::new(&[0x05; 64]);
        let mut sched = sched_gen.generate_schedule(&["ext_delta"], &mut u);

        let verdict_ok =
            verify_spec_postcondition_against_schedule(&sound_probe, &raw_ok, Some(&mut sched))
                .expect("evaluate sound probe");
        assert_eq!(verdict_ok, SpecPostconditionVerdict::VerifiedHold);

        // Precondition violated (`pair.active == u32::MAX`) -> `VacuouslyFiltered`, NOT `PanicOrTrap`.
        let mut raw_filtered = raw_ok.clone();
        raw_filtered[4..8].copy_from_slice(&u32::MAX.to_le_bytes());
        let verdict_filt = sound_probe
            .verify_spec_postcondition_against_schedule(&raw_filtered, None)
            .expect("evaluate filtered trial");
        assert_eq!(
            verdict_filt,
            SpecPostconditionVerdict::VacuouslyFiltered {
                failed_requires_index: 0,
                failed_requires_label: "room_for_delta".to_string(),
            }
        );
        assert!(!verdict_filt.is_verified_hold());
        assert!(!verdict_filt.is_mutant_killed());

        // Vacuous `requires(false)` batch report must NOT pass `is_sound_and_non_vacuous()`.
        let batch_vacuous = sound_probe
            .verify_spec_postcondition_batch(&[(raw_filtered, None)])
            .expect("vacuous batch");
        assert_eq!(batch_vacuous.vacuously_filtered_count, 1);
        assert_eq!(batch_vacuous.verified_hold_count, 0);
        assert!(!batch_vacuous.is_sound_and_non_vacuous());

        // Scheduled `PanicOnCall` -> `PanicOrTrap { phase: Body, .. }`.
        let panic_gen = EnvScheduleGenerator::new(&dict)
            .with_horizon_steps(1)
            .with_callee_return_layout("ext_delta", u32_layout.clone());
        let mut u_panic = Unstructured::new(&[0x11; 32]);
        let mut panic_sched = EnvSchedule::new();
        panic_gen.apply_strategy(
            &mut panic_sched,
            "ext_delta",
            &EnvStrategy::PanicOnCall(0),
            &mut u_panic,
        );
        let verdict_panic = sound_probe
            .verify_spec_postcondition_against_schedule(&raw_ok, Some(&mut panic_sched))
            .expect("evaluate panic trial");
        assert!(matches!(
            verdict_panic,
            SpecPostconditionVerdict::PanicOrTrap {
                phase: SpecExecPhase::Body,
                ..
            }
        ));
        assert!(verdict_panic.is_mutant_killed());

        // Lexical shadowing inside inner blocks must restore outer bindings on exit.
        let shadow_probe = SpecContractOracleProbe::new(
            "lexical_shadow",
            vec![SpecParamBinding::by_value("x", "u32", u32_layout.clone())],
            "u32",
            u32_layout,
            "let mut acc: u32 = x;\n\
             if x >= 0u32 {\n    \
                 let acc: u32 = 999u32;\n    \
                 let _ = acc;\n\
             }\n\
             acc",
        )
        .with_ensures("unchanged_outer", "result == x");
        let shadow_verdict = shadow_probe
            .verify_spec_postcondition_against_schedule(&42u32.to_le_bytes(), None)
            .expect("shadowing probe");
        assert_eq!(shadow_verdict, SpecPostconditionVerdict::VerifiedHold);
    }

    #[test]
    fn write_chain_coverage_bound_separates_local_writes_overwrites_and_rmw_walks() {
        // Boundary `d = 0` and `m = 0` configurations fail closed with exact reasons.
        let zero_d = WriteChainCoverageBound::new(3, 0);
        assert_eq!(zero_d.random_walk_step_bound(), 0);
        assert!(!zero_d.is_depth_certified());
        assert_eq!(
            zero_d.under_exploration_reason(),
            Some(UnderExplorationReason::InvalidTargetDepth { min_walk_length: 0 })
        );

        let zero_m = WriteChainCoverageBound::new(0, 2);
        assert_eq!(zero_m.random_walk_step_bound(), 0);
        assert!(!zero_m.is_depth_certified());
        assert_eq!(
            zero_m.under_exploration_reason(),
            Some(UnderExplorationReason::InvalidSlotCount { num_slots: 0 })
        );

        // Fresh tracker (`m = 3, d = 3`): coupon-collector bound ceil(3 * 3 * (1 + 1/2 + 1/3)) = ceil(16.5) = 17.
        let mut tracker = WriteChainCoverageBound::new(3, 3);
        assert_eq!(tracker.random_walk_step_bound(), 17);
        assert_eq!(WriteChainCoverageBound::compute_random_walk_step_bound(1, 4), 4);
        assert!(!tracker.is_depth_certified());
        assert_eq!(
            tracker.under_exploration_reason(),
            Some(UnderExplorationReason::NoWritesObserved { required_depth: 3 })
        );

        // Repeated independent depth-1 local writes (`x = 1; y = 2; z = 3; x = 4`) NEVER
        // sum to depth 3!
        tracker.observe_write_chain(&[
            WriteChainStep::local_write("x"),
            WriteChainStep::local_write("y"),
            WriteChainStep::local_write("z"),
            WriteChainStep::local_write("x"),
        ]);
        assert_eq!(tracker.max_observed_depth(), 1);
        assert!(!tracker.is_depth_certified());
        assert_eq!(
            tracker.under_exploration_reason(),
            Some(UnderExplorationReason::OnlyDepthOneLocalWrites {
                steps_observed: 4,
                distinct_slots_written: 3,
                required_depth: 3,
            })
        );

        // Depth 1 (`d = 1`) IS certified by a single local write.
        let mut d1 = WriteChainCoverageBound::with_target_depth(1);
        assert_eq!(d1.observe_step(&WriteChainStep::local_write("x")), 1);
        assert!(d1.is_depth_certified());
        assert_eq!(d1.under_exploration_reason(), None);

        // Reading `x` into `y` reaches depth 2 (`InsufficientChainDepth` for `d = 3`),
        // AND overwriting `y` with a constant (`local_write("y")`) resets `y`'s live
        // depth back to 1 so a subsequent `z := f(y)` gets depth 2, NOT stale depth 3!
        assert_eq!(
            tracker.observe_step(&WriteChainStep::dependent_write("y", ["x"])),
            2
        );
        assert!(!tracker.is_depth_certified());
        assert_eq!(
            tracker.under_exploration_reason(),
            Some(UnderExplorationReason::InsufficientChainDepth {
                max_observed_depth: 2,
                required_depth: 3,
                steps_observed: 5,
                recommended_walk_steps: 17,
            })
        );
        assert_eq!(tracker.observe_step(&WriteChainStep::local_write("y")), 1);
        assert_eq!(
            tracker.observe_step(&WriteChainStep::dependent_write("z", ["y"])),
            2
        );
        assert!(!tracker.is_depth_certified());

        // Self-RMW `z = f(z)` advances live depth of `z` from 2 -> 3 and certifies depth 3!
        assert_eq!(
            tracker.observe_step(&WriteChainStep::dependent_write("z", ["z"])),
            3
        );
        assert!(tracker.is_depth_certified());
        assert_eq!(tracker.under_exploration_reason(), None);

        // Broken `EnvSchedule` boundary step (`PassThrough` / `PanicOnCall`) clears the
        // target slot's live causal depth and surfaces `BrokenEnvScheduleLink`.
        let dict = MirInputDictionary::new();
        let panic_gen = EnvScheduleGenerator::new(&dict)
            .with_horizon_steps(3)
            .with_callee_return_layout("ext_hop", LayoutSpec::Scalar(ScalarLayout::u32()));
        let mut u = Unstructured::new(&[0x42; 64]);
        let mut gapped_sched = EnvSchedule::new();
        panic_gen.apply_strategy(
            &mut gapped_sched,
            "ext_hop",
            &EnvStrategy::Constant(1u32.to_le_bytes().to_vec()),
            &mut u,
        );
        gapped_sched.set_callee_panic_on_call("ext_hop", 1);

        let planned = vec![
            EnvScheduledWriteStep::new("ext_hop", "s0", std::iter::empty::<&str>()),
            EnvScheduledWriteStep::new("ext_hop", "s1", ["s0"]),
            EnvScheduledWriteStep::new("ext_hop", "s2", ["s1"]),
        ];
        let mut env_tracker = WriteChainCoverageBound::new(3, 3);
        env_tracker.observe_env_schedule(&gapped_sched, &planned);
        assert!(!env_tracker.is_depth_certified());
        assert_eq!(env_tracker.current_slot_depth("s1"), 0);
        assert_eq!(env_tracker.current_slot_depth("s2"), 1);
        assert!(matches!(
            env_tracker.under_exploration_reason(),
            Some(UnderExplorationReason::BrokenEnvScheduleLink {
                max_observed_depth: 1,
                required_depth: 3,
                broken_links: 1,
            })
        ));
    }

    #[test]
    fn spec_contract_oracle_probe_padding_semantic_eq_lazy_old_and_nested_mutations() {
        let u32_layout = LayoutSpec::Scalar(ScalarLayout::u32());
        let u128_layout = LayoutSpec::Scalar(ScalarLayout::unsigned(16));

        // 1. `old(result)` must be rejected by `validate()` so `synthesize_rust_probe`
        //    never emits uncompilable pre-body references to `result`.
        let bad_old_result = SpecContractOracleProbe::new(
            "bad_old_result",
            vec![SpecParamBinding::by_value("x", "u32", u32_layout.clone())],
            "u32",
            u32_layout.clone(),
            "x + 1u32",
        )
        .with_ensures("bad_ref", "result == old(result)");
        assert!(bad_old_result.validate().is_err());

        // 2. Poison padding bytes (`0xAA`), struct update `..*state`, semantic `==` / `assert_eq!`,
        //    nested `state.slots[idx]` compound `/=` & `%=`, `&mut` helper writeback, and
        //    short-circuit guarded `old(100u32 / denom)`!
        let state_layout = LayoutSpec::Struct {
            name: "PaddedSlots".to_string(),
            total_size: 24,
            fields: vec![
                FieldLayout {
                    name: "tag".to_string(),
                    offset: 0,
                    layout: LayoutSpec::Scalar(ScalarLayout::u8()),
                },
                FieldLayout {
                    name: "slots".to_string(),
                    offset: 4,
                    layout: LayoutSpec::Array {
                        elem: Box::new(u32_layout.clone()),
                        elem_stride: 4,
                        len: 4,
                    },
                },
                FieldLayout {
                    name: "framed".to_string(),
                    offset: 20,
                    layout: u32_layout.clone(),
                },
            ],
        };

        let probe = SpecContractOracleProbe::new(
            "update_padded_slots",
            vec![
                SpecParamBinding::mut_ref("state", "PaddedSlots", state_layout)
                    .with_frame_preserved_fields(["tag", "framed"]),
                SpecParamBinding::by_value("denom", "u32", u32_layout.clone()),
            ],
            "u32",
            u32_layout,
            "let () = ();\n\
             let (prev0, after0): (u32, u32) = bump_unit_helper(&mut state.slots[0], 6u32);\n\
             assert_eq!(after0, prev0 + 6u32);\n\
             state.slots[1] /= 2u32;\n\
             state.slots[2] %= 5u32;\n\
             let mut i: usize = 0usize;\n\
             let mut acc: u32 = 0u32;\n\
             while i < 3usize {\n    \
                 acc += state.slots[i];\n    \
                 i += 1usize;\n\
             }\n\
             *state = PaddedSlots { slots: state.slots, ..*state };\n\
             let rebuilt: PaddedSlots = PaddedSlots {\n    \
                 tag: state.tag,\n    \
                 slots: state.slots,\n    \
                 framed: state.framed,\n\
             };\n\
             assert_eq!(*state, rebuilt);\n\
             acc",
        )
        .with_type_defs(
            "#[repr(C)]\n\
             #[derive(Copy, Clone, Debug, PartialEq, Eq)]\n\
             pub struct PaddedSlots { pub tag: u8, pub slots: [u32; 4], pub framed: u32 }\n\
             pub fn bump_unit_helper(cell: &mut u32, add: u32) -> (u32, u32) {\n    \
                 let prev: u32 = *cell;\n    \
                 *cell += add;\n    \
                 (prev, *cell)\n\
             }",
        )
        .with_requires("bounded_slot0", "state.slots[0] <= 1000u32")
        .with_ensures(
            "guarded_lazy_old_div",
            "denom == 0u32 || old(100u32 / denom) <= 100u32",
        )
        .with_ensures(
            "semantic_struct_eq",
            "*state == PaddedSlots { tag: old(state.tag), slots: [old(state.slots[0]) + 6u32, old(state.slots[1]) / 2u32, old(state.slots[2]) % 5u32, old(state.slots[3])], framed: old(state.framed) }",
        );

        let mut packed = vec![0xAAu8; 28];
        packed[0] = 9u8;
        packed[4..8].copy_from_slice(&10u32.to_le_bytes());
        packed[8..12].copy_from_slice(&20u32.to_le_bytes());
        packed[12..16].copy_from_slice(&17u32.to_le_bytes());
        packed[16..20].copy_from_slice(&99u32.to_le_bytes());
        packed[20..24].copy_from_slice(&777u32.to_le_bytes());
        // `denom = 0` exercises short-circuit `denom == 0u32 || old(100u32 / denom) <= 100u32`!
        packed[24..28].copy_from_slice(&0u32.to_le_bytes());

        let verdict = probe
            .verify_spec_postcondition_against_schedule(&packed, None)
            .expect("evaluate padded/lazy-old probe");
        assert_eq!(verdict, SpecPostconditionVerdict::VerifiedHold);

        // 3. `u128::MAX` (> `i128::MAX`) must not wrap negative inside `to_signed_i128`.
        let u128_probe = SpecContractOracleProbe::new(
            "u128_high_bit_check",
            vec![SpecParamBinding::by_value("big", "u128", u128_layout.clone())],
            "u128",
            u128_layout,
            "big",
        )
        .with_ensures("exact_max", "result == u128::MAX && result > 1u128");
        let max_verdict = u128_probe
            .verify_spec_postcondition_against_schedule(&u128::MAX.to_le_bytes(), None)
            .expect("u128::MAX evaluation");
        assert_eq!(max_verdict, SpecPostconditionVerdict::VerifiedHold);
    }

    #[test]
    fn write_chain_coverage_bound_exact_rational_harmonic_zst_and_trial_reset() {
        // Exact integer coupon-collector products must NOT over-round by +1:
        // m = 3, d = 2 -> 2 * 3 * (1 + 1/2 + 1/3) = 2 * 5.5 = 11 (exact).
        assert_eq!(WriteChainCoverageBound::compute_random_walk_step_bound(3, 2), 11);
        // m = 6, d = 10 -> 10 * 6 * (1 + 1/2 + 1/3 + 1/4 + 1/5 + 1/6) = 10 * 14.7 = 147 (exact).
        assert_eq!(
            WriteChainCoverageBound::compute_random_walk_step_bound(6, 10),
            147
        );
        // m = 10, d = 1 -> ceil(10 * 7381 / 2520) = ceil(29.28968...) = 30.
        assert_eq!(
            WriteChainCoverageBound::compute_random_walk_step_bound(10, 1),
            30
        );

        // `env_link_satisfied = false` must fail closed even if `env_callee` is `None`.
        let mut unsatisfied_local = WriteChainCoverageBound::new(2, 2);
        assert_eq!(
            unsatisfied_local.observe_step(&WriteChainStep {
                written_slot: "x".to_string(),
                read_slots: Vec::new(),
                env_callee: None,
                env_link_satisfied: false,
            }),
            0
        );
        assert_eq!(unsatisfied_local.broken_env_links(), 1);
        assert_eq!(unsatisfied_local.current_slot_depth("x"), 0);

        // Zero-sized `()` (`0`-byte) external returns certify cleanly when `expected_return_size == Some(0)`,
        // while unregistered empty payloads remain rejected.
        let mut zst_sched = EnvSchedule::new().with_callee_return_size("ext_unit", 0);
        zst_sched.set_callee_default("ext_unit", Vec::new());
        let zst_plan = vec![
            EnvScheduledWriteStep::new("ext_unit", "a", std::iter::empty::<&str>()),
            EnvScheduledWriteStep::new("ext_unit", "b", ["a"]),
        ];
        let mut zst_tracker = WriteChainCoverageBound::new(2, 2);
        assert_eq!(zst_tracker.observe_env_schedule(&zst_sched, &zst_plan), 2);
        assert!(zst_tracker.is_depth_certified());

        let mut unreg_empty_sched = EnvSchedule::new();
        unreg_empty_sched.set_callee_default("ext_unreg", Vec::new());
        let unreg_plan = vec![EnvScheduledWriteStep::new(
            "ext_unreg",
            "a",
            std::iter::empty::<&str>(),
        )];
        let mut unreg_tracker = WriteChainCoverageBound::new(1, 1);
        assert_eq!(
            unreg_tracker.observe_env_schedule(&unreg_empty_sched, &unreg_plan),
            0
        );
        assert!(!unreg_tracker.is_depth_certified());

        // `reset_live_slots()` isolates independent trials while preserving cumulative maxima.
        let mut multi_trial = WriteChainCoverageBound::new(2, 2);
        assert_eq!(multi_trial.observe_step(&WriteChainStep::local_write("x")), 1);
        multi_trial.reset_live_slots();
        assert_eq!(multi_trial.current_slot_depth("x"), 0);
        assert_eq!(
            multi_trial.observe_step(&WriteChainStep::dependent_write("y", ["x"])),
            1
        );
        assert!(!multi_trial.is_depth_certified());
    }
}
