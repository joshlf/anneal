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

    /// Returns a `bit_width`-bit witness `v` with `(v <op> target) == want`, or
    /// `None` when no such value exists (e.g. `v < 0` or `v > u32::MAX`).
    pub fn witness(self, target: u128, want: bool, bit_width: u32) -> Option<u128> {
        let mask = width_mask(bit_width);
        let t = target & mask;
        [
            Some(t),
            t.checked_sub(1),
            t.checked_add(1).filter(|&v| v <= mask),
            Some(0),
            Some(mask),
        ]
        .into_iter()
        .flatten()
        .find(|&v| self.eval(v, t) == want)
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
                // `locked_bits` is valid for `layout` and satisfies every prefix guard
                // on `fname`.
                let clamped = layout.clamp_to_valid_bits(locked_bits);
                let encoded = encode_scalar_le_bytes(clamped, layout.size_bytes);
                let guards_ok = prefix_guards
                    .iter()
                    .filter(|g| g.field_name.as_deref() == Some(fname))
                    .all(|g| g.effective_term(locked_bits));
                if clamped == locked_bits
                    && LayoutSpec::Scalar(layout.clone()).validate_bytes(&encoded).is_ok()
                    && guards_ok
                {
                    vec![clamped]
                } else {
                    Vec::new()
                }
            } else {
                candidate_arg_bytes_for_layout(&layout, field_source, &self.arg_tuple[i], dict)
                    .iter()
                    .map(|b| decode_scalar_le_bytes(b))
                    .filter(|&bits| {
                        field_source.is_none_or(|fname| {
                            prefix_guards
                                .iter()
                                .filter(|g| g.field_name.as_deref() == Some(fname))
                                .all(|g| g.effective_term(bits))
                        })
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
        let mut candidates = vec![g.concrete_bits];
        if let Some(w) = g.op.witness(g.target_bits, g.taken, g.bit_width) {
            candidates.push(w);
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
    // The operator's own witness for the flipped polarity comes first (e.g. `x = t`
    // for an untaken `x == t`, `x = t` for a taken `x > t`).
    if let Some(w) =
        target_guard
            .op
            .witness(target_guard.target_bits, !target_guard.taken, target_guard.bit_width)
    {
        cands.push(w);
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
    }
}
