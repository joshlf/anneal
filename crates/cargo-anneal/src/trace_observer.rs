// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Runtime trace observer and Lean 4 `TraceCheck` module generator.
//!
//! Bridges compiled Rust artifacts to Anneal's coinductive `MIR -> ITree`
//! semantics (`Anneal.Rustc.V2026_06_01.TraceCheck`) along two design axes:
//!
//! 1. **Interposition & Branch Erasure**:
//!    - **Call-boundary interposition (`check_branches = false`)**: captures
//!      layout-aware argument and return byte slices at the root entry/exit and
//!      at unresolved external/callee boundaries (`MirCallE`), checking the
//!      resulting `RawByteTrace` against `mirObsErasedStatefulTree` via
//!      `checkRawByteTraceObsErasedBounded_sound` and
//!      `diagnoseRawByteTraceObsErasedBounded` without requiring internal
//!      `switchInt` branch instrumentation.
//!    - **Full branch + call observation (`check_branches = true`)**:
//!      additionally records `switchInt` branch tags (`MirObsE`) and checks the
//!      trace against `mirStatefulTree` via `checkRawByteTraceFullBounded_sound`
//!      and `diagnoseRawByteTraceFullBounded`.
//!    - **Inlining duality (`inlined_callee_modules`)**: callees placed in
//!      `inlinedCallees` (`Memory.callees`) are stepped transparently via
//!      `.tau` transitions in the Lean model rather than emitting `MirCallE`
//!      events.
//!
//! 2. **Layout-Aware Byte Capture, Safe Schedule Decoding & Shadow Provenance**:
//!    - **Padding-safe byte capture ([`TraceCapture`], [`capture_value_bytes`],
//!      [`value_as_raw_bytes`])**: captures only initialized field bytes at
//!      their compiler-computed `core::mem::offset_of!` offsets and leaves
//!      inter-field/trailing struct padding bytes as `None` (unknown) in
//!      [`capture_value_bytes`] (or `0` in [`value_as_raw_bytes`]), never
//!      reading uninitialized padding bytes from memory.
//!    - **Validity-checked schedule materialization ([`FromScheduleBytes`])**:
//!      scheduled `EnvAction::ReturnBytes` payloads are validated for exact byte
//!      length and bit-validity invariants (`bool`, `char`, `NonZero*`, enums,
//!      and structs) without `MaybeUninit::assume_init`.
//!    - **Shadow provenance table**: [`TraceRecorder::register_allocation`]
//!      maps watched runtime virtual address ranges `[base_addr, base_addr +
//!      byte_len)` to abstract MIR `(alloc_id, tag)` provenance so thin and
//!      wide pointers/references in raw byte slices decode to `Value.ptr` with
//!      relative offset `addr - base_addr`.

use std::any::Any;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt::{self, Write as _};
use std::mem;
use std::num::{
    NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128, NonZeroIsize, NonZeroU8,
    NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize,
};
use std::panic::{self, AssertUnwindSafe};

/// Error returned when a scheduled environment payload or layout-aware input
/// fails size or bit-validity checks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScheduleError {
    /// Payload byte length did not match the target type or layout size.
    PayloadSizeMismatch {
        /// Callee or type context where the mismatch occurred.
        context: String,
        /// Expected byte length (`size_of::<T>()` or `LayoutSpec::total_size()`).
        expected: usize,
        /// Actual byte length supplied.
        actual: usize,
    },
    /// Payload bytes violated a bit-validity invariant of the target type
    /// (for example, `bool > 1`, surrogate `char`, zero `NonZero*`, or an
    /// unrecognized enum discriminant).
    InvalidBitPattern {
        /// Callee or type context where the invalid bit pattern was rejected.
        context: String,
        /// Human-readable explanation of the violated validity invariant.
        reason: String,
    },
}

impl fmt::Display for ScheduleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PayloadSizeMismatch {
                context,
                expected,
                actual,
            } => write!(
                f,
                "schedule payload size mismatch for `{context}`: expected {expected} bytes, got {actual}"
            ),
            Self::InvalidBitPattern { context, reason } => write!(
                f,
                "invalid bit pattern in schedule payload for `{context}`: {reason}"
            ),
        }
    }
}

impl std::error::Error for ScheduleError {}

/// Layout-aware trace byte capture that writes `Some(byte)` at initialized field
/// offsets and leaves inter-field or trailing padding offsets untouched (`None`),
/// avoiding any read of uninitialized padding bytes.
///
/// Composite structs and unit enums in traced crates can derive this trait (and
/// [`FromScheduleBytes`]) via `#[anneal_trace::capture]`.
pub trait TraceCapture {
    /// Write the initialized field bytes of `self` into `dst` (which is
    /// pre-initialized to `None` of length `core::mem::size_of_val(self)`).
    /// Any padding offsets in `dst` must remain `None`.
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]);

    /// Write the niche byte representation for `Option::<Self>::None` when
    /// `size_of::<Option<Self>>() == size_of::<Self>()` (defaults to all-zero
    /// bytes, as used by `NonZero*` and references).
    fn write_niche_none_bytes(dst: &mut [Option<u8>]) {
        for slot in dst.iter_mut() {
            *slot = Some(0);
        }
    }
}

/// Capture the layout-aware byte representation of `val`, returning `Some(b)`
/// for every initialized field byte and `None` for unknown/padding bytes.
///
/// Unlike raw pointer byte copies, this function never reads padding bytes from
/// `val` and is completely free of Undefined Behavior under Miri even when
/// `val` contains uninitialized padding.
pub fn capture_value_bytes<T: TraceCapture + ?Sized>(val: &T) -> Vec<Option<u8>> {
    let size = mem::size_of_val(val);
    let mut dst = vec![None; size];
    val.write_captured_bytes(&mut dst);
    dst
}

/// Capture the byte representation of `val` as a `Vec<u8>` by reading only
/// initialized field bytes via [`TraceCapture`] and substituting `0u8` for any
/// unknown (`None`) padding offsets.
///
/// Because padding bytes are never read from `val` and are deterministically
/// represented as `0` where `capture_value_bytes` marks `None`, this function
/// is Miri-clean even when `val` has uninitialized inter-field or trailing
/// padding.
pub fn value_as_raw_bytes<T: TraceCapture + ?Sized>(val: &T) -> Vec<u8> {
    capture_value_bytes(val)
        .into_iter()
        .map(|b| b.unwrap_or(0))
        .collect()
}

/// Safe, validity-checked deserialization of scheduled return bytes (`EnvAction::ReturnBytes`)
/// and layout-aware generated inputs without `MaybeUninit::assume_init`.
pub trait FromScheduleBytes: Sized {
    /// Decode `bytes` into `Self` after verifying that `bytes.len() == size_of::<Self>()`
    /// and that every scalar, niche, and discriminant bit-validity invariant holds.
    fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, ScheduleError>;

    /// Return `true` if `bytes` encodes `Option::<Self>::None` when
    /// `size_of::<Option<Self>>() == size_of::<Self>()` (defaults to checking
    /// whether all bytes are zero and rejected by `Self::from_schedule_bytes`).
    fn is_niche_none_bytes(bytes: &[u8]) -> bool {
        !bytes.is_empty()
            && bytes.iter().all(|&b| b == 0)
            && Self::from_schedule_bytes(bytes).is_err()
    }
}

fn check_exact_len(context: &str, expected: usize, actual: usize) -> Result<(), ScheduleError> {
    if expected != actual {
        Err(ScheduleError::PayloadSizeMismatch {
            context: context.to_string(),
            expected,
            actual,
        })
    } else {
        Ok(())
    }
}

fn write_le_some(dst: &mut [Option<u8>], bytes: &[u8]) {
    for (slot, &b) in dst.iter_mut().zip(bytes.iter()) {
        *slot = Some(b);
    }
}

impl TraceCapture for () {
    fn write_captured_bytes(&self, _dst: &mut [Option<u8>]) {}
}

impl FromScheduleBytes for () {
    fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, ScheduleError> {
        check_exact_len("()", 0, bytes.len())?;
        Ok(())
    }
}

impl TraceCapture for bool {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        if let Some(slot) = dst.first_mut() {
            *slot = Some(u8::from(*self));
        }
    }

    fn write_niche_none_bytes(dst: &mut [Option<u8>]) {
        if let Some(slot) = dst.first_mut() {
            *slot = Some(2);
        }
    }
}

impl FromScheduleBytes for bool {
    fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, ScheduleError> {
        check_exact_len("bool", 1, bytes.len())?;
        match bytes[0] {
            0 => Ok(false),
            1 => Ok(true),
            other => Err(ScheduleError::InvalidBitPattern {
                context: "bool".to_string(),
                reason: format!("expected 0 or 1 for `bool`, got {other:#04x}"),
            }),
        }
    }

    fn is_niche_none_bytes(bytes: &[u8]) -> bool {
        bytes == [2]
    }
}

impl TraceCapture for char {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let code = *self as u32;
        write_le_some(dst, &code.to_le_bytes());
    }

    fn write_niche_none_bytes(dst: &mut [Option<u8>]) {
        write_le_some(dst, &0x0011_0000u32.to_le_bytes());
    }
}

impl FromScheduleBytes for char {
    fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, ScheduleError> {
        check_exact_len("char", 4, bytes.len())?;
        let raw = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
        char::from_u32(raw).ok_or_else(|| ScheduleError::InvalidBitPattern {
            context: "char".to_string(),
            reason: format!("invalid Unicode scalar value {raw:#010x}"),
        })
    }

    fn is_niche_none_bytes(bytes: &[u8]) -> bool {
        bytes == 0x0011_0000u32.to_le_bytes()
    }
}

macro_rules! impl_int_trace_capture {
    ($($ty:ty),* $(,)?) => {
        $(
            impl TraceCapture for $ty {
                fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
                    write_le_some(dst, &self.to_le_bytes());
                }
            }

            impl FromScheduleBytes for $ty {
                fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, ScheduleError> {
                    const N: usize = mem::size_of::<$ty>();
                    check_exact_len(stringify!($ty), N, bytes.len())?;
                    let mut arr = [0u8; N];
                    arr.copy_from_slice(bytes);
                    Ok(<$ty>::from_le_bytes(arr))
                }
            }
        )*
    };
}

impl_int_trace_capture!(
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, f32, f64
);

macro_rules! impl_nonzero_trace_capture {
    ($($nz:ty => $prim:ty),* $(,)?) => {
        $(
            impl TraceCapture for $nz {
                fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
                    self.get().write_captured_bytes(dst);
                }
            }

            impl FromScheduleBytes for $nz {
                fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, ScheduleError> {
                    let raw = <$prim as FromScheduleBytes>::from_schedule_bytes(bytes).map_err(
                        |e| match e {
                            ScheduleError::PayloadSizeMismatch { expected, actual, .. } => {
                                ScheduleError::PayloadSizeMismatch {
                                    context: stringify!($nz).to_string(),
                                    expected,
                                    actual,
                                }
                            }
                            other => other,
                        },
                    )?;
                    <$nz>::new(raw).ok_or_else(|| ScheduleError::InvalidBitPattern {
                        context: stringify!($nz).to_string(),
                        reason: "zero bit pattern is invalid for NonZero integer".to_string(),
                    })
                }
            }
        )*
    };
}

impl_nonzero_trace_capture!(
    NonZeroU8 => u8,
    NonZeroU16 => u16,
    NonZeroU32 => u32,
    NonZeroU64 => u64,
    NonZeroU128 => u128,
    NonZeroUsize => usize,
    NonZeroI8 => i8,
    NonZeroI16 => i16,
    NonZeroI32 => i32,
    NonZeroI64 => i64,
    NonZeroI128 => i128,
    NonZeroIsize => isize,
);

impl<T: TraceCapture, const N: usize> TraceCapture for [T; N] {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let elem_size = mem::size_of::<T>();
        for (idx, item) in self.iter().enumerate() {
            let start = idx * elem_size;
            item.write_captured_bytes(&mut dst[start..start + elem_size]);
        }
    }
}

impl<T: FromScheduleBytes, const N: usize> FromScheduleBytes for [T; N] {
    fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, ScheduleError> {
        let elem_size = mem::size_of::<T>();
        let expected = elem_size * N;
        check_exact_len("[T; N]", expected, bytes.len())?;
        let mut items = Vec::with_capacity(N);
        for idx in 0..N {
            let start = idx * elem_size;
            items.push(T::from_schedule_bytes(&bytes[start..start + elem_size])?);
        }
        items
            .try_into()
            .map_err(|_| ScheduleError::PayloadSizeMismatch {
                context: "[T; N]".to_string(),
                expected,
                actual: bytes.len(),
            })
    }
}

impl<T: TraceCapture> TraceCapture for [T] {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let elem_size = mem::size_of::<T>();
        for (idx, item) in self.iter().enumerate() {
            let start = idx * elem_size;
            item.write_captured_bytes(&mut dst[start..start + elem_size]);
        }
    }
}

impl TraceCapture for str {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        write_le_some(dst, self.as_bytes());
    }
}

impl<T> TraceCapture for &T {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let addr = (*self as *const T) as usize;
        write_le_some(dst, &addr.to_le_bytes());
    }
}

impl<T> TraceCapture for &mut T {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let addr = (*self as *const T) as usize;
        write_le_some(dst, &addr.to_le_bytes());
    }
}

impl<T> TraceCapture for *const T {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let addr = *self as usize;
        write_le_some(dst, &addr.to_le_bytes());
    }
}

impl<T> TraceCapture for *mut T {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let addr = *self as usize;
        write_le_some(dst, &addr.to_le_bytes());
    }
}

impl<T> TraceCapture for &[T] {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let ptr_size = mem::size_of::<usize>();
        let addr = self.as_ptr() as usize;
        let len = self.len();
        if dst.len() >= ptr_size * 2 {
            write_le_some(&mut dst[..ptr_size], &addr.to_le_bytes());
            write_le_some(&mut dst[ptr_size..ptr_size * 2], &len.to_le_bytes());
        }
    }
}

impl TraceCapture for &str {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        self.as_bytes().write_captured_bytes(dst);
    }
}

impl<A: TraceCapture, B: TraceCapture> TraceCapture for (A, B) {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let off0 = mem::offset_of!(Self, 0);
        let len0 = mem::size_of::<A>();
        self.0.write_captured_bytes(&mut dst[off0..off0 + len0]);
        let off1 = mem::offset_of!(Self, 1);
        let len1 = mem::size_of::<B>();
        self.1.write_captured_bytes(&mut dst[off1..off1 + len1]);
    }
}

impl<A: FromScheduleBytes, B: FromScheduleBytes> FromScheduleBytes for (A, B) {
    fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, ScheduleError> {
        check_exact_len("(A, B)", mem::size_of::<Self>(), bytes.len())?;
        let off0 = mem::offset_of!(Self, 0);
        let len0 = mem::size_of::<A>();
        let off1 = mem::offset_of!(Self, 1);
        let len1 = mem::size_of::<B>();
        Ok((
            A::from_schedule_bytes(&bytes[off0..off0 + len0])?,
            B::from_schedule_bytes(&bytes[off1..off1 + len1])?,
        ))
    }
}

impl<A: TraceCapture, B: TraceCapture, C: TraceCapture> TraceCapture for (A, B, C) {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let off0 = mem::offset_of!(Self, 0);
        let len0 = mem::size_of::<A>();
        self.0.write_captured_bytes(&mut dst[off0..off0 + len0]);
        let off1 = mem::offset_of!(Self, 1);
        let len1 = mem::size_of::<B>();
        self.1.write_captured_bytes(&mut dst[off1..off1 + len1]);
        let off2 = mem::offset_of!(Self, 2);
        let len2 = mem::size_of::<C>();
        self.2.write_captured_bytes(&mut dst[off2..off2 + len2]);
    }
}

impl<A: FromScheduleBytes, B: FromScheduleBytes, C: FromScheduleBytes> FromScheduleBytes
    for (A, B, C)
{
    fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, ScheduleError> {
        check_exact_len("(A, B, C)", mem::size_of::<Self>(), bytes.len())?;
        let off0 = mem::offset_of!(Self, 0);
        let len0 = mem::size_of::<A>();
        let off1 = mem::offset_of!(Self, 1);
        let len1 = mem::size_of::<B>();
        let off2 = mem::offset_of!(Self, 2);
        let len2 = mem::size_of::<C>();
        Ok((
            A::from_schedule_bytes(&bytes[off0..off0 + len0])?,
            B::from_schedule_bytes(&bytes[off1..off1 + len1])?,
            C::from_schedule_bytes(&bytes[off2..off2 + len2])?,
        ))
    }
}

impl<A: TraceCapture, B: TraceCapture, C: TraceCapture, D: TraceCapture> TraceCapture
    for (A, B, C, D)
{
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let off0 = mem::offset_of!(Self, 0);
        let len0 = mem::size_of::<A>();
        self.0.write_captured_bytes(&mut dst[off0..off0 + len0]);
        let off1 = mem::offset_of!(Self, 1);
        let len1 = mem::size_of::<B>();
        self.1.write_captured_bytes(&mut dst[off1..off1 + len1]);
        let off2 = mem::offset_of!(Self, 2);
        let len2 = mem::size_of::<C>();
        self.2.write_captured_bytes(&mut dst[off2..off2 + len2]);
        let off3 = mem::offset_of!(Self, 3);
        let len3 = mem::size_of::<D>();
        self.3.write_captured_bytes(&mut dst[off3..off3 + len3]);
    }
}

impl<A: FromScheduleBytes, B: FromScheduleBytes, C: FromScheduleBytes, D: FromScheduleBytes>
    FromScheduleBytes for (A, B, C, D)
{
    fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, ScheduleError> {
        check_exact_len("(A, B, C, D)", mem::size_of::<Self>(), bytes.len())?;
        let off0 = mem::offset_of!(Self, 0);
        let len0 = mem::size_of::<A>();
        let off1 = mem::offset_of!(Self, 1);
        let len1 = mem::size_of::<B>();
        let off2 = mem::offset_of!(Self, 2);
        let len2 = mem::size_of::<C>();
        let off3 = mem::offset_of!(Self, 3);
        let len3 = mem::size_of::<D>();
        Ok((
            A::from_schedule_bytes(&bytes[off0..off0 + len0])?,
            B::from_schedule_bytes(&bytes[off1..off1 + len1])?,
            C::from_schedule_bytes(&bytes[off2..off2 + len2])?,
            D::from_schedule_bytes(&bytes[off3..off3 + len3])?,
        ))
    }
}

impl<T: TraceCapture> TraceCapture for Option<T> {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let total = dst.len();
        let val_size = mem::size_of::<T>();
        match self {
            None => {
                if total == val_size {
                    T::write_niche_none_bytes(dst);
                } else if let Some(tag) = dst.first_mut() {
                    *tag = Some(0);
                }
            }
            Some(v) => {
                if total == val_size {
                    // Niche-optimized `Option<T>` (e.g., `Option<NonZeroU32>`, `Option<bool>`).
                    v.write_captured_bytes(dst);
                } else {
                    if let Some(tag) = dst.first_mut() {
                        *tag = Some(1);
                    }
                    let payload_off = total.saturating_sub(val_size);
                    v.write_captured_bytes(&mut dst[payload_off..payload_off + val_size]);
                }
            }
        }
    }
}

impl<T: FromScheduleBytes> FromScheduleBytes for Option<T> {
    fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, ScheduleError> {
        let total = mem::size_of::<Self>();
        check_exact_len("Option<T>", total, bytes.len())?;
        let val_size = mem::size_of::<T>();
        if total == val_size {
            if T::is_niche_none_bytes(bytes) {
                return Ok(None);
            }
            return T::from_schedule_bytes(bytes).map(Some);
        }
        match bytes[0] {
            0 => Ok(None),
            1 => {
                let payload_off = total.saturating_sub(val_size);
                T::from_schedule_bytes(&bytes[payload_off..payload_off + val_size]).map(Some)
            }
            other => Err(ScheduleError::InvalidBitPattern {
                context: "Option<T>".to_string(),
                reason: format!("expected Option discriminant 0 or 1, got {other:#04x}"),
            }),
        }
    }
}

impl<T: TraceCapture, E: TraceCapture> TraceCapture for Result<T, E> {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let total = dst.len();
        match self {
            Ok(v) => {
                if let Some(tag) = dst.first_mut() {
                    *tag = Some(0);
                }
                let val_size = mem::size_of::<T>();
                if val_size > 0 && total > val_size {
                    let off = total - val_size;
                    v.write_captured_bytes(&mut dst[off..off + val_size]);
                }
            }
            Err(e) => {
                if let Some(tag) = dst.first_mut() {
                    *tag = Some(1);
                }
                let err_size = mem::size_of::<E>();
                if err_size > 0 && total > err_size {
                    let off = total - err_size;
                    e.write_captured_bytes(&mut dst[off..off + err_size]);
                }
            }
        }
    }
}

impl<T: FromScheduleBytes, E: FromScheduleBytes> FromScheduleBytes for Result<T, E> {
    fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, ScheduleError> {
        let total = mem::size_of::<Self>();
        check_exact_len("Result<T, E>", total, bytes.len())?;
        if total == 0 {
            return T::from_schedule_bytes(&[]).map(Ok);
        }
        match bytes[0] {
            0 => {
                let val_size = mem::size_of::<T>();
                let off = if val_size == 0 {
                    0
                } else {
                    total.saturating_sub(val_size)
                };
                T::from_schedule_bytes(&bytes[off..off + val_size]).map(Ok)
            }
            1 => {
                let err_size = mem::size_of::<E>();
                let off = if err_size == 0 {
                    0
                } else {
                    total.saturating_sub(err_size)
                };
                E::from_schedule_bytes(&bytes[off..off + err_size]).map(Err)
            }
            other => Err(ScheduleError::InvalidBitPattern {
                context: "Result<T, E>".to_string(),
                reason: format!("expected Result discriminant 0 or 1, got {other:#04x}"),
            }),
        }
    }
}

/// Entry in the runtime observer's shadow provenance table mapping a native
/// virtual address range `[base_addr, base_addr + byte_len)` to an abstract
/// MIR `(alloc_id, tag)` and optional initial referent bytes `raw_bytes`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordedShadowAlloc {
    /// Native runtime base virtual address (`ptr as usize`).
    pub base_addr: usize,
    /// Allocation size in bytes.
    pub byte_len: usize,
    /// Abstract MIR `AllocId`.
    pub alloc_id: usize,
    /// Tree Borrows provenance tag associated with this allocation.
    pub tag: usize,
    /// Initial raw referent bytes captured when the allocation was registered.
    pub raw_bytes: Vec<u8>,
}

/// Alias preserving compatibility with JSON trace interchange descriptors.
pub type ShadowAllocEntryJson = RecordedShadowAlloc;

/// Single observable event captured by [`TraceRecorder`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecordedEvent {
    /// A `TerminatorKind.switchInt` branch observation (`MirObs.event tag`).
    Branch {
        /// Discriminant value taken at the `switchInt` terminator.
        tag: u128,
    },
    /// An external/callee call to `def_path` that returned normally.
    ExtCall {
        /// Rust `DefPath` of the callee (e.g., `"trace_demo::ext_scale_add"`).
        def_path: String,
        /// Raw little-endian byte slices for each argument in declaration order.
        raw_args: Vec<Vec<u8>>,
        /// Raw little-endian byte slice for the returned value.
        raw_ret: Vec<u8>,
    },
    /// An external/callee call to `def_path` that unwound (panicked).
    ExtCallPanic {
        /// Rust `DefPath` of the callee.
        def_path: String,
        /// Raw little-endian byte slices for each argument in declaration order.
        raw_args: Vec<Vec<u8>>,
    },
    /// An external/callee call to `def_path` that aborted.
    ExtCallAbort {
        /// Rust `DefPath` of the callee.
        def_path: String,
        /// Raw little-endian byte slices for each argument in declaration order.
        raw_args: Vec<Vec<u8>>,
    },
}

/// Structured call-boundary event representation for interchange across
/// differential-testing and trace serialization pipelines.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawCallEventJson {
    /// Rust `DefPath` of the callee.
    pub def_path: String,
    /// Raw little-endian byte slices for each argument in declaration order.
    pub raw_args: Vec<Vec<u8>>,
    /// Raw little-endian return bytes when the call returned normally.
    pub raw_ret: Option<Vec<u8>>,
    /// Whether the callee unwound via panic.
    pub panicked: bool,
    /// Whether the callee terminated the process via abort.
    pub aborted: bool,
}

impl RawCallEventJson {
    /// Convert this structured call record into a [`RecordedEvent`].
    pub fn into_recorded_event(self) -> RecordedEvent {
        if self.aborted {
            RecordedEvent::ExtCallAbort {
                def_path: self.def_path,
                raw_args: self.raw_args,
            }
        } else if self.panicked {
            RecordedEvent::ExtCallPanic {
                def_path: self.def_path,
                raw_args: self.raw_args,
            }
        } else {
            RecordedEvent::ExtCall {
                def_path: self.def_path,
                raw_args: self.raw_args,
                raw_ret: self.raw_ret.unwrap_or_default(),
            }
        }
    }
}

/// Alias preserving compatibility with JSON trace event descriptors.
pub type RawTraceEventJson = RecordedEvent;

/// Terminal outcome of a root function invocation captured by [`TraceRecorder`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecordedOutcome {
    /// Normal return with the raw byte slice of the return value (`_0`).
    Normal {
        /// Raw little-endian byte slice of the return value.
        raw_ret: Vec<u8>,
    },
    /// Unwinding panic.
    Panic,
    /// Process abort.
    Abort,
}

/// Alias preserving compatibility with JSON outcome descriptors.
pub type RawOutcomeJson = RecordedOutcome;

/// Complete raw byte-level execution trace captured by [`TraceRecorder`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordedRawTrace {
    /// Rust `DefPath` of the root function.
    pub root_def_path: String,
    /// Raw little-endian byte slices of the root function's arguments.
    pub raw_args: Vec<Vec<u8>>,
    /// Shadow provenance table mapping native virtual addresses to abstract
    /// MIR `(alloc_id, tag)` provenance.
    pub shadow_provenance: Vec<RecordedShadowAlloc>,
    /// Sequence of observed branch and external-call events.
    pub events: Vec<RecordedEvent>,
    /// Terminal outcome of the root invocation.
    pub outcome: RecordedOutcome,
}

/// Alias preserving compatibility with JSON raw byte trace descriptors.
pub type RawByteTraceJson = RecordedRawTrace;

/// Deterministic action prescribed by an [`EnvSchedule`] for an external call site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EnvAction {
    /// Invoke the underlying implementation normally and record its return bytes.
    PassThrough,
    /// Return a deterministic pre-scheduled byte payload.
    ReturnBytes(Vec<u8>),
    /// Deterministically trigger a mid-call panic at call index `k`.
    PanicOnCall(usize),
}

/// Deterministic environment response schedule (`inputs-over-time`) across external
/// callees, supporting per-callee response queues and optional `PanicOnCall(usize)`
/// unwind fault injection.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EnvSchedule {
    /// Per-callee FIFO queues of raw return-value byte buffers.
    pub callee_queues: BTreeMap<String, VecDeque<Vec<u8>>>,
    /// Per-callee fallback constant bytes when the FIFO queue is exhausted.
    pub callee_defaults: BTreeMap<String, Vec<u8>>,
    /// Optional per-callee expected return byte sizes used to reject mismatched
    /// schedule payloads at construction / registration time.
    pub callee_return_sizes: BTreeMap<String, usize>,
    /// Optional global call index (`0`-based) at which any external call panics.
    pub global_panic_on_call: Option<usize>,
    /// Optional per-callee call index (`0`-based) at which that callee panics.
    pub callee_panic_on_call: BTreeMap<String, usize>,
    /// Per-callee count of invocations served so far.
    callee_call_counts: BTreeMap<String, usize>,
}

impl EnvSchedule {
    /// Creates an empty pass-through schedule with no injected panics.
    pub fn new() -> Self {
        Self::default()
    }

    /// Registers the expected return byte size for `callee` and returns `self`.
    pub fn with_callee_return_size(mut self, callee: &str, expected_size: usize) -> Self {
        self.register_callee_return_size(callee, expected_size);
        self
    }

    /// Registers the expected return byte size for `callee`.
    pub fn register_callee_return_size(&mut self, callee: &str, expected_size: usize) {
        self.callee_return_sizes
            .insert(callee.to_string(), expected_size);
    }

    /// Looks up the expected return byte size for `callee` (checking both the
    /// full path and the short function name).
    pub fn expected_return_size(&self, callee: &str) -> Option<usize> {
        if let Some(&sz) = self.callee_return_sizes.get(callee) {
            return Some(sz);
        }
        if let Some((_, short)) = callee.rsplit_once("::")
            && let Some(&sz) = self.callee_return_sizes.get(short)
        {
            return Some(sz);
        }
        None
    }

    /// Validates that `bytes.len()` matches the registered return size for
    /// `callee` (if one has been registered).
    pub fn validate_callee_payload(
        &self,
        callee: &str,
        bytes: &[u8],
    ) -> Result<(), ScheduleError> {
        if let Some(expected_size) = self.expected_return_size(callee)
            && bytes.len() != expected_size
        {
            return Err(ScheduleError::PayloadSizeMismatch {
                context: callee.to_string(),
                expected: expected_size,
                actual: bytes.len(),
            });
        }
        Ok(())
    }

    /// Configures a deterministic global `PanicOnCall(k)` trigger.
    pub fn with_panic_on_call(mut self, call_index: usize) -> Self {
        self.global_panic_on_call = Some(call_index);
        self
    }

    /// Sets or updates the global `PanicOnCall(k)` trigger.
    pub fn set_panic_on_call(&mut self, call_index: usize) {
        self.global_panic_on_call = Some(call_index);
    }

    /// Configures a per-callee `PanicOnCall(k)` trigger for `callee`.
    pub fn set_callee_panic_on_call(&mut self, callee: &str, call_index: usize) {
        self.callee_panic_on_call
            .insert(callee.to_string(), call_index);
    }

    /// Appends a single scheduled raw-byte return payload to `callee`'s queue,
    /// returning an error if `callee` has a registered return size that does
    /// not match `bytes.len()`.
    pub fn push_callee_response_checked(
        &mut self,
        callee: &str,
        bytes: Vec<u8>,
    ) -> Result<(), ScheduleError> {
        self.validate_callee_payload(callee, &bytes)?;
        self.callee_queues
            .entry(callee.to_string())
            .or_default()
            .push_back(bytes);
        Ok(())
    }

    /// Appends a single scheduled raw-byte return payload to `callee`'s queue.
    ///
    /// # Panics
    ///
    /// Panics if `callee` has a registered return size that does not match
    /// `bytes.len()`.
    pub fn push_callee_response(&mut self, callee: &str, bytes: Vec<u8>) {
        self.push_callee_response_checked(callee, bytes)
            .unwrap_or_else(|err| panic!("invalid schedule response for `{callee}`: {err}"));
    }

    /// Sets the default fallback byte payload for `callee` once its queue
    /// empties, returning an error if `callee` has a registered return size
    /// that does not match `bytes.len()`.
    pub fn set_callee_default_checked(
        &mut self,
        callee: &str,
        bytes: Vec<u8>,
    ) -> Result<(), ScheduleError> {
        self.validate_callee_payload(callee, &bytes)?;
        self.callee_defaults.insert(callee.to_string(), bytes);
        Ok(())
    }

    /// Sets the default fallback byte payload for `callee` once its queue empties.
    ///
    /// # Panics
    ///
    /// Panics if `callee` has a registered return size that does not match
    /// `bytes.len()`.
    pub fn set_callee_default(&mut self, callee: &str, bytes: Vec<u8>) {
        self.set_callee_default_checked(callee, bytes)
            .unwrap_or_else(|err| panic!("invalid schedule default for `{callee}`: {err}"));
    }

    fn resolve_key(&self, callee: &str) -> String {
        if self.callee_queues.contains_key(callee)
            || self.callee_defaults.contains_key(callee)
            || self.callee_panic_on_call.contains_key(callee)
        {
            return callee.to_string();
        }
        if let Some((_, short)) = callee.rsplit_once("::")
            && (self.callee_queues.contains_key(short)
                || self.callee_defaults.contains_key(short)
                || self.callee_panic_on_call.contains_key(short))
        {
            return short.to_string();
        }
        callee.to_string()
    }

    /// Returns `true` if `global_call_index` or `callee_call_index` matches a configured
    /// `PanicOnCall` trigger.
    pub fn should_panic(
        &self,
        callee: &str,
        global_call_index: usize,
        callee_call_index: usize,
    ) -> bool {
        if self.global_panic_on_call == Some(global_call_index) {
            return true;
        }
        let key = self.resolve_key(callee);
        if self.callee_panic_on_call.get(&key).copied() == Some(callee_call_index) {
            return true;
        }
        false
    }

    /// Advances the schedule state for `callee` at `global_call_index` and returns the
    /// prescribed [`EnvAction`].
    pub fn next_action(&mut self, callee: &str, global_call_index: usize) -> EnvAction {
        let key = self.resolve_key(callee);
        let count_entry = self.callee_call_counts.entry(key.clone()).or_insert(0);
        let callee_call_idx = *count_entry;
        *count_entry += 1;

        if self.should_panic(&key, global_call_index, callee_call_idx) {
            return EnvAction::PanicOnCall(global_call_index);
        }

        if let Some(queue) = self.callee_queues.get_mut(&key)
            && let Some(front) = queue.pop_front()
        {
            return EnvAction::ReturnBytes(front);
        }

        if let Some(default_bytes) = self.callee_defaults.get(&key) {
            return EnvAction::ReturnBytes(default_bytes.clone());
        }

        EnvAction::PassThrough
    }
}

struct ActiveBoundaryState {
    root_crate_prefix: Option<String>,
    schedule: EnvSchedule,
    inlined_callees: BTreeSet<String>,
    events: Vec<RecordedEvent>,
    branch_tags: Vec<u32>,
    call_count: usize,
    boundary_depth: usize,
}

impl ActiveBoundaryState {
    fn is_inlined(&self, def_path: &str, short_name: &str) -> bool {
        self.inlined_callees.contains(def_path) || self.inlined_callees.contains(short_name)
    }

    fn canonical_def_path(&self, callee_module_path: &str, callee_fn_name: &str) -> String {
        if let Some(ref root_crate) = self.root_crate_prefix {
            if callee_module_path == root_crate
                || callee_module_path.starts_with(&format!("{root_crate}::"))
            {
                return format!("{callee_module_path}::{callee_fn_name}");
            }
            return format!("{root_crate}::{callee_fn_name}");
        }
        if callee_module_path.is_empty() {
            callee_fn_name.to_string()
        } else {
            format!("{callee_module_path}::{callee_fn_name}")
        }
    }
}

thread_local! {
    static ACTIVE_RECORDER: RefCell<Option<ActiveBoundaryState>> = const { RefCell::new(None) };
}

struct BoundaryDepthGuard;

impl Drop for BoundaryDepthGuard {
    fn drop(&mut self) {
        ACTIVE_RECORDER.with(|cell| {
            if let Some(state) = cell.borrow_mut().as_mut() {
                state.boundary_depth = state.boundary_depth.saturating_sub(1);
            }
        });
    }
}

/// Runtime boundary hook invoked by functions annotated with
/// `#[anneal_trace::external]` when compiled under `#[cfg(any(test, anneal_trace_ext))]`.
///
/// When called inside an active [`TraceRecorder::observe_root`] scope (at
/// top-level boundary depth `0` and when the callee is not listed in
/// `inlined_callees`), this function records the actual runtime argument byte
/// slices `raw_args`, consults the active [`EnvSchedule`], executes `f()`, and
/// records either [`RecordedEvent::ExtCall`] or [`RecordedEvent::ExtCallPanic`].
/// When called outside `observe_root`, inside a nested external call, or when
/// the callee is marked inlined, it invokes `f()` directly with no trace event.
pub fn observe_boundary_call<R: TraceCapture + FromScheduleBytes>(
    callee_module_path: &str,
    callee_fn_name: &str,
    raw_args: Vec<Vec<u8>>,
    f: impl FnOnce() -> R,
) -> R {
    let intercept = ACTIVE_RECORDER.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let state = borrow.as_mut()?;
        let def_path = state.canonical_def_path(callee_module_path, callee_fn_name);
        if state.boundary_depth > 0 || state.is_inlined(&def_path, callee_fn_name) {
            return None;
        }
        state.boundary_depth += 1;
        let call_idx = state.call_count;
        state.call_count += 1;
        let action = state.schedule.next_action(&def_path, call_idx);
        Some((def_path, action))
    });

    let Some((def_path, action)) = intercept else {
        return f();
    };

    let _depth_guard = BoundaryDepthGuard;

    match action {
        EnvAction::PanicOnCall(k) => {
            ACTIVE_RECORDER.with(|cell| {
                if let Some(state) = cell.borrow_mut().as_mut() {
                    state.events.push(RecordedEvent::ExtCallPanic {
                        def_path,
                        raw_args,
                    });
                }
            });
            panic!("anneal scheduled PanicOnCall({k}) triggered in `{callee_fn_name}`");
        }
        EnvAction::ReturnBytes(sched_bytes) => {
            if sched_bytes.len() != mem::size_of::<R>() {
                panic!(
                    "anneal scheduled ReturnBytes for `{def_path}` has mismatched payload size: \
                     expected {} bytes for `{}`, got {} bytes",
                    mem::size_of::<R>(),
                    std::any::type_name::<R>(),
                    sched_bytes.len()
                );
            }
            let ret = R::from_schedule_bytes(&sched_bytes).unwrap_or_else(|err| {
                panic!("anneal scheduled ReturnBytes for `{def_path}` failed validation: {err}")
            });
            let raw_ret = value_as_raw_bytes(&ret);
            ACTIVE_RECORDER.with(|cell| {
                if let Some(state) = cell.borrow_mut().as_mut() {
                    state.events.push(RecordedEvent::ExtCall {
                        def_path,
                        raw_args,
                        raw_ret,
                    });
                }
            });
            ret
        }
        EnvAction::PassThrough => match panic::catch_unwind(AssertUnwindSafe(f)) {
            Ok(ret) => {
                let raw_ret = value_as_raw_bytes(&ret);
                ACTIVE_RECORDER.with(|cell| {
                    if let Some(state) = cell.borrow_mut().as_mut() {
                        state.events.push(RecordedEvent::ExtCall {
                            def_path,
                            raw_args,
                            raw_ret,
                        });
                    }
                });
                ret
            }
            Err(payload) => {
                ACTIVE_RECORDER.with(|cell| {
                    if let Some(state) = cell.borrow_mut().as_mut() {
                        state.events.push(RecordedEvent::ExtCallPanic {
                            def_path,
                            raw_args,
                        });
                    }
                });
                panic::resume_unwind(payload)
            }
        },
    }
}

/// Stateful recorder that interposes at function boundaries (and optional
/// branch points) to capture a [`RecordedRawTrace`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TraceRecorder {
    /// Active environment schedule governing external callees.
    pub schedule: EnvSchedule,
    /// Callees (`DefPath` or function identifier) stepped as `.tau` inlined calls
    /// rather than emitting `MirCallE` boundary events.
    pub inlined_callees: BTreeSet<String>,
    /// Watched runtime allocations mapped to abstract MIR `(alloc_id, tag)` provenance.
    pub shadow_provenance: Vec<RecordedShadowAlloc>,
    /// Ordered log of recorded branch and external-call events.
    pub events: Vec<RecordedEvent>,
    /// Compact sequence of visited basic-block / branch tags.
    pub branch_tags: Vec<u32>,
    /// Terminal execution outcome when recorded on the stateful recorder.
    pub outcome: Option<RecordedOutcome>,
    /// Total number of external calls initiated during this execution.
    pub call_count: usize,
}

impl TraceRecorder {
    /// Construct an empty [`TraceRecorder`].
    pub fn new() -> Self {
        Self::default()
    }

    /// Construct a [`TraceRecorder`] configured with `schedule`.
    pub fn with_schedule(schedule: EnvSchedule) -> Self {
        Self {
            schedule,
            ..Self::default()
        }
    }

    /// Construct a [`TraceRecorder`] with the given set of inlined callee names
    /// or `DefPath`s.
    pub fn with_inlined_callees<I, S>(inlined: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Self {
            inlined_callees: inlined.into_iter().map(Into::into).collect(),
            ..Self::default()
        }
    }

    /// Mark `callee` (`DefPath` or function name) as inlined (stepped via `.tau`
    /// rather than recorded as a `MirCallE` external call event).
    pub fn add_inlined_callee(&mut self, callee: impl Into<String>) {
        self.inlined_callees.insert(callee.into());
    }

    /// Return the currently registered shadow provenance table entries.
    pub fn shadow_provenance(&self) -> &[RecordedShadowAlloc] {
        &self.shadow_provenance
    }

    /// Return the currently recorded interaction events.
    pub fn events(&self) -> &[RecordedEvent] {
        &self.events
    }

    /// Register a watched runtime allocation in the shadow provenance table,
    /// capturing its initial referent bytes via [`value_as_raw_bytes`] so
    /// Lean `TraceCheck` can populate initial memory for pointer dereferences.
    pub fn register_allocation<T: TraceCapture + ?Sized>(
        &mut self,
        referent: &T,
        alloc_id: usize,
        tag: usize,
    ) {
        let base_addr = (referent as *const T).cast::<u8>() as usize;
        let byte_len = mem::size_of_val(referent);
        let raw_bytes = value_as_raw_bytes(referent);
        self.register_address_range_with_bytes(base_addr, byte_len, alloc_id, tag, raw_bytes);
    }

    /// Register an explicit native virtual address range `[base_addr, base_addr + byte_len)`
    /// in the shadow provenance table without initial memory bytes.
    pub fn register_address_range(
        &mut self,
        base_addr: usize,
        byte_len: usize,
        alloc_id: usize,
        tag: usize,
    ) {
        self.register_address_range_with_bytes(base_addr, byte_len, alloc_id, tag, Vec::new());
    }

    /// Register an explicit native virtual address range `[base_addr, base_addr + byte_len)`
    /// with initial referent bytes `raw_bytes` in the shadow provenance table.
    pub fn register_address_range_with_bytes(
        &mut self,
        base_addr: usize,
        byte_len: usize,
        alloc_id: usize,
        tag: usize,
        raw_bytes: Vec<u8>,
    ) {
        self.shadow_provenance.push(RecordedShadowAlloc {
            base_addr,
            byte_len,
            alloc_id,
            tag,
            raw_bytes,
        });
    }

    /// Record a `TerminatorKind.switchInt` branch observation (`MirObs.event tag`).
    pub fn record_branch(&mut self, tag: u128) {
        let pushed_active = ACTIVE_RECORDER.with(|cell| {
            if let Some(state) = cell.borrow_mut().as_mut() {
                state.branch_tags.push(tag as u32);
                state.events.push(RecordedEvent::Branch { tag });
                true
            } else {
                false
            }
        });
        if !pushed_active {
            self.branch_tags.push(tag as u32);
            self.events.push(RecordedEvent::Branch { tag });
        }
    }

    /// Consults the embedded [`EnvSchedule`] before invoking `callee`. If `PanicOnCall(k)`
    /// fires, records [`RecordedEvent::ExtCallPanic`] and sets `outcome` to [`RecordedOutcome::Panic`].
    pub fn step_ext_call(&mut self, callee: &str) -> (usize, EnvAction) {
        let idx = self.call_count;
        self.call_count += 1;
        let action = self.schedule.next_action(callee, idx);
        if matches!(action, EnvAction::PanicOnCall(_)) {
            self.events.push(RecordedEvent::ExtCallPanic {
                def_path: callee.to_string(),
                raw_args: Vec::new(),
            });
            self.outcome = Some(RecordedOutcome::Panic);
        }
        (idx, action)
    }

    /// Record a completed external call event directly from raw argument and
    /// return byte slices.
    pub fn record_ext_call(
        &mut self,
        def_path: impl Into<String>,
        raw_args: Vec<Vec<u8>>,
        raw_ret: Vec<u8>,
    ) {
        let ev = RecordedEvent::ExtCall {
            def_path: def_path.into(),
            raw_args,
            raw_ret,
        };
        let pushed_active = ACTIVE_RECORDER.with(|cell| {
            if let Some(state) = cell.borrow_mut().as_mut() {
                state.events.push(ev.clone());
                true
            } else {
                false
            }
        });
        if !pushed_active {
            self.events.push(ev);
        }
    }

    /// Record an unwinding external call event directly from raw argument bytes.
    pub fn record_ext_call_panic(
        &mut self,
        def_path: impl Into<String>,
        raw_args: Vec<Vec<u8>>,
    ) {
        let ev = RecordedEvent::ExtCallPanic {
            def_path: def_path.into(),
            raw_args,
        };
        let pushed_active = ACTIVE_RECORDER.with(|cell| {
            if let Some(state) = cell.borrow_mut().as_mut() {
                state.events.push(ev.clone());
                true
            } else {
                false
            }
        });
        if !pushed_active {
            self.events.push(ev);
        }
    }

    /// Record an aborting external call event directly from raw argument bytes.
    pub fn record_ext_call_abort(
        &mut self,
        def_path: impl Into<String>,
        raw_args: Vec<Vec<u8>>,
    ) {
        let ev = RecordedEvent::ExtCallAbort {
            def_path: def_path.into(),
            raw_args,
        };
        let pushed_active = ACTIVE_RECORDER.with(|cell| {
            if let Some(state) = cell.borrow_mut().as_mut() {
                state.events.push(ev.clone());
                true
            } else {
                false
            }
        });
        if !pushed_active {
            self.events.push(ev);
        }
    }

    /// Record a normal function return by capturing `value_as_raw_bytes(val)`.
    pub fn finish_return<T: TraceCapture + ?Sized>(&mut self, val: &T) {
        self.outcome = Some(RecordedOutcome::Normal {
            raw_ret: value_as_raw_bytes(val),
        });
    }

    /// Record an unwinding panic outcome.
    pub fn finish_panic(&mut self) {
        self.outcome = Some(RecordedOutcome::Panic);
    }

    /// Return `true` iff the recorded execution terminated via panic.
    pub fn is_panic(&self) -> bool {
        matches!(self.outcome, Some(RecordedOutcome::Panic))
    }

    /// Extract the canonical external-call sequence shape `(def_path, call_index)`
    /// across completed and panicking external calls.
    pub fn ext_call_sequence_shape(&self) -> Vec<(String, usize)> {
        let mut shape = Vec::new();
        let mut call_idx = 0usize;
        for ev in &self.events {
            match ev {
                RecordedEvent::ExtCall { def_path, .. }
                | RecordedEvent::ExtCallPanic { def_path, .. }
                | RecordedEvent::ExtCallAbort { def_path, .. } => {
                    shape.push((def_path.clone(), call_idx));
                    call_idx += 1;
                }
                RecordedEvent::Branch { .. } => {}
            }
        }
        shape
    }

    /// Execute and observe a root function invocation `f`, capturing its
    /// `raw_args`, all interaction events recorded at `#[anneal_trace::external]`
    /// boundaries, and its terminal `RecordedOutcome` (`Normal` or `Panic`).
    pub fn observe_root<R: TraceCapture>(
        root_def_path: impl Into<String>,
        raw_args: Vec<Vec<u8>>,
        f: impl FnOnce(&mut TraceRecorder) -> R,
    ) -> (Result<R, Box<dyn Any + Send>>, RecordedRawTrace) {
        let (res, trace, _rec) =
            Self::observe_root_with_recorder(TraceRecorder::new(), root_def_path, raw_args, f);
        (res, trace)
    }

    /// Execute and observe a root function invocation `f` with the specified
    /// `inlined_callees` stepped transparently without emitting `MirCallE`
    /// boundary events.
    pub fn observe_root_with_inlined_callees<R: TraceCapture, I, S>(
        root_def_path: impl Into<String>,
        raw_args: Vec<Vec<u8>>,
        inlined_callees: I,
        f: impl FnOnce(&mut TraceRecorder) -> R,
    ) -> (Result<R, Box<dyn Any + Send>>, RecordedRawTrace)
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let rec = TraceRecorder::with_inlined_callees(inlined_callees);
        let (res, trace, _rec) = Self::observe_root_with_recorder(rec, root_def_path, raw_args, f);
        (res, trace)
    }

    /// Execute and observe a root function invocation `f` using a pre-configured
    /// [`TraceRecorder`] (e.g., carrying an [`EnvSchedule`] or `inlined_callees`),
    /// returning the invocation result, the [`RecordedRawTrace`], and the updated
    /// [`TraceRecorder`].
    pub fn observe_root_with_recorder<R: TraceCapture>(
        mut recorder: TraceRecorder,
        root_def_path: impl Into<String>,
        raw_args: Vec<Vec<u8>>,
        f: impl FnOnce(&mut TraceRecorder) -> R,
    ) -> (Result<R, Box<dyn Any + Send>>, RecordedRawTrace, TraceRecorder) {
        let root_def_path_str = root_def_path.into();
        let root_crate_prefix = root_def_path_str
            .split_once("::")
            .map(|(prefix, _)| prefix.to_string());

        let active_init = ActiveBoundaryState {
            root_crate_prefix,
            schedule: recorder.schedule.clone(),
            inlined_callees: recorder.inlined_callees.clone(),
            events: Vec::new(),
            branch_tags: Vec::new(),
            call_count: recorder.call_count,
            boundary_depth: 0,
        };

        let prev_active = ACTIVE_RECORDER.with(|cell| cell.borrow_mut().replace(active_init));
        let res = panic::catch_unwind(AssertUnwindSafe(|| f(&mut recorder)));
        let finished_active = ACTIVE_RECORDER.with(|cell| {
            let mut borrow = cell.borrow_mut();
            let current = borrow.take();
            *borrow = prev_active;
            current
        });

        if let Some(active) = finished_active {
            recorder.schedule = active.schedule;
            recorder.events.extend(active.events);
            recorder.branch_tags.extend(active.branch_tags);
            recorder.call_count = active.call_count;
        }

        let outcome = match &res {
            Ok(ret) => RecordedOutcome::Normal {
                raw_ret: value_as_raw_bytes(ret),
            },
            Err(_) => RecordedOutcome::Panic,
        };
        recorder.outcome = Some(outcome.clone());

        let trace = RecordedRawTrace {
            root_def_path: root_def_path_str,
            raw_args,
            shadow_provenance: recorder.shadow_provenance.clone(),
            events: recorder.events.clone(),
            outcome,
        };
        (res, trace, recorder)
    }
}

/// Configuration for rendering a Lean 4 trace-verification module over one or
/// more [`RecordedRawTrace`]s.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceCheckModuleConfig {
    /// Lean module namespace (e.g., `"TraceVerify.Canary"`).
    pub module_namespace: String,
    /// Lean module path for the root function's captured MIR (e.g.,
    /// `"Mir.TracePkg.compute_packet"`), whose `.body` is checked.
    pub root_mir_module: String,
    /// Lean module paths for external callees whose signatures (`localDecls`
    /// and `layouts`) are used by `decodeRawByteTrace` to decode `MirCallE`
    /// argument and return byte slices.
    pub callee_sig_modules: Vec<String>,
    /// Lean module paths for transparent inlined callees placed in
    /// `RawByteTrace.inlinedCallees` (`Memory.callees`), stepped via `.tau`.
    pub inlined_callee_modules: Vec<String>,
    /// Optional Lean expression for `RawByteTrace.initMem` (defaults to
    /// `"emptyMemory"`).
    pub init_mem_expr: Option<String>,
    /// Step fuel bound passed to `checkRawByteTraceObsErasedBounded` /
    /// `checkRawByteTraceFullBounded` and `diagnoseRawByteTrace*Bounded`.
    pub fuel: usize,
    /// Whether to emit a full-trace theorem (`checkBranches = true`,
    /// `mirStatefulTree`) in addition to or instead of the branch-erased
    /// theorem (`checkBranches = false`, `mirObsErasedStatefulTree`).
    pub check_branches: bool,
}

/// Alias preserving compatibility with observer specification descriptors.
pub type TraceObserverSpec = TraceCheckModuleConfig;

/// Single case entry for batch diagnostic and kernel verification module
/// generation ([`render_batch_trace_eval_lean_module`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BatchTraceEvalCase {
    /// Lean identifier prefix for generated definitions and theorems (e.g.,
    /// `"case_01_packet"`).
    pub case_ident: String,
    /// Per-case module and fuel configuration.
    pub config: TraceCheckModuleConfig,
    /// Observed raw byte trace for this test case.
    pub trace: RecordedRawTrace,
    /// Optional expected `TraceReplayDiag.tagName` string (defaults to `"ok"`).
    /// When `Some("ok")` or `None`, a kernel `by rfl` soundness theorem is also
    /// emitted; when set to a non-`"ok"` tag such as `"outcome_mismatch"`, a
    /// negative diagnostic equality theorem is emitted.
    pub expected_diag_tag: Option<String>,
    /// Optional tampered outcome for emitting an additional negative diagnostic
    /// theorem asserting `(diagnoseRawByteTrace... { trace with outcome := ... }).tagName = "outcome_mismatch"`.
    pub tampered_outcome: Option<RecordedOutcome>,
}

fn render_u8_list_lean(bytes: &[u8]) -> String {
    if bytes.is_empty() {
        return "[]".to_string();
    }
    let items: Vec<String> = bytes.iter().map(|b| format!("{b}")).collect();
    format!("[{}]", items.join(", "))
}

fn render_u8_nested_list_lean(slices: &[Vec<u8>]) -> String {
    if slices.is_empty() {
        return "[]".to_string();
    }
    let items: Vec<String> = slices.iter().map(|s| render_u8_list_lean(s)).collect();
    format!("[{}]", items.join(", "))
}

fn escape_lean_string(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

/// Render a [`RecordedOutcome`] as a Lean `RawObservedOutcome` term.
pub fn render_raw_outcome_lean(outcome: &RecordedOutcome) -> String {
    match outcome {
        RecordedOutcome::Normal { raw_ret } => {
            format!(".normal {}", render_u8_list_lean(raw_ret))
        }
        RecordedOutcome::Panic => ".panic".to_string(),
        RecordedOutcome::Abort => ".abort".to_string(),
    }
}

/// Render a [`RecordedShadowAlloc`] slice as a Lean `ShadowProvenanceTable` literal.
pub fn render_shadow_provenance_table_lean(entries: &[RecordedShadowAlloc]) -> String {
    if entries.is_empty() {
        return "[]".to_string();
    }
    let rendered: Vec<String> = entries
        .iter()
        .map(|e| {
            if e.raw_bytes.is_empty() {
                format!(
                    "{{ baseAddr := {}, byteLen := {}, allocId := {}, tag := {} }}",
                    e.base_addr, e.byte_len, e.alloc_id, e.tag
                )
            } else {
                format!(
                    "{{ baseAddr := {}, byteLen := {}, allocId := {}, tag := {}, rawBytes := {} }}",
                    e.base_addr,
                    e.byte_len,
                    e.alloc_id,
                    e.tag,
                    render_u8_list_lean(&e.raw_bytes)
                )
            }
        })
        .collect();
    format!("[{}]", rendered.join(", "))
}

/// Render a [`RecordedRawTrace`] as a Lean `RawByteTrace` structure literal.
pub fn render_raw_byte_trace_lean(
    trace: &RecordedRawTrace,
    init_mem_expr: &str,
    inlined_callee_modules: &[String],
) -> String {
    let raw_args = render_u8_nested_list_lean(&trace.raw_args);
    let inlined_bodies: Vec<String> = inlined_callee_modules
        .iter()
        .map(|m| format!("{m}.body"))
        .collect();
    let inlined_expr = if inlined_bodies.is_empty() {
        "[]".to_string()
    } else {
        format!("[{}]", inlined_bodies.join(", "))
    };

    let events_expr = if trace.events.is_empty() {
        "[]".to_string()
    } else {
        let evs: Vec<String> = trace
            .events
            .iter()
            .map(|ev| match ev {
                RecordedEvent::Branch { tag } => format!(".branch {tag}"),
                RecordedEvent::ExtCall {
                    def_path,
                    raw_args,
                    raw_ret,
                } => format!(
                    ".extCall \"{}\" {} {}",
                    escape_lean_string(def_path),
                    render_u8_nested_list_lean(raw_args),
                    render_u8_list_lean(raw_ret)
                ),
                RecordedEvent::ExtCallPanic { def_path, raw_args } => format!(
                    ".extCallPanic \"{}\" {}",
                    escape_lean_string(def_path),
                    render_u8_nested_list_lean(raw_args)
                ),
                RecordedEvent::ExtCallAbort { def_path, raw_args } => format!(
                    ".extCallAbort \"{}\" {}",
                    escape_lean_string(def_path),
                    render_u8_nested_list_lean(raw_args)
                ),
            })
            .collect();
        format!("[{}]", evs.join(", "))
    };

    let outcome_expr = render_raw_outcome_lean(&trace.outcome);

    format!(
        "{{\n  rawArgs := {raw_args}\n  initMem := {init_mem_expr}\n  inlinedCallees := {inlined_expr}\n  events := {events_expr}\n  outcome := {outcome_expr}\n}}"
    )
}

/// Render a named `@[reducible] def <def_name> : RawByteTrace := ...` Lean
/// declaration from a [`RecordedRawTrace`].
pub fn render_raw_byte_trace_lean_def(
    def_name: &str,
    trace: &RecordedRawTrace,
    init_mem_expr: &str,
    inlined_callee_modules: &[String],
) -> String {
    let body = render_raw_byte_trace_lean(trace, init_mem_expr, inlined_callee_modules);
    format!("@[reducible]\ndef {def_name} : RawByteTrace :=\n{body}\n")
}

/// Render a Lean 4 snippet asserting that the computable diagnostic runner
/// (`diagnoseRawByteTraceFullBounded` when `cfg.check_branches` is `true`, or
/// `diagnoseRawByteTraceObsErasedBounded` when `false`) evaluates to
/// `expected_tag` (e.g., `"ok"` or `"outcome_mismatch"`) by kernel reduction
/// (`by rfl`), with an optional `#eval` diagnostic line.
pub fn render_trace_diag_eval_lean_snippet(
    theorem_name: &str,
    cfg: &TraceCheckModuleConfig,
    callee_sigs_expr: &str,
    table_expr: &str,
    trace_expr: &str,
    expected_tag: &str,
    emit_eval: bool,
) -> String {
    let root_body = format!("{}.body", cfg.root_mir_module);
    let fuel = cfg.fuel;
    let diag_fn = if cfg.check_branches {
        "diagnoseRawByteTraceFullBounded"
    } else {
        "diagnoseRawByteTraceObsErasedBounded"
    };
    let escaped_tag = escape_lean_string(expected_tag);

    let mut out = String::new();
    let _ = writeln!(
        out,
        "set_option maxHeartbeats 400000 in\n\
         theorem {theorem_name} :\n\
         \x20   ({diag_fn} {fuel} {root_body} {callee_sigs_expr} {table_expr} {trace_expr}).tagName = \"{escaped_tag}\" := by\n\
         \x20 rfl\n"
    );
    if emit_eval {
        let _ = writeln!(
            out,
            "#eval ({diag_fn} {fuel} {root_body} {callee_sigs_expr} {table_expr} {trace_expr}).tagName\n"
        );
    }
    out
}

/// Render a Lean 4 negative assertion snippet proving by `by rfl` that
/// replacing `trace_ident`'s `outcome` with `tampered_outcome` yields
/// `.tagName = "outcome_mismatch"` under `diagnoseRawByteTraceObsErasedBounded`
/// (or `diagnoseRawByteTraceFullBounded` when `cfg.check_branches` is `true`).
pub fn render_tampered_outcome_diag_lean_snippet(
    theorem_name: &str,
    cfg: &TraceCheckModuleConfig,
    callee_sigs_expr: &str,
    table_expr: &str,
    trace_ident: &str,
    tampered_outcome: &RecordedOutcome,
) -> String {
    let outcome_expr = render_raw_outcome_lean(tampered_outcome);
    let tampered_trace_expr = format!("{{ {trace_ident} with outcome := {outcome_expr} }}");
    render_trace_diag_eval_lean_snippet(
        theorem_name,
        cfg,
        callee_sigs_expr,
        table_expr,
        &tampered_trace_expr,
        "outcome_mismatch",
        false,
    )
}

/// Render a complete Lean 4 module that decodes `trace` via `decodeRawByteTrace`,
/// verifies its diagnostic tag (`"ok"`) via `diagnoseRawByteTrace*Bounded`,
/// and proves its consistency with the captured `Mir.*` interaction tree in the
/// Lean 4 kernel (`checkRawByteTraceFullBounded_sound` when
/// `cfg.check_branches` is `true`, or `checkRawByteTraceObsErasedBounded_sound`
/// when `cfg.check_branches` is `false`).
pub fn render_trace_check_lean_module(
    cfg: &TraceCheckModuleConfig,
    trace: &RecordedRawTrace,
) -> String {
    let mut out = String::new();
    out.push_str("import Trusted\n");
    out.push_str("import Anneal\n");
    let _ = writeln!(out, "import {}", cfg.root_mir_module);

    let mut imported = vec![cfg.root_mir_module.clone()];
    for m in cfg
        .callee_sig_modules
        .iter()
        .chain(cfg.inlined_callee_modules.iter())
    {
        if !imported.contains(m) {
            let _ = writeln!(out, "import {m}");
            imported.push(m.clone());
        }
    }

    let _ = writeln!(out, "\nnamespace {}\n", cfg.module_namespace);
    out.push_str("open Trusted.Effect\n");
    out.push_str("open Trusted.ITree\n");
    out.push_str("open Trusted.Rustc.V2026_06_01.MirAst\n");
    out.push_str("open Trusted.Rustc.V2026_06_01.MirSemantics\n");
    out.push_str("open Trusted.VerificationResult\n");
    out.push_str("open Anneal.Rustc.V2026_06_01.TraceCheck\n\n");

    let callee_sigs_list = if cfg.callee_sig_modules.is_empty() {
        "[]".to_string()
    } else {
        let items: Vec<String> = cfg
            .callee_sig_modules
            .iter()
            .map(|m| format!("{m}.body"))
            .collect();
        format!("[{}]", items.join(", "))
    };

    let init_mem_expr = cfg.init_mem_expr.as_deref().unwrap_or("emptyMemory");
    let table_expr = render_shadow_provenance_table_lean(&trace.shadow_provenance);
    let trace_expr =
        render_raw_byte_trace_lean(trace, init_mem_expr, &cfg.inlined_callee_modules);

    let _ = writeln!(
        out,
        "@[reducible]\ndef calleeSigs : List CapturedMir := {callee_sigs_list}\n"
    );
    let _ = writeln!(
        out,
        "@[reducible]\ndef shadowTable : ShadowProvenanceTable := {table_expr}\n"
    );
    let _ = writeln!(
        out,
        "@[reducible]\ndef observedRawTrace : RawByteTrace :=\n{trace_expr}\n"
    );

    let root_body = format!("{}.body", cfg.root_mir_module);
    let fuel = cfg.fuel;

    if cfg.check_branches {
        let _ = writeln!(
            out,
            "set_option maxHeartbeats 400000 in\n\
             theorem trace_consistent :\n\
             \x20   ∃ obsTrace tr out,\n\
             \x20     decodeRawByteTrace {root_body} calleeSigs shadowTable observedRawTrace = some obsTrace ∧\n\
             \x20     MatchesObservedEvents obsTrace.events tr ∧\n\
             \x20     MatchesObservedOutcome obsTrace.outcome out ∧\n\
             \x20     ReachesRet\n\
             \x20       (mirStatefulTree {root_body} obsTrace.args\n\
             \x20         {{ obsTrace.initMem with callees := obsTrace.inlinedCallees }})\n\
             \x20       tr out :=\n\
             \x20 checkRawByteTraceFullBounded_sound {fuel} {root_body} calleeSigs shadowTable observedRawTrace rfl\n"
        );
    } else {
        let _ = writeln!(
            out,
            "set_option maxHeartbeats 400000 in\n\
             theorem trace_consistent :\n\
             \x20   ∃ obsTrace tr out,\n\
             \x20     decodeRawByteTrace {root_body} calleeSigs shadowTable observedRawTrace = some obsTrace ∧\n\
             \x20     MatchesObservedEvents obsTrace.events tr ∧\n\
             \x20     MatchesObservedOutcome obsTrace.outcome out ∧\n\
             \x20     ReachesRet\n\
             \x20       (mirObsErasedStatefulTree {root_body} obsTrace.args\n\
             \x20         {{ obsTrace.initMem with callees := obsTrace.inlinedCallees }})\n\
             \x20       tr out :=\n\
             \x20 checkRawByteTraceObsErasedBounded_sound {fuel} {root_body} calleeSigs shadowTable observedRawTrace rfl\n"
        );
    }

    out.push_str(&render_trace_diag_eval_lean_snippet(
        "trace_diag_ok",
        cfg,
        "calleeSigs",
        "shadowTable",
        "observedRawTrace",
        "ok",
        false,
    ));

    let _ = writeln!(out, "end {}", cfg.module_namespace);
    out
}

/// Render a batched Lean 4 verification and diagnostic evaluation module across
/// multiple [`BatchTraceEvalCase`] entries, sharing a single Lake/Lean
/// invocation and import header set.
pub fn render_batch_trace_eval_lean_module(
    module_namespace: &str,
    cases: &[BatchTraceEvalCase],
    emit_eval_commands: bool,
) -> String {
    let mut out = String::new();
    out.push_str("import Trusted\n");
    out.push_str("import Anneal\n");

    let mut imported: Vec<String> = Vec::new();
    for case in cases {
        for m in std::iter::once(&case.config.root_mir_module)
            .chain(case.config.callee_sig_modules.iter())
            .chain(case.config.inlined_callee_modules.iter())
        {
            if !imported.contains(m) {
                let _ = writeln!(out, "import {m}");
                imported.push(m.clone());
            }
        }
    }

    let _ = writeln!(out, "\nnamespace {module_namespace}\n");
    out.push_str("open Trusted.Effect\n");
    out.push_str("open Trusted.ITree\n");
    out.push_str("open Trusted.Rustc.V2026_06_01.MirAst\n");
    out.push_str("open Trusted.Rustc.V2026_06_01.MirSemantics\n");
    out.push_str("open Trusted.VerificationResult\n");
    out.push_str("open Anneal.Rustc.V2026_06_01.TraceCheck\n\n");

    for case in cases {
        let id = &case.case_ident;
        let cfg = &case.config;
        let callee_sigs_list = if cfg.callee_sig_modules.is_empty() {
            "[]".to_string()
        } else {
            let items: Vec<String> = cfg
                .callee_sig_modules
                .iter()
                .map(|m| format!("{m}.body"))
                .collect();
            format!("[{}]", items.join(", "))
        };
        let init_mem_expr = cfg.init_mem_expr.as_deref().unwrap_or("emptyMemory");
        let table_expr = render_shadow_provenance_table_lean(&case.trace.shadow_provenance);
        let trace_expr =
            render_raw_byte_trace_lean(&case.trace, init_mem_expr, &cfg.inlined_callee_modules);

        let sigs_ident = format!("{id}_calleeSigs");
        let table_ident = format!("{id}_shadowTable");
        let trace_ident = format!("{id}_rawTrace");

        let _ = writeln!(
            out,
            "@[reducible]\ndef {sigs_ident} : List CapturedMir := {callee_sigs_list}\n"
        );
        let _ = writeln!(
            out,
            "@[reducible]\ndef {table_ident} : ShadowProvenanceTable := {table_expr}\n"
        );
        let _ = writeln!(
            out,
            "@[reducible]\ndef {trace_ident} : RawByteTrace :=\n{trace_expr}\n"
        );

        let expected_tag = case.expected_diag_tag.as_deref().unwrap_or("ok");
        if expected_tag == "ok" {
            let root_body = format!("{}.body", cfg.root_mir_module);
            let fuel = cfg.fuel;
            let sound_thm = format!("{id}_trace_consistent");
            if cfg.check_branches {
                let _ = writeln!(
                    out,
                    "set_option maxHeartbeats 400000 in\n\
                     theorem {sound_thm} :\n\
                     \x20   ∃ obsTrace tr out,\n\
                     \x20     decodeRawByteTrace {root_body} {sigs_ident} {table_ident} {trace_ident} = some obsTrace ∧\n\
                     \x20     MatchesObservedEvents obsTrace.events tr ∧\n\
                     \x20     MatchesObservedOutcome obsTrace.outcome out ∧\n\
                     \x20     ReachesRet\n\
                     \x20       (mirStatefulTree {root_body} obsTrace.args\n\
                     \x20         {{ obsTrace.initMem with callees := obsTrace.inlinedCallees }})\n\
                     \x20       tr out :=\n\
                     \x20 checkRawByteTraceFullBounded_sound {fuel} {root_body} {sigs_ident} {table_ident} {trace_ident} rfl\n"
                );
            } else {
                let _ = writeln!(
                    out,
                    "set_option maxHeartbeats 400000 in\n\
                     theorem {sound_thm} :\n\
                     \x20   ∃ obsTrace tr out,\n\
                     \x20     decodeRawByteTrace {root_body} {sigs_ident} {table_ident} {trace_ident} = some obsTrace ∧\n\
                     \x20     MatchesObservedEvents obsTrace.events tr ∧\n\
                     \x20     MatchesObservedOutcome obsTrace.outcome out ∧\n\
                     \x20     ReachesRet\n\
                     \x20       (mirObsErasedStatefulTree {root_body} obsTrace.args\n\
                     \x20         {{ obsTrace.initMem with callees := obsTrace.inlinedCallees }})\n\
                     \x20       tr out :=\n\
                     \x20 checkRawByteTraceObsErasedBounded_sound {fuel} {root_body} {sigs_ident} {table_ident} {trace_ident} rfl\n"
                );
            }
        }

        let diag_thm = format!("{id}_diag_tag");
        out.push_str(&render_trace_diag_eval_lean_snippet(
            &diag_thm,
            cfg,
            &sigs_ident,
            &table_ident,
            &trace_ident,
            expected_tag,
            emit_eval_commands,
        ));

        if let Some(ref tampered) = case.tampered_outcome {
            let tampered_thm = format!("{id}_tampered_outcome_mismatch");
            out.push_str(&render_tampered_outcome_diag_lean_snippet(
                &tampered_thm,
                cfg,
                &sigs_ident,
                &table_ident,
                &trace_ident,
                tampered,
            ));
        }
    }

    let _ = writeln!(out, "end {module_namespace}");
    out
}

/// Render a Stage-1 Lean 4 probe module that evaluates
/// `diagnoseRawByteTraceObsErasedBounded` (or `diagnoseRawByteTraceFullBounded`)
/// via `#eval` for each [`BatchTraceEvalCase`] and prints
/// `ANNEAL_ITREE_DIAG:<case_ident>:<tag_name>:<repr>` to stdout without
/// failing compilation when a case diverges (`tagName != "ok"`).
pub fn render_batch_trace_probe_lean_module(
    module_namespace: &str,
    cases: &[BatchTraceEvalCase],
) -> String {
    let mut out = String::new();
    out.push_str("import Trusted\n");
    out.push_str("import Anneal\n");

    let mut imported: Vec<String> = Vec::new();
    for case in cases {
        for m in std::iter::once(&case.config.root_mir_module)
            .chain(case.config.callee_sig_modules.iter())
            .chain(case.config.inlined_callee_modules.iter())
        {
            if !imported.contains(m) {
                let _ = writeln!(out, "import {m}");
                imported.push(m.clone());
            }
        }
    }

    let _ = writeln!(out, "\nnamespace {module_namespace}\n");
    out.push_str("open Trusted.Effect\n");
    out.push_str("open Trusted.ITree\n");
    out.push_str("open Trusted.Rustc.V2026_06_01.MirAst\n");
    out.push_str("open Trusted.Rustc.V2026_06_01.MirSemantics\n");
    out.push_str("open Trusted.VerificationResult\n");
    out.push_str("open Anneal.Rustc.V2026_06_01.TraceCheck\n\n");

    for case in cases {
        let id = &case.case_ident;
        let cfg = &case.config;
        let callee_sigs_list = if cfg.callee_sig_modules.is_empty() {
            "[]".to_string()
        } else {
            let items: Vec<String> = cfg
                .callee_sig_modules
                .iter()
                .map(|m| format!("{m}.body"))
                .collect();
            format!("[{}]", items.join(", "))
        };
        let init_mem_expr = cfg.init_mem_expr.as_deref().unwrap_or("emptyMemory");
        let table_expr = render_shadow_provenance_table_lean(&case.trace.shadow_provenance);
        let trace_expr =
            render_raw_byte_trace_lean(&case.trace, init_mem_expr, &cfg.inlined_callee_modules);

        let sigs_ident = format!("{id}_calleeSigs");
        let table_ident = format!("{id}_shadowTable");
        let trace_ident = format!("{id}_rawTrace");

        let _ = writeln!(
            out,
            "@[reducible]\ndef {sigs_ident} : List CapturedMir := {callee_sigs_list}\n"
        );
        let _ = writeln!(
            out,
            "@[reducible]\ndef {table_ident} : ShadowProvenanceTable := {table_expr}\n"
        );
        let _ = writeln!(
            out,
            "@[reducible]\ndef {trace_ident} : RawByteTrace :=\n{trace_expr}\n"
        );

        let diag_fn = if cfg.check_branches {
            "diagnoseRawByteTraceFullBounded"
        } else {
            "diagnoseRawByteTraceObsErasedBounded"
        };
        let root_body = format!("{}.body", cfg.root_mir_module);
        let fuel = cfg.fuel;
        let diag_ident = format!("{id}_diag");
        let _ = writeln!(
            out,
            "def {diag_ident} : TraceReplayDiag :=\n  {diag_fn} {fuel} {root_body} {sigs_ident} {table_ident} {trace_ident}\n"
        );
        let _ = writeln!(
            out,
            "#eval IO.println s!\"ANNEAL_ITREE_DIAG:{id}:{{{diag_ident}.tagName}}:{{reprStr {diag_ident}}}\"\n"
        );
    }

    let _ = writeln!(out, "end {module_namespace}");
    out
}

/// Parse stdout lines emitted by [`render_batch_trace_probe_lean_module`] into
/// a map from `case_ident` to `(tag_name, diag_repr)`.
pub fn parse_batch_trace_probe_output(stdout: &str) -> BTreeMap<String, (String, String)> {
    const PREFIX: &str = "ANNEAL_ITREE_DIAG:";
    let mut out = BTreeMap::new();
    for line in stdout.lines() {
        let trimmed = line.trim();
        let Some(rest) = trimmed.strip_prefix(PREFIX) else {
            continue;
        };
        let Some((case_ident, after_id)) = rest.split_once(':') else {
            continue;
        };
        let (tag_name, repr_str) = after_id.split_once(':').unwrap_or((after_id, ""));
        out.insert(
            case_ident.to_string(),
            (tag_name.to_string(), repr_str.to_string()),
        );
    }
    out
}

fn bytes_to_hex(bytes: &[u8]) -> String {
    if bytes.is_empty() {
        return "-".to_string();
    }
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        let _ = write!(s, "{b:02x}");
    }
    s
}

fn hex_to_bytes(hex: &str) -> Result<Vec<u8>, String> {
    let trimmed = hex.trim();
    if trimmed.is_empty() || trimmed == "-" {
        return Ok(Vec::new());
    }
    if trimmed.len() % 2 != 0 {
        return Err(format!("odd-length hex slice `{trimmed}`"));
    }
    let mut out = Vec::with_capacity(trimmed.len() / 2);
    let bytes = trimmed.as_bytes();
    let mut i = 0usize;
    while i < bytes.len() {
        let pair = std::str::from_utf8(&bytes[i..i + 2])
            .map_err(|e| format!("invalid utf-8 in hex `{trimmed}`: {e}"))?;
        let b = u8::from_str_radix(pair, 16)
            .map_err(|e| format!("invalid hex byte `{pair}` in `{trimmed}`: {e}"))?;
        out.push(b);
        i += 2;
    }
    Ok(out)
}

fn encode_byte_slices_hex(slices: &[Vec<u8>]) -> String {
    if slices.is_empty() {
        return String::new();
    }
    slices
        .iter()
        .map(|s| bytes_to_hex(s))
        .collect::<Vec<_>>()
        .join(",")
}

fn decode_byte_slices_hex(raw: &str) -> Result<Vec<Vec<u8>>, String> {
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return Ok(Vec::new());
    }
    trimmed.split(',').map(hex_to_bytes).collect()
}

/// Encode a [`RecordedRawTrace`] as a single compact ASCII line suitable for
/// subprocess trace collection and standalone reproducer bundles.
pub fn encode_recorded_raw_trace_hex(trace: &RecordedRawTrace) -> String {
    let args_part = encode_byte_slices_hex(&trace.raw_args);
    let shadow_part = trace
        .shadow_provenance
        .iter()
        .map(|s| {
            if s.raw_bytes.is_empty() {
                format!("{}:{}:{}:{}", s.base_addr, s.byte_len, s.alloc_id, s.tag)
            } else {
                format!(
                    "{}:{}:{}:{}:{}",
                    s.base_addr,
                    s.byte_len,
                    s.alloc_id,
                    s.tag,
                    bytes_to_hex(&s.raw_bytes)
                )
            }
        })
        .collect::<Vec<_>>()
        .join(",");
    let events_part = trace
        .events
        .iter()
        .map(|ev| match ev {
            RecordedEvent::Branch { tag } => format!("B@{tag}"),
            RecordedEvent::ExtCall {
                def_path,
                raw_args,
                raw_ret,
            } => format!(
                "C@{def_path}@{}@{}",
                encode_byte_slices_hex(raw_args),
                bytes_to_hex(raw_ret)
            ),
            RecordedEvent::ExtCallPanic { def_path, raw_args } => {
                format!("P@{def_path}@{}", encode_byte_slices_hex(raw_args))
            }
            RecordedEvent::ExtCallAbort { def_path, raw_args } => {
                format!("A@{def_path}@{}", encode_byte_slices_hex(raw_args))
            }
        })
        .collect::<Vec<_>>()
        .join(";");
    let outcome_part = match &trace.outcome {
        RecordedOutcome::Normal { raw_ret } => format!("N@{}", bytes_to_hex(raw_ret)),
        RecordedOutcome::Panic => "P".to_string(),
        RecordedOutcome::Abort => "A".to_string(),
    };
    format!(
        "{}|{}|{}|{}|{}",
        trace.root_def_path, args_part, shadow_part, events_part, outcome_part
    )
}

/// Decode a single line produced by [`encode_recorded_raw_trace_hex`] back into
/// a [`RecordedRawTrace`].
pub fn decode_recorded_raw_trace_hex(line: &str) -> Result<RecordedRawTrace, String> {
    let parts: Vec<&str> = line.trim().splitn(5, '|').collect();
    if parts.len() != 5 {
        return Err(format!(
            "expected 5 `|`-separated fields in trace line, got {}: `{line}`",
            parts.len()
        ));
    }
    let root_def_path = parts[0].to_string();
    let raw_args = decode_byte_slices_hex(parts[1])?;
    let mut shadow_provenance = Vec::new();
    if !parts[2].trim().is_empty() {
        for item in parts[2].split(',') {
            let nums: Vec<&str> = item.split(':').collect();
            if nums.len() != 4 && nums.len() != 5 {
                return Err(format!("invalid shadow provenance entry `{item}`"));
            }
            let raw_bytes = if nums.len() == 5 {
                hex_to_bytes(nums[4])?
            } else {
                Vec::new()
            };
            shadow_provenance.push(RecordedShadowAlloc {
                base_addr: nums[0]
                    .parse::<usize>()
                    .map_err(|e| format!("invalid base_addr `{}`: {e}", nums[0]))?,
                byte_len: nums[1]
                    .parse::<usize>()
                    .map_err(|e| format!("invalid byte_len `{}`: {e}", nums[1]))?,
                alloc_id: nums[2]
                    .parse::<usize>()
                    .map_err(|e| format!("invalid alloc_id `{}`: {e}", nums[2]))?,
                tag: nums[3]
                    .parse::<usize>()
                    .map_err(|e| format!("invalid tag `{}`: {e}", nums[3]))?,
                raw_bytes,
            });
        }
    }
    let mut events = Vec::new();
    if !parts[3].trim().is_empty() {
        for ev_str in parts[3].split(';') {
            let fields: Vec<&str> = ev_str.split('@').collect();
            match fields.as_slice() {
                ["B", tag_s] => {
                    let tag = tag_s
                        .parse::<u128>()
                        .map_err(|e| format!("invalid branch tag `{tag_s}`: {e}"))?;
                    events.push(RecordedEvent::Branch { tag });
                }
                ["C", def_path, args_s, ret_s] => {
                    events.push(RecordedEvent::ExtCall {
                        def_path: (*def_path).to_string(),
                        raw_args: decode_byte_slices_hex(args_s)?,
                        raw_ret: hex_to_bytes(ret_s)?,
                    });
                }
                ["P", def_path, args_s] => {
                    events.push(RecordedEvent::ExtCallPanic {
                        def_path: (*def_path).to_string(),
                        raw_args: decode_byte_slices_hex(args_s)?,
                    });
                }
                ["A", def_path, args_s] => {
                    events.push(RecordedEvent::ExtCallAbort {
                        def_path: (*def_path).to_string(),
                        raw_args: decode_byte_slices_hex(args_s)?,
                    });
                }
                _ => return Err(format!("unrecognized encoded event `{ev_str}`")),
            }
        }
    }
    let outcome = if let Some(ret_hex) = parts[4].strip_prefix("N@") {
        RecordedOutcome::Normal {
            raw_ret: hex_to_bytes(ret_hex)?,
        }
    } else if parts[4] == "P" {
        RecordedOutcome::Panic
    } else if parts[4] == "A" {
        RecordedOutcome::Abort
    } else {
        return Err(format!("unrecognized encoded outcome `{}`", parts[4]));
    };

    Ok(RecordedRawTrace {
        root_def_path,
        raw_args,
        shadow_provenance,
        events,
        outcome,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::num::NonZeroU32;

    #[anneal_trace::capture]
    #[repr(C)]
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct TestPaddedStruct {
        flag: u8,
        value: u32,
    }

    #[anneal_trace::capture]
    #[repr(C)]
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum TestMode {
        Fast = 0,
        Safe = 1,
    }

    #[test]
    fn capture_value_bytes_never_reads_uninitialized_padding_and_marks_it_unknown() {
        let mut slot = mem::MaybeUninit::<TestPaddedStruct>::uninit();
        let s_ref = unsafe {
            let base = slot.as_mut_ptr();
            core::ptr::addr_of_mut!((*base).flag).write(1);
            core::ptr::addr_of_mut!((*base).value).write(0x0403_0201);
            slot.assume_init_ref()
        };
        let captured = capture_value_bytes(s_ref);
        assert_eq!(
            captured,
            vec![
                Some(1),
                None,
                None,
                None,
                Some(1),
                Some(2),
                Some(3),
                Some(4),
            ]
        );
        let raw = value_as_raw_bytes(s_ref);
        assert_eq!(raw, vec![1, 0, 0, 0, 1, 2, 3, 4]);
    }

    #[test]
    fn value_as_raw_bytes_ignores_scribbled_padding_bytes_and_masks_them_as_zero() {
        let mut s = TestPaddedStruct {
            flag: 1,
            value: 0x0403_0201,
        };
        unsafe {
            let ptr = (&mut s as *mut TestPaddedStruct).cast::<u8>();
            *ptr.add(1) = 0xAA;
            *ptr.add(2) = 0xBB;
            *ptr.add(3) = 0xCC;
        }
        assert_eq!(
            capture_value_bytes(&s),
            vec![
                Some(1),
                None,
                None,
                None,
                Some(1),
                Some(2),
                Some(3),
                Some(4),
            ]
        );
        let raw = value_as_raw_bytes(&s);
        assert_eq!(raw, vec![1, 0, 0, 0, 1, 2, 3, 4]);
        assert!(value_as_raw_bytes(&()).is_empty());
    }

    #[test]
    fn from_schedule_bytes_validates_invariants_without_ub() {
        assert_eq!(bool::from_schedule_bytes(&[0]), Ok(false));
        assert_eq!(bool::from_schedule_bytes(&[1]), Ok(true));
        assert!(bool::from_schedule_bytes(&[2]).is_err());
        assert!(bool::from_schedule_bytes(&[0, 0]).is_err());

        assert_eq!(
            char::from_schedule_bytes(&('A' as u32).to_le_bytes()),
            Ok('A')
        );
        assert!(char::from_schedule_bytes(&0xD800u32.to_le_bytes()).is_err());
        assert!(char::from_schedule_bytes(&0x0011_0000u32.to_le_bytes()).is_err());

        assert!(NonZeroU32::from_schedule_bytes(&0u32.to_le_bytes()).is_err());
        assert_eq!(
            NonZeroU32::from_schedule_bytes(&7u32.to_le_bytes()),
            Ok(NonZeroU32::new(7).unwrap())
        );

        assert_eq!(
            TestMode::from_schedule_bytes(&0i32.to_le_bytes()),
            Ok(TestMode::Fast)
        );
        assert_eq!(
            TestMode::from_schedule_bytes(&1i32.to_le_bytes()),
            Ok(TestMode::Safe)
        );
        assert!(TestMode::from_schedule_bytes(&2i32.to_le_bytes()).is_err());

        let decoded_struct =
            TestPaddedStruct::from_schedule_bytes(&[1, 0xFF, 0xFF, 0xFF, 1, 2, 3, 4])
                .expect("valid struct fields decode cleanly ignoring padding bytes");
        assert_eq!(
            decoded_struct,
            TestPaddedStruct {
                flag: 1,
                value: 0x0403_0201
            }
        );

        // Niche-optimized Option<bool>
        for opt_b in [None, Some(false), Some(true)] {
            let raw = value_as_raw_bytes(&opt_b);
            assert_eq!(Option::<bool>::from_schedule_bytes(&raw), Ok(opt_b));
        }
        assert!(Option::<bool>::from_schedule_bytes(&[3]).is_err());

        // Niche-optimized Option<char>
        for opt_c in [None, Some('\0'), Some('A')] {
            let raw = value_as_raw_bytes(&opt_c);
            assert_eq!(Option::<char>::from_schedule_bytes(&raw), Ok(opt_c));
        }
        assert!(Option::<char>::from_schedule_bytes(&0xD800u32.to_le_bytes()).is_err());

        // Niche-optimized Option<NonZeroU32>
        let nz7 = NonZeroU32::new(7).unwrap();
        assert_eq!(
            capture_value_bytes(&None::<NonZeroU32>),
            vec![Some(0), Some(0), Some(0), Some(0)]
        );
        for opt_nz in [None, Some(nz7)] {
            let raw = value_as_raw_bytes(&opt_nz);
            assert_eq!(Option::<NonZeroU32>::from_schedule_bytes(&raw), Ok(opt_nz));
        }

        // Niche-optimized Option<TestMode>
        for opt_m in [None, Some(TestMode::Fast), Some(TestMode::Safe)] {
            let raw = value_as_raw_bytes(&opt_m);
            assert_eq!(Option::<TestMode>::from_schedule_bytes(&raw), Ok(opt_m));
        }
        assert!(Option::<TestMode>::from_schedule_bytes(&2i32.to_le_bytes()).is_err());
    }

    #[anneal_trace::external]
    fn ext(x: u32) -> u32 {
        x.wrapping_mul(2)
    }

    #[anneal_trace::external]
    fn ext_bool(x: u32) -> bool {
        x != 0
    }

    #[anneal_trace::external]
    fn boom() -> u32 {
        panic!("simulated external panic");
    }

    #[test]
    fn env_schedule_rejects_mismatched_return_payload_sizes() {
        let mut sched = EnvSchedule::new().with_callee_return_size("demo::ext", 4);
        assert!(sched.push_callee_response_checked("demo::ext", vec![1, 2, 3, 4]).is_ok());
        let err = sched
            .push_callee_response_checked("demo::ext", vec![1, 2])
            .expect_err("2-byte payload for 4-byte callee must fail");
        assert_eq!(
            err,
            ScheduleError::PayloadSizeMismatch {
                context: "demo::ext".to_string(),
                expected: 4,
                actual: 2,
            }
        );
    }

    #[test]
    fn observe_boundary_call_rejects_mismatched_and_invalid_return_bytes_without_fallthrough() {
        let mut bad_len_sched = EnvSchedule::new();
        bad_len_sched.push_callee_response("demo::ext", vec![1, 2]);
        let rec = TraceRecorder::with_schedule(bad_len_sched);
        let (res, _trace, _rec) =
            TraceRecorder::observe_root_with_recorder(rec, "demo::root", vec![], |_rec| ext(5));
        assert!(
            res.is_err(),
            "mismatched ReturnBytes payload size must panic rather than falling through to f()"
        );

        let mut bad_bool_sched = EnvSchedule::new();
        bad_bool_sched.push_callee_response("demo::ext_bool", vec![2]);
        let rec2 = TraceRecorder::with_schedule(bad_bool_sched);
        let (res2, _trace2, _rec2) =
            TraceRecorder::observe_root_with_recorder(rec2, "demo::root", vec![], |_rec| {
                ext_bool(5)
            });
        assert!(
            res2.is_err(),
            "invalid bool bit pattern in ReturnBytes must fail validation without UB"
        );
    }

    #[test]
    fn trace_recorder_captures_normal_and_panicking_external_calls() {
        let arg: u32 = 7;
        let (ok_res, ok_trace) =
            TraceRecorder::observe_root("demo::root", vec![value_as_raw_bytes(&arg)], |rec| {
                rec.record_branch(0);
                ext(arg)
            });
        assert_eq!(ok_res.expect("normal return"), 14);
        assert_eq!(
            ok_trace.events,
            vec![
                RecordedEvent::Branch { tag: 0 },
                RecordedEvent::ExtCall {
                    def_path: "demo::ext".to_string(),
                    raw_args: vec![vec![7, 0, 0, 0]],
                    raw_ret: vec![14, 0, 0, 0],
                },
            ]
        );
        assert_eq!(
            ok_trace.outcome,
            RecordedOutcome::Normal {
                raw_ret: vec![14, 0, 0, 0]
            }
        );

        let (panic_res, panic_trace) =
            TraceRecorder::observe_root("demo::panic_root", vec![], |_rec| boom());
        assert!(panic_res.is_err());
        assert_eq!(
            panic_trace.events,
            vec![RecordedEvent::ExtCallPanic {
                def_path: "demo::boom".to_string(),
                raw_args: vec![],
            }]
        );
        assert_eq!(panic_trace.outcome, RecordedOutcome::Panic);
    }

    #[test]
    fn render_single_and_batch_lean_modules_emit_soundness_and_diag_assertions() {
        let trace = RecordedRawTrace {
            root_def_path: "trace_pkg::process_packet".to_string(),
            raw_args: vec![vec![1, 0xAA, 0xBB, 0xCC, 11, 0, 0, 0], vec![10, 0, 0, 0]],
            shadow_provenance: vec![RecordedShadowAlloc {
                base_addr: 0x1000,
                byte_len: 4,
                alloc_id: 7,
                tag: 7,
                raw_bytes: Vec::new(),
            }],
            events: vec![RecordedEvent::ExtCall {
                def_path: "trace_pkg::ext_scale_add".to_string(),
                raw_args: vec![vec![10, 0, 0, 0], vec![11, 0, 0, 0]],
                raw_ret: vec![21, 0, 0, 0],
            }],
            outcome: RecordedOutcome::Normal {
                raw_ret: vec![42, 0, 0, 0],
            },
        };
        let cfg = TraceCheckModuleConfig {
            module_namespace: "TraceVerify.Unit".to_string(),
            root_mir_module: "Mir.TracePkg.process_packet".to_string(),
            callee_sig_modules: vec!["Mir.TracePkg.ext_scale_add".to_string()],
            inlined_callee_modules: vec!["Mir.TracePkg.helper_double".to_string()],
            init_mem_expr: None,
            fuel: 60,
            check_branches: false,
        };

        let single_mod = render_trace_check_lean_module(&cfg, &trace);
        assert!(single_mod.contains("checkRawByteTraceObsErasedBounded_sound 60"));
        assert!(single_mod.contains("diagnoseRawByteTraceObsErasedBounded 60"));
        assert!(single_mod.contains(".tagName = \"ok\""));
        assert!(single_mod.contains("{ baseAddr := 4096, byteLen := 4, allocId := 7, tag := 7 }"));

        let batch_mod = render_batch_trace_eval_lean_module(
            "TraceVerify.Batch",
            &[BatchTraceEvalCase {
                case_ident: "packet_case".to_string(),
                config: cfg,
                trace,
                expected_diag_tag: Some("ok".to_string()),
                tampered_outcome: Some(RecordedOutcome::Normal {
                    raw_ret: vec![99, 0, 0, 0],
                }),
            }],
            true,
        );
        assert!(batch_mod.contains("theorem packet_case_trace_consistent"));
        assert!(batch_mod.contains("theorem packet_case_diag_tag"));
        assert!(batch_mod.contains("#eval (diagnoseRawByteTraceObsErasedBounded 60"));
        assert!(batch_mod.contains("theorem packet_case_tampered_outcome_mismatch"));
        assert!(batch_mod.contains("outcome := .normal [99, 0, 0, 0]"));
        assert!(batch_mod.contains(".tagName = \"outcome_mismatch\""));
    }
}
