//! Runnable companion crate for the Anneal Tutor (`docs/tutor/`).
//!
//! `frame_tutor` models a minimal packet-frame header verifier that progresses
//! across all six chapters of the tutorial:
//!
//! - [`magic_version`]: a zero-argument constant function verified
//!   automatically by `Verify.FrameTutor.magic_version.defaultProof` without
//!   authored `Specs` or `Proof` files (Chapter 1).
//! - [`pin_magic`]: an identity function with a pinned Rust `#[spec]`
//!   precondition (`magic == 7`), proved directly against
//!   `Obligations.FrameTutor.pin_magic.defaultSpec` via `dischargeRustEqU32`
//!   without a `Specs` override (Chapters 2, 3, and 4).
//! - [`total_frame_len`]: a two-argument arithmetic function with a conjunctive
//!   Rust `#[spec]` precondition (`header_len == 1 && payload_len == 2`),
//!   proved directly against `Obligations.FrameTutor.total_frame_len.defaultSpec`
//!   via `dischargeRustEq2U8` without a `Specs` override (Chapters 2 and 4).
//! - [`advance_offset`]: a safe bounded-arithmetic function whose Rust
//!   `#[spec]` contract is refined in `Specs/FrameTutor/advance_offset.lean`
//!   via `Obligations.FrameTutor.advance_offset.refineSafeSpec` (separating
//!   the `.defined` safety domain `advanceOffsetSafetyDomain` from the `.val`
//!   functional precondition `offset < 4`) and discharged in
//!   `Proof/FrameTutor/advance_offset.lean` via `verifyByWPSafe` and
//!   `MirContractHoldsWithSafety` (Chapters 2 and 4).
//! - [`is_valid_version`] and [`FrameLen`]: a `#[model]` specification helper
//!   and an `#[invariant]` newtype captured alongside the crate's subject
//!   items (Chapter 2).
//! - [`read_version_ref`]: a stateful `unsafe` reference read whose `# Safety`
//!   pointer-validity precondition populates `.defined` of
//!   `MirStatefulContractSpec` via `StatefulItemSpec`, verified against
//!   `StatefulVerificationResult` using `dischargeStatefulEq` (Chapters 5 and
//!   6).
//! - [`write_version_mut`]: a stateful `unsafe` mutable reference write whose
//!   `.active` Tree Borrows `BorrowEntry` precondition populates `.defined` of
//!   `MirStatefulContractSpec` via `StatefulItemSpec`, verified against
//!   `StatefulVerificationResult` using `dischargeStatefulEq` and paired with a
//!   `BorrowTokenSep` ownership witness (Chapters 5 and 6).
//! - [`WireHeader`]: an `#[anneal_spec::unsafe_trait]` marker trait whose
//!   `#[anneal_spec::unsafe_impl(true)]` implementation for [`FrameLen`]
//!   generates the `__anneal_unsafe_impl_WireHeader_for_FrameLen` obligation,
//!   verified alongside `Anneal.BitValidity` layout theorems (Chapters 5 and
//!   6).

#![no_std]

use anneal_spec::*;

/// Returns the wire-format protocol magic version (`1`).
///
/// Because `magic_version` takes zero arguments and has no custom contract,
/// `cargo anneal scaffold` generates a `Verify.FrameTutor.magic_version`
/// root that discharges `VerificationResult` automatically via `verifyByWP`.
pub const fn magic_version() -> u32 {
    1
}

/// Echoes a pinned 32-bit frame magic constant (`7`).
///
/// The inline `#[anneal_spec::spec]` contract lowers directly into
/// `Obligations.FrameTutor.pin_magic.rustRequires` and `rustEnsures`, allowing
/// `Proof/FrameTutor/pin_magic.lean` to discharge the default `ItemSpec`
/// without a separate `Specs` override.
#[anneal_spec::spec(
    requires: magic == 7,
    ensures: |ref ret| *ret == 7,
)]
pub fn pin_magic(magic: u32) -> u32 {
    magic
}

/// Computes the total wire-frame byte length from a fixed 1-byte header
/// and a 2-byte payload.
///
/// Demonstrates multi-argument `#[anneal_spec::spec]` precondition
/// inversion (`requires: header_len == 1 && payload_len == 2`) discharged
/// in a single call to `Anneal.Tactics.dischargeRustEq2U8` with no authored
/// `Specs` override.
#[anneal_spec::spec(
    requires: header_len == 1 && payload_len == 2,
    ensures: |ref ret| *ret == 3,
)]
pub fn total_frame_len(header_len: u8, payload_len: u8) -> u8 {
    header_len + payload_len
}

/// Advances a 1-byte header offset by 4 bytes when `offset < 4`.
///
/// `Specs/FrameTutor/advance_offset.lean` refines the generated `defaultSpec`
/// via `Obligations.FrameTutor.advance_offset.refineSafeSpec`, placing a
/// two-case safety domain (`offset = 2` and `offset = 255`) in `.defined` of
/// `MirContractSpec` while guarding `rustEnsures` (`*ret == offset + 4`)
/// behind `rustRequires` (`offset < 4`) inside `.val`.
/// `Proof/FrameTutor/advance_offset.lean` discharges `VerificationResult` via
/// `verifyByWPSafe`—proving the functional postcondition at `offset = 2` and
/// safe overflow panic (`TerminationKind.panic`, `WPSafe = True`) at
/// `offset = 255`—and derives `MirContractHoldsWithSafety`.
#[anneal_spec::spec(
    requires: offset < 4,
    ensures: |ref ret| *ret == offset + 4,
)]
pub fn advance_offset(offset: u8) -> u8 {
    offset + 4
}

/// Pure specification helper that returns `true` when `v` matches wire version
/// `1`.
#[anneal_spec::model]
pub const fn is_valid_version(v: u8) -> bool {
    v == 1
}

/// Validated frame byte length bounded to at most 64 bytes.
#[anneal_spec::invariant(self.0 <= 64)]
pub struct FrameLen(pub u8);

/// Reads the version byte pointed to by `hdr`.
///
/// Unlike safe `advance_offset` (which panics safely without Undefined
/// Behavior on out-of-contract inputs), `read_version_ref` is `unsafe fn`: its
/// pointer-validity precondition lives in `.defined` of
/// `MirStatefulContractSpec` via `StatefulItemSpec`.
///
/// # Safety
///
/// `hdr` must point to an initialized, readable byte in memory.
pub unsafe fn read_version_ref(hdr: &u8) -> u8 {
    *hdr
}

/// Overwrites the protocol version byte in place through a mutable
/// reference and returns the stored version byte.
///
/// Demonstrates stateful `unsafe` verification (`StatefulItemSpec` +
/// `dischargeStatefulEq`) over an `.active` Tree Borrows `BorrowEntry` and
/// `Anneal.SepLogic` (`BorrowTokenSep`).
///
/// # Safety
///
/// `hdr` must point to a writable, uniquely borrowed byte in memory under an
/// `.active` Tree Borrows permission.
pub unsafe fn write_version_mut(hdr: &mut u8, ver: u8) -> u8 {
    *hdr = ver;
    *hdr
}

/// Marker trait for wire-frame header types whose single-byte layout is
/// unaligned and free of padding bytes.
#[anneal_spec::unsafe_trait]
pub unsafe trait WireHeader {}

#[anneal_spec::unsafe_impl(true)]
unsafe impl WireHeader for FrameLen {}

