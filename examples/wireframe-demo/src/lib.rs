//! End-to-end binary packet and frame codec showcase (`wireframe_demo`) for
//! Anneal's four human-and-agent verification user journeys.
//!
//! Each item in this crate anchors one stage of the walkthrough in
//! `docs/demo-user-journeys.md` and `examples/wireframe-demo/run_live_demo.py`:
//!
//! 1. **Journey 1 — Bootstrapping Verification on Safe Rust**:
//!    - [`WIRE_VERSION_V1`] and [`wire_protocol_version`]: zero-argument
//!      constants verified automatically by generated `defaultProof` instances
//!      (`SymbolicEval.verifyByWP`) with zero authored Lean files.
//!    - [`is_valid_payload_len`] (`#[anneal_spec::model]`) and [`FrameCursor`]
//!      (`#[anneal_spec::invariant]`): Rust-level specification companions
//!      extracted into `.anneal/capture/Mir/WireframeDemo/`.
//!    - [`frame_total_len`]: safe bounded-arithmetic contract verified
//!      universally across all `17 * 1025 = 17,425` valid `(header_len,
//!      payload_len)` inputs directly from its inline `#[anneal_spec::spec]`.
//!    - [`advance_cursor`]: stateful `&mut FrameCursor` cursor advancement
//!      verified via `Anneal.FunctionalTranslation` (`MutLens` + `PointsTo` +
//!      `TransPlan`), proving both functional postcondition satisfaction and
//!      preservation of `FrameCursor`'s `offset <= limit` invariant.
//!
//! 2. **Journey 2 — Finding and Repairing an Existing `unsafe` Bug**:
//!    - [`WireHeader`] and [`decode_wire_header`]: zero-copy wire header
//!      decoding via `core::mem::transmute::<[u8; 4], WireHeader>(raw)`. Without
//!      the `raw[1] > 1` bit-validity guard on `WireHeader::compressed: bool`,
//!      Anneal refutes `Claim.holds` with a kernel-checked Undefined Behavior
//!      counterexample at `raw = [1, 2, 4, 0]` (`refuteClaimByBoundedUB`); with
//!      the guard in place, `decode_wire_header` verifies unconditionally across
//!      all `2^32` 4-byte inputs.
//!
//! 3. **Journey 3 — Keeping the Code Author and Reviewer in Check**:
//!    - *3A (Agent Authoring Under Locked Specs)* — [`clamp_payload_window`]:
//!      human lead locks `#[anneal_spec::spec]` via
//!      `cargo anneal lock-specs --allow-impl-edit clamp_payload_window`;
//!      `cargo anneal agent-verify` rejects specification tampering, buggy
//!      implementations, `sorry`, and rogue `axiom` declarations before
//!      accepting the verified implementation.
//!    - *3B (Agent Reviewing Human-Authored Code)* — [`parse_compression_flag`]:
//!      review contract using `refineSafeSpec` (`MirContractHoldsWithSafety`)
//!      requires safe `pub fn parse_compression_flag(flags_byte: u8) -> bool`
//!      to remain free of Undefined Behavior across all `256` `u8` inputs—even
//!      when `requires: (flags_byte & 1) == flags_byte` is false—catching a
//!      human-authored `unsafe { core::mem::transmute::<u8, bool>(flags_byte) }`
//!      shortcut at `flags_byte = 2` while `NonVacuousPre` guards against
//!      contradictory preconditions.
//!
//! 4. **Journey 4 — Iterative Verified `safe -> unsafe` Optimization**:
//!    - [`checksum_frame_safe`] and [`checksum_frame_fast`]: `checksum_frame_fast`
//!      replaces `checksum_frame_safe`'s four-iteration `while i < 4` loop and
//!      eight per-byte array bounds checks with a single `unsafe`
//!      `core::mem::transmute::<[u8; 8], [u16; 4]>(*frame)` word load and
//!      lane byte-swap. `Specs/WireframeDemo/checksum_frame_fast.lean` freezes
//!      `Mir.WireframeDemo.checksum_frame_safe.body` as the behavioral
//!      specification (`StatefulEquivItemSpec` / `StatefulEquivVerificationResult`:
//!      `RefinesStatefulMir` + `TotalClaim.holds`), rejecting an endianness-buggy
//!      first iteration in seconds via `--item checksum_frame_fast` and
//!      certifying full behavioral equivalence across all `2^64` 8-byte frames.

#![no_std]

use anneal_spec::*;

/// Protocol version byte for v1 wire frames.
pub const WIRE_VERSION_V1: u8 = 1;

/// Returns the active wire-frame protocol version (`1`).
///
/// Verified automatically by `Verify.WireframeDemo.wire_protocol_version`'s
/// generated `defaultProof` instance without authored `Specs` or `Proof` files.
pub const fn wire_protocol_version() -> u8 {
    WIRE_VERSION_V1
}

/// Pure specification model predicate bounding valid frame payloads to `1024`
/// bytes.
#[anneal_spec::model]
pub const fn is_valid_payload_len(len: u16) -> bool {
    len <= 1024
}

/// Bounded read cursor over a wire-frame buffer whose `offset` never exceeds
/// `limit`.
#[anneal_spec::invariant(self.offset <= self.limit)]
#[repr(C)]
pub struct FrameCursor {
    /// Current byte position within the frame window.
    pub offset: u16,
    /// End byte offset of the frame window (`offset <= limit`).
    pub limit: u16,
}

/// Computes the total byte length of a wire frame from bounded `header_len` and
/// `payload_len` components.
#[anneal_spec::spec(
    requires: header_len <= 16 && payload_len <= 1024,
    ensures: |ref ret| *ret == header_len + payload_len,
)]
pub fn frame_total_len(header_len: u16, payload_len: u16) -> u16 {
    header_len + payload_len
}

/// Advances `cursor.offset` by `step` bytes when `step <= cursor.limit - cursor.offset`,
/// preserving `cursor.offset <= cursor.limit` and returning whether the cursor
/// advanced.
pub fn advance_cursor(cursor: &mut FrameCursor, step: u16) -> bool {
    let remaining = cursor.limit - cursor.offset;
    if step <= remaining {
        cursor.offset = cursor.offset + step;
        true
    } else {
        false
    }
}

/// Four-byte `#[repr(C)]` wire header decoded from network frame prefixes.
///
/// Because `compressed` has type `bool` (scalar `validRange = 0..=1`),
/// transmuting unvalidated bytes with `raw[1] >= 2` into `WireHeader` triggers
/// immediate bit-validity Undefined Behavior in Rust and `ITree.fail .ub` in
/// Anneal's `V2026_06_01` MIR semantics.
#[repr(C)]
pub struct WireHeader {
    /// Protocol version (`1` for v1 frames).
    pub version: u8,
    /// Compression flag (`0` = uncompressed, `1` = compressed; `2..=255` = UB).
    pub compressed: bool,
    /// Native-endian 16-bit payload length (`<= 1024` for valid frames).
    pub payload_len: u16,
}

/// Decodes and validates a 4-byte wire header, returning `payload_len` for
/// well-formed v1 headers (`<= 1024`) and `0` for malformed inputs.
///
/// Guarding `raw[1] > 1` before `core::mem::transmute::<[u8; 4], WireHeader>`
/// repairs the bit-validity Undefined Behavior refuted in Journey 2.
pub fn decode_wire_header(raw: [u8; 4]) -> u16 {
    if raw[0] != 1 {
        return 0;
    }
    if raw[1] > 1 {
        return 0;
    }
    let hdr: WireHeader = unsafe { core::mem::transmute::<[u8; 4], WireHeader>(raw) };
    if hdr.payload_len > 1024 {
        return 0;
    }
    hdr.payload_len
}

/// Clamps `requested` to at most `max_window` bytes (`max_window <= 1024`).
///
/// Used in Journey 3A to demonstrate agent implementation authoring under
/// `cargo anneal lock-specs --allow-impl-edit clamp_payload_window` and
/// `cargo anneal agent-verify`.
#[anneal_spec::spec(
    requires: requested <= 65535 && max_window <= 1024,
    ensures: |ref ret| *ret <= max_window && *ret <= requested && (*ret == requested || *ret == max_window),
)]
pub fn clamp_payload_window(requested: u16, max_window: u16) -> u16 {
    if requested <= max_window {
        requested
    } else {
        max_window
    }
}

/// Extracts bit `0` of `flags_byte` as the frame compression flag.
///
/// Used in Journey 3B to demonstrate agent code review via `refineSafeSpec`
/// (`MirContractHoldsWithSafety`): because `parse_compression_flag` is a safe
/// `pub fn`, it must remain UB-free across all `256` `u8` inputs even outside
/// `requires: (flags_byte & 1) == flags_byte`, rejecting an unguarded
/// `unsafe { core::mem::transmute::<u8, bool>(flags_byte) }` shortcut.
#[anneal_spec::spec(
    requires: (flags_byte & 1) == flags_byte,
    ensures: |ref ret| *ret == (flags_byte == 1),
)]
pub fn parse_compression_flag(flags_byte: u8) -> bool {
    (flags_byte & 1) != 0
}

/// Reference safe Rust implementation summing four big-endian 16-bit words from
/// an 8-byte frame via a `while i < 4` loop with per-byte bounds checks.
///
/// Serves as the frozen behavioral specification (`specBody`) for
/// [`checksum_frame_fast`] in Journey 4 (`StatefulEquivItemSpec`).
pub fn checksum_frame_safe(frame: &[u8; 8]) -> u32 {
    let mut i: usize = 0;
    let mut acc: u32 = 0;
    while i < 4 {
        let hi = frame[i * 2] as u32;
        let lo = frame[i * 2 + 1] as u32;
        acc = acc + ((hi << 8) | lo);
        i = i + 1;
    }
    acc
}

/// Optimized `unsafe` word-lane implementation of [`checksum_frame_safe`].
///
/// Reinterprets `*frame` as `[u16; 4]` in a single `transmute` and byte-swaps
/// each little-endian `u16` lane into big-endian order before accumulating into
/// `u32`. Verified in `Proof/WireframeDemo/checksum_frame_fast.lean` to satisfy
/// `StatefulEquivVerificationResult` (`RefinesStatefulMir` against
/// `Mir.WireframeDemo.checksum_frame_safe.body` plus `TotalClaim.holds`) across
/// all `2^64` 8-byte frames.
pub fn checksum_frame_fast(frame: &[u8; 8]) -> u32 {
    let words: [u16; 4] = unsafe { core::mem::transmute::<[u8; 8], [u16; 4]>(*frame) };
    let w0 = (((words[0] & 0x00ff) << 8) | (words[0] >> 8)) as u32;
    let w1 = (((words[1] & 0x00ff) << 8) | (words[1] >> 8)) as u32;
    let w2 = (((words[2] & 0x00ff) << 8) | (words[2] >> 8)) as u32;
    let w3 = (((words[3] & 0x00ff) << 8) | (words[3] >> 8)) as u32;
    w0 + w1 + w2 + w3
}
