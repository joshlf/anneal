//! Trusted `rustc` capture serializer (`trusted/rustc-capture`).
//!
//! This crate sits inside `trusted/` and may not depend on any workspace crate
//! outside `trusted/`. It defines the `CaptureManifest` handshake consumed by
//! `trusted/audit/` and will host the mechanical `rustc_driver` MIR and
//! attribute serializer (#99, #103).

/// A single captured item and its generated `Mir/<Item>.lean` module digest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapturedTarget {
    /// Canonical item identifier (`DefId` path) within the crate.
    pub def_id: String,
    /// Relative path to the read-only generated `Mir/<Item>.lean` module.
    pub mir_module_path: String,
    /// SHA-256 hex digest of the generated `Mir/<Item>.lean` file.
    pub mir_module_sha256: String,
}

/// Cryptographic handshake written by `anneal-rustc-capture` and verified by
/// `trusted/audit/` before accepting compiled `.olean` proofs (#103 §5).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CaptureManifest {
    /// Schema version of the capture manifest.
    pub schema: u32,
    /// True only after `rustc` completes compilation of the crate (including
    /// post-monomorphization checks) with zero errors (#99 §3).
    pub compilation_succeeded: bool,
    /// Relative path and SHA-256 hex digest of every `.rs` input file.
    pub rust_sources: Vec<(String, String)>,
    /// Verification targets extracted for this compilation unit.
    pub targets: Vec<CapturedTarget>,
}

impl CaptureManifest {
    /// Current manifest schema version.
    pub const SCHEMA_VERSION: u32 = 1;
}
