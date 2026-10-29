//! Trusted `rustc` capture serializer (`trusted/rustc-capture`).
//!
//! This crate sits inside `trusted/` and may not depend on any workspace crate
//! outside `trusted/`. It defines the `CaptureManifest` and
//! `UnitCaptureManifest` handshakes consumed by `trusted/audit/` and
//! `crates/cargo-anneal`, and hosts the version-scoped `rustc_driver` MIR,
//! layout, and specification attribute serializer (#99, #103).

pub mod lean_emit;
pub mod manifest;

pub use manifest::{
    ANNEAL_CAPTURE_DIR_ENV, ANNEAL_CAPTURE_FILTER_ENV, CaptureManifest, CapturedItemKind,
    CapturedTarget, MIR_DIALECT_V2026_06_01, RUSTC_COMMIT_SHA, RUSTC_VERSION_STRING,
    UnitCaptureManifest, UnitTargetRecord, sha256_hex,
};
