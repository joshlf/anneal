//! Untrusted CLI entry point (`cargo-anneal`).
//!
//! All semantic extraction is performed by `anneal-rustc-capture` in
//! `trusted/rustc-capture/`, and final proof acceptance is gated by
//! `trusted/audit/` (#103 §2, §5).

use anneal_rustc_capture::CaptureManifest;

fn main() {
    let _schema = CaptureManifest::SCHEMA_VERSION;
}
