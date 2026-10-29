//! Binary entry point for `anneal-rustc-capture` when invoked by Cargo via
//! `RUSTC_WORKSPACE_WRAPPER` or `RUSTC_WRAPPER`.

#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_type_ir;

pub use anneal_rustc_capture::{lean_emit, manifest};

pub mod rustc_2026_06_01;

fn main() {
    let code = rustc_2026_06_01::driver::run_from_env_args();
    std::process::exit(code);
}
