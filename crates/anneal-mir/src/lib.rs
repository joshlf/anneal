//! Anneal MIR abstract syntax and lowering crate.

pub mod ir;
pub mod lower;
pub mod rustc_v2026_06_01;

pub use ir::*;
pub use lower::*;
pub use rustc_v2026_06_01::{
    ABORTING_PANIC_DEF_PATHS_V2026_06_01, RUST_INTRINSIC_DEF_PATHS_V2026_06_01,
    UNREACHABLE_DEF_PATHS_V2026_06_01, UNWINDING_PANIC_DEF_PATHS_V2026_06_01,
    classify_call_target_v2026_06_01, classify_linked_call_target_v2026_06_01,
    lower_call_target_v2026_06_01, lower_intrinsic_kind_v2026_06_01,
};
