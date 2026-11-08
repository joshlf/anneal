//! MIR lowering module.

pub mod cast;
pub use cast::{
    CastEvalError, CastLowerError, ExposedProvenanceTracker, LoweredCast, eval_int_to_ptr,
    eval_ptr_to_int, lower_cast_rvalue, lower_int_to_ptr, lower_ptr_to_int,
};
