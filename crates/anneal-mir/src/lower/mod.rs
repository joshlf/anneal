//! MIR lowering and dynamic evaluation module.

pub mod cast;
pub mod rvalue;

pub use cast::{
    CastEvalError, CastLowerError, CastOp, ExposedProvenanceTracker, LoweredCast, TransmutePolicy,
    TransmuteValue, eval_int_to_int, eval_int_to_ptr, eval_int_to_ptr_with_ptr_width,
    eval_ptr_to_int, eval_ptr_to_int_with_ptr_width, eval_transmute, lower_cast_rvalue,
    lower_cast_rvalue_with_ptr_width, lower_int_to_ptr, lower_ptr_to_int, lower_transmute,
};
pub use rvalue::{
    LoweredBasicBlock, LoweredBody, LoweredRvalue, LoweredStatement, MirValue, RvalueEvalError,
    RvalueLowerError, RvalueValue, eval_aggregate, eval_binop, eval_checked_binop, eval_constant,
    eval_lowered_cast, eval_lowered_rvalue, eval_unop, lower_body, lower_body_with_policy,
    lower_rvalue, lower_rvalue_with_policy, lower_statement, lower_statement_with_policy,
    resolve_operand_ty, resolve_place_ty,
};
