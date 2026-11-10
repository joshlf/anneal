//! MIR lowering and dynamic evaluation module.

pub mod cast;
pub mod cfg;
pub mod rvalue;

pub use cast::{
    AbstractByte, CastEvalError, CastLowerError, CastOp, ExposedProvenanceTracker, LoweredCast,
    ProvenanceFrag, TransmutePolicy, TransmuteValue, eval_char_to_int, eval_int_to_int,
    eval_int_to_ptr, eval_int_to_ptr_with_ptr_width, eval_ptr_to_int,
    eval_ptr_to_int_with_ptr_width, eval_transmute, is_subtype_compatible, lower_cast_rvalue,
    lower_cast_rvalue_with_ptr_width, lower_char_to_int, lower_int_to_ptr, lower_ptr_to_int,
    lower_transmute,
};
pub use cfg::{
    CallHandler, CallOutcome, CfgEvalError, CfgEvalOutcome, LoweredTerminator, PanicMessage,
    TerminatorLowerError, eval_cfg_in_state, eval_lowered_body_cfg,
    eval_lowered_body_cfg_with_calls, lower_terminator,
};
pub use rvalue::{
    FieldSlot, LocalFrame, LocalSlotState, LoweredBasicBlock, LoweredBody, LoweredRvalue,
    LoweredStatement, MirValue, PartialAggregate, RvalueEvalError, RvalueLowerError, RvalueValue,
    StatementEvalState, eval_aggregate, eval_binop, eval_checked_binop, eval_constant,
    eval_lowered_block, eval_lowered_cast, eval_lowered_rvalue, eval_lowered_rvalue_in_state,
    eval_lowered_statement, eval_nullary_op, eval_place_read, eval_place_write, eval_unop,
    lower_body, lower_body_with_policy, lower_rvalue, lower_rvalue_with_policy, lower_statement,
    lower_statement_with_policy, resolve_offset_of, resolve_operand_ty, resolve_place_ty,
};
