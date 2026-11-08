//! Integration tests for MIR cast lowering and MiniRust provenance correspondence.

use anneal_mir::ir::{CastKind, IntTy, Mutability, Operand, PointerValue, Provenance, Ty, UintTy};
use anneal_mir::lower::{
    CastEvalError, ExposedProvenanceTracker, LoweredCast, eval_int_to_ptr, eval_ptr_to_int,
    lower_cast_rvalue,
};

#[test]
fn test_end_to_end_ptr_to_int_to_ptr() {
    let mut tracker = ExposedProvenanceTracker::new();
    let prov = Provenance { alloc_id: 10, tag: 456 };
    let ptr = PointerValue::with_provenance(0xbeef_0000, prov.alloc_id, prov.tag);

    let ptr_ty = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Mut);
    let usize_ty = Ty::Uint(UintTy::Usize);

    // Lowering checks
    let op = Operand::Constant(anneal_mir::ir::Constant::Ptr(ptr, ptr_ty.clone()));
    let lowered_p2i = lower_cast_rvalue(CastKind::PointerExposeProvenance, &op, &ptr_ty, &usize_ty)
        .expect("lower ptr to int");
    assert!(matches!(lowered_p2i, LoweredCast::PtrToInt { .. }));

    // Dynamic evaluation
    let addr = eval_ptr_to_int(ptr, &usize_ty, &mut tracker).expect("eval ptr to int");
    assert_eq!(addr, 0xbeef_0000);
    assert!(tracker.is_exposed(&prov));

    // Lowering int to ptr
    let int_op = Operand::Constant(anneal_mir::ir::Constant::Int(addr, usize_ty.clone()));
    let lowered_i2p = lower_cast_rvalue(CastKind::PointerWithExposedProvenance, &int_op, &usize_ty, &ptr_ty)
        .expect("lower int to ptr");
    assert!(matches!(lowered_i2p, LoweredCast::IntToPtr { .. }));

    // Dynamic reconstruction
    let reconstituted = eval_int_to_ptr(addr, &ptr_ty, &tracker, Some(prov))
        .expect("eval int to ptr with exposed provenance");
    assert_eq!(reconstituted.addr, ptr.addr);
    assert_eq!(reconstituted.provenance, ptr.provenance);
}

#[test]
fn test_unexposed_provenance_rejected() {
    let tracker = ExposedProvenanceTracker::new();
    let unexposed = Provenance { alloc_id: 999, tag: 888 };
    let ptr_ty = Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Not);

    let err = eval_int_to_ptr(0x1234_5678, &ptr_ty, &tracker, Some(unexposed))
        .expect_err("unexposed provenance must be rejected");
    assert_eq!(err, CastEvalError::UnexposedProvenance(unexposed));
}

#[test]
fn test_wildcard_provenance_allowed() {
    let tracker = ExposedProvenanceTracker::new();
    let ptr_ty = Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Not);

    let ptr = eval_int_to_ptr(0x1234_5678, &ptr_ty, &tracker, None)
        .expect("wildcard / None provenance is always valid");
    assert_eq!(ptr.addr, 0x1234_5678);
    assert_eq!(ptr.provenance, None);
}
