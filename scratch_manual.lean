import LeanMiriSpec.Correspondence.CopyLM4_2
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

theorem manual_divergence_uninit
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {srcIdx dstIdx : Local} {countOp : MirAst.Operand} {span : String}
    {srcMut dstMut : Mutability} {pointeeTy countTy : Ty}
    {ptId : Miri.MIR.TyId} {elemBytes elemAlign : Nat}
    {srcPtr dstPtr : ProvenancePtr} {countSc : MirAst.ScalarInt}
    {e_s e_d : AllocMapEntry} {decl_s decl_d : LocalDecl} {srcBytes dstBytes : Nat}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp),
        span⟩)
    (hsrcDecl : get? body.localDecls srcIdx = some srcDecl)
    (hsrcTy : srcDecl.ty.kind = .rawPtr srcMut pointeeTy.kind)
    (hsrcImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf srcIdx)
    (hdstDecl : get? body.localDecls dstIdx = some dstDecl)
    (hdstTy : dstDecl.ty.kind = .rawPtr dstMut pointeeTy.kind)
    (hdstImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx)
    (hcountInt : IsIntegralTy countTy .usize)
    (hcountOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf countOp countTy)
    (hpt : CopyPointee body.layouts pointeeTy.kind ptId elemBytes elemAlign)
    (hsrc_val : get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)))
    (hdst_val : get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)))
    (hoff0_s : srcPtr.offsetBytes = 0)
    (hoff0_d : dstPtr.offsetBytes = 0)
    (hcnt_pre : WriteBytesScalarPreVal s.frame.locals countOp countSc)
    (hcount_pos : 0 < countSc.bits * elemBytes)
    (hcount_max : countSc.bits * elemBytes ≤ isizeMaxBytes)
    (he_s : e_s ∈ allocMap) (het_s : e_s.tag = srcPtr.tag)
    (he_d : e_d ∈ allocMap) (het_d : e_d.tag = dstPtr.tag)
    (hdecl_s : get? body.localDecls e_s.localIdx = some decl_s)
    (hdecl_d : get? body.localDecls e_d.localIdx = some decl_d)
    (hcompat : CopyTargetCompatible decl_s decl_d pointeeTy.kind)
    (hsrcBytes : rigidTyByteSize body.layouts decl_s.ty = some srcBytes)
    (hdstBytes : rigidTyByteSize body.layouts decl_d.ty = some dstBytes)
    (hsrc_in_bounds : srcPtr.offsetBytes + countSc.bits * elemBytes ≤ srcBytes)
    (hdst_in_bounds : dstPtr.offsetBytes + countSc.bits * elemBytes ≤ dstBytes)
    (huninit_s : get? s.frame.locals e_s.localIdx = some .uninit)
    (hdst_live : get? s.frame.locals e_d.localIdx ≠ some .dead) :
    stepMirFn body s = MirStepNode.fail .ub := by
  have hanneal_step : stepMirFn body s =
      evalCopyNonOverlapping s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
        body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s sorry hphase]
    simp only [hbb, hstmt]; rfl
  sorry
