import LeanMiriSpec.Correspondence.Simulation

namespace LeanMiriSpec.Correspondence
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

theorem readAssertCondition_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[topFrame])
    (hframe : FrameRel body m.machine s.frame topFrame)
    (_hbor : s.memory.borrows = .nil) (_hcaller : s.memory.callerLocals = .nil)
    (cond : Operand) (condTy : Ty) (hbool : condTy.kind = .bool)
    (hop : WellTypedScalarOperand body topFrame cond condTy) :
    let m_res := (annealTerminatorHooks body.localDecls body.layouts).readAssertCondition () (translateOperand cond) m
    let a_res := evalOperand s.frame.locals cond .nil s.memory.globals body.layouts .nil
    (∃ sc m' locals', a_res = .ok (.scalar sc) locals' ∧ m_res = (m', .ok (sc.bits ≠ 0)) ∧ (sc.bits = 0 ∨ sc.bits = 1) ∧ ∃ tf', m'.stack.frames = #[tf']) ∨
    (a_res = .ub ∧ ∃ m' msg, m_res = (m', .error (.undefinedBehavior msg))) := by
  intro m_res a_res
  have hop_sim := evalOperand_scalar_simulation hframes hframe hop s.memory.globals none
  dsimp only [m_res, a_res]
  generalize ha_eval : evalOperand s.frame.locals cond .nil s.memory.globals body.layouts .nil = aRes at hop_sim
  generalize hm_eval : (annealEvalOperand body.localDecls body.layouts (translateOperand cond) none >>= annealReadImmediate) m = mRes at hop_sim
  cases hop_sim with
  | ok val locals' tf' imm hf_rel himm_rel himm_loc htf_eq =>
    have himm := ImmediateRel.of_primitive_scalar himm_rel (Or.inl hbool)
    rcases himm with ⟨sc, msc, hval_eq, himm_eq, hsc_rel, hsc_sz, hsc_bool, _⟩
    subst hval_eq himm_eq
    left
    refine ⟨sc, { stack := ⟨#[tf']⟩, machine := m.machine }, locals', rfl, ?_, (hsc_bool hbool).2, ⟨tf', rfl⟩⟩
    dsimp only [annealTerminatorHooks, Miri.Interpreter.TerminatorHooks.readAssertCondition]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_assoc_apply]
    rw [EStateM.bind_eq_ok hm_eval]
    rcases hsc_bool hbool with ⟨hsc_sz_eq, hsc_bits⟩
    have hmsc_sz : msc.size = Miri.ABI.Size.ofBytes 1 := by
      rw [hsc_rel.size_eq, hsc_sz_eq]
      rfl
    have hmsc_data_eq : msc.data = sc.bits := hsc_rel.data_eq
    rcases msc with ⟨msc_data, msc_size⟩
    subst hmsc_sz
    rcases hsc_bits with h0 | h1
    · rw [h0] at hmsc_data_eq ⊢
      subst hmsc_data_eq
      dsimp [Miri.Interpreter.Immediate.toScalar, bind, EStateM.bind, pure, EStateM.pure, Miri.Memory.Scalar.toBool, Miri.Memory.Scalar.fromScalarInt, Miri.Memory.Scalar.toUInt8, Except.bind, Miri.Memory.Scalar.toUInt, Miri.Memory.Scalar.toBits, Miri.Memory.ScalarInt.toBits, Miri.Memory.Scalar.toScalarInt, Except.mapError, Miri.Memory.Scalar.tryToScalarInt, Miri.ABI.Size.bytes, Miri.ABI.Size.ofBytes]
      rfl
    · rw [h1] at hmsc_data_eq ⊢
      subst hmsc_data_eq
      dsimp [Miri.Interpreter.Immediate.toScalar, bind, EStateM.bind, pure, EStateM.pure, Miri.Memory.Scalar.toBool, Miri.Memory.Scalar.fromScalarInt, Miri.Memory.Scalar.toUInt8, Except.bind, Miri.Memory.Scalar.toUInt, Miri.Memory.Scalar.toBits, Miri.Memory.ScalarInt.toBits, Miri.Memory.Scalar.toScalarInt, Except.mapError, Miri.Memory.Scalar.tryToScalarInt, Miri.ABI.Size.bytes, Miri.ABI.Size.ofBytes]
      rfl
  | ub m' msg =>
    right
    refine ⟨rfl, m', msg, ?_⟩
    dsimp only [annealTerminatorHooks, Miri.Interpreter.TerminatorHooks.readAssertCondition]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_assoc_apply]
    rw [EStateM.bind_eq_error hm_eval]

theorem readAssertCondition_to_8 {body : CapturedMir} {cond : Operand} {m : AnnealStepState} {m' : _} {res : _}
    (h : (annealTerminatorHooks body.localDecls body.layouts).readAssertCondition () (translateOperand cond) m = (m', res)) :
    (annealTerminatorHooks body.localDecls body.layouts).8 () (translateOperand cond) m = (m', res) :=
  h

theorem assert_cond_beq (expected : Bool) (bits : Nat) (hbool : bits = 0 ∨ bits = 1) :
    ((expected == decide (bits ≠ 0)) = true) → bits.beq (match expected with | true => 1 | false => 0) = true := by
  intro h_match
  rcases hbool with h0 | h1
  · revert h_match; rw [h0]; cases expected <;> decide
  · revert h_match; rw [h1]; cases expected <;> decide

theorem assert_cond_beq_false (expected : Bool) (bits : Nat) (hbool : bits = 0 ∨ bits = 1) :
    ((expected == decide (bits ≠ 0)) = false) → bits.beq (match expected with | true => 1 | false => 0) = false := by
  intro h_match
  rcases hbool with h0 | h1
  · revert h_match; rw [h0]; cases expected <;> decide
  · revert h_match; rw [h1]; cases expected <;> decide

theorem step_terminator_assert_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[topFrame])
    (hframe : FrameRel body m.machine s.frame topFrame)
    (hbor : s.memory.borrows = .nil) (hcaller : s.memory.callerLocals = .nil)
    (cond : Operand) (condTy : Ty) (expected : Bool) (target : BasicBlockIdx)
    (hbool : condTy.kind = .bool)
    (hop : WellTypedScalarOperand body topFrame cond condTy)
    (term : Terminator) (hterm : term.kind = .assert cond expected target .unreachable) :
    let m_res := Miri.Interpreter.ControlFlow.evalTerminator (annealTerminatorHooks body.localDecls body.layouts) () (translateTerminator term) m
    let a_res := evalTerminator s term (some body)
    (a_res = MirStepNode.fail .ub ∧ ∃ m' msg', m_res = (m', .error (.undefinedBehavior msg'))) ∨
    (∃ m' locals', a_res = MirStepNode.step { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } } ∧ m_res = (m', .ok ())) := by
  intro m_res a_res
  rcases term with ⟨srcInfo, kind⟩
  dsimp only at hterm
  subst hterm
  dsimp only [m_res, a_res, evalTerminator]
  rw [hbor, hcaller]
  dsimp only [Miri.Interpreter.ControlFlow.evalTerminator, translateTerminator, translateTerminatorKind]
  have hread := readAssertCondition_simulation hframes hframe hbor hcaller cond condTy hbool hop
  rcases hread with ⟨sc, m', locals', h_a, h_m, hsc_bool, tf', htf'⟩ | ⟨h_a, m', msg, h_m⟩
  · have h_m' := readAssertCondition_to_8 h_m
    simp only [h_m']
    dsimp only [Id.run, bind, Except.bind, EStateM.bind, pure, EStateM.pure, Miri.Interpreter.TerminatorHooks.ignoreOptionalOverflowChecks, Miri.Interpreter.ControlFlow.isOptionalOverflowCheck]
    by_cases h_match : (expected == decide (sc.bits ≠ 0)) = true
    · right
      have h_goto : ∃ m_new, Miri.Interpreter.ControlFlow.goToBlock target m' = (m_new, Except.ok ()) := by
        dsimp only [Miri.Interpreter.ControlFlow.goToBlock, Miri.Interpreter.ControlFlow.setLocation]
        simp only [Miri.Interpreter.Stack.currentFrame?, htf']
        exact ⟨_, rfl⟩
      rcases h_goto with ⟨m_new, hm_new⟩
      refine ⟨m_new, locals', ?_, ?_⟩
      · rw [h_a]
        dsimp only
        split
        · rfl
        · next h_contra => 
          rcases hsc_bool with h0 | h1
          · revert h_match h_contra; simp only [h0]; intros; cases expected <;> contradiction
          · revert h_match h_contra; simp only [h1]; intros; cases expected <;> contradiction
      · simp only [Bool.and_false, Bool.false_or, h_match]
        simp only [ite_true]
        exact hm_new
    · left
      refine ⟨?_, m', "assert panic", ?_⟩
      · rw [h_a]
        dsimp only
        have h_if : (expected == decide (sc.bits ≠ 0)) = false := by
          revert h_match; cases (expected == decide (sc.bits ≠ 0)) <;> decide
        split
        · next h_contra =>
          rcases hsc_bool with h0 | h1
          · revert h_if h_contra; simp only [h0]; intros; cases expected <;> contradiction
          · revert h_if h_contra; simp only [h1]; intros; cases expected <;> contradiction
        · rfl
      · dsimp only [annealTerminatorHooks]
        simp only [Bool.and_false, Bool.false_or]
        have h_if : (expected == decide (sc.bits ≠ 0)) = false := by
          revert h_match; cases (expected == decide (sc.bits ≠ 0)) <;> decide
        simp only [h_if]
        rfl
  · left
    refine ⟨?_, m', msg, ?_⟩
    · rw [h_a]
    · have h_m' := readAssertCondition_to_8 h_m
      simp only [h_m']
      rfl

theorem array_get_some_exists {α} (a : Array α) (i : Nat) (v : α) (h : a[i]? = some v) : ∃ (hlt : i < a.size), a[i]'hlt = v := by
  revert h
  simp only [getElem?_def]
  split
  · intro h; exact ⟨‹_›, by injection h⟩
  · intro hcontra; injection hcontra

theorem evalPlaceProject_scalarPair_field0_field1_simulation
    {body : CapturedMir} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m : AnnealStepState} {idx : Local} {decl : LocalDecl}
    (hframes : m.stack.frames = #[topFrame])
    (hframe : FrameRel body m.machine af topFrame)
    (globals : List CapturedAllocation)
    (known : Option Miri.Interpreter.LocalLayout)
    (hdecl : get? body.localDecls idx = some decl)
    (sc0 sc1 : ScalarInt) (msc0 msc1 : Miri.Memory.ScalarInt)
    (hls : get? af.locals idx = some (LocalSlot.init (.aggregate 0 [.scalar sc0, .scalar sc1])))
    (hloc : ∃ l, topFrame.locals[idx]? = some ({ value := .live (.immediate (.scalarPair (.fromScalarInt msc0) (.fromScalarInt msc1))), layout := some l } : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) ∧ l = translateTy decl.ty body.layouts)
    (fidx : Nat) (fty : Ty) (hfidx : (fidx = 0 ∧ sc0.sizeBytes ≠ 0) ∨ (fidx = 1 ∧ sc1.sizeBytes ≠ 0))
    (hfty : fty = if fidx = 0 then { kind := (match decl.ty.kind with | .tuple (t::_) => t | _ => .tuple []), layoutIdx := 0 } else { kind := .bool, layoutIdx := 0 }) :
    let op := Operand.copy ⟨idx, [ProjectionElem.field fidx fty]⟩
    (evalOperand af.locals op [] globals body.layouts) = .ok (.scalar (if fidx = 0 then sc0 else sc1)) af.locals ∧
    ∃ topFrame',
      topFrame' = { topFrame with locals := topFrame'.locals } ∧
      (∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame' j) ∧
      FrameRel body m.machine af topFrame' ∧
      ((annealEvalOperand body.localDecls body.layouts (translateOperand op) known >>= annealReadImmediate) m) = 
      EStateM.Result.ok { imm := .scalar (.fromScalarInt (if fidx = 0 then msc0 else msc1)), layout := ⟨encodeTyId fty, (translateTy decl.ty body.layouts).layout⟩ } 
      { m with stack := ⟨#[topFrame']⟩ } := by
  intro op
  obtain ⟨l, hloc_eq, h_l_eq⟩ := hloc
  subst h_l_eq
  obtain ⟨hlt, h_get⟩ := array_get_some_exists _ _ _ hloc_eq
  have hcache : ∀ l, (topFrame.locals[idx]'hlt).layout = some l → l = translateTy decl.ty body.layouts := by
    intro l' hl'
    rw [h_get] at hl'
    dsimp only at hl'
    cases hl'
    rfl
  constructor
  · dsimp only [op, evalOperand]
    rw [hls]
    dsimp only [readProjectedValue, List.brecOn, List.below]
    rcases hfidx with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · rfl
    · rfl
  · let topFrame' := cacheFrameLocalLayout topFrame idx hlt (translateTy decl.ty body.layouts)
    refine ⟨topFrame', ?_, ?_, ?_, ?_⟩
    · rfl
    · intro j hj
      exact hj.cache_layout hlt _
    · exact hframe.cache_local_layout hdecl hlt
    · have hres := annealResolveAndCacheLocalLayout_eq (known := known) hframes hlt hdecl hcache
      have hget_c := cacheFrameLocalLayout_getLocal topFrame hlt (translateTy decl.ty body.layouts)
      rw [h_get] at hget_c
      have hgop := frame_getLocalOperand_live _ hget_c
      have hm_op : annealEvalOperand body.localDecls body.layouts (translateOperand op) known m =
          .ok ⟨.immediate (.scalar (.fromScalarInt (if fidx = 0 then msc0 else msc1))), ⟨encodeTyId fty, (translateTy decl.ty body.layouts).layout⟩⟩
            { m with stack := ⟨#[topFrame']⟩ } := by
        with_unfolding_all
          unfold annealEvalOperand
          rcases hfidx with ⟨rfl, _⟩ | ⟨rfl, _⟩
          · simp only [op, translateOperand, translatePlace, translateProjectionElem, List.map, encodeTyId, Bool.false_eq_true, ↓reduceIte, get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind, Pure.pure, stack_currentFrame?_singleton m.stack topFrame hframes, Option.isNone_some, hres, hgop, beq_self_eq_true]
            rfl
          · simp only [op, translateOperand, translatePlace, translateProjectionElem, List.map, encodeTyId, Bool.false_eq_true, ↓reduceIte, get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind, Pure.pure, stack_currentFrame?_singleton m.stack topFrame hframes, Option.isNone_some, hres, hgop]
            rfl
      rw [EStateM.bind_eq_ok hm_op]
      unfold annealReadImmediate
      rfl



theorem evalCheckedAdd_simulation
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (hsz_eq : sc₁.sizeBytes = sc₂.sizeBytes)
    (kind : Miri.MIR.IntegerKind)
    (locals : List LocalSlot) (mem : Memory) :
    IntegerBinOpResultRel locals mem
      (evalScalarBinOp .addWithOverflow sc₁ sc₂ locals mem kind.signed)
      (Miri.Interpreter.IntegerOps.binary .AddWithOverflow
        ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
        ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩) := by
  have harith : IsArithmeticOrCmpBinOp .addWithOverflow := by
    dsimp [IsArithmeticOrCmpBinOp]
    right; right; right; right; right; right; left; rfl
  have hop : (translateBinOp .addWithOverflow : Option Miri.MIR.BinOp) = some .AddWithOverflow := rfl
  exact evalBinOp_arithmetic_simulation harith hop hrel₁ hrel₂ hsz_eq kind locals mem

theorem evalCheckedSub_simulation
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (hsz_eq : sc₁.sizeBytes = sc₂.sizeBytes)
    (kind : Miri.MIR.IntegerKind)
    (locals : List LocalSlot) (mem : Memory) :
    IntegerBinOpResultRel locals mem
      (evalScalarBinOp .subWithOverflow sc₁ sc₂ locals mem kind.signed)
      (Miri.Interpreter.IntegerOps.binary .SubWithOverflow
        ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
        ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩) := by
  have harith : IsArithmeticOrCmpBinOp .subWithOverflow := by
    dsimp [IsArithmeticOrCmpBinOp]
    right; right; right; right; right; right; right; left; rfl
  have hop : (translateBinOp .subWithOverflow : Option Miri.MIR.BinOp) = some .SubWithOverflow := rfl
  exact evalBinOp_arithmetic_simulation harith hop hrel₁ hrel₂ hsz_eq kind locals mem

theorem evalCheckedMul_simulation
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (hsz_eq : sc₁.sizeBytes = sc₂.sizeBytes)
    (kind : Miri.MIR.IntegerKind)
    (locals : List LocalSlot) (mem : Memory) :
    IntegerBinOpResultRel locals mem
      (evalScalarBinOp .mulWithOverflow sc₁ sc₂ locals mem kind.signed)
      (Miri.Interpreter.IntegerOps.binary .MulWithOverflow
        ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
        ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩) := by
  have harith : IsArithmeticOrCmpBinOp .mulWithOverflow := by
    dsimp [IsArithmeticOrCmpBinOp]
    right; right; right; right; right; right; right; right; left; rfl
  have hop : (translateBinOp .mulWithOverflow : Option Miri.MIR.BinOp) = some .MulWithOverflow := rfl
  exact evalBinOp_arithmetic_simulation harith hop hrel₁ hrel₂ hsz_eq kind locals mem




theorem checked_binop_then_assert_simulation
    {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    {s0 : MachineState} {m0 : AnnealStepState}
    {topFrame0 : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (_hframes0 : m0.stack.frames = #[topFrame0])
    (hstate0 : StateRel body s0 m0)
    (hloc0 : ValidFrameLocation body s0.frame)
    (himm0 : NonAddrTakenImmediate body nonAddrTaken m0)
    (hbody : WellTypedBody body nonAddrTaken)
    (op : BinOp) (_hop : op = .addWithOverflow ∨ op = .subWithOverflow ∨ op = .mulWithOverflow)
    (tmp dest : Local) (a b : Operand) (target : BasicBlockIdx)
    (bb0 bb1 : BasicBlockData)
    (_hbb0 : get? body.basicBlocks s0.frame.blockIdx = some bb0)
    (stmt0 : Statement)
    (_hstmt0_get : get? bb0.statements s0.frame.stmtIdx = some stmt0)
    (_hstmt0 : stmt0.kind = .assign ⟨tmp, []⟩ (.binaryOp op a b))
    (_hstmt1 : get? bb0.statements (s0.frame.stmtIdx + 1) = none)
    (_hterm : bb0.terminator.kind = .assert (.copy ⟨tmp, [ProjectionElem.field 1 { kind := .bool, layoutIdx := 0 }]⟩) false target .unreachable)
    (_hbb1 : get? body.basicBlocks target = some bb1)
    (tmpTy : Ty)
    (_hdecl_tmp : get? body.localDecls tmp = some { mutability := .mut, ty := tmpTy, debugName := none })
    (destTy : Ty)
    (_hdecl_dest : get? body.localDecls dest = some { mutability := .mut, ty := destTy, debugName := none })
    (stmt2 : Statement)
    (_hstmt2_get : get? bb1.statements 0 = some stmt2)
    (_hstmt2 : stmt2.kind = .assign ⟨dest, []⟩ (.use (.copy ⟨tmp, [ProjectionElem.field 0 destTy]⟩))) :
    RunRel body nonAddrTaken (runAnnealBounded body 3 s0) (runMiriBounded body 3 m0) :=
  run_wellTypedBody_simulation 3 hbody hstate0 hloc0 himm0


end LeanMiriSpec.Correspondence

