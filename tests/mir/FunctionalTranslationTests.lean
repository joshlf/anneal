import Anneal.FunctionalTranslation

namespace Anneal.FunctionalTranslationTests

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Refinement
open Anneal.Effect
open Anneal.ITree
open Anneal.EffectWP
open Anneal.ITreeWP
open Anneal.Memory
open Anneal.UnsafeObligations
open Anneal.SepLogic
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.FunctionalTranslation

/-!
Kernel-checked verification test suites for `Anneal.FunctionalTranslation` over
`V2026_06_01` `CapturedMir` bodies, exercising all four pillars:

1. **Suite 1 (Pillar 1 + Pillar 2 Diamond Joining Without Path Splitting)**:
   - Spine-preserving symbolic aggregate merging (`SymVal`, `zipSymVal`,
     `denote_zipSymVal`, `zipSymLocals`, `denote_zipSymLocals`).
   - Multi-diamond `CapturedMir` verification (`twoDiamondTupleBody`) constructing
     and projecting a `(u32, u32)` tuple across two sequential `if/else` diamonds
     over symbolic `c1 c2 : Bool` and `x : Nat` (`x < 1000`), verified via
     `TransPlan.branch` without case-splitting on `c1` or `c2`.
2. **Suite 2 (Pillar 2 Symbolic `while`-Loop Total & Coinductive Partial Verification)**:
   - Symbolic `while i < n` arithmetic-accumulation loop (`sumToNLoopBody`) over
     arbitrary `n : Nat` (`n ≤ 1000`), verified for total correctness
     (`TotalVerificationResult` and `MirTerminatesAndNoUB`) via `TransPlan.loop`
     and for partial correctness (`VerificationResult`) via
     `dwlp_mirTree_while_invariant`.
3. **Suite 3 (Pillar 3 `&mut` Lenses, `ActiveTypedMutBorrow`, and `CapturedMir` `&mut` Body)**:
   - `FrameCursor` (`pos : Nat`, `len : Nat`) pure state-update specification
     `FrameCursor.advancePure`, sub-place field lens composition
     (`LawfulMutLens.comp`), sequential update composition (`MutUpdate.seq`), and
     spatial `ActiveTypedMutBorrow` + `AgreeOnFootprint` disjoint-allocation
     framing via `memoryPtrMutLens`.
   - Symbolic verification of `advanceCursorMutMirBody` (`Rvalue.ref (.mut false)`
     + `(*_ptr).0` / `(*_ptr).1` dereference projections + conditional field
     mutation) via `MutRefLocalSpec`, `verifyMutRefLocalTotalByTransPlan`, and
     `statefulOfTotalMutRefLocal`.
4. **Suite 4 (Pillar 4 Program-to-Program Layer 1A Refinement `≤` and `=`)**:
   - Literal Layer 1A `ITree.toPartial` refinement (`≤`), behavioral equality
     (`=`), and `MirTerminatesAndNoUB` between `fastSliceSumBody` (`unsafe`
     unchecked indexing + `BinOp.addUnchecked`) and `safeSliceSumBody` (checked
     `Rvalue.len` bounds `TerminatorKind.assert` + `BinOp.addWithOverflow`
     overflow `TerminatorKind.assert`) over arbitrary symbolic `elems : List Nat`
     and `n ≤ elems.length` via `dwp_mirTree_stateful_while_ranked` and
     `verifyStatefulEquivViaPureModel`.
   - Branch-observation-erased Layer 1A equivalence (`mirObsErasedStatefulTree`
     and `eraseTracePartial`) between `branchlessMulDoubleBody` (`0` `switchInt`
     events) and `branchingSelectDoubleBody` (`1` `switchInt` event) via
     `verifyObsErasedStatefulEquivByTransPlan`.
-/

/-! ## Shared `V2026_06_01` `CapturedMir` AST Builders and Scalar Simplification Lemmas -/

@[reducible] private def boolMirTy : Ty := { kind := .bool, layoutIdx := 0 }
@[reducible] private def u32MirTy : Ty := { kind := .uint .u32, layoutIdx := 0 }
@[reducible] private def usizeMirTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
@[reducible] private def pairU32MirTy : Ty :=
  { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 0 }
@[reducible] private def pairU32MutRefMirTy : Ty :=
  { kind := .ref .mut (.tuple [.uint .u32, .uint .u32]), layoutIdx := 0 }
@[reducible] private def checkedU32MirTy : Ty :=
  { kind := .tuple [.uint .u32, .bool], layoutIdx := 0 }
@[reducible] private def cursorRetMirTy : Ty :=
  { kind := .tuple [.tuple [.uint .u32, .uint .u32], .bool], layoutIdx := 0 }
@[reducible] private def u32ArrayMirTy : Ty :=
  { kind := .array (.uint .u32) 0, layoutIdx := 0 }

@[reducible] private def u32ConstOp (n : Nat) : Operand :=
  .constant { ty := u32MirTy, val := .scalar (.int { bits := n, sizeBytes := 4 }) }

@[reducible] private def usizeConstOp (n : Nat) : Operand :=
  .constant { ty := usizeMirTy, val := .scalar (.int { bits := n, sizeBytes := 8 }) }

@[reducible] private def defaultU32Layout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 4 }
  backendRepr := .memory
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

@[reducible] private def defaultFnAbi : FnAbi := {
  args := []
  ret := { layout := defaultU32Layout, mode := .direct }
  conv := .rust
  canUnwind := false
}

@[reducible] private def mkDecl (mutability : Mutability) (ty : Ty) : LocalDecl :=
  { mutability, ty, debugName := none }

@[reducible] private def mkStmt (kind : StatementKind) : Statement :=
  { kind, span := "FunctionalTranslationTests.lean" }

@[reducible] private def mkTerm (kind : TerminatorKind) : Terminator :=
  { kind, span := "FunctionalTranslationTests.lean" }

@[reducible] private def mkMirBody
    (defPath : DefPath) (argCount : Nat)
    (localDecls : List LocalDecl) (basicBlocks : List BasicBlockData) :
    CapturedMir := {
  defPath, argCount, localDecls, basicBlocks
  phase := .runtimePostCleanup
  role := .subject
  fnAbi := defaultFnAbi
  layouts := emptyLayoutTable
  allocations := []
}

@[reducible] private def locPlace (idx : Local) : Place :=
  { local_ := idx, projection := [] }

private theorem nat_add_eq (a b : Nat) : a.add b = a + b := rfl
private theorem nat_mul_eq (a b : Nat) : a.mul b = a * b := rfl

private theorem nat_ble_eq_false_of_lt {a b : Nat} (h : b < a) :
    Nat.ble a b = false := by
  cases hb : Nat.ble a b
  · rfl
  · exact absurd (Nat.le_of_ble_eq_true hb) (by omega)

private theorem nat_ble_eq_true_of_le {a b : Nat} (h : a ≤ b) :
    Nat.ble a b = true :=
  Nat.ble_eq_true_of_le h

private theorem scalarModulus_four : scalarModulus 4 = 4294967296 := by decide
private theorem scalarModulus_eight : scalarModulus 8 = 18446744073709551616 := by decide

private theorem wrapScalarBits_of_lt {val modulus : Nat} (h : val < modulus) :
    wrapScalarBits val modulus = val := by
  unfold wrapScalarBits
  rw [nat_ble_eq_false_of_lt h]

private theorem boolToScalar_eq (b : Bool) :
    boolToScalar b = ⟨b.toNat, 1⟩ := by
  cases b <;> rfl

private theorem not_beq_toNat_zero (b : Bool) :
    (!b.toNat.beq 0) = b := by
  cases b <;> rfl

private theorem dec_rec_const {p : Prop} {α : Sort u} (v : α) (d : Decidable p) :
    @Decidable.rec p (fun _ => α) (fun _ => v) (fun _ => v) d = v := by
  cases d <;> rfl

private theorem not_beq_boolToScalar_zero (b : Bool) :
    !(Nat.beq (boolToScalar b).bits 0) = b := by
  cases b <;> rfl

private theorem evalScalarBinOp_le_u32
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .le ⟨a, 4⟩ ⟨b, 4⟩ locals mem false =
      .ok (.scalar ⟨(Nat.ble a b).toNat, 1⟩) locals mem := by
  unfold evalScalarBinOp
  dsimp only
  rw [boolToScalar_eq]

/-- Non-dead local slot helper (`none ↦ .uninit`, `some v ↦ .init v`). -/
@[reducible] private def optSlot : Option Value → LocalSlot
  | none => .uninit
  | some v => .init v

private theorem readProjectedValue_index
    (locals : List LocalSlot) (fields : List Value) (idxLocal : Local) :
    readProjectedValue locals (.aggregate 0 fields) [.index idxLocal] =
      match get? locals idxLocal with
      | .some (.init (.scalar sc)) =>
        match get? fields sc.bits with
        | .some elemVal => .ok elemVal
        | .none => .ub
      | _ => .ub := rfl

private theorem runMirTauToBlock_succ
    (fuel : Nat) (body : CapturedMir) (targetBlock : BasicBlockIdx) (s : MachineState) :
    runMirTauToBlock (fuel + 1) body targetBlock s =
      if Nat.beq s.frame.blockIdx targetBlock && Nat.beq s.frame.stmtIdx 0 then
        some s
      else
        match stepMirFn body s with
        | .tau (.running s') => runMirTauToBlock fuel body targetBlock s'
        | _ => none := rfl

private theorem evalRvalue_len_eq
    (locals : List LocalSlot) (place : Place) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals (.len place) mem localDecls layouts =
      match evalOperand locals (.copy place) mem.borrows mem.globals layouts mem.callerLocals with
      | .ok (.aggregate tag elems) locals' =>
        if Nat.beq tag 0 then
          .ok (.scalar ⟨length elems, 8⟩) locals' mem
        else
          .unsupported
      | .ok _ _ => .unsupported
      | .ub => .ub
      | .unsupported => .unsupported := by
  unfold evalRvalue
  dsimp only
  cases evalOperand locals (.copy place) mem.borrows mem.globals layouts mem.callerLocals with
  | ok v locals' =>
    cases v with
    | aggregate tag elems =>
      cases tag <;> rfl
    | _ => rfl
  | _ => rfl

private theorem evalScalarBinOp_add_u32
    {a b : Nat} {locals : List LocalSlot} {mem : Memory}
    (h_lt : a + b < 4294967296) :
    evalScalarBinOp .add ⟨a, 4⟩ ⟨b, 4⟩ locals mem false =
      .ok (.scalar ⟨a + b, 4⟩) locals mem := by
  unfold evalScalarBinOp
  dsimp only
  rw [nat_add_eq, scalarModulus_four, wrapScalarBits_of_lt h_lt]

private theorem evalScalarBinOp_add_usize
    {a b : Nat} {locals : List LocalSlot} {mem : Memory}
    (h_lt : a + b < 18446744073709551616) :
    evalScalarBinOp .add ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨a + b, 8⟩) locals mem := by
  unfold evalScalarBinOp
  dsimp only
  rw [nat_add_eq, scalarModulus_eight, wrapScalarBits_of_lt h_lt]

private theorem evalScalarBinOp_addUnchecked_u32
    {a b : Nat} {locals : List LocalSlot} {mem : Memory}
    (h_lt : a + b < 4294967296) :
    evalScalarBinOp .addUnchecked ⟨a, 4⟩ ⟨b, 4⟩ locals mem false =
      .ok (.scalar ⟨a + b, 4⟩) locals mem := by
  unfold evalScalarBinOp
  dsimp only
  rw [nat_add_eq, scalarModulus_four, nat_ble_eq_false_of_lt h_lt]

private theorem evalScalarBinOp_addUnchecked_usize
    {a b : Nat} {locals : List LocalSlot} {mem : Memory}
    (h_lt : a + b < 18446744073709551616) :
    evalScalarBinOp .addUnchecked ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨a + b, 8⟩) locals mem := by
  unfold evalScalarBinOp
  dsimp only
  rw [nat_add_eq, scalarModulus_eight, nat_ble_eq_false_of_lt h_lt]

private theorem evalScalarBinOp_addWithOverflow_u32
    {a b : Nat} {locals : List LocalSlot} {mem : Memory}
    (h_lt : a + b < 4294967296) :
    evalScalarBinOp .addWithOverflow ⟨a, 4⟩ ⟨b, 4⟩ locals mem false =
      .ok (.aggregate 0 [.scalar ⟨a + b, 4⟩, .scalar ⟨0, 1⟩]) locals mem := by
  unfold evalScalarBinOp
  dsimp only
  rw [nat_add_eq, scalarModulus_four, wrapScalarBits_of_lt h_lt,
      nat_ble_eq_false_of_lt h_lt]

private theorem evalScalarBinOp_mul_u32
    {a b : Nat} {locals : List LocalSlot} {mem : Memory}
    (h_lt : a * b < 4294967296) :
    evalScalarBinOp .mul ⟨a, 4⟩ ⟨b, 4⟩ locals mem false =
      .ok (.scalar ⟨a * b, 4⟩) locals mem := by
  unfold evalScalarBinOp
  dsimp only
  rw [nat_mul_eq, scalarModulus_four, wrapScalarBits_of_lt h_lt]

private theorem evalScalarBinOp_lt_u32_of_lt
    {a b : Nat} {locals : List LocalSlot} {mem : Memory}
    (h_lt : a < b) :
    evalScalarBinOp .lt ⟨a, 4⟩ ⟨b, 4⟩ locals mem false =
      .ok (.scalar ⟨1, 1⟩) locals mem := by
  unfold evalScalarBinOp
  dsimp only
  rw [nat_ble_eq_false_of_lt h_lt]
  rfl

private theorem evalScalarBinOp_lt_u32_of_ge
    {a b : Nat} {locals : List LocalSlot} {mem : Memory}
    (h_ge : b ≤ a) :
    evalScalarBinOp .lt ⟨a, 4⟩ ⟨b, 4⟩ locals mem false =
      .ok (.scalar ⟨0, 1⟩) locals mem := by
  unfold evalScalarBinOp
  dsimp only
  rw [nat_ble_eq_true_of_le h_ge]
  rfl

private theorem evalScalarBinOp_lt_usize_of_lt
    {a b : Nat} {locals : List LocalSlot} {mem : Memory}
    (h_lt : a < b) :
    evalScalarBinOp .lt ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨1, 1⟩) locals mem := by
  unfold evalScalarBinOp
  dsimp only
  rw [nat_ble_eq_false_of_lt h_lt]
  rfl

private theorem evalScalarBinOp_lt_usize_of_ge
    {a b : Nat} {locals : List LocalSlot} {mem : Memory}
    (h_ge : b ≤ a) :
    evalScalarBinOp .lt ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨0, 1⟩) locals mem := by
  unfold evalScalarBinOp
  dsimp only
  rw [nat_ble_eq_true_of_le h_ge]
  rfl

/-! ## Suite 1: Pillar 1 Symbolic Value Merging & Multi-Diamond `TransPlan.branch` -/

/--
Direct Pillar 1 test: `zipSymVal` merges nested symbolic aggregates while keeping
every outer `.adt` constructor exposed definitionally (`rfl`), and `SymVal.denote`
commutes with `zipSymVal` without path splitting.
-/
theorem pillar1_nested_agg_zip_spine_and_denote
    (cond : Bool) (a d : Nat) (b₁ b₂ : Bool) (c e : Nat) :
    let vThen : SymVal := .adt 0 [.scalar a 4, .adt 0 [.bool b₁, .scalar c 8]]
    let vElse : SymVal := .adt 0 [.scalar d 4, .adt 0 [.bool b₂, .scalar e 8]]
    zipSymVal cond vThen vElse =
      .adt 0
        [.scalar (if cond then a else d) 4,
         .adt 0 [.bool (if cond then b₁ else b₂), .scalar (if cond then c else e) 8]] ∧
    (zipSymVal cond vThen vElse).denote =
      (if cond then vThen.denote else vElse.denote) :=
  ⟨rfl, denote_zipSymVal cond _ _⟩

/-- Direct Pillar 1 frame-level test for `zipSymLocals` and `denote_zipSymLocals`. -/
theorem pillar1_symLocals_zip_denote
    (cond : Bool) (x y : Nat) :
    let fThen : SymLocals := [.uninit, .init (.scalar (x + 10) 4), .dead]
    let fElse : SymLocals := [.uninit, .init (.scalar (y + 20) 4), .dead]
    (zipSymLocals cond fThen fElse).denote =
      (if cond then fThen.denote else fElse.denote) :=
  denote_zipSymLocals cond rfl

/--
`V2026_06_01` `CapturedMir` body with two sequential `if/else` diamonds:
```rust
fn two_diamond_tuple(c1: bool, c2: bool, x: u32) -> u32 {
    let pair: (u32, u32) = if c1 { (x + 10, x + 20) } else { (x + 1, x + 2) };
    if c2 { pair.0 } else { pair.1 }
}
```
Notice that `pair` (`_4`) is constructed separately in `bb1` and `bb2`, joined
into a single symbolic aggregate at `bb3`, and then field-projected (`_4.0` and
`_4.1`) across the second diamond (`bb4` / `bb5` → `bb6`).
-/
def twoDiamondTupleBody : CapturedMir :=
  mkMirBody "test::two_diamond_tuple" 3
    [mkDecl .mut u32MirTy,
     mkDecl .not boolMirTy,
     mkDecl .not boolMirTy,
     mkDecl .not u32MirTy,
     mkDecl .mut pairU32MirTy,
     mkDecl .mut u32MirTy,
     mkDecl .mut u32MirTy]
    [ -- bb0: switch on c1 (_1)
      { statements := [mkStmt (.storageLive 4), mkStmt (.storageLive 5), mkStmt (.storageLive 6)]
        terminator := mkTerm (.switchInt (.copy (locPlace 1))
          { branches := [(0, 2)], otherwise := 1 })
        isCleanup := false },
      -- bb1 (c1 == true): _4 = (_3 + 10, _3 + 20); goto bb3
      { statements :=
          [mkStmt (.assign (locPlace 5) (.binaryOp .add (.copy (locPlace 3)) (u32ConstOp 10))),
           mkStmt (.assign (locPlace 6) (.binaryOp .add (.copy (locPlace 3)) (u32ConstOp 20))),
           mkStmt (.assign (locPlace 4) (.aggregate .tuple
             [.copy (locPlace 5), .copy (locPlace 6)]))]
        terminator := mkTerm (.goto 3)
        isCleanup := false },
      -- bb2 (c1 == false): _4 = (_3 + 1, _3 + 2); goto bb3
      { statements :=
          [mkStmt (.assign (locPlace 5) (.binaryOp .add (.copy (locPlace 3)) (u32ConstOp 1))),
           mkStmt (.assign (locPlace 6) (.binaryOp .add (.copy (locPlace 3)) (u32ConstOp 2))),
           mkStmt (.assign (locPlace 4) (.aggregate .tuple
             [.copy (locPlace 5), .copy (locPlace 6)]))]
        terminator := mkTerm (.goto 3)
        isCleanup := false },
      -- bb3 (first join): switch on c2 (_2)
      { statements := []
        terminator := mkTerm (.switchInt (.copy (locPlace 2))
          { branches := [(0, 5)], otherwise := 4 })
        isCleanup := false },
      -- bb4 (c2 == true): _0 = _4.0; goto bb6
      { statements :=
          [mkStmt (.assign (locPlace 0)
            (.use (.copy { local_ := 4, projection := [.field 0 u32MirTy] })))]
        terminator := mkTerm (.goto 6)
        isCleanup := false },
      -- bb5 (c2 == false): _0 = _4.1; goto bb6
      { statements :=
          [mkStmt (.assign (locPlace 0)
            (.use (.copy { local_ := 4, projection := [.field 1 u32MirTy] })))]
        terminator := mkTerm (.goto 6)
        isCleanup := false },
      -- bb6 (second join): return
      { statements := []
        terminator := mkTerm .return_
        isCleanup := false } ]

/-- Pure Lean functional specification of `twoDiamondTupleBody`. -/
def twoDiamondPure (c1 c2 : Bool) (x : Nat) : Nat :=
  if c2 then (if c1 then x + 10 else x + 1) else (if c1 then x + 20 else x + 2)

/-- Two-diamond `TransPlan.branch` joining at `bb3` and `bb6`. -/
def twoDiamondPlan : TransPlan :=
  .branch 3 (.jump 3 5) (.jump 3 5)
    (.branch 6 (.jump 6 3) (.jump 6 3) (.ret 1) 1)
    4

def twoDiamondClaim : Claim where
  body := twoDiamondTupleBody
  pre args :=
    ∃ (c1 c2 : Bool) (x : Nat),
      x < 1000 ∧
      args = [.scalar (boolToScalar c1), .scalar (boolToScalar c2), .scalar ⟨x, 4⟩]
  post args retVal :=
    ∀ (c1 c2 : Bool) (x : Nat),
      args = [.scalar (boolToScalar c1), .scalar (boolToScalar c2), .scalar ⟨x, 4⟩] →
      retVal = .scalar ⟨twoDiamondPure c1 c2 x, 4⟩

def twoDiamondTotalClaim : TotalClaim where
  body := twoDiamondTupleBody
  pre args mem :=
    mem = emptyMemory ∧
    ∃ (c1 c2 : Bool) (x : Nat),
      x < 1000 ∧
      args = [.scalar (boolToScalar c1), .scalar (boolToScalar c2), .scalar ⟨x, 4⟩]
  post args _ retVal mem' :=
    mem' = emptyMemory ∧
    ∀ (c1 c2 : Bool) (x : Nat),
      args = [.scalar (boolToScalar c1), .scalar (boolToScalar c2), .scalar ⟨x, 4⟩] →
      retVal = .scalar ⟨twoDiamondPure c1 c2 x, 4⟩

private theorem boolToScalar_inj {b₁ b₂ : Bool}
    (h : Value.scalar (boolToScalar b₁) = Value.scalar (boolToScalar b₂)) :
    b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> simp [boolToScalar] at h <;> rfl

/--
Core `wpTransPlan` proof for `twoDiamondTupleBody` over symbolic `(c1, c2, x)`.
Crucially, this proof NEVER invokes `cases c1` or `cases c2`: `zipLocalSlots`
merges the symbolic `(u32, u32)` aggregate at `bb3` so field projections `.0`
and `.1` in the second diamond evaluate in a single pass.
-/
theorem wpTransPlan_twoDiamondTuple
    (c1 c2 : Bool) (x : Nat) (hx : x < 1000) :
    wpTransPlan mirNoCallWP twoDiamondTupleBody twoDiamondPlan
      (· = .normal (.scalar ⟨twoDiamondPure c1 c2 x, 4⟩, emptyMemory))
      (initMachineStateWithMemory twoDiamondTupleBody
        [.scalar (boolToScalar c1), .scalar (boolToScalar c2), .scalar ⟨x, 4⟩]
        emptyMemory) := by
  have hx10 : x + 10 < 4294967296 := by omega
  have hx20 : x + 20 < 4294967296 := by omega
  have hx1 : x + 1 < 4294967296 := by omega
  have hx2 : x + 2 < 4294967296 := by omega
  rw [boolToScalar_eq c1, boolToScalar_eq c2]
  dsimp only [twoDiamondPlan, twoDiamondTupleBody]
  rw [wpTransPlan]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, evalTerminator, lookupSwitchTarget, optSlot, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, invalidateConflictingBorrows, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList, evalScalarBinOp]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial, trivial, ?_⟩
  rw [wpTransPlan]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, evalTerminator, lookupSwitchTarget, optSlot, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, invalidateConflictingBorrows, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList, evalScalarBinOp]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial, trivial, ?_⟩
  rw [wpTransPlan]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, evalTerminator, lookupSwitchTarget, optSlot, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, invalidateConflictingBorrows, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList, evalScalarBinOp]
  rw [dec_rec_const c2.toNat, not_beq_toNat_zero c2, not_beq_toNat_zero c1,
      nat_add_eq x 10, nat_add_eq x 20, nat_add_eq x 1, nat_add_eq x 2,
      scalarModulus_four,
      wrapScalarBits_of_lt hx10, wrapScalarBits_of_lt hx20,
      wrapScalarBits_of_lt hx1, wrapScalarBits_of_lt hx2]
  dsimp only [twoDiamondPure, ite, instDecidableEqBool, Bool.decEq]

theorem twoDiamondClaim_verified : VerificationResult twoDiamondClaim := by
  refine verifyByTransPlan (ewp := mirNoCallWP)
    twoDiamondClaim (fun _ => twoDiamondPlan) ?_
  rintro args ⟨c1, c2, x, hx, rfl⟩
  exact wpTransPlan_mono
    (fun out h_eq retVal _ h_norm => by
      rw [h_eq] at h_norm
      injection h_norm with h_pair
      injection h_pair with h_ret _
      subst h_ret
      intro c1' c2' x' h_args
      injection h_args with h1 h_tl
      injection h_tl with h2 h_tl2
      injection h_tl2 with h3 _
      have hc1 := boolToScalar_inj h1.symm
      have hc2 := boolToScalar_inj h2.symm
      injection h3 with hsc; injection hsc with hx_eq _
      subst hc1 hc2 hx_eq
      rfl)
    (wpTransPlan_twoDiamondTuple c1 c2 x hx)

theorem twoDiamondTotalClaim_verified :
    TotalVerificationResult twoDiamondTotalClaim := by
  refine verifyTotalByTransPlan (ewp := mirNoCallWP)
    twoDiamondTotalClaim (fun _ _ => twoDiamondPlan) ?_
  rintro args mem ⟨rfl, c1, c2, x, hx, rfl⟩
  exact wpTransPlan_mono
    (fun out h_eq => by
      subst h_eq
      refine ⟨_, _, rfl, rfl, ?_⟩
      intro c1' c2' x' h_args
      injection h_args with h1 h_tl
      injection h_tl with h2 h_tl2
      injection h_tl2 with h3 _
      have hc1 := boolToScalar_inj h1.symm
      have hc2 := boolToScalar_inj h2.symm
      injection h3 with hsc; injection hsc with hx_eq _
      subst hc1 hc2 hx_eq
      rfl)
    (wpTransPlan_twoDiamondTuple c1 c2 x hx)

/-! ## Suite 2: Pillar 2 Symbolic `while`-Loop Total & Coinductive Partial Verification -/

/--
`V2026_06_01` `CapturedMir` body for a symbolic `while i < n` arithmetic-sum loop:
```rust
fn sum_to_n(n: u32) -> u32 {
    let mut i: u32 = 0;
    let mut acc: u32 = 0;
    while i < n {
        acc = acc + i;
        i = i + 1;
    }
    acc
}
```
-/
def sumToNLoopBody : CapturedMir :=
  mkMirBody "test::sum_to_n" 1
    [mkDecl .mut u32MirTy,
     mkDecl .not u32MirTy,
     mkDecl .mut u32MirTy,
     mkDecl .mut u32MirTy,
     mkDecl .mut boolMirTy]
    [ -- bb0 (entry): _2 (i) = 0; _3 (acc) = 0; goto bb1
      { statements :=
          [mkStmt (.storageLive 2),
           mkStmt (.storageLive 3),
           mkStmt (.storageLive 4),
           mkStmt (.assign (locPlace 2) (.use (u32ConstOp 0))),
           mkStmt (.assign (locPlace 3) (.use (u32ConstOp 0)))]
        terminator := mkTerm (.goto 1)
        isCleanup := false },
      -- bb1 (loop header): _4 = (_2 < _1); switchInt(_4) [0 -> bb3, otherwise -> bb2]
      { statements :=
          [mkStmt (.assign (locPlace 4)
            (.binaryOp .lt (.copy (locPlace 2)) (.copy (locPlace 1))))]
        terminator := mkTerm (.switchInt (.copy (locPlace 4))
          { branches := [(0, 3)], otherwise := 2 })
        isCleanup := false },
      -- bb2 (loop body): _3 = _3 + _2; _2 = _2 + 1; goto bb1
      { statements :=
          [mkStmt (.assign (locPlace 3)
            (.binaryOp .add (.copy (locPlace 3)) (.copy (locPlace 2)))),
           mkStmt (.assign (locPlace 2)
            (.binaryOp .add (.copy (locPlace 2)) (u32ConstOp 1)))]
        terminator := mkTerm (.goto 1)
        isCleanup := false },
      -- bb3 (loop exit): _0 = _3; return
      { statements :=
          [mkStmt (.assign (locPlace 0) (.use (.copy (locPlace 3))))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/-- Pure arithmetic sum $\sum_{k=0}^{n-1} k$. -/
def arithSum : Nat → Nat
  | 0 => 0
  | k + 1 => arithSum k + k

private theorem arithSum_le_sq : ∀ k : Nat, arithSum k ≤ k * k
  | 0 => Nat.le_refl 0
  | k + 1 => by
    have ih := arithSum_le_sq k
    calc
      arithSum (k + 1) = arithSum k + k := rfl
      _ ≤ k * k + k := Nat.add_le_add_right ih k
      _ ≤ (k + 1) * (k + 1) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        omega

/-- Loop header `MachineState` at iteration `i` with `acc = arithSum i`. -/
private def sumToNHeaderState (n i : Nat) (cmpOpt : Option Value) : MachineState :=
  { frame := {
      blockIdx := 1
      stmtIdx := 0
      locals :=
        [.uninit,
         .init (.scalar ⟨n, 4⟩),
         .init (.scalar ⟨i, 4⟩),
         .init (.scalar ⟨arithSum i, 4⟩),
         optSlot cmpOpt]
    }
    memory := emptyMemory }

private def sumToNBranchState (bb n i cmpBits : Nat) : MachineState :=
  { frame := {
      blockIdx := bb
      stmtIdx := 0
      locals :=
        [.uninit,
         .init (.scalar ⟨n, 4⟩),
         .init (.scalar ⟨i, 4⟩),
         .init (.scalar ⟨arithSum i, 4⟩),
         .init (.scalar ⟨cmpBits, 1⟩)]
    }
    memory := emptyMemory }

private theorem sumToN_header_switch_ge
    (i : Nat) (cmpOpt : Option Value) :
    runMirToBinarySwitch 2 sumToNLoopBody (sumToNHeaderState i i cmpOpt) =
      some (false, 0, sumToNBranchState 2 i i 0, sumToNBranchState 3 i i 0) := by
  cases cmpOpt <;>
    (dsimp only [sumToNHeaderState, sumToNLoopBody, sumToNBranchState]
     dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
     rw [evalScalarBinOp_lt_u32_of_ge (Nat.le_refl i)]
     dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
     rfl)

private theorem sumToN_header_switch_lt
    {n i : Nat} (cmpOpt : Option Value) (h_lt : i < n) :
    runMirToBinarySwitch 2 sumToNLoopBody (sumToNHeaderState n i cmpOpt) =
      some (true, 1, sumToNBranchState 2 n i 1, sumToNBranchState 3 n i 1) := by
  cases cmpOpt <;>
    (dsimp only [sumToNHeaderState, sumToNLoopBody, sumToNBranchState]
     dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
     rw [evalScalarBinOp_lt_u32_of_lt h_lt]
     dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
     rfl)

private theorem sumToN_body_step
    {n i : Nat}
    (h_acc_lt : arithSum i + i < 4294967296)
    (h_inc_lt : i + 1 < 4294967296) :
    evalPlanToJoin sumToNLoopBody (.jump 1 4) (sumToNBranchState 2 n i 1) =
      some (sumToNHeaderState n (i + 1) (some (.scalar ⟨1, 1⟩))) := by
  dsimp only [sumToNBranchState, sumToNLoopBody, sumToNHeaderState]
  dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
  rw [evalScalarBinOp_add_u32 h_acc_lt]
  dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
  rw [evalScalarBinOp_add_u32 h_inc_lt]
  dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
  rfl

/--
Inductive `wpTransPlan` proof for the `TransPlan.loop` sub-plan rooted at header
`bb1` for arbitrary symbolic `n ≤ 1000` and remaining iterations `rem = n - i`.
-/
private theorem wpTransPlan_sumToN_header
    (n : Nat) (hn : n ≤ 1000) :
    ∀ (rem i : Nat) (cmpOpt : Option Value),
      i + rem = n →
      wpTransPlan mirNoCallWP sumToNLoopBody
        (.loop 1 rem (.jump 1 4) (.ret 2) 2)
        (· = .normal (.scalar ⟨arithSum n, 4⟩, emptyMemory))
        (sumToNHeaderState n i cmpOpt)
  | 0, i, cmpOpt, h_sum => by
    have h_eq : i = n := by omega
    subst h_eq
    rw [wpTransPlan]
    rw [sumToN_header_switch_ge i cmpOpt]
    refine ⟨rfl, rfl, rfl, ?_⟩
    rw [wpTransPlan]
    rfl
  | rem + 1, i, cmpOpt, h_sum => by
    have h_lt : i < n := by omega
    have h_ai_le : arithSum i ≤ i * i := arithSum_le_sq i
    have h_i_le : i * i ≤ 1000 * 1000 := Nat.mul_le_mul (by omega) (by omega)
    have h_acc_lt : arithSum i + i < 4294967296 := by omega
    have h_inc_lt : i + 1 < 4294967296 := by omega
    have ih := wpTransPlan_sumToN_header n hn rem (i + 1) (some (.scalar ⟨1, 1⟩)) (by omega)
    rw [wpTransPlan]
    rw [sumToN_header_switch_lt cmpOpt h_lt]
    dsimp only
    refine ⟨rfl, rfl, (fun h => by cases h), fun _ => ?_⟩
    rw [sumToN_body_step h_acc_lt h_inc_lt]
    dsimp only
    exact ⟨trivial, ih⟩

def sumToNTotalClaim (n : Nat) : TotalClaim where
  body := sumToNLoopBody
  pre args mem := args = [.scalar ⟨n, 4⟩] ∧ mem = emptyMemory
  post _ _ retVal mem' :=
    retVal = .scalar ⟨arithSum n, 4⟩ ∧ mem' = emptyMemory

/--
Symbolic total-correctness (`DWP` / `TotalVerificationResult`) and
`MirTerminatesAndNoUB` theorem for `sumToNLoopBody` across all `n ≤ 1000`.
-/
theorem sumToNLoop_total_and_terminates (n : Nat) (hn : n ≤ 1000) :
    TotalVerificationResult (sumToNTotalClaim n) ∧
    MirTerminatesAndNoUB sumToNLoopBody [.scalar ⟨n, 4⟩] emptyMemory := by
  have h_entry :
      runMirToBlock 7 sumToNLoopBody 1
        (initMachineStateWithMemory sumToNLoopBody [.scalar ⟨n, 4⟩] emptyMemory) =
        some (sumToNHeaderState n 0 none) := rfl
  have h_plan :
      wpTransPlan mirNoCallWP sumToNLoopBody
        (.seq 1 (.loop 1 n (.jump 1 4) (.ret 2) 2) 7)
        (· = .normal (.scalar ⟨arithSum n, 4⟩, emptyMemory))
        (initMachineStateWithMemory sumToNLoopBody [.scalar ⟨n, 4⟩] emptyMemory) := by
    rw [wpTransPlan]
    rw [h_entry]
    exact wpTransPlan_sumToN_header n hn n 0 none (Nat.zero_add n)
  have h_total : TotalVerificationResult (sumToNTotalClaim n) := by
    refine verifyTotalByTransPlan (ewp := mirNoCallWP)
      (sumToNTotalClaim n)
      (fun _ _ => .seq 1 (.loop 1 n (.jump 1 4) (.ret 2) 2) 7) ?_
    rintro _ _ ⟨rfl, rfl⟩
    exact wpTransPlan_mono
      (fun _ h_eq => ⟨_, _, h_eq, rfl, rfl⟩)
      h_plan
  have h_term : MirTerminatesAndNoUB sumToNLoopBody [.scalar ⟨n, 4⟩] emptyMemory :=
    mirTerminatesAndNoUB_of_dwp (ewp := mirNoCallWP) (P := fun _ _ => True)
      (DWP.mono
        (fun _ _ h_eq => ⟨_, _, h_eq, trivial⟩)
        (dwp_mirStatefulTree_of_transPlan h_plan))
  exact ⟨h_total, h_term⟩

def sumToNPartialClaim (n : Nat) : Claim where
  body := sumToNLoopBody
  pre args := args = [.scalar ⟨n, 4⟩]
  post _ retVal := retVal = .scalar ⟨arithSum n, 4⟩

/--
Coinductive partial-correctness (`VerificationResult`) verification of
`sumToNLoopBody` via `dwlp_mirTree_while_invariant` (without supplying a rank).
-/
theorem sumToNLoop_partial_by_coinductive_invariant (n : Nat) (hn : n ≤ 1000) :
    VerificationResult (sumToNPartialClaim n) := by
  refine verifyByDWLP (sumToNPartialClaim n) ?_
  rintro _ rfl
  let Inv : MachineState → Prop := fun s =>
    ∃ i cmpOpt, i ≤ n ∧ s = sumToNHeaderState n i cmpOpt
  have h_entry :
      runMirTauToBlock 7 sumToNLoopBody 1
        (initMachineState sumToNLoopBody [.scalar ⟨n, 4⟩]) =
        some (sumToNHeaderState n 0 none) := rfl
  refine dwlp_of_runMirTauToBlock 7 h_entry ?_
  refine dwlp_mirTree_while_invariant (ewp := mirDefaultWP)
    sumToNLoopBody Inv 2 (.jump 1 4) (.ret 2) ?_
    ⟨0, none, Nat.zero_le n, rfl⟩
  rintro s ⟨i, cmpOpt, h_le, rfl⟩
  rcases Nat.lt_or_eq_of_le h_le with h_lt | rfl
  · have h_ai_le : arithSum i ≤ i * i := arithSum_le_sq i
    have h_i_le : i * i ≤ 1000 * 1000 := Nat.mul_le_mul (by omega) (by omega)
    have h_acc_lt : arithSum i + i < 4294967296 := by omega
    have h_inc_lt : i + 1 < 4294967296 := by omega
    refine ⟨true, 1, _, _, sumToN_header_switch_lt cmpOpt h_lt,
            (fun h => by cases h), fun _ => ?_⟩
    exact ⟨sumToNHeaderState n (i + 1) (some (.scalar ⟨1, 1⟩)),
           sumToN_body_step h_acc_lt h_inc_lt, trivial,
           ⟨i + 1, _, by omega, rfl⟩⟩
  · refine ⟨false, 0, _, _, sumToN_header_switch_ge i cmpOpt,
            fun _ => ?_, (fun h => by cases h)⟩
    rw [wpTransPlan]
    intro retVal _ h_out
    injection h_out with h_pair
    injection h_pair with h_ret _
    exact h_ret.symm

/-! ## Suite 3: Pillar 3 `&mut` Lenses, `ActiveTypedMutBorrow`, and `&mut FrameCursor` MIR -/

/-- Logical Rust struct `struct FrameCursor { pos: u32, len: u32 }`. -/
structure FrameCursor : Type where
  pos : Nat
  len : Nat
  deriving DecidableEq, Repr

/-- `ValueCodec` encoding `FrameCursor` as `Value.aggregate 0 [pos, len]`. -/
def frameCursorCodec : ValueCodec FrameCursor where
  encode c := .aggregate 0 [.scalar ⟨c.pos, 4⟩, .scalar ⟨c.len, 4⟩]
  decode
    | .aggregate 0 [.scalar ⟨p, 4⟩, .scalar ⟨l, 4⟩] => some { pos := p, len := l }
    | _ => none
  default := { pos := 0, len := 0 }
  decode_encode c := by rcases c with ⟨p, l⟩; rfl

/-- Pure state-update translation of `fn advance(&mut self, delta: u32) -> bool`. -/
def FrameCursor.advancePure (delta : Nat) : MutUpdate FrameCursor Bool :=
  fun c =>
    if Nat.ble (c.pos + delta) c.len then
      ({ c with pos := c.pos + delta }, true)
    else
      (c, false)

/-- Sub-place field lens `FrameCursor ⟶ pos` (`&mut cursor.pos`). -/
def FrameCursor.posLens : MutLens FrameCursor Nat where
  readView c := c.pos
  writeBack p c := { c with pos := p }

theorem lawfulMutLens_frameCursor_posLens :
    LawfulMutLens FrameCursor.posLens (fun _ => True) where
  valid_writeBack _ _ _ := trivial
  readView_writeBack _ _ _ := rfl
  writeBack_readView c _ := by cases c; rfl
  writeBack_writeBack _ _ c _ := by cases c; rfl

/--
Part 3A: Spatial `ActiveTypedMutBorrow` (`PointsTo ∗ BorrowToken .active`),
sequential `MutUpdate.seq` composition, sub-place lens reading, and
disjoint-allocation `AgreeOnFootprint` framing via `memoryPtrMutLens`.
-/
theorem pillar3_activeTypedMutBorrow_seq_and_disjoint_frame
    {rp : RawPtrVal} {m : Memory} {frameFp : Footprint}
    (c : FrameCursor) (d₁ d₂ : Nat)
    (h_borrow : ActiveTypedMutBorrow rp frameCursorCodec c ⟨m, mutBorrowFootprint rp⟩)
    (h_disj_addrs : ∀ allocId offset,
      (allocId, offset) ∈ frameFp.addrs → allocId ≠ rp.allocId)
    (h_disj_tags : ∀ tag ∈ frameFp.tags,
      ∃ entry,
        lookupBorrow m.borrows tag = some entry ∧
        entry.targetLocal ≠ rp.allocId) :
    let L := memoryPtrMutLens rp frameCursorCodec
    let (m₁, r₁) := L.applyUpdate (FrameCursor.advancePure d₁) m
    let (m₂, r₂) := L.applyUpdate (FrameCursor.advancePure d₂) m₁
    let (cSeq, rSeq) :=
      MutUpdate.seq (FrameCursor.advancePure d₁)
        (fun _ => FrameCursor.advancePure d₂) c
    (r₁, r₂) = rSeq ∧
    ActiveTypedMutBorrow rp frameCursorCodec cSeq ⟨m₂, mutBorrowFootprint rp⟩ ∧
    (L.comp FrameCursor.posLens).readView m₂ = cSeq.pos ∧
    AgreeOnFootprint frameFp m m₁ := by
  dsimp only
  obtain ⟨hr₁, h_sep₁⟩ :=
    memoryPtrMutLens_applyUpdate_sep (FrameCursor.advancePure d₁) h_borrow
  have h_frame₁ :
      AgreeOnFootprint frameFp m
        ((memoryPtrMutLens rp frameCursorCodec).applyUpdate
          (FrameCursor.advancePure d₁) m).1 := by
    dsimp only [MutLens.applyUpdate]
    exact memoryPtrMutLens_writeBack_agreeOnDisjointAllocs _ frameFp
      h_borrow h_disj_addrs h_disj_tags
  obtain ⟨hr₂, h_sep₂⟩ :=
    memoryPtrMutLens_applyUpdate_sep (FrameCursor.advancePure d₂) h_sep₁
  have h_read₂ :
      (memoryPtrMutLens rp frameCursorCodec).readView
        ((memoryPtrMutLens rp frameCursorCodec).applyUpdate
          (FrameCursor.advancePure d₂)
          ((memoryPtrMutLens rp frameCursorCodec).applyUpdate
            (FrameCursor.advancePure d₁) m).1).1 =
        (FrameCursor.advancePure d₂ (FrameCursor.advancePure d₁ c).1).1 :=
    memoryPtrMutLens_readView_of_sep h_sep₂
  refine ⟨?_, h_sep₂, ?_, h_frame₁⟩
  · dsimp only [MutUpdate.seq]
    rw [hr₁, hr₂]
  · dsimp only [MutLens.comp, FrameCursor.posLens, MutUpdate.seq]
    rw [h_read₂]

/--
Part 3B: `V2026_06_01` `CapturedMir` body exercising `&mut FrameCursor` creation
(`Rvalue.ref (.mut false)`), dereference-field reads (`(*_3).0`, `(*_3).1`),
conditional dereference-field mutation (`(*_3).0 = _4` inside `bb1`), diamond
joining at `bb3`, and returning `(updated_cursor, ok_bool)`:
```rust
fn advance_cursor_mut(mut c: FrameCursor, delta: u32) -> (FrameCursor, bool) {
    let r: &mut FrameCursor = &mut c;
    let next_pos: u32 = (*r).pos + delta;
    let ok: bool = next_pos <= (*r).len;
    if ok {
        (*r).pos = next_pos;
    }
    (*r, ok)
}
```
-/
def advanceCursorMutMirBody : CapturedMir :=
  mkMirBody "test::advance_cursor_mut" 2
    [mkDecl .mut cursorRetMirTy,
     mkDecl .mut pairU32MirTy,
     mkDecl .not u32MirTy,
     mkDecl .mut pairU32MutRefMirTy,
     mkDecl .mut u32MirTy,
     mkDecl .mut boolMirTy,
     mkDecl .mut pairU32MirTy]
    [ -- bb0: _3 = &mut _1; _4 = (*_3).0 + _2; _5 = (_4 <= (*_3).1); switchInt(_5)
      { statements :=
          [mkStmt (.storageLive 3),
           mkStmt (.storageLive 4),
           mkStmt (.storageLive 5),
           mkStmt (.storageLive 6),
           mkStmt (.assign (locPlace 3) (.ref (.mut false) (locPlace 1))),
           mkStmt (.assign (locPlace 4)
             (.binaryOp .add
               (.copy { local_ := 3, projection := [.deref, .field 0 u32MirTy] })
               (.copy (locPlace 2)))),
           mkStmt (.assign (locPlace 5)
             (.binaryOp .le
               (.copy (locPlace 4))
               (.copy { local_ := 3, projection := [.deref, .field 1 u32MirTy] })))]
        terminator := mkTerm (.switchInt (.copy (locPlace 5))
          { branches := [(0, 2)], otherwise := 1 })
        isCleanup := false },
      -- bb1 (ok == true): (*_3).0 = _4; goto bb3
      { statements :=
          [mkStmt (.assign
            { local_ := 3, projection := [.deref, .field 0 u32MirTy] }
            (.use (.copy (locPlace 4))))]
        terminator := mkTerm (.goto 3)
        isCleanup := false },
      -- bb2 (ok == false): goto bb3
      { statements := []
        terminator := mkTerm (.goto 3)
        isCleanup := false },
      -- bb3 (join): _6 = *_3; _0 = (_6, _5); return
      { statements :=
          [mkStmt (.assign (locPlace 6)
            (.use (.copy { local_ := 3, projection := [.deref] }))),
           mkStmt (.assign (locPlace 0)
            (.aggregate .tuple [.copy (locPlace 6), .copy (locPlace 5)]))]
        terminator := mkTerm .return_
        isCleanup := false } ]

def advanceCursorMutPlan : TransPlan :=
  .branch 3 (.jump 3 3) (.jump 3 2) (.ret 3) 8

/--
`MutRefLocalSpec FrameCursor Bool` connecting `advanceCursorMutMirBody` to pure
`FrameCursor.advancePure` while certifying that Tree Borrows tag `1` remains
`.active` on local `1` at function exit.
-/
def advanceCursorMutSpec : MutRefLocalSpec FrameCursor Bool where
  body := advanceCursorMutMirBody
  stateCodec := frameCursorCodec
  retCodec := ValueCodec.rustBool
  pre c extraArgs mem :=
    c.pos < 10000 ∧
    c.len < 10000 ∧
    mem = emptyMemory ∧
    ∃ delta : Nat,
      delta < 10000 ∧
      extraArgs = [.scalar ⟨delta, 4⟩]
  update extraArgs :=
    match extraArgs with
    | [.scalar ⟨delta, 4⟩] => FrameCursor.advancePure delta
    | _ => fun c => (c, false)
  postMem _ _ _ mem' :=
    lookupBorrow mem'.borrows 1 =
      some { tag := 1, targetLocal := 1, targetProjection := [], perm := .active }

/--
Symbolic total & stateful verification of `advanceCursorMutMirBody` against
`FrameCursor.advancePure` for all `c : FrameCursor` (`c.pos, c.len < 10000`) and
`delta < 10000` — proved via `TransPlan.branch` without case-splitting during
MIR diamond execution.
-/
theorem advanceCursorMutSpec_total_and_stateful_verified :
    TotalVerificationResult advanceCursorMutSpec.toTotalClaim ∧
    StatefulVerificationResult advanceCursorMutSpec.toStatefulClaim := by
  have h_tot : TotalVerificationResult advanceCursorMutSpec.toTotalClaim := by
    refine verifyMutRefLocalTotalByTransPlan (ewp := mirNoCallWP)
      advanceCursorMutSpec (fun _ _ _ => advanceCursorMutPlan) ?_
    rintro c extraArgs mem ⟨h_pos, h_len, rfl, delta, h_delta, rfl⟩
    have h_add_lt : c.pos + delta < 4294967296 := by omega
    have h_plan :
        wpTransPlan mirNoCallWP advanceCursorMutMirBody advanceCursorMutPlan
          (fun out =>
            out =
              .normal
                ((ValueCodec.pair frameCursorCodec ValueCodec.rustBool).encode
                   (FrameCursor.advancePure delta c),
                 { emptyMemory with
                   borrows :=
                     [{ tag := 1, targetLocal := 1, targetProjection := [], perm := .active }]
                   nextTag := 2 }))
          (initMachineStateWithMemory advanceCursorMutMirBody
            [frameCursorCodec.encode c, .scalar ⟨delta, 4⟩] emptyMemory) := by
      dsimp only [advanceCursorMutPlan, advanceCursorMutMirBody, frameCursorCodec]
      rw [wpTransPlan]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
      rw [evalScalarBinOp_add_u32 h_add_lt]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
      rw [evalScalarBinOp_le_u32]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial, trivial, ?_⟩
      rw [wpTransPlan]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
      rw [dec_rec_const (Nat.ble (c.pos + delta) c.len).toNat,
          not_beq_toNat_zero (Nat.ble (c.pos + delta) c.len)]
      dsimp only [ValueCodec.pair, frameCursorCodec, ValueCodec.rustBool,
                  FrameCursor.advancePure]
      cases Nat.ble (c.pos + delta) c.len <;> rfl
    exact wpTransPlan_mono
      (fun out h_eq => by
        subst h_eq
        exact ⟨_, rfl, rfl⟩)
      h_plan
  exact ⟨h_tot, statefulOfTotalMutRefLocal h_tot⟩


end Anneal.FunctionalTranslationTests
