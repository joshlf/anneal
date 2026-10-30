import Anneal.FunctionalTranslation

namespace Anneal.FunctionalTranslationEquivTests

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

/-! ## Suite 4: Pillar 4 Program-to-Program Layer 1A Refinement (`≤` and `=`) -/

/-! ### Part 4A: Unchecked Slice-Sum Loop Refines & Equals Checked Slice-Sum Loop -/

/--
Checked `V2026_06_01` `CapturedMir` slice/array summation loop with BOTH:
1. Runtime array-bounds `TerminatorKind.assert` (`i < Len(arr)`, unwinding with
   `.continue_` panic on out-of-bounds), and
2. Runtime checked `BinOp.addWithOverflow` + `TerminatorKind.assert`
   (`!overflow`, unwinding with `.continue_` panic on `u32` overflow):
```rust
fn safe_slice_sum(arr: [u32], n: usize) -> u32 {
    let mut i: usize = 0;
    let mut acc: u32 = 0;
    while i < n {
        assert!(i < arr.len());
        let elem = arr[i];
        let (next_acc, ovf) = overflowing_add(acc, elem);
        assert!(!ovf);
        acc = next_acc;
        i += 1;
    }
    acc
}
```
-/
def safeSliceSumBody : CapturedMir :=
  mkMirBody "test::safe_slice_sum" 2
    [mkDecl .mut u32MirTy,         -- _0: return u32
     mkDecl .not u32ArrayMirTy,    -- _1: arr
     mkDecl .not usizeMirTy,       -- _2: n
     mkDecl .mut usizeMirTy,       -- _3: i
     mkDecl .mut u32MirTy,         -- _4: acc
     mkDecl .mut boolMirTy,        -- _5: i < n
     mkDecl .mut usizeMirTy,       -- _6: len(arr)
     mkDecl .mut boolMirTy,        -- _7: i < len(arr)
     mkDecl .mut u32MirTy,         -- _8: arr[i]
     mkDecl .mut checkedU32MirTy,  -- _9: (acc + arr[i], ovf)
     mkDecl .mut boolMirTy]        -- _10: ovf
    [ -- bb0 (entry): _3 (i) = 0; _4 (acc) = 0; goto bb1
      { statements :=
          [mkStmt (.storageLive 3), mkStmt (.storageLive 4),
           mkStmt (.storageLive 5), mkStmt (.storageLive 6),
           mkStmt (.storageLive 7), mkStmt (.storageLive 8),
           mkStmt (.storageLive 9), mkStmt (.storageLive 10),
           mkStmt (.assign (locPlace 3) (.use (usizeConstOp 0))),
           mkStmt (.assign (locPlace 4) (.use (u32ConstOp 0)))]
        terminator := mkTerm (.goto 1)
        isCleanup := false },
      -- bb1 (while header): _5 = (_3 < _2); switchInt(_5) [0 -> bb5, otherwise -> bb2]
      { statements :=
          [mkStmt (.assign (locPlace 5)
            (.binaryOp .lt (.copy (locPlace 3)) (.copy (locPlace 2))))]
        terminator := mkTerm (.switchInt (.copy (locPlace 5))
          { branches := [(0, 5)], otherwise := 2 })
        isCleanup := false },
      -- bb2 (bounds check): _6 = Len(_1); _7 = (_3 < _6); assert(_7 == true) -> bb3
      { statements :=
          [mkStmt (.assign (locPlace 6) (.len (locPlace 1))),
           mkStmt (.assign (locPlace 7)
            (.binaryOp .lt (.copy (locPlace 3)) (.copy (locPlace 6))))]
        terminator := mkTerm (.assert (.copy (locPlace 7)) true 3 .continue_)
        isCleanup := false },
      -- bb3 (checked add): _8 = _1[_3]; _9 = AddWithOverflow(_4, _8); _10 = _9.1; assert(_10 == false) -> bb4
      { statements :=
          [mkStmt (.assign (locPlace 8)
            (.use (.copy { local_ := 1, projection := [.index 3] }))),
           mkStmt (.assign (locPlace 9)
            (.binaryOp .addWithOverflow (.copy (locPlace 4)) (.copy (locPlace 8)))),
           mkStmt (.assign (locPlace 10)
            (.use (.copy { local_ := 9, projection := [.field 1 boolMirTy] })))]
        terminator := mkTerm (.assert (.copy (locPlace 10)) false 4 .continue_)
        isCleanup := false },
      -- bb4 (latch): _4 = _9.0; _3 = Add(_3, 1); goto bb1
      { statements :=
          [mkStmt (.assign (locPlace 4)
            (.use (.copy { local_ := 9, projection := [.field 0 u32MirTy] }))),
           mkStmt (.assign (locPlace 3)
            (.binaryOp .add (.copy (locPlace 3)) (usizeConstOp 1)))]
        terminator := mkTerm (.goto 1)
        isCleanup := false },
      -- bb5 (exit): _0 = _4; return
      { statements :=
          [mkStmt (.assign (locPlace 0) (.use (.copy (locPlace 4))))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/--
Optimized `unsafe` `V2026_06_01` `CapturedMir` slice/array summation loop eliding
BOTH runtime `TerminatorKind.assert` checks and using `BinOp.addUnchecked`
(where out-of-bounds indexing or `u32`/`usize` overflow is immediate UB):
```rust
unsafe fn fast_slice_sum(arr: [u32], n: usize) -> u32 {
    let mut i: usize = 0;
    let mut acc: u32 = 0;
    while i < n {
        let elem = *arr.get_unchecked(i);
        acc = acc.unchecked_add(elem);
        i = i.unchecked_add(1);
    }
    acc
}
```
-/
def fastSliceSumBody : CapturedMir :=
  mkMirBody "test::fast_slice_sum" 2
    [mkDecl .mut u32MirTy,       -- _0: return u32
     mkDecl .not u32ArrayMirTy,  -- _1: arr
     mkDecl .not usizeMirTy,     -- _2: n
     mkDecl .mut usizeMirTy,     -- _3: i
     mkDecl .mut u32MirTy,       -- _4: acc
     mkDecl .mut boolMirTy,      -- _5: i < n
     mkDecl .mut u32MirTy]       -- _6: arr[i]
    [ -- bb0 (entry): _3 (i) = 0; _4 (acc) = 0; goto bb1
      { statements :=
          [mkStmt (.storageLive 3), mkStmt (.storageLive 4),
           mkStmt (.storageLive 5), mkStmt (.storageLive 6),
           mkStmt (.assign (locPlace 3) (.use (usizeConstOp 0))),
           mkStmt (.assign (locPlace 4) (.use (u32ConstOp 0)))]
        terminator := mkTerm (.goto 1)
        isCleanup := false },
      -- bb1 (while header): _5 = (_3 < _2); switchInt(_5) [0 -> bb3, otherwise -> bb2]
      { statements :=
          [mkStmt (.assign (locPlace 5)
            (.binaryOp .lt (.copy (locPlace 3)) (.copy (locPlace 2))))]
        terminator := mkTerm (.switchInt (.copy (locPlace 5))
          { branches := [(0, 3)], otherwise := 2 })
        isCleanup := false },
      -- bb2 (unchecked body): _6 = _1[_3]; _4 = AddUnchecked(_4, _6); _3 = AddUnchecked(_3, 1); goto bb1
      { statements :=
          [mkStmt (.assign (locPlace 6)
            (.use (.copy { local_ := 1, projection := [.index 3] }))),
           mkStmt (.assign (locPlace 4)
            (.binaryOp .addUnchecked (.copy (locPlace 4)) (.copy (locPlace 6)))),
           mkStmt (.assign (locPlace 3)
            (.binaryOp .addUnchecked (.copy (locPlace 3)) (usizeConstOp 1)))]
        terminator := mkTerm (.goto 1)
        isCleanup := false },
      -- bb3 (exit): _0 = _4; return
      { statements :=
          [mkStmt (.assign (locPlace 0) (.use (.copy (locPlace 4))))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/-- Encode a symbolic `List Nat` as a `V2026_06_01` `[u32]` `Value.aggregate`. -/
def encodeU32Slice (elems : List Nat) : Value :=
  .aggregate 0 (elems.map (fun x => Value.scalar ⟨x, 4⟩))

/-- Pure sum of the first `k` elements of `elems`. -/
def prefixSum (elems : List Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => prefixSum elems k + elems.getD k 0

private theorem prefixSum_succ (elems : List Nat) (k : Nat) :
    prefixSum elems (k + 1) = prefixSum elems k + elems.getD k 0 := rfl

private theorem prefixSum_mono (elems : List Nat) :
    ∀ {i j : Nat}, i ≤ j → prefixSum elems i ≤ prefixSum elems j := by
  intro i j h_le
  induction h_le with
  | refl => exact Nat.le_refl _
  | @step m _ ih =>
    rw [prefixSum_succ]
    omega

/-- Exact `MirEffect` event trace emitted by `n` iterations of `while i < n`. -/
def sliceLoopTrace (n : Nat) : List (Event MirEffect) :=
  List.replicate n (mirSwitchEvent 1) ++ [mirSwitchEvent 0]

private theorem replicate_append_single {α : Type} (i : Nat) (x : α) :
    List.replicate i x ++ [x] = List.replicate (i + 1) x := by
  induction i with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

private theorem length_map_u32 (elems : List Nat) :
    (elems.map (fun x => Value.scalar ⟨x, 4⟩)).length =
      elems.length :=
  List.length_map _

private theorem get?Internal_eq_getElem? {α : Type} (xs : List α) (i : Nat) :
    xs.get?Internal i = xs[i]? := rfl

private theorem get?_map_u32 {elems : List Nat} {i : Nat} (h_lt : i < elems.length) :
    (elems.map (fun x => Value.scalar ⟨x, 4⟩)).get?Internal i =
      some (.scalar ⟨elems.getD i 0, 4⟩) := by
  rw [get?Internal_eq_getElem?, List.getElem?_map, List.getElem?_eq_getElem h_lt,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h_lt]
  rfl

/-- Trace-aware `DWP mirNoCallTraceWP` proof for `fastSliceSumBody`. -/
theorem dwp_fastSliceSumBody_trace
    (elems : List Nat) (n : Nat)
    (h_n_le : n ≤ elems.length)
    (h_len_bound : elems.length < 18446744073709551616)
    (h_sum_bound : prefixSum elems n < 4294967296) :
    let args := [encodeU32Slice elems, .scalar ⟨n, 8⟩]
    DWP mirNoCallTraceWP (mirStatefulTree fastSliceSumBody args emptyMemory)
      (fun out tr =>
        tr = sliceLoopTrace n ∧
        out = .normal (.scalar ⟨prefixSum elems n, 4⟩, emptyMemory))
      [] := by
  dsimp only
  let args := [encodeU32Slice elems, .scalar ⟨n, 8⟩]
  let mkState (bb : Nat) (i : Nat) (o5 o6 : Option Value) : MachineState :=
    { frame := {
        blockIdx := bb
        stmtIdx := 0
        locals :=
          [.uninit,
           .init (encodeU32Slice elems),
           .init (.scalar ⟨n, 8⟩),
           .init (.scalar ⟨i, 8⟩),
           .init (.scalar ⟨prefixSum elems i, 4⟩),
           optSlot o5, optSlot o6]
      }
      memory := emptyMemory }
  let Inv : Nat → MachineState → List (Event MirEffect) → Prop :=
    fun r s tr =>
      ∃ (i : Nat) (temps : Option (Value × Value)),
        i + r = n ∧
        tr = List.replicate i (mirSwitchEvent 1) ∧
        s = mkState 1 i (temps.map Prod.fst) (temps.map Prod.snd)
  have h_entry :
      runMirTauToBlock 8 fastSliceSumBody 1
        (initMachineStateWithMemory fastSliceSumBody args emptyMemory) =
        some (mkState 1 0 none none) := by
    dsimp only [mkState, fastSliceSumBody, args]
    (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]); (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]); (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]); (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList])
    (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]); (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]); (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]); (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList])
    rfl
  refine dwp_of_runMirTauToBlock 8 h_entry ?_
  refine dwp_mirTree_stateful_while_ranked fastSliceSumBody 1 2 5 Inv
    (h_zero := ?_) (h_succ := ?_) n ⟨0, none, Nat.zero_add n, rfl, rfl⟩
  · rintro s tr ⟨i, temps, h_ir, rfl, rfl⟩
    have h_eq : i = n := by omega
    subst h_eq
    have h_sw :
        runMirToBinarySwitch 2 fastSliceSumBody
          (mkState 1 i (temps.map Prod.fst) (temps.map Prod.snd)) =
          some (false, 0,
                mkState 2 i (some (.scalar ⟨0, 1⟩)) (temps.map Prod.snd),
                mkState 3 i (some (.scalar ⟨0, 1⟩)) (temps.map Prod.snd)) := by
      rcases temps with _ | ⟨v5, v6⟩ <;>
        (dsimp only [mkState, fastSliceSumBody, Option.map]
         dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
         rw [evalScalarBinOp_lt_usize_of_ge (Nat.le_refl i)]
         dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
         rfl)
    refine ⟨0, _, _, h_sw, ?_⟩
    dsimp only [mirNoCallTraceWP]
    exact dwp_of_runMirTauToRet 3
      (out := .normal (.scalar ⟨prefixSum elems i, 4⟩, emptyMemory)) rfl ⟨rfl, rfl⟩
  · rintro r s tr ⟨i, temps, h_ir, rfl, rfl⟩
    have h_i_lt_n : i < n := by omega
    have h_i_lt_len : i < elems.length := Nat.lt_of_lt_of_le h_i_lt_n h_n_le
    have h_ps_le : prefixSum elems (i + 1) ≤ prefixSum elems n :=
      prefixSum_mono elems (by omega)
    have h_add_u32 : prefixSum elems i + elems.getD i 0 < 4294967296 := by
      rw [prefixSum_succ] at h_ps_le; omega
    have h_add_usize : i + 1 < 18446744073709551616 := by omega
    have h_sw :
        runMirToBinarySwitch 2 fastSliceSumBody
          (mkState 1 i (temps.map Prod.fst) (temps.map Prod.snd)) =
          some (true, 1,
                mkState 2 i (some (.scalar ⟨1, 1⟩)) (temps.map Prod.snd),
                mkState 3 i (some (.scalar ⟨1, 1⟩)) (temps.map Prod.snd)) := by
      rcases temps with _ | ⟨v5, v6⟩ <;>
        (dsimp only [mkState, fastSliceSumBody, Option.map]
         dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
         rw [evalScalarBinOp_lt_usize_of_lt h_i_lt_n]
         dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
         rfl)
    have h_body :
        runMirTauToBlock 5 fastSliceSumBody 1
          (mkState 2 i (some (.scalar ⟨1, 1⟩)) (temps.map Prod.snd)) =
          some (mkState 1 (i + 1) (some (.scalar ⟨1, 1⟩))
                  (some (.scalar ⟨elems.getD i 0, 4⟩))) := by
      rcases temps with _ | ⟨v5, v6⟩ <;>
        (dsimp only [mkState, fastSliceSumBody, encodeU32Slice, Option.map]
         (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList])
         rw [get?_map_u32 h_i_lt_len]
         dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
         (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList])
         rw [evalScalarBinOp_addUnchecked_u32 h_add_u32]
         dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
         (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList])
         rw [evalScalarBinOp_addUnchecked_usize h_add_usize]
         dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
         (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList])
         (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList])
         rfl)
    refine ⟨1, _, _, _, h_sw, h_body, ?_⟩
    dsimp only [mirNoCallTraceWP]
    exact ⟨i + 1, some (.scalar ⟨1, 1⟩, .scalar ⟨elems.getD i 0, 4⟩),
           by omega, replicate_append_single i (mirSwitchEvent 1), rfl⟩

private theorem safeSliceSum_bb2_len_step
    (elems : List Nat) (n i : Nat) (o6 : Option Value)
    (s7 s8 s9 s10 : LocalSlot) :
    stepMirFn safeSliceSumBody
      { frame := {
          blockIdx := 2
          stmtIdx := 0
          locals :=
            [.uninit,
             .init (encodeU32Slice elems),
             .init (.scalar ⟨n, 8⟩),
             .init (.scalar ⟨i, 8⟩),
             .init (.scalar ⟨prefixSum elems i, 4⟩),
             optSlot (some (.scalar ⟨1, 1⟩)),
             optSlot o6, s7, s8, s9, s10] }
        memory := emptyMemory } =
      .tau (.running
        { frame := {
            blockIdx := 2
            stmtIdx := 1
            locals :=
              [.uninit,
               .init (encodeU32Slice elems),
               .init (.scalar ⟨n, 8⟩),
               .init (.scalar ⟨i, 8⟩),
               .init (.scalar ⟨prefixSum elems i, 4⟩),
               .init (.scalar ⟨1, 1⟩),
               .init (.scalar ⟨(elems.map (fun x => Value.scalar ⟨x, 4⟩)).length, 8⟩),
               s7, s8, s9, s10] }
          memory := emptyMemory }) := by
  cases o6 <;> rfl

/-- Trace-aware `DWP mirNoCallTraceWP` proof for `safeSliceSumBody`. -/
theorem dwp_safeSliceSumBody_trace
    (elems : List Nat) (n : Nat)
    (h_n_le : n ≤ elems.length)
    (h_len_bound : elems.length < 18446744073709551616)
    (h_sum_bound : prefixSum elems n < 4294967296) :
    let args := [encodeU32Slice elems, .scalar ⟨n, 8⟩]
    DWP mirNoCallTraceWP (mirStatefulTree safeSliceSumBody args emptyMemory)
      (fun out tr =>
        tr = sliceLoopTrace n ∧
        out = .normal (.scalar ⟨prefixSum elems n, 4⟩, emptyMemory))
      [] := by
  dsimp only
  let args := [encodeU32Slice elems, .scalar ⟨n, 8⟩]
  let mkState (bb : Nat) (i : Nat)
      (o5 : Option Value)
      (rest : Option (Value × Value × Value × Value × Value)) : MachineState :=
    { frame := {
        blockIdx := bb
        stmtIdx := 0
        locals :=
          [.uninit,
           .init (encodeU32Slice elems),
           .init (.scalar ⟨n, 8⟩),
           .init (.scalar ⟨i, 8⟩),
           .init (.scalar ⟨prefixSum elems i, 4⟩),
           optSlot o5,
           optSlot (rest.map (·.1)),
           optSlot (rest.map (·.2.1)),
           optSlot (rest.map (·.2.2.1)),
           optSlot (rest.map (·.2.2.2.1)),
           optSlot (rest.map (·.2.2.2.2))]
      }
      memory := emptyMemory }
  let Inv : Nat → MachineState → List (Event MirEffect) → Prop :=
    fun r s tr =>
      ∃ (i : Nat) (o5 : Option Value)
        (rest : Option (Value × Value × Value × Value × Value)),
        i + r = n ∧
        tr = List.replicate i (mirSwitchEvent 1) ∧
        s = mkState 1 i o5 rest
  have h_entry :
      runMirTauToBlock 12 safeSliceSumBody 1
        (initMachineStateWithMemory safeSliceSumBody args emptyMemory) =
        some (mkState 1 0 none none) := by
    dsimp only [mkState, safeSliceSumBody, args, Option.map]
    (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]); (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]); (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]); (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList])
    (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]); (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]); (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]); (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList])
    (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]); (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]); (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]); (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList])
    rfl
  refine dwp_of_runMirTauToBlock 12 h_entry ?_
  refine dwp_mirTree_stateful_while_ranked safeSliceSumBody 1 2 11 Inv
    (h_zero := ?_) (h_succ := ?_) n
    ⟨0, none, none, Nat.zero_add n, rfl, rfl⟩
  · rintro s tr ⟨i, o5, rest, h_ir, rfl, rfl⟩
    have h_eq : i = n := by omega
    subst h_eq
    have h_sw :
        runMirToBinarySwitch 2 safeSliceSumBody (mkState 1 i o5 rest) =
          some (false, 0,
                mkState 2 i (some (.scalar ⟨0, 1⟩)) rest,
                mkState 5 i (some (.scalar ⟨0, 1⟩)) rest) := by
      cases o5 <;>
        (dsimp only [mkState, safeSliceSumBody]
         dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
         rw [evalScalarBinOp_lt_usize_of_ge (Nat.le_refl i)]
         dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
         rfl)
    refine ⟨0, _, _, h_sw, ?_⟩
    dsimp only [mirNoCallTraceWP]
    exact dwp_of_runMirTauToRet 3
      (out := .normal (.scalar ⟨prefixSum elems i, 4⟩, emptyMemory)) rfl ⟨rfl, rfl⟩
  · rintro r s tr ⟨i, o5, rest, h_ir, rfl, rfl⟩
    have h_i_lt_n : i < n := by omega
    have h_i_lt_len : i < elems.length := Nat.lt_of_lt_of_le h_i_lt_n h_n_le
    have h_ps_le : prefixSum elems (i + 1) ≤ prefixSum elems n :=
      prefixSum_mono elems (by omega)
    have h_add_u32 : prefixSum elems i + elems.getD i 0 < 4294967296 := by
      rw [prefixSum_succ] at h_ps_le; omega
    have h_add_usize : i + 1 < 18446744073709551616 := by omega
    have h_sw :
        runMirToBinarySwitch 2 safeSliceSumBody (mkState 1 i o5 rest) =
          some (true, 1,
                mkState 2 i (some (.scalar ⟨1, 1⟩)) rest,
                mkState 5 i (some (.scalar ⟨1, 1⟩)) rest) := by
      cases o5 <;>
        (dsimp only [mkState, safeSliceSumBody]
         dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
         rw [evalScalarBinOp_lt_usize_of_lt h_i_lt_n]
         dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
         rfl)
    have h_body :
        runMirTauToBlock 11 safeSliceSumBody 1
          (mkState 2 i (some (.scalar ⟨1, 1⟩)) rest) =
          some (mkState 1 (i + 1) (some (.scalar ⟨1, 1⟩))
                  (some (.scalar ⟨elems.length, 8⟩,
                         .scalar ⟨1, 1⟩,
                         .scalar ⟨elems.getD i 0, 4⟩,
                         .aggregate 0
                           [.scalar ⟨prefixSum elems (i + 1), 4⟩, .scalar ⟨0, 1⟩],
                         .scalar ⟨0, 1⟩))) := by
      rcases rest with _ | ⟨v6, v7, v8, v9, v10⟩ <;>
        (dsimp only [mkState, Option.map]
         rw [runMirTauToBlock_succ]
         rw [safeSliceSum_bb2_len_step]
         dsimp only [safeSliceSumBody, encodeU32Slice]
         (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList])
         rw [length_map_u32 elems, evalScalarBinOp_lt_usize_of_lt h_i_lt_len]
         dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
         (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList])
         (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList])
         rw [get?_map_u32 h_i_lt_len]
         dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
         (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList])
         rw [evalScalarBinOp_addWithOverflow_u32 h_add_u32]
         dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
         (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList])
         (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList])
         (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList])
         (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList])
         rw [evalScalarBinOp_add_usize h_add_usize]
         dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
         (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList])
         (rw [runMirTauToBlock_succ]; dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList])
         rfl)
    refine ⟨1, _, _, _, h_sw, h_body, ?_⟩
    dsimp only [mirNoCallTraceWP]
    exact ⟨i + 1, _, _, by omega,
           replicate_append_single i (mirSwitchEvent 1), rfl⟩

/--
Pillar 4 flagship theorem: for ANY symbolic slice `elems : List Nat` and prefix
length `n ≤ elems.length` whose sum fits in `u32`, the optimized `unsafe`
`fastSliceSumBody` (eliding bounds & overflow `TerminatorKind.assert`s and using
`BinOp.addUnchecked`) literally refines AND equals `safeSliceSumBody` in
Layer 1A (`ITree.toPartial`), and both loops terminate without UB, panics, or
aborts (`MirTerminatesAndNoUB`).
-/
theorem fastSliceSum_refines_and_equiv_safeSliceSum
    (elems : List Nat) (n : Nat)
    (h_n_le : n ≤ elems.length)
    (h_len_bound : elems.length < 18446744073709551616)
    (h_sum_bound : prefixSum elems n < 4294967296) :
    let args := [encodeU32Slice elems, .scalar ⟨n, 8⟩]
    (mirStatefulTree fastSliceSumBody args emptyMemory).toPartial ≤
      (mirStatefulTree safeSliceSumBody args emptyMemory).toPartial ∧
    (mirStatefulTree fastSliceSumBody args emptyMemory).toPartial =
      (mirStatefulTree safeSliceSumBody args emptyMemory).toPartial ∧
    MirTerminatesAndNoUB fastSliceSumBody args emptyMemory ∧
    MirTerminatesAndNoUB safeSliceSumBody args emptyMemory :=
  verifyTraceStatefulEquivViaPureModel
    (dwp_fastSliceSumBody_trace elems n h_n_le h_len_bound h_sum_bound)
    (dwp_safeSliceSumBody_trace elems n h_n_le h_len_bound h_sum_bound)

/-! ### Part 4B: Branchless Arithmetic vs. Branching `switchInt` (`mirObsErasedStatefulTree`) -/

/--
Branching `CapturedMir` body (`1` `switchInt` event):
`fn select_double_branching(flag: bool, x: u32) -> u32 { if flag { x + x } else { 0 } }`.
-/
def branchingSelectDoubleBody : CapturedMir :=
  mkMirBody "test::select_double_branching" 2
    [mkDecl .mut u32MirTy,
     mkDecl .not boolMirTy,
     mkDecl .not u32MirTy]
    [ -- bb0: switchInt(_1) [0 -> bb2, otherwise -> bb1]
      { statements := []
        terminator := mkTerm (.switchInt (.copy (locPlace 1))
          { branches := [(0, 2)], otherwise := 1 })
        isCleanup := false },
      -- bb1: _0 = _2 + _2; return
      { statements :=
          [mkStmt (.assign (locPlace 0)
            (.binaryOp .add (.copy (locPlace 2)) (.copy (locPlace 2))))]
        terminator := mkTerm .return_
        isCleanup := false },
      -- bb2: _0 = 0; return
      { statements :=
          [mkStmt (.assign (locPlace 0) (.use (u32ConstOp 0)))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/--
Branchless `CapturedMir` body (`0` `switchInt` events):
`fn select_double_branchless(flag: bool, x: u32) -> u32 { (flag as u32) * (x + x) }`.
-/
def branchlessMulDoubleBody : CapturedMir :=
  mkMirBody "test::select_double_branchless" 2
    [mkDecl .mut u32MirTy,
     mkDecl .not boolMirTy,
     mkDecl .not u32MirTy,
     mkDecl .mut u32MirTy,
     mkDecl .mut u32MirTy]
    [ { statements :=
          [mkStmt (.storageLive 3),
           mkStmt (.storageLive 4),
           mkStmt (.assign (locPlace 3)
             (.cast .intToInt (.copy (locPlace 1)) u32MirTy)),
           mkStmt (.assign (locPlace 4)
             (.binaryOp .add (.copy (locPlace 2)) (.copy (locPlace 2)))),
           mkStmt (.assign (locPlace 0)
             (.binaryOp .mul (.copy (locPlace 3)) (.copy (locPlace 4))))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/--
Branch-observation-erased Layer 1A equivalence (`mirObsErasedStatefulTree` and
`eraseTracePartial`) between `branchlessMulDoubleBody` (`0` `switchInt`s) and
`branchingSelectDoubleBody` (`1` `switchInt`) over all symbolic `flag : Bool`
and `x < 1000`.
-/
theorem branchlessMulDouble_obsErased_equiv_branchingSelectDouble
    (flag : Bool) (x : Nat) (hx : x < 1000) :
    let args := [.scalar (boolToScalar flag), .scalar ⟨x, 4⟩]
    (mirObsErasedStatefulTree branchlessMulDoubleBody args emptyMemory).toPartial ≤
      (mirObsErasedStatefulTree branchingSelectDoubleBody args emptyMemory).toPartial ∧
    (mirObsErasedStatefulTree branchlessMulDoubleBody args emptyMemory).toPartial =
      (mirObsErasedStatefulTree branchingSelectDoubleBody args emptyMemory).toPartial ∧
    eraseTracePartial (mirStatefulTree branchlessMulDoubleBody args emptyMemory).toPartial =
      eraseTracePartial (mirStatefulTree branchingSelectDoubleBody args emptyMemory).toPartial ∧
    MirTerminatesAndNoUB branchlessMulDoubleBody args emptyMemory ∧
    MirTerminatesAndNoUB branchingSelectDoubleBody args emptyMemory := by
  dsimp only
  have h_2x : x + x < 4294967296 := by omega
  let expectedVal : Value := .scalar ⟨if flag then x + x else 0, 4⟩
  refine verifyObsErasedStatefulEquivByTransPlan
    (implPlan := .ret 6)
    (specPlan := .splitBranch (.ret 2) (.ret 2) 1)
    (expectedRet := expectedVal)
    (expectedMem := emptyMemory)
    ?_ ?_
  · cases flag with
    | false =>
      have h_mul0 : 0 * (x + x) < 4294967296 := by omega
      have h_0_lt : 0 < 4294967296 := by decide
      rw [wpTransPlan]
      dsimp only [branchlessMulDoubleBody, boolToScalar, expectedVal]
      dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
      rw [scalarModulus_four, wrapScalarBits_of_lt h_0_lt,
          evalScalarBinOp_add_u32 h_2x]
      dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
      rw [evalScalarBinOp_mul_u32 h_mul0, Nat.zero_mul]
      dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
      try rfl
    | true =>
      have h_mul1 : 1 * (x + x) < 4294967296 := by omega
      have h_1_lt : 1 < 4294967296 := by decide
      rw [wpTransPlan]
      dsimp only [branchlessMulDoubleBody, boolToScalar, expectedVal]
      dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
      rw [scalarModulus_four, wrapScalarBits_of_lt h_1_lt,
          evalScalarBinOp_add_u32 h_2x]
      dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
      rw [evalScalarBinOp_mul_u32 h_mul1, Nat.one_mul]
      dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
      try rfl
  · cases flag with
    | false =>
      rw [wpTransPlan]
      dsimp only [branchingSelectDoubleBody, boolToScalar, expectedVal]
      dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
      refine ⟨(fun h => by cases h), fun _ => ?_⟩
      rw [wpTransPlan]
      rfl
    | true =>
      rw [wpTransPlan]
      dsimp only [branchingSelectDoubleBody, boolToScalar, expectedVal]
      dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
      refine ⟨fun _ => ?_, (fun h => by cases h)⟩
      rw [wpTransPlan]
      dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
      rw [evalScalarBinOp_add_u32 h_2x]
      dsimp only [evalPlanToJoin, joinPlanMemConsistent, runMirToBinarySwitch, inspectBinarySwitch, runMirToBlock, runMirTauToRet, initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, stepMirFn, stepMirState, wpCoalBounded, MirStepNode.step, MirStepNode.retNormal, evalStmt, advanceStmt, evalRvalue_len_eq, evalRvalue, evalOperand, evalOperands, evalConstValue, readProjectedValue, readProjectedValue_index, evalPlaceWrite, writePlaceValue, writeProjectedValue, operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy, tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, evalTerminator, lookupSwitchTarget, applyUnwindAction, ProvenancePtr.tag, optSlot, lookupBorrow, appendProjections, stripTransparentProjections, projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or, Option.getD, List.length, List.set, List.map, BEq.beq, instBEqOfDecidableEq, get?, set?, length, emptyMemory, zipLocalSlots, zipSymLocals, zipSymSlot, zipSymVal, zipSymValList, SymLocals.ofLocalSlots, SymLocals.denote, SymSlot.ofLocalSlot, SymSlot.denote, SymVal.ofValue, SymVal.ofValueList, SymVal.denote, SymVal.denoteList]
      try rfl

end Anneal.FunctionalTranslationEquivTests
