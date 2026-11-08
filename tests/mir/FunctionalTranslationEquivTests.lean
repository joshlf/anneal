import Anneal.FunctionalTranslation

namespace Anneal.FunctionalTranslationEquivTests

open Trusted.Effect
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.ITreeWP
open Anneal.FunctionalTranslation

/-!
Kernel-checked Pillar 4 (program-to-program Layer 1A refinement `≤` and `=`) test
suite for `Anneal.FunctionalTranslation` over `V2026_06_01` `CapturedMir` bodies
(pillars 1–3 are exercised in `FunctionalTranslationTests`):

- Literal Layer 1A `ITree.toPartial` refinement (`≤`), behavioral equality
  (`=`), and `MirTerminatesAndNoUB` between `fastSliceSumBody` (`unsafe`
  unchecked indexing + `BinOp.addUnchecked`) and `safeSliceSumBody` (checked
  `Rvalue.len` bounds `TerminatorKind.assert` + `BinOp.addWithOverflow`
  overflow `TerminatorKind.assert`) over arbitrary symbolic `elems : List Nat`
  and `n ≤ elems.length` via `dwp_mirTree_stateful_while_ranked` and
  `verifyTraceStatefulEquivViaPureModel`.
- Branch-observation-erased Layer 1A equivalence (`mirObsErasedStatefulTree`
  and `eraseTracePartial`) between `branchlessMulDoubleBody` (`0` `switchInt`
  events) and `branchingSelectDoubleBody` (`1` `switchInt` event) via
  `verifyObsErasedStatefulEquivByTransPlan`.
-/

/-! ## Shared `V2026_06_01` `CapturedMir` AST Builders and Scalar Simplification Lemmas -/

@[reducible] private def boolMirTy : Ty := { kind := .bool, layoutIdx := 0 }
@[reducible] private def u32MirTy : Ty := { kind := .uint .u32, layoutIdx := 0 }
@[reducible] private def usizeMirTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
@[reducible] private def checkedU32MirTy : Ty :=
  { kind := .tuple [.uint .u32, .bool], layoutIdx := 0 }
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

/-- Non-dead local slot helper (`none ↦ .uninit`, `some v ↦ .init v`). -/
@[reducible] private def optSlot : Option Value → LocalSlot
  | none => .uninit
  | some v => .init v

/-- Continue a silent running step with `k` (`none` for any other step node). -/
private def tauThen (k : MachineState → Option MachineState) : MirStepNode → Option MachineState
  | .tau (.running s') => k s'
  | _ => none

/--
`tauThen` fires only on a concrete `.tau (.running s')`: used as a `dsimp` lemma instead
of unfolding `tauThen`, so a stuck step never exposes the continuation under a binder.
-/
private theorem tauThen_tau (k : MachineState → Option MachineState) (s' : MachineState) :
    tauThen k (.tau (.running s')) = k s' := rfl

/-- `_1[_3]` projection read, by `rfl` (a `dsimp` lemma for the slice-sum loop bodies). -/
private theorem readProjectedValue_index
    (locals : List LocalSlot) (fields : List Value) (idxLocal : Local) :
    readProjectedValue locals (.aggregate 0 fields) [.index idxLocal] =
      match get? locals idxLocal with
      | .some (.init (.scalar sc)) =>
        match get? fields sc.bits with
        | .some elemVal => .ok elemVal
        | .none => .ub
      | _ => .ub := rfl

/--
`runMirTauToBlock` unfolding that keeps the continuation folded until the step
node is a concrete `.tau (.running s')` (see `tauThen_tau`).
-/
private theorem runMirTauToBlock_succ
    (fuel : Nat) (body : CapturedMir) (targetBlock : BasicBlockIdx) (s : MachineState) :
    runMirTauToBlock (fuel + 1) body targetBlock s =
      if Nat.beq s.frame.blockIdx targetBlock && Nat.beq s.frame.stmtIdx 0 then some s
      else tauThen (runMirTauToBlock fuel body targetBlock) (stepMirFn body s) := rfl

private theorem evalScalarBinOp_add_usize
    {a b : Nat} {locals : List LocalSlot} {mem : Memory}
    (h_lt : a + b < 18446744073709551616) :
    evalScalarBinOp .add ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨a + b, 8⟩) locals mem := by
  unfold evalScalarBinOp; dsimp only
  rw [show wrapScalarBits (a.add b) (scalarModulus 8) = a + b from wrapScalarBits_of_lt h_lt]

private theorem evalScalarBinOp_addUnchecked_u32
    {a b : Nat} {locals : List LocalSlot} {mem : Memory}
    (h_lt : a + b < 4294967296) :
    evalScalarBinOp .addUnchecked ⟨a, 4⟩ ⟨b, 4⟩ locals mem false =
      .ok (.scalar ⟨a + b, 4⟩) locals mem := by
  unfold evalScalarBinOp; dsimp only
  rw [show Nat.ble (scalarModulus 4) (a.add b) = false from nat_ble_eq_false_of_lt h_lt]
  rfl

private theorem evalScalarBinOp_addUnchecked_usize
    {a b : Nat} {locals : List LocalSlot} {mem : Memory}
    (h_lt : a + b < 18446744073709551616) :
    evalScalarBinOp .addUnchecked ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨a + b, 8⟩) locals mem := by
  unfold evalScalarBinOp; dsimp only
  rw [show Nat.ble (scalarModulus 8) (a.add b) = false from nat_ble_eq_false_of_lt h_lt]
  rfl

private theorem evalScalarBinOp_addWithOverflow_u32
    {a b : Nat} {locals : List LocalSlot} {mem : Memory}
    (h_lt : a + b < 4294967296) :
    evalScalarBinOp .addWithOverflow ⟨a, 4⟩ ⟨b, 4⟩ locals mem false =
      .ok (.aggregate 0 [.scalar ⟨a + b, 4⟩, .scalar ⟨0, 1⟩]) locals mem := by
  unfold evalScalarBinOp; dsimp only
  rw [show wrapScalarBits (a.add b) (scalarModulus 4) = a + b from wrapScalarBits_of_lt h_lt,
      show Nat.ble (scalarModulus 4) (a.add b) = false from nat_ble_eq_false_of_lt h_lt]

private theorem evalScalarBinOp_lt_usize_of_lt
    {a b : Nat} {locals : List LocalSlot} {mem : Memory}
    (h_lt : a < b) :
    evalScalarBinOp .lt ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨1, 1⟩) locals mem := by
  unfold evalScalarBinOp; dsimp only
  rw [nat_ble_eq_false_of_lt h_lt]; rfl

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

/-- The symbolic `elems[i]` read: the only non-definitional step of `_1[_3]`. -/
private theorem get?_map_u32 {elems : List Nat} {i : Nat} (h_lt : i < elems.length) :
    (elems.map (fun x => Value.scalar ⟨x, 4⟩)).get?Internal i =
      some (.scalar ⟨elems.getD i 0, 4⟩) := by
  show (elems.map _)[i]? = _
  simp [h_lt]

@[reducible] private def fastSliceSumMkState
    (elems : List Nat) (n : Nat) (bb : Nat) (i : Nat) (o5 o6 : Option Value) : MachineState :=
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

private theorem fastSliceSum_header_switch_raw
    (elems : List Nat) (n i : Nat) (o5 o6 : Option Value) :
    runMirToBinarySwitch 2 fastSliceSumBody (fastSliceSumMkState elems n 1 i o5 o6) =
      let sc := boolToScalar (!Nat.ble n i)
      some (!sc.bits.beq 0, sc.bits,
            fastSliceSumMkState elems n 2 i (some (.scalar sc)) o6,
            fastSliceSumMkState elems n 3 i (some (.scalar sc)) o6) := by
  cases o5 <;> rfl

/--
One loop-body pass `bb2 → bb1`, by `dsimp` plus the four non-definitional rewrites.
`dsimp` (not `simp`) on purpose: `simp [f]` realizes `f`'s equation lemmas in this test
module, which `trusted/audit/check_trusted.py` then rejects as foreign dependencies of the
theory modules that realize the same lemmas.
-/
private theorem fastSliceSum_h_body
    (elems : List Nat) (n i : Nat) (o6 : Option Value)
    (h_i_lt_len : i < elems.length)
    (h_add_u32 : prefixSum elems i + elems.getD i 0 < 4294967296)
    (h_add_usize : i + 1 < 18446744073709551616) :
    runMirTauToBlock 5 fastSliceSumBody 1
      (fastSliceSumMkState elems n 2 i (some (.scalar ⟨1, 1⟩)) o6) =
      some (fastSliceSumMkState elems n 1 (i + 1) (some (.scalar ⟨1, 1⟩))
              (some (.scalar ⟨elems.getD i 0, 4⟩))) := by
  cases o6 <;>
    repeat' first
      | dsimp only [runMirTauToBlock_succ, tauThen_tau, fastSliceSumMkState, fastSliceSumBody,
          encodeU32Slice, optSlot, stepMirFn, MirStepNode.step, evalStmt,
          advanceStmt, evalRvalue, evalOperand, evalConstValue, readProjectedValue,
          readProjectedValue_index, evalPlaceWrite, operandIsSigned, operandTy, placeTy,
          tyIsSigned, evalTerminator, applyUnwindAction, Option.getD, GetElem?.getElem?,
          List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq,
          instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and,
          List.length, List.set, BEq.beq, get?, set?, length, emptyMemory,
          invalidateConflictingBorrows, prefixSum_succ]
      | rw [get?_map_u32 h_i_lt_len]
      | rw [evalScalarBinOp_addUnchecked_u32 h_add_u32]
      | rw [evalScalarBinOp_addUnchecked_usize h_add_usize]

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
  refine dwp_of_runMirTauToBlock (targetBlock := 1) 8
    (s' := fastSliceSumMkState elems n 1 0 none none) rfl ?_
  refine dwp_mirTree_stateful_while_ranked fastSliceSumBody 1 2 5
    (fun r s tr =>
      ∃ (i : Nat) (o5 o6 : Option Value),
        i + r = n ∧
        tr = List.replicate i (mirSwitchEvent 1) ∧
        s = fastSliceSumMkState elems n 1 i o5 o6)
    (h_zero := ?_) (h_succ := ?_) n ⟨0, none, none, Nat.zero_add n, rfl, rfl⟩
  · rintro s tr ⟨i, o5, o6, h_ir, rfl, rfl⟩
    obtain rfl : i = n := by omega
    refine ⟨0, _, _, by
      rw [fastSliceSum_header_switch_raw, nat_ble_eq_true_of_le (Nat.le_refl i)]; rfl, ?_⟩
    exact dwp_of_runMirTauToRet 3
      (out := .normal (.scalar ⟨prefixSum elems i, 4⟩, emptyMemory)) rfl ⟨rfl, rfl⟩
  · rintro r s tr ⟨i, o5, o6, h_ir, rfl, rfl⟩
    have h_ps_le : prefixSum elems i + elems.getD i 0 ≤ prefixSum elems n :=
      prefixSum_mono elems (show i + 1 ≤ n by omega)
    refine ⟨1, _, _, _, by
      rw [fastSliceSum_header_switch_raw, nat_ble_eq_false_of_lt (show i < n by omega)]; rfl,
      fastSliceSum_h_body elems n i o6 (by omega) (by omega) (by omega), ?_⟩
    exact ⟨i + 1, _, _, by omega, List.replicate_succ'.symm, rfl⟩

@[reducible] private def safeSliceSumMkState
    (elems : List Nat) (n : Nat) (bb : Nat) (i : Nat)
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

/--
`bb2` `Len(_1)` step by `rfl` (sparing `dsimp` the `evalPlaceLen` unfolding); the
slice length is left as `(elems.map _).length` for `List.length_map`.
-/
private theorem safeSliceSum_bb2_len_step (elems : List Nat) (n i : Nat)
    (rest : Option (Value × Value × Value × Value × Value)) :
    stepMirFn safeSliceSumBody (safeSliceSumMkState elems n 2 i (some (.scalar ⟨1, 1⟩)) rest) =
      .tau (.running
        { frame :=
            { blockIdx := 2, stmtIdx := 1,
              locals :=
                (safeSliceSumMkState elems n 2 i (some (.scalar ⟨1, 1⟩)) rest).frame.locals.set 6
                  (.init (.scalar ⟨(elems.map (fun x => Value.scalar ⟨x, 4⟩)).length, 8⟩)) }
          memory := emptyMemory }) := by
  rcases rest with _ | ⟨_, _, _, _, _⟩ <;> rfl

private theorem safeSliceSum_header_switch_raw
    (elems : List Nat) (n i : Nat) (o5 : Option Value)
    (rest : Option (Value × Value × Value × Value × Value)) :
    runMirToBinarySwitch 2 safeSliceSumBody (safeSliceSumMkState elems n 1 i o5 rest) =
      let sc := boolToScalar (!Nat.ble n i)
      some (!sc.bits.beq 0, sc.bits,
            safeSliceSumMkState elems n 2 i (some (.scalar sc)) rest,
            safeSliceSumMkState elems n 5 i (some (.scalar sc)) rest) := by
  cases o5 <;> rfl

private theorem safeSliceSum_h_body
    (elems : List Nat) (n i : Nat)
    (rest : Option (Value × Value × Value × Value × Value))
    (h_i_lt_len : i < elems.length)
    (h_add_u32 : prefixSum elems i + elems.getD i 0 < 4294967296)
    (h_add_usize : i + 1 < 18446744073709551616) :
    runMirTauToBlock 11 safeSliceSumBody 1
      (safeSliceSumMkState elems n 2 i (some (.scalar ⟨1, 1⟩)) rest) =
      some (safeSliceSumMkState elems n 1 (i + 1) (some (.scalar ⟨1, 1⟩))
              (some (.scalar ⟨elems.length, 8⟩,
                     .scalar ⟨1, 1⟩,
                     .scalar ⟨elems.getD i 0, 4⟩,
                     .aggregate 0
                       [.scalar ⟨prefixSum elems (i + 1), 4⟩, .scalar ⟨0, 1⟩],
                     .scalar ⟨0, 1⟩))) := by
  rcases rest with _ | ⟨_, _, _, _, _⟩ <;>
    rw [runMirTauToBlock_succ, safeSliceSum_bb2_len_step, List.length_map] <;>
    repeat' first
      | dsimp only [runMirTauToBlock_succ, tauThen_tau, safeSliceSumMkState, safeSliceSumBody,
          encodeU32Slice, Option.map, optSlot, stepMirFn, MirStepNode.step, evalStmt,
          advanceStmt, evalRvalue, evalOperand, evalConstValue, readProjectedValue,
          readProjectedValue_index, evalPlaceWrite, operandIsSigned, operandTy, placeTy,
          tyIsSigned, evalTerminator, applyUnwindAction, Option.getD, GetElem?.getElem?,
          List.get?Internal, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq,
          instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and,
          List.length, List.set, BEq.beq, get?, set?, length, emptyMemory,
          invalidateConflictingBorrows, prefixSum_succ]
      | rw [evalScalarBinOp_lt_usize_of_lt h_i_lt_len]
      | rw [get?_map_u32 h_i_lt_len]
      | rw [evalScalarBinOp_addWithOverflow_u32 h_add_u32]
      | rw [evalScalarBinOp_add_usize h_add_usize]

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
  refine dwp_of_runMirTauToBlock (targetBlock := 1) 12
    (s' := safeSliceSumMkState elems n 1 0 none none) rfl ?_
  refine dwp_mirTree_stateful_while_ranked safeSliceSumBody 1 2 11
    (fun r s tr =>
      ∃ (i : Nat) (o5 : Option Value)
        (rest : Option (Value × Value × Value × Value × Value)),
        i + r = n ∧
        tr = List.replicate i (mirSwitchEvent 1) ∧
        s = safeSliceSumMkState elems n 1 i o5 rest)
    (h_zero := ?_) (h_succ := ?_) n ⟨0, none, none, Nat.zero_add n, rfl, rfl⟩
  · rintro s tr ⟨i, o5, rest, h_ir, rfl, rfl⟩
    obtain rfl : i = n := by omega
    refine ⟨0, _, _, by
      rw [safeSliceSum_header_switch_raw, nat_ble_eq_true_of_le (Nat.le_refl i)]; rfl, ?_⟩
    exact dwp_of_runMirTauToRet 3
      (out := .normal (.scalar ⟨prefixSum elems i, 4⟩, emptyMemory)) rfl ⟨rfl, rfl⟩
  · rintro r s tr ⟨i, o5, rest, h_ir, rfl, rfl⟩
    have h_ps_le : prefixSum elems i + elems.getD i 0 ≤ prefixSum elems n :=
      prefixSum_mono elems (show i + 1 ≤ n by omega)
    refine ⟨1, _, _, _, by
      rw [safeSliceSum_header_switch_raw, nat_ble_eq_false_of_lt (show i < n by omega)]; rfl,
      safeSliceSum_h_body elems n i rest (by omega) (by omega) (by omega), ?_⟩
    exact ⟨i + 1, _, _, by omega, List.replicate_succ'.symm, rfl⟩

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
  have h_2x : wrapScalarBits (x + x) (scalarModulus 4) = x + x :=
    wrapScalarBits_of_lt (show x + x < 4294967296 by omega)
  refine verifyObsErasedStatefulEquivByTransPlan
    (implPlan := .ret)
    (specPlan := .splitBranch .ret .ret)
    (expectedRet := .scalar ⟨if flag then x + x else 0, 4⟩)
    (expectedMem := emptyMemory)
    ?_ ?_ <;> cases flag <;> rw [wpTransPlan]
  · -- `branchlessMulDoubleBody`, `flag = false`: `(0 : u32) * (x + x)`
    change Outcome.normal (Value.scalar ⟨wrapScalarBits
      (0 * wrapScalarBits (x + x) (scalarModulus 4)) (scalarModulus 4), 4⟩, emptyMemory) = _
    rw [h_2x, Nat.zero_mul]
    rfl
  · -- `branchlessMulDoubleBody`, `flag = true`: `(1 : u32) * (x + x)`
    change Outcome.normal (Value.scalar ⟨wrapScalarBits
      (1 * wrapScalarBits (x + x) (scalarModulus 4)) (scalarModulus 4), 4⟩, emptyMemory) = _
    rw [h_2x, Nat.one_mul, h_2x]
    rfl
  · -- `branchingSelectDoubleBody`, `flag = false`: `bb2` returns `0`
    exact ⟨(fun h => by cases h), fun _ => by rw [wpTransPlan]; rfl⟩
  · -- `branchingSelectDoubleBody`, `flag = true`: `bb1` returns `x + x`
    refine ⟨fun _ => ?_, (fun h => by cases h)⟩
    rw [wpTransPlan]
    change Outcome.normal
      (Value.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, emptyMemory) = _
    rw [h_2x]
    rfl

end Anneal.FunctionalTranslationEquivTests
