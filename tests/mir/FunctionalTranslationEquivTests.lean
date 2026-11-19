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

@[reducible] def boolMirTy : Ty := { kind := .bool, layoutIdx := 0 }
@[reducible] def u32MirTy : Ty := { kind := .uint .u32, layoutIdx := 0 }
@[reducible] def usizeMirTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
@[reducible] def checkedU32MirTy : Ty :=
  { kind := .tuple [.uint .u32, .bool], layoutIdx := 0 }
@[reducible] private def u32ArrayMirTy : Ty :=
  { kind := .array (.uint .u32) 0, layoutIdx := 0 }

@[reducible] def u32ConstOp (n : Nat) : Operand :=
  .constant { ty := u32MirTy, val := .scalar (.int { bits := n, sizeBytes := 4 }) }

@[reducible] private def usizeConstOp (n : Nat) : Operand :=
  .constant { ty := usizeMirTy, val := .scalar (.int { bits := n, sizeBytes := 8 }) }

@[reducible] def defaultU32Layout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 4 }
  backendRepr := .memory
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

@[reducible] def defaultFnAbi : FnAbi := {
  args := []
  ret := { layout := defaultU32Layout, mode := .direct }
  conv := .rust
  canUnwind := false
}

@[reducible] def mkDecl (mutability : Mutability) (ty : Ty) : LocalDecl :=
  { mutability, ty, debugName := none }

@[reducible] def mkStmt (kind : StatementKind) : Statement :=
  { kind, span := "FunctionalTranslationTests.lean" }

@[reducible] def mkTerm (kind : TerminatorKind) : Terminator :=
  { kind, span := "FunctionalTranslationTests.lean" }

@[reducible] def mkMirBody
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

@[reducible] def locPlace (idx : Local) : Place :=
  { local_ := idx, projection := [] }

/-- Non-dead local slot helper (`none ↦ .uninit`, `some v ↦ .init v`). -/
@[reducible] def optSlot : Option Value → LocalSlot
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
    ∀ {i j : Nat}, i ≤ j → prefixSum elems i ≤ prefixSum elems j
  | _, _, .refl => Nat.le_refl _
  | _, _ + 1, .step h => by
    have := prefixSum_mono elems h
    rw [prefixSum_succ]; omega

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
          instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or,
          List.length, List.set, BEq.beq, get?, set?, length, emptyMemory,
          invalidateConflictingBorrows, validateLoadedValue, resolveProjectedTy, elemTyOf,
          prefixSum_succ]
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
          instDecidableEqNat, Nat.ble, Nat.beq, Bool.decEq, instDecidableEqBool, Bool.and, Bool.or,
          List.length, List.set, BEq.beq, get?, set?, length, emptyMemory,
          invalidateConflictingBorrows, validateLoadedValue, resolveProjectedTy, elemTyOf,
          prefixSum_succ]
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

/-! ## Suite 5: Gap-Preserving `ContextEquiv` and Gap-Free `ProgramEquiv`

Kernel-checked positive and negative non-vacuity canaries for
`Anneal.Refinement.ContextEquiv` and `Anneal.Pass.runMirWithGap` on concrete
`V2026_06_01` `CapturedMir` bodies:

- two callers (`callerBranchingBody`, `callerRefactoredBody`) that agree on the
  supported branch up to refactored arithmetic and both call the shared
  unmodeled helper `unsupportedHelperBody` on the other branch;
- `ContextEquiv` on **all** inputs with no gap-freedom proof for the helper,
  upgraded by `ContextEquivOn.toProgramEquivOn` to gap-free `ProgramEquivOn` on
  the inputs where the baseline is proved gap-free;
- rejected refactorings: a newly introduced gap, mismatched gap tags, and UB
  confused with a normal return or with a panic.
-/

section GapPreservingCanaries

open Trusted.Refinement
open Anneal.Refinement
open Anneal.Pass

/-- Function-item operand naming the callee `defPath`. -/
def fnItemOp (defPath : DefPath) : Operand :=
  .constant { ty := { kind := .fnDef defPath [], layoutIdx := 0 }, val := .zeroSized }

/--
Shared helper callee whose MIR phase is not a modeled runtime phase, so
`stepMirFn` steps to `MirStepNode.unsupported` as soon as it is entered:
`fn unmodeled_helper(x: u32) -> u32 { /* unmodeled */ }`.
-/
def unsupportedHelperBody : CapturedMir :=
  { mkMirBody "test::unmodeled_helper" 1
      [mkDecl .mut u32MirTy, mkDecl .not u32MirTy]
      [ { statements := [mkStmt (.assign (locPlace 0) (.use (.copy (locPlace 1))))]
          terminator := mkTerm .return_
          isCleanup := false } ] with
    phase := .other "unmodeled" }

/-- A second unmodeled helper with a different `DefPath` (a different gap site). -/
def otherUnsupportedHelperBody : CapturedMir :=
  { unsupportedHelperBody with defPath := "test::other_unmodeled_helper" }

/-- `switchInt(_1) [0 -> bb2, otherwise -> bb1]`: `flag = true` runs `bb1`. -/
def flagSwitchBlock : BasicBlockData :=
  { statements := []
    terminator := mkTerm (.switchInt (.copy (locPlace 1))
      { branches := [(0, 2)], otherwise := 1 })
    isCleanup := false }

/-- `_0 = helper(copy _2) -> bb3`. -/
def helperCallBlock (helper : DefPath) : BasicBlockData :=
  { statements := []
    terminator := mkTerm
      (.call (fnItemOp helper) [.copy (locPlace 2)] (locPlace 0) (some 3) .continue_)
    isCleanup := false }

/-- `return`. -/
def returnBlock : BasicBlockData :=
  { statements := [], terminator := mkTerm .return_, isCleanup := false }

/--
Baseline caller:
`fn caller(flag: bool, x: u32) -> u32 { if flag { x + x } else { unmodeled_helper(x) } }`.
-/
def callerBranchingBody : CapturedMir :=
  mkMirBody "test::caller_branching" 2
    [mkDecl .mut u32MirTy, mkDecl .not boolMirTy, mkDecl .not u32MirTy]
    [ flagSwitchBlock,
      -- bb1: _0 = _2 + _2; return
      { statements :=
          [mkStmt (.assign (locPlace 0)
            (.binaryOp .add (.copy (locPlace 2)) (.copy (locPlace 2))))]
        terminator := mkTerm .return_
        isCleanup := false },
      helperCallBlock "test::unmodeled_helper",
      returnBlock ]

/--
Refactored caller (different arithmetic, an extra temporary, more steps):
`fn caller(flag: bool, x: u32) -> u32 { if flag { let t = x * 2; t } else { helper(x) } }`
where `helper` is `unmodeled_helper`.
-/
def callerRefactoredBody : CapturedMir :=
  mkMirBody "test::caller_refactored" 2
    [mkDecl .mut u32MirTy, mkDecl .not boolMirTy, mkDecl .not u32MirTy,
     mkDecl .mut u32MirTy]
    [ flagSwitchBlock,
      -- bb1: StorageLive(_3); _3 = _2 * 2; _0 = copy _3; return
      { statements :=
          [mkStmt (.storageLive 3),
           mkStmt (.assign (locPlace 3)
            (.binaryOp .mul (.copy (locPlace 2)) (u32ConstOp 2))),
           mkStmt (.assign (locPlace 0) (.use (.copy (locPlace 3))))]
        terminator := mkTerm .return_
        isCleanup := false },
      helperCallBlock "test::unmodeled_helper",
      returnBlock ]

/-- Argument list of the query `(flag, x)`. -/
def callerArgs (q : Bool × Nat) : List Value :=
  [.scalar (boolToScalar q.1), .scalar ⟨q.2, 4⟩]

/-- Callee bodies linked into every caller run. -/
def linkedHelpers : List CapturedMir :=
  [unsupportedHelperBody, otherUnsupportedHelperBody]

/-- Bounded gap-aware run of a caller on the query `(flag, x)`. -/
def callerRun (body : CapturedMir) (fuel : Nat) (q : Bool × Nat) :
    OutcomeWithGap ExecFault (GapTag DefPath) MirReturn :=
  runMirWithGap MirCallEnv.unresolved linkedHelpers body fuel (callerArgs q)

/-- Fuel-free gap-aware semantics of a caller over queries `(flag, x)`. -/
def callerGapSem (body : CapturedMir) :
    GapSem (Bool × Nat) ExecFault (GapTag DefPath) MirReturn :=
  fun q => mirGapBehaviors MirCallEnv.unresolved linkedHelpers body (callerArgs q)


/-! ### Part 5A: Positive Canary (Shared Unmodeled Helper, Refactored Arithmetic) -/

/-- Root memory of every caller run: the initial memory linking the helpers. -/
def linkedMemory : Memory :=
  (initMachineStateWithCallees callerBranchingBody [] linkedHelpers).memory

/-- Baseline, `flag = true`: three steps to `x + x` (no gap, no fault). -/
theorem callerBranching_run_true (x : Nat) :
    callerRun callerBranchingBody 3 (true, x) =
      .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, linkedMemory) :=
  rfl

/--
Baseline, `flag = false`: the call enters `unsupportedHelperBody`, whose first
step is `MirStepNode.unsupported`, giving the gap tagged with the helper.
-/
theorem callerBranching_run_false (x : Nat) :
    callerRun callerBranchingBody 3 (false, x) =
      .gap (.unsupported "test::unmodeled_helper") :=
  rfl

/-- Refactored, `flag = true`: five steps to `x * 2`. -/
theorem callerRefactored_run_true (x : Nat) :
    callerRun callerRefactoredBody 5 (true, x) =
      .ok (.scalar ⟨wrapScalarBits (x * 2) (scalarModulus 4), 4⟩, linkedMemory) :=
  rfl

/-- Refactored, `flag = false`: the identical helper gap. -/
theorem callerRefactored_run_false (x : Nat) :
    callerRun callerRefactoredBody 5 (false, x) =
      .gap (.unsupported "test::unmodeled_helper") :=
  rfl

/-- A bounded run with a known non-budget outcome is not out of fuel. -/
theorem ne_outOfFuel_of_eq {o o' : OutcomeWithGap ExecFault (GapTag DefPath) MirReturn}
    (h : o = o') (h' : o' ≠ .gap .outOfFuel) : o ≠ .gap .outOfFuel :=
  fun h₀ => h' (h.symm.trans h₀)

/--
The helper's gap does not depend on who calls it: from *any* machine state in
which `unsupportedHelperBody` is the active callee, under any root body and any
callee environment, the run is the gap tagged with the helper's `DefPath`.
-/
theorem unsupportedHelper_gap_of_any_caller (env : MirCallEnv) (root : CapturedMir)
    (s : MachineState) (h : s.memory.activeCallee = some unsupportedHelperBody)
    (fuel : Nat) :
    runMirStepsWithGap env root (fuel + 1) (.running s) =
      .gap (.unsupported "test::unmodeled_helper") := by
  have hphase : (s.memory.activeCallee.getD root).phase = .other "unmodeled" := by
    rw [h]; rfl
  have hrun := runMirStepsWithGap_of_phase_other (env := env) hphase fuel
  rw [h] at hrun
  exact hrun

/--
The two bounded runs (budgets `3` and `5`) are related up to identical gaps on
**every** input: equal values on `flag = true` and the identical helper gap on
`flag = false`.
-/
theorem callerRefactored_gapEqErr (q : Bool × Nat) :
    GapEqErr (· = ·) (· = ·) (callerRun callerBranchingBody 3 q)
      (callerRun callerRefactoredBody 5 q) := by
  obtain ⟨flag, x⟩ := q
  cases flag with
  | true =>
    rw [callerBranching_run_true, callerRefactored_run_true, Nat.mul_two]
    exact GapEqErr.refl (fun _ => rfl) (fun _ => rfl) _
  | false =>
    rw [callerBranching_run_false, callerRefactored_run_false]
    exact GapEqErr.refl (fun _ => rfl) (fun _ => rfl) _

theorem callerBranching_run_ne_outOfFuel (q : Bool × Nat) :
    callerRun callerBranchingBody 3 q ≠ .gap .outOfFuel := by
  obtain ⟨flag, x⟩ := q
  cases flag with
  | true => rw [callerBranching_run_true]; exact fun h => by cases h
  | false => rw [callerBranching_run_false]; exact fun h => by cases h

theorem callerRefactored_run_ne_outOfFuel (q : Bool × Nat) :
    callerRun callerRefactoredBody 5 q ≠ .gap .outOfFuel := by
  obtain ⟨flag, x⟩ := q
  cases flag with
  | true => rw [callerRefactored_run_true]; exact fun h => by cases h
  | false => rw [callerRefactored_run_false]; exact fun h => by cases h

/--
Positive canary: `ContextEquiv` between the baseline and the refactored caller
on **all** `flag : Bool` and `x : Nat`, with no gap-freedom proof for
`unsupportedHelperBody`.
-/
theorem callerRefactored_contextEquiv :
    ContextEquiv (· = ·) (· = ·) (callerGapSem callerBranchingBody)
      (callerGapSem callerRefactoredBody) :=
  fun q => mirGapBehaviors_equiv_of_runs (callerBranching_run_ne_outOfFuel q)
    (callerRefactored_gapEqErr q)

/--
The same equivalence for the deterministic fuel-indexed semantics, at every
common budget of at least five steps.
-/
theorem callerRefactored_contextEquiv_bounded (fuel : Nat) (hfuel : 5 ≤ fuel) :
    ContextEquiv (· = ·) (· = ·) (GapSem.det (callerRun callerBranchingBody fuel))
      (GapSem.det (callerRun callerRefactoredBody fuel)) := by
  refine contextEquiv_det_iff.mpr (fun q => ?_)
  have h₁ : callerRun callerBranchingBody fuel q = callerRun callerBranchingBody 3 q :=
    runMirWithGap_fuel_mono (Nat.le_trans (by decide) hfuel)
      (callerBranching_run_ne_outOfFuel q)
  have h₂ : callerRun callerRefactoredBody fuel q =
      callerRun callerRefactoredBody 5 q :=
    runMirWithGap_fuel_mono hfuel (callerRefactored_run_ne_outOfFuel q)
  rw [h₁, h₂]
  exact callerRefactored_gapEqErr q

/-- The baseline alone is proved gap-free on the inputs with `flag = true`. -/
theorem callerBranching_gapFreeOn :
    GapFreeOn (fun q : Bool × Nat => q.1 = true) (callerGapSem callerBranchingBody) := by
  rintro ⟨flag, x⟩ (rfl : flag = true)
  have h : (callerRun callerBranchingBody 3 (true, x)).isGapFree := by
    rw [callerBranching_run_true]; exact trivial
  exact neverGap_mirGapBehaviors_of_run h

/--
Upgrade: on `flag = true`, where only the baseline was proved gap-free,
`ContextEquiv` becomes full gap-free `ProgramEquivOn`.
-/
theorem callerRefactored_programEquivOn :
    ProgramEquivOn (fun q : Bool × Nat => q.1 = true) (· = ·) (· = ·)
      (callerGapSem callerBranchingBody) (callerGapSem callerRefactoredBody) :=
  callerRefactored_contextEquiv.toProgramEquivOn callerBranching_gapFreeOn

/--
Gap-freedom of the refactored caller on `flag = true` is a *consequence* of the
upgrade: it is never established by evaluating the refactored caller.
-/
theorem callerRefactored_gapFreeOn :
    GapFreeOn (fun q : Bool × Nat => q.1 = true)
      (callerGapSem callerRefactoredBody) :=
  callerRefactored_programEquivOn.gapFree_right

/-- Non-vacuity: on `flag = false` the baseline really does hit the helper gap. -/
theorem callerBranching_gap_of_false (x : Nat) :
    callerGapSem callerBranchingBody (false, x)
      (.gap (.unsupported "test::unmodeled_helper")) :=
  (mirGapBehaviors_iff_of_run (callerBranching_run_ne_outOfFuel (false, x)) _).mpr
    (callerBranching_run_false x).symm

/--
Non-vacuity: the related behaviors on `flag = true` are real values. For
`x + x < 2^32` the refactored caller returns exactly `x + x`.
-/
theorem callerRefactored_value_of_true (x : Nat) (hx : x + x < 4294967296) :
    callerGapSem callerRefactoredBody (true, x)
      (.ok (.scalar ⟨x + x, 4⟩, linkedMemory)) := by
  obtain ⟨o₂, ho₂, hr⟩ := (callerRefactored_contextEquiv (true, x)).forward
    ((mirGapBehaviors_iff_of_run (callerBranching_run_ne_outOfFuel (true, x)) _).mpr
      (callerBranching_run_true x).symm)
  rw [wrapScalarBits_of_lt (show x + x < scalarModulus 4 from hx)] at hr
  cases GapEqErr.eq_iff.mp hr
  exact ho₂

/--
Whole-program gap-free equivalence is *not* available for these callers: the
baseline is not gap-free on `flag = false`, so `ProgramEquiv` on all inputs
fails while `ContextEquiv` holds.
-/
theorem callerRefactored_not_programEquiv :
    ¬ ProgramEquiv (· = ·) (· = ·) (callerGapSem callerBranchingBody)
      (callerGapSem callerRefactoredBody) :=
  fun h => h.gapFree_left (false, 0) (callerBranching_gap_of_false 0)

/--
Layer 1A bridge: the positive canary induces an identity-observation
`ExactPass` between the two callers, still with no gap-freedom proof for the
shared helper.
-/
theorem callerRefactored_exactPass :
    ExactPass (gapSemantics ExecFault.isUB callerGapSem)
      (gapSemantics ExecFault.isUB callerGapSem) id id
      callerBranchingBody callerRefactoredBody :=
  callerRefactored_contextEquiv.toExactPass_eq

/--
On `flag = true` the upgrade also yields definedness (gap-freedom and
UB-freedom) of the refactored caller, from definedness of the baseline alone.
-/
theorem callerRefactored_defined_of_true :
    ProgramEquivOn (fun q : Bool × Nat => q.1 = true) (· = ·) (· = ·)
        (callerGapSem callerBranchingBody) (callerGapSem callerRefactoredBody) ∧
      ∀ q : Bool × Nat, q.1 = true →
        OutcomeSet.Defined ExecFault.isUB (callerGapSem callerRefactoredBody q) := by
  refine mirContextEquivOn_toProgramEquivOn (callerRefactored_contextEquiv.on _) ?_
  rintro ⟨flag, x⟩ (rfl : flag = true)
  have h : (callerRun callerBranchingBody 3 (true, x)).isDefined ExecFault.isUB := by
    rw [callerBranching_run_true]; exact trivial
  exact defined_mirGapBehaviors_of_run h

/--
Adequacy: the value obtained through the upgrade is a value of the *trusted*
interaction-tree semantics `mirTree` of the refactored caller.
-/
theorem callerRefactored_mirTree_returns (x : Nat) (hx : x + x < 4294967296) :
    ∃ tr, Trusted.ITree.ReachesRet
      (mirTree callerRefactoredBody
        (initMachineStateWithCallees callerRefactoredBody (callerArgs (true, x))
          linkedHelpers))
      tr (.normal (.scalar ⟨x + x, 4⟩, linkedMemory)) :=
  mirGapBehaviors_ok_reachesRet (callerRefactored_value_of_true x hx)

/--
Full end-to-end adequacy on `flag = true`: from `callerRefactored_contextEquiv`
and the baseline's single bounded run alone (without re-evaluating
`callerRefactoredBody`), BOTH trusted `mirTree`s satisfy `MirNoUBTree` and have
literally equal trace-erased Layer 1A `ITree.toPartial` semantics.
-/
theorem callerRefactored_mirTree_adequate_and_toPartial_eq (x : Nat) :
    let t₁ := mirTree callerBranchingBody
      (initMachineStateWithCallees callerBranchingBody (callerArgs (true, x))
        linkedHelpers)
    let t₂ := mirTree callerRefactoredBody
      (initMachineStateWithCallees callerRefactoredBody (callerArgs (true, x))
        linkedHelpers)
    MirNoUBTree t₁ ∧ MirNoUBTree t₂ ∧
      Partial.map (BehaviorSet.map Prod.snd) t₁.toPartial =
        Partial.map (BehaviorSet.map Prod.snd) t₂.toPartial := by
  refine mirContextEquivOn_toPartial_eq
    (pre := fun args => ∃ n : Nat, args = callerArgs (true, n))
    (body₁ := callerBranchingBody) (body₂ := callerRefactoredBody)
    (hEq := fun args hpre => by
      obtain ⟨n, rfl⟩ := hpre
      exact callerRefactored_contextEquiv (true, n))
    (hpre := ⟨x, rfl⟩)
    (out := .normal (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, linkedMemory))
    (callerBranching_run_true x)

/--
On `flag = false` the trusted interaction tree of either caller reaches the
helper's `unsupported` fault, so the trusted Layer 1A semantics is undefined
there and says nothing. `ContextEquiv` still records that both callers hit the
identical gap.
-/
theorem callers_not_mirNoUBTree_of_false (x : Nat) :
    ¬ MirNoUBTree (mirTree callerBranchingBody
        (initMachineStateWithCallees callerBranchingBody (callerArgs (false, x))
          linkedHelpers)) ∧
      ¬ MirNoUBTree (mirTree callerRefactoredBody
        (initMachineStateWithCallees callerRefactoredBody (callerArgs (false, x))
          linkedHelpers)) :=
  ⟨not_mirNoUBTree_of_run_undefined (callerBranching_run_false x)
      (Or.inr (Or.inl ⟨_, rfl⟩)),
   not_mirNoUBTree_of_run_undefined (callerRefactored_run_false x)
      (Or.inr (Or.inl ⟨_, rfl⟩))⟩

/--
A third equivalent caller computing `0 + (x + x)` on `flag = true` and calling
the same shared unmodeled helper on `flag = false`, used to exercise
certificate-checker composition (`VerifiedContextChecker.trans`) and
query-scoped upgrade (`toExactChecker_of_gapFreeOn`).
-/
def callerZeroAddBody : CapturedMir :=
  mkMirBody "test::caller_zero_add" 2
    [mkDecl .mut u32MirTy, mkDecl .not boolMirTy, mkDecl .not u32MirTy,
     mkDecl .mut u32MirTy]
    [ flagSwitchBlock,
      { statements :=
          [mkStmt (.storageLive 3),
           mkStmt (.assign (locPlace 3)
             (.binaryOp .add (u32ConstOp 0) (.copy (locPlace 2)))),
           mkStmt (.assign (locPlace 0)
             (.binaryOp .add (.copy (locPlace 3)) (.copy (locPlace 2))))]
        terminator := mkTerm .return_
        isCleanup := false },
      helperCallBlock "test::unmodeled_helper",
      returnBlock ]

theorem callerZeroAdd_run_true (x : Nat) :
    callerRun callerZeroAddBody 5 (true, x) =
      .ok (.scalar
        ⟨wrapScalarBits (wrapScalarBits (0 + x) (scalarModulus 4) + x)
          (scalarModulus 4), 4⟩, linkedMemory) :=
  rfl

theorem callerZeroAdd_run_false (x : Nat) :
    callerRun callerZeroAddBody 5 (false, x) =
      .gap (.unsupported "test::unmodeled_helper") :=
  rfl

private theorem wrapScalarBits_eq_mod (v m : Nat) :
    wrapScalarBits v m = v % m := by
  unfold wrapScalarBits
  cases h : Nat.ble m v with
  | true => rfl
  | false =>
    have hlt : v < m :=
      Nat.lt_of_not_le (fun hle => by rw [nat_ble_eq_true_of_le hle] at h; cases h)
    exact (Nat.mod_eq_of_lt hlt).symm

private theorem wrapScalarBits_zero_add_add (x : Nat) :
    wrapScalarBits (wrapScalarBits (0 + x) (scalarModulus 4) + x) (scalarModulus 4) =
      wrapScalarBits (x + x) (scalarModulus 4) := by
  rw [Nat.zero_add, wrapScalarBits_eq_mod, wrapScalarBits_eq_mod, wrapScalarBits_eq_mod]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

theorem callerRefactored_to_zeroAdd_contextEquiv :
    ContextEquiv (· = ·) (· = ·) (callerGapSem callerRefactoredBody)
      (callerGapSem callerZeroAddBody) := by
  intro ⟨flag, x⟩
  cases flag with
  | true =>
    refine mirGapBehaviors_equiv_of_runs (fuel₂ := 5)
      (callerRefactored_run_ne_outOfFuel (true, x)) ?_
    change GapEqErr (· = ·) (· = ·)
      (callerRun callerRefactoredBody 5 (true, x))
      (callerRun callerZeroAddBody 5 (true, x))
    rw [callerRefactored_run_true, callerZeroAdd_run_true,
      wrapScalarBits_zero_add_add, Nat.mul_two]
    exact GapEqErr.refl (fun _ => rfl) (fun _ => rfl) _
  | false =>
    refine mirGapBehaviors_equiv_of_runs (fuel₂ := 5)
      (callerRefactored_run_ne_outOfFuel (false, x)) ?_
    change GapEqErr (· = ·) (· = ·)
      (callerRun callerRefactoredBody 5 (false, x))
      (callerRun callerZeroAddBody 5 (false, x))
    rw [callerRefactored_run_false, callerZeroAdd_run_false]
    exact GapEqErr.refl (fun _ => rfl) (fun _ => rfl) _

/-- Decidable identifiers for the three caller bodies in the certificate pipeline. -/
inductive CallerId : Type where
  | branching
  | refactored
  | zeroAdd
  deriving DecidableEq

/-- Resolve a `CallerId` to its concrete `V2026_06_01` `CapturedMir` body. -/
def callerOfId : CallerId → CapturedMir
  | .branching => callerBranchingBody
  | .refactored => callerRefactoredBody
  | .zeroAdd => callerZeroAddBody

/-- Semantics of a `CallerId` via `callerGapSem`. -/
def callerIdSem (id : CallerId) :
    GapSem (Bool × Nat) ExecFault (GapTag DefPath) MirReturn :=
  callerGapSem (callerOfId id)

/--
Certificate-checker canary: compose two concrete `VerifiedContextChecker`s via
`VerifiedContextChecker.trans` (`branching → refactored → zeroAdd`) and upgrade
with a query-scoped `VerifiedGapFreeOnChecker` (`flag = true`) to a
`VerifiedExactChecker` over `{q // q.1 = true}`, certifying gap-freedom of
`callerZeroAddBody` on `flag = true` without inspecting its body.
-/
theorem callerPipeline_verifiedCheckers :
    let chk₁₂ : CallerId → CallerId → Unit → Bool :=
      fun p₁ p₂ _ => decide (p₁ = .branching ∧ p₂ = .refactored)
    let chk₂₃ : CallerId → CallerId → Unit → Bool :=
      fun p₂ p₃ _ => decide (p₂ = .refactored ∧ p₃ = .zeroAdd)
    let chkComp := fun p₁ p₃ (c : CallerId × Unit × Unit) =>
      chk₁₂ p₁ c.1 c.2.1 && chk₂₃ c.1 p₃ c.2.2
    VerifiedContextChecker (· = ·) (· = ·) callerIdSem callerIdSem chkComp ∧
      VerifiedExactChecker (gapSemantics ExecFault.isUB callerIdSem)
        (gapSemantics ExecFault.isUB callerIdSem) id id chkComp ∧
      GapFreeOn (fun q : Bool × Nat => q.1 = true) (callerGapSem callerZeroAddBody) := by
  dsimp only
  have h₁₂ : VerifiedContextChecker (· = ·) (· = ·) callerIdSem callerIdSem
      (fun p₁ p₂ (_ : Unit) => decide (p₁ = .branching ∧ p₂ = .refactored)) :=
    { sound := fun hc => by
        obtain ⟨rfl, rfl⟩ := of_decide_eq_true hc
        exact callerRefactored_contextEquiv }
  have h₂₃ : VerifiedContextChecker (· = ·) (· = ·) callerIdSem callerIdSem
      (fun p₂ p₃ (_ : Unit) => decide (p₂ = .refactored ∧ p₃ = .zeroAdd)) :=
    { sound := fun hc => by
        obtain ⟨rfl, rfl⟩ := of_decide_eq_true hc
        exact callerRefactored_to_zeroAdd_contextEquiv }
  have hComp := h₁₂.trans (fun _ _ _ h₁ h₂ => h₁.trans h₂)
    (fun _ _ _ h₁ h₂ => h₁.trans h₂) h₂₃
  have hGap : VerifiedGapFreeOnChecker (fun q : Bool × Nat => q.1 = true)
      callerIdSem (fun p (_ : Unit) => decide (p = .branching)) :=
    { sound := fun hc => by
        cases of_decide_eq_true hc
        exact callerBranching_gapFreeOn }
  have hUpg := hComp.toExactChecker_of_gapFreeOn ExecFault.eq_preserves_isUB hGap
  have hAccept :
      ((decide (CallerId.branching = .branching ∧ CallerId.refactored = .refactored) &&
        decide (CallerId.refactored = .refactored ∧ CallerId.zeroAdd = .zeroAdd)) &&
        decide (CallerId.branching = .branching)) = true := by
    decide
  exact ⟨hComp, hComp.toExactChecker_eq,
    (hUpg.2 (p₁ := .branching) (p₂ := .zeroAdd)
      (c := ((.refactored, (), ()), ())) hAccept).2⟩


/-! ### Part 5B: Negative Canaries (Rejected Gaps, Gap Tags, and Faults) -/

/--
Buggy refactoring that calls the unmodeled helper on **every** input, also on
`flag = true` where the baseline returns a value:
`fn caller_buggy(flag: bool, x: u32) -> u32 { unmodeled_helper(x) }`.
-/
def callerBuggyBody : CapturedMir :=
  mkMirBody "test::caller_buggy" 2
    [mkDecl .mut u32MirTy, mkDecl .not boolMirTy, mkDecl .not u32MirTy]
    [ { statements := [], terminator := mkTerm (.goto 2), isCleanup := false },
      returnBlock,
      helperCallBlock "test::unmodeled_helper",
      returnBlock ]

/--
Refactoring that redirects the unmodeled branch to a *different* unmodeled
helper: `if flag { x + x } else { other_unmodeled_helper(x) }`.
-/
def callerOtherHelperBody : CapturedMir :=
  mkMirBody "test::caller_other_helper" 2
    [mkDecl .mut u32MirTy, mkDecl .not boolMirTy, mkDecl .not u32MirTy]
    [ flagSwitchBlock,
      { statements :=
          [mkStmt (.assign (locPlace 0)
            (.binaryOp .add (.copy (locPlace 2)) (.copy (locPlace 2))))]
        terminator := mkTerm .return_
        isCleanup := false },
      helperCallBlock "test::other_unmodeled_helper",
      returnBlock ]

theorem callerBuggy_run (q : Bool × Nat) :
    callerRun callerBuggyBody 3 q = .gap (.unsupported "test::unmodeled_helper") :=
  rfl

theorem callerOtherHelper_run_false (x : Nat) :
    callerRun callerOtherHelperBody 3 (false, x) =
      .gap (.unsupported "test::other_unmodeled_helper") :=
  rfl

/--
Negative canary (newly introduced gap): on `flag = true` the baseline returns a
value while the buggy refactoring hits the helper gap. A value is never
`GapEqErr`-related to a gap.
-/
theorem callerBuggy_not_gapEqErr (x : Nat) :
    ¬ GapEqErr (· = ·) (· = ·) (callerRun callerBranchingBody 3 (true, x))
      (callerRun callerBuggyBody 3 (true, x)) := by
  rw [callerBranching_run_true, callerBuggy_run]
  exact GapEqErr.not_ok_gap

/-- The buggy refactoring is therefore rejected by `ContextEquiv`. -/
theorem callerBuggy_not_contextEquiv :
    ¬ ContextEquiv (· = ·) (· = ·) (callerGapSem callerBranchingBody)
      (callerGapSem callerBuggyBody) :=
  fun h => callerBuggy_not_gapEqErr 0
    ((mirGapBehaviors_equiv_iff_of_runs
      (callerBranching_run_ne_outOfFuel (true, 0))
      (ne_outOfFuel_of_eq (callerBuggy_run (true, 0)) (fun h₀ => by cases h₀))).mp
      (h (true, 0)))

/--
Negative canary (mismatched gap tags): on `flag = false` both callers hit an
unmodeled helper, but not the same one. Gaps match only when identical.
-/
theorem callerOtherHelper_not_gapEqErr (x : Nat) :
    ¬ GapEqErr (· = ·) (· = ·) (callerRun callerBranchingBody 3 (false, x))
      (callerRun callerOtherHelperBody 3 (false, x)) := by
  rw [callerBranching_run_false, callerOtherHelper_run_false]
  intro h
  exact absurd (GapTag.unsupported.inj h) (by decide)

/-- Redirecting to a different unmodeled helper is rejected by `ContextEquiv`. -/
theorem callerOtherHelper_not_contextEquiv :
    ¬ ContextEquiv (· = ·) (· = ·) (callerGapSem callerBranchingBody)
      (callerGapSem callerOtherHelperBody) :=
  fun h => callerOtherHelper_not_gapEqErr 0
    ((mirGapBehaviors_equiv_iff_of_runs
      (callerBranching_run_ne_outOfFuel (false, 0))
      (ne_outOfFuel_of_eq (callerOtherHelper_run_false 0)
        (fun h₀ => by cases h₀))).mp
      (h (false, 0)))

/--
Checked accessor: `fn checked(flag: bool, x: u32) -> u32 { assert!(flag); x }`
(a defined panic on `flag = false`).
-/
def assertFlagBody : CapturedMir :=
  mkMirBody "test::assert_flag" 2
    [mkDecl .mut u32MirTy, mkDecl .not boolMirTy, mkDecl .not u32MirTy]
    [ { statements := []
        terminator := mkTerm (.assert (.copy (locPlace 1)) true 1 .continue_)
        isCleanup := false },
      { statements := [mkStmt (.assign (locPlace 0) (.use (.copy (locPlace 2))))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/--
Unchecked accessor:
`unsafe fn unchecked(flag: bool, x: u32) -> u32 { if !flag { unreachable_unchecked() } x }`
(undefined behavior on `flag = false`).
-/
def assumeFlagBody : CapturedMir :=
  mkMirBody "test::assume_flag" 2
    [mkDecl .mut u32MirTy, mkDecl .not boolMirTy, mkDecl .not u32MirTy]
    [ flagSwitchBlock,
      { statements := [mkStmt (.assign (locPlace 0) (.use (.copy (locPlace 2))))]
        terminator := mkTerm .return_
        isCleanup := false },
      { statements := [], terminator := mkTerm .unreachable, isCleanup := false } ]

/-- Total accessor: `fn total(flag: bool, x: u32) -> u32 { x }`. -/
def returnArgBody : CapturedMir :=
  mkMirBody "test::return_arg" 2
    [mkDecl .mut u32MirTy, mkDecl .not boolMirTy, mkDecl .not u32MirTy]
    [ { statements := [mkStmt (.assign (locPlace 0) (.use (.copy (locPlace 2))))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/-- `assert!(flag)` with `flag = false` is the *defined* fault `.panic`. -/
theorem assertFlag_run_false (x : Nat) :
    callerRun assertFlagBody 3 (false, x) = .fault .panic := rfl

/-- `unreachable_unchecked()` with `flag = false` is the fault `.ub`. -/
theorem assumeFlag_run_false (x : Nat) :
    callerRun assumeFlagBody 3 (false, x) = .fault .ub := rfl

theorem returnArg_run (q : Bool × Nat) :
    callerRun returnArgBody 3 q = .ok (.scalar ⟨q.2, 4⟩, linkedMemory) := rfl

/-- Outcome level: UB is never related to a normal return. -/
theorem ub_not_gapEqErr_ok (v : MirReturn) :
    ¬ GapEqErr (Gap := GapTag DefPath) (· = ·) (· = ·)
      (.fault ExecFault.ub) (.ok v) :=
  GapEqErr.not_fault_ok

/-- Outcome level: under exact fault matching UB is never related to a panic. -/
theorem ub_not_gapEqErr_panic :
    ¬ GapEqErr (Gap := GapTag DefPath) (Val₁ := MirReturn) (Val₂ := MirReturn)
      (· = ·) (· = ·) (.fault ExecFault.ub) (.fault ExecFault.panic) :=
  fun h => by cases h

/-- Outcome level: under exact fault matching panic is never related to abort. -/
theorem panic_not_gapEqErr_abort :
    ¬ GapEqErr (Gap := GapTag DefPath) (Val₁ := MirReturn) (Val₂ := MirReturn)
      (· = ·) (· = ·) (.fault ExecFault.panic) (.fault ExecFault.abort) :=
  fun h => by cases h

/-- Outcome level: a gap is never related to a fault, in either direction. -/
theorem gap_not_gapEqErr_ub (g : GapTag DefPath) :
    ¬ GapEqErr (Val₁ := MirReturn) (Val₂ := MirReturn) (· = ·) (· = ·)
      (.gap g) (.fault ExecFault.ub) :=
  GapEqErr.not_gap_fault

/--
Negative canary (UB vs. normal return): replacing the total accessor by the
unchecked one turns a value into UB on `flag = false`.
-/
theorem assumeFlag_not_gapEqErr_returnArg (x : Nat) :
    ¬ GapEqErr (· = ·) (· = ·) (callerRun assumeFlagBody 3 (false, x))
      (callerRun returnArgBody 3 (false, x)) := by
  rw [assumeFlag_run_false, returnArg_run]
  exact GapEqErr.not_fault_ok

/--
Negative canary (UB vs. panic): the unchecked accessor is not equivalent to the
checked one, because UB is never conflated with a defined panic.
-/
theorem assumeFlag_not_gapEqErr_assertFlag (x : Nat) :
    ¬ GapEqErr (· = ·) (· = ·) (callerRun assumeFlagBody 3 (false, x))
      (callerRun assertFlagBody 3 (false, x)) := by
  rw [assumeFlag_run_false, assertFlag_run_false]
  exact ub_not_gapEqErr_panic

theorem assertFlag_not_contextEquiv_assumeFlag :
    ¬ ContextEquiv (· = ·) (· = ·) (callerGapSem assumeFlagBody)
      (callerGapSem assertFlagBody) :=
  fun h => assumeFlag_not_gapEqErr_assertFlag 0
    ((mirGapBehaviors_equiv_iff_of_runs
      (ne_outOfFuel_of_eq (assumeFlag_run_false 0) (fun h₀ => by cases h₀))
      (ne_outOfFuel_of_eq (assertFlag_run_false 0) (fun h₀ => by cases h₀))).mp
      (h (false, 0)))

/--
Negative canary (gap vs. fault): replacing the unmodeled helper call by UB is
rejected as well. A gap says nothing about the program, so it is never traded
for a fault.
-/
theorem callerBuggy_not_gapEqErr_assumeFlag (x : Nat) :
    ¬ GapEqErr (· = ·) (· = ·) (callerRun callerBuggyBody 3 (false, x))
      (callerRun assumeFlagBody 3 (false, x)) := by
  rw [callerBuggy_run, assumeFlag_run_false]
  exact GapEqErr.not_gap_fault

/--
Negative canary (fault vs. gap): the checked accessor panics on `flag = false`
where the buggy caller hits the helper gap. A defined fault is never related
to a gap either.
-/
theorem assertFlag_not_gapEqErr_callerBuggy (x : Nat) :
    ¬ GapEqErr (· = ·) (· = ·) (callerRun assertFlagBody 3 (false, x))
      (callerRun callerBuggyBody 3 (false, x)) := by
  rw [assertFlag_run_false, callerBuggy_run]
  exact GapEqErr.not_fault_gap

/--
Soundness of the UB side condition: a fault relation that conflates UB with a
panic does relate the unchecked and the checked accessor outcome-wise, but it
is rejected by every Layer 1A bridge (`ExecFault.not_preserves_isUB_of_ub_panic`),
and rightly so: the checked accessor is defined on `flag = false` while the
unchecked one is not.
-/
theorem conflating_fault_relation_rejected (x : Nat) :
    GapEqErr (· = ·) (fun _ _ => True) (callerRun assumeFlagBody 3 (false, x))
        (callerRun assertFlagBody 3 (false, x)) ∧
      (¬ ∀ e₁ e₂ : ExecFault, (fun _ _ => True) e₁ e₂ → (e₁.isUB ↔ e₂.isUB)) ∧
      OutcomeSet.Defined ExecFault.isUB (callerGapSem assertFlagBody (false, x)) ∧
      ¬ OutcomeSet.Defined ExecFault.isUB (callerGapSem assumeFlagBody (false, x)) := by
  refine ⟨?_, ExecFault.not_preserves_isUB_of_ub_panic trivial, ?_, ?_⟩
  · rw [assumeFlag_run_false, assertFlag_run_false]
    exact trivial
  · have h : (callerRun assertFlagBody 3 (false, x)).isDefined ExecFault.isUB := by
      rw [assertFlag_run_false]; exact fun hub => hub
    exact defined_mirGapBehaviors_of_run h
  · intro hdef
    have hmem : callerGapSem assumeFlagBody (false, x) (.fault .ub) :=
      (mirGapBehaviors_iff_of_run
        (ne_outOfFuel_of_eq (assumeFlag_run_false x) (fun h₀ => by cases h₀)) _).mpr
        (assumeFlag_run_false x).symm
    exact hdef hmem trivial

/-! #### Rust Unwind Soundness Canaries (`MirCallEnv` + `UnwindAction`) -/

/--
Caller of `"test::ext_helper"` with an explicit `UnwindAction`:
exercises `.continue_`, `.unreachable` (`nounwind`), `.terminate`, and
`.cleanup 2` (whose cleanup block calls `unsupportedHelperBody`).
-/
def unwindCallerBody (name : DefPath) (unwind : UnwindAction) : CapturedMir :=
  mkMirBody name 1
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy]
    [ { statements := []
        terminator := mkTerm
          (.call (fnItemOp "test::ext_helper") [.copy (locPlace 1)]
            (locPlace 0) (some 1) unwind)
        isCleanup := false },
      returnBlock,
      { statements := []
        terminator := mkTerm
          (.call (fnItemOp "test::unmodeled_helper") [.copy (locPlace 1)]
            (locPlace 0) (some 1) .continue_)
        isCleanup := true } ]

/-- External callee summary that always panics. -/
def panickingHelperSummary (_ : DefPath) (_ : List Value) :
    OutcomeWithGap ExecFault (GapTag DefPath) Value :=
  .fault .panic

/--
Unwind soundness: a panicking external callee called through
`MirCallEnv.ofPure` MUST route through `MirCallAns.panicked` into the caller's
`UnwindAction`:
- `.continue_` -> defined `.fault .panic`;
- `.unreachable` (`nounwind`) -> undefined behavior `.fault .ub` (never masked as panic!);
- `.terminate` -> defined `.fault .abort` (never left as panic!);
- `.cleanup 2` -> executes cleanup block `bb2` (reaching `unsupportedHelperBody`'s gap!).
-/
theorem unwindAction_soundness_of_panicking_callee (x : Nat) :
    let env := MirCallEnv.ofPure panickingHelperSummary
    let args := [Value.scalar ⟨x, 4⟩]
    runMirWithGap env linkedHelpers
        (unwindCallerBody "test::unwind_continue" .continue_) 3 args =
        .fault .panic ∧
      runMirWithGap env linkedHelpers
          (unwindCallerBody "test::unwind_unreachable" .unreachable) 3 args =
        .fault .ub ∧
      runMirWithGap env linkedHelpers
          (unwindCallerBody "test::unwind_terminate" .terminate) 3 args =
        .fault .abort ∧
      runMirWithGap env linkedHelpers
          (unwindCallerBody "test::unwind_cleanup" (.cleanup 2)) 4 args =
        .gap (.unsupported "test::unmodeled_helper") :=
  ⟨rfl, rfl, rfl, rfl⟩

/--
Because `UnwindAction.unreachable` turns a callee panic into UB while
`UnwindAction.continue_` produces a defined panic, the two callers are NOT
`ContextEquiv` under `MirCallEnv.ofPure panickingHelperSummary`.
-/
theorem unwindContinue_not_contextEquiv_unwindUnreachable :
    let env := MirCallEnv.ofPure panickingHelperSummary
    ¬ ContextEquiv (· = ·) (· = ·)
      (mirGapBehaviors env linkedHelpers
        (unwindCallerBody "test::unwind_continue" .continue_))
      (mirGapBehaviors env linkedHelpers
        (unwindCallerBody "test::unwind_unreachable" .unreachable)) := by
  dsimp only
  intro h
  have h1 : runMirWithGap (MirCallEnv.ofPure panickingHelperSummary) linkedHelpers
      (unwindCallerBody "test::unwind_continue" .continue_) 3 [.scalar ⟨0, 4⟩] =
      .fault .panic := rfl
  have h2 : runMirWithGap (MirCallEnv.ofPure panickingHelperSummary) linkedHelpers
      (unwindCallerBody "test::unwind_unreachable" .unreachable) 3 [.scalar ⟨0, 4⟩] =
      .fault .ub := rfl
  have hEq := (mirGapBehaviors_equiv_iff_of_runs
    (ne_outOfFuel_of_eq h1 (fun h₀ => by cases h₀))
    (ne_outOfFuel_of_eq h2 (fun h₀ => by cases h₀))).mp (h [.scalar ⟨0, 4⟩])
  rw [h1, h2] at hEq
  cases hEq

/-! #### Nondeterministic `OutcomeSet` Canaries (`OutcomeSetEquiv.bind_congr` & `valSemantics`) -/

/--
Nondeterministic positive canary: a prefix behavior set containing both a
normal value and a modeling gap composes with two refactored nondeterministic
continuations via `OutcomeSetEquiv.bind_congr`, without requiring gap-freedom;
on a gap-free nondeterministic prefix, `ContextEquiv.toProgramEquiv` upgrades to
`ProgramEquiv` and `ProgramEquiv.toValExactPass_eq` erases both `Gap` and `Fault`.
-/
theorem nondet_outcomeSet_bind_congr_and_val_bridge :
    let S_gap : OutcomeSet ExecFault String Nat :=
      fun o => o = .ok 3 ∨ o = .gap "nondet_helper"
    let S_ok : OutcomeSet ExecFault String Nat :=
      fun o => o = .ok 3 ∨ o = .ok 5
    let k₁ : Nat → OutcomeSet ExecFault String Nat :=
      fun v o => o = .ok (v + v) ∨ o = .ok (v + 1)
    let k₂ : Nat → OutcomeSet ExecFault String Nat :=
      fun v o => o = .ok (v * 2) ∨ o = .ok (1 + v)
    OutcomeSetEquiv (GapEqErr (· = ·) (· = ·))
        (OutcomeSet.bind S_gap k₁) (OutcomeSet.bind S_gap k₂) ∧
      ProgramEquiv (· = ·) (· = ·)
        (fun (_ : Unit) => OutcomeSet.bind S_ok k₁)
        (fun (_ : Unit) => OutcomeSet.bind S_ok k₂) ∧
      ExactPass
        (valSemantics (fun (b : Bool) (_ : Unit) =>
          OutcomeSet.bind S_ok (if b then k₁ else k₂)))
        (valSemantics (fun (b : Bool) (_ : Unit) =>
          OutcomeSet.bind S_ok (if b then k₁ else k₂)))
        id id true false := by
  dsimp only
  have hk : ∀ a₁ a₂ : Nat, a₁ = a₂ →
      OutcomeSetEquiv (GapEqErr (· = ·) (· = ·))
        (fun o : OutcomeWithGap ExecFault String Nat => o = .ok (a₁ + a₁) ∨ o = .ok (a₁ + 1))
        (fun o : OutcomeWithGap ExecFault String Nat => o = .ok (a₂ * 2) ∨ o = .ok (1 + a₂)) := by
    intro a₁ a₂ ha; cases ha
    constructor
    · rintro o (rfl | rfl)
      · exact ⟨.ok (a₁ * 2), Or.inl rfl, (Nat.mul_two a₁).symm⟩
      · exact ⟨.ok (1 + a₁), Or.inr rfl, Nat.add_comm a₁ 1⟩
    · rintro o (rfl | rfl)
      · exact ⟨.ok (a₁ + a₁), Or.inl rfl, (Nat.mul_two a₁).symm⟩
      · exact ⟨.ok (a₁ + 1), Or.inr rfl, Nat.add_comm a₁ 1⟩
  have hGap : OutcomeSetEquiv (GapEqErr (· = ·) (· = ·))
      (OutcomeSet.bind (fun o => o = .ok 3 ∨ o = .gap "nondet_helper")
        (fun v o => o = .ok (v + v) ∨ o = .ok (v + 1)))
      (OutcomeSet.bind (fun o => o = .ok 3 ∨ o = .gap "nondet_helper")
        (fun v o => o = .ok (v * 2) ∨ o = .ok (1 + v))) :=
    (OutcomeSetEquiv.refl (GapEqErr.refl (fun _ => rfl) (fun _ => rfl)) _).bind_congr hk
  have hCtxOk : ContextEquiv (· = ·) (· = ·)
      (fun (_ : Unit) =>
        OutcomeSet.bind (fun o => o = .ok 3 ∨ o = .ok 5)
          (fun v o => o = .ok (v + v) ∨ o = .ok (v + 1)))
      (fun (_ : Unit) =>
        OutcomeSet.bind (fun o => o = .ok 3 ∨ o = .ok 5)
          (fun v o => o = .ok (v * 2) ∨ o = .ok (1 + v))) :=
    fun _ =>
      (OutcomeSetEquiv.refl (GapEqErr.refl (fun _ => rfl) (fun _ => rfl)) _).bind_congr hk
  have hGapFree : AllGapFree (fun (_ : Unit) =>
      OutcomeSet.bind (fun o : OutcomeWithGap ExecFault String Nat => o = .ok 3 ∨ o = .ok 5)
        (fun v o => o = .ok (v + v) ∨ o = .ok (v + 1))) := by
    intro _
    refine (OutcomeSet.neverGap_bind_iff _ _).mpr ⟨?_, ?_⟩
    · rintro o (rfl | rfl) <;> trivial
    · rintro v _ o (rfl | rfl) <;> trivial
  have hProg := hCtxOk.toProgramEquiv hGapFree
  exact ⟨hGap, hProg, ProgramEquiv.toValExactPass_eq
    (sem₁ := fun (b : Bool) (_ : Unit) =>
      OutcomeSet.bind (fun o : OutcomeWithGap ExecFault String Nat => o = .ok 3 ∨ o = .ok 5)
        (if b then (fun v o => o = .ok (v + v) ∨ o = .ok (v + 1))
         else (fun v o => o = .ok (v * 2) ∨ o = .ok (1 + v))))
    (sem₂ := fun (b : Bool) (_ : Unit) =>
      OutcomeSet.bind (fun o : OutcomeWithGap ExecFault String Nat => o = .ok 3 ∨ o = .ok 5)
        (if b then (fun v o => o = .ok (v + v) ∨ o = .ok (v + 1))
         else (fun v o => o = .ok (v * 2) ∨ o = .ok (1 + v))))
    hProg⟩

/--
Nondeterministic negative canary: a nondeterministic behavior set that may hit
a gap `{.ok 1, .gap "site"}` is NEVER `OutcomeSetEquiv` to the gap-free `{.ok 1}`.
-/
theorem nondet_gap_branch_not_contextEquiv :
    ¬ OutcomeSetEquiv (GapEqErr (· = ·) (· = ·))
      (fun o : OutcomeWithGap ExecFault String Nat => o = .ok 1 ∨ o = .gap "site")
      (BehaviorSet.singleton (.ok 1)) := by
  intro h
  obtain ⟨o₂, ho₂, hr⟩ := h.forward (Or.inr rfl)
  cases ho₂
  exact hr

/-! ### Part 5C: Any Callee Environment (`GapEqErr.bind_congr`) -/

/--
Baseline caller of an *external* helper (no linked body):
`fn tail_caller(flag: bool, x: u32) -> u32 { if flag { x + x } else { become ext_helper(x) } }`.
-/
def tailCallerBody : CapturedMir :=
  mkMirBody "test::tail_caller" 2
    [mkDecl .mut u32MirTy, mkDecl .not boolMirTy, mkDecl .not u32MirTy]
    [ flagSwitchBlock,
      { statements :=
          [mkStmt (.assign (locPlace 0)
            (.binaryOp .add (.copy (locPlace 2)) (.copy (locPlace 2))))]
        terminator := mkTerm .return_
        isCleanup := false },
      { statements := []
        terminator := mkTerm
          (.tailCall (fnItemOp "test::ext_helper") [.copy (locPlace 2)])
        isCleanup := false } ]

/-- Refactored caller of the same external helper (`x * 2` via a temporary). -/
def tailCallerRefactoredBody : CapturedMir :=
  mkMirBody "test::tail_caller_refactored" 2
    [mkDecl .mut u32MirTy, mkDecl .not boolMirTy, mkDecl .not u32MirTy,
     mkDecl .mut u32MirTy]
    [ flagSwitchBlock,
      { statements :=
          [mkStmt (.storageLive 3),
           mkStmt (.assign (locPlace 3)
            (.binaryOp .mul (.copy (locPlace 2)) (u32ConstOp 2))),
           mkStmt (.assign (locPlace 0) (.use (.copy (locPlace 3))))]
        terminator := mkTerm .return_
        isCleanup := false },
      { statements := []
        terminator := mkTerm
          (.tailCall (fnItemOp "test::ext_helper") [.copy (locPlace 2)])
        isCleanup := false } ]

/-- Root memory of the external-helper callers (no linked callee bodies). -/
def unlinkedMemory : Memory := (initMachineState tailCallerBody []).memory

/-- The external request both callers issue on `flag = false`. -/
def extHelperReq (x : Nat) : MirCallReq :=
  { defPath := "test::ext_helper", typeArgs := [], args := [.scalar ⟨x, 4⟩],
    memory := unlinkedMemory }

/-- Machine state of a tail caller after the `flag = false` switch to `bb2`. -/
def tailCallerAtCall (body : CapturedMir) (x : Nat) : MachineState :=
  { frame :=
      { blockIdx := 2
        stmtIdx := 0
        locals := (initMachineState body (callerArgs (false, x))).frame.locals }
    memory := (initMachineState body (callerArgs (false, x))).memory }

/-- Bounded run against the memory-preserving helper summary `f`. -/
def tailRun
    (f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value)
    (body : CapturedMir) (fuel : Nat) (q : Bool × Nat) :
    OutcomeWithGap ExecFault (GapTag DefPath) MirReturn :=
  runMirWithGap (MirCallEnv.ofPure f) [] body fuel (callerArgs q)

/--
Call-handler law on the baseline: on `flag = false` the run is the `bind` of
the sealed environment answer with the rest of the run, for every environment.
-/
theorem tailCaller_run_false (env : MirCallEnv) (x fuel : Nat) :
    runMirWithGap env [] tailCallerBody (fuel + 2) (callerArgs (false, x)) =
      (((env (extHelperReq x)).mapFault (fun _ => .ub)).mapGap
          (·.sealOutOfFuel "test::ext_helper")).bind (fun ans =>
        runMirStepsWithGap env tailCallerBody fuel (resumeExternalTailCall ans)) :=
  (runGapSteps_succ_of_next (mirSiteGapStep env tailCallerBody)
      (s := mirSiteOfExec tailCallerBody (.running (initMachineStateWithCallees tailCallerBody
        (callerArgs (false, x)) [])))
      (s' := mirSiteOfExec tailCallerBody (.running (tailCallerAtCall tailCallerBody x)))
      rfl (fuel + 1)).trans
    (runMirStepsWithGap_of_root_extCall (env := env) (body := tailCallerBody)
      (s := tailCallerAtCall tailCallerBody x) (req := extHelperReq x)
      (k := resumeExternalTailCall) rfl rfl rfl fuel)

/-- Call-handler law on the refactored caller: the same request and `bind`. -/
theorem tailCallerRefactored_run_false (env : MirCallEnv) (x fuel : Nat) :
    runMirWithGap env [] tailCallerRefactoredBody (fuel + 2) (callerArgs (false, x)) =
      (((env (extHelperReq x)).mapFault (fun _ => .ub)).mapGap
          (·.sealOutOfFuel "test::ext_helper")).bind (fun ans =>
        runMirStepsWithGap env tailCallerRefactoredBody fuel
          (resumeExternalTailCall ans)) :=
  (runGapSteps_succ_of_next (mirSiteGapStep env tailCallerRefactoredBody)
      (s := mirSiteOfExec tailCallerRefactoredBody
        (.running (initMachineStateWithCallees tailCallerRefactoredBody
          (callerArgs (false, x)) [])))
      (s' := mirSiteOfExec tailCallerRefactoredBody
        (.running (tailCallerAtCall tailCallerRefactoredBody x))) rfl
      (fuel + 1)).trans
    (runMirStepsWithGap_of_root_extCall (env := env) (body := tailCallerRefactoredBody)
      (s := tailCallerAtCall tailCallerRefactoredBody x) (req := extHelperReq x)
      (k := resumeExternalTailCall) rfl rfl rfl fuel)

/--
For **every** helper summary `f` (returning, panicking, aborting, UB, or hitting
any gap, with callee `.outOfFuel` sealed to `.budget "test::ext_helper"`), the
baseline's `flag = false` run is `f`'s sealed outcome on the helper request.
-/
theorem tailCaller_run_false_pure
    (f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value)
    (x : Nat) :
    tailRun f tailCallerBody 3 (false, x) =
      ((f "test::ext_helper" [.scalar ⟨x, 4⟩]).mapGap
        (·.sealOutOfFuel "test::ext_helper")).map (fun v => (v, unlinkedMemory)) := by
  show runMirWithGap (MirCallEnv.ofPure f) [] tailCallerBody (1 + 2)
    (callerArgs (false, x)) = _
  rw [tailCaller_run_false]
  unfold MirCallEnv.ofPure extHelperReq
  dsimp only
  cases f "test::ext_helper" [.scalar ⟨x, 4⟩] with
  | ok v => rfl
  | fault e => cases e <;> rfl
  | gap g => cases g <;> rfl

theorem tailCallerRefactored_run_false_pure
    (f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value)
    (x : Nat) :
    tailRun f tailCallerRefactoredBody 3 (false, x) =
      ((f "test::ext_helper" [.scalar ⟨x, 4⟩]).mapGap
        (·.sealOutOfFuel "test::ext_helper")).map (fun v => (v, unlinkedMemory)) := by
  show runMirWithGap (MirCallEnv.ofPure f) [] tailCallerRefactoredBody (1 + 2)
    (callerArgs (false, x)) = _
  rw [tailCallerRefactored_run_false]
  unfold MirCallEnv.ofPure extHelperReq
  dsimp only
  cases f "test::ext_helper" [.scalar ⟨x, 4⟩] with
  | ok v => rfl
  | fault e => cases e <;> rfl
  | gap g => cases g <;> rfl

theorem tailCaller_run_true
    (f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value)
    (x : Nat) :
    tailRun f tailCallerBody 3 (true, x) =
      .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, unlinkedMemory) :=
  rfl

theorem tailCallerRefactored_run_true
    (f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value)
    (x : Nat) :
    tailRun f tailCallerRefactoredBody 5 (true, x) =
      .ok (.scalar ⟨wrapScalarBits (x * 2) (scalarModulus 4), 4⟩, unlinkedMemory) :=
  rfl

/--
Positive canary, modular in the callee: for **every** helper summary `f` the
two callers are related up to identical gaps on every input. On `flag = false`
both runs are `f`'s outcome, whatever it is; nothing about `f` is assumed.
-/
theorem tailCallerRefactored_gapEqErr_any_helper
    (f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value)
    (q : Bool × Nat) :
    GapEqErr (· = ·) (· = ·) (tailRun f tailCallerBody 3 q)
      (tailRun f tailCallerRefactoredBody (if q.1 then 5 else 3) q) := by
  obtain ⟨flag, x⟩ := q
  cases flag with
  | true =>
    show GapEqErr _ _ _ (tailRun f tailCallerRefactoredBody 5 (true, x))
    rw [tailCaller_run_true, tailCallerRefactored_run_true, Nat.mul_two]
    exact GapEqErr.refl (fun _ => rfl) (fun _ => rfl) _
  | false =>
    show GapEqErr _ _ _ (tailRun f tailCallerRefactoredBody 3 (false, x))
    rw [tailCaller_run_false_pure, tailCallerRefactored_run_false_pure]
    exact GapEqErr.refl (fun _ => rfl) (fun _ => rfl) _

/--
Fuel-free `ContextEquiv` for **every** stack-preserving callee environment
`env : MirCallEnv` (returning with arbitrary heap memory, panicking, aborting,
UB, or hitting any gap), proved directly via `mirGapBehaviors_equiv_of_stutter_with`
(`StepNodeRelWith.vis`) with no fuel-budget asymmetry.
-/
theorem tailCallerRefactored_contextEquiv_any_env (env : MirCallEnv)
    (hStackRet : ∀ x v mem,
      env (extHelperReq x) = .ok (.returned v mem) → mem.callStack = [])
    (hStackPanic : ∀ x mem,
      env (extHelperReq x) = .ok (.panicked mem) → mem.callStack = []) :
    ContextEquiv (· = ·) (· = ·)
      (fun q : Bool × Nat => mirGapBehaviors env [] tailCallerBody (callerArgs q))
      (fun q : Bool × Nat =>
        mirGapBehaviors env [] tailCallerRefactoredBody (callerArgs q)) := by
  intro ⟨flag, x⟩
  cases flag with
  | true =>
    have h₁ : runMirWithGap env [] tailCallerBody 3 (callerArgs (true, x)) =
        .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, unlinkedMemory) :=
      rfl
    have h₂ : runMirWithGap env [] tailCallerRefactoredBody 5 (callerArgs (true, x)) =
        .ok (.scalar ⟨wrapScalarBits (x * 2) (scalarModulus 4), 4⟩, unlinkedMemory) :=
      rfl
    refine mirGapBehaviors_equiv_of_runs (fuel₂ := 5)
      (ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀)) ?_
    rw [h₁, h₂, Nat.mul_two]
    exact GapEqErr.refl (fun _ => rfl) (fun _ => rfl) _
  | false =>
    let s₁₀ : MirSiteState :=
      mirSiteOfExec tailCallerBody
        (.running (initMachineStateWithCallees tailCallerBody (callerArgs (false, x)) []))
    let s₂₀ : MirSiteState :=
      mirSiteOfExec tailCallerRefactoredBody
        (.running (initMachineStateWithCallees tailCallerRefactoredBody
          (callerArgs (false, x)) []))
    let R : MirSiteState → MirSiteState → Prop :=
      fun a b => (a = s₁₀ ∧ b = s₂₀) ∨ ∃ out, a = .halted out ∧ b = .halted out
    refine mirGapBehaviors_equiv_of_stutter_with (R := R) (fun _ => rfl) ?_ (Or.inl ⟨rfl, rfl⟩)
    intro a b hR
    rcases hR with ⟨rfl, rfl⟩ | ⟨out, rfl, rfl⟩
    · let t₁ : MirSiteState :=
        mirSiteOfExec tailCallerBody (.running (tailCallerAtCall tailCallerBody x))
      let t₂ : MirSiteState :=
        mirSiteOfExec tailCallerRefactoredBody
          (.running (tailCallerAtCall tailCallerRefactoredBody x))
      refine ⟨1, 1, t₁, t₂, .step rfl (.refl _), .step rfl (.refl _), ?_⟩
      change StepNodeRelWith (mirGapHandle env) (mirGapHandle env) R (· = ·) (· = ·)
        (mirSiteOfState tailCallerBody t₁) (mirSiteOfState tailCallerRefactoredBody t₂)
        (.vis (.inr (.inr (.call (extHelperReq x))))
          (fun ans => mirNextSiteState tailCallerBody t₁ (resumeExternalTailCall ans)))
        (.vis (.inr (.inr (.call (extHelperReq x))))
          (fun ans => mirNextSiteState tailCallerRefactoredBody t₂ (resumeExternalTailCall ans)))
      refine StepNodeRelWith.vis (· = ·)
        (GapEqErr.refl (fun _ => rfl) (fun _ => rfl) _) ?_
      rintro ans _ ho₁ _ rfl
      have he : env (extHelperReq x) = .ok ans := mirGapHandle_call_eq_ok ho₁
      cases ans with
      | returned v mem =>
        have hcs := hStackRet x v mem he
        refine Or.inr ⟨.normal (v, mem), ?_, ?_⟩
        · dsimp only [mirNextSiteState, t₁, mirSiteOfExec, resumeExternalTailCall]
          rw [hcs]
        · dsimp only [mirNextSiteState, t₂, mirSiteOfExec, resumeExternalTailCall]
          rw [hcs]
      | panicked mem =>
        have hcs := hStackPanic x mem he
        refine Or.inr ⟨.panic, ?_, ?_⟩
        · dsimp only [mirNextSiteState, t₁, mirSiteOfExec, resumeExternalTailCall]
          rw [hcs]
          rfl
        · dsimp only [mirNextSiteState, t₂, mirSiteOfExec, resumeExternalTailCall]
          rw [hcs]
          rfl
      | aborted =>
        exact Or.inr ⟨.abort, rfl, rfl⟩
    · refine ⟨0, 0, .halted out, .halted out, .refl _, .refl _, ?_⟩
      change StepNodeRelWith _ _ _ _ _ _ _ (.ret out) (.ret out)
      cases out with
      | normal r => exact StepNodeRelWith.normal rfl
      | panic => exact StepNodeRelWith.panic
      | abort => exact StepNodeRelWith.abort

/--
Summary of the unmodeled helper obtained by *running* `unsupportedHelperBody`:
its gap-aware semantics is the gap tagged with its own `DefPath`.
-/
def unmodeledHelperSummary (_ : DefPath) (args : List Value) :
    OutcomeWithGap ExecFault (GapTag DefPath) Value :=
  (runMirWithGap MirCallEnv.unresolved [] unsupportedHelperBody 2 args).map Prod.fst

theorem unmodeledHelperSummary_eq (defPath : DefPath) (args : List Value) :
    unmodeledHelperSummary defPath args =
      .gap (.unsupported "test::unmodeled_helper") :=
  rfl

/--
Instantiating the any-helper canary with the unmodeled helper: both callers hit
the helper's own gap, and that gap is what makes them equivalent there.
-/
theorem tailCaller_run_false_unmodeled (x : Nat) :
    tailRun unmodeledHelperSummary tailCallerBody 3 (false, x) =
        .gap (.unsupported "test::unmodeled_helper") ∧
      tailRun unmodeledHelperSummary tailCallerRefactoredBody 3 (false, x) =
        .gap (.unsupported "test::unmodeled_helper") := by
  rw [tailCaller_run_false_pure, tailCallerRefactored_run_false_pure,
    unmodeledHelperSummary_eq]
  exact ⟨rfl, rfl⟩

/--
With no summary at all (`MirCallEnv.unresolved`), the external call is the
`unresolved` gap tagged with the callee, again identical for both callers.
-/
theorem tailCaller_run_false_unresolved (x : Nat) :
    runMirWithGap MirCallEnv.unresolved [] tailCallerBody 3 (callerArgs (false, x)) =
        .gap (.unresolved "test::ext_helper") ∧
      runMirWithGap MirCallEnv.unresolved [] tailCallerRefactoredBody 3
          (callerArgs (false, x)) =
        .gap (.unresolved "test::ext_helper") :=
  ⟨rfl, rfl⟩

/-! ### Part 5D: Sequential Non-Tail Call + Refactored Continuation (`GapEqErr.bind_congr` & `mirGapBehaviors_env_congr`) -/

/--
Sequential caller using non-tail `TerminatorKind.call` with a post-call
continuation:
`fn seq_caller(x: u32) -> u32 { let y = ext_helper(x); y + y }`.
-/
def seqCallerBody : CapturedMir :=
  mkMirBody "test::seq_caller" 1
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy, mkDecl .mut u32MirTy]
    [ { statements := [mkStmt (.storageLive 2)]
        terminator := mkTerm
          (.call (fnItemOp "test::ext_helper") [.copy (locPlace 1)]
            (locPlace 2) (some 1) .continue_)
        isCleanup := false },
      { statements :=
          [mkStmt (.assign (locPlace 0)
            (.binaryOp .add (.copy (locPlace 2)) (.copy (locPlace 2))))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/--
Refactored sequential caller with a different post-call continuation
(`StorageLive(_3); _3 = y * 2; _0 = copy _3; return`, taking two extra steps):
`fn seq_caller_refactored(x: u32) -> u32 { let y = ext_helper(x); let t = y * 2; t }`.
-/
def seqCallerRefactoredBody : CapturedMir :=
  mkMirBody "test::seq_caller_refactored" 1
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy, mkDecl .mut u32MirTy,
     mkDecl .mut u32MirTy]
    [ { statements := [mkStmt (.storageLive 2)]
        terminator := mkTerm
          (.call (fnItemOp "test::ext_helper") [.copy (locPlace 1)]
            (locPlace 2) (some 1) .continue_)
        isCleanup := false },
      { statements :=
          [mkStmt (.storageLive 3),
           mkStmt (.assign (locPlace 3)
             (.binaryOp .mul (.copy (locPlace 2)) (u32ConstOp 2))),
           mkStmt (.assign (locPlace 0) (.use (.copy (locPlace 3))))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/-- Machine state of `seqCallerBody` right at the external call terminator. -/
def seqCallerAtCall (body : CapturedMir) (x : Nat) : MachineState :=
  let init := initMachineState body [.scalar ⟨x, 4⟩]
  { frame :=
      { blockIdx := 0
        stmtIdx := 1
        locals := init.frame.locals.set 2 .uninit }
    memory := init.memory }

/--
Call-handler law for `seqCallerBody`: the bounded run is literally the monadic
`bind` of the sealed external helper outcome with the post-call continuation.
-/
theorem seqCaller_run_eq_bind (env : MirCallEnv) (x fuel : Nat) :
    runMirWithGap env [] seqCallerBody (fuel + 2) [.scalar ⟨x, 4⟩] =
      (((env (extHelperReq x)).mapFault (fun _ => .ub)).mapGap
          (·.sealOutOfFuel "test::ext_helper")).bind (fun ans =>
        runMirStepsWithGap env seqCallerBody fuel
          (resumeExternalCall (seqCallerAtCall seqCallerBody x)
            (seqCallerAtCall seqCallerBody x).frame.locals
            (locPlace 2) 1 .continue_ ans)) :=
  (runGapSteps_succ_of_next (mirSiteGapStep env seqCallerBody)
      (s := mirSiteOfExec seqCallerBody
        (.running (initMachineStateWithCallees seqCallerBody [.scalar ⟨x, 4⟩] [])))
      (s' := mirSiteOfExec seqCallerBody (.running (seqCallerAtCall seqCallerBody x)))
      rfl (fuel + 1)).trans
    (runMirStepsWithGap_of_root_extCall (env := env) (body := seqCallerBody)
      (s := seqCallerAtCall seqCallerBody x) (req := extHelperReq x)
      (k := resumeExternalCall (seqCallerAtCall seqCallerBody x)
        (seqCallerAtCall seqCallerBody x).frame.locals
        (locPlace 2) 1 .continue_)
      rfl rfl rfl fuel)

/-- Call-handler law for `seqCallerRefactoredBody`: same request, different continuation. -/
theorem seqCallerRefactored_run_eq_bind (env : MirCallEnv) (x fuel : Nat) :
    runMirWithGap env [] seqCallerRefactoredBody (fuel + 2) [.scalar ⟨x, 4⟩] =
      (((env (extHelperReq x)).mapFault (fun _ => .ub)).mapGap
          (·.sealOutOfFuel "test::ext_helper")).bind (fun ans =>
        runMirStepsWithGap env seqCallerRefactoredBody fuel
          (resumeExternalCall (seqCallerAtCall seqCallerRefactoredBody x)
            (seqCallerAtCall seqCallerRefactoredBody x).frame.locals
            (locPlace 2) 1 .continue_ ans)) :=
  (runGapSteps_succ_of_next (mirSiteGapStep env seqCallerRefactoredBody)
      (s := mirSiteOfExec seqCallerRefactoredBody
        (.running (initMachineStateWithCallees seqCallerRefactoredBody [.scalar ⟨x, 4⟩] [])))
      (s' := mirSiteOfExec seqCallerRefactoredBody
        (.running (seqCallerAtCall seqCallerRefactoredBody x)))
      rfl (fuel + 1)).trans
    (runMirStepsWithGap_of_root_extCall (env := env) (body := seqCallerRefactoredBody)
      (s := seqCallerAtCall seqCallerRefactoredBody x) (req := extHelperReq x)
      (k := resumeExternalCall (seqCallerAtCall seqCallerRefactoredBody x)
        (seqCallerAtCall seqCallerRefactoredBody x).frame.locals
        (locPlace 2) 1 .continue_)
      rfl rfl rfl fuel)

/--
Post-call continuation agreement via `GapEqErr.bind_congr`: for **every**
`u32`-returning, panicking, aborting, UB, or gap-producing pure helper summary
`f`, the baseline continuation (`y + y`, 3 post-call steps) and the refactored
continuation (`let t = y * 2; t`, 5 post-call steps) are `GapEqErr`-related.
When `f` hits a gap, `GapEqErr.bind_congr` matches both runs without executing
either continuation.
-/
theorem seqCallerRefactored_gapEqErr_via_bind_congr
    (f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value)
    (hU32 : ∀ x v, f "test::ext_helper" [.scalar ⟨x, 4⟩] = .ok v →
      ∃ y, v = .scalar ⟨y, 4⟩)
    (x : Nat) :
    GapEqErr (· = ·) (· = ·)
      (runMirWithGap (MirCallEnv.ofPure f) [] seqCallerBody 5 [.scalar ⟨x, 4⟩])
      (runMirWithGap (MirCallEnv.ofPure f) [] seqCallerRefactoredBody 7 [.scalar ⟨x, 4⟩]) := by
  show GapEqErr (· = ·) (· = ·)
    (runMirWithGap (MirCallEnv.ofPure f) [] seqCallerBody (3 + 2) [.scalar ⟨x, 4⟩])
    (runMirWithGap (MirCallEnv.ofPure f) [] seqCallerRefactoredBody (5 + 2) [.scalar ⟨x, 4⟩])
  rw [seqCaller_run_eq_bind, seqCallerRefactored_run_eq_bind]
  refine GapEqErr.bind_congr
    (rVal := fun a₁ a₂ => a₁ = a₂ ∧
      ((∃ y, a₁ = .returned (.scalar ⟨y, 4⟩) unlinkedMemory) ∨
       a₁ = .panicked unlinkedMemory ∨ a₁ = .aborted))
    ?_ ?_
  · unfold MirCallEnv.ofPure extHelperReq
    cases hf : f "test::ext_helper" [.scalar ⟨x, 4⟩] with
    | ok v =>
      obtain ⟨y, rfl⟩ := hU32 x v hf
      exact ⟨rfl, Or.inl ⟨y, rfl⟩⟩
    | fault e =>
      cases e with
      | ub => exact (rfl : ExecFault.ub = ExecFault.ub)
      | panic => exact ⟨rfl, Or.inr (Or.inl rfl)⟩
      | abort => exact ⟨rfl, Or.inr (Or.inr rfl)⟩
    | gap g => exact (rfl : _ = _)
  · rintro a₁ a₂ ⟨rfl, ⟨y, rfl⟩ | rfl | rfl⟩
    · change GapEqErr (· = ·) (· = ·)
        (OutcomeWithGap.ok
          (Value.scalar ⟨wrapScalarBits (y + y) (scalarModulus 4), 4⟩, unlinkedMemory))
        (OutcomeWithGap.ok
          (Value.scalar ⟨wrapScalarBits (y * 2) (scalarModulus 4), 4⟩, unlinkedMemory))
      rw [Nat.mul_two]
      exact GapEqErr.refl (fun _ => rfl) (fun _ => rfl) _
    · exact GapEqErr.refl (fun _ => rfl) (fun _ => rfl)
        (OutcomeWithGap.fault ExecFault.panic)
    · exact GapEqErr.refl (fun _ => rfl) (fun _ => rfl)
        (OutcomeWithGap.fault ExecFault.abort)

/--
Fuel-free `ContextEquiv` for sequential non-tail callers over all `x : Nat` and
**every** `u32`-typed helper summary `f` — including unmodeled/gapping and
budget-exhausted (`outOfFuel`) summaries, with NO `hNoOOF` side condition!
-/
theorem seqCallerRefactored_contextEquiv_any_pure
    (f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value)
    (hU32 : ∀ x v, f "test::ext_helper" [.scalar ⟨x, 4⟩] = .ok v →
      ∃ y, v = .scalar ⟨y, 4⟩) :
    ContextEquiv (· = ·) (· = ·)
      (fun x : Nat =>
        mirGapBehaviors (MirCallEnv.ofPure f) [] seqCallerBody [.scalar ⟨x, 4⟩])
      (fun x : Nat =>
        mirGapBehaviors (MirCallEnv.ofPure f) [] seqCallerRefactoredBody [.scalar ⟨x, 4⟩]) := by
  intro x
  have hne : runMirWithGap (MirCallEnv.ofPure f) [] seqCallerBody 5 [.scalar ⟨x, 4⟩] ≠
      .gap .outOfFuel := by
    show runMirWithGap (MirCallEnv.ofPure f) [] seqCallerBody (3 + 2) [.scalar ⟨x, 4⟩] ≠ _
    rw [seqCaller_run_eq_bind]
    unfold MirCallEnv.ofPure extHelperReq
    cases hf : f "test::ext_helper" [.scalar ⟨x, 4⟩] with
    | ok v =>
      obtain ⟨y, rfl⟩ := hU32 x v hf
      exact fun h₀ => by cases h₀
    | fault e =>
      cases e <;> exact fun h₀ => by cases h₀
    | gap g =>
      intro h₀
      exact GapTag.sealOutOfFuel_ne_outOfFuel "test::ext_helper" _ (OutcomeWithGap.gap.inj h₀)
  exact mirGapBehaviors_equiv_of_runs hne
    (seqCallerRefactored_gapEqErr_via_bind_congr f hU32 x)

/-- Concrete gap-free pure helper: `x ↦ x + 1 (mod 2^32)`. -/
def incHelperSummary (_ : DefPath) (args : List Value) :
    OutcomeWithGap ExecFault (GapTag DefPath) Value :=
  match args with
  | [.scalar ⟨x, 4⟩] => .ok (.scalar ⟨wrapScalarBits (x + 1) (scalarModulus 4), 4⟩)
  | _ => .fault .ub

/-- Refactored pure helper: `x ↦ 1 + x (mod 2^32)`. -/
def incHelperRefactoredSummary (_ : DefPath) (args : List Value) :
    OutcomeWithGap ExecFault (GapTag DefPath) Value :=
  match args with
  | [.scalar ⟨x, 4⟩] => .ok (.scalar ⟨wrapScalarBits (1 + x) (scalarModulus 4), 4⟩)
  | _ => .fault .ub

private theorem incHelperSummary_eq_refactored (dp : DefPath) (args : List Value) :
    incHelperSummary dp args = incHelperRefactoredSummary dp args := by
  unfold incHelperSummary incHelperRefactoredSummary
  cases args with
  | nil => rfl
  | cons a rest =>
    cases a with
    | scalar sc =>
      cases sc with
      | mk bits sz =>
        cases sz with
        | zero => rfl
        | succ sz1 =>
          cases sz1 with
          | zero => rfl
          | succ sz2 =>
            cases sz2 with
            | zero => rfl
            | succ sz3 =>
              cases sz3 with
              | zero => rfl
              | succ sz4 =>
                cases sz4 with
                | zero =>
                  cases rest with
                  | nil =>
                    change OutcomeWithGap.ok
                        (Value.scalar ⟨wrapScalarBits (bits + 1) (scalarModulus 4), 4⟩) =
                      OutcomeWithGap.ok
                        (Value.scalar ⟨wrapScalarBits (1 + bits) (scalarModulus 4), 4⟩)
                    rw [Nat.add_comm bits 1]
                  | cons _ _ => rfl
                | succ _ => rfl
    | unit => rfl
    | ptr _ _ => rfl
    | aggregate _ _ => rfl

/--
Full modular composition canary:
1. Refactoring the sequential caller (`seqCallerBody → seqCallerRefactoredBody`)
   and refactoring the callee environment (`incHelperSummary →
   incHelperRefactoredSummary`) compose via `ContextEquiv.trans` and
   `mirGapBehaviors_env_congr`;
2. Because `incHelperSummary` is gap-free, `ContextEquiv.toProgramEquiv`
   upgrades the composed equivalence to full gap-free `ProgramEquiv` across all
   `x : Nat`; and
3. Against `unmodeledHelperSummary`, `ContextEquiv` still holds with zero
   gap-freedom proof for the helper!
-/
theorem seqCallerRefactored_modular_composition_and_upgrade :
    ProgramEquiv (· = ·) (· = ·)
        (fun x : Nat =>
          mirGapBehaviors (MirCallEnv.ofPure incHelperSummary) []
            seqCallerBody [.scalar ⟨x, 4⟩])
        (fun x : Nat =>
          mirGapBehaviors (MirCallEnv.ofPure incHelperRefactoredSummary) []
            seqCallerRefactoredBody [.scalar ⟨x, 4⟩]) ∧
      ContextEquiv (· = ·) (· = ·)
        (fun x : Nat =>
          mirGapBehaviors (MirCallEnv.ofPure unmodeledHelperSummary) []
            seqCallerBody [.scalar ⟨x, 4⟩])
        (fun x : Nat =>
          mirGapBehaviors (MirCallEnv.ofPure unmodeledHelperSummary) []
            seqCallerRefactoredBody [.scalar ⟨x, 4⟩]) := by
  have hCallerInc : ContextEquiv (· = ·) (· = ·)
      (fun x : Nat =>
        mirGapBehaviors (MirCallEnv.ofPure incHelperSummary) []
          seqCallerBody [.scalar ⟨x, 4⟩])
      (fun x : Nat =>
        mirGapBehaviors (MirCallEnv.ofPure incHelperSummary) []
          seqCallerRefactoredBody [.scalar ⟨x, 4⟩]) :=
    seqCallerRefactored_contextEquiv_any_pure incHelperSummary
      (fun x v hv => by cases hv; exact ⟨_, rfl⟩)
  have hEnv : ∀ req, GapEqErr (· = ·) (· = ·)
      (MirCallEnv.ofPure incHelperSummary req)
      (MirCallEnv.ofPure incHelperRefactoredSummary req) := fun req => by
    unfold MirCallEnv.ofPure
    rw [incHelperSummary_eq_refactored]
    exact GapEqErr.refl (fun _ => rfl) (fun _ => rfl) _
  have hCallee : ContextEquiv (· = ·) (· = ·)
      (fun x : Nat =>
        mirGapBehaviors (MirCallEnv.ofPure incHelperSummary) []
          seqCallerRefactoredBody [.scalar ⟨x, 4⟩])
      (fun x : Nat =>
        mirGapBehaviors (MirCallEnv.ofPure incHelperRefactoredSummary) []
          seqCallerRefactoredBody [.scalar ⟨x, 4⟩]) :=
    fun x => mirGapBehaviors_env_congr hEnv [.scalar ⟨x, 4⟩]
  have hComposed := ContextEquiv.trans
    (fun _ _ _ h₁ h₂ => h₁.trans h₂) (fun _ _ _ h₁ h₂ => h₁.trans h₂)
    hCallerInc hCallee
  have hGapFree : AllGapFree (fun x : Nat =>
      mirGapBehaviors (MirCallEnv.ofPure incHelperSummary) []
        seqCallerBody [.scalar ⟨x, 4⟩]) := fun x => by
    have hrun : (runMirWithGap (MirCallEnv.ofPure incHelperSummary) []
        seqCallerBody 5 [.scalar ⟨x, 4⟩]).isGapFree := by
      show (runMirWithGap (MirCallEnv.ofPure incHelperSummary) []
        seqCallerBody (3 + 2) [.scalar ⟨x, 4⟩]).isGapFree
      rw [seqCaller_run_eq_bind]
      exact trivial
    exact neverGap_mirGapBehaviors_of_run hrun
  have hUnmodeled : ContextEquiv (· = ·) (· = ·)
      (fun x : Nat =>
        mirGapBehaviors (MirCallEnv.ofPure unmodeledHelperSummary) []
          seqCallerBody [.scalar ⟨x, 4⟩])
      (fun x : Nat =>
        mirGapBehaviors (MirCallEnv.ofPure unmodeledHelperSummary) []
          seqCallerRefactoredBody [.scalar ⟨x, 4⟩]) :=
    seqCallerRefactored_contextEquiv_any_pure unmodeledHelperSummary
      (fun x v hv => by rw [unmodeledHelperSummary_eq] at hv; cases hv)
  exact ⟨hComposed.toProgramEquiv hGapFree, hUnmodeled⟩

/-! ### Part 5E: Sealed Callee Budgets, Diverging Loops, Inline Post-Call Gap Sites, Distinct-Memory Stuttering, and Gapping Spec Transfer -/

/--
Zero-fuel callee summary obtained by running `unsupportedHelperBody` with budget
`0`, producing the raw sentinel `.gap .outOfFuel`. `MirCallEnv.ofPure` MUST seal
this sentinel to `.gap (.budget "test::ext_helper")` rather than leaking raw
`.outOfFuel` into the outer evaluator.
-/
def zeroBudgetHelperSummary (_ : DefPath) (args : List Value) :
    OutcomeWithGap ExecFault (GapTag DefPath) Value :=
  (runMirWithGap MirCallEnv.unresolved [] unsupportedHelperBody 0 args).map Prod.fst

/-- 1-block infinite loop: `fn spin_loop() -> u32 { loop {} }`. -/
def spinLoopBody : CapturedMir :=
  mkMirBody "test::spin_loop" 0
    [mkDecl .mut u32MirTy]
    [ { statements := [], terminator := mkTerm (.goto 0), isCleanup := false } ]

/-- 2-block refactored infinite loop: `bb0 -> bb1 -> bb0`. -/
def spinTwoBlockBody : CapturedMir :=
  mkMirBody "test::spin_two_block" 0
    [mkDecl .mut u32MirTy]
    [ { statements := [], terminator := mkTerm (.goto 1), isCleanup := false },
      { statements := [], terminator := mkTerm (.goto 0), isCleanup := false } ]

/-- Every bounded run of `spinLoopBody` exhausts its fuel. -/
theorem spinLoop_run_outOfFuel (fuel : Nat) :
    runMirWithGap MirCallEnv.unresolved [] spinLoopBody fuel [] = .gap .outOfFuel := by
  let s₀ : MirSiteState :=
    mirSiteOfExec spinLoopBody (.running (initMachineStateWithCallees spinLoopBody [] []))
  change runGapSteps (mirSiteGapStep MirCallEnv.unresolved spinLoopBody) fuel s₀ =
    .gap .outOfFuel
  induction fuel with
  | zero => rfl
  | succ n ih =>
    exact (runGapSteps_succ_of_next (mirSiteGapStep MirCallEnv.unresolved spinLoopBody)
      (rfl : mirSiteGapStep MirCallEnv.unresolved spinLoopBody s₀ = .next s₀) n).trans ih

/--
Sealed budget-exhausted callee canary:
1. Calling `zeroBudgetHelperSummary` seals `.outOfFuel` to
   `.gap (.budget "test::ext_helper")`;
2. `mirGapBehaviors` contains `.gap (.budget "test::ext_helper")`, so it is NOT
   vacuously `NeverGap`; and
3. It is NOT `OutcomeSetEquiv` to the genuinely diverging `spinLoopBody`
   (whose `mirGapBehaviors` is empty).
-/
theorem seqCaller_zeroBudgetHelper_sealed_and_not_spinLoop (x : Nat) :
    let env := MirCallEnv.ofPure zeroBudgetHelperSummary
    runMirWithGap env [] seqCallerBody 3 [.scalar ⟨x, 4⟩] =
        .gap (.budget "test::ext_helper") ∧
      mirGapBehaviors env [] seqCallerBody [.scalar ⟨x, 4⟩]
        (.gap (.budget "test::ext_helper")) ∧
      ¬ NeverGap (mirGapBehaviors env [] seqCallerBody [.scalar ⟨x, 4⟩]) ∧
      ¬ OutcomeSetEquiv (GapEqErr (· = ·) (· = ·))
        (mirGapBehaviors env [] seqCallerBody [.scalar ⟨x, 4⟩])
        (mirGapBehaviors MirCallEnv.unresolved [] spinLoopBody []) := by
  dsimp only
  have hrun : runMirWithGap (MirCallEnv.ofPure zeroBudgetHelperSummary) []
      seqCallerBody 3 [.scalar ⟨x, 4⟩] = .gap (.budget "test::ext_helper") := rfl
  have hmem : mirGapBehaviors (MirCallEnv.ofPure zeroBudgetHelperSummary) []
      seqCallerBody [.scalar ⟨x, 4⟩] (.gap (.budget "test::ext_helper")) :=
    (mirGapBehaviors_iff_of_run
      (ne_outOfFuel_of_eq hrun (fun h₀ => by cases h₀)) _).mpr hrun.symm
  refine ⟨hrun, hmem, fun hng => hng hmem, fun heq => ?_⟩
  obtain ⟨o₂, ⟨hne₂, fuel, hrun₂⟩, _⟩ := heq.forward hmem
  exact hne₂ (hrun₂.symm.trans (spinLoop_run_outOfFuel fuel))

/--
Fuel-free `mirTree` adequacy on genuinely diverging loops: `spinLoopBody` and
`spinTwoBlockBody` never halt (`¬ OutcomeSet.Terminates`), yet both are
`OutcomeSet.Defined` and `ContextEquivOn (· = [])` via `mirGapBehaviors_equiv_of_stutter_with`,
and `mirContextEquivOn_toPartial_eq_of_defined` proves `MirNoUBTree` and equal
trace-erased `ITree.toPartial` semantics for BOTH diverging `mirTree`s!
-/
theorem spinLoop_mirTree_adequate_and_toPartial_eq :
    let t₁ := mirTree spinLoopBody (initMachineStateWithCallees spinLoopBody [] [])
    let t₂ := mirTree spinTwoBlockBody (initMachineStateWithCallees spinTwoBlockBody [] [])
    ¬ OutcomeSet.Terminates (mirGapBehaviors MirCallEnv.unresolved [] spinLoopBody []) ∧
      MirNoUBTree t₁ ∧ MirNoUBTree t₂ ∧
      Partial.map (BehaviorSet.map Prod.snd) t₁.toPartial =
        Partial.map (BehaviorSet.map Prod.snd) t₂.toPartial := by
  dsimp only
  have hEmpty : ∀ o, ¬ mirGapBehaviors MirCallEnv.unresolved [] spinLoopBody [] o :=
    fun _ ⟨hne, fuel, hrun⟩ => hne (hrun.symm.trans (spinLoop_run_outOfFuel fuel))
  have hNotTerm :
      ¬ OutcomeSet.Terminates (mirGapBehaviors MirCallEnv.unresolved [] spinLoopBody []) :=
    fun ⟨o, ho⟩ => hEmpty o ho
  have hDef₁ : OutcomeSet.Defined ExecFault.isUB
      (mirGapBehaviors MirCallEnv.unresolved [] spinLoopBody []) :=
    fun o ho => False.elim (hEmpty o ho)
  have hEqOn : ContextEquivOn (fun args => args = []) (· = ·) (· = ·)
      (mirGapBehaviors MirCallEnv.unresolved [] spinLoopBody)
      (mirGapBehaviors MirCallEnv.unresolved [] spinTwoBlockBody) := by
    intro args hargs
    subst hargs
    let s₁ : MirSiteState :=
      mirSiteOfExec spinLoopBody (.running (initMachineStateWithCallees spinLoopBody [] []))
    let init₂ := initMachineStateWithCallees spinTwoBlockBody [] []
    let s₂₀ : MirSiteState := mirSiteOfExec spinTwoBlockBody (.running init₂)
    let s₂₁ : MirSiteState :=
      mirSiteOfExec spinTwoBlockBody
        (.running { init₂ with frame := { init₂.frame with blockIdx := 1 } })
    let R : MirSiteState → MirSiteState → Prop :=
      fun a b => a = s₁ ∧ (b = s₂₀ ∨ b = s₂₁)
    refine mirGapBehaviors_equiv_of_stutter_with (R := R) (fun _ => rfl) ?_ ⟨rfl, Or.inl rfl⟩
    rintro a b ⟨rfl, rfl | rfl⟩
    · exact ⟨0, 0, s₁, s₂₀, .refl _, .refl _, StepNodeRelWith.tau ⟨rfl, Or.inr rfl⟩⟩
    · exact ⟨0, 0, s₁, s₂₁, .refl _, .refl _, StepNodeRelWith.tau ⟨rfl, Or.inl rfl⟩⟩
  exact ⟨hNotTerm, mirContextEquivOn_toPartial_eq_of_defined hEqOn rfl hDef₁⟩

/--
Modeled-phase inline helper (`phase := .runtimePostCleanup`) whose post-call
destination write (`{ local_ := 1, projection := [.field 0 u32MirTy, .deref] }`)
transitions `resumeExternalCall` directly to `MirExecState.faulted .unsupported`,
erasing `MachineState`. `MirSiteState` must stamp the inline helper's `DefPath`
rather than the outer caller's `DefPath`.
-/
def postCallUnsupportedHelperBody (name : DefPath) : CapturedMir :=
  mkMirBody name 1
    [mkDecl .mut u32MirTy, mkDecl .mut u32MirTy]
    [ { statements := []
        terminator := mkTerm
          (.call (fnItemOp "test::ext_helper") [.copy (locPlace 1)]
            { local_ := 1, projection := [.field 0 u32MirTy, .deref] }
            (some 1) .continue_)
        isCleanup := false },
      returnBlock ]

def postCallLinkedHelpers : List CapturedMir :=
  [postCallUnsupportedHelperBody "test::post_call_helper",
   postCallUnsupportedHelperBody "test::other_post_call_helper"]

def callerPostCallBranchingBody : CapturedMir :=
  mkMirBody "test::caller_post_call_branching" 2
    [mkDecl .mut u32MirTy, mkDecl .not boolMirTy, mkDecl .not u32MirTy]
    [ flagSwitchBlock,
      { statements :=
          [mkStmt (.assign (locPlace 0)
            (.binaryOp .add (.copy (locPlace 2)) (.copy (locPlace 2))))]
        terminator := mkTerm .return_
        isCleanup := false },
      helperCallBlock "test::post_call_helper",
      returnBlock ]

def callerPostCallRefactoredBody : CapturedMir :=
  mkMirBody "test::caller_post_call_refactored" 2
    [mkDecl .mut u32MirTy, mkDecl .not boolMirTy, mkDecl .not u32MirTy,
     mkDecl .mut u32MirTy]
    [ flagSwitchBlock,
      { statements :=
          [mkStmt (.storageLive 3),
           mkStmt (.assign (locPlace 3)
             (.binaryOp .mul (.copy (locPlace 2)) (u32ConstOp 2))),
           mkStmt (.assign (locPlace 0) (.use (.copy (locPlace 3))))]
        terminator := mkTerm .return_
        isCleanup := false },
      helperCallBlock "test::post_call_helper",
      returnBlock ]

def callerOtherPostCallBody : CapturedMir :=
  mkMirBody "test::caller_other_post_call" 2
    [mkDecl .mut u32MirTy, mkDecl .not boolMirTy, mkDecl .not u32MirTy]
    [ flagSwitchBlock,
      { statements :=
          [mkStmt (.assign (locPlace 0)
            (.binaryOp .add (.copy (locPlace 2)) (.copy (locPlace 2))))]
        terminator := mkTerm .return_
        isCleanup := false },
      helperCallBlock "test::other_post_call_helper",
      returnBlock ]

def postCallSem (body : CapturedMir) :
    GapSem (Bool × Nat) ExecFault (GapTag DefPath) MirReturn :=
  fun q => mirGapBehaviors (MirCallEnv.ofPure incHelperSummary) postCallLinkedHelpers
    body (callerArgs q)

/--
Inline-callee post-call `.faulted .unsupported` site attribution canary:
1. Both `callerPostCallBranchingBody` and `callerPostCallRefactoredBody` report
   `.gap (.unsupported "test::post_call_helper")` (NOT their own root `DefPath`s)
   on `flag = false`;
2. They satisfy `ContextEquiv` across all `(flag, x)`; and
3. Redirecting to `other_post_call_helper` produces
   `.gap (.unsupported "test::other_post_call_helper")` and is rejected (`¬ ContextEquiv`).
-/
theorem inlineCallee_postCall_unsupported_site_and_contextEquiv :
    runMirWithGap (MirCallEnv.ofPure incHelperSummary) postCallLinkedHelpers
        callerPostCallBranchingBody 5 (callerArgs (false, 7)) =
        .gap (.unsupported "test::post_call_helper") ∧
      runMirWithGap (MirCallEnv.ofPure incHelperSummary) postCallLinkedHelpers
          callerPostCallRefactoredBody 5 (callerArgs (false, 7)) =
        .gap (.unsupported "test::post_call_helper") ∧
      ContextEquiv (· = ·) (· = ·)
        (postCallSem callerPostCallBranchingBody)
        (postCallSem callerPostCallRefactoredBody) ∧
      ¬ ContextEquiv (· = ·) (· = ·)
        (postCallSem callerPostCallBranchingBody)
        (postCallSem callerOtherPostCallBody) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro ⟨flag, x⟩
    cases flag with
    | true =>
      have h₁ : runMirWithGap (MirCallEnv.ofPure incHelperSummary) postCallLinkedHelpers
          callerPostCallBranchingBody 3 (callerArgs (true, x)) =
          .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩,
            (initMachineStateWithCallees callerPostCallBranchingBody []
              postCallLinkedHelpers).memory) := rfl
      have h₂ : runMirWithGap (MirCallEnv.ofPure incHelperSummary) postCallLinkedHelpers
          callerPostCallRefactoredBody 5 (callerArgs (true, x)) =
          .ok (.scalar ⟨wrapScalarBits (x * 2) (scalarModulus 4), 4⟩,
            (initMachineStateWithCallees callerPostCallBranchingBody []
              postCallLinkedHelpers).memory) := rfl
      refine mirGapBehaviors_equiv_of_runs (fuel₂ := 5)
        (ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀)) ?_
      rw [h₁, h₂, Nat.mul_two]
      exact GapEqErr.refl (fun _ => rfl) (fun _ => rfl) _
    | false =>
      have h₁ : runMirWithGap (MirCallEnv.ofPure incHelperSummary) postCallLinkedHelpers
          callerPostCallBranchingBody 5 (callerArgs (false, x)) =
          .gap (.unsupported "test::post_call_helper") := rfl
      have h₂ : runMirWithGap (MirCallEnv.ofPure incHelperSummary) postCallLinkedHelpers
          callerPostCallRefactoredBody 5 (callerArgs (false, x)) =
          .gap (.unsupported "test::post_call_helper") := rfl
      refine mirGapBehaviors_equiv_of_runs (fuel₂ := 5)
        (ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀)) ?_
      rw [h₁, h₂]
      exact GapEqErr.refl (fun _ => rfl) (fun _ => rfl) _
  · intro h
    have h₁ : runMirWithGap (MirCallEnv.ofPure incHelperSummary) postCallLinkedHelpers
        callerPostCallBranchingBody 5 (callerArgs (false, 0)) =
        .gap (.unsupported "test::post_call_helper") := rfl
    have h₂ : runMirWithGap (MirCallEnv.ofPure incHelperSummary) postCallLinkedHelpers
        callerOtherPostCallBody 5 (callerArgs (false, 0)) =
        .gap (.unsupported "test::other_post_call_helper") := rfl
    have hEq := (mirGapBehaviors_equiv_iff_of_runs
      (ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀))
      (ne_outOfFuel_of_eq h₂ (fun h₀ => by cases h₀))).mp (h (false, 0))
    rw [h₁, h₂] at hEq
    exact absurd (GapTag.unsupported.inj hEq) (by decide)

/-- Shared-reference MIR type `&u32` for the distinct-memory borrow canary. -/
@[reducible] def u32SharedRefMirTy : Ty :=
  { kind := .ref .not (.uint .u32), layoutIdx := 0 }

/--
Refactored sequential caller that allocates a temporary local borrow `&_1` before
invoking `"test::ext_helper"`, mutating `memory.borrows` and `memory.nextTag` so
its `MirCallReq` has `req₂.memory ≠ req₁.memory`:
`fn borrow_before_call(x: u32) -> u32 { let _r = &x; let y = ext_helper(x); y * 2 }`.
-/
def borrowBeforeCallBody : CapturedMir :=
  mkMirBody "test::borrow_before_call" 1
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy, mkDecl .mut u32MirTy,
     mkDecl .mut u32SharedRefMirTy]
    [ { statements :=
          [mkStmt (.storageLive 2),
           mkStmt (.storageLive 3),
           mkStmt (.assign (locPlace 3) (.ref .shared (locPlace 1)))]
        terminator := mkTerm
          (.call (fnItemOp "test::ext_helper") [.copy (locPlace 1)]
            (locPlace 2) (some 1) .continue_)
        isCleanup := false },
      { statements :=
          [mkStmt (.assign (locPlace 0)
            (.binaryOp .mul (.copy (locPlace 2)) (u32ConstOp 2)))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/-- Machine state of `borrowBeforeCallBody` right at the external call terminator. -/
def borrowBeforeCallAtCall (x : Nat) : MachineState :=
  let init := initMachineState borrowBeforeCallBody [.scalar ⟨x, 4⟩]
  match stepMirFn borrowBeforeCallBody init with
  | .tau (.running s1) =>
    match stepMirFn borrowBeforeCallBody s1 with
    | .tau (.running s2) =>
      match stepMirFn borrowBeforeCallBody s2 with
      | .tau (.running s3) => s3
      | _ => init
    | _ => init
  | _ => init

/-- The external call request emitted by `borrowBeforeCallBody`. -/
def borrowBeforeCallReq (x : Nat) : MirCallReq :=
  { defPath := "test::ext_helper"
    typeArgs := []
    args := [.scalar ⟨x, 4⟩]
    memory := (borrowBeforeCallAtCall x).memory }

/--
Distinct-memory external-call canary (`StepNodeRelWith` + `MirCallEnv.ofPure_rel_of_same_target`):
1. `borrowBeforeCallReq x ≠ extHelperReq x` because `borrowBeforeCallBody` has an
   active borrow entry (`(borrowBeforeCallReq x).memory ≠ (extHelperReq x).memory`),
   so rigid `StepNodeRel.vis` (`i₁ = i₂`) CANNOT be applied; and
2. `mirGapBehaviors_equiv_of_stutter_with` + `MirCallEnv.ofPure_rel_of_same_target`
   proves return-value `ContextEquiv (fun r₁ r₂ => r₁.1 = r₂.1) (· = ·)` across
   all `x : Nat` and **every** `u32`-returning/faulting/gapping pure helper `f`!
-/
theorem borrowBeforeCall_distinct_memory_contextEquiv
    (f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value)
    (hU32 : ∀ x v, f "test::ext_helper" [.scalar ⟨x, 4⟩] = .ok v →
      ∃ y, v = .scalar ⟨y, 4⟩) :
    (∀ x, (borrowBeforeCallReq x).memory ≠ (extHelperReq x).memory) ∧
      ContextEquiv (fun r₁ r₂ => r₁.1 = r₂.1) (· = ·)
        (fun x : Nat =>
          mirGapBehaviors (MirCallEnv.ofPure f) [] seqCallerBody [.scalar ⟨x, 4⟩])
        (fun x : Nat =>
          mirGapBehaviors (MirCallEnv.ofPure f) [] borrowBeforeCallBody [.scalar ⟨x, 4⟩]) := by
  refine ⟨(fun x hmem => by
      have hlen := congrArg (fun m => m.borrows.length) hmem
      cases hlen), ?_⟩
  intro x
  let env := MirCallEnv.ofPure f
  let s₁₀ : MirSiteState :=
    mirSiteOfExec seqCallerBody
      (.running (initMachineStateWithCallees seqCallerBody [.scalar ⟨x, 4⟩] []))
  let s₂₀ : MirSiteState :=
    mirSiteOfExec borrowBeforeCallBody
      (.running (initMachineStateWithCallees borrowBeforeCallBody [.scalar ⟨x, 4⟩] []))
  let R : MirSiteState → MirSiteState → Prop :=
    fun a b =>
      (a = s₁₀ ∧ b = s₂₀) ∨
      (∃ y,
        a = mirNextSiteState seqCallerBody
              (mirSiteOfExec seqCallerBody (.running (seqCallerAtCall seqCallerBody x)))
              (resumeExternalCall (seqCallerAtCall seqCallerBody x)
                (seqCallerAtCall seqCallerBody x).frame.locals
                (locPlace 2) 1 .continue_ (.returned (.scalar ⟨y, 4⟩) (extHelperReq x).memory)) ∧
        b = mirNextSiteState borrowBeforeCallBody
              (mirSiteOfExec borrowBeforeCallBody (.running (borrowBeforeCallAtCall x)))
              (resumeExternalCall (borrowBeforeCallAtCall x)
                (borrowBeforeCallAtCall x).frame.locals
                (locPlace 2) 1 .continue_
                (.returned (.scalar ⟨y, 4⟩) (borrowBeforeCallReq x).memory))) ∨
      (a = .halted .panic ∧ b = .halted .panic) ∨
      (a = .halted .abort ∧ b = .halted .abort)
  refine mirGapBehaviors_equiv_of_stutter_with (R := R) (fun _ => rfl) ?_ (Or.inl ⟨rfl, rfl⟩)
  intro a b hR
  rcases hR with ⟨rfl, rfl⟩ | ⟨y, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · let t₁ : MirSiteState :=
      mirSiteOfExec seqCallerBody (.running (seqCallerAtCall seqCallerBody x))
    let t₂ : MirSiteState :=
      mirSiteOfExec borrowBeforeCallBody (.running (borrowBeforeCallAtCall x))
    have hr₁ : GapReach (mirSiteGapStep env seqCallerBody) 1 s₁₀ t₁ :=
      .step rfl (.refl _)
    have hr₂ : GapReach (mirSiteGapStep env borrowBeforeCallBody) 3 s₂₀ t₂ :=
      .step rfl (.step rfl (.step rfl (.refl _)))
    refine ⟨1, 3, t₁, t₂, hr₁, hr₂, ?_⟩
    change StepNodeRelWith (mirGapHandle env) (mirGapHandle env)
      R (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
      (mirSiteOfState seqCallerBody t₁) (mirSiteOfState borrowBeforeCallBody t₂)
      (.vis (.inr (.inr (.call (extHelperReq x))))
        (fun ans => mirNextSiteState seqCallerBody t₁
          (resumeExternalCall (seqCallerAtCall seqCallerBody x)
            (seqCallerAtCall seqCallerBody x).frame.locals (locPlace 2) 1 .continue_ ans)))
      (.vis (.inr (.inr (.call (borrowBeforeCallReq x))))
        (fun ans => mirNextSiteState borrowBeforeCallBody t₂
          (resumeExternalCall (borrowBeforeCallAtCall x)
            (borrowBeforeCallAtCall x).frame.locals (locPlace 2) 1 .continue_ ans)))
    refine StepNodeRelWith.vis _
      (MirCallEnv.mirGapHandle_ofPure_rel_of_same_target f
        (req₁ := extHelperReq x) (req₂ := borrowBeforeCallReq x) rfl rfl) ?_
    rintro a₁ a₂ ho₁ _ (⟨v, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · obtain ⟨hf, _⟩ := MirCallEnv.mirGapHandle_ofPure_eq_ok_returned ho₁
      obtain ⟨y, rfl⟩ := hU32 x v hf
      exact Or.inr (Or.inl ⟨y, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · refine ⟨1, 1, _, _, .step rfl (.refl _), .step rfl (.refl _), ?_⟩
    refine StepNodeRelWith.normal ?_
    change Value.scalar ⟨wrapScalarBits (y + y) (scalarModulus 4), 4⟩ =
      Value.scalar ⟨wrapScalarBits (y * 2) (scalarModulus 4), 4⟩
    rw [Nat.mul_two]
  · exact ⟨0, 0, .halted .panic, .halted .panic, .refl _, .refl _, StepNodeRelWith.panic⟩
  · exact ⟨0, 0, .halted .abort, .halted .abort, .refl _, .refl _, StepNodeRelWith.abort⟩

/--
Direct `valSemantics` `ExactPass` and `valLanguage` / `outcomeLanguage` contract
transfer on gapping callers (`callerBranchingBody → callerRefactoredBody`), with
NO global `ProgramEquiv` (`callerRefactored_not_programEquiv`): a contract scoped
to `q.1 = true ∧ q.2 + q.2 < 2^32` transfers cleanly across `ContextEquiv` while
`q.1 = false` continues to hit `.gap (.unsupported "test::unmodeled_helper")`.
-/
theorem callerRefactored_valExactPass_and_spec_transfer :
    let valSpec : (valLanguage callerGapSem).Behavior :=
      Language.ContractSpec (valLanguage callerGapSem)
        (fun q => q.1 = true)
        (fun q => q.2 + q.2 < 4294967296)
        (fun q r => r.1 = Value.scalar ⟨q.2 + q.2, 4⟩)
    let outSpec : (outcomeLanguage callerGapSem).Behavior :=
      Language.ContractSpec (outcomeLanguage callerGapSem)
        (fun q => q.1 = true)
        (fun q => q.2 + q.2 < 4294967296)
        (fun q out => out = .normal (Value.scalar ⟨q.2 + q.2, 4⟩, linkedMemory))
    ExactPass (valSemantics callerGapSem) (valSemantics callerGapSem) id id
        callerBranchingBody callerRefactoredBody ∧
      ((valLanguage callerGapSem).sem callerRefactoredBody ≤ valSpec) ∧
      ((outcomeLanguage callerGapSem).sem callerRefactoredBody ≤ outSpec) := by
  dsimp only
  refine ⟨ContextEquiv.toValExactPass_eq callerRefactored_contextEquiv, ?_, ?_⟩
  · refine ContextEquiv.valTransfer_spec callerRefactored_contextEquiv ?_
    rintro ⟨flag, x⟩ (rfl : flag = true)
    have hrun : runMirWithGap MirCallEnv.unresolved linkedHelpers
        callerBranchingBody 3 (callerArgs (true, x)) =
        .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, linkedMemory) :=
      callerBranching_run_true x
    have hne : runMirWithGap MirCallEnv.unresolved linkedHelpers
        callerBranchingBody 3 (callerArgs (true, x)) ≠ .gap .outOfFuel :=
      callerBranching_run_ne_outOfFuel (true, x)
    have hOnly : OutcomeSet.OnlyValues (callerGapSem callerBranchingBody (true, x)) := by
      intro o ho
      rw [(mirGapBehaviors_iff_of_run hne o).mp ho, hrun]
      exact ⟨_, rfl⟩
    refine ⟨hOnly, fun r hr hx => ?_⟩
    have heq := (mirGapBehaviors_iff_of_run hne (.ok r)).mp hr
    rw [hrun, wrapScalarBits_of_lt (show x + x < scalarModulus 4 from hx)] at heq
    cases OutcomeWithGap.ok.inj heq
    rfl
  · refine ContextEquiv.outcomeTransfer_spec callerRefactored_contextEquiv ?_
    rintro ⟨flag, x⟩ (rfl : flag = true)
    have hrun : runMirWithGap MirCallEnv.unresolved linkedHelpers
        callerBranchingBody 3 (callerArgs (true, x)) =
        .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, linkedMemory) :=
      callerBranching_run_true x
    have hne : runMirWithGap MirCallEnv.unresolved linkedHelpers
        callerBranchingBody 3 (callerArgs (true, x)) ≠ .gap .outOfFuel :=
      callerBranching_run_ne_outOfFuel (true, x)
    have hDef : OutcomeSet.Defined ExecFault.isUB
        (callerGapSem callerBranchingBody (true, x)) :=
      defined_mirGapBehaviors_of_run (fuel := 3) (by rw [hrun]; exact trivial)
    refine ⟨hDef, fun out hout hx => ?_⟩
    have heq := (mirGapBehaviors_iff_of_run hne (classifyOutcome out)).mp hout
    rw [hrun, wrapScalarBits_of_lt (show x + x < scalarModulus 4 from hx)] at heq
    cases out with
    | normal r => cases OutcomeWithGap.ok.inj heq; rfl
    | panic => cases heq
    | abort => cases heq

/-! ### Part 5F: Handler-Boundary Sealing, Inline `return_` Destination Attribution, and Direct Trusted `MirLang` / `mirTree` `ExactPass` -/

/--
Raw unsealed `MirCallEnv` that returns the outer evaluator's `.gap .outOfFuel`
sentinel directly, bypassing `MirCallEnv.ofPure` / `MirCallEnv.seal`.
-/
def rawOOFEnv : MirCallEnv :=
  fun _ => .gap .outOfFuel

/--
Handler-boundary sealing canary: even for a raw unsealed `MirCallEnv` that
fails `MirCallEnv.IsSealed`, `mirGapHandle` seals `.gap .outOfFuel` into
`.gap (.budget req.defPath)` unconditionally, so `mirGapBehaviors` never
collapses to `∅` (`¬ NeverGap`, and `¬ OutcomeSetEquiv` against `spinLoopBody`).
-/
theorem seqCaller_rawOOFEnv_sealed_and_not_spinLoop (x : Nat) :
    ¬ rawOOFEnv.IsSealed ∧
      runMirWithGap rawOOFEnv [] seqCallerBody 3 [.scalar ⟨x, 4⟩] =
        .gap (.budget "test::ext_helper") ∧
      mirGapBehaviors rawOOFEnv [] seqCallerBody [.scalar ⟨x, 4⟩]
        (.gap (.budget "test::ext_helper")) ∧
      ¬ NeverGap (mirGapBehaviors rawOOFEnv [] seqCallerBody [.scalar ⟨x, 4⟩]) ∧
      ¬ OutcomeSetEquiv (GapEqErr (· = ·) (· = ·))
        (mirGapBehaviors rawOOFEnv [] seqCallerBody [.scalar ⟨x, 4⟩])
        (mirGapBehaviors MirCallEnv.unresolved [] spinLoopBody []) := by
  have hUnsealed : ¬ rawOOFEnv.IsSealed := fun h => h (extHelperReq x) rfl
  have hrun : runMirWithGap rawOOFEnv [] seqCallerBody 3 [.scalar ⟨x, 4⟩] =
      .gap (.budget "test::ext_helper") := rfl
  have hmem : mirGapBehaviors rawOOFEnv [] seqCallerBody [.scalar ⟨x, 4⟩]
      (.gap (.budget "test::ext_helper")) :=
    (mirGapBehaviors_iff_of_run
      (ne_outOfFuel_of_eq hrun (fun h₀ => by cases h₀)) _).mpr hrun.symm
  refine ⟨hUnsealed, hrun, hmem, fun hng => hng hmem, fun heq => ?_⟩
  obtain ⟨o₂, ⟨hne₂, fuel, hrun₂⟩, _⟩ := heq.forward hmem
  exact hne₂ (hrun₂.symm.trans (spinLoop_run_outOfFuel fuel))

/-- Modeled-phase inline identity helper: `fn id_helper(x: u32) -> u32 { x }`. -/
def idHelperBody : CapturedMir :=
  mkMirBody "test::id_helper" 1
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy]
    [ { statements := [mkStmt (.assign (locPlace 0) (.use (.copy (locPlace 1))))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/--
Caller invoking inline `idHelperBody` with an unmodeled destination projection
`[.field 0 u32MirTy, .deref]`: `idHelperBody` executes cleanly up to
`TerminatorKind.return_`, where `writeReturnDestination` fails on the caller's
destination projection.
-/
def callerWithBadReturnDest (name : DefPath) : CapturedMir :=
  mkMirBody name 1
    [mkDecl .mut u32MirTy, mkDecl .mut u32MirTy]
    [ { statements := []
        terminator := mkTerm
          (.call (fnItemOp "test::id_helper") [.copy (locPlace 1)]
            { local_ := 1, projection := [.field 0 u32MirTy, .deref] }
            (some 1) .continue_)
        isCleanup := false },
      returnBlock ]

def callerBadDestA : CapturedMir :=
  callerWithBadReturnDest "test::caller_bad_dest_a"

def callerBadDestB : CapturedMir :=
  callerWithBadReturnDest "test::caller_bad_dest_b"

def midBadDestHelperBody : CapturedMir :=
  callerWithBadReturnDest "test::mid_bad_dest_helper"

def returnDestLinkedHelpers : List CapturedMir :=
  [midBadDestHelperBody, idHelperBody]

def outerBadDestBranchingBody : CapturedMir :=
  mkMirBody "test::outer_bad_dest_branching" 2
    [mkDecl .mut u32MirTy, mkDecl .not boolMirTy, mkDecl .not u32MirTy]
    [ flagSwitchBlock,
      { statements :=
          [mkStmt (.assign (locPlace 0)
            (.binaryOp .add (.copy (locPlace 2)) (.copy (locPlace 2))))]
        terminator := mkTerm .return_
        isCleanup := false },
      helperCallBlock "test::mid_bad_dest_helper",
      returnBlock ]

def outerBadDestRefactoredBody : CapturedMir :=
  mkMirBody "test::outer_bad_dest_refactored" 2
    [mkDecl .mut u32MirTy, mkDecl .not boolMirTy, mkDecl .not u32MirTy,
     mkDecl .mut u32MirTy]
    [ flagSwitchBlock,
      { statements :=
          [mkStmt (.storageLive 3),
           mkStmt (.assign (locPlace 3)
             (.binaryOp .mul (.copy (locPlace 2)) (u32ConstOp 2))),
           mkStmt (.assign (locPlace 0) (.use (.copy (locPlace 3))))]
        terminator := mkTerm .return_
        isCleanup := false },
      helperCallBlock "test::mid_bad_dest_helper",
      returnBlock ]

/--
Inline-callee `TerminatorKind.return_` destination-write attribution canary:
1. When `callerBadDestA` and `callerBadDestB` call modeled `idHelperBody` with
   an unmodeled destination projection, `mirRunningFailSite` attributes the gap
   to `"test::caller_bad_dest_a"` vs `"test::caller_bad_dest_b"` (the frame
   owning `caller.destination`), NEVER blaming `"test::id_helper"`;
2. Consequently `callerBadDestA` and `callerBadDestB` are rejected
   (`¬ ContextEquiv`); and
3. When two refactored outer callers share `midBadDestHelperBody` (which owns
   the unmodeled destination in its call to `idHelperBody`), both stamp
   `"test::mid_bad_dest_helper"` and satisfy `ContextEquiv` across all `(flag, x)`.
-/
theorem inlineCallee_returnDest_gap_attribution_and_contextEquiv :
    runMirWithGap MirCallEnv.unresolved [idHelperBody]
        callerBadDestA 4 [.scalar ⟨7, 4⟩] =
        .gap (.unsupported "test::caller_bad_dest_a") ∧
      runMirWithGap MirCallEnv.unresolved [idHelperBody]
          callerBadDestB 4 [.scalar ⟨7, 4⟩] =
        .gap (.unsupported "test::caller_bad_dest_b") ∧
      ¬ ContextEquiv (· = ·) (· = ·)
        (fun x : Nat =>
          mirGapBehaviors MirCallEnv.unresolved [idHelperBody]
            callerBadDestA [.scalar ⟨x, 4⟩])
        (fun x : Nat =>
          mirGapBehaviors MirCallEnv.unresolved [idHelperBody]
            callerBadDestB [.scalar ⟨x, 4⟩]) ∧
      runMirWithGap MirCallEnv.unresolved returnDestLinkedHelpers
          outerBadDestBranchingBody 6 (callerArgs (false, 7)) =
        .gap (.unsupported "test::mid_bad_dest_helper") ∧
      ContextEquiv (· = ·) (· = ·)
        (fun q : Bool × Nat =>
          mirGapBehaviors MirCallEnv.unresolved returnDestLinkedHelpers
            outerBadDestBranchingBody (callerArgs q))
        (fun q : Bool × Nat =>
          mirGapBehaviors MirCallEnv.unresolved returnDestLinkedHelpers
            outerBadDestRefactoredBody (callerArgs q)) := by
  refine ⟨rfl, rfl, ?_, rfl, ?_⟩
  · intro h
    have h₁ : runMirWithGap MirCallEnv.unresolved [idHelperBody]
        callerBadDestA 4 [.scalar ⟨0, 4⟩] =
        .gap (.unsupported "test::caller_bad_dest_a") := rfl
    have h₂ : runMirWithGap MirCallEnv.unresolved [idHelperBody]
        callerBadDestB 4 [.scalar ⟨0, 4⟩] =
        .gap (.unsupported "test::caller_bad_dest_b") := rfl
    have hEq := (mirGapBehaviors_equiv_iff_of_runs
      (ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀))
      (ne_outOfFuel_of_eq h₂ (fun h₀ => by cases h₀))).mp (h 0)
    rw [h₁, h₂] at hEq
    exact absurd (GapTag.unsupported.inj hEq) (by decide)
  · intro ⟨flag, x⟩
    cases flag with
    | true =>
      have h₁ : runMirWithGap MirCallEnv.unresolved returnDestLinkedHelpers
          outerBadDestBranchingBody 3 (callerArgs (true, x)) =
          .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩,
            (initMachineStateWithCallees outerBadDestBranchingBody []
              returnDestLinkedHelpers).memory) := rfl
      have h₂ : runMirWithGap MirCallEnv.unresolved returnDestLinkedHelpers
          outerBadDestRefactoredBody 5 (callerArgs (true, x)) =
          .ok (.scalar ⟨wrapScalarBits (x * 2) (scalarModulus 4), 4⟩,
            (initMachineStateWithCallees outerBadDestBranchingBody []
              returnDestLinkedHelpers).memory) := rfl
      refine mirGapBehaviors_equiv_of_runs (fuel₂ := 5)
        (ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀)) ?_
      rw [h₁, h₂, Nat.mul_two]
      exact GapEqErr.refl (fun _ => rfl) (fun _ => rfl) _
    | false =>
      have h₁ : runMirWithGap MirCallEnv.unresolved returnDestLinkedHelpers
          outerBadDestBranchingBody 6 (callerArgs (false, x)) =
          .gap (.unsupported "test::mid_bad_dest_helper") := rfl
      have h₂ : runMirWithGap MirCallEnv.unresolved returnDestLinkedHelpers
          outerBadDestRefactoredBody 6 (callerArgs (false, x)) =
          .gap (.unsupported "test::mid_bad_dest_helper") := rfl
      refine mirGapBehaviors_equiv_of_runs (fuel₂ := 6)
        (ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀)) ?_
      rw [h₁, h₂]
      exact GapEqErr.refl (fun _ => rfl) (fun _ => rfl) _

/--
Direct trusted `MirLang` `ExactPass` and closed-world `MirNoUBTree ↔ Defined`
canary: `spinLoopBody` and `spinTwoBlockBody` satisfy full-domain
`ContextEquiv` across every `args : List Value`, inducing an unconditional
`ExactPass` directly on `mirLangTraceErasedSem` (`MirLang`).
-/
theorem spinLoop_mirLang_exactPass :
    ExactPass mirLangTraceErasedSem mirLangTraceErasedSem id id
        spinLoopBody spinTwoBlockBody ∧
      ∀ args : List Value,
        OutcomeSet.Defined ExecFault.isUB
            (mirGapBehaviors MirCallEnv.unresolved [] spinLoopBody args) ↔
          MirNoUBTree (mirCallTree spinLoopBody args) := by
  have hInitSpin : ∀ args : List Value,
      initMachineStateWithCallees spinLoopBody args [] =
        initMachineStateWithCallees spinLoopBody [] [] := by
    intro args; cases args <;> rfl
  have hInitTwo : ∀ args : List Value,
      initMachineStateWithCallees spinTwoBlockBody args [] =
        initMachineStateWithCallees spinTwoBlockBody [] [] := by
    intro args; cases args <;> rfl
  have hClosed : ∀ (args : List Value) (site : DefPath),
      ¬ mirGapBehaviors MirCallEnv.unresolved [] spinLoopBody args (.gap (.unresolved site)) := by
    intro args site ⟨hne, fuel, hrun⟩
    have hrun' : runMirWithGap MirCallEnv.unresolved [] spinLoopBody fuel args = .gap .outOfFuel := by
      unfold runMirWithGap
      rw [hInitSpin args]
      exact spinLoop_run_outOfFuel fuel
    exact hne (hrun.symm.trans hrun')
  have hEq : ContextEquiv (· = ·) (· = ·)
      (mirGapBehaviors MirCallEnv.unresolved [] spinLoopBody)
      (mirGapBehaviors MirCallEnv.unresolved [] spinTwoBlockBody) := by
    intro args
    unfold mirGapBehaviors
    rw [hInitSpin args, hInitTwo args]
    let s₁ : MirSiteState :=
      mirSiteOfExec spinLoopBody (.running (initMachineStateWithCallees spinLoopBody [] []))
    let init₂ := initMachineStateWithCallees spinTwoBlockBody [] []
    let s₂₀ : MirSiteState := mirSiteOfExec spinTwoBlockBody (.running init₂)
    let s₂₁ : MirSiteState :=
      mirSiteOfExec spinTwoBlockBody
        (.running { init₂ with frame := { init₂.frame with blockIdx := 1 } })
    let R : MirSiteState → MirSiteState → Prop :=
      fun a b => a = s₁ ∧ (b = s₂₀ ∨ b = s₂₁)
    refine mirGapBehaviors_equiv_of_stutter_with (R := R) (fun _ => rfl) ?_ ⟨rfl, Or.inl rfl⟩
    rintro a b ⟨rfl, rfl | rfl⟩
    · exact ⟨0, 0, s₁, s₂₀, .refl _, .refl _, StepNodeRelWith.tau ⟨rfl, Or.inr rfl⟩⟩
    · exact ⟨0, 0, s₁, s₂₁, .refl _, .refl _, StepNodeRelWith.tau ⟨rfl, Or.inl rfl⟩⟩
  exact ⟨mirContextEquiv_mirLang_exactPass hEq hClosed,
    fun args => mirGapBehaviors_defined_iff_mirNoUBTree (hClosed args)⟩

/--
Direct trusted `mirTree` `ExactPass` canary on gapping callers
(`callerBranchingBody → callerRefactoredBody`): using
`mirContextEquivOn_mirTree_exactPass` and `mirContextEquivOn_mirTree_toPartial_eq`,
the two trusted `mirTree`s form an `ExactPass` across BOTH the supported branch
(`flag = true`, defined returns) AND the unmodeled branch (`flag = false`, where
both `mirTree`s fail `MirNoUBTree` via `.unsupported "test::unmodeled_helper"`).
-/
theorem callerRefactored_mirTree_exactPass_with_gaps :
    let pre : List Value → Prop := fun args => ∃ q : Bool × Nat, args = callerArgs q
    ExactPass
        (fun b (q : { args : List Value // pre args }) =>
          mirTreeTraceErasedSem linkedHelpers b q.1)
        (fun b (q : { args : List Value // pre args }) =>
          mirTreeTraceErasedSem linkedHelpers b q.1)
        id id callerBranchingBody callerRefactoredBody ∧
      ¬ MirNoUBTree (mirTree callerBranchingBody
          (initMachineStateWithCallees callerBranchingBody (callerArgs (false, 7)) linkedHelpers)) ∧
      mirTreeTraceErasedSem linkedHelpers callerBranchingBody (callerArgs (false, 7)) =
        mirTreeTraceErasedSem linkedHelpers callerRefactoredBody (callerArgs (false, 7)) := by
  dsimp only
  let pre : List Value → Prop := fun args => ∃ q : Bool × Nat, args = callerArgs q
  have hEqOn : ContextEquivOn pre (· = ·) (· = ·)
      (mirGapBehaviors MirCallEnv.unresolved linkedHelpers callerBranchingBody)
      (mirGapBehaviors MirCallEnv.unresolved linkedHelpers callerRefactoredBody) := by
    rintro _ ⟨q, rfl⟩
    exact callerRefactored_contextEquiv q
  have hClosed : ∀ args, pre args → ∀ site,
      ¬ mirGapBehaviors MirCallEnv.unresolved linkedHelpers callerBranchingBody args
          (.gap (.unresolved site)) := by
    rintro _ ⟨⟨flag, x⟩, rfl⟩ site hm
    have heq : OutcomeWithGap.gap (GapTag.unresolved site) =
        callerRun callerBranchingBody 3 (flag, x) :=
      (mirGapBehaviors_iff_of_run
        (callerBranching_run_ne_outOfFuel (flag, x)) _).mp hm
    cases flag with
    | true => rw [callerBranching_run_true x] at heq; cases heq
    | false => rw [callerBranching_run_false x] at heq; cases heq
  exact ⟨mirContextEquivOn_mirTree_exactPass hEqOn hClosed,
    not_mirNoUBTree_of_run_undefined (callerBranching_run_false 7)
      (Or.inr (Or.inl ⟨"test::unmodeled_helper", rfl⟩)),
    mirContextEquivOn_mirTree_toPartial_eq hEqOn ⟨(false, 7), rfl⟩
      (hClosed _ ⟨(false, 7), rfl⟩)⟩

/-! ### Part 5G: Standalone Caller-Frame Preservation, Reachable-Request Env Linking, Kernel `VerificationResult` Transfer, Open-World `mirHandledTreeWithCallees` `ExactPass`, and Partition/Query-Scoped Transfer -/

/-- Standalone external MIR body: `fn ext_double(x: u32) -> u32 { x + x }`. -/
def extDoubleBody : CapturedMir :=
  mkMirBody "test::ext_double" 1
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy]
    [ { statements :=
          [mkStmt (.assign (locPlace 0)
            (.binaryOp .add (.copy (locPlace 1)) (.copy (locPlace 1))))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/--
Modeled-phase inline middle helper calling standalone `"test::ext_double"`:
`fn mid_ext_call(x: u32) -> u32 { let y = ext_double(x); y }`.
-/
def midExtCallHelperBody : CapturedMir :=
  mkMirBody "test::mid_ext_call" 1
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy, mkDecl .mut u32MirTy]
    [ { statements := [mkStmt (.storageLive 2)]
        terminator := mkTerm
          (.call (fnItemOp "test::ext_double") [.copy (locPlace 1)]
            (locPlace 2) (some 1) .continue_)
        isCleanup := false },
      { statements :=
          [mkStmt (.assign (locPlace 0) (.use (.copy (locPlace 2))))]
        terminator := mkTerm .return_
        isCleanup := false } ]

def outerMidBranchingBody : CapturedMir :=
  mkMirBody "test::outer_mid_branching" 2
    [mkDecl .mut u32MirTy, mkDecl .not boolMirTy, mkDecl .not u32MirTy]
    [ flagSwitchBlock,
      { statements :=
          [mkStmt (.assign (locPlace 0)
            (.binaryOp .add (.copy (locPlace 2)) (.copy (locPlace 2))))]
        terminator := mkTerm .return_
        isCleanup := false },
      helperCallBlock "test::mid_ext_call",
      returnBlock ]

def outerMidRefactoredBody : CapturedMir :=
  mkMirBody "test::outer_mid_refactored" 2
    [mkDecl .mut u32MirTy, mkDecl .not boolMirTy, mkDecl .not u32MirTy,
     mkDecl .mut u32MirTy]
    [ flagSwitchBlock,
      { statements :=
          [mkStmt (.storageLive 3),
           mkStmt (.assign (locPlace 3)
             (.binaryOp .mul (.copy (locPlace 2)) (u32ConstOp 2))),
           mkStmt (.assign (locPlace 0) (.use (.copy (locPlace 3))))]
        terminator := mkTerm .return_
        isCleanup := false },
      helperCallBlock "test::mid_ext_call",
      returnBlock ]

/-- Raw `MirCallEnv.ofMirOutcome` wrapping standalone `runMirWithGap` on `extDoubleBody`. -/
def buggyStandaloneEnv : MirCallEnv :=
  MirCallEnv.ofMirOutcome (fun req =>
    runMirWithGap MirCallEnv.unresolved [] extDoubleBody 3 req.args)

/-- Frame-preserving `MirCallEnv.ofStandaloneBody` wrapping standalone `extDoubleBody`. -/
def safeStandaloneEnv : MirCallEnv :=
  MirCallEnv.ofStandaloneBody [] 3
    (fun dp => if dp == "test::ext_double" then some extDoubleBody else none)

/--
Standalone caller-frame corruption vs. `MirCallEnv.ofStandaloneBody` canary:
1. Summarizing standalone `extDoubleBody` via raw `MirCallEnv.ofMirOutcome`
   wipes out `activeCallee = some midExtCallHelperBody` and `callStack` upon
   return, causing `outerMidBranchingBody` on `(false, 3)` to execute its own
   `bb1` (`_2 + _2`) against `midExtCallHelperBody`'s local `_2 = 6` (returning
   `12` instead of `6`!) while `outerMidRefactoredBody` hits spurious `.fault .ub`
   on out-of-bounds local `_3`, falsifying `PreservesCallFrame` and breaking
   `ContextEquiv`;
2. Summarizing the same `extDoubleBody` via `MirCallEnv.ofStandaloneBody`
   satisfies `PreservesCallFrame` (`callFramePreserved`), returns `6` on both
   callers, and preserves `ContextEquiv` (`r₁.1 = r₂.1`) across all `(flag, x)`.
-/
theorem ofMirOutcome_frame_corruption_vs_ofStandaloneBody :
    ¬ buggyStandaloneEnv.PreservesCallFrame ∧
      (runMirWithGap buggyStandaloneEnv [midExtCallHelperBody]
          outerMidBranchingBody 10 (callerArgs (false, 3))).map Prod.fst =
        .ok (.scalar ⟨12, 4⟩) ∧
      runMirWithGap buggyStandaloneEnv [midExtCallHelperBody]
          outerMidRefactoredBody 10 (callerArgs (false, 3)) = .fault .ub ∧
      ¬ ContextEquiv (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
        (fun q : Bool × Nat =>
          mirGapBehaviors buggyStandaloneEnv [midExtCallHelperBody]
            outerMidBranchingBody (callerArgs q))
        (fun q : Bool × Nat =>
          mirGapBehaviors buggyStandaloneEnv [midExtCallHelperBody]
            outerMidRefactoredBody (callerArgs q)) ∧
      safeStandaloneEnv.PreservesCallFrame ∧
      (runMirWithGap safeStandaloneEnv [midExtCallHelperBody]
          outerMidBranchingBody 10 (callerArgs (false, 3))).map Prod.fst =
        .ok (.scalar ⟨6, 4⟩) ∧
      (runMirWithGap safeStandaloneEnv [midExtCallHelperBody]
          outerMidRefactoredBody 10 (callerArgs (false, 3))).map Prod.fst =
        .ok (.scalar ⟨6, 4⟩) ∧
      ContextEquiv (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
        (fun q : Bool × Nat =>
          mirGapBehaviors safeStandaloneEnv [midExtCallHelperBody]
            outerMidBranchingBody (callerArgs q))
        (fun q : Bool × Nat =>
          mirGapBehaviors safeStandaloneEnv [midExtCallHelperBody]
            outerMidRefactoredBody (callerArgs q)) := by
  have hNoFrame : ¬ buggyStandaloneEnv.PreservesCallFrame := by
    intro h
    let memActive : Memory :=
      { (initMachineStateWithCallees outerMidBranchingBody (callerArgs (false, 3))
          [midExtCallHelperBody]).memory with
        activeCallee := some midExtCallHelperBody }
    let req : MirCallReq :=
      { defPath := "test::ext_double", typeArgs := [], args := [.scalar ⟨3, 4⟩],
        memory := memActive }
    have hok : buggyStandaloneEnv req =
        .ok (.returned (.scalar ⟨6, 4⟩)
          (initMachineStateWithCallees extDoubleBody [.scalar ⟨3, 4⟩] []).memory) := rfl
    have hpres := h req _ hok
    cases hpres.2.2.1
  have hBuggy₂ : runMirWithGap buggyStandaloneEnv [midExtCallHelperBody]
      outerMidRefactoredBody 10 (callerArgs (false, 3)) = .fault .ub := rfl
  have hNotCtx : ¬ ContextEquiv (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
      (fun q : Bool × Nat =>
        mirGapBehaviors buggyStandaloneEnv [midExtCallHelperBody]
          outerMidBranchingBody (callerArgs q))
      (fun q : Bool × Nat =>
        mirGapBehaviors buggyStandaloneEnv [midExtCallHelperBody]
          outerMidRefactoredBody (callerArgs q)) := by
    intro hEq
    have h₁ : runMirWithGap buggyStandaloneEnv [midExtCallHelperBody]
        outerMidBranchingBody 10 (callerArgs (false, 3)) =
        .ok (.scalar ⟨12, 4⟩,
          (initMachineStateWithCallees extDoubleBody [.scalar ⟨3, 4⟩] []).memory) := rfl
    have hrel := (mirGapBehaviors_equiv_iff_of_runs
      (ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀))
      (ne_outOfFuel_of_eq hBuggy₂ (fun h₀ => by cases h₀))).mp (hEq (false, 3))
    rw [h₁, hBuggy₂] at hrel
    exact False.elim hrel
  have hSafeCtx : ContextEquiv (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
      (fun q : Bool × Nat =>
        mirGapBehaviors safeStandaloneEnv [midExtCallHelperBody]
          outerMidBranchingBody (callerArgs q))
      (fun q : Bool × Nat =>
        mirGapBehaviors safeStandaloneEnv [midExtCallHelperBody]
          outerMidRefactoredBody (callerArgs q)) := by
    intro ⟨flag, x⟩
    cases flag with
    | true =>
      have h₁ : runMirWithGap safeStandaloneEnv [midExtCallHelperBody]
          outerMidBranchingBody 3 (callerArgs (true, x)) =
          .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩,
            (initMachineStateWithCallees outerMidBranchingBody []
              [midExtCallHelperBody]).memory) := rfl
      have h₂ : runMirWithGap safeStandaloneEnv [midExtCallHelperBody]
          outerMidRefactoredBody 5 (callerArgs (true, x)) =
          .ok (.scalar ⟨wrapScalarBits (x * 2) (scalarModulus 4), 4⟩,
            (initMachineStateWithCallees outerMidBranchingBody []
              [midExtCallHelperBody]).memory) := rfl
      refine mirGapBehaviors_equiv_of_runs (fuel₂ := 5)
        (ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀)) ?_
      rw [h₁, h₂, Nat.mul_two]
      exact (rfl : Value.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩ = _)
    | false =>
      have hm₁ : (runMirWithGap safeStandaloneEnv [midExtCallHelperBody]
          outerMidBranchingBody 10 (callerArgs (false, x))).map Prod.fst =
          .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩) := rfl
      have hm₂ : (runMirWithGap safeStandaloneEnv [midExtCallHelperBody]
          outerMidRefactoredBody 10 (callerArgs (false, x))).map Prod.fst =
          .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩) := rfl
      have hne₁ : runMirWithGap safeStandaloneEnv [midExtCallHelperBody]
          outerMidBranchingBody 10 (callerArgs (false, x)) ≠ .gap .outOfFuel := by
        intro h₀; rw [h₀] at hm₁; cases hm₁
      refine mirGapBehaviors_equiv_of_runs (fuel₂ := 10) hne₁ ?_
      cases ho₁ : runMirWithGap safeStandaloneEnv [midExtCallHelperBody]
          outerMidBranchingBody 10 (callerArgs (false, x)) with
      | ok r₁ =>
        cases ho₂ : runMirWithGap safeStandaloneEnv [midExtCallHelperBody]
            outerMidRefactoredBody 10 (callerArgs (false, x)) with
        | ok r₂ =>
          rw [ho₁] at hm₁; rw [ho₂] at hm₂
          exact (OutcomeWithGap.ok.inj hm₁).trans (OutcomeWithGap.ok.inj hm₂).symm
        | fault _ => rw [ho₂] at hm₂; cases hm₂
        | gap _ => rw [ho₂] at hm₂; cases hm₂
      | fault _ => rw [ho₁] at hm₁; cases hm₁
      | gap _ => rw [ho₁] at hm₁; cases hm₁
  exact ⟨hNoFrame, rfl, hBuggy₂, hNotCtx,
    MirCallEnv.ofStandaloneBody_preservesCallFrame [] 3 _, rfl, rfl, hSafeCtx⟩

/-- Partial callee table resolving only `"test::ext_helper"`. -/
def partialLinkEnv : MirCallEnv :=
  MirCallEnv.ofPure (fun dp args =>
    if dp == "test::ext_helper" then incHelperSummary dp args else .gap (.unresolved dp))

/-- Extended callee table adding a summary for `"test::unrelated_fn"`. -/
def extendedLinkEnv : MirCallEnv :=
  MirCallEnv.ofPure (fun dp args =>
    if dp == "test::ext_helper" then incHelperSummary dp args
    else if dp == "test::unrelated_fn" then .ok (.scalar ⟨99, 4⟩)
    else .gap (.unresolved dp))

/--
Reachable-request modular environment linking canary (`mirGapBehaviors_env_congr_of_requestsAllIn`):
1. Upgrading `"test::unrelated_fn"` from `.gap (.unresolved "test::unrelated_fn")` to
   `.ok 99` falsifies global `∀ req, GapEqErr ...`;
2. `mirRequestsAllIn` genuinely rejects a callee predicate that omits `"test::ext_helper"`
   (`mirRequestsAllIn ... (· == "test::unrelated_fn") = false`, non-vacuity); and
3. `mirGapBehaviors_env_congr_of_requestsAllIn` proves `OutcomeSetEquiv` on
   `seqCallerBody` across all `x : Nat` in one step (`rfl`) because only
   `"test::ext_helper"` is `MirCallReachable`.
-/
theorem incremental_env_linking_congr_on_reachable :
    (¬ ∀ req, GapEqErr (· = ·) (· = ·) (partialLinkEnv.seal req) (extendedLinkEnv.seal req)) ∧
      mirRequestsAllIn partialLinkEnv seqCallerBody (fun dp => dp == "test::unrelated_fn") 5
          (mirSiteOfExec seqCallerBody
            (.running (initMachineStateWithCallees seqCallerBody [.scalar ⟨0, 4⟩] []))) =
        false ∧
      ∀ x : Nat,
        OutcomeSetEquiv (GapEqErr (· = ·) (· = ·))
          (mirGapBehaviors partialLinkEnv [] seqCallerBody [.scalar ⟨x, 4⟩])
          (mirGapBehaviors extendedLinkEnv [] seqCallerBody [.scalar ⟨x, 4⟩]) := by
  refine ⟨?_, rfl, fun x =>
    mirGapBehaviors_env_congr_of_requestsAllIn (pred := fun dp => dp == "test::ext_helper")
      (fuel := 5) rfl (fun req hpred => ?_)⟩
  · intro hAll
    let unrReq : MirCallReq := { extHelperReq 0 with defPath := "test::unrelated_fn" }
    have hBad := hAll unrReq
    exact False.elim hBad
  · have hdp : req.defPath = "test::ext_helper" := eq_of_beq hpred
    dsimp only [partialLinkEnv, extendedLinkEnv, MirCallEnv.seal, MirCallEnv.ofPure]
    rw [hdp]
    exact GapEqErr.refl (fun _ => rfl) (fun _ => rfl) _

/--
Kernel `Trusted.VerificationResult` certificate transfer and open-world
`mirHandledTreeWithCallees` `ExactPass` canary:
1. Global `hClosed` fails on `tailCallerBody` (which calls unresolved
   `"test::ext_helper"` on `flag = false`), yet `VerificationResult.of_contextEquiv`
   transfers a kernel `Trusted.VerificationResult.VerificationResult` certificate
   on `flag = true ∧ x + x < 2^32` from `tailCallerBody` to `tailCallerRefactoredBody`;
2. `mirContextEquivOn_mirHandledTree_exactPass` establishes an open-world
   `ExactPass` on `mirHandledTraceErasedSem MirCallEnv.unresolved []` between
   `tailCallerBody` and `tailCallerRefactoredBody` across BOTH `flag = true` AND
   `flag = false` (where `MirCallEnv.unresolved` emits `.gap (.unresolved "test::ext_helper")`
   with ZERO `hClosed` assumption!); and
3. `mirContextEquivOn_mirHandledTree_exactPass` and
   `mirContextEquivOn_mirHandledTree_toPartial_eq` prove open-world `ExactPass`
   and `toPartial` equality on `mirHandledTraceErasedSem (MirCallEnv.ofPure f) []`
   for EVERY pure summary `f` (including gapping `unmodeledHelperSummary`).
-/
theorem tailCaller_verificationResult_and_openWorld_mirHandledTree :
    let pre : List Value → Prop :=
      fun args => ∃ x, x + x < 4294967296 ∧ args = callerArgs (true, x)
    let post : List Value → Value → Prop :=
      fun args ret => ∃ x, args = callerArgs (true, x) ∧ ret = .scalar ⟨x + x, 4⟩
    let qPre : List Value × Memory → Prop :=
      fun am => ∃ q' : Bool × Nat, am = (callerArgs q', unlinkedMemory)
    (∃ args site,
        mirGapBehaviors MirCallEnv.unresolved [] tailCallerBody args (.gap (.unresolved site))) ∧
      Nonempty (Trusted.VerificationResult.VerificationResult
        { body := tailCallerRefactoredBody, pre := pre, post := post, callees := [] }) ∧
      ExactPass
        (fun b (q : { am : List Value × Memory // qPre am }) =>
          mirHandledTraceErasedSem MirCallEnv.unresolved [] b q.1)
        (fun b (q : { am : List Value × Memory // qPre am }) =>
          mirHandledTraceErasedSem MirCallEnv.unresolved [] b q.1)
        id id tailCallerBody tailCallerRefactoredBody ∧
      ∀ (f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value),
        ExactPass
          (fun b (q : { am : List Value × Memory // qPre am }) =>
            mirHandledTraceErasedSem (MirCallEnv.ofPure f) [] b q.1)
          (fun b (q : { am : List Value × Memory // qPre am }) =>
            mirHandledTraceErasedSem (MirCallEnv.ofPure f) [] b q.1)
          id id tailCallerBody tailCallerRefactoredBody ∧
        ∀ (q : Bool × Nat),
          mirHandledTraceErasedSem (MirCallEnv.ofPure f) [] tailCallerBody
              (callerArgs q, unlinkedMemory) =
            mirHandledTraceErasedSem (MirCallEnv.ofPure f) [] tailCallerRefactoredBody
              (callerArgs q, unlinkedMemory) := by
  dsimp only
  let pre : List Value → Prop :=
    fun args => ∃ x, x + x < 4294967296 ∧ args = callerArgs (true, x)
  let post : List Value → Value → Prop :=
    fun args ret => ∃ x, args = callerArgs (true, x) ∧ ret = .scalar ⟨x + x, 4⟩
  let qPre : List Value × Memory → Prop :=
    fun am => ∃ q' : Bool × Nat, am = (callerArgs q', unlinkedMemory)
  have hOpen : ∃ args site,
      mirGapBehaviors MirCallEnv.unresolved [] tailCallerBody args (.gap (.unresolved site)) := by
    have hrun := (tailCaller_run_false_unresolved 0).1
    exact ⟨callerArgs (false, 0), "test::ext_helper",
      (mirGapBehaviors_iff_of_run
        (ne_outOfFuel_of_eq hrun (fun h₀ => by cases h₀)) _).mpr hrun.symm⟩
  have vBase : Trusted.VerificationResult.VerificationResult
      { body := tailCallerBody, pre := pre, post := post, callees := [] } :=
    { proof := by
        rintro _ ⟨x, hx, rfl⟩
        have hrun : runMirWithGap MirCallEnv.unresolved [] tailCallerBody 3
            (callerArgs (true, x)) =
            classifyOutcome (.normal (.scalar ⟨x + x, 4⟩, unlinkedMemory)) := by
          change runMirWithGap MirCallEnv.unresolved [] tailCallerBody 3
              (callerArgs (true, x)) =
            .ok (.scalar ⟨x + x, 4⟩, unlinkedMemory)
          have h₀ : runMirWithGap MirCallEnv.unresolved [] tailCallerBody 3
              (callerArgs (true, x)) =
              .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, unlinkedMemory) := rfl
          rw [h₀, wrapScalarBits_of_lt (show x + x < scalarModulus 4 from hx)]
        obtain ⟨hsafe, _, huniq⟩ := mirTree_adequate_of_defined hrun
        refine ⟨hsafe, fun outPair hrr _ retVal mem' hout => ?_⟩
        rcases outPair with ⟨tr, out⟩
        dsimp only at hout
        subst hout
        have heq := huniq tr (.normal (retVal, mem')) hrr
        injection heq with hpair
        injection hpair with hret _
        exact ⟨x, rfl, hret⟩ }
  have hTailEqOn : ContextEquivOn pre (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
      (mirGapBehaviors MirCallEnv.unresolved [] tailCallerBody)
      (mirGapBehaviors MirCallEnv.unresolved [] tailCallerRefactoredBody) := by
    rintro _ ⟨x, _, rfl⟩
    have h₁ : runMirWithGap MirCallEnv.unresolved [] tailCallerBody 3
        (callerArgs (true, x)) =
        .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, unlinkedMemory) := rfl
    have h₂ : runMirWithGap MirCallEnv.unresolved [] tailCallerRefactoredBody 5
        (callerArgs (true, x)) =
        .ok (.scalar ⟨wrapScalarBits (x * 2) (scalarModulus 4), 4⟩, unlinkedMemory) := rfl
    refine mirGapBehaviors_equiv_of_runs (fuel₂ := 5)
      (ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀)) ?_
    rw [h₁, h₂, Nat.mul_two]
    exact (rfl : Value.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩ = _)
  have hTailClosedOn : ∀ args, pre args → ∀ site,
      ¬ mirGapBehaviors MirCallEnv.unresolved [] tailCallerBody args (.gap (.unresolved site)) := by
    rintro _ ⟨x, _, rfl⟩ site hm
    have h₁ : runMirWithGap MirCallEnv.unresolved [] tailCallerBody 3
        (callerArgs (true, x)) =
        .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, unlinkedMemory) := rfl
    have heq := (mirGapBehaviors_iff_of_run
      (ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀)) _).mp hm
    rw [h₁] at heq
    cases heq
  have vRefactored := VerificationResult.of_contextEquiv hTailEqOn hTailClosedOn vBase
  have hUnresStateful : ContextEquivOn qPre (· = ·) (· = ·)
      (mirStatefulGapBehaviors MirCallEnv.unresolved [] tailCallerBody)
      (mirStatefulGapBehaviors MirCallEnv.unresolved [] tailCallerRefactoredBody) := by
    rintro _ ⟨q', rfl⟩
    exact tailCallerRefactored_contextEquiv_any_env MirCallEnv.unresolved
      (fun x _ _ he => by cases he) (fun x _ he => by cases he) q'
  refine ⟨hOpen, ⟨vRefactored⟩, mirContextEquivOn_mirHandledTree_exactPass hUnresStateful,
    fun f => ?_⟩
  have hTailStateful : ContextEquivOn qPre (· = ·) (· = ·)
      (mirStatefulGapBehaviors (MirCallEnv.ofPure f) [] tailCallerBody)
      (mirStatefulGapBehaviors (MirCallEnv.ofPure f) [] tailCallerRefactoredBody) := by
    rintro _ ⟨q', rfl⟩
    exact tailCallerRefactored_contextEquiv_any_env (MirCallEnv.ofPure f)
      (fun x v mem he => MirCallEnv.ofPure_preservesCallStack f (extHelperReq x) _ he)
      (fun x mem he => MirCallEnv.ofPure_preservesCallStack f (extHelperReq x) _ he) q'
  exact ⟨mirContextEquivOn_mirHandledTree_exactPass hTailStateful,
    fun q => mirContextEquivOn_mirHandledTree_toPartial_eq hTailStateful ⟨q, rfl⟩⟩

/--
Query-scoped specification transfer (`ContextEquivOn.valTransfer_spec` and
`ContextEquivOn.outcomeTransfer_spec`), constructive Boolean partition patching
(`ContextEquiv.of_boolPartition`), and injective gap reflection
(`ContextEquiv.mapGap_iff_of_injective`) canary.
-/
theorem queryScoped_transfer_boolPartition_and_mapGap :
    let valSpec : (valLanguage callerGapSem).Behavior :=
      Language.ContractSpec (valLanguage callerGapSem)
        (fun q => q.1 = true)
        (fun _ => True)
        (fun q r => r.1 = Value.scalar ⟨q.2, 4⟩)
    let outSpec : (outcomeLanguage callerGapSem).Behavior :=
      Language.ContractSpec (outcomeLanguage callerGapSem)
        (fun q => q.1 = true)
        (fun _ => True)
        (fun q out => out = .normal (Value.scalar ⟨q.2, 4⟩, linkedMemory))
    ¬ ContextEquiv (· = ·) (· = ·) (callerGapSem returnArgBody) (callerGapSem assumeFlagBody) ∧
      ((valLanguage callerGapSem).sem assumeFlagBody ≤ valSpec) ∧
      ((outcomeLanguage callerGapSem).sem assumeFlagBody ≤ outSpec) ∧
      ContextEquiv (· = ·) (· = ·)
        (callerGapSem callerBranchingBody) (callerGapSem callerRefactoredBody) ∧
      (ContextEquiv (· = ·) (· = ·)
          (fun q => OutcomeSet.mapGap (Sum.inl (β := Nat)) (callerGapSem callerBranchingBody q))
          (fun q => OutcomeSet.mapGap (Sum.inl (β := Nat)) (callerGapSem callerRefactoredBody q)) ↔
        ContextEquiv (· = ·) (· = ·)
          (callerGapSem callerBranchingBody) (callerGapSem callerRefactoredBody)) := by
  dsimp only
  have hNotGlobal : ¬ ContextEquiv (· = ·) (· = ·)
      (callerGapSem returnArgBody) (callerGapSem assumeFlagBody) := by
    intro h
    have h₁ : runMirWithGap MirCallEnv.unresolved linkedHelpers
        returnArgBody 3 (callerArgs (false, 0)) = .ok (.scalar ⟨0, 4⟩, linkedMemory) := rfl
    have h₂ : runMirWithGap MirCallEnv.unresolved linkedHelpers
        assumeFlagBody 3 (callerArgs (false, 0)) = .fault .ub := rfl
    have hEq := (mirGapBehaviors_equiv_iff_of_runs
      (ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀))
      (ne_outOfFuel_of_eq h₂ (fun h₀ => by cases h₀))).mp (h (false, 0))
    rw [h₁, h₂] at hEq
    exact False.elim hEq
  have hOnTrue : ContextEquivOn (fun q : Bool × Nat => q.1 = true) (· = ·) (· = ·)
      (callerGapSem returnArgBody) (callerGapSem assumeFlagBody) := by
    rintro ⟨flag, x⟩ hflag
    dsimp only at hflag
    subst hflag
    have h₁ : runMirWithGap MirCallEnv.unresolved linkedHelpers
        returnArgBody 3 (callerArgs (true, x)) =
        .ok (.scalar ⟨x, 4⟩, linkedMemory) := rfl
    have h₂ : runMirWithGap MirCallEnv.unresolved linkedHelpers
        assumeFlagBody 3 (callerArgs (true, x)) =
        .ok (.scalar ⟨x, 4⟩, linkedMemory) := rfl
    refine mirGapBehaviors_equiv_of_runs (fuel₂ := 3)
      (ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀)) ?_
    rw [h₁, h₂]
    exact GapEqErr.refl (fun _ => rfl) (fun _ => rfl) _
  have hValTrans : (valLanguage callerGapSem).sem assumeFlagBody ≤
      Language.ContractSpec (valLanguage callerGapSem)
        (fun q => q.1 = true) (fun _ => True) (fun q r => r.1 = Value.scalar ⟨q.2, 4⟩) := by
    refine ContextEquivOn.valTransfer_spec hOnTrue (fun _ hq => hq) ?_
    rintro ⟨flag, x⟩ (rfl : flag = true)
    have h₁ : runMirWithGap MirCallEnv.unresolved linkedHelpers
        returnArgBody 3 (callerArgs (true, x)) = .ok (.scalar ⟨x, 4⟩, linkedMemory) := rfl
    have hne : runMirWithGap MirCallEnv.unresolved linkedHelpers
        returnArgBody 3 (callerArgs (true, x)) ≠ .gap .outOfFuel :=
      ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀)
    refine ⟨fun o ho => ?_, fun r hr _ => ?_⟩
    · rw [(mirGapBehaviors_iff_of_run hne o).mp ho, h₁]
      exact ⟨_, rfl⟩
    · have heq := (mirGapBehaviors_iff_of_run hne (.ok r)).mp hr
      rw [h₁] at heq
      cases OutcomeWithGap.ok.inj heq
      rfl
  have hOutTrans : (outcomeLanguage callerGapSem).sem assumeFlagBody ≤
      Language.ContractSpec (outcomeLanguage callerGapSem)
        (fun q => q.1 = true) (fun _ => True)
        (fun q out => out = .normal (Value.scalar ⟨q.2, 4⟩, linkedMemory)) := by
    refine ContextEquivOn.outcomeTransfer_spec hOnTrue (fun _ hq => hq) ?_
    rintro ⟨flag, x⟩ (rfl : flag = true)
    have h₁ : runMirWithGap MirCallEnv.unresolved linkedHelpers
        returnArgBody 3 (callerArgs (true, x)) = .ok (.scalar ⟨x, 4⟩, linkedMemory) := rfl
    have hne : runMirWithGap MirCallEnv.unresolved linkedHelpers
        returnArgBody 3 (callerArgs (true, x)) ≠ .gap .outOfFuel :=
      ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀)
    have hDef : OutcomeSet.Defined ExecFault.isUB (callerGapSem returnArgBody (true, x)) :=
      defined_mirGapBehaviors_of_run (fuel := 3) (by rw [h₁]; exact trivial)
    refine ⟨hDef, fun out hout _ => ?_⟩
    have heq := (mirGapBehaviors_iff_of_run hne (classifyOutcome out)).mp hout
    rw [h₁] at heq
    cases out with
    | normal r => cases OutcomeWithGap.ok.inj heq; rfl
    | panic => cases heq
    | abort => cases heq
  have hPart : ContextEquiv (· = ·) (· = ·)
      (callerGapSem callerBranchingBody) (callerGapSem callerRefactoredBody) :=
    ContextEquiv.of_boolPartition Prod.fst callerRefactored_programEquivOn
      (fun q _ => callerRefactored_contextEquiv q)
  exact ⟨hNotGlobal, hValTrans, hOutTrans, hPart,
    ContextEquiv.mapGap_iff_of_injective (fun _ _ h => Sum.inl.inj h)⟩

/-! ### Part 5H: Standalone Caller-Memory Borrow Preservation, Kernel `StatefulVerificationResult`, and Relational `ModularVerificationResult` Transfer -/

/--
Caller holding a live shared borrow `&x` across a call to standalone `"test::ext_double"`:
`fn borrow_across_ext_call(x: u32) -> u32 { let r = &x; let y = ext_double(x); *r + y }`.
-/
def borrowAcrossExtCallBody : CapturedMir :=
  mkMirBody "test::borrow_across_ext_call" 1
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy, mkDecl .mut u32MirTy,
     mkDecl .mut u32SharedRefMirTy, mkDecl .mut u32MirTy]
    [ { statements :=
          [mkStmt (.storageLive 2),
           mkStmt (.storageLive 3),
           mkStmt (.assign (locPlace 3) (.ref .shared (locPlace 1)))]
        terminator := mkTerm
          (.call (fnItemOp "test::ext_double") [.copy (locPlace 1)]
            (locPlace 2) (some 1) .continue_)
        isCleanup := false },
      { statements :=
          [mkStmt (.storageLive 4),
           mkStmt (.assign (locPlace 4)
             (.use (.copy { local_ := 3, projection := [.deref] }))),
           mkStmt (.assign (locPlace 0)
             (.binaryOp .add (.copy (locPlace 4)) (.copy (locPlace 2))))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/--
Equivalent caller taking `&x` after calling `"test::ext_double"`:
`fn borrow_after_ext_call(x: u32) -> u32 { let y = ext_double(x); let r = &x; *r + y }`.
-/
def borrowAfterExtCallBody : CapturedMir :=
  mkMirBody "test::borrow_after_ext_call" 1
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy, mkDecl .mut u32MirTy,
     mkDecl .mut u32SharedRefMirTy, mkDecl .mut u32MirTy]
    [ { statements := [mkStmt (.storageLive 2)]
        terminator := mkTerm
          (.call (fnItemOp "test::ext_double") [.copy (locPlace 1)]
            (locPlace 2) (some 1) .continue_)
        isCleanup := false },
      { statements :=
          [mkStmt (.storageLive 3),
           mkStmt (.assign (locPlace 3) (.ref .shared (locPlace 1))),
           mkStmt (.storageLive 4),
           mkStmt (.assign (locPlace 4)
             (.use (.copy { local_ := 3, projection := [.deref] }))),
           mkStmt (.assign (locPlace 0)
             (.binaryOp .add (.copy (locPlace 4)) (.copy (locPlace 2))))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/--
Unsound misuse of `MirCallEnv.ofStatefulOutcome` (`Memory.restoreCallerFrame`)
on a standalone `runMirWithGap` summary: restores call-frame metadata while
wiping out caller `borrows`, `globals`, `callerLocals`, and fresh counters.
-/
def buggyRestoreFrameEnv : MirCallEnv :=
  MirCallEnv.ofStatefulOutcome (fun req =>
    if req.defPath == "test::ext_double" then
      runMirWithGap MirCallEnv.unresolved [] extDoubleBody 3 req.args
    else
      .gap (.unresolved req.defPath))

/--
Standalone caller-borrow preservation canary (`ofStatefulOutcome` vs `ofStandaloneBody`):
1. `buggyRestoreFrameEnv` satisfies `PreservesCallFrame`, YET because
   `Memory.restoreCallerFrame` discards caller `borrows`, `borrowAcrossExtCallBody`
   crashes with spurious `.fault .ub` when dereferencing `*r` after `ext_double(3)`
   while `borrowAfterExtCallBody` returns `9`, breaking `ContextEquiv`; and
2. `safeStandaloneEnv` (`MirCallEnv.ofStandaloneBody`, using `Memory.preserveCallerMemory`)
   preserves caller `borrows` and counters alongside the call frame, so BOTH bodies
   return `9` on `x = 3` and satisfy `ContextEquiv (fun r₁ r₂ => r₁.1 = r₂.1) (· = ·)`
   across all `x : Nat`!
-/
theorem ofStatefulOutcome_borrow_wipe_vs_ofStandaloneBody :
    buggyRestoreFrameEnv.PreservesCallFrame ∧
      runMirWithGap buggyRestoreFrameEnv [] borrowAcrossExtCallBody 10 [.scalar ⟨3, 4⟩] =
        .fault .ub ∧
      (runMirWithGap buggyRestoreFrameEnv [] borrowAfterExtCallBody 10 [.scalar ⟨3, 4⟩]).map Prod.fst =
        .ok (.scalar ⟨9, 4⟩) ∧
      ¬ ContextEquiv (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
        (fun x : Nat =>
          mirGapBehaviors buggyRestoreFrameEnv [] borrowAcrossExtCallBody [.scalar ⟨x, 4⟩])
        (fun x : Nat =>
          mirGapBehaviors buggyRestoreFrameEnv [] borrowAfterExtCallBody [.scalar ⟨x, 4⟩]) ∧
      (runMirWithGap safeStandaloneEnv [] borrowAcrossExtCallBody 10 [.scalar ⟨3, 4⟩]).map Prod.fst =
        .ok (.scalar ⟨9, 4⟩) ∧
      (runMirWithGap safeStandaloneEnv [] borrowAfterExtCallBody 10 [.scalar ⟨3, 4⟩]).map Prod.fst =
        .ok (.scalar ⟨9, 4⟩) ∧
      ContextEquiv (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
        (fun x : Nat =>
          mirGapBehaviors safeStandaloneEnv [] borrowAcrossExtCallBody [.scalar ⟨x, 4⟩])
        (fun x : Nat =>
          mirGapBehaviors safeStandaloneEnv [] borrowAfterExtCallBody [.scalar ⟨x, 4⟩]) := by
  have hBuggyAcross :
      runMirWithGap buggyRestoreFrameEnv [] borrowAcrossExtCallBody 10 [.scalar ⟨3, 4⟩] =
        .fault .ub := rfl
  have hBuggyAfter :
      (runMirWithGap buggyRestoreFrameEnv [] borrowAfterExtCallBody 10 [.scalar ⟨3, 4⟩]).map Prod.fst =
        .ok (.scalar ⟨9, 4⟩) := rfl
  have hNotCtx : ¬ ContextEquiv (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
      (fun x : Nat =>
        mirGapBehaviors buggyRestoreFrameEnv [] borrowAcrossExtCallBody [.scalar ⟨x, 4⟩])
      (fun x : Nat =>
        mirGapBehaviors buggyRestoreFrameEnv [] borrowAfterExtCallBody [.scalar ⟨x, 4⟩]) := by
    intro hEq
    have hne₂ : runMirWithGap buggyRestoreFrameEnv [] borrowAfterExtCallBody 10 [.scalar ⟨3, 4⟩] ≠
        .gap .outOfFuel := by
      intro h₀; rw [h₀] at hBuggyAfter; cases hBuggyAfter
    have hrel := (mirGapBehaviors_equiv_iff_of_runs
      (ne_outOfFuel_of_eq hBuggyAcross (fun h₀ => by cases h₀)) hne₂).mp (hEq 3)
    rw [hBuggyAcross] at hrel
    cases ho₂ : runMirWithGap buggyRestoreFrameEnv [] borrowAfterExtCallBody 10 [.scalar ⟨3, 4⟩] with
    | ok _ => rw [ho₂] at hrel; exact False.elim hrel
    | fault _ => rw [ho₂] at hBuggyAfter; cases hBuggyAfter
    | gap _ => rw [ho₂] at hBuggyAfter; cases hBuggyAfter
  have hSafeCtx : ContextEquiv (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
      (fun x : Nat =>
        mirGapBehaviors safeStandaloneEnv [] borrowAcrossExtCallBody [.scalar ⟨x, 4⟩])
      (fun x : Nat =>
        mirGapBehaviors safeStandaloneEnv [] borrowAfterExtCallBody [.scalar ⟨x, 4⟩]) := by
    intro x
    have hm₁ : (runMirWithGap safeStandaloneEnv [] borrowAcrossExtCallBody 10
        [.scalar ⟨x, 4⟩]).map Prod.fst =
        .ok (.scalar ⟨wrapScalarBits
          (x + wrapScalarBits (x + x) (scalarModulus 4)) (scalarModulus 4), 4⟩) := rfl
    have hm₂ : (runMirWithGap safeStandaloneEnv [] borrowAfterExtCallBody 10
        [.scalar ⟨x, 4⟩]).map Prod.fst =
        .ok (.scalar ⟨wrapScalarBits
          (x + wrapScalarBits (x + x) (scalarModulus 4)) (scalarModulus 4), 4⟩) := rfl
    have hne₁ : runMirWithGap safeStandaloneEnv [] borrowAcrossExtCallBody 10 [.scalar ⟨x, 4⟩] ≠
        .gap .outOfFuel := by
      intro h₀; rw [h₀] at hm₁; cases hm₁
    refine mirGapBehaviors_equiv_of_runs (fuel₂ := 10) hne₁ ?_
    cases ho₁ : runMirWithGap safeStandaloneEnv [] borrowAcrossExtCallBody 10 [.scalar ⟨x, 4⟩] with
    | ok r₁ =>
      cases ho₂ : runMirWithGap safeStandaloneEnv [] borrowAfterExtCallBody 10 [.scalar ⟨x, 4⟩] with
      | ok r₂ =>
        rw [ho₁] at hm₁; rw [ho₂] at hm₂
        exact (OutcomeWithGap.ok.inj hm₁).trans (OutcomeWithGap.ok.inj hm₂).symm
      | fault _ => rw [ho₂] at hm₂; cases hm₂
      | gap _ => rw [ho₂] at hm₂; cases hm₂
    | fault _ => rw [ho₁] at hm₁; cases hm₁
    | gap _ => rw [ho₁] at hm₁; cases hm₁
  exact ⟨MirCallEnv.ofStatefulOutcome_preservesCallFrame _,
    hBuggyAcross, hBuggyAfter, hNotCtx, rfl, rfl, hSafeCtx⟩

/--
Refactored branching caller taking a temporary local borrow `&_2` on the `true`
branch (so its post-return `Memory` differs from `callerBranchingBody` in
`borrows`/`nextTag`), while sharing `"test::unmodeled_helper"` on `false`.
-/
def callerBorrowRefactoredBody : CapturedMir :=
  mkMirBody "test::caller_borrow_refactored" 2
    [mkDecl .mut u32MirTy, mkDecl .not boolMirTy, mkDecl .not u32MirTy,
     mkDecl .mut u32SharedRefMirTy]
    [ flagSwitchBlock,
      { statements :=
          [mkStmt (.storageLive 3),
           mkStmt (.assign (locPlace 3) (.ref .shared (locPlace 2))),
           mkStmt (.assign (locPlace 0)
             (.binaryOp .mul (.copy (locPlace 2)) (u32ConstOp 2)))]
        terminator := mkTerm .return_
        isCleanup := false },
      helperCallBlock "test::unmodeled_helper",
      returnBlock ]

/--
Relational kernel `StatefulVerificationResult.of_contextEquiv` and open-world
`ModularVerificationResult.of_contextEquiv` transfer canary:
1. `callerBranchingBody` and `callerBorrowRefactoredBody` produce strictly
   distinct post-return memories (`r₁.2 ≠ r₂.2`, breaking exact `(· = ·)` on
   `MirReturn`) and hit `.gap (.unsupported "test::unmodeled_helper")` on
   `flag = false`, yet `StatefulVerificationResult.of_contextEquiv` with
   `rVal := fun r₁ r₂ => r₁.1 = r₂.1` transfers a kernel
   `Trusted.VerificationResult.StatefulVerificationResult` on `flag = true`; and
2. `seqCallerBody` and `borrowBeforeCallBody` produce strictly distinct external
   call requests AND post-return memories, yet `ModularVerificationResult.of_contextEquiv`
   transfers a kernel `Trusted.VerificationResult.ModularVerificationResult` across
   the whole family of `incHelperSummary`-compatible external call handlers with
   ZERO `hClosed` assumption!
-/
theorem stateful_and_modular_verificationResult_relational_transfer :
    let stPre : List Value → Memory → Prop :=
      fun args mem => ∃ x, x + x < 4294967296 ∧ args = callerArgs (true, x) ∧ mem = linkedMemory
    let stPost : List Value → Memory → Value → Memory → Prop :=
      fun args _ ret _ => ∃ x, args = callerArgs (true, x) ∧ ret = .scalar ⟨x + x, 4⟩
    let modPre : List Value → Memory → Prop :=
      fun args mem =>
        ∃ x, (x + 1) + (x + 1) < 4294967296 ∧ args = [.scalar ⟨x, 4⟩] ∧ mem = unlinkedMemory
    let modPost : List Value → Memory → Value → Memory → Prop :=
      fun args _ ret _ =>
        ∃ x, args = [.scalar ⟨x, 4⟩] ∧ ret = .scalar ⟨(x + 1) + (x + 1), 4⟩
    let envAssumed : Trusted.VerificationResult.ExternalCallHandler → Prop :=
      fun h => ∃ f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value,
        (∀ x, f "test::ext_helper" [.scalar ⟨x, 4⟩] =
          .ok (.scalar ⟨wrapScalarBits (x + 1) (scalarModulus 4), 4⟩)) ∧
        h = (MirCallEnv.ofPure f).toExternalCallHandler
    (¬ ContextEquivOn (fun q => stPre q.1 q.2) (· = ·) (· = ·)
        (mirStatefulGapBehaviors MirCallEnv.unresolved linkedHelpers callerBranchingBody)
        (mirStatefulGapBehaviors MirCallEnv.unresolved linkedHelpers callerBorrowRefactoredBody)) ∧
      Nonempty (Trusted.VerificationResult.StatefulVerificationResult
        { body := callerBorrowRefactoredBody, pre := stPre, post := stPost,
          callees := linkedHelpers }) ∧
      (¬ ContextEquivOn (fun q => modPre q.1 q.2) (· = ·) (· = ·)
        (mirStatefulGapBehaviors (MirCallEnv.ofPure incHelperSummary) [] seqCallerBody)
        (mirStatefulGapBehaviors (MirCallEnv.ofPure incHelperSummary) [] borrowBeforeCallBody)) ∧
      Nonempty (Trusted.VerificationResult.ModularVerificationResult
        { body := borrowBeforeCallBody, envAssumed := envAssumed,
          pre := modPre, post := modPost, callees := [] }) := by
  dsimp only
  let stPre : List Value → Memory → Prop :=
    fun args mem => ∃ x, x + x < 4294967296 ∧ args = callerArgs (true, x) ∧ mem = linkedMemory
  let stPost : List Value → Memory → Value → Memory → Prop :=
    fun args _ ret _ => ∃ x, args = callerArgs (true, x) ∧ ret = .scalar ⟨x + x, 4⟩
  let modPre : List Value → Memory → Prop :=
    fun args mem =>
      ∃ x, (x + 1) + (x + 1) < 4294967296 ∧ args = [.scalar ⟨x, 4⟩] ∧ mem = unlinkedMemory
  let modPost : List Value → Memory → Value → Memory → Prop :=
    fun args _ ret _ =>
      ∃ x, args = [.scalar ⟨x, 4⟩] ∧ ret = .scalar ⟨(x + 1) + (x + 1), 4⟩
  let envAssumed : Trusted.VerificationResult.ExternalCallHandler → Prop :=
    fun h => ∃ f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value,
      (∀ x, f "test::ext_helper" [.scalar ⟨x, 4⟩] =
        .ok (.scalar ⟨wrapScalarBits (x + 1) (scalarModulus 4), 4⟩)) ∧
      h = (MirCallEnv.ofPure f).toExternalCallHandler
  -- 1. Strict memory inequality on `callerBranchingBody` vs `callerBorrowRefactoredBody`
  have hStNotExact : ¬ ContextEquivOn (fun q => stPre q.1 q.2) (· = ·) (· = ·)
      (mirStatefulGapBehaviors MirCallEnv.unresolved linkedHelpers callerBranchingBody)
      (mirStatefulGapBehaviors MirCallEnv.unresolved linkedHelpers callerBorrowRefactoredBody) := by
    intro hEq
    have h₁ : runMirStepsWithGap MirCallEnv.unresolved callerBranchingBody 3
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          callerBranchingBody (callerArgs (true, 3)) linkedMemory linkedHelpers)) =
        .ok (.scalar ⟨6, 4⟩, linkedMemory) := rfl
    have h₂ : (runMirStepsWithGap MirCallEnv.unresolved callerBorrowRefactoredBody 5
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          callerBorrowRefactoredBody (callerArgs (true, 3)) linkedMemory linkedHelpers))).map
          (fun r => r.2.borrows.length) = .ok 1 := rfl
    have hne₁ : runMirStepsWithGap MirCallEnv.unresolved callerBranchingBody 3
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          callerBranchingBody (callerArgs (true, 3)) linkedMemory linkedHelpers)) ≠
        .gap .outOfFuel := ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀)
    have hmem₁ : mirStatefulGapBehaviors MirCallEnv.unresolved linkedHelpers callerBranchingBody
        (callerArgs (true, 3), linkedMemory) (.ok (.scalar ⟨6, 4⟩, linkedMemory)) :=
      ⟨(fun h₀ => by cases h₀), ⟨3, h₁⟩⟩
    obtain ⟨o₂, hm₂, hrel⟩ :=
      (hEq (callerArgs (true, 3), linkedMemory) ⟨3, by decide, rfl, rfl⟩).forward hmem₁
    have ho₂Eq : o₂ = .ok (.scalar ⟨6, 4⟩, linkedMemory) := (GapEqErr.eq_iff.mp hrel).symm
    subst ho₂Eq
    have hne₂' : runMirStepsWithGap MirCallEnv.unresolved callerBorrowRefactoredBody 5
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          callerBorrowRefactoredBody (callerArgs (true, 3)) linkedMemory linkedHelpers)) ≠
        .gap .outOfFuel := by
      intro h₀; rw [h₀] at h₂; cases h₂
    have hsame : OutcomeWithGap.ok (.scalar ⟨6, 4⟩, linkedMemory) =
        runMirStepsWithGap MirCallEnv.unresolved callerBorrowRefactoredBody 5
          (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            callerBorrowRefactoredBody (callerArgs (true, 3)) linkedMemory linkedHelpers)) :=
      (gapBehaviors_iff_of_run _ hne₂' _).mp hm₂
    rw [← hsame] at h₂
    cases OutcomeWithGap.ok.inj h₂
  -- 2. Base `StatefulVerificationResult` on `callerBranchingBody` + relational transfer
  have stBase : Trusted.VerificationResult.StatefulVerificationResult
      { body := callerBranchingBody, pre := stPre, post := stPost, callees := linkedHelpers } :=
    { proof := by
        rintro _ _ ⟨x, hx, rfl, rfl⟩
        have hrun : runMirWithGap MirCallEnv.unresolved linkedHelpers callerBranchingBody 3
            (callerArgs (true, x)) =
            classifyOutcome (.normal (.scalar ⟨x + x, 4⟩, linkedMemory)) := by
          change runMirWithGap MirCallEnv.unresolved linkedHelpers callerBranchingBody 3
              (callerArgs (true, x)) =
            .ok (.scalar ⟨x + x, 4⟩, linkedMemory)
          have h₀ : runMirWithGap MirCallEnv.unresolved linkedHelpers callerBranchingBody 3
              (callerArgs (true, x)) =
              .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, linkedMemory) :=
            callerBranching_run_true x
          rw [h₀, wrapScalarBits_of_lt (show x + x < scalarModulus 4 from hx)]
        obtain ⟨hsafe, _, huniq⟩ := mirTree_adequate_of_defined hrun
        refine ⟨hsafe, fun outPair hrr _ retVal mem' hout => ?_⟩
        rcases outPair with ⟨tr, out⟩
        dsimp only at hout
        subst hout
        have heq := huniq tr (.normal (retVal, mem')) hrr
        injection heq with hpair
        injection hpair with hret _
        exact ⟨x, rfl, hret⟩ }
  have hStEqOn : ContextEquivOn (fun q => stPre q.1 q.2) (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1)
      (· = ·)
      (mirStatefulGapBehaviors MirCallEnv.unresolved linkedHelpers callerBranchingBody)
      (mirStatefulGapBehaviors MirCallEnv.unresolved linkedHelpers callerBorrowRefactoredBody) := by
    rintro ⟨_, _⟩ ⟨x, _, rfl, rfl⟩
    have h₁ : runMirStepsWithGap MirCallEnv.unresolved callerBranchingBody 3
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          callerBranchingBody (callerArgs (true, x)) linkedMemory linkedHelpers)) =
        .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, linkedMemory) := rfl
    have hm₂ : (runMirStepsWithGap MirCallEnv.unresolved callerBorrowRefactoredBody 5
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          callerBorrowRefactoredBody (callerArgs (true, x)) linkedMemory linkedHelpers))).map
          Prod.fst =
        .ok (.scalar ⟨wrapScalarBits (x * 2) (scalarModulus 4), 4⟩) := rfl
    have hne₁ : runMirStepsWithGap MirCallEnv.unresolved callerBranchingBody 3
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          callerBranchingBody (callerArgs (true, x)) linkedMemory linkedHelpers)) ≠
        .gap .outOfFuel := ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀)
    have hne₂ : runMirStepsWithGap MirCallEnv.unresolved callerBorrowRefactoredBody 5
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          callerBorrowRefactoredBody (callerArgs (true, x)) linkedMemory linkedHelpers)) ≠
        .gap .outOfFuel := by
      intro h₀; rw [h₀] at hm₂; cases hm₂
    refine (gapBehaviors_equiv_iff_of_runs hne₁ hne₂).mpr ?_
    change GapEqErr (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
      (runMirStepsWithGap MirCallEnv.unresolved callerBranchingBody 3
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          callerBranchingBody (callerArgs (true, x)) linkedMemory linkedHelpers)))
      (runMirStepsWithGap MirCallEnv.unresolved callerBorrowRefactoredBody 5
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          callerBorrowRefactoredBody (callerArgs (true, x)) linkedMemory linkedHelpers)))
    rw [h₁]
    cases ho₂ : runMirStepsWithGap MirCallEnv.unresolved callerBorrowRefactoredBody 5
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          callerBorrowRefactoredBody (callerArgs (true, x)) linkedMemory linkedHelpers)) with
    | ok r₂ =>
      rw [ho₂] at hm₂
      have hr₂ := OutcomeWithGap.ok.inj hm₂
      change Value.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩ = r₂.1
      rw [hr₂, Nat.mul_two]
    | fault _ => rw [ho₂] at hm₂; cases hm₂
    | gap _ => rw [ho₂] at hm₂; cases hm₂
  have hStClosed : ∀ args mem, stPre args mem → ∀ site,
      ¬ mirStatefulGapBehaviors MirCallEnv.unresolved linkedHelpers callerBranchingBody
          (args, mem) (.gap (.unresolved site)) := by
    rintro _ _ ⟨x, _, rfl, rfl⟩ site hm
    have h₁ : runMirStepsWithGap MirCallEnv.unresolved callerBranchingBody 3
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          callerBranchingBody (callerArgs (true, x)) linkedMemory linkedHelpers)) =
        .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, linkedMemory) := rfl
    have heq : OutcomeWithGap.gap (.unresolved site) =
        runMirStepsWithGap MirCallEnv.unresolved callerBranchingBody 3
          (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            callerBranchingBody (callerArgs (true, x)) linkedMemory linkedHelpers)) :=
      (gapBehaviors_iff_of_run _
        (ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀)) _).mp hm
    rw [h₁] at heq
    cases heq
  have stRefactored := StatefulVerificationResult.of_contextEquiv hStEqOn
    (fun args mem v₁ _ v₂ _ _ hrv hp => by
      obtain ⟨x, hargs, hv₁⟩ := hp
      exact ⟨x, hargs, hrv.symm.trans hv₁⟩)
    hStClosed stBase
  -- 3. Strict memory inequality on `seqCallerBody` vs `borrowBeforeCallBody`
  have hModNotExact : ¬ ContextEquivOn (fun q => modPre q.1 q.2) (· = ·) (· = ·)
      (mirStatefulGapBehaviors (MirCallEnv.ofPure incHelperSummary) [] seqCallerBody)
      (mirStatefulGapBehaviors (MirCallEnv.ofPure incHelperSummary) [] borrowBeforeCallBody) := by
    intro hEq
    have h₁ : runMirStepsWithGap (MirCallEnv.ofPure incHelperSummary) seqCallerBody 5
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          seqCallerBody [.scalar ⟨3, 4⟩] unlinkedMemory [])) =
        .ok (.scalar ⟨8, 4⟩, unlinkedMemory) := rfl
    have h₂ : (runMirStepsWithGap (MirCallEnv.ofPure incHelperSummary) borrowBeforeCallBody 7
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          borrowBeforeCallBody [.scalar ⟨3, 4⟩] unlinkedMemory []))).map
          (fun r => r.2.borrows.length) = .ok 1 := rfl
    have hmem₁ : mirStatefulGapBehaviors (MirCallEnv.ofPure incHelperSummary) [] seqCallerBody
        ([.scalar ⟨3, 4⟩], unlinkedMemory) (.ok (.scalar ⟨8, 4⟩, unlinkedMemory)) :=
      ⟨(fun h₀ => by cases h₀), ⟨5, h₁⟩⟩
    obtain ⟨o₂, hm₂, hrel⟩ :=
      (hEq ([.scalar ⟨3, 4⟩], unlinkedMemory) ⟨3, by decide, rfl, rfl⟩).forward hmem₁
    have ho₂Eq : o₂ = .ok (.scalar ⟨8, 4⟩, unlinkedMemory) := (GapEqErr.eq_iff.mp hrel).symm
    subst ho₂Eq
    have hne₂' : runMirStepsWithGap (MirCallEnv.ofPure incHelperSummary) borrowBeforeCallBody 7
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          borrowBeforeCallBody [.scalar ⟨3, 4⟩] unlinkedMemory [])) ≠
        .gap .outOfFuel := by
      intro h₀; rw [h₀] at h₂; cases h₂
    have hsame : OutcomeWithGap.ok (.scalar ⟨8, 4⟩, unlinkedMemory) =
        runMirStepsWithGap (MirCallEnv.ofPure incHelperSummary) borrowBeforeCallBody 7
          (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            borrowBeforeCallBody [.scalar ⟨3, 4⟩] unlinkedMemory [])) :=
      (gapBehaviors_iff_of_run _ hne₂' _).mp hm₂
    rw [← hsame] at h₂
    cases OutcomeWithGap.ok.inj h₂
  -- 4. Base `ModularVerificationResult` on `seqCallerBody` + open-world relational transfer
  have modBase : Trusted.VerificationResult.ModularVerificationResult
      { body := seqCallerBody, envAssumed := envAssumed,
        pre := modPre, post := modPost, callees := [] } :=
    { proof := by
        rintro _ ⟨f, hfInc, rfl⟩ _ _ ⟨x, hx, rfl, rfl⟩
        have hInc : f "test::ext_helper" [.scalar ⟨x, 4⟩] =
            .ok (.scalar ⟨x + 1, 4⟩) := by
          rw [hfInc x, wrapScalarBits_of_lt
            (Nat.lt_of_le_of_lt (Nat.le_add_right (x + 1) (x + 1)) (show _ < scalarModulus 4 from hx))]
        have hrun : runMirWithGap (MirCallEnv.ofPure f) [] seqCallerBody 5 [.scalar ⟨x, 4⟩] =
            .ok (.scalar ⟨(x + 1) + (x + 1), 4⟩, unlinkedMemory) := by
          have hstep : runMirWithGap (MirCallEnv.ofPure f) [] seqCallerBody 5 [.scalar ⟨x, 4⟩] =
              runMirStepsWithGap (MirCallEnv.ofPure f) seqCallerBody 4
                (.running (seqCallerAtCall seqCallerBody x)) := rfl
          rw [hstep]
          have hHandle : mirGapHandle (MirCallEnv.ofPure f) (.inr (.call (extHelperReq x))) =
              .ok (.returned (.scalar ⟨x + 1, 4⟩) unlinkedMemory) := by
            dsimp only [mirGapHandle, MirCallEnv.ofPure, extHelperReq]
            rw [hInc]
            rfl
          have hcall : mirSiteGapStep (MirCallEnv.ofPure f) seqCallerBody
              (mirSiteOfExec seqCallerBody (.running (seqCallerAtCall seqCallerBody x))) =
              .next (mirNextSiteState seqCallerBody
                (mirSiteOfExec seqCallerBody (.running (seqCallerAtCall seqCallerBody x)))
                (resumeExternalCall (seqCallerAtCall seqCallerBody x)
                  (seqCallerAtCall seqCallerBody x).frame.locals
                  (locPlace 2) 1 .continue_
                  (.returned (.scalar ⟨x + 1, 4⟩) unlinkedMemory))) := by
            dsimp only [mirSiteGapStep, gapStep]
            have hVis : stepMirSiteState seqCallerBody
                (mirSiteOfExec seqCallerBody (.running (seqCallerAtCall seqCallerBody x))) =
                .vis (.inr (.inr (.call (extHelperReq x))))
                  (fun ans => mirNextSiteState seqCallerBody
                    (mirSiteOfExec seqCallerBody (.running (seqCallerAtCall seqCallerBody x)))
                    (resumeExternalCall (seqCallerAtCall seqCallerBody x)
                      (seqCallerAtCall seqCallerBody x).frame.locals
                      (locPlace 2) 1 .continue_ ans)) := rfl
            rw [hVis]
            dsimp only
            rw [hHandle]
          change runGapSteps (mirSiteGapStep (MirCallEnv.ofPure f) seqCallerBody) 4 _ = _
          rw [runGapSteps_succ_of_next _ hcall]
          have hfin : runGapSteps (mirSiteGapStep (MirCallEnv.ofPure f) seqCallerBody) 3
              (mirNextSiteState seqCallerBody
                (mirSiteOfExec seqCallerBody (.running (seqCallerAtCall seqCallerBody x)))
                (resumeExternalCall (seqCallerAtCall seqCallerBody x)
                  (seqCallerAtCall seqCallerBody x).frame.locals
                  (locPlace 2) 1 .continue_
                  (.returned (.scalar ⟨x + 1, 4⟩) unlinkedMemory))) =
              .ok (.scalar ⟨wrapScalarBits ((x + 1) + (x + 1)) (scalarModulus 4), 4⟩,
                unlinkedMemory) := rfl
          rw [hfin, wrapScalarBits_of_lt (show (x + 1) + (x + 1) < scalarModulus 4 from hx)]
        have hneRun : runMirWithGap (MirCallEnv.ofPure f) [] seqCallerBody 5 [.scalar ⟨x, 4⟩] ≠
            .gap .outOfFuel := ne_outOfFuel_of_eq hrun (fun h₀ => by cases h₀)
        have hDef : OutcomeSet.Defined ExecFault.isUB
            (mirStatefulGapBehaviors (MirCallEnv.ofPure f) [] seqCallerBody
              ([.scalar ⟨x, 4⟩], unlinkedMemory)) := by
          intro o ho
          have heq : o = runMirWithGap (MirCallEnv.ofPure f) [] seqCallerBody 5 [.scalar ⟨x, 4⟩] :=
            (gapBehaviors_iff_of_run _ hneRun o).mp ho
          rw [heq, hrun]
          exact trivial
        have hSafe := (mirHandledTree_safe_iff_defined (MirCallEnv.ofPure f) []
          seqCallerBody [.scalar ⟨x, 4⟩] unlinkedMemory).mpr hDef
        refine ⟨hSafe, fun outPair hrr _ retVal mem' hout => ?_⟩
        rcases outPair with ⟨tr, out⟩
        dsimp only at hout
        subst hout
        have hmem := (mirHandledTree_reachesRet_iff_of_defined hDef
          (.normal (retVal, mem'))).mp ⟨tr, hrr⟩
        have heq : classifyOutcome (.normal (retVal, mem')) =
            runMirWithGap (MirCallEnv.ofPure f) [] seqCallerBody 5 [.scalar ⟨x, 4⟩] :=
          (gapBehaviors_iff_of_run _ hneRun _).mp hmem
        rw [hrun] at heq
        have hpair := OutcomeWithGap.ok.inj heq
        exact ⟨x, rfl, congrArg Prod.fst hpair⟩ }
  have modRefactored := ModularVerificationResult.of_contextEquiv (body₂ := borrowBeforeCallBody)
    (rVal := fun r₁ r₂ : MirReturn => r₁.1 = r₂.1)
    (fun h hAss => by
      obtain ⟨f, hfInc, rfl⟩ := hAss
      refine ⟨MirCallEnv.ofPure f, rfl, ?_⟩
      rintro ⟨_, _⟩ ⟨x, _, rfl, rfl⟩
      exact (borrowBeforeCall_distinct_memory_contextEquiv f (fun y v hv => by
        rw [hfInc y] at hv
        exact ⟨_, (OutcomeWithGap.ok.inj hv).symm⟩)).2 x)
    (fun args mem v₁ _ v₂ _ _ hrv hp => by
      obtain ⟨x, hargs, hv₁⟩ := hp
      exact ⟨x, hargs, hrv.symm.trans hv₁⟩)
    modBase
  exact ⟨hStNotExact, ⟨stRefactored⟩, hModNotExact, ⟨modRefactored⟩⟩

/-! ### Part 5I: Function-Pointer Re-Interning & Remapping, `MirCallContract.holdsOn` Handler Refinement, Polymorphic `mirCallReqsAll` & Loop-Invariant Linking, and `TotalVerificationResult` / `UbExceptionVerificationResult` / Indexed-Cover Transfers -/

/-- Function-pointer MIR type `fn(u32) -> u32`. -/
@[reducible] def u32FnPtrMirTy : Ty :=
  { kind := .fnPtr [.uint .u32] (.uint .u32) .safe .rust, layoutIdx := 0 }

/-- Linked helper `fn fn_ten(x: u32) -> u32 { x + 10 }`. -/
def fnTenBody : CapturedMir :=
  mkMirBody "test::fn_ten" 1
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy]
    [ { statements :=
          [mkStmt (.assign (locPlace 0)
            (.binaryOp .add (.copy (locPlace 1)) (u32ConstOp 10)))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/-- Linked helper `fn fn_twenty(x: u32) -> u32 { x + 20 }`. -/
def fnTwentyBody : CapturedMir :=
  mkMirBody "test::fn_twenty" 1
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy]
    [ { statements :=
          [mkStmt (.assign (locPlace 0)
            (.binaryOp .add (.copy (locPlace 1)) (u32ConstOp 20)))]
        terminator := mkTerm .return_
        isCleanup := false } ]

def fnPtrCallees : List CapturedMir := [fnTenBody, fnTwentyBody]

/--
Standalone callee that reifies `fn_twenty` into a local function pointer
(allocating synthetic `allocId = 65536` in its fresh standalone memory!) and
returns `x + 1`.
-/
def extReifyTwentyBody : CapturedMir :=
  mkMirBody "test::ext_reify_twenty" 1
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy, mkDecl .mut u32FnPtrMirTy]
    [ { statements :=
          [mkStmt (.storageLive 2),
           mkStmt (.assign (locPlace 2)
             (.cast (.pointerCoercion "ReifyFnPointer")
               (fnItemOp "test::fn_twenty") u32FnPtrMirTy)),
           mkStmt (.assign (locPlace 0)
             (.binaryOp .add (.copy (locPlace 1)) (u32ConstOp 1)))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/--
Standalone callee that reifies `fn_twenty` (synthetic `allocId = 65536` in its
fresh standalone memory) and returns that function pointer directly to the caller!
-/
def extReturnTwentyFpBody : CapturedMir :=
  mkMirBody "test::ext_ret_twenty_fp" 1
    [mkDecl .mut u32FnPtrMirTy, mkDecl .not u32MirTy]
    [ { statements :=
          [mkStmt (.assign (locPlace 0)
            (.cast (.pointerCoercion "ReifyFnPointer")
              (fnItemOp "test::fn_twenty") u32FnPtrMirTy))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/--
Caller holding a live function pointer `fp = fn_ten as fn(u32) -> u32` across
an external call to `"test::ext_reify_twenty"`:
`let fp = fn_ten as fn(u32) -> u32; let y = ext_reify_twenty(x); let z = fp(x); y + z`.
-/
def fnPtrAcrossExtCallBody : CapturedMir :=
  mkMirBody "test::fnptr_across_ext" 1
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy, mkDecl .mut u32FnPtrMirTy,
     mkDecl .mut u32MirTy, mkDecl .mut u32MirTy]
    [ { statements :=
          [mkStmt (.storageLive 2),
           mkStmt (.assign (locPlace 2)
             (.cast (.pointerCoercion "ReifyFnPointer")
               (fnItemOp "test::fn_ten") u32FnPtrMirTy)),
           mkStmt (.storageLive 3)]
        terminator := mkTerm
          (.call (fnItemOp "test::ext_reify_twenty") [.copy (locPlace 1)]
            (locPlace 3) (some 1) .continue_)
        isCleanup := false },
      { statements := [mkStmt (.storageLive 4)]
        terminator := mkTerm
          (.call (.copy (locPlace 2)) [.copy (locPlace 1)]
            (locPlace 4) (some 2) .continue_)
        isCleanup := false },
      { statements :=
          [mkStmt (.assign (locPlace 0)
            (.binaryOp .add (.copy (locPlace 3)) (.copy (locPlace 4))))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/--
Equivalent caller reifying `fp = fn_ten as fn(u32) -> u32` AFTER calling
`"test::ext_reify_twenty"`:
`let y = ext_reify_twenty(x); let fp = fn_ten as fn(u32) -> u32; let z = fp(x); y + z`.
-/
def fnPtrAfterExtCallBody : CapturedMir :=
  mkMirBody "test::fnptr_after_ext" 1
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy, mkDecl .mut u32FnPtrMirTy,
     mkDecl .mut u32MirTy, mkDecl .mut u32MirTy]
    [ { statements := [mkStmt (.storageLive 3)]
        terminator := mkTerm
          (.call (fnItemOp "test::ext_reify_twenty") [.copy (locPlace 1)]
            (locPlace 3) (some 1) .continue_)
        isCleanup := false },
      { statements :=
          [mkStmt (.storageLive 2),
           mkStmt (.assign (locPlace 2)
             (.cast (.pointerCoercion "ReifyFnPointer")
               (fnItemOp "test::fn_ten") u32FnPtrMirTy)),
           mkStmt (.storageLive 4)]
        terminator := mkTerm
          (.call (.copy (locPlace 2)) [.copy (locPlace 1)]
            (locPlace 4) (some 2) .continue_)
        isCleanup := false },
      { statements :=
          [mkStmt (.assign (locPlace 0)
            (.binaryOp .add (.copy (locPlace 3)) (.copy (locPlace 4))))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/--
Caller exercising BOTH a pre-call caller `fnPtr` (`fn_ten`, `allocId = 65536`)
AND a function pointer returned by standalone `"test::ext_ret_twenty_fp"`
(`fn_twenty`, remapped from `65536` to `65537` by `Memory.mergeStandaloneReturn`!):
`let fp1 = fn_ten as fn(u32) -> u32; let fp2 = ext_ret_twenty_fp(x); fp1(x) + fp2(x)`.
-/
def callBothFnPtrsBody : CapturedMir :=
  mkMirBody "test::call_both_fnptrs" 1
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy, mkDecl .mut u32FnPtrMirTy,
     mkDecl .mut u32FnPtrMirTy, mkDecl .mut u32MirTy, mkDecl .mut u32MirTy]
    [ { statements :=
          [mkStmt (.storageLive 2),
           mkStmt (.assign (locPlace 2)
             (.cast (.pointerCoercion "ReifyFnPointer")
               (fnItemOp "test::fn_ten") u32FnPtrMirTy)),
           mkStmt (.storageLive 3)]
        terminator := mkTerm
          (.call (fnItemOp "test::ext_ret_twenty_fp") [.copy (locPlace 1)]
            (locPlace 3) (some 1) .continue_)
        isCleanup := false },
      { statements := [mkStmt (.storageLive 4)]
        terminator := mkTerm
          (.call (.copy (locPlace 2)) [.copy (locPlace 1)]
            (locPlace 4) (some 2) .continue_)
        isCleanup := false },
      { statements := [mkStmt (.storageLive 5)]
        terminator := mkTerm
          (.call (.copy (locPlace 3)) [.copy (locPlace 1)]
            (locPlace 5) (some 3) .continue_)
        isCleanup := false },
      { statements :=
          [mkStmt (.assign (locPlace 0)
            (.binaryOp .add (.copy (locPlace 4)) (.copy (locPlace 5))))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/--
Unsound naive `fnPtrs` list-prepend environment (`List.append after.fnPtrs before.fnPtrs`):
satisfies `callFramePreserved`, yet shadows caller `allocId = 65536` (`fn_ten`)
with standalone callee `allocId = 65536` (`fn_twenty`) because `lookupFnPtr`
scans `fnPtrs` from head to tail!
-/
def buggyPrependFnPtrEnv : MirCallEnv :=
  fun req =>
    if req.defPath == "test::ext_reify_twenty" then
      match runMirWithGap MirCallEnv.unresolved fnPtrCallees extReifyTwentyBody 6 req.args with
      | .ok (v, after) =>
        .ok (.returned v { req.memory with fnPtrs := List.append after.fnPtrs req.memory.fnPtrs })
      | .fault .panic => .ok (.panicked req.memory)
      | .fault .abort => .ok .aborted
      | .fault .ub => .fault .ub
      | .gap g => .gap (g.sealOutOfFuel req.defPath)
    else
      .gap (.unresolved req.defPath)

/--
Sound standalone environment (`MirCallEnv.ofStandaloneBody` using
`Memory.mergeStandaloneReturn` / `Memory.preserveCallerMemory`): re-interns
standalone `fnPtrs` via `internFnPtr` without shadowing caller `fnPtrs` and
remaps returned function-pointer `AllocId`s.
-/
def safeFnPtrStandaloneEnv : MirCallEnv :=
  MirCallEnv.ofStandaloneBody fnPtrCallees 6 (fun dp =>
    if dp == "test::ext_reify_twenty" then some extReifyTwentyBody
    else if dp == "test::ext_ret_twenty_fp" then some extReturnTwentyFpBody
    else none)

/--
Function-pointer head-shadowing vs collision-free re-interning & remapping canary:
1. Under `buggyPrependFnPtrEnv`, `fnPtrAcrossExtCallBody` on `x = 5` returns `31`
   (`fp` was hijacked from `fn_ten` to `fn_twenty`!) while `fnPtrAfterExtCallBody`
   returns `21`, refuting `ContextEquiv`;
2. Under `safeFnPtrStandaloneEnv` (`MirCallEnv.ofStandaloneBody`), BOTH callers
   return `21` on `x = 5` and satisfy `ContextEquiv (fun r₁ r₂ => r₁.1 = r₂.1) (· = ·)`
   across all `x : Nat`;
3. `callBothFnPtrsBody` calls BOTH the pre-existing caller `fp_ten` (`65536`) and
   the standalone-returned `fp_twenty` (remapped from `65536` to `65537`), returning
   `(5 + 10) + (5 + 20) = 40`; and
4. `Memory.lookupFnPtr_preserveCallerMemory_of_some` and
   `Memory.lookupFnPtr_restoreCallerFrame_of_some` guarantee zero caller shadowing.
-/
theorem standalone_fnPtr_shadowing_vs_reintern_and_remap :
    (runMirWithGap buggyPrependFnPtrEnv fnPtrCallees fnPtrAcrossExtCallBody 15
        [.scalar ⟨5, 4⟩]).map Prod.fst = .ok (.scalar ⟨31, 4⟩) ∧
      (runMirWithGap buggyPrependFnPtrEnv fnPtrCallees fnPtrAfterExtCallBody 15
        [.scalar ⟨5, 4⟩]).map Prod.fst = .ok (.scalar ⟨21, 4⟩) ∧
      ¬ ContextEquiv (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
        (fun x : Nat =>
          mirGapBehaviors buggyPrependFnPtrEnv fnPtrCallees fnPtrAcrossExtCallBody [.scalar ⟨x, 4⟩])
        (fun x : Nat =>
          mirGapBehaviors buggyPrependFnPtrEnv fnPtrCallees fnPtrAfterExtCallBody [.scalar ⟨x, 4⟩]) ∧
      (runMirWithGap safeFnPtrStandaloneEnv fnPtrCallees fnPtrAcrossExtCallBody 15
        [.scalar ⟨5, 4⟩]).map Prod.fst = .ok (.scalar ⟨21, 4⟩) ∧
      (runMirWithGap safeFnPtrStandaloneEnv fnPtrCallees fnPtrAfterExtCallBody 15
        [.scalar ⟨5, 4⟩]).map Prod.fst = .ok (.scalar ⟨21, 4⟩) ∧
      ContextEquiv (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
        (fun x : Nat =>
          mirGapBehaviors safeFnPtrStandaloneEnv fnPtrCallees fnPtrAcrossExtCallBody [.scalar ⟨x, 4⟩])
        (fun x : Nat =>
          mirGapBehaviors safeFnPtrStandaloneEnv fnPtrCallees fnPtrAfterExtCallBody [.scalar ⟨x, 4⟩]) ∧
      (runMirWithGap safeFnPtrStandaloneEnv fnPtrCallees callBothFnPtrsBody 20
        [.scalar ⟨5, 4⟩]).map Prod.fst = .ok (.scalar ⟨40, 4⟩) ∧
      (∀ (before after : Memory) (id : AllocId) (e : FnPtrEntry),
        lookupFnPtr before.fnPtrs id = some e →
          lookupFnPtr (Memory.preserveCallerMemory before after).fnPtrs id = some e ∧
          lookupFnPtr (Memory.restoreCallerFrame before after).fnPtrs id = some e) := by
  have hBug1 :
      (runMirWithGap buggyPrependFnPtrEnv fnPtrCallees fnPtrAcrossExtCallBody 15
        [.scalar ⟨5, 4⟩]).map Prod.fst = .ok (.scalar ⟨31, 4⟩) := rfl
  have hBug2 :
      (runMirWithGap buggyPrependFnPtrEnv fnPtrCallees fnPtrAfterExtCallBody 15
        [.scalar ⟨5, 4⟩]).map Prod.fst = .ok (.scalar ⟨21, 4⟩) := rfl
  have hNotCtx : ¬ ContextEquiv (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
      (fun x : Nat =>
        mirGapBehaviors buggyPrependFnPtrEnv fnPtrCallees fnPtrAcrossExtCallBody [.scalar ⟨x, 4⟩])
      (fun x : Nat =>
        mirGapBehaviors buggyPrependFnPtrEnv fnPtrCallees fnPtrAfterExtCallBody [.scalar ⟨x, 4⟩]) := by
    intro hEq
    have hne₁ : runMirWithGap buggyPrependFnPtrEnv fnPtrCallees fnPtrAcrossExtCallBody 15
        [.scalar ⟨5, 4⟩] ≠ .gap .outOfFuel := by
      intro h₀; rw [h₀] at hBug1; cases hBug1
    have hne₂ : runMirWithGap buggyPrependFnPtrEnv fnPtrCallees fnPtrAfterExtCallBody 15
        [.scalar ⟨5, 4⟩] ≠ .gap .outOfFuel := by
      intro h₀; rw [h₀] at hBug2; cases hBug2
    have hrel := (mirGapBehaviors_equiv_iff_of_runs hne₁ hne₂).mp (hEq 5)
    cases ho₁ : runMirWithGap buggyPrependFnPtrEnv fnPtrCallees fnPtrAcrossExtCallBody 15
        [.scalar ⟨5, 4⟩] with
    | ok r₁ =>
      cases ho₂ : runMirWithGap buggyPrependFnPtrEnv fnPtrCallees fnPtrAfterExtCallBody 15
          [.scalar ⟨5, 4⟩] with
      | ok r₂ =>
        rw [ho₁] at hBug1; rw [ho₂] at hBug2; rw [ho₁, ho₂] at hrel
        have hv : Value.scalar ⟨31, 4⟩ = Value.scalar ⟨21, 4⟩ :=
          (OutcomeWithGap.ok.inj hBug1).symm.trans (Eq.trans hrel
            (OutcomeWithGap.ok.inj hBug2))
        cases hv
      | fault _ => rw [ho₂] at hBug2; cases hBug2
      | gap _ => rw [ho₂] at hBug2; cases hBug2
    | fault _ => rw [ho₁] at hBug1; cases hBug1
    | gap _ => rw [ho₁] at hBug1; cases hBug1
  have hSafeCtx : ContextEquiv (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
      (fun x : Nat =>
        mirGapBehaviors safeFnPtrStandaloneEnv fnPtrCallees fnPtrAcrossExtCallBody [.scalar ⟨x, 4⟩])
      (fun x : Nat =>
        mirGapBehaviors safeFnPtrStandaloneEnv fnPtrCallees fnPtrAfterExtCallBody [.scalar ⟨x, 4⟩]) := by
    intro x
    have hm₁ : (runMirWithGap safeFnPtrStandaloneEnv fnPtrCallees fnPtrAcrossExtCallBody 15
        [.scalar ⟨x, 4⟩]).map Prod.fst =
        .ok (.scalar ⟨wrapScalarBits
          (wrapScalarBits (x + 1) (scalarModulus 4) + wrapScalarBits (x + 10) (scalarModulus 4))
          (scalarModulus 4), 4⟩) := rfl
    have hm₂ : (runMirWithGap safeFnPtrStandaloneEnv fnPtrCallees fnPtrAfterExtCallBody 15
        [.scalar ⟨x, 4⟩]).map Prod.fst =
        .ok (.scalar ⟨wrapScalarBits
          (wrapScalarBits (x + 1) (scalarModulus 4) + wrapScalarBits (x + 10) (scalarModulus 4))
          (scalarModulus 4), 4⟩) := rfl
    have hne₁ : runMirWithGap safeFnPtrStandaloneEnv fnPtrCallees fnPtrAcrossExtCallBody 15
        [.scalar ⟨x, 4⟩] ≠ .gap .outOfFuel := by
      intro h₀; rw [h₀] at hm₁; cases hm₁
    refine mirGapBehaviors_equiv_of_runs (fuel₂ := 15) hne₁ ?_
    cases ho₁ : runMirWithGap safeFnPtrStandaloneEnv fnPtrCallees fnPtrAcrossExtCallBody 15
        [.scalar ⟨x, 4⟩] with
    | ok r₁ =>
      cases ho₂ : runMirWithGap safeFnPtrStandaloneEnv fnPtrCallees fnPtrAfterExtCallBody 15
          [.scalar ⟨x, 4⟩] with
      | ok r₂ =>
        rw [ho₁] at hm₁; rw [ho₂] at hm₂
        exact (OutcomeWithGap.ok.inj hm₁).trans (OutcomeWithGap.ok.inj hm₂).symm
      | fault _ => rw [ho₂] at hm₂; cases hm₂
      | gap _ => rw [ho₂] at hm₂; cases hm₂
    | fault _ => rw [ho₁] at hm₁; cases hm₁
    | gap _ => rw [ho₁] at hm₁; cases hm₁
  exact ⟨hBug1, hBug2, hNotCtx, rfl, rfl, hSafeCtx, rfl,
    fun _ after _ _ h =>
      ⟨Memory.lookupFnPtr_preserveCallerMemory_of_some h,
       Memory.lookupFnPtr_restoreCallerFrame_of_some h⟩⟩

section CallContractCanaries

open Trusted.ITree

/--
Genuine `MirCallContract` for `"test::ext_helper"`: specifies `x + 1` on `u32`
arguments while admitting ALL `ExternalCallHandler`s satisfying `holdsOn`
(including `.tau`-stepped, `MirObsE`-emitting, and `ITree.spin` handlers).
-/
def incCallContract : Trusted.VerificationResult.MirCallContract where
  pre req := req.defPath = "test::ext_helper" ∧ ∃ x, req.args = [.scalar ⟨x, 4⟩]
  post req ans :=
    ∃ x, req.args = [.scalar ⟨x, 4⟩] ∧
      ans = .returned (.scalar ⟨wrapScalarBits (x + 1) (scalarModulus 4), 4⟩) req.memory

/--
A terminating `.tau`-delayed `ExternalCallHandler` that satisfies
`incCallContract.holdsOn` yet is NOT equal to `env.toExternalCallHandler` for
any `env : MirCallEnv`!
-/
def tauIncHandler : Trusted.VerificationResult.ExternalCallHandler :=
  fun req => .tau ((MirCallEnv.ofPure incHelperSummary).toExternalCallHandler req)

/--
`MirCallContract.holdsOn` modular transfer & non-`toExternalCallHandler` canary:
1. Requiring `h = env.toExternalCallHandler` is refutable on `incCallContract.holdsOn`
   BOTH via `mirCallContract_not_all_toExternalCallHandler` (`ITree.spin`) AND via
   the terminating `.tau`-stepped `tauIncHandler`; and
2. `ModularVerificationResult.of_callContract_contextEquiv` transfers a genuine
   kernel `ModularVerificationResult` with `envAssumed := incCallContract.holdsOn`
   from `seqCallerBody` to `borrowBeforeCallBody` across distinct borrow histories!
-/
theorem callContract_holdsOn_modular_transfer_and_non_env_handlers :
    let modPre : List Value → Memory → Prop :=
      fun args mem =>
        ∃ x, (x + 1) + (x + 1) < 4294967296 ∧ args = [.scalar ⟨x, 4⟩] ∧ mem = unlinkedMemory
    let modPost : List Value → Memory → Value → Memory → Prop :=
      fun args _ ret _ =>
        ∃ x, args = [.scalar ⟨x, 4⟩] ∧ ret = .scalar ⟨(x + 1) + (x + 1), 4⟩
    (¬ ∀ h, incCallContract.holdsOn h → ∃ env : MirCallEnv, h = env.toExternalCallHandler) ∧
      incCallContract.holdsOn tauIncHandler ∧
      (∀ env : MirCallEnv, tauIncHandler ≠ env.toExternalCallHandler) ∧
      Nonempty (Trusted.VerificationResult.ModularVerificationResult
        { body := borrowBeforeCallBody, envAssumed := incCallContract.holdsOn,
          pre := modPre, post := modPost, callees := [] }) := by
  dsimp only
  let modPre : List Value → Memory → Prop :=
    fun args mem =>
      ∃ x, (x + 1) + (x + 1) < 4294967296 ∧ args = [.scalar ⟨x, 4⟩] ∧ mem = unlinkedMemory
  let modPost : List Value → Memory → Value → Memory → Prop :=
    fun args _ ret _ =>
      ∃ x, args = [.scalar ⟨x, 4⟩] ∧ ret = .scalar ⟨(x + 1) + (x + 1), 4⟩
  let env₀ := MirCallEnv.ofPure incHelperSummary
  have hNoAll : ¬ ∀ h, incCallContract.holdsOn h →
      ∃ env : MirCallEnv, h = env.toExternalCallHandler := by
    intro hAll
    obtain ⟨h, hHolds, hNe⟩ := mirCallContract_not_all_toExternalCallHandler incCallContract
    obtain ⟨env, heq⟩ := hAll h hHolds
    exact hNe env heq
  have hEnvHolds : incCallContract.holdsOn env₀.toExternalCallHandler := by
    rintro req ⟨hPath, x, hArgs⟩
    have hseal : env₀.seal req =
        .ok (.returned (.scalar ⟨wrapScalarBits (x + 1) (scalarModulus 4), 4⟩) req.memory) := by
      dsimp only [env₀, MirCallEnv.seal, MirCallEnv.ofPure]
      rw [hPath, hArgs]
      rfl
    have hTree : env₀.toExternalCallHandler req =
        ITree.ret (.returned (.scalar ⟨wrapScalarBits (x + 1) (scalarModulus 4), 4⟩) req.memory) := by
      unfold MirCallEnv.toExternalCallHandler; rw [hseal]
    rw [hTree]
    have hRetEq : ∀ {s₀ u : ITree Trusted.VerificationResult.MirClosedEffect MirCallAns} {tr},
        Reaches s₀ tr u →
        s₀ = ITree.ret (.returned (.scalar ⟨wrapScalarBits (x + 1) (scalarModulus 4), 4⟩) req.memory) →
        u = ITree.ret (.returned (.scalar ⟨wrapScalarBits (x + 1) (scalarModulus 4), 4⟩) req.memory) := by
      intro s₀ u tr hr
      induction hr with
      | refl => exact fun hs => hs
      | tau htau _ _ => intro hs; rw [hs, ITree.observe_ret] at htau; cases htau
      | vis hv _ _ _ _ => intro hs; rw [hs, ITree.observe_ret] at hv; cases hv
    refine ⟨fun tr u hru ⟨u', _, _, hts, hvu', _⟩ => ?_, fun tr ans ⟨u, hru, hur⟩ => ?_⟩
    · have hu := hRetEq hru rfl
      subst hu
      cases hts with
      | refl => rw [ITree.observe_ret] at hvu'; cases hvu'
      | step htau _ => rw [ITree.observe_ret] at htau; cases htau
    · rw [hRetEq hru rfl, ITree.observe_ret] at hur
      injection hur with ha
      exact ⟨x, hArgs, ha.symm⟩
  have hTauHolds : incCallContract.holdsOn tauIncHandler := by
    intro req hpre
    obtain ⟨hs, hr⟩ := hEnvHolds req hpre
    refine ⟨fun tr u hru hfn => ?_, fun tr ans ⟨u, hru, hur⟩ => ?_⟩
    · cases hru with
      | refl =>
        obtain ⟨u', idx, k, hts, hvu', hfi⟩ := hfn
        cases hts with
        | refl =>
          dsimp only [tauIncHandler] at hvu'
          rw [ITree.observe_tau] at hvu'; cases hvu'
        | step htau hts' =>
          dsimp only [tauIncHandler] at htau
          rw [ITree.observe_tau] at htau
          injection htau with hnext
          subst hnext
          exact hs [] _ (.refl _) ⟨u', idx, k, hts', hvu', hfi⟩
      | tau htau hr' =>
        dsimp only [tauIncHandler] at htau
        rw [ITree.observe_tau] at htau
        injection htau with hnext
        subst hnext
        exact hs _ u hr' hfn
      | vis hv _ _ _ =>
        dsimp only [tauIncHandler] at hv
        rw [ITree.observe_tau] at hv; cases hv
    · cases hru with
      | refl =>
        dsimp only [tauIncHandler] at hur
        rw [ITree.observe_tau] at hur; cases hur
      | tau htau hr' =>
        dsimp only [tauIncHandler] at htau
        rw [ITree.observe_tau] at htau
        injection htau with hnext
        subst hnext
        exact hr tr ans ⟨u, hr', hur⟩
      | vis hv _ _ _ =>
        dsimp only [tauIncHandler] at hv
        rw [ITree.observe_tau] at hv; cases hv
  have hTauNe : ∀ env : MirCallEnv, tauIncHandler ≠ env.toExternalCallHandler := by
    intro env heq
    let req₀ : MirCallReq := { defPath := "", args := [], memory := unlinkedMemory }
    have hobs := congrArg ITree.observe (congrFun heq req₀)
    dsimp only [tauIncHandler] at hobs
    rw [ITree.observe_tau] at hobs
    unfold MirCallEnv.toExternalCallHandler at hobs
    have hFailNe : ∀ (t₀ : ITree Trusted.VerificationResult.MirClosedEffect MirCallAns)
        (fk : FailureKind),
        ITreeF.tau t₀ ≠
          (ITree.fail (E := Trusted.VerificationResult.MirClosedEffect)
            (R := MirCallAns) fk).observe := by
      intro t₀ fk h
      unfold ITree.fail ITree.triggerSub at h
      rw [Anneal.ITree.vis_bind, ITree.observe_vis] at h
      cases h
    cases hseal : env.seal req₀ with
    | ok ans => rw [hseal, ITree.observe_ret] at hobs; cases hobs
    | fault u => cases u; rw [hseal] at hobs; exact hFailNe _ .ub hobs
    | gap g =>
      cases g <;> rw [hseal] at hobs <;>
        first | exact hFailNe _ .outOfFuel hobs | exact hFailNe _ .unsupported hobs
  -- Base contract under `env₀.toExternalCallHandler`, lifted to ALL `incCallContract.holdsOn`
  have hEnvBase :
      (fun args mem =>
        (Trusted.VerificationResult.mirHandledTreeWithCallees
          seqCallerBody args mem [] env₀.toExternalCallHandler).toPartial) ≤
        Trusted.VerificationResult.MirClosedStatefulContractSpec modPre modPre modPost := by
    rintro _ _ ⟨x, hx, rfl, rfl⟩
    have hrun : runMirWithGap env₀ [] seqCallerBody 5 [.scalar ⟨x, 4⟩] =
        .ok (.scalar ⟨(x + 1) + (x + 1), 4⟩, unlinkedMemory) := by
      have h₀ : runMirWithGap env₀ [] seqCallerBody 5 [.scalar ⟨x, 4⟩] =
          .ok (.scalar ⟨wrapScalarBits
            (wrapScalarBits (x + 1) (scalarModulus 4) +
              wrapScalarBits (x + 1) (scalarModulus 4))
            (scalarModulus 4), 4⟩, unlinkedMemory) := rfl
      have hx₁ : x + 1 < scalarModulus 4 :=
        Nat.lt_of_le_of_lt (Nat.le_add_right (x + 1) (x + 1)) hx
      rw [h₀, wrapScalarBits_of_lt hx₁, wrapScalarBits_of_lt (show (x + 1) + (x + 1) < scalarModulus 4 from hx)]
    have hne : runMirWithGap env₀ [] seqCallerBody 5 [.scalar ⟨x, 4⟩] ≠ .gap .outOfFuel :=
      ne_outOfFuel_of_eq hrun (fun h₀ => by cases h₀)
    have hDef : OutcomeSet.Defined ExecFault.isUB
        (mirStatefulGapBehaviors env₀ [] seqCallerBody ([.scalar ⟨x, 4⟩], unlinkedMemory)) := by
      intro o ho
      have heq : o = runMirWithGap env₀ [] seqCallerBody 5 [.scalar ⟨x, 4⟩] :=
        (gapBehaviors_iff_of_run _ hne o).mp ho
      rw [heq, hrun]; exact trivial
    refine ⟨(mirHandledTree_safe_iff_defined env₀ [] seqCallerBody [.scalar ⟨x, 4⟩] unlinkedMemory).mpr hDef,
      fun outPair hrr _ retVal mem' hout => ?_⟩
    rcases outPair with ⟨tr, out⟩
    dsimp only at hout; subst hout
    have hm := (mirHandledTree_reachesRet_iff_of_defined hDef (.normal (retVal, mem'))).mp ⟨tr, hrr⟩
    have heq : classifyOutcome (.normal (retVal, mem')) =
        runMirWithGap env₀ [] seqCallerBody 5 [.scalar ⟨x, 4⟩] :=
      (gapBehaviors_iff_of_run _ hne _).mp hm
    rw [hrun] at heq
    exact ⟨x, rfl, congrArg Prod.fst (OutcomeWithGap.ok.inj heq)⟩
  have hBeqSelf : ∀ n : Nat, Nat.beq n n = true := by
    intro n; induction n with | zero => rfl | succ n ih => exact ih
  have hExtReq : ∀ (x : Nat) (req : MirCallReq),
      ((req.defPath == "test::ext_helper") &&
        match req.args with
        | [.scalar ⟨y, sz⟩] => Nat.beq y x && Nat.beq sz 4
        | _ => false) = true →
      req.defPath = "test::ext_helper" ∧ req.args = [.scalar ⟨x, 4⟩] := by
    intro x req hp
    cases hb : (req.defPath == "test::ext_helper") with
    | false => rw [hb] at hp; cases hp
    | true =>
      rw [hb] at hp
      refine ⟨eq_of_beq hb, ?_⟩
      cases ha : req.args with
      | nil => rw [ha] at hp; cases hp
      | cons v vs =>
        cases vs with
        | cons _ _ => rw [ha] at hp; cases v <;> cases hp
        | nil =>
          cases v with
          | unit => rw [ha] at hp; cases hp
          | ptr _ _ => rw [ha] at hp; cases hp
          | aggregate _ _ => rw [ha] at hp; cases hp
          | scalar sc =>
            rcases sc with ⟨y, sz⟩
            rw [ha] at hp
            dsimp only at hp
            cases hy : Nat.beq y x with
            | false => rw [hy] at hp; cases hp
            | true =>
              rw [hy] at hp
              have hsz : Nat.beq sz 4 = true := hp
              rw [Nat.eq_of_beq_eq_true hy, Nat.eq_of_beq_eq_true hsz]
  have hReachSeq : ∀ args mem, modPre args mem →
      ∀ req,
        MirCallReachable env₀ seqCallerBody
          (mirSiteOfExec seqCallerBody (.running
            (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
              seqCallerBody args mem []))) req →
        ∀ ans, env₀.seal req = .ok ans →
          incCallContract.pre req ∧ ∀ ans', incCallContract.post req ans' → ans' = ans := by
    rintro _ _ ⟨x, _, rfl, rfl⟩ req hreach ans hseal
    let predSeq : MirCallReq → Bool :=
      fun r => (r.defPath == "test::ext_helper") &&
        match r.args with
        | [.scalar ⟨y, sz⟩] => Nat.beq y x && Nat.beq sz 4
        | _ => false
    have hChk : mirCallReqsAll env₀ seqCallerBody predSeq 6
        (mirSiteOfExec seqCallerBody (.running
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            seqCallerBody [.scalar ⟨x, 4⟩] unlinkedMemory []))) = true := by
      have hEval : mirCallReqsAll env₀ seqCallerBody predSeq 6
          (mirSiteOfExec seqCallerBody (.running
            (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
              seqCallerBody [.scalar ⟨x, 4⟩] unlinkedMemory []))) =
          (true && (("test::ext_helper" == "test::ext_helper") && (Nat.beq x x && Nat.beq 4 4) && true)) := rfl
      rw [hEval, hBeqSelf x]
      rfl
    obtain ⟨hPath, hArgs⟩ := hExtReq x req (mirCallReachable_of_callReqsAll hChk hreach)
    have hAns : ans = .returned (.scalar ⟨wrapScalarBits (x + 1) (scalarModulus 4), 4⟩) req.memory := by
      dsimp only [env₀, MirCallEnv.seal, MirCallEnv.ofPure] at hseal
      rw [hPath, hArgs] at hseal
      exact (OutcomeWithGap.ok.inj hseal).symm
    refine ⟨⟨hPath, x, hArgs⟩, fun ans' hpost => ?_⟩
    obtain ⟨y, hyArgs, hyAns⟩ := hpost
    rw [hArgs] at hyArgs
    have hxy : x = y := by
      injection List.cons.inj hyArgs |>.1 with hsc
      injection hsc
    subst hxy
    exact hyAns.trans hAns.symm
  have modBase : Trusted.VerificationResult.ModularVerificationResult
      { body := seqCallerBody, envAssumed := incCallContract.holdsOn,
        pre := modPre, post := modPost, callees := [] } :=
    ⟨fun h hHolds => mirClosedStatefulContract_of_handler_refines_on
      (fun args mem hp req hreach ans hseal => by
        obtain ⟨hpre, huniq⟩ := hReachSeq args mem hp req hreach ans hseal
        obtain ⟨hs, hr⟩ := hHolds req hpre
        exact ⟨hs, fun tr_h ans' hrr => huniq ans' (hr tr_h ans' hrr)⟩)
      hEnvBase⟩
  have hReachBorrow : ∀ args mem, modPre args mem →
      ∀ req,
        MirCallReachable env₀ borrowBeforeCallBody
          (mirSiteOfExec borrowBeforeCallBody (.running
            (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
              borrowBeforeCallBody args mem []))) req →
        ∀ ans, env₀.seal req = .ok ans →
          incCallContract.pre req ∧ ∀ ans', incCallContract.post req ans' → ans' = ans := by
    rintro _ _ ⟨x, _, rfl, rfl⟩ req hreach ans hseal
    let predBorrow : MirCallReq → Bool :=
      fun r => (r.defPath == "test::ext_helper") &&
        match r.args with
        | [.scalar ⟨y, sz⟩] => Nat.beq y x && Nat.beq sz 4
        | _ => false
    have hChk : mirCallReqsAll env₀ borrowBeforeCallBody predBorrow 8
        (mirSiteOfExec borrowBeforeCallBody (.running
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            borrowBeforeCallBody [.scalar ⟨x, 4⟩] unlinkedMemory []))) = true := by
      have hEval : mirCallReqsAll env₀ borrowBeforeCallBody predBorrow 8
          (mirSiteOfExec borrowBeforeCallBody (.running
            (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
              borrowBeforeCallBody [.scalar ⟨x, 4⟩] unlinkedMemory []))) =
          (true && (true && (true && (("test::ext_helper" == "test::ext_helper") && (Nat.beq x x && Nat.beq 4 4) && true)))) := rfl
      rw [hEval, hBeqSelf x]
      rfl
    obtain ⟨hPath, hArgs⟩ := hExtReq x req (mirCallReachable_of_callReqsAll hChk hreach)
    have hAns : ans = .returned (.scalar ⟨wrapScalarBits (x + 1) (scalarModulus 4), 4⟩) req.memory := by
      dsimp only [env₀, MirCallEnv.seal, MirCallEnv.ofPure] at hseal
      rw [hPath, hArgs] at hseal
      exact (OutcomeWithGap.ok.inj hseal).symm
    refine ⟨⟨hPath, x, hArgs⟩, fun ans' hpost => ?_⟩
    obtain ⟨y, hyArgs, hyAns⟩ := hpost
    rw [hArgs] at hyArgs
    have hxy : x = y := by
      injection List.cons.inj hyArgs |>.1 with hsc
      injection hsc
    subst hxy
    exact hyAns.trans hAns.symm
  have modTransferred := ModularVerificationResult.of_callContract_contextEquiv
    (body₂ := borrowBeforeCallBody) (rVal := fun r₁ r₂ : MirReturn => r₁.1 = r₂.1)
    hEnvHolds
    (by
      rintro ⟨_, _⟩ ⟨x, _, rfl, rfl⟩
      exact (borrowBeforeCall_distinct_memory_contextEquiv incHelperSummary
        (fun y v hv => ⟨_, (OutcomeWithGap.ok.inj hv).symm⟩)).2 x)
    hReachBorrow
    (fun args _ v₁ _ v₂ _ _ hrv hp => by
      obtain ⟨x, hargs, hv₁⟩ := hp
      exact ⟨x, hargs, hrv.symm.trans hv₁⟩)
    modBase
  exact ⟨hNoAll, hTauHolds, hTauNe, ⟨modTransferred⟩⟩

/--
Caller invoking polymorphic `"test::poly_id"` specialized at `typeArgs := [.uint .u32]`.
-/
def polyU32CallerBody : CapturedMir :=
  mkMirBody "test::poly_u32_caller" 1
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy]
    [ { statements := []
        terminator := mkTerm
          (.call
            (.constant
              { ty := { kind := .fnDef "test::poly_id" [.uint .u32], layoutIdx := 0 }
                val := .zeroSized })
            [.copy (locPlace 1)] (locPlace 0) (some 1) .continue_)
        isCleanup := false },
      returnBlock ]

def isU32TypeArg : List RigidTy → Bool
  | [.uint .u32] => true
  | _ => false

def isU64TypeArg : List RigidTy → Bool
  | [.uint .u64] => true
  | _ => false

def polyEnv₁ : MirCallEnv :=
  fun req =>
    if (req.defPath == "test::poly_id") && isU32TypeArg req.typeArgs then
      match req.args with
      | [.scalar ⟨x, 4⟩] =>
        .ok (.returned (.scalar ⟨wrapScalarBits (x + 1) (scalarModulus 4), 4⟩) req.memory)
      | _ => .gap (.unresolved req.defPath)
    else
      .gap (.unresolved req.defPath)

def polyEnv₂ : MirCallEnv :=
  fun req =>
    if (req.defPath == "test::poly_id") && isU32TypeArg req.typeArgs then
      match req.args with
      | [.scalar ⟨x, 4⟩] =>
        .ok (.returned (.scalar ⟨wrapScalarBits (x + 1) (scalarModulus 4), 4⟩) req.memory)
      | _ => .gap (.unresolved req.defPath)
    else if (req.defPath == "test::poly_id") && isU64TypeArg req.typeArgs then
      .ok (.returned (.scalar ⟨0, 8⟩) req.memory)
    else
      .gap (.unresolved req.defPath)

/--
Unbounded countdown coalgebra emitting `"test::tick"` `n` times before halting:
no fixed `fuel` satisfies `stepRequestsAll ... fuel n` uniformly for all `n : Nat`,
yet `stepRequestReachable_of_inv` proves handler congruence across ALL `n : Nat`!
-/
def countdownStep : Nat → ITreeF (SumE (FailE FailureKind) MirCallE) (Outcome Unit) Nat
  | 0 => .ret (.normal ())
  | n + 1 =>
    .vis (.inr (.call { defPath := "test::tick", args := [], memory := unlinkedMemory }))
      (fun _ => n)

/--
Polymorphic `typeArgs`-sensitive `mirCallReqsAll` and unbounded loop-invariant
`stepRequestReachable_of_inv` canary:
1. `polyEnv₁` and `polyEnv₂` DISAGREE on `req.defPath == "test::poly_id"` (at
   `typeArgs = [.uint .u64]`, `polyEnv₁` gaps while `polyEnv₂` returns `.ok`),
   so `DefPath`-only `mirRequestsAllIn` cannot separate the two monomorphizations;
2. `mirGapBehaviors_env_congr_of_callReqsAll` and
   `mirStatefulGapBehaviors_env_congr_of_callReqsAll` distinguish `req.typeArgs = [.uint .u32]`
   and prove `OutcomeSetEquiv` across all `x : Nat`; and
3. On `countdownStep`, NO fixed `fuel : Nat` certifies all `n : Nat` via bounded
   `stepRequestsAll`, whereas `stepRequestReachable_of_inv` proves
   `gapBehaviors_handle_congr_on` uniformly for every `n : Nat`!
-/
theorem poly_typeArgs_callReqsAll_and_loop_inv_env_linking :
    (∃ req : MirCallReq,
      (req.defPath == "test::poly_id") = true ∧
        ¬ GapEqErr (· = ·) (· = ·) (polyEnv₁.seal req) (polyEnv₂.seal req)) ∧
      (∀ x : Nat,
        OutcomeSetEquiv (GapEqErr (· = ·) (· = ·))
          (mirGapBehaviors polyEnv₁ [] polyU32CallerBody [.scalar ⟨x, 4⟩])
          (mirGapBehaviors polyEnv₂ [] polyU32CallerBody [.scalar ⟨x, 4⟩]) ∧
        OutcomeSetEquiv (GapEqErr (· = ·) (· = ·))
          (mirStatefulGapBehaviors polyEnv₁ [] polyU32CallerBody ([.scalar ⟨x, 4⟩], unlinkedMemory))
          (mirStatefulGapBehaviors polyEnv₂ [] polyU32CallerBody ([.scalar ⟨x, 4⟩], unlinkedMemory))) ∧
      (let tickH₁ : (i : MirCallE.I) → OutcomeWithGap ExecFault (GapTag DefPath) (MirCallE.O i) :=
          fun i => match i with
            | .call r =>
              if r.defPath == "test::tick" then .ok (.returned .unit r.memory)
              else .gap (.unresolved r.defPath)
        let tickH₂ : (i : MirCallE.I) → OutcomeWithGap ExecFault (GapTag DefPath) (MirCallE.O i) :=
          fun i => match i with
            | .call r =>
              if r.defPath == "test::tick" then .ok (.returned .unit r.memory)
              else .ok .aborted
        (∀ fuel : Nat,
          stepRequestsAll countdownStep (fun _ => "test::countdown") tickH₁
            (fun i => match i with | .call r => r.defPath == "test::tick")
            fuel (fuel + 1) = false) ∧
        (∀ n : Nat,
          OutcomeSetEquiv (GapEqErr (· = ·) (· = ·))
            (gapBehaviors (gapStep countdownStep (fun _ => "test::countdown") tickH₁) n)
            (gapBehaviors (gapStep countdownStep (fun _ => "test::countdown") tickH₂) n))) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨{ defPath := "test::poly_id", typeArgs := [.uint .u64],
              args := [], memory := unlinkedMemory }, rfl, ?_⟩
    intro hrel
    exact False.elim hrel
  · intro x
    let predU32 : MirCallReq → Bool :=
      fun req => (req.defPath == "test::poly_id") && isU32TypeArg req.typeArgs
    have hHen : ∀ req, predU32 req = true →
        GapEqErr (· = ·) (· = ·) (polyEnv₁.seal req) (polyEnv₂.seal req) := by
      intro req hp
      dsimp only [predU32] at hp
      dsimp only [MirCallEnv.seal, polyEnv₁, polyEnv₂]
      rw [hp]
      exact GapEqErr.refl (fun _ => rfl) (fun _ => rfl) _
    exact ⟨mirGapBehaviors_env_congr_of_callReqsAll (pred := predU32) (fuel := 5) rfl hHen,
      mirStatefulGapBehaviors_env_congr_of_callReqsAll (pred := predU32) (fuel := 5) rfl hHen⟩
  · dsimp only
    let tickH₁ : (i : MirCallE.I) → OutcomeWithGap ExecFault (GapTag DefPath) (MirCallE.O i) :=
      fun i => match i with
        | .call r =>
          if r.defPath == "test::tick" then .ok (.returned .unit r.memory)
          else .gap (.unresolved r.defPath)
    let tickH₂ : (i : MirCallE.I) → OutcomeWithGap ExecFault (GapTag DefPath) (MirCallE.O i) :=
      fun i => match i with
        | .call r =>
          if r.defPath == "test::tick" then .ok (.returned .unit r.memory)
          else .ok .aborted
    have hNoFixedFuel : ∀ fuel : Nat,
        stepRequestsAll countdownStep (fun _ => "test::countdown") tickH₁
          (fun i => match i with | .call r => r.defPath == "test::tick")
          fuel (fuel + 1) = false := by
      intro fuel
      induction fuel with
      | zero => rfl
      | succ fuel ih => exact ih
    refine ⟨hNoFixedFuel, fun n => ?_⟩
    refine gapBehaviors_handle_congr_on (fun _ => rfl) ?_
    refine stepRequestReachable_of_inv (I := fun _ => True) trivial
      (fun _ _ _ _ => trivial) (fun t i k _ ht => ?_)
    cases t with
    | zero => cases ht
    | succ m =>
      dsimp only [countdownStep] at ht
      injection ht with hi _
      injection hi with hcall
      subst hcall
      exact (rfl : MirCallAns.returned .unit unlinkedMemory = _)

/--
Branchless double body (`0` `switchInt` events): `fn branchless_double(flag: bool, x: u32) -> u32 { x + x }`.
Agrees with `callerBranchingBody` (`1` `switchInt` event) on `flag = true`, while
differing in CFG branching observations (`MirObsE`)!
-/
def branchlessDoubleCallerBody : CapturedMir :=
  mkMirBody "test::branchless_double_caller" 2
    [mkDecl .mut u32MirTy, mkDecl .not boolMirTy, mkDecl .not u32MirTy]
    [ { statements :=
          [mkStmt (.assign (locPlace 0)
            (.binaryOp .add (.copy (locPlace 2)) (.copy (locPlace 2))))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/--
Constructive `MirConstructiveTotalHolds` (`mirConstructiveTotalHolds_of_contextEquiv`),
trusted `RefinesStatefulMirWithCallees` (`refinesStatefulMirWithCallees_of_contextEquiv`
and `mirObsErasedStatefulTree_toPartial_eq_of_contextEquiv` across BOTH gapping
inputs AND distinct `switchInt` branching!), kernel
`UbExceptionVerificationResult.of_contextEquiv` (with genuinely `.unsupported`-gapping
inputs inside `pre` outside `strictSafetyPre`!), constructive `Fin 3` indexed-cover
patching (`ContextEquiv.of_iSup_cover`), and relational Layer 1A specification
transfers (`ContextEquivOn.valTransfer_spec_rel`, `ContextEquivOn.transfer_spec_rel`,
`ContextEquivOn.outcomeTransfer_spec_rel`) across distinct `MirReturn` memories.
-/
theorem constructiveTotal_obsErasedRefines_ubException_and_indexed_cover_transfer :
    let stPre : List Value → Memory → Prop :=
      fun args mem => ∃ x, x + x < 4294967296 ∧ args = callerArgs (true, x) ∧ mem = linkedMemory
    let fullPre : List Value → Memory → Prop :=
      fun args mem => ∃ b x, x + x < 4294967296 ∧ args = callerArgs (b, x) ∧ mem = linkedMemory
    let stPost : List Value → Memory → Value → Memory → Prop :=
      fun args _ ret _ => ∃ b x, args = callerArgs (b, x) ∧ ret = .scalar ⟨x + x, 4⟩
    let borrowGapSem : CapturedMir → GapSem (Bool × Nat) ExecFault (GapTag DefPath) MirReturn :=
      fun b q => mirStatefulGapBehaviors MirCallEnv.unresolved linkedHelpers b
        (callerArgs q, linkedMemory)
    let valSpec₂ : (valLanguage borrowGapSem).Behavior :=
      Language.ContractSpec (valLanguage borrowGapSem)
        (fun q => q.1 = true) (fun q => q.2 + q.2 < 4294967296)
        (fun q r => r.1 = Value.scalar ⟨q.2 + q.2, 4⟩)
    let gapSpec₂ : (gapLanguage ExecFault.isUB borrowGapSem).Behavior :=
      Language.ContractSpec (gapLanguage ExecFault.isUB borrowGapSem)
        (fun q => q.1 = true) (fun q => q.2 + q.2 < 4294967296)
        (fun q o => ∃ m, o = .ok (Value.scalar ⟨q.2 + q.2, 4⟩, m))
    let outSpec₂ : (outcomeLanguage borrowGapSem).Behavior :=
      Language.ContractSpec (outcomeLanguage borrowGapSem)
        (fun q => q.1 = true) (fun q => q.2 + q.2 < 4294967296)
        (fun q out => ∃ m, out = .normal (Value.scalar ⟨q.2 + q.2, 4⟩, m))
    MirConstructiveTotalHolds linkedHelpers callerBorrowRefactoredBody stPre stPost ∧
      Trusted.VerificationResult.RefinesStatefulMirWithCallees
        callerRefactoredBody linkedHelpers callerBranchingBody linkedHelpers fullPre ∧
      Trusted.VerificationResult.RefinesStatefulMirWithCallees
        branchlessDoubleCallerBody linkedHelpers callerBranchingBody linkedHelpers stPre ∧
      (∃ args mem, fullPre args mem ∧
        ¬ TreeSafe (Trusted.VerificationResult.mirStatefulTreeWithCallees
          callerBorrowRefactoredBody args mem linkedHelpers)) ∧
      Nonempty (Trusted.VerificationResult.UbExceptionVerificationResult
        { body := callerBorrowRefactoredBody, pre := fullPre, strictSafetyPre := stPre,
          post := stPost, callees := linkedHelpers }) ∧
      ContextEquiv (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
        (borrowGapSem callerBranchingBody) (borrowGapSem callerBorrowRefactoredBody) ∧
      ((valLanguage borrowGapSem).sem callerBorrowRefactoredBody ≤ valSpec₂) ∧
      ((gapLanguage ExecFault.isUB borrowGapSem).sem callerBorrowRefactoredBody ≤ gapSpec₂) ∧
      ((outcomeLanguage borrowGapSem).sem callerBorrowRefactoredBody ≤ outSpec₂) := by
  dsimp only
  let stPre : List Value → Memory → Prop :=
    fun args mem => ∃ x, x + x < 4294967296 ∧ args = callerArgs (true, x) ∧ mem = linkedMemory
  let fullPre : List Value → Memory → Prop :=
    fun args mem => ∃ b x, x + x < 4294967296 ∧ args = callerArgs (b, x) ∧ mem = linkedMemory
  let stPost : List Value → Memory → Value → Memory → Prop :=
    fun args _ ret _ => ∃ b x, args = callerArgs (b, x) ∧ ret = .scalar ⟨x + x, 4⟩
  let borrowGapSem : CapturedMir → GapSem (Bool × Nat) ExecFault (GapTag DefPath) MirReturn :=
    fun b q => mirStatefulGapBehaviors MirCallEnv.unresolved linkedHelpers b
      (callerArgs q, linkedMemory)
  -- Pairwise `OutcomeSetEquiv` on all `(b, x)` (shared `.unsupported` gap on `false`,
  -- equal return scalar across distinct borrow memories on `true`)
  have hPairEquiv : ∀ q : Bool × Nat,
      OutcomeSetEquiv (GapEqErr (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·))
        (borrowGapSem callerBranchingBody q) (borrowGapSem callerBorrowRefactoredBody q) := by
    rintro ⟨flag, x⟩
    dsimp only [borrowGapSem, mirStatefulGapBehaviors]
    cases flag with
    | true =>
      let st₁ := mirSiteOfExec callerBranchingBody (.running
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          callerBranchingBody (callerArgs (true, x)) linkedMemory linkedHelpers))
      let st₂ := mirSiteOfExec callerBorrowRefactoredBody (.running
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          callerBorrowRefactoredBody (callerArgs (true, x)) linkedMemory linkedHelpers))
      have h₁ : runGapSteps (mirSiteGapStep MirCallEnv.unresolved callerBranchingBody) 3 st₁ =
          .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, linkedMemory) := rfl
      have hm₂ : (runGapSteps (mirSiteGapStep MirCallEnv.unresolved callerBorrowRefactoredBody) 5
          st₂).map Prod.fst =
          .ok (.scalar ⟨wrapScalarBits (x * 2) (scalarModulus 4), 4⟩) := rfl
      have hne₁ := ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀)
      have hne₂ : runGapSteps (mirSiteGapStep MirCallEnv.unresolved callerBorrowRefactoredBody) 5
          st₂ ≠ .gap .outOfFuel := by
        intro h₀; rw [h₀] at hm₂; cases hm₂
      refine (gapBehaviors_equiv_iff_of_runs hne₁ hne₂).mpr ?_
      rw [h₁]
      cases ho₂ : runGapSteps (mirSiteGapStep MirCallEnv.unresolved callerBorrowRefactoredBody) 5
          st₂ with
      | ok r₂ =>
        rw [ho₂] at hm₂
        change Value.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩ = r₂.1
        rw [OutcomeWithGap.ok.inj hm₂, Nat.mul_two]
      | fault _ => rw [ho₂] at hm₂; cases hm₂
      | gap _ => rw [ho₂] at hm₂; cases hm₂
    | false =>
      let st₁ := mirSiteOfExec callerBranchingBody (.running
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          callerBranchingBody (callerArgs (false, x)) linkedMemory linkedHelpers))
      let st₂ := mirSiteOfExec callerBorrowRefactoredBody (.running
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          callerBorrowRefactoredBody (callerArgs (false, x)) linkedMemory linkedHelpers))
      have h₁ : runGapSteps (mirSiteGapStep MirCallEnv.unresolved callerBranchingBody) 3 st₁ =
          .gap (.unsupported "test::unmodeled_helper") := rfl
      have h₂ : runGapSteps (mirSiteGapStep MirCallEnv.unresolved callerBorrowRefactoredBody) 3 st₂ =
          .gap (.unsupported "test::unmodeled_helper") := rfl
      refine gapBehaviors_equiv_of_runs (fuel₂ := 3)
        (ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀)) ?_
      rw [h₁, h₂]
      exact (rfl : GapTag.unsupported "test::unmodeled_helper" = _)
  -- Constructive 3-way `Fin 3` indexed-cover patching (`ContextEquiv.of_iSup_cover`)
  have hIndexedCover : ContextEquiv (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
      (borrowGapSem callerBranchingBody) (borrowGapSem callerBorrowRefactoredBody) :=
    ContextEquiv.of_iSup_cover (ι := Fin 3)
      (P := fun i q => q.2 % 3 = i.1)
      (fun q => ⟨⟨q.2 % 3, Nat.mod_lt q.2 (by decide)⟩, rfl⟩)
      (fun _ q _ => hPairEquiv q)
  have hClosedFull : ∀ args mem, fullPre args mem → ∀ site,
      ¬ mirStatefulGapBehaviors MirCallEnv.unresolved linkedHelpers callerBranchingBody
          (args, mem) (.gap (.unresolved site)) := by
    rintro _ _ ⟨b, x, _, rfl, rfl⟩ site hm
    dsimp only [mirStatefulGapBehaviors] at hm
    cases b with
    | true =>
      let st₁ := mirSiteOfExec callerBranchingBody (.running
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          callerBranchingBody (callerArgs (true, x)) linkedMemory linkedHelpers))
      have h₁ : runGapSteps (mirSiteGapStep MirCallEnv.unresolved callerBranchingBody) 3 st₁ =
          .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, linkedMemory) := rfl
      have heq := (gapBehaviors_iff_of_run _ (ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀))
        (.gap (.unresolved site))).mp hm
      rw [h₁] at heq; cases heq
    | false =>
      let st₁ := mirSiteOfExec callerBranchingBody (.running
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          callerBranchingBody (callerArgs (false, x)) linkedMemory linkedHelpers))
      have h₁ : runGapSteps (mirSiteGapStep MirCallEnv.unresolved callerBranchingBody) 3 st₁ =
          .gap (.unsupported "test::unmodeled_helper") := rfl
      have heq := (gapBehaviors_iff_of_run _ (ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀))
        (.gap (.unresolved site))).mp hm
      rw [h₁] at heq; cases heq
  -- 1. Constructive `MirConstructiveTotalHolds` (`0` `Classical.choice`) & `RefinesStatefulMirWithCallees`
  have totalBase : MirConstructiveTotalHolds linkedHelpers callerBranchingBody stPre stPost := by
    rintro _ _ ⟨x, hx, rfl, rfl⟩
    have hrun : runMirWithGap MirCallEnv.unresolved linkedHelpers callerBranchingBody 3
        (callerArgs (true, x)) =
        classifyOutcome (.normal (.scalar ⟨x + x, 4⟩, linkedMemory)) := by
      change runMirWithGap MirCallEnv.unresolved linkedHelpers callerBranchingBody 3
          (callerArgs (true, x)) =
        .ok (.scalar ⟨x + x, 4⟩, linkedMemory)
      have h₀ : runMirWithGap MirCallEnv.unresolved linkedHelpers callerBranchingBody 3
          (callerArgs (true, x)) =
          .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, linkedMemory) := rfl
      rw [h₀, wrapScalarBits_of_lt (show x + x < scalarModulus 4 from hx)]
    obtain ⟨hsafe, hex, huniq⟩ := mirTree_adequate_of_defined hrun
    obtain ⟨tr₀, hrr₀⟩ := hex
    have hTerm : OutcomeSet.Terminates
        (mirStatefulGapBehaviors MirCallEnv.unresolved linkedHelpers callerBranchingBody
          (callerArgs (true, x), linkedMemory)) :=
      ⟨_, ⟨(fun h₀ => by cases h₀), 3, hrun⟩⟩
    have hProd := mirTree_productive_of_terminates_closed
      (hClosedFull _ _ ⟨true, x, hx, rfl, rfl⟩) hTerm
    refine ⟨hsafe, hProd, ⟨tr₀, _, hrr₀⟩, fun tr out hrr => ?_⟩
    have heq := huniq tr out hrr
    subst heq
    exact ⟨_, _, rfl, ⟨true, x, rfl, rfl⟩⟩
  have totalTransferred := mirConstructiveTotalHolds_of_contextEquiv
    (body₂ := callerBorrowRefactoredBody) (rVal := fun r₁ r₂ : MirReturn => r₁.1 = r₂.1)
    (by rintro ⟨_, _⟩ ⟨x, _, rfl, rfl⟩; exact hIndexedCover (true, x))
    (fun _ _ v₁ _ v₂ _ _ hrv hp => by
      obtain ⟨b, x, hargs, hv₁⟩ := hp
      exact ⟨b, x, hargs, hrv.symm.trans hv₁⟩)
    (fun args mem hq => by
      obtain ⟨x, hx, hargs, hmem⟩ := hq
      exact hClosedFull args mem ⟨true, x, hx, hargs, hmem⟩)
    totalBase
  have hRefinesGapping : Trusted.VerificationResult.RefinesStatefulMirWithCallees
      callerRefactoredBody linkedHelpers callerBranchingBody linkedHelpers fullPre :=
    (refinesStatefulMirWithCallees_of_contextEquiv
      (by
        rintro ⟨_, _⟩ ⟨b, x, _, rfl, rfl⟩
        exact callerRefactored_contextEquiv (b, x))
      hClosedFull).1
  have hRefinesBranchless : Trusted.VerificationResult.RefinesStatefulMirWithCallees
      branchlessDoubleCallerBody linkedHelpers callerBranchingBody linkedHelpers stPre :=
    (refinesStatefulMirWithCallees_of_contextEquiv
      (by
        rintro ⟨_, _⟩ ⟨x, _, rfl, rfl⟩
        let stB := mirSiteOfExec callerBranchingBody (.running
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            callerBranchingBody (callerArgs (true, x)) linkedMemory linkedHelpers))
        let stL := mirSiteOfExec branchlessDoubleCallerBody (.running
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            branchlessDoubleCallerBody (callerArgs (true, x)) linkedMemory linkedHelpers))
        have h₁ : runGapSteps (mirSiteGapStep MirCallEnv.unresolved callerBranchingBody) 3 stB =
            .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, linkedMemory) := rfl
        have h₂ : runGapSteps (mirSiteGapStep MirCallEnv.unresolved branchlessDoubleCallerBody) 2 stL =
            .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, linkedMemory) := rfl
        refine gapBehaviors_equiv_of_runs (fuel₂ := 2)
          (ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀)) ?_
        rw [h₁, h₂]
        exact GapEqErr.refl (fun _ => rfl) (fun _ => rfl) _)
      (fun args mem hq => by
        obtain ⟨x, hx, hargs, hmem⟩ := hq
        exact hClosedFull args mem ⟨true, x, hx, hargs, hmem⟩)).1
  -- 2. Base & transferred `UbExceptionVerificationResult` (plus non-`TreeSafe` witness in `fullPre`)
  have hFalseNotSafe : ∃ args mem, fullPre args mem ∧
      ¬ TreeSafe (Trusted.VerificationResult.mirStatefulTreeWithCallees
        callerBorrowRefactoredBody args mem linkedHelpers) := by
    refine ⟨callerArgs (false, 0), linkedMemory, ⟨false, 0, by decide, rfl, rfl⟩, fun hs => ?_⟩
    let st₀ := mirSiteOfExec callerBorrowRefactoredBody (.running
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        callerBorrowRefactoredBody (callerArgs (false, 0)) linkedMemory linkedHelpers))
    have hrun : runStepsWithGap (stepMirSiteState callerBorrowRefactoredBody)
        (mirSiteOfState callerBorrowRefactoredBody) (mirGapHandle MirCallEnv.unresolved) 3 st₀ =
        .gap (.unsupported "test::unmodeled_helper") := rfl
    have hns := not_treeSafe_of_runStepsWithGap mirHandled_not_fault hrun
      (fun h => by cases h) (fun h => h)
      (fun i _ hi => by cases i with | inl o => cases o; cases hi | inr c => cases c; cases hi)
      (fun i _ hi => by
        cases i with
        | inl o => cases o; cases hi
        | inr c =>
          cases c
          injection hi with hg
          intro h
          subst hg
          cases h)
    rw [cofix_stepMirSiteState_eq_mirTree] at hns
    exact hns hs
  have ubExBase : Trusted.VerificationResult.UbExceptionVerificationResult
      { body := callerBranchingBody, pre := fullPre, strictSafetyPre := stPre,
        post := stPost, callees := linkedHelpers } :=
    { proof := by
        refine ⟨?_, ?_⟩
        · rintro _ _ ⟨_, ⟨x, hx, rfl, rfl⟩⟩
          obtain ⟨hs, _, _, hret⟩ := totalBase _ _ ⟨x, hx, rfl, rfl⟩
          refine ⟨hs, fun outPair hrr _ retVal mem' hout => ?_⟩
          rcases outPair with ⟨tr, out⟩
          dsimp only at hout; subst hout
          obtain ⟨rv, mm, heq, hpost⟩ := hret tr (.normal (retVal, mem')) hrr
          injection heq with hp; injection hp with hrv _
          subst hrv
          exact hpost
        · rintro _ _ ⟨b, x, hx, rfl, rfl⟩ tr retVal mem' hrr
          have hm := (mirReachesRet_iff_of_closed
            (hClosedFull _ _ ⟨b, x, hx, rfl, rfl⟩) (.normal (retVal, mem'))).mp ⟨tr, hrr⟩
          dsimp only [mirStatefulGapBehaviors] at hm
          cases b with
          | true =>
            let st₁ := mirSiteOfExec callerBranchingBody (.running
              (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
                callerBranchingBody (callerArgs (true, x)) linkedMemory linkedHelpers))
            have h₁ : runGapSteps (mirSiteGapStep MirCallEnv.unresolved callerBranchingBody) 3 st₁ =
                .ok (.scalar ⟨x + x, 4⟩, linkedMemory) := by
              have h₀ : runGapSteps (mirSiteGapStep MirCallEnv.unresolved callerBranchingBody) 3 st₁ =
                  .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, linkedMemory) := rfl
              rw [h₀, wrapScalarBits_of_lt (show x + x < scalarModulus 4 from hx)]
            have heq := (gapBehaviors_iff_of_run _ (ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀))
              (.ok (retVal, mem'))).mp hm
            rw [h₁] at heq
            exact ⟨true, x, rfl, congrArg Prod.fst (OutcomeWithGap.ok.inj heq)⟩
          | false =>
            let st₁ := mirSiteOfExec callerBranchingBody (.running
              (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
                callerBranchingBody (callerArgs (false, x)) linkedMemory linkedHelpers))
            have h₁ : runGapSteps (mirSiteGapStep MirCallEnv.unresolved callerBranchingBody) 3 st₁ =
                .gap (.unsupported "test::unmodeled_helper") := rfl
            have heq := (gapBehaviors_iff_of_run _ (ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀))
              (.ok (retVal, mem'))).mp hm
            rw [h₁] at heq; cases heq }
  have ubExTransferred := UbExceptionVerificationResult.of_contextEquiv
    (body₂ := callerBorrowRefactoredBody) (rVal := fun r₁ r₂ : MirReturn => r₁.1 = r₂.1)
    (by rintro ⟨_, _⟩ ⟨b, x, _, rfl, rfl⟩; exact hIndexedCover (b, x))
    (fun _ _ v₁ _ v₂ _ _ hrv hp => by
      obtain ⟨b, x, hargs, hv₁⟩ := hp
      exact ⟨b, x, hargs, hrv.symm.trans hv₁⟩)
    hClosedFull ubExBase
  -- 3. Relational `valTransfer_spec_rel`, `transfer_spec_rel`, `outcomeTransfer_spec_rel`
  have hOnTrue : ContextEquivOn (fun q : Bool × Nat => q.1 = true)
      (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
      (borrowGapSem callerBranchingBody) (borrowGapSem callerBorrowRefactoredBody) :=
    fun q _ => hIndexedCover q
  have hValSpec₁ : (valLanguage borrowGapSem).sem callerBranchingBody ≤
      Language.ContractSpec (valLanguage borrowGapSem)
        (fun q => q.1 = true) (fun q => q.2 + q.2 < 4294967296)
        (fun q r => r.1 = Value.scalar ⟨q.2 + q.2, 4⟩) := by
    rintro ⟨flag, x⟩ (rfl : flag = true)
    dsimp only [valLanguage, Language.ContractSpec, borrowGapSem, mirStatefulGapBehaviors,
      OutcomeSet.toValPartial]
    let st₃ := mirSiteOfExec callerBranchingBody (.running
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        callerBranchingBody (callerArgs (true, x)) linkedMemory linkedHelpers))
    have h₁ : runGapSteps (mirSiteGapStep MirCallEnv.unresolved callerBranchingBody) 3 st₃ =
        .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, linkedMemory) := rfl
    have hne := ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀)
    refine ⟨fun o ho => ?_, fun r hr hx => ?_⟩
    · rw [(gapBehaviors_iff_of_run _ hne o).mp ho, h₁]; exact ⟨_, rfl⟩
    · have heq := (gapBehaviors_iff_of_run _ hne (.ok r)).mp hr
      rw [h₁, wrapScalarBits_of_lt (show x + x < scalarModulus 4 from hx)] at heq
      exact congrArg Prod.fst (OutcomeWithGap.ok.inj heq)
  have hValTrans := hOnTrue.valTransfer_spec_rel
    (fun _ hs => ⟨hs, hs⟩)
    (fun _ _ _ _ _ ⟨_, hv₁, hrv⟩ hx => hrv.symm.trans (hv₁ hx))
    hValSpec₁
  have hGapSpec₁ : (gapLanguage ExecFault.isUB borrowGapSem).sem callerBranchingBody ≤
      Language.ContractSpec (gapLanguage ExecFault.isUB borrowGapSem)
        (fun q => q.1 = true) (fun q => q.2 + q.2 < 4294967296)
        (fun q o => ∃ m, o = .ok (Value.scalar ⟨q.2 + q.2, 4⟩, m)) := by
    rintro ⟨flag, x⟩ (rfl : flag = true)
    dsimp only [gapLanguage, Language.ContractSpec, borrowGapSem, mirStatefulGapBehaviors]
    let st₃ := mirSiteOfExec callerBranchingBody (.running
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        callerBranchingBody (callerArgs (true, x)) linkedMemory linkedHelpers))
    have h₁ : runGapSteps (mirSiteGapStep MirCallEnv.unresolved callerBranchingBody) 3 st₃ =
        .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, linkedMemory) := rfl
    have hne := ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀)
    have hDef : OutcomeSet.Defined ExecFault.isUB
        (gapBehaviors (mirSiteGapStep MirCallEnv.unresolved callerBranchingBody) st₃) :=
      defined_gapBehaviors_of_run (fuel := 3) (by rw [h₁]; exact trivial)
    refine ⟨hDef, fun o ho hx => ?_⟩
    have heq := (gapBehaviors_iff_of_run _ hne o).mp ho
    rw [h₁, wrapScalarBits_of_lt (show x + x < scalarModulus 4 from hx)] at heq
    exact ⟨linkedMemory, heq⟩
  have hGapTrans := hOnTrue.transfer_spec_rel (fun _ _ hr hu => hr ▸ hu)
    (fun _ hs => ⟨hs, hs⟩)
    (fun _ _ _ _ o₂ ⟨o₁, ho₁, hr⟩ hx => by
      obtain ⟨m₁, rfl⟩ := ho₁ hx
      obtain ⟨⟨v₂, m₂⟩, rfl, hrv⟩ := GapEqErr.ok_iff.mp hr
      exact ⟨m₂, congrArg (fun v => OutcomeWithGap.ok (v, m₂)) hrv.symm⟩)
    hGapSpec₁
  have hOutSpec₁ : (outcomeLanguage borrowGapSem).sem callerBranchingBody ≤
      Language.ContractSpec (outcomeLanguage borrowGapSem)
        (fun q => q.1 = true) (fun q => q.2 + q.2 < 4294967296)
        (fun q out => ∃ m, out = .normal (Value.scalar ⟨q.2 + q.2, 4⟩, m)) := by
    rintro ⟨flag, x⟩ (rfl : flag = true)
    dsimp only [outcomeLanguage, Language.ContractSpec, borrowGapSem, mirStatefulGapBehaviors,
      OutcomeSet.toOutcomePartial]
    let st₃ := mirSiteOfExec callerBranchingBody (.running
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        callerBranchingBody (callerArgs (true, x)) linkedMemory linkedHelpers))
    have h₁ : runGapSteps (mirSiteGapStep MirCallEnv.unresolved callerBranchingBody) 3 st₃ =
        .ok (.scalar ⟨wrapScalarBits (x + x) (scalarModulus 4), 4⟩, linkedMemory) := rfl
    have hne := ne_outOfFuel_of_eq h₁ (fun h₀ => by cases h₀)
    have hDef : OutcomeSet.Defined ExecFault.isUB
        (gapBehaviors (mirSiteGapStep MirCallEnv.unresolved callerBranchingBody) st₃) :=
      defined_gapBehaviors_of_run (fuel := 3) (by rw [h₁]; exact trivial)
    refine ⟨hDef, fun (out : MirOutcome) hout hx => ?_⟩
    have heq := (gapBehaviors_iff_of_run _ hne (classifyOutcome out)).mp hout
    rw [h₁, wrapScalarBits_of_lt (show x + x < scalarModulus 4 from hx)] at heq
    cases out with
    | normal r => exact ⟨linkedMemory, congrArg Outcome.normal (OutcomeWithGap.ok.inj heq)⟩
    | panic => cases heq
    | abort => cases heq
  have hOutTrans := ContextEquivOn.outcomeTransfer_spec_rel hOnTrue
    (fun _ hs => ⟨hs, hs⟩)
    (fun _ _ _ _ out₂ ⟨out₁, hout₁, hr⟩ hx => by
      obtain ⟨m₁, rfl⟩ := hout₁ hx
      cases out₂ with
      | normal r₂ => exact ⟨r₂.2, congrArg Outcome.normal (Prod.ext hr.symm rfl)⟩
      | panic => cases hr
      | abort => cases hr)
    hOutSpec₁
  exact ⟨totalTransferred, hRefinesGapping, hRefinesBranchless,
    hFalseNotSafe, ⟨ubExTransferred⟩,
    hIndexedCover, hValTrans, hGapTrans, hOutTrans⟩

end CallContractCanaries

end GapPreservingCanaries

end Anneal.FunctionalTranslationEquivTests
