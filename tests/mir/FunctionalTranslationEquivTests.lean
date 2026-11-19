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
  ⟨not_mirNoUBTree_of_run_undefined (callerBranching_run_false x) (Or.inr ⟨_, rfl⟩),
   not_mirNoUBTree_of_run_undefined (callerRefactored_run_false x) (Or.inr ⟨_, rfl⟩)⟩


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
the environment's answer with the rest of the run, for every environment.
-/
theorem tailCaller_run_false (env : MirCallEnv) (x fuel : Nat) :
    runMirWithGap env [] tailCallerBody (fuel + 2) (callerArgs (false, x)) =
      (env (extHelperReq x)).bind (fun ans =>
        runMirStepsWithGap env tailCallerBody fuel (resumeExternalTailCall ans)) :=
  (runGapSteps_succ_of_next (mirGapStep env tailCallerBody)
      (s := .running (initMachineStateWithCallees tailCallerBody
        (callerArgs (false, x)) []))
      (s' := .running (tailCallerAtCall tailCallerBody x)) rfl (fuel + 1)).trans
    (runStepsWithGap_of_vis (step := stepMirState tailCallerBody)
      (site := mirGapSite tailCallerBody) (handle := mirGapHandle env)
      (s := .running (tailCallerAtCall tailCallerBody x))
      (i := .inr (.call (extHelperReq x))) (k := resumeExternalTailCall) rfl fuel)

/-- Call-handler law on the refactored caller: the same request and `bind`. -/
theorem tailCallerRefactored_run_false (env : MirCallEnv) (x fuel : Nat) :
    runMirWithGap env [] tailCallerRefactoredBody (fuel + 2) (callerArgs (false, x)) =
      (env (extHelperReq x)).bind (fun ans =>
        runMirStepsWithGap env tailCallerRefactoredBody fuel
          (resumeExternalTailCall ans)) :=
  (runGapSteps_succ_of_next (mirGapStep env tailCallerRefactoredBody)
      (s := .running (initMachineStateWithCallees tailCallerRefactoredBody
        (callerArgs (false, x)) []))
      (s' := .running (tailCallerAtCall tailCallerRefactoredBody x)) rfl
      (fuel + 1)).trans
    (runStepsWithGap_of_vis (step := stepMirState tailCallerRefactoredBody)
      (site := mirGapSite tailCallerRefactoredBody) (handle := mirGapHandle env)
      (s := .running (tailCallerAtCall tailCallerRefactoredBody x))
      (i := .inr (.call (extHelperReq x))) (k := resumeExternalTailCall) rfl fuel)

/--
For **every** helper summary `f` (returning, faulting, or hitting any gap), the
baseline's `flag = false` run is `f`'s outcome on the helper request.
-/
theorem tailCaller_run_false_pure
    (f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value)
    (x : Nat) :
    tailRun f tailCallerBody 3 (false, x) =
      (f "test::ext_helper" [.scalar ⟨x, 4⟩]).map (fun v => (v, unlinkedMemory)) := by
  show runMirWithGap (MirCallEnv.ofPure f) [] tailCallerBody (1 + 2)
    (callerArgs (false, x)) = _
  rw [tailCaller_run_false]
  show ((f "test::ext_helper" [.scalar ⟨x, 4⟩]).map
    (fun v => MirCallAns.returned v unlinkedMemory)).bind _ = _
  cases f "test::ext_helper" [.scalar ⟨x, 4⟩] <;> rfl

theorem tailCallerRefactored_run_false_pure
    (f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value)
    (x : Nat) :
    tailRun f tailCallerRefactoredBody 3 (false, x) =
      (f "test::ext_helper" [.scalar ⟨x, 4⟩]).map (fun v => (v, unlinkedMemory)) := by
  show runMirWithGap (MirCallEnv.ofPure f) [] tailCallerRefactoredBody (1 + 2)
    (callerArgs (false, x)) = _
  rw [tailCallerRefactored_run_false]
  show ((f "test::ext_helper" [.scalar ⟨x, 4⟩]).map
    (fun v => MirCallAns.returned v unlinkedMemory)).bind _ = _
  cases f "test::ext_helper" [.scalar ⟨x, 4⟩] <;> rfl

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

end GapPreservingCanaries

end Anneal.FunctionalTranslationEquivTests
