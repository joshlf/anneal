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

end GapPreservingCanaries

end Anneal.FunctionalTranslationEquivTests
