-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.ParametricCore.ByteRun
import Anneal.ParametricCore.OverflowCastJoin
import Anneal.ParametricCore.CallStackUnwind
import Anneal.ParametricCore.V2026Bridge
import Anneal.PureLift.SpatialMemV2026
import Anneal.RefFrame.RangedTree

/-!
# Episode 2 `StageCut` / `ByteRun` / `OverflowCastJoin` / `CallStackUnwind` ↔ `V2026_06_01` Bridge

Instantiates Episode 1's zero-TCB parametric core (`ByteRun`, `OverflowCastJoin`,
`CallStackUnwind`, `Anneal.RefFrame.RangedTree`) directly on unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics`, `Anneal.MirFuelFree`,
`Anneal.PureMirExec`, `Anneal.SepLogicLenses`, `Anneal.ParametricCore.V2026Bridge`,
and `Anneal.PureLift.SpatialMemV2026` with **zero shadow operational semantics**:

1. **`ByteRun` ↔ `V2026_06_01` (`Section 1`):**
   - `abstractByteRunCodec : ByteRunCodec (Nat × Nat) AbstractByte` (bijection),
   - `v2026ByteMemByteStoreOps` + `LawfulByteStoreOps` on `V2026ByteMem`, alongside
     existing `byteMemByteStoreOps` (`SepLogicLenses.ByteMem`), `memGlobalsByteStoreOps`
     (`Memory.globals`, `ByteRunCodec.optionUInt8`), and `memCallerByteStoreOps`
     (`Memory.callerLocals`, `PlainByteRunCodec.uint8`),
   - Padded `(u8, [pad; 3], u32)` `copyRangeComp` preservation & `decodeValueFromBytes`
     recovery, `[T; N]` `copyRepeatedlyComp` / `Rvalue.repeat` alignment,
     `ByteRunCopyCut` → `MirWpConverges` transport, and fail-closed immutable/relocated/OOB
     negative theorems.
2. **`OverflowCastJoin` ↔ `V2026_06_01` (`Section 2`):**
   - Exact equational agreement of `ScalarWidth`, `intToIntCast`, `{add,sub,mul}WithOverflowU`,
     `{add,sub,mul,shl}UncheckedU`, and `addWithOverflowS` against unmodified
     `V2026_06_01.MirSemantics.{scalarModulus, wrapScalarBits, signExtendBits, evalScalarBinOp}`,
   - Lawful `OvfCastFrameOps MachineState Value` (`v2026ValOvfCastFrameOps`) and
     `OvfCastFrameOps MachineState LocalSlot` (`v2026SlotOvfCastFrameOps`) plus `.signedView`,
   - Direct `OvfCastStageCut` → `MirStepsConverges` / `MirWpConverges` transport over
     `mirDetStep` / `mirDetWpOps` and `BlockTree` / `Chunk8BlockTree`.
3. **`CallStackUnwind` & `RefFrame` ↔ `V2026_06_01` (`Section 3`):**
   - Exact bijections `UnwindAction ↔ UnwindAction4` and
     `TreeBorrowPerm ↔ Anneal.RefFrame.TbPermission` plus full 56-case transition-table
     agreement with unmodified `treeBorrowPermTransition` and `treeBorrowNodeAccess`,
   - `CallCont4` extraction from `TerminatorKind.call` / `SavedCallerFrame`,
   - Direct `applyUnwindAction` / `unwindFromCallStack` correspondence, fail-closed
     `V2026_06_01` UB theorems (`stepMirFn_return_diverging_ub`,
     `stepMirFn_assert_unreachable_ub`, `not_mirWpConverges_of_step_fail`), and
     `CallSpecCut` → `MirWpConverges` transport.
-/

namespace Anneal.ParametricCore.StageCutV2026Bridge

open Trusted.Effect
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Anneal.SepLogicLenses
open Anneal.ParametricCore
open Anneal.ParametricCore.V2026Bridge
open Anneal.PureLift.SpatialMemV2026
open Anneal.PureLift.V2026_06_01Bridge
open Anneal.RefFrame

/-! ## General Fail-Closed `MirWpConverges` Helper -/

/-- Any machine state whose unmodified `stepMirFn` fails (`MirStepNode.fail fk`)
cannot converge under `MirFuelFree.MirWpConverges`. -/
theorem not_mirWpConverges_of_step_fail {body : CapturedMir} {s : MachineState}
    {fk : FailureKind} {post : MirOutcome → Prop}
    (hStep : stepMirFn body s = MirStepNode.fail fk) :
    ¬ MirWpConverges body s post := by
  rintro ⟨fuel, hWp⟩
  cases fuel with
  | zero => exact hWp
  | succ _ =>
    unfold Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirSym
      Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym at hWp
    rw [Anneal.Rustc.V2026_06_01.SymbolicEval.evalSymNodeTree_eq,
      Anneal.Rustc.V2026_06_01.SymbolicEval.stepMirExecSymTree_eval,
      Anneal.Rustc.V2026_06_01.SymbolicEval.evalNodeWP_eq] at hWp
    dsimp only [stepMirState] at hWp
    rw [hStep] at hWp
    exact hWp

/-- **Silent-step inversion for `MirWpConverges`**: if `stepMirFn body s` takes a
silent `.tau (.running s')` step, convergence from `s` forces convergence from
`s'`. Lets fail-closed canaries walk a REAL multi-step `CapturedMir` execution
(e.g. a caller's inline `TerminatorKind.call`) up to a `MirStepNode.fail` node. -/
theorem mirWpConverges_of_step_tau_inv {body : CapturedMir} {s s' : MachineState}
    {post : MirOutcome → Prop}
    (hStep : stepMirFn body s = .tau (.running s'))
    (h : MirWpConverges body s post) : MirWpConverges body s' post := by
  rcases h with ⟨fuel, hWp⟩
  cases fuel with
  | zero => exact False.elim hWp
  | succ f =>
    refine ⟨f, ?_⟩
    unfold Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirSym
      Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym at hWp
    rw [Anneal.Rustc.V2026_06_01.SymbolicEval.evalSymNodeTree_eq,
      Anneal.Rustc.V2026_06_01.SymbolicEval.stepMirExecSymTree_eval,
      Anneal.Rustc.V2026_06_01.SymbolicEval.evalNodeWP_eq] at hWp
    dsimp only [stepMirState] at hWp
    rw [hStep] at hWp
    exact hWp

/-- A silent `.tau` step into a state that cannot converge cannot converge. -/
theorem not_mirWpConverges_of_step_tau {body : CapturedMir} {s s' : MachineState}
    {post : MirOutcome → Prop}
    (hStep : stepMirFn body s = .tau (.running s'))
    (hNext : ¬ MirWpConverges body s' post) :
    ¬ MirWpConverges body s post :=
  fun h => hNext (mirWpConverges_of_step_tau_inv hStep h)

/-- Compose a `wpUntilOk` derivation over any `MirWpOps.ofDetStep (mirDetStep body) tag`
directly with a `MirFuelFree.MirWpConverges` continuation at the stopping cutpoint. -/
theorem mirWpConverges_of_wpUntilOk_det {body : CapturedMir} {tag : MachineState → Option Nat}
    {ms : MachineState} {stop : MachineState → Prop} {post : MirOutcome → Prop}
    (h : wpUntilOk (ops := MirWpOps.ofDetStep (mirDetStep body) tag) stop post ms)
    (hCont : ∀ ms', stop ms' → MirWpConverges body ms' post) :
    MirWpConverges body ms post :=
  wpUntil_det_induction
    (C := fun s => MirWpConverges body s post)
    hCont
    (fun _ _ hStep ih =>
      Anneal.PureMirExec.mirWpConverges_of_mirStep_cont
        (mirDetStep_step_iff.mp hStep) ih)
    (fun _ _ hDone hPost =>
      MirWpConverges.ret_of_step
        (Anneal.PureMirExec.stepMirFn_of_mirStep_done (mirDetStep_done_iff.mp hDone))
        hPost)
    (fun _ _ _ hF => False.elim hF) h

/-- Compose a `wpUntilOk` derivation over `mirDetWpOps body` directly with a
`MirFuelFree.MirWpConverges` continuation at the stopping cutpoint. -/
theorem mirWpConverges_of_wpUntilOk_cont {body : CapturedMir} {ms : MachineState}
    {stop : MachineState → Prop} {post : MirOutcome → Prop}
    (h : wpUntilOk (ops := mirDetWpOps body) stop post ms)
    (hCont : ∀ ms', stop ms' → MirWpConverges body ms' post) :
    MirWpConverges body ms post :=
  mirWpConverges_of_wpUntilOk_det h hCont

/-- Transport `wpUntilOk` over any `MirWpOps.ofDetStep (mirDetStep body) tag` directly
into `Anneal.MirFuelFree.MirStepsConverges`. -/
theorem mirStepsConverges_of_wpUntilOk_det {body : CapturedMir} {tag : MachineState → Option Nat}
    {ms : MachineState} {stop : MachineState → Prop} {post : MirOutcome → Prop}
    (h : wpUntilOk (ops := MirWpOps.ofDetStep (mirDetStep body) tag) stop post ms) :
    MirStepsConverges body ms stop post :=
  wpUntil_det_induction
    (C := fun s => MirStepsConverges body s stop post)
    (fun _ hStop => MirStepsConverges.refl hStop)
    (fun _ _ hStep ih =>
      Anneal.PureMirExec.mirStepsConverges_of_mirStep_cont
        (mirDetStep_step_iff.mp hStep) ih)
    (fun _ _ hDone hPost =>
      MirStepsConverges.ret_of_step
        (Anneal.PureMirExec.stepMirFn_of_mirStep_done (mirDetStep_done_iff.mp hDone))
        hPost)
    (fun _ _ _ hF => False.elim hF) h

/-! ## Section 1: `ByteRun` ↔ `V2026_06_01` Operational Bridge -/

/-- Exact bijection `ByteRunCodec (Nat × Nat) AbstractByte` mapping
`ByteRunAtom (Nat × Nat)` onto unmodified `V2026_06_01.MirSemantics.AbstractByte`,
preserving `.uninit`, plain `.init b none`, and provenance `.init b (some (aid, tag))`
verbatim. -/
def abstractByteRunCodec : ByteRunCodec (Nat × Nat) AbstractByte where
  encodeAtom
    | .uninitPad => .uninit
    | .initPlain b => .init b none
    | .initProv b p => .init b (some p)
  decodeAtom?
    | .uninit => some .uninitPad
    | .init b none => some (.initPlain b)
    | .init b (some p) => some (.initProv b p)
  decode_encode a := by
    cases a with
    | uninitPad => rfl
    | initPlain _ => rfl
    | initProv _ _ => rfl

/-- Right inverse of `abstractByteRunCodec`: every `AbstractByte` round-trips
through `decodeAtom?` and `encodeAtom`. -/
theorem abstractByteRunCodec_encode_decode (b : AbstractByte) :
    ∃ a : ByteRunAtom (Nat × Nat),
      abstractByteRunCodec.decodeAtom? b = some a ∧
      abstractByteRunCodec.encodeAtom a = b := by
  cases b with
  | uninit => exact ⟨.uninitPad, rfl, rfl⟩
  | init u p =>
    cases p with
    | none => exact ⟨.initPlain u, rfl, rfl⟩
    | some pr => exact ⟨.initProv u pr, rfl, rfl⟩

/-- `AllocView` of a `SpatialMemV2026.V2026ByteAlloc` (`AbstractByte` slots):
accessible iff the allocation is live (`a.live = true`) and mutable (`a.mutability = .mut`). -/
def v2026ByteAllocView : AllocView V2026ByteAlloc AbstractByte where
  allocId a := a.allocId
  bytes a := a.bytes
  setBytes a bs := { a with bytes := bs }
  writable a :=
    match a.mutability with
    | .mut => a.live
    | .not => false

/-- Lawfulness of `v2026ByteAllocView`. -/
theorem v2026ByteAllocView_lawful : v2026ByteAllocView.Lawful where
  allocId_setBytes _ _ := rfl
  bytes_setBytes _ _ := rfl
  writable_setBytes _ _ := rfl
  setBytes_bytes _ := rfl
  setBytes_setBytes _ _ _ := rfl

/-- Canonical `ByteStoreOps` instance over `SpatialMemV2026.V2026ByteMem`. -/
instance v2026ByteMemByteStoreOps :
    ByteStoreOps V2026ByteMem AllocId AbstractByte :=
  ByteStoreOps.ofTable v2026ByteAllocView
    (fun m => m.allocs) (fun m xs => { m with allocs := xs })

/-- Lawfulness of `v2026ByteMemByteStoreOps` via `LawfulByteStoreOps.ofTable`. -/
instance v2026ByteMemLawfulByteStoreOps :
    LawfulByteStoreOps V2026ByteMem AllocId AbstractByte :=
  LawfulByteStoreOps.ofTable v2026ByteAllocView_lawful
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl)

/-- Exact identification of `SpatialMemV2026.findV2026Alloc` with `tableFind`. -/
theorem findV2026Alloc_eq_tableFind (xs : List V2026ByteAlloc) (aid : AllocId) :
    findV2026Alloc aid xs = tableFind v2026ByteAllocView aid xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    unfold findV2026Alloc tableFind
    dsimp only [v2026ByteAllocView, List.foldr]
    cases hEq : Nat.beq a.allocId aid with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih

/-- On any live mutable allocation with `1 ≤ a.alignBytes`, `ByteSubLens.get`
on `V2026ByteMem` agrees with `SpatialMemV2026.readV2026Bytes` at byte alignment `1`. -/
theorem v2026ByteMem_get_eq_readV2026Bytes (m : V2026ByteMem)
    (L : ByteSubLens AllocId) (a : V2026ByteAlloc)
    (hFind : findV2026Alloc L.addr m.allocs = some a)
    (hLive : a.live = true) (hMut : a.mutability = .mut)
    (hAlPos : 1 ≤ a.alignBytes) (hLenPos : 0 < L.len) :
    L.get m = readV2026Bytes m ⟨L.addr, L.offset⟩ L.len 1 := by
  have hTF : tableFind v2026ByteAllocView L.addr m.allocs = some a := by
    rw [← findV2026Alloc_eq_tableFind]; exact hFind
  have hBlt : Nat.blt 0 L.len = true := Nat.blt_eq.mpr hLenPos
  unfold ByteSubLens.get readV2026Bytes
  change (match Nat.blt 0 L.len with
    | false => none
    | true => tableRead v2026ByteAllocView m.allocs L.addr L.offset L.len) = _
  rw [hBlt]
  unfold tableRead
  rw [hTF, hFind]
  dsimp only [v2026ByteAllocView]
  rw [hMut, hLive]
  have hAl1 : v2026Aligned a L.offset 1 = true := by
    unfold v2026Aligned
    simp only [Nat.ble_eq.mpr hAlPos, Nat.mod_one, Nat.beq_refl]
    rfl
  rw [hAl1]
  cases hIb : Nat.ble (L.offset + L.len) a.bytes.length with
  | true =>
    have hInB : v2026InBounds a L.offset L.len = true := by
      unfold v2026InBounds; exact hIb
    rw [hInB]
    rfl
  | false =>
    have hInB : v2026InBounds a L.offset L.len = false := by
      unfold v2026InBounds; exact hIb
    rw [hInB]
    rfl

/-- Canonical 3-run `ByteRun (Nat × Nat)` layout for a padded
`#[repr(C)] (u8, [pad; 3], u32)` struct:
1 plain byte (`aByte`), 3 uninitialized padding bytes, and 4 plain LE bytes (`bVal`). -/
def paddedU8U32ByteRuns (s : U8U32Struct) : List (ByteRun (Nat × Nat)) :=
  [ .initPlain [s.aByte]
  , .uninitPad 3
  , .initPlain (encodeU32LEBytes s.bVal.val) ]

/-- Flattening `paddedU8U32ByteRuns s` through `abstractByteRunCodec` equals
`paddedU8U32Encode s` verbatim (and therefore `encodeValueToBytes` on `(u8, [pad; 3], u32)`). -/
theorem flattenByteRuns_paddedU8U32_eq (s : U8U32Struct) :
    flattenByteRuns abstractByteRunCodec (paddedU8U32ByteRuns s) =
      paddedU8U32Encode s := by
  rfl

/-- Copying a padded `#[repr(C)] (u8, [pad; 3], u32)` slice via `copyRangeComp`
over ANY lawful `AbstractByte` store (`SepLogicLenses.ByteMem` or `V2026ByteMem`)
preserves the `.uninit` padding bytes `[1..4)` verbatim, decodes identically at
`dst` via unmodified `V2026_06_01.MirSemantics.decodeValueFromBytes`, and frames
every disjoint sibling sub-lens. -/
theorem copyRangeComp_paddedU8U32_preserves_decode {Mem Addr : Type}
    [ByteStoreOps Mem Addr AbstractByte] [LawfulByteStoreOps Mem Addr AbstractByte]
    {layouts : LayoutTable} {idx : Nat} {l : TypeLayout} {mem : List Nat}
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size.bytes = 8)
    (hFields : l.fields = .arbitrary [⟨0⟩, ⟨4⟩] mem)
    (src dst : ByteSubLens Addr) (m₀ m₁ : Mem) (s : U8U32Struct)
    (hSrc : src.get m₀ = some (paddedU8U32Encode s))
    (hCopy : copyRangeComp src dst m₀ = some m₁) :
    dst.get m₁ = some (paddedU8U32Encode s) ∧
    (∀ bs, dst.get m₁ = some bs →
      decodeValueFromBytes defaultCodecFuel layouts (u8U32Ty idx) bs =
        some (paddedU8U32ToMirVal s)) ∧
    (∀ other : ByteSubLens Addr, other.Disjoint Mem dst →
      other.get m₁ = other.get m₀) := by
  have hRaw := copyRangeComp_sound_raw hSrc hCopy
  refine ⟨hRaw.2.1, ?_, hRaw.2.2⟩
  intro bs hGet
  rw [hRaw.2.1] at hGet
  injection hGet with hEq
  subst hEq
  exact ((paddedU8U32MemCodec_lawful hLookup hSize hFields).encodeProps s).2.2.2.2.1

/-- Canonical 3-run `ByteRun (Nat × Nat)` layout for a provenance-carrying
`#[repr(C)] (u8, [pad; 7], *mut u8)` struct. -/
def provPtrByteRuns (aid tag : Nat) (s : ProvPtrStruct) : List (ByteRun (Nat × Nat)) :=
  [ .initPlain [s.tagByte]
  , .uninitPad 7
  , .initProv
      [ UInt8.ofNat s.ptrOffset.val
      , UInt8.ofNat (s.ptrOffset.val / 256)
      , UInt8.ofNat (s.ptrOffset.val / 65536)
      , UInt8.ofNat (s.ptrOffset.val / 16777216)
      , UInt8.ofNat (s.ptrOffset.val / 4294967296)
      , UInt8.ofNat (s.ptrOffset.val / 1099511627776)
      , UInt8.ofNat (s.ptrOffset.val / 281474976710656)
      , UInt8.ofNat (s.ptrOffset.val / 72057594037927936) ]
      (aid, tag) ]

/-- Copying a provenance-carrying `#[repr(C)] (u8, [pad; 7], *mut u8)` struct via
`copyRangeComp` preserves all 7 `.uninit` padding bytes and all 8 `(aid, aid)`
pointer provenance bytes verbatim, decodes identically via unmodified
`decodeValueFromBytes`, and frames every disjoint sibling sub-lens. -/
theorem copyRangeComp_provPtr_preserves_decode {Mem Addr : Type}
    [ByteStoreOps Mem Addr AbstractByte] [LawfulByteStoreOps Mem Addr AbstractByte]
    {layouts : LayoutTable} {idx : Nat} {l : TypeLayout} {mem : List Nat}
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size.bytes = 16)
    (hFields : l.fields = .arbitrary [⟨0⟩, ⟨8⟩] mem)
    (aid : AllocId) (src dst : ByteSubLens Addr) (m₀ m₁ : Mem) (s : ProvPtrStruct)
    (hSrc : src.get m₀ = some (provPtrEncode aid aid s))
    (hCopy : copyRangeComp src dst m₀ = some m₁) :
    dst.get m₁ = some (provPtrEncode aid aid s) ∧
    (∀ bs, dst.get m₁ = some bs →
      decodeValueFromBytes defaultCodecFuel layouts (provPtrMirTy idx) bs =
        some (provPtrToMirVal aid s)) ∧
    (∀ other : ByteSubLens Addr, other.Disjoint Mem dst →
      other.get m₁ = other.get m₀) := by
  have hRaw := copyRangeComp_sound_raw hSrc hCopy
  refine ⟨hRaw.2.1, ?_, hRaw.2.2⟩
  intro bs hGet
  rw [hRaw.2.1] at hGet
  injection hGet with hEq
  subst hEq
  exact ((provPtrPaddedMemCodec_lawful hLookup hSize hFields aid).encodeProps s).2.2.2.2.1

/-- Agreement between unmodified `MirSemantics.replicateValue n v` (produced by
`Rvalue.repeat op n`) and `ByteRun.repeatSlice n [v]`. -/
theorem replicateValue_eq_repeatSlice (n : Nat) (v : Value) :
    replicateValue n v = repeatSlice n [v] := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [repeatSlice_succ, ← repeatSlice_cons_head]
    exact congrArg (List.cons v) ih

/-- Exact `encodeValueToBytes` agreement for `[u16; n]` produced by `Rvalue.repeat`:
encoding `Value.aggregate 0 (replicateValue n (.scalar ⟨x, 2⟩))` equals
`repeatSlice n (encodeLittleEndianBytes x 2 none)` =
`flattenByteRuns abstractByteRunCodec (repeatByteRuns n [.plainBytes [UInt8.ofNat x, UInt8.ofNat (x / 256)]])`. -/
theorem encodeArrayU16Repeat_eq_flattenByteRuns (layouts : LayoutTable)
    (n : Nat) (x : Nat) :
    encodeValueToBytes defaultCodecFuel layouts
      { kind := .array (.uint .u16) n, layoutIdx := 0 }
      (.aggregate 0 (replicateValue n (.scalar ⟨x, 2⟩))) =
      some (flattenByteRuns abstractByteRunCodec
        (repeatByteRuns n [.initPlain [UInt8.ofNat x, UInt8.ofNat (x / 256)]])) := by
  have hElem :
      encodeValueToBytes 15 layouts { kind := .uint .u16, layoutIdx := 0 } (.scalar ⟨x, 2⟩) =
        some [AbstractByte.init (UInt8.ofNat x) none, AbstractByte.init (UInt8.ofNat (x / 256)) none] :=
    rfl
  have hAux : ∀ k : Nat,
      encodeListWith (encodeValueToBytes 15 layouts { kind := .uint .u16, layoutIdx := 0 })
        2 (replicateValue k (.scalar ⟨x, 2⟩)) =
      some (repeatSlice k [AbstractByte.init (UInt8.ofNat x) none, AbstractByte.init (UInt8.ofNat (x / 256)) none]) := by
    intro k
    induction k with
    | zero => rfl
    | succ j ih =>
      unfold replicateValue encodeListWith
      rw [hElem]
      dsimp only [Trusted.Sequence.length, List.length, Nat.beq]
      rw [ih]
      rw [repeatSlice_succ, ← repeatSlice_cons_head]
      rfl
  rw [flattenByteRuns_repeat]
  cases n with
  | zero => rfl
  | succ m =>
    have hRepLen :
        Trusted.Sequence.length (replicateValue (m + 1) (.scalar ⟨x, 2⟩)) = m + 1 := by
      change (replicateValue (m + 1) (.scalar ⟨x, 2⟩)).length = m + 1
      rw [replicateValue_eq_repeatSlice, repeatSlice_length]
      simp
    unfold encodeValueToBytes
    dsimp only [defaultCodecFuel]
    change (match Nat.beq (Trusted.Sequence.length (replicateValue (m + 1) (.scalar ⟨x, 2⟩))) (m + 1) with
      | false => none
      | true =>
        encodeListWith (fun e => encodeValueToBytes 15 layouts { kind := .uint .u16, layoutIdx := 0 } e)
          2 (replicateValue (m + 1) (.scalar ⟨x, 2⟩))) = _
    rw [hRepLen, Nat.beq_refl]
    exact hAux (m + 1)

/-- Transport `ByteRunCopyCut` over `mirDetStep body` directly into
`Anneal.MirFuelFree.MirStepsConverges`. -/
theorem mirStepsConverges_of_byteRunCopyCut {Mem Addr Byte : Type}
    [ByteStoreOps Mem Addr Byte]
    {body : CapturedMir} {memOf : MachineState → Mem}
    {opsList : List (ByteRunCopyOp Addr)} {fuel : Nat}
    {ms₀ ms₁ : MachineState}
    (hCut : ByteRunCopyCut (mirDetStep body) memOf opsList fuel ms₀ ms₁) :
    MirStepsConverges body ms₀
      (fun ms' => ms' = ms₁ ∧ execByteRunCopyOps opsList (memOf ms₀) = some (memOf ms'))
      (fun _ => False) :=
  mirStepsConverges_of_wpUntilOk
    (hCut.to_wpUntil (tag := fun ms => some ms.frame.blockIdx)
      (wpUntil_here (ops := mirDetWpOps body) ⟨rfl, hCut.exec_eq⟩))

/-- Transport `ByteRunCopyCut` over `mirDetStep body` directly into
`Anneal.MirFuelFree.MirWpConverges` by composing with a continuation from `ms₁`. -/
theorem mirWpConverges_of_byteRunCopyCut {Mem Addr Byte : Type}
    [ByteStoreOps Mem Addr Byte]
    {body : CapturedMir} {memOf : MachineState → Mem}
    {opsList : List (ByteRunCopyOp Addr)} {fuel : Nat}
    {ms₀ ms₁ : MachineState} {post : MirOutcome → Prop}
    (hCut : ByteRunCopyCut (mirDetStep body) memOf opsList fuel ms₀ ms₁)
    (hCont : execByteRunCopyOps opsList (memOf ms₀) = some (memOf ms₁) →
      MirWpConverges body ms₁ post) :
    MirWpConverges body ms₀ post :=
  mirWpConverges_of_wpUntilOk_cont
    (hCut.to_wpUntil (tag := fun ms => some ms.frame.blockIdx)
      (wpUntil_here (ops := mirDetWpOps body) (stop := fun ms' => ms' = ms₁) rfl))
    (fun ms' hEq => by subst hEq; exact hCont hCut.exec_eq)

/-- Fail-closed negative bridge: copying out of an immutable global
`CapturedAllocation` (`mutability = .not`) fails with `none`. -/
theorem copyRangeComp_memGlobals_none_of_immutable {m : Memory}
    {src dst : ByteSubLens Nat} {alloc : CapturedAllocation}
    (hFind : lookupGlobalAlloc m.globals src.addr = some alloc)
    (hImm : alloc.mutability = .not) :
    copyRangeComp (Mem := Memory) (Addr := Nat) (Byte := Option UInt8) src dst m = none :=
  copyRangeComp_none_of_src_none (memGlobals_get_none_of_immutable hFind hImm)

/-- Fail-closed negative bridge: copying out of a relocation-bearing global
`CapturedAllocation` (`relocations ≠ []`) fails with `none`. -/
theorem copyRangeComp_memGlobals_none_of_relocated {m : Memory}
    {src dst : ByteSubLens Nat} {alloc : CapturedAllocation}
    (hFind : lookupGlobalAlloc m.globals src.addr = some alloc)
    (hRel : alloc.relocations ≠ []) :
    copyRangeComp (Mem := Memory) (Addr := Nat) (Byte := Option UInt8) src dst m = none :=
  copyRangeComp_none_of_src_none (memGlobals_get_none_of_relocated hFind hRel)

/-- Fail-closed negative bridge: repeated copying out of an immutable global
`CapturedAllocation` fails with `none`. -/
theorem copyRepeatedlyComp_memGlobals_none_of_immutable {m : Memory}
    {src : ByteSubLens Nat} {dstAddr dstOff n : Nat} {alloc : CapturedAllocation}
    (hFind : lookupGlobalAlloc m.globals src.addr = some alloc)
    (hImm : alloc.mutability = .not) :
    copyRepeatedlyComp (Mem := Memory) (Addr := Nat) (Byte := Option UInt8)
      src dstAddr dstOff n m = none :=
  copyRepeatedlyComp_none_of_src_get_none (src := src) dstAddr dstOff n m
    (memGlobals_get_none_of_immutable hFind hImm)

/-- Fail-closed negative bridge: zero-length source or destination copy on
`V2026ByteMem` fails with `none`. -/
theorem copyRangeComp_v2026_none_of_zero_len {m : V2026ByteMem}
    {src dst : ByteSubLens AllocId} (hZero : src.len = 0 ∨ dst.len = 0) :
    copyRangeComp (Mem := V2026ByteMem) (Addr := AllocId) (Byte := AbstractByte)
      src dst m = none := by
  cases hZero with
  | inl hs => exact copyRangeComp_none_of_src_zero m hs
  | inr hd => exact copyRangeComp_none_of_dst_zero m hd

/-! ## Section 2: `OverflowCastJoin` ↔ `V2026_06_01` Operational Bridge -/

/-- Byte width of a `ParametricCore.ScalarWidth` matching unmodified
`V2026_06_01.MirSemantics.intCastTargetBytes`. -/
@[reducible] def scalarWidthToBytes : ScalarWidth → Nat
  | .u8 => 1
  | .u16 => 2
  | .u32 => 4
  | .u64 => 8
  | .u128 => 16

/-- Maps unmodified `MirAst.UintTy` (on 64-bit targets, `usize = u64`) to `ScalarWidth`. -/
@[reducible] def uintTyToScalarWidth : UintTy → ScalarWidth
  | .u8 => .u8
  | .u16 => .u16
  | .u32 => .u32
  | .u64 => .u64
  | .u128 => .u128
  | .usize => .u64

/-- Maps unmodified `MirAst.IntTy` (on 64-bit targets, `isize = i64`) to `ScalarWidth`. -/
@[reducible] def intTyToScalarWidth : IntTy → ScalarWidth
  | .i8 => .u8
  | .i16 => .u16
  | .i32 => .u32
  | .i64 => .u64
  | .i128 => .u128
  | .isize => .u64

/-- Exact agreement between `MirSemantics.intCastTargetBytes (.uint ut)` and
`scalarWidthToBytes (uintTyToScalarWidth ut)`. -/
theorem intCastTargetBytes_uint_eq (ut : UintTy) :
    intCastTargetBytes (.uint ut) = some (scalarWidthToBytes (uintTyToScalarWidth ut)) := by
  cases ut <;> rfl

/-- Exact agreement between `MirSemantics.intCastTargetBytes (.int it)` and
`scalarWidthToBytes (intTyToScalarWidth it)`. -/
theorem intCastTargetBytes_int_eq (it : IntTy) :
    intCastTargetBytes (.int it) = some (scalarWidthToBytes (intTyToScalarWidth it)) := by
  cases it <;> rfl

/-- Exact agreement between unmodified `V2026_06_01.MirSemantics.scalarModulus`
and `ScalarWidth.modulus` across all 5 widths (`u8`, `u16`, `u32`, `u64`, `u128`). -/
theorem scalarModulus_scalarWidthToBytes (w : ScalarWidth) :
    scalarModulus (scalarWidthToBytes w) = w.modulus := by
  cases w <;> decide

/-- Exact bit-width agreement `w.bits = Nat.mul (scalarWidthToBytes w) 8`. -/
theorem scalarWidth_bits_eq_mul8 (w : ScalarWidth) :
    w.bits = Nat.mul (scalarWidthToBytes w) 8 := by
  cases w <;> rfl

/-- Exact agreement between `Nat.ble dstW.bits srcW.bits` and
`Nat.ble (scalarWidthToBytes dstW) (scalarWidthToBytes srcW)`. -/
theorem scalarWidth_ble_bits_iff_bytes (dstW srcW : ScalarWidth) :
    Nat.ble dstW.bits srcW.bits =
      Nat.ble (scalarWidthToBytes dstW) (scalarWidthToBytes srcW) := by
  cases dstW <;> cases srcW <;> rfl

/-- Exact agreement between `MirSemantics.isSignedNegative x (scalarWidthToBytes w)`
and `Nat.ble w.halfModulus (x % w.modulus)`. -/
private theorem nat_lt_of_ble_false {a b : Nat} (h : Nat.ble b a = false) : a < b :=
  match Nat.lt_or_ge a b with
  | .inl hLt => hLt
  | .inr hGe => by rw [Nat.ble_eq.mpr hGe] at h; cases h

private theorem wrapScalarBits_eq_mod (x m : Nat) :
    wrapScalarBits x m = x % m := by
  unfold wrapScalarBits
  cases h : Nat.ble m x with
  | true => rfl
  | false => exact (Nat.mod_eq_of_lt (nat_lt_of_ble_false h)).symm

private theorem scalarPow2_eq_pow2 (k : Nat) : scalarPow2 k = pow2 k := by
  induction k with
  | zero => rfl
  | succ j ih =>
    change Nat.mul 2 (scalarPow2 j) = 2 * pow2 j
    rw [ih]
    rfl

/-- Exact agreement between `MirSemantics.isSignedNegative x (scalarWidthToBytes w)`
and `Nat.ble w.halfModulus (x % w.modulus)`. -/
theorem isSignedNegative_scalarWidth (w : ScalarWidth) (x : Nat) :
    isSignedNegative x (scalarWidthToBytes w) = Nat.ble w.halfModulus (x % w.modulus) := by
  have hSzNe0 : Nat.beq (scalarWidthToBytes w) 0 = false := by cases w <;> rfl
  have hMod : scalarModulus (scalarWidthToBytes w) = w.modulus :=
    scalarModulus_scalarWidthToBytes w
  have hHalf : Nat.div (scalarModulus (scalarWidthToBytes w)) 2 = w.halfModulus := by
    cases w <;> decide
  unfold isSignedNegative
  rw [hSzNe0]
  dsimp only
  rw [hHalf, hMod, wrapScalarBits_eq_mod]

/-- Unconditional narrowing agreement: whenever `dstW.bits ≤ srcW.bits`,
`intToIntCast srcW false dstW x` equals unmodified
`MirSemantics.wrapScalarBits x (scalarModulus (scalarWidthToBytes dstW))` for all `x`. -/
theorem intToIntCast_unsigned_narrow_eq_wrapScalarBits (srcW dstW : ScalarWidth)
    (hNarrow : dstW.bits ≤ srcW.bits) (x : Nat) :
    intToIntCast srcW false dstW x =
      wrapScalarBits x (scalarModulus (scalarWidthToBytes dstW)) := by
  have hMod : scalarModulus (scalarWidthToBytes dstW) = dstW.modulus :=
    scalarModulus_scalarWidthToBytes dstW
  have hBle : Nat.ble dstW.bits srcW.bits = true := Nat.ble_eq.mpr hNarrow
  unfold intToIntCast
  rw [hMod, wrapScalarBits_eq_mod, hBle]
  dsimp only
  exact mod_pow2_mod_pow2_of_le x hNarrow

/-- Canonical-input agreement: for any canonical `x < srcW.modulus`,
`intToIntCast srcW false dstW x` equals unmodified `wrapScalarBits x (scalarModulus (scalarWidthToBytes dstW))`. -/
theorem intToIntCast_unsigned_eq_wrapScalarBits_of_lt (srcW dstW : ScalarWidth)
    {x : Nat} (hx : x < srcW.modulus) :
    intToIntCast srcW false dstW x =
      wrapScalarBits x (scalarModulus (scalarWidthToBytes dstW)) := by
  have hMod : scalarModulus (scalarWidthToBytes dstW) = dstW.modulus :=
    scalarModulus_scalarWidthToBytes dstW
  unfold intToIntCast
  rw [hMod, wrapScalarBits_eq_mod, Nat.mod_eq_of_lt hx]
  cases hLe : Nat.ble dstW.bits srcW.bits with
  | true => rfl
  | false =>
    have hSrcLt : srcW.bits < dstW.bits := nat_lt_of_ble_false hLe
    have hLtDst : x < dstW.modulus :=
      Nat.lt_of_lt_of_le hx (pow2_le_pow2 (Nat.le_of_lt hSrcLt))
    exact (Nat.mod_eq_of_lt hLtDst).symm

/-- Exact unconditional agreement between `OverflowCastJoin.intToIntCast srcW true dstW x`
and unmodified `V2026_06_01.MirSemantics.signExtendBits x (scalarWidthToBytes srcW) (scalarWidthToBytes dstW)`
(matching `Rvalue.cast .intToInt` on signed operands across all 25 `(srcW, dstW)` pairs). -/
theorem intToIntCast_signed_eq_signExtendBits (srcW dstW : ScalarWidth) (x : Nat) :
    intToIntCast srcW true dstW x =
      signExtendBits x (scalarWidthToBytes srcW) (scalarWidthToBytes dstW) := by
  have hSrcMod : scalarModulus (scalarWidthToBytes srcW) = srcW.modulus :=
    scalarModulus_scalarWidthToBytes srcW
  have hDstMod : scalarModulus (scalarWidthToBytes dstW) = dstW.modulus :=
    scalarModulus_scalarWidthToBytes dstW
  unfold intToIntCast signExtendBits
  rw [hSrcMod, hDstMod, ← scalarWidth_ble_bits_iff_bytes]
  dsimp only
  rw [wrapScalarBits_eq_mod]
  cases hLe : Nat.ble dstW.bits srcW.bits with
  | true =>
    dsimp only
    rw [wrapScalarBits_eq_mod]
  | false =>
    dsimp only
    rw [isSignedNegative_scalarWidth, wrapScalarBits_eq_mod, Nat.mod_mod]
    cases Nat.ble srcW.halfModulus (x % srcW.modulus) with
    | false => rfl
    | true => rfl

/-- Exact agreement between unmodified `evalScalarBinOp .addWithOverflow` (unsigned)
and `OverflowCastJoin.addWithOverflowU`. -/
theorem evalScalarBinOp_addWithOverflow_unsigned_eq (w : ScalarWidth) (a b : Nat)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .addWithOverflow
      ⟨a, scalarWidthToBytes w⟩ ⟨b, scalarWidthToBytes w⟩ locals mem false =
      .ok (.aggregate 0
        [ .scalar ⟨(addWithOverflowU w a b).1, scalarWidthToBytes w⟩
        , .scalar ⟨if (addWithOverflowU w a b).2 then 1 else 0, 1⟩ ]) locals mem := by
  have hSzNe0 : Nat.beq (scalarWidthToBytes w) 0 = false := by cases w <;> rfl
  have hMod : scalarModulus (scalarWidthToBytes w) = w.modulus :=
    scalarModulus_scalarWidthToBytes w
  unfold evalScalarBinOp addWithOverflowU
  rw [hSzNe0]
  dsimp only
  rw [Nat.beq_refl]
  dsimp only
  rw [hMod, wrapScalarBits_eq_mod]
  by_cases hOvf : Nat.ble w.modulus (a + b) = true
  · have hOvf' : Nat.ble w.modulus (Nat.add a b) = true := hOvf
    simp only [hOvf', hOvf, ↓reduceIte]
    rfl
  · have hF : Nat.ble w.modulus (a + b) = false := Bool.eq_false_iff.mpr hOvf
    have hF' : Nat.ble w.modulus (Nat.add a b) = false := hF
    simp only [hF', hF, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- Exact agreement between unmodified `evalScalarBinOp .mulWithOverflow` (unsigned)
and `OverflowCastJoin.mulWithOverflowU`. -/
theorem evalScalarBinOp_mulWithOverflow_unsigned_eq (w : ScalarWidth) (a b : Nat)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .mulWithOverflow
      ⟨a, scalarWidthToBytes w⟩ ⟨b, scalarWidthToBytes w⟩ locals mem false =
      .ok (.aggregate 0
        [ .scalar ⟨(mulWithOverflowU w a b).1, scalarWidthToBytes w⟩
        , .scalar ⟨if (mulWithOverflowU w a b).2 then 1 else 0, 1⟩ ]) locals mem := by
  have hSzNe0 : Nat.beq (scalarWidthToBytes w) 0 = false := by cases w <;> rfl
  have hMod : scalarModulus (scalarWidthToBytes w) = w.modulus :=
    scalarModulus_scalarWidthToBytes w
  unfold evalScalarBinOp mulWithOverflowU
  rw [hSzNe0]
  dsimp only
  rw [Nat.beq_refl]
  dsimp only
  rw [hMod, wrapScalarBits_eq_mod]
  by_cases hOvf : Nat.ble w.modulus (a * b) = true
  · have hOvf' : Nat.ble w.modulus (Nat.mul a b) = true := hOvf
    simp only [hOvf', hOvf, ↓reduceIte]
    rfl
  · have hF : Nat.ble w.modulus (a * b) = false := Bool.eq_false_iff.mpr hOvf
    have hF' : Nat.ble w.modulus (Nat.mul a b) = false := hF
    simp only [hF', hF, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- Exact agreement between unmodified `evalScalarBinOp .subWithOverflow` (unsigned)
and `OverflowCastJoin.subWithOverflowU` for canonical inputs `a < w.modulus`, `b < w.modulus`. -/
theorem evalScalarBinOp_subWithOverflow_unsigned_eq (w : ScalarWidth) {a b : Nat}
    (ha : a < w.modulus) (hb : b < w.modulus)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .subWithOverflow
      ⟨a, scalarWidthToBytes w⟩ ⟨b, scalarWidthToBytes w⟩ locals mem false =
      .ok (.aggregate 0
        [ .scalar ⟨(subWithOverflowU w a b).1, scalarWidthToBytes w⟩
        , .scalar ⟨if (subWithOverflowU w a b).2 then 1 else 0, 1⟩ ]) locals mem := by
  have hSzNe0 : Nat.beq (scalarWidthToBytes w) 0 = false := by cases w <;> rfl
  have hMod : scalarModulus (scalarWidthToBytes w) = w.modulus :=
    scalarModulus_scalarWidthToBytes w
  have hBleA : Nat.ble w.modulus a = false := by
    cases h : Nat.ble w.modulus a with
    | false => rfl
    | true => have := Nat.ble_eq.mp h; omega
  have hBleB : Nat.ble w.modulus b = false := by
    cases h : Nat.ble w.modulus b with
    | false => rfl
    | true => have := Nat.ble_eq.mp h; omega
  unfold evalScalarBinOp subWithOverflowU
  rw [hSzNe0]
  dsimp only
  rw [Nat.beq_refl]
  dsimp only
  rw [hMod, hBleA, hBleB, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  cases hLe : Nat.ble b a with
  | true =>
    dsimp only
    rw [wrapScalarBits_eq_mod]
    have hBa : b ≤ a := Nat.ble_eq.mp hLe
    have hBlt : Nat.blt a b = false := by
      cases h : Nat.blt a b with
      | false => rfl
      | true => have := Nat.blt_eq.mp h; omega
    have hEqMod : (a - b) % w.modulus = (a + w.modulus - b) % w.modulus := by
      have hSub : a + w.modulus - b = (a - b) + w.modulus := by omega
      rw [hSub, Nat.add_mod_right]
    simp only [hBlt, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    change RvalueEvalResult.ok (.aggregate 0 [.scalar ⟨(a - b) % w.modulus, scalarWidthToBytes w⟩, .scalar ⟨0, 1⟩]) locals mem =
      RvalueEvalResult.ok (.aggregate 0 [.scalar ⟨(a + w.modulus - b) % w.modulus, scalarWidthToBytes w⟩, .scalar ⟨0, 1⟩]) locals mem
    rw [hEqMod]
  | false =>
    dsimp only
    rw [wrapScalarBits_eq_mod, wrapScalarBits_eq_mod, wrapScalarBits_eq_mod,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
    have hLt : a < b := nat_lt_of_ble_false hLe
    have hBlt : Nat.blt a b = true := Nat.blt_eq.mpr hLt
    simp only [hBlt, Bool.true_or, ↓reduceIte]
    change RvalueEvalResult.ok (.aggregate 0 [.scalar ⟨(w.modulus + a - b) % w.modulus, scalarWidthToBytes w⟩, .scalar ⟨1, 1⟩]) locals mem =
      RvalueEvalResult.ok (.aggregate 0 [.scalar ⟨(a + w.modulus - b) % w.modulus, scalarWidthToBytes w⟩, .scalar ⟨1, 1⟩]) locals mem
    rw [Nat.add_comm w.modulus a]

/-- Exact agreement between unmodified `evalScalarBinOp .addUnchecked` (unsigned)
and `OverflowCastJoin.addUncheckedU`: returns `.ok (.scalar ⟨r, sz⟩)` iff
`addUncheckedU w a b = some r`, and `.ub` iff `addUncheckedU w a b = none`. -/
theorem evalScalarBinOp_addUnchecked_unsigned_eq (w : ScalarWidth) (a b : Nat)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .addUnchecked
      ⟨a, scalarWidthToBytes w⟩ ⟨b, scalarWidthToBytes w⟩ locals mem false =
      match addUncheckedU w a b with
      | some r => .ok (.scalar ⟨r, scalarWidthToBytes w⟩) locals mem
      | none => .ub := by
  have hSzNe0 : Nat.beq (scalarWidthToBytes w) 0 = false := by cases w <;> rfl
  have hMod : scalarModulus (scalarWidthToBytes w) = w.modulus :=
    scalarModulus_scalarWidthToBytes w
  unfold evalScalarBinOp addUncheckedU addWithOverflowU
  rw [hSzNe0]
  dsimp only
  rw [Nat.beq_refl]
  dsimp only
  rw [hMod]
  cases hGe : Nat.ble w.modulus (Nat.add a b) with
  | true => rfl
  | false =>
    have hLt : a + b < w.modulus := nat_lt_of_ble_false hGe
    change RvalueEvalResult.ok (.scalar ⟨a + b, scalarWidthToBytes w⟩) locals mem =
      RvalueEvalResult.ok (.scalar ⟨(a + b) % w.modulus, scalarWidthToBytes w⟩) locals mem
    rw [Nat.mod_eq_of_lt hLt]

/-- Exact agreement between unmodified `evalScalarBinOp .mulUnchecked` (unsigned)
and `OverflowCastJoin.mulUncheckedU`. -/
theorem evalScalarBinOp_mulUnchecked_unsigned_eq (w : ScalarWidth) (a b : Nat)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .mulUnchecked
      ⟨a, scalarWidthToBytes w⟩ ⟨b, scalarWidthToBytes w⟩ locals mem false =
      match mulUncheckedU w a b with
      | some r => .ok (.scalar ⟨r, scalarWidthToBytes w⟩) locals mem
      | none => .ub := by
  have hSzNe0 : Nat.beq (scalarWidthToBytes w) 0 = false := by cases w <;> rfl
  have hMod : scalarModulus (scalarWidthToBytes w) = w.modulus :=
    scalarModulus_scalarWidthToBytes w
  unfold evalScalarBinOp mulUncheckedU mulWithOverflowU
  rw [hSzNe0]
  dsimp only
  rw [Nat.beq_refl]
  dsimp only
  rw [hMod]
  cases hGe : Nat.ble w.modulus (Nat.mul a b) with
  | true => rfl
  | false =>
    have hLt : a * b < w.modulus := nat_lt_of_ble_false hGe
    change RvalueEvalResult.ok (.scalar ⟨a * b, scalarWidthToBytes w⟩) locals mem =
      RvalueEvalResult.ok (.scalar ⟨(a * b) % w.modulus, scalarWidthToBytes w⟩) locals mem
    rw [Nat.mod_eq_of_lt hLt]

/-- Exact agreement between unmodified `evalScalarBinOp .shlUnchecked` (unsigned)
and `OverflowCastJoin.shlUncheckedU`. -/
theorem evalScalarBinOp_shlUnchecked_unsigned_eq (w : ScalarWidth) (a shift : Nat)
    (rhsSz : Nat) (hRhsNe0 : Nat.beq rhsSz 0 = false)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .shlUnchecked
      ⟨a, scalarWidthToBytes w⟩ ⟨shift, rhsSz⟩ locals mem false =
      match shlUncheckedU w a shift with
      | some r => .ok (.scalar ⟨r, scalarWidthToBytes w⟩) locals mem
      | none => .ub := by
  have hSzNe0 : Nat.beq (scalarWidthToBytes w) 0 = false := by cases w <;> rfl
  have hMod : scalarModulus (scalarWidthToBytes w) = w.modulus :=
    scalarModulus_scalarWidthToBytes w
  have hBits : Nat.mul (scalarWidthToBytes w) 8 = w.bits := (scalarWidth_bits_eq_mul8 w).symm
  unfold evalScalarBinOp shlUncheckedU shlWithOverflowU
  rw [hSzNe0]
  dsimp only
  rw [hRhsNe0]
  dsimp only
  rw [hBits, hMod]
  cases hGe : Nat.ble w.bits shift with
  | true => rfl
  | false =>
    have hShiftEq : shiftLeftBits a shift w.modulus = (a * pow2 shift) % w.modulus := by
      unfold shiftLeftBits
      rw [wrapScalarBits_eq_mod, scalarPow2_eq_pow2]
      rfl
    change RvalueEvalResult.ok (.scalar ⟨shiftLeftBits a shift w.modulus, scalarWidthToBytes w⟩) locals mem =
      RvalueEvalResult.ok (.scalar ⟨(a * pow2 (shift % w.bits)) % w.modulus, scalarWidthToBytes w⟩) locals mem
    rw [hShiftEq, Nat.mod_eq_of_lt (nat_lt_of_ble_false hGe)]

/-- Lawful `OvfCastFrameOps MachineState Value` directly over unmodified
`V2026_06_01.MirSemantics.{MachineState, Value}`. -/
def v2026ValOvfCastFrameOps : OvfCastFrameOps MachineState Value where
  blockOf ms := ms.frame.blockIdx
  localsOf ms :=
    ms.frame.locals.map fun slot =>
      match slot with
      | .init v => v
      | .uninit => .uninit
      | .dead => .uninit
  withBlockLocals ms bb vals :=
    { ms with frame := { blockIdx := bb, stmtIdx := 0, locals := vals.map LocalSlot.init } }
  mkScalar w n := .scalar ⟨n, scalarWidthToBytes w⟩
  asScalar? w v :=
    match v with
    | .scalar sc =>
      if Nat.beq sc.sizeBytes (scalarWidthToBytes w) && Nat.blt sc.bits w.modulus then
        some sc.bits
      else none
    | _ => none
  mkOvfTuple w wrapped ovf :=
    .aggregate 0 [.scalar ⟨wrapped, scalarWidthToBytes w⟩, .scalar ⟨if ovf then 1 else 0, 1⟩]

/-- Constructive lawfulness proof for `v2026ValOvfCastFrameOps`. -/
theorem v2026ValOvfCastFrameOps_lawful : v2026ValOvfCastFrameOps.Lawful where
  blockOf_withBlockLocals _ _ _ := rfl
  localsOf_withBlockLocals _ _ vals := by
    change (vals.map LocalSlot.init).map (fun slot =>
      match slot with | .init v => v | .uninit => .uninit | .dead => .uninit) = vals
    induction vals with
    | nil => rfl
    | cons v vs ih => exact congrArg (List.cons v) ih
  asScalar?_mkScalar w n hn := by
    change (if Nat.beq (scalarWidthToBytes w) (scalarWidthToBytes w) &&
        Nat.blt n w.modulus then some n else none) = some n
    rw [Nat.beq_refl, Nat.blt_eq.mpr hn]
    rfl

/-- Signed biased-coordinate view of `v2026ValOvfCastFrameOps`. -/
abbrev v2026ValSignedOvfCastFrameOps : OvfCastFrameOps MachineState Value :=
  v2026ValOvfCastFrameOps.signedView

theorem v2026ValSignedOvfCastFrameOps_lawful : v2026ValSignedOvfCastFrameOps.Lawful :=
  v2026ValOvfCastFrameOps.signedView_lawful v2026ValOvfCastFrameOps_lawful

/-- Exact `LocalSlot`-preserving `OvfCastFrameOps MachineState LocalSlot` directly
over unmodified `V2026_06_01.MirSemantics.{MachineState, LocalSlot}` (preserves
`.dead` and `.uninit` slots losslessly across `withBlockLocals`). -/
def v2026SlotOvfCastFrameOps : OvfCastFrameOps MachineState LocalSlot where
  blockOf ms := ms.frame.blockIdx
  localsOf ms := ms.frame.locals
  withBlockLocals ms bb locs :=
    { ms with frame := { blockIdx := bb, stmtIdx := 0, locals := locs } }
  mkScalar w n := .init (.scalar ⟨n, scalarWidthToBytes w⟩)
  asScalar? w slot :=
    match slot with
    | .init (.scalar sc) =>
      if Nat.beq sc.sizeBytes (scalarWidthToBytes w) && Nat.blt sc.bits w.modulus then
        some sc.bits
      else none
    | _ => none
  mkOvfTuple w wrapped ovf :=
    .init (.aggregate 0 [.scalar ⟨wrapped, scalarWidthToBytes w⟩, .scalar ⟨if ovf then 1 else 0, 1⟩])

/-- Constructive lawfulness proof for `v2026SlotOvfCastFrameOps`. -/
theorem v2026SlotOvfCastFrameOps_lawful : v2026SlotOvfCastFrameOps.Lawful where
  blockOf_withBlockLocals _ _ _ := rfl
  localsOf_withBlockLocals _ _ _ := rfl
  asScalar?_mkScalar w n hn := by
    change (if Nat.beq (scalarWidthToBytes w) (scalarWidthToBytes w) &&
        Nat.blt n w.modulus then some n else none) = some n
    rw [Nat.beq_refl, Nat.blt_eq.mpr hn]
    rfl

/-- Signed biased-coordinate view of `v2026SlotOvfCastFrameOps`. -/
abbrev v2026SlotSignedOvfCastFrameOps : OvfCastFrameOps MachineState LocalSlot :=
  v2026SlotOvfCastFrameOps.signedView

theorem v2026SlotSignedOvfCastFrameOps_lawful : v2026SlotSignedOvfCastFrameOps.Lawful :=
  v2026SlotOvfCastFrameOps.signedView_lawful v2026SlotOvfCastFrameOps_lawful

/-- Cutpoint-normalized pure-scalar `OvfCastFrameOps MachineState LocalSlot` over
unmodified `V2026_06_01.MirSemantics.MachineState`: encodes `stmtIdx = 0`,
`activeCallee = none`, `borrows = []`, and `callStack = []` directly into
`blockOf` (`< 1000000` iff at a clean root-frame block entry), so every
`StageIntervalStateInv` cutpoint directly admits unmodified `mirDetStep body`
execution without any shadow semantics or extra side-conditions. -/
def v2026PureSlotOvfCastFrameOps : OvfCastFrameOps MachineState LocalSlot where
  blockOf ms :=
    if Nat.beq ms.frame.stmtIdx 0 && ms.memory.activeCallee.isNone &&
        ms.memory.borrows.isEmpty && ms.memory.callStack.isEmpty then
      ms.frame.blockIdx
    else
      1000000 + ms.frame.blockIdx
  localsOf ms := ms.frame.locals
  withBlockLocals ms bb locs :=
    { frame := { blockIdx := bb, stmtIdx := 0, locals := locs }
      memory := { ms.memory with activeCallee := none, borrows := [], callStack := [] } }
  mkScalar w n := .init (.scalar ⟨n, scalarWidthToBytes w⟩)
  asScalar? w slot :=
    match slot with
    | .init (.scalar sc) =>
      if Nat.beq sc.sizeBytes (scalarWidthToBytes w) && Nat.blt sc.bits w.modulus then
        some sc.bits
      else none
    | _ => none
  mkOvfTuple w wrapped ovf :=
    .init (.aggregate 0 [.scalar ⟨wrapped, scalarWidthToBytes w⟩, .scalar ⟨if ovf then 1 else 0, 1⟩])

/-- Constructive lawfulness proof for `v2026PureSlotOvfCastFrameOps`. -/
theorem v2026PureSlotOvfCastFrameOps_lawful : v2026PureSlotOvfCastFrameOps.Lawful where
  blockOf_withBlockLocals _ _ _ := rfl
  localsOf_withBlockLocals _ _ _ := rfl
  asScalar?_mkScalar w n hn := by
    change (if Nat.beq (scalarWidthToBytes w) (scalarWidthToBytes w) &&
        Nat.blt n w.modulus then some n else none) = some n
    rw [Nat.beq_refl, Nat.blt_eq.mpr hn]
    rfl

/-- Unpack a clean block-entry cutpoint (`bb < 1000000`) from
`v2026PureSlotOvfCastFrameOps.blockOf ms = bb`. -/
theorem v2026PureSlot_blockOf_unpack {ms : MachineState} {bb : Nat}
    (hBbLt : bb < 1000000)
    (hBlk : v2026PureSlotOvfCastFrameOps.blockOf ms = bb) :
    ms.frame.blockIdx = bb ∧
    ms.frame.stmtIdx = 0 ∧
    ms.memory.activeCallee = none ∧
    ms.memory.borrows = [] ∧
    ms.memory.callStack = [] := by
  unfold v2026PureSlotOvfCastFrameOps at hBlk
  dsimp only at hBlk
  cases hCond :
      (Nat.beq ms.frame.stmtIdx 0 && ms.memory.activeCallee.isNone &&
        ms.memory.borrows.isEmpty && ms.memory.callStack.isEmpty) with
  | false =>
    rw [hCond] at hBlk
    simp only [Bool.false_eq_true, ↓reduceIte] at hBlk
    omega
  | true =>
    rw [hCond] at hBlk
    simp only [↓reduceIte] at hBlk
    simp only [Bool.and_eq_true, Nat.beq_eq, Option.isNone_iff_eq_none] at hCond
    have hBor : ms.memory.borrows = [] := by
      cases hB : ms.memory.borrows with
      | nil => rfl
      | cons _ _ => rw [hB] at hCond; cases hCond.1.2
    have hStk : ms.memory.callStack = [] := by
      cases hS : ms.memory.callStack with
      | nil => rfl
      | cons _ _ => rw [hS] at hCond; cases hCond.2
    exact ⟨hBlk, hCond.1.1.1, hCond.1.1.2, hBor, hStk⟩

/-- Transport ANY `OvfCastStageCut` over `mirDetStep body` (including
`v2026ValOvfCastFrameOps`, `v2026SlotOvfCastFrameOps`, `v2026PureSlotOvfCastFrameOps`,
and their `.signedView`s) directly into `Anneal.MirFuelFree.MirStepsConverges`. -/
theorem mirStepsConverges_of_ovfCastStageCut {Val : Type}
    {fops : OvfCastFrameOps MachineState Val}
    {body : CapturedMir} {baseLocals : List Val} {ids : StageLocalIds}
    {earlyOk : MirOutcome → Bool} {srcSpec dstSpec : StageIntervalSpec} {fuel : Nat}
    (hCut : OvfCastStageCut fops (mirDetStep body) baseLocals ids earlyOk srcSpec dstSpec fuel)
    {ms₀ : MachineState}
    (hInv : StageIntervalStateInv fops baseLocals ids srcSpec ms₀) :
    MirStepsConverges body ms₀
      (StageIntervalStateInv fops baseLocals ids dstSpec)
      (fun out => earlyOk out = true) :=
  mirStepsConverges_of_wpUntilOk_det
    (wpUntil_of_wpUntilFuel
      (ops := MirWpOps.ofDetStep (mirDetStep body) (fun st => some (fops.blockOf st)))
      (open_ovfCastStageCut hCut ms₀ hInv))

/-- Transport ANY `OvfCastStageCut` directly over `mirDetStep body` into
`Anneal.MirFuelFree.MirWpConverges`, composing the stage cut with a continuation
from `dstSpec` and an early-return obligation for `earlyOk`. -/
theorem mirWpConverges_of_ovfCastStageCut {Val : Type}
    {fops : OvfCastFrameOps MachineState Val}
    {body : CapturedMir} {baseLocals : List Val} {ids : StageLocalIds}
    {earlyOk : MirOutcome → Bool} {srcSpec dstSpec : StageIntervalSpec} {fuel : Nat}
    {post : MirOutcome → Prop}
    (hCut : OvfCastStageCut fops (mirDetStep body) baseLocals ids earlyOk srcSpec dstSpec fuel)
    {ms₀ : MachineState}
    (hInv : StageIntervalStateInv fops baseLocals ids srcSpec ms₀)
    (hCont : ∀ ms', StageIntervalStateInv fops baseLocals ids dstSpec ms' →
      MirWpConverges body ms' post)
    (hEarly : ∀ out, earlyOk out = true → post out) :
    MirWpConverges body ms₀ post :=
  mirWpConverges_of_wpUntilOk_det
    (wpUntil_mono
      (ops := MirWpOps.ofDetStep (mirDetStep body) (fun st => some (fops.blockOf st)))
      (fun _ h => h) hEarly (fun _ hf => hf)
      (wpUntil_of_wpUntilFuel
        (ops := MirWpOps.ofDetStep (mirDetStep body) (fun st => some (fops.blockOf st)))
        (open_ovfCastStageCut hCut ms₀ hInv)))
    hCont

/-- **`BlockTree` on `CapturedMir` → `OvfCastStageCut`**: lifts an
`OvfCastStageCut` proved over the `O(log n)` `BlockTree`-backed live step
`mirDetStepWith body bt.lookupForced?` (any `ValidBlockTree body.basicBlocks bt`)
to the unmodified list-backed `mirDetStep body`. -/
theorem ovfCastStageCut_mir_of_validBlockTree {Val : Type}
    {fops : OvfCastFrameOps MachineState Val} {body : CapturedMir}
    {bt : BlockTree BasicBlockData} (hValid : ValidBlockTree body.basicBlocks bt)
    {baseLocals : List Val} {ids : StageLocalIds} {earlyOk : MirOutcome → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {fuel : Nat}
    (h : OvfCastStageCut fops (mirDetStepWith body bt.lookupForced?) baseLocals ids
      earlyOk srcSpec dstSpec fuel) :
    OvfCastStageCut fops (mirDetStep body) baseLocals ids earlyOk srcSpec dstSpec fuel :=
  ovfCastStageCut_congr_step (mirDetStepWith_listGet?_eq body)
    (ovfCastStageCut_of_validBlockTree hValid fops (mirDetStepWith body)
      (fun f g s hEq => mirDetStepWith_pointwise body f g s (hEq s.frame.blockIdx)) h)

/-- **`Chunk8BlockTree` on `CapturedMir` → `OvfCastStageCut`** (radix-8 variant of
`ovfCastStageCut_mir_of_validBlockTree`). -/
theorem ovfCastStageCut_mir_of_validChunk8BlockTree {Val : Type}
    {fops : OvfCastFrameOps MachineState Val} {body : CapturedMir}
    {cbt : Chunk8BlockTree BasicBlockData}
    (hValid : ValidChunk8BlockTree body.basicBlocks cbt)
    {baseLocals : List Val} {ids : StageLocalIds} {earlyOk : MirOutcome → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {fuel : Nat}
    (h : OvfCastStageCut fops (mirDetStepWith body cbt.lookupForced?) baseLocals ids
      earlyOk srcSpec dstSpec fuel) :
    OvfCastStageCut fops (mirDetStep body) baseLocals ids earlyOk srcSpec dstSpec fuel :=
  ovfCastStageCut_congr_step (mirDetStepWith_listGet?_eq body)
    (ovfCastStageCut_of_validChunk8BlockTree hValid fops (mirDetStepWith body)
      (fun f g s hEq => mirDetStepWith_pointwise body f g s (hEq s.frame.blockIdx)) h)

/-- **`evalBlockTreeToCut` on `CapturedMir` → `OvfCastStageCut`**: seals an
`OvfCastStageCut` over live `mirDetStep body` directly from kernel evaluation of
`evalBlockTreeToCut` over the `BlockTree`-backed `mirDetStepWith body`. -/
theorem ovfCastStageCut_mir_of_evalBlockTreeToCut {Val : Type}
    {fops : OvfCastFrameOps MachineState Val} {body : CapturedMir}
    {bt : BlockTree BasicBlockData} (hValid : ValidBlockTree body.basicBlocks bt)
    {baseLocals : List Val} {ids : StageLocalIds} {earlyOk : MirOutcome → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {cuts : MaskTree} {fuel : Nat}
    (hEval : ∀ s : MachineState, StageIntervalStateInv fops baseLocals ids srcSpec s →
      ∃ s' : MachineState,
        evalBlockTreeToCut bt (mirDetStepWith body) StepOutcome.next? fops.blockOf cuts
          fuel s = .cut s' ∧
        StageIntervalStateInv fops baseLocals ids dstSpec s') :
    OvfCastStageCut fops (mirDetStep body) baseLocals ids earlyOk srcSpec dstSpec fuel :=
  ovfCastStageCut_congr_step (mirDetStepWith_listGet?_eq body)
    (ovfCastStageCut_of_evalBlockTreeToCut hValid fops (mirDetStepWith body)
      (fun f g s hEq => mirDetStepWith_pointwise body f g s (hEq s.frame.blockIdx)) hEval)

/-- **`BlockTree` on `CapturedMir` → `ByteRunCopyCut`**: lifts a `ByteRunCopyCut`
proved over `mirDetStepWith body bt.lookupForced?` to live `mirDetStep body`. -/
theorem byteRunCopyCut_mir_of_validBlockTree {Mem Addr Byte : Type}
    [ByteStoreOps Mem Addr Byte] {body : CapturedMir}
    {bt : BlockTree BasicBlockData} (hValid : ValidBlockTree body.basicBlocks bt)
    {memOf : MachineState → Mem} {opsList : List (ByteRunCopyOp Addr)} {fuel : Nat}
    {ms₀ ms₁ : MachineState}
    (h : ByteRunCopyCut (mirDetStepWith body bt.lookupForced?) memOf opsList fuel ms₀ ms₁) :
    ByteRunCopyCut (mirDetStep body) memOf opsList fuel ms₀ ms₁ :=
  ByteRunCopyCut.congr_step (mirDetStepWith_listGet?_eq body)
    (ByteRunCopyCut.of_validBlockTree hValid (stepWith := mirDetStepWith body)
      (fun f g s hEq => mirDetStepWith_pointwise body f g s (hEq s.frame.blockIdx)) h)

/-! ## Section 3: `CallStackUnwind` & `RefFrame` ↔ `V2026_06_01` Operational Bridge -/

/-- Exact bijection mapping unmodified `MirAst.UnwindAction` to `ParametricCore.UnwindAction4`. -/
@[reducible] def unwindActionTo4 : UnwindAction → UnwindAction4
  | .cleanup bb => .cleanup bb
  | .unreachable => .unreachable
  | .terminate => .terminate
  | .continue_ => .continue_

/-- Inverse bijection mapping `ParametricCore.UnwindAction4` to unmodified `MirAst.UnwindAction`. -/
@[reducible] def unwindActionFrom4 : UnwindAction4 → UnwindAction
  | .cleanup bb => .cleanup bb
  | .unreachable => .unreachable
  | .terminate => .terminate
  | .continue_ => .continue_

theorem unwindActionFrom4_to4 (u : UnwindAction) :
    unwindActionFrom4 (unwindActionTo4 u) = u := by
  cases u <;> rfl

theorem unwindActionTo4_from4 (u : UnwindAction4) :
    unwindActionTo4 (unwindActionFrom4 u) = u := by
  cases u <;> rfl

/-- Extract a `CallCont4` descriptor directly from an unmodified `TerminatorKind.call`. -/
@[reducible] def callCont4OfTerminator? : TerminatorKind → Option CallCont4
  | .call _ _ _ target unwind => some ⟨target, unwindActionTo4 unwind⟩
  | _ => none

/-- Extract the active `CallCont4` descriptor directly from an unmodified
`V2026_06_01.MirSemantics.SavedCallerFrame`. -/
@[reducible] def callCont4OfSavedFrame (sf : SavedCallerFrame) : CallCont4 :=
  ⟨if sf.isDiverging then none else some sf.returnTarget, unwindActionTo4 sf.returnUnwind⟩

/-- Exact bijection mapping unmodified `MirSemantics.TreeBorrowPerm` to
`Anneal.RefFrame.TbPermission`. -/
@[reducible] def tbPermOfMir : TreeBorrowPerm → TbPermission
  | .cell => .Cell
  | .reservedFrz conflicted => .ReservedFrz conflicted
  | .reservedIM => .ReservedIM
  | .unique => .Unique
  | .frozen => .Frozen
  | .disabled => .Disabled

/-- Inverse bijection mapping `Anneal.RefFrame.TbPermission` to unmodified
`MirSemantics.TreeBorrowPerm`. -/
@[reducible] def mirOfTbPerm : TbPermission → TreeBorrowPerm
  | .Cell => .cell
  | .ReservedFrz conflicted => .reservedFrz conflicted
  | .ReservedIM => .reservedIM
  | .Unique => .unique
  | .Frozen => .frozen
  | .Disabled => .disabled

theorem mirOfTbPerm_tbPermOfMir (p : TreeBorrowPerm) :
    mirOfTbPerm (tbPermOfMir p) = p := by
  cases p <;> rfl

theorem tbPermOfMir_mirOfTbPerm (p : TbPermission) :
    tbPermOfMir (mirOfTbPerm p) = p := by
  cases p <;> rfl

/-- Exact bijection `TreeBorrowAccessKind → TbAccessKind`. -/
@[reducible] def tbKindOfMir : TreeBorrowAccessKind → TbAccessKind
  | .read => .Read
  | .write => .Write

/-- Exact bijection `TreeBorrowRelatedness → TbAccessRelatedness`. -/
@[reducible] def tbRelOfMir : TreeBorrowRelatedness → TbAccessRelatedness
  | .localAccess => .LocalAccess
  | .foreignAccess => .ForeignAccess

/-- Exact bijection `TreeBorrowTransition → TbAccessOutcome`. -/
@[reducible] def tbOutcomeOfMir : TreeBorrowTransition → TbAccessOutcome
  | .transition p => .Transition (tbPermOfMir p)
  | .ub => .UndefinedBehavior
  | .protectedReservedIM => .ImpossibleProtectedReservedIM

/-- **Full 56-case transition-table equivalence**: unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.treeBorrowPermTransition` agrees on every
`(kind, rel, perm, isProtected)` tuple with `Anneal.RefFrame.performPermAccess`. -/
theorem treeBorrowPermTransition_eq_performPermAccess
    (kind : TreeBorrowAccessKind) (rel : TreeBorrowRelatedness)
    (perm : TreeBorrowPerm) (isProtected : Bool) :
    tbOutcomeOfMir (treeBorrowPermTransition kind rel perm isProtected) =
      performPermAccess (tbKindOfMir kind) (tbRelOfMir rel) (tbPermOfMir perm) isProtected := by
  cases kind <;> cases rel <;> cases perm <;> cases isProtected <;>
    first | rfl | (rename_i c; cases c <;> rfl)

/-- **Accessed non-disabled node-access agreement**: for every active (non-`.disabled`)
`BorrowEntry` permission, unmodified `V2026_06_01.MirSemantics.treeBorrowNodeAccess`
and `Anneal.RefFrame.TbLocationState.performAccess ⟨tbPermOfMir perm, true⟩` agree on
exact next permission AND on UB / `.ProtectedDisabled` / invariant-failure classification. -/
theorem treeBorrowNodeAccess_agrees_with_performAccess
    (kind : TreeBorrowAccessKind) (rel : TreeBorrowRelatedness)
    (perm : TreeBorrowPerm) (isProtected : Bool)
    (hNotDis : perm ≠ .disabled) :
    (∀ p' : TreeBorrowPerm,
      treeBorrowNodeAccess kind rel perm isProtected = .transition p' ↔
      TbLocationState.performAccess ⟨tbPermOfMir perm, true⟩
        (tbKindOfMir kind) (tbRelOfMir rel) isProtected =
        .Success ⟨tbPermOfMir p', true⟩) ∧
    (treeBorrowTransitionIsUB (treeBorrowNodeAccess kind rel perm isProtected) = true ↔
      (match TbLocationState.performAccess ⟨tbPermOfMir perm, true⟩
        (tbKindOfMir kind) (tbRelOfMir rel) isProtected with
      | .Success _ => false
      | .Error _ _ => true
      | .InvariantFailure _ => true) = true) := by
  cases perm with
  | disabled => exact False.elim (hNotDis rfl)
  | cell =>
    cases kind <;> cases rel <;> cases isProtected <;>
      exact ⟨fun p' => by cases p' <;> simp [TbLocationState.performAccess, performPermAccess,
        TbAccessRelatedness.isForeign, childReadPerm, childWritePerm, foreignReadPerm,
        foreignWritePerm, TbPermission.isDisabled, tbKindOfMir, tbPermOfMir],
        by decide⟩
  | reservedFrz c =>
    cases c <;> cases kind <;> cases rel <;> cases isProtected <;>
      exact ⟨fun p' => by cases p' <;> simp [TbLocationState.performAccess, performPermAccess,
        TbAccessRelatedness.isForeign, childReadPerm, childWritePerm, foreignReadPerm,
        foreignWritePerm, TbPermission.isDisabled, tbKindOfMir, tbPermOfMir],
        by decide⟩
  | reservedIM =>
    cases kind <;> cases rel <;> cases isProtected <;>
      exact ⟨fun p' => by cases p' <;> simp [TbLocationState.performAccess, performPermAccess,
        TbAccessRelatedness.isForeign, childReadPerm, childWritePerm, foreignReadPerm,
        foreignWritePerm, TbPermission.isDisabled, tbKindOfMir, tbPermOfMir],
        by decide⟩
  | unique =>
    cases kind <;> cases rel <;> cases isProtected <;>
      exact ⟨fun p' => by cases p' <;> simp [TbLocationState.performAccess, performPermAccess,
        TbAccessRelatedness.isForeign, childReadPerm, childWritePerm, foreignReadPerm,
        foreignWritePerm, TbPermission.isDisabled, tbKindOfMir, tbPermOfMir],
        by decide⟩
  | frozen =>
    cases kind <;> cases rel <;> cases isProtected <;>
      exact ⟨fun p' => by cases p' <;> simp [TbLocationState.performAccess, performPermAccess,
        TbAccessRelatedness.isForeign, childReadPerm, childWritePerm, foreignReadPerm,
        foreignWritePerm, TbPermission.isDisabled, tbKindOfMir, tbPermOfMir],
        by decide⟩

/-- Direct operational equations for unmodified `applyUnwindAction`. -/
theorem applyUnwindAction_unreachable_eq_ub (s : MachineState)
    (locs : List LocalSlot) (mem : Memory) :
    applyUnwindAction s locs mem .unreachable = .faulted .ub := rfl

theorem applyUnwindAction_terminate_eq_abort (s : MachineState)
    (locs : List LocalSlot) (mem : Memory) :
    applyUnwindAction s locs mem .terminate = .halted .abort := rfl

theorem applyUnwindAction_cleanup_eq_running (s : MachineState)
    (locs : List LocalSlot) (mem : Memory) (cleanupBb : Nat) :
    applyUnwindAction s locs mem (.cleanup cleanupBb) =
      .running { frame := { s.frame with blockIdx := cleanupBb, stmtIdx := 0, locals := locs }
                 memory := mem } := rfl

theorem unwindFromCallStack_nil_eq_panic (mem : Memory) :
    unwindFromCallStack [] mem = .halted .panic := rfl

theorem unwindFromCallStack_unreachable_eq_ub (caller : SavedCallerFrame)
    (rest : List SavedCallerFrame) (mem : Memory)
    (hUnw : caller.returnUnwind = .unreachable) :
    unwindFromCallStack (caller :: rest) mem = .faulted .ub := by
  unfold unwindFromCallStack; rw [hUnw]

theorem unwindFromCallStack_terminate_eq_abort (caller : SavedCallerFrame)
    (rest : List SavedCallerFrame) (mem : Memory)
    (hUnw : caller.returnUnwind = .terminate) :
    unwindFromCallStack (caller :: rest) mem = .halted .abort := by
  unfold unwindFromCallStack; rw [hUnw]

/-- **Fail-closed diverging-return UB on unmodified `V2026_06_01.MirSemantics`**:
when the current block's terminator is `.return_` with an initialized return local,
no frame-deallocation protector conflict, and a caller frame with `isDiverging = true`
(i.e. `callCont4OfSavedFrame caller` has `onRet = none`), `stepMirFn` fails with
`MirStepNode.fail .ub` and `¬ MirWpConverges`. -/
theorem stepMirFn_return_diverging_ub {body : CapturedMir} {s : MachineState}
    {bb : BasicBlockData} {retVal : Value} {caller : SavedCallerFrame}
    {rest : List SavedCallerFrame}
    (hPhase : body.phase = .runtimeOptimized)
    (hActive : s.memory.activeCallee = none)
    (hBlk : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hStmt : s.frame.stmtIdx = length bb.statements)
    (hTerm : bb.terminator.kind = .return_)
    (hRet : get? s.frame.locals 0 = some (.init retVal))
    (hStack : s.memory.callStack = caller :: rest)
    (hDiv : caller.isDiverging = true) :
    stepMirFn body s = MirStepNode.fail .ub := by
  have hStmtNone : get? bb.statements s.frame.stmtIdx = none := by
    rw [hStmt]
    clear hStmt hTerm hRet hStack hDiv hActive hBlk hPhase
    induction bb.statements with
    | nil => rfl
    | cons _ tl ih => exact ih
  unfold stepMirFn
  rw [hActive]
  dsimp only [Option.getD]
  rw [hPhase, hBlk]
  dsimp only
  rw [hStmtNone, hStmt]
  simp only [beq_self_eq_true, ↓reduceIte, evalTerminator, hTerm, hRet, hStack, hDiv]
  cases hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
      (length (caller :: rest)) (length s.frame.locals) <;> rfl

theorem not_mirWpConverges_return_diverging_ub {body : CapturedMir} {s : MachineState}
    {bb : BasicBlockData} {retVal : Value} {caller : SavedCallerFrame}
    {rest : List SavedCallerFrame} {post : MirOutcome → Prop}
    (hPhase : body.phase = .runtimeOptimized)
    (hActive : s.memory.activeCallee = none)
    (hBlk : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hStmt : s.frame.stmtIdx = length bb.statements)
    (hTerm : bb.terminator.kind = .return_)
    (hRet : get? s.frame.locals 0 = some (.init retVal))
    (hStack : s.memory.callStack = caller :: rest)
    (hDiv : caller.isDiverging = true) :
    ¬ MirWpConverges body s post :=
  not_mirWpConverges_of_step_fail
    (stepMirFn_return_diverging_ub hPhase hActive hBlk hStmt hTerm hRet hStack hDiv)

/-- **Fail-closed `UnwindAction.unreachable` assert UB on unmodified `V2026_06_01.MirSemantics`**:
when `.assert cond expected target .unreachable` evaluates `cond` to a scalar whose
value disagrees with `expected`, `stepMirFn` fails with `MirStepNode.fail .ub` and
`¬ MirWpConverges`. -/
theorem stepMirFn_assert_unreachable_ub {body : CapturedMir} {s : MachineState}
    {bb : BasicBlockData} {cond : Operand} {expected : Bool} {target : BasicBlockIdx}
    {sc : ScalarInt} {locals' : List LocalSlot}
    (hPhase : body.phase = .runtimeOptimized)
    (hActive : s.memory.activeCallee = none)
    (hBlk : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hStmt : s.frame.stmtIdx = length bb.statements)
    (hTerm : bb.terminator.kind = .assert cond expected target .unreachable)
    (hEval :
      evalOperand s.frame.locals cond s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals (callStack := s.memory.callStack) = .ok (.scalar sc) locals')
    (hNe : Nat.beq sc.bits (if expected then 1 else 0) = false) :
    stepMirFn body s = MirStepNode.fail .ub := by
  have hStmtNone : get? bb.statements s.frame.stmtIdx = none := by
    rw [hStmt]
    clear hStmt hTerm hEval hNe hActive hBlk hPhase
    induction bb.statements with
    | nil => rfl
    | cons _ tl ih => exact ih
  unfold stepMirFn
  rw [hActive]
  dsimp only [Option.getD]
  rw [hPhase, hBlk]
  dsimp only
  rw [hStmtNone, hStmt]
  cases expected with
  | true =>
    simp only [beq_self_eq_true, ↓reduceIte, evalTerminator, hTerm, hEval]
    simp only [↓reduceIte] at hNe
    rw [hNe]
    rfl
  | false =>
    simp only [beq_self_eq_true, ↓reduceIte, evalTerminator, hTerm, hEval]
    simp only [Bool.false_eq_true, ↓reduceIte] at hNe
    rw [hNe]
    rfl

theorem not_mirWpConverges_assert_unreachable_ub {body : CapturedMir} {s : MachineState}
    {bb : BasicBlockData} {cond : Operand} {expected : Bool} {target : BasicBlockIdx}
    {sc : ScalarInt} {locals' : List LocalSlot} {post : MirOutcome → Prop}
    (hPhase : body.phase = .runtimeOptimized)
    (hActive : s.memory.activeCallee = none)
    (hBlk : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hStmt : s.frame.stmtIdx = length bb.statements)
    (hTerm : bb.terminator.kind = .assert cond expected target .unreachable)
    (hEval :
      evalOperand s.frame.locals cond s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals (callStack := s.memory.callStack) = .ok (.scalar sc) locals')
    (hNe : Nat.beq sc.bits (if expected then 1 else 0) = false) :
    ¬ MirWpConverges body s post :=
  not_mirWpConverges_of_step_fail
    (stepMirFn_assert_unreachable_ub hPhase hActive hBlk hStmt hTerm hEval hNe)

/-- **Inline-callee diverging-return UB on unmodified `V2026_06_01.MirSemantics`**:
the REAL inline-call shape of a diverging `TerminatorKind.call` (`target = none`).
After `pushDivergingCalleeFrame`, `Memory.activeCallee = some callee` and the
saved caller frame has `isDiverging = true`; when `callee` reaches
`TerminatorKind.return_`, `stepMirFn` (executing `activeCallee`, NOT the root
`body`) fails with `MirStepNode.fail .ub`. Unlike `stepMirFn_return_diverging_ub`
(root frame, `activeCallee = none`), this covers states actually reachable from
a caller's diverging `TerminatorKind.call`. -/
theorem stepMirFn_inline_return_diverging_ub {body callee : CapturedMir} {s : MachineState}
    {bb : BasicBlockData} {retVal : Value} {caller : SavedCallerFrame}
    {rest : List SavedCallerFrame}
    (hActive : s.memory.activeCallee = some callee)
    (hPhase : callee.phase = .runtimeOptimized)
    (hBlk : get? callee.basicBlocks s.frame.blockIdx = some bb)
    (hStmt : s.frame.stmtIdx = length bb.statements)
    (hTerm : bb.terminator.kind = .return_)
    (hRet : get? s.frame.locals 0 = some (.init retVal))
    (hStack : s.memory.callStack = caller :: rest)
    (hDiv : caller.isDiverging = true) :
    stepMirFn body s = MirStepNode.fail .ub := by
  have hStmtNone : get? bb.statements s.frame.stmtIdx = none := by
    rw [hStmt]
    clear hStmt hTerm hRet hStack hDiv hActive hBlk hPhase
    induction bb.statements with
    | nil => rfl
    | cons _ tl ih => exact ih
  unfold stepMirFn
  rw [hActive]
  dsimp only [Option.getD]
  rw [hPhase, hBlk]
  dsimp only
  rw [hStmtNone, hStmt]
  simp only [beq_self_eq_true, ↓reduceIte, evalTerminator, hTerm, hRet, hStack, hDiv]
  cases hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
      (length (caller :: rest)) (length s.frame.locals) <;> rfl

theorem not_mirWpConverges_inline_return_diverging_ub {body callee : CapturedMir}
    {s : MachineState} {bb : BasicBlockData} {retVal : Value} {caller : SavedCallerFrame}
    {rest : List SavedCallerFrame} {post : MirOutcome → Prop}
    (hActive : s.memory.activeCallee = some callee)
    (hPhase : callee.phase = .runtimeOptimized)
    (hBlk : get? callee.basicBlocks s.frame.blockIdx = some bb)
    (hStmt : s.frame.stmtIdx = length bb.statements)
    (hTerm : bb.terminator.kind = .return_)
    (hRet : get? s.frame.locals 0 = some (.init retVal))
    (hStack : s.memory.callStack = caller :: rest)
    (hDiv : caller.isDiverging = true) :
    ¬ MirWpConverges body s post :=
  not_mirWpConverges_of_step_fail
    (stepMirFn_inline_return_diverging_ub hActive hPhase hBlk hStmt hTerm hRet hStack hDiv)

/-- Transport `CallStackUnwind.wpCallSite` over `mirDetWpOps body` directly into
`Anneal.MirFuelFree.MirWpConverges`. -/
theorem mirWpConverges_of_wpCallSite {Mem Val : Type}
    {body : CapturedMir}
    {adapter : CalleeMachineAdapter MachineState MirOutcome Mem Val}
    {cont : CallCont4} {isCleanupBb : Nat → Bool} {frameTags : List Nat}
    {onNormal : Nat → Val → Mem → RangedBorrowTree → Prop}
    {onCleanup : Nat → Mem → RangedBorrowTree → Prop}
    {onUnwindExit : Mem → RangedBorrowTree → Prop}
    {onTerminate : Mem → RangedBorrowTree → Prop}
    {m₀ : Mem} {t₀ : RangedBorrowTree}
    (hWp : wpCallSite (wops := mirDetWpOps body) adapter cont isCleanupBb frameTags
      onNormal onCleanup onUnwindExit onTerminate m₀ t₀) :
    MirWpConverges body (adapter.mkEntry m₀ t₀)
      (fun out =>
        match adapter.classifyOut out with
        | none => False
        | some (.returned retVal m₁ t₁) =>
          match exitFrameWithProtectors t₁ frameTags with
          | ⟨tRel, .Released⟩ =>
            match evalCallCont4Dispatch isCleanupBb cont (.returned retVal m₁ tRel) with
            | .stepNormal retBb rv m' t' => onNormal retBb rv m' t'
            | _ => False
          | _ => False
        | some (.unwound m₁ t₁) =>
          match exitFrameWithProtectors t₁ frameTags with
          | ⟨tRel, .Released⟩ =>
            match evalCallCont4Dispatch isCleanupBb cont
                (FrameExitOutcome.unwound (Val := Val) m₁ tRel) with
            | .stepCleanup cleanupBb m' t' => onCleanup cleanupBb m' t'
            | .exitUnwind m' t' => onUnwindExit m' t'
            | .exitTerminate m' t' => onTerminate m' t'
            | _ => False
          | _ => False
        | some (.abortTerminate m₁ t₁) =>
          match evalCallCont4Dispatch isCleanupBb cont
              (FrameExitOutcome.abortTerminate (Val := Val) m₁ t₁) with
          | .exitTerminate m' t' => onTerminate m' t'
          | _ => False) :=
  mirWpConverges_of_wpStateOk hWp

/-- Transport `CallSpecCut` (with `⟨some retBb, .cleanup cleanupBb⟩` continuation)
over `mirDetWpOps body` directly into `MirFuelFree.MirWpConverges`. -/
theorem mirWpConverges_of_callSpecCut_normal_cleanup {Mem Addr Byte Val : Type}
    [ByteStoreOps Mem Addr Byte]
    {body : CapturedMir}
    {adapter : CalleeMachineAdapter MachineState MirOutcome Mem Val}
    {spec : CallSpec Mem Addr Val}
    {isCleanupBb : Nat → Bool} {retBb cleanupBb : Nat}
    {onNormal : Nat → Val → Mem → RangedBorrowTree → Prop}
    {onCleanup : Nat → Mem → RangedBorrowTree → Prop}
    {onUnwindExit : Mem → RangedBorrowTree → Prop}
    {onTerminate : Mem → RangedBorrowTree → Prop}
    {m₀ : Mem} {t₀ : RangedBorrowTree}
    (hCut : CallSpecCut (wops := mirDetWpOps body) adapter spec)
    (hPre : spec.pre m₀ t₀)
    (hCleanValid : isCleanupBb cleanupBb = true)
    (hNormal : ∀ retVal m₁ tRel,
      spec.canNormal = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      (∀ t, natListMem t spec.frameTags = true → natListMem t tRel.protectedTags = false) →
      spec.postRet retVal m₁ tRel →
      onNormal retBb retVal m₁ tRel)
    (hCleanup : ∀ m₁ tRel,
      spec.canUnwind = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      (∀ t, natListMem t spec.frameTags = true → natListMem t tRel.protectedTags = false) →
      spec.postUnwind m₁ tRel →
      onCleanup cleanupBb m₁ tRel)
    (hAbort : ∀ m₁ t₁,
      spec.canAbort = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      spec.postAbort m₁ t₁ →
      onTerminate m₁ t₁) :
    MirWpConverges body (adapter.mkEntry m₀ t₀)
      (fun out =>
        match adapter.classifyOut out with
        | none => False
        | some (.returned retVal m₁ t₁) =>
          match exitFrameWithProtectors t₁ spec.frameTags with
          | ⟨tRel, .Released⟩ =>
            match evalCallCont4Dispatch isCleanupBb ⟨some retBb, .cleanup cleanupBb⟩
                (.returned retVal m₁ tRel) with
            | .stepNormal bb rv m' t' => onNormal bb rv m' t'
            | _ => False
          | _ => False
        | some (.unwound m₁ t₁) =>
          match exitFrameWithProtectors t₁ spec.frameTags with
          | ⟨tRel, .Released⟩ =>
            match evalCallCont4Dispatch isCleanupBb ⟨some retBb, .cleanup cleanupBb⟩
                (FrameExitOutcome.unwound (Val := Val) m₁ tRel) with
            | .stepCleanup bb m' t' => onCleanup bb m' t'
            | .exitUnwind m' t' => onUnwindExit m' t'
            | .exitTerminate m' t' => onTerminate m' t'
            | _ => False
          | _ => False
        | some (.abortTerminate m₁ t₁) =>
          match evalCallCont4Dispatch isCleanupBb ⟨some retBb, .cleanup cleanupBb⟩
              (FrameExitOutcome.abortTerminate (Val := Val) m₁ t₁) with
          | .exitTerminate m' t' => onTerminate m' t'
          | _ => False) :=
  mirWpConverges_of_wpCallSite
    (callSpecCut_call_normal_cleanup (wops := mirDetWpOps body) hCut hPre hCleanValid hNormal hCleanup hAbort)

/-- Transport `CallSpecCut` (with `⟨some retBb, .continue_⟩` continuation) over
`mirDetWpOps body` directly into `MirFuelFree.MirWpConverges`. -/
theorem mirWpConverges_of_callSpecCut_normal_continue {Mem Addr Byte Val : Type}
    [ByteStoreOps Mem Addr Byte]
    {body : CapturedMir}
    {adapter : CalleeMachineAdapter MachineState MirOutcome Mem Val}
    {spec : CallSpec Mem Addr Val}
    {isCleanupBb : Nat → Bool} {retBb : Nat}
    {onNormal : Nat → Val → Mem → RangedBorrowTree → Prop}
    {onCleanup : Nat → Mem → RangedBorrowTree → Prop}
    {onUnwindExit : Mem → RangedBorrowTree → Prop}
    {onTerminate : Mem → RangedBorrowTree → Prop}
    {m₀ : Mem} {t₀ : RangedBorrowTree}
    (hCut : CallSpecCut (wops := mirDetWpOps body) adapter spec)
    (hPre : spec.pre m₀ t₀)
    (hNormal : ∀ retVal m₁ tRel,
      spec.canNormal = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      (∀ t, natListMem t spec.frameTags = true → natListMem t tRel.protectedTags = false) →
      spec.postRet retVal m₁ tRel →
      onNormal retBb retVal m₁ tRel)
    (hUnwind : ∀ m₁ tRel,
      spec.canUnwind = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      (∀ t, natListMem t spec.frameTags = true → natListMem t tRel.protectedTags = false) →
      spec.postUnwind m₁ tRel →
      onUnwindExit m₁ tRel)
    (hAbort : ∀ m₁ t₁,
      spec.canAbort = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      spec.postAbort m₁ t₁ →
      onTerminate m₁ t₁) :
    MirWpConverges body (adapter.mkEntry m₀ t₀)
      (fun out =>
        match adapter.classifyOut out with
        | none => False
        | some (.returned retVal m₁ t₁) =>
          match exitFrameWithProtectors t₁ spec.frameTags with
          | ⟨tRel, .Released⟩ =>
            match evalCallCont4Dispatch isCleanupBb ⟨some retBb, .continue_⟩
                (.returned retVal m₁ tRel) with
            | .stepNormal bb rv m' t' => onNormal bb rv m' t'
            | _ => False
          | _ => False
        | some (.unwound m₁ t₁) =>
          match exitFrameWithProtectors t₁ spec.frameTags with
          | ⟨tRel, .Released⟩ =>
            match evalCallCont4Dispatch isCleanupBb ⟨some retBb, .continue_⟩
                (FrameExitOutcome.unwound (Val := Val) m₁ tRel) with
            | .stepCleanup bb m' t' => onCleanup bb m' t'
            | .exitUnwind m' t' => onUnwindExit m' t'
            | .exitTerminate m' t' => onTerminate m' t'
            | _ => False
          | _ => False
        | some (.abortTerminate m₁ t₁) =>
          match evalCallCont4Dispatch isCleanupBb ⟨some retBb, .continue_⟩
              (FrameExitOutcome.abortTerminate (Val := Val) m₁ t₁) with
          | .exitTerminate m' t' => onTerminate m' t'
          | _ => False) :=
  mirWpConverges_of_wpCallSite
    (callSpecCut_call_normal_continue (wops := mirDetWpOps body)
      (isCleanupBb := isCleanupBb) (onCleanup := onCleanup)
      hCut hPre hNormal hUnwind hAbort)

/-- Sound `accessed` projection for unmodified `V2026_06_01.MirSemantics.BorrowEntry`.
`BorrowEntry` stores a single `perm : TreeBorrowPerm` and NO `accessed` bit, and its
per-node semantics `treeBorrowNodeAccess` coincides EXACTLY with
`TbLocationState.performAccess ⟨tbPermOfMir perm, true⟩` on every non-disabled node
(`treeBorrowNodeAccess_agrees_with_performAccess`), i.e. MIR treats every node as
ACCESSED. The projection must therefore set `accessed := true` for every borrow:
marking `.reservedFrz false` as unaccessed (the A2 choice) is UNSOUND in the safety
direction, because `RefFrame` lets a protected UNACCESSED `Reserved` node absorb a
foreign write silently (`.Success ⟨.Disabled, false⟩`) while unmodified MIR faults
(`treeBorrowNodeAccess .write .foreignAccess (.reservedFrz false) true = .ub`) — and
Miri agrees with MIR here, since `Retag(FnEntry)` performs an initial read through the
fresh protected child (`evalFnEntryRetag` / `freezeTreeBorrowsOnReadAtProj`), so that
child IS accessed. See `borrowEntryAccessed_unaccessed_reserved_unsound`. -/
@[reducible] def borrowEntryAccessed (_e : BorrowEntry) : Bool := true

/-- **Exact `accessed`-bit contrast between unmodified `V2026_06_01.MirSemantics` and
`Anneal.RefFrame.TbLocationState`**: because `BorrowEntry` omits a separate `accessed`
field, `treeBorrowNodeAccess` agrees identically with `TbLocationState.performAccess` on
every accessed node (`treeBorrowNodeAccess_agrees_with_performAccess`), and on an
unaccessed `.reservedFrz false` child write (`⟨.Reserved false, false⟩ → ⟨.Unique, true⟩`),
while conservatively rejecting protected foreign writes to `.frozen` as `.ub` even when
full Tree Borrows permits an *unaccessed* protected `.Frozen` node (`accessed = false`) to
transition to `.Disabled` without UB (sound over-approximation). -/
theorem mirSemantics_vs_refFrame_accessed_coarsening :
    (TbLocationState.performAccess ⟨.ReservedFrz false, false⟩ .Write .LocalAccess true =
      .Success ⟨.Unique, true⟩ ∧
     treeBorrowNodeAccess .write .localAccess (.reservedFrz false) true = .transition .unique) ∧
    (TbLocationState.performAccess ⟨.Frozen, false⟩ .Write .ForeignAccess true =
      .Success ⟨.Disabled, false⟩ ∧
     treeBorrowNodeAccess .write .foreignAccess .frozen true = .ub) := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- Project unmodified `V2026_06_01.MirSemantics` `{BorrowEntry, activeProtectors}`
directly into an `Anneal.RefFrame.RangedBorrowTree` over byte span `[0, rangeLen)`.
- Tag `0` is the root stack-allocation owner (`parent := none`, `.Unique`).
- Each live `BorrowEntry` in `borrows` maps to `TbTopoNode ⟨e.tag, some (e.parentTag.getD 0)⟩`
  with permission `tbPermOfMir e.perm` and `accessed := borrowEntryAccessed e`.
- `protectedTags` contains precisely those `e.tag` whose `e.protector = some pid`
  with `pid ∈ activeProtectors`. -/
def rangedBorrowTreeOfMirBorrows (borrows : List BorrowEntry)
    (activeProtectors : List Nat) (rangeLen : Nat) : RangedBorrowTree :=
  let topo : List TbTopoNode :=
    ⟨0, none⟩ :: borrows.map (fun e => ⟨e.tag, some (e.parentTag.getD 0)⟩)
  let protTags : List Nat :=
    (borrows.filter (fun e =>
      match e.protector with
      | some pid => natListMem pid activeProtectors
      | none => false)).map (fun e => e.tag)
  let states : List (Nat × TbLocationState) :=
    (0, ⟨.Unique, true⟩) ::
      borrows.map (fun e =>
        (e.tag, ⟨tbPermOfMir e.perm, borrowEntryAccessed e⟩))
  { topology := topo
    protectedTags := protTags
    segments := [⟨0, rangeLen, states⟩] }

/-- **Why `borrowEntryAccessed` must be constantly `true`**: (1) node level — a protected
`.reservedFrz false` foreign write is MIR `.ub`; the unaccessed `RefFrame` state accepts
it silently, while the accessed state reports `.ProtectedDisabled` exactly like MIR;
(2) tree level — on the projection of the REAL post-`Retag(FnEntry)` borrow chain
(`child 2` protected `.reservedFrz false` under `root 1`) extended by a sibling `&mut`
tag `3`, a write through tag `3` is a FOREIGN write to protected tag `2`: the sound
(`accessed := true`) projection fails with `.ProtectedDisabled (.ReservedFrz false)`,
agreeing with MIR's `.ub`, whereas the unaccessed encoding would complete silently. -/
theorem borrowEntryAccessed_unaccessed_reserved_unsound :
    (treeBorrowNodeAccess .write .foreignAccess (.reservedFrz false) true = .ub ∧
     TbLocationState.performAccess ⟨.ReservedFrz false, false⟩ .Write .ForeignAccess true =
       .Success ⟨.Disabled, false⟩ ∧
     TbLocationState.performAccess ⟨tbPermOfMir (.reservedFrz false), true⟩ .Write
       .ForeignAccess true =
       .Error ⟨.Disabled, true⟩ (.ProtectedDisabled (.ReservedFrz false))) ∧
    (let child : BorrowEntry :=
       { tag := 2, targetLocal := 1, targetFrameDepth := 0, targetProjection := [],
         perm := .reservedFrz false, protector := some 1, parentTag := some 1 }
     let sib : BorrowEntry :=
       { tag := 3, targetLocal := 1, targetFrameDepth := 0, targetProjection := [],
         perm := .unique, parentTag := some 1 }
     let root : BorrowEntry :=
       { tag := 1, targetLocal := 1, targetFrameDepth := 0, targetProjection := [],
         perm := .unique }
     let tSound := rangedBorrowTreeOfMirBorrows [sib, child, root] [1] 4
     let tUnacc : RangedBorrowTree :=
       { tSound with
         segments := [⟨0, 4, [(0, ⟨.Unique, true⟩), (3, ⟨.Unique, true⟩),
           (2, ⟨.ReservedFrz false, false⟩), (1, ⟨.Unique, true⟩)]⟩] }
     (performRangedAccess tSound 0 4 3 .Write .VisitChildrenOfAccessed).status =
       .TransitionError 0 4 2 (.ProtectedDisabled (.ReservedFrz false)) ∧
     (performRangedAccess tUnacc 0 4 3 .Write .VisitChildrenOfAccessed).status = .Completed) :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- When `Memory.activeProtectors = []` (e.g. after `TerminatorKind.return_`
restores an empty caller protector set), `rangedBorrowTreeOfMirBorrows` has
empty `protectedTags = []`. -/
theorem rangedBorrowTreeOfMirBorrows_protectedTags_nil (borrows : List BorrowEntry)
    (rangeLen : Nat) :
    (rangedBorrowTreeOfMirBorrows borrows [] rangeLen).protectedTags = [] := by
  unfold rangedBorrowTreeOfMirBorrows
  dsimp only
  induction borrows with
  | nil => rfl
  | cons e rest ih =>
    cases hP : e.protector with
    | none => simp only [List.filter, hP]; exact ih
    | some pid => simp only [List.filter, hP, natListMem, List.foldr]; exact ih

/-- Head-entry permission & protector projection: the most recently pushed
`BorrowEntry` (`e :: rest`, e.g. from `evalFnEntryRetag`) projects its exact
permission `tbPermOfMir e.perm` at `e.tag` (when `e.tag ≠ 0`) and appears at
the head of `protectedTags` whenever `e.protector = some pid` is active in
`activeProtectors`. -/
theorem rangedBorrowTreeOfMirBorrows_head_protected (e : BorrowEntry)
    (rest : List BorrowEntry) (activeProtectors : List Nat) (rangeLen pid : Nat)
    (hTagNe0 : e.tag ≠ 0)
    (hProt : e.protector = some pid)
    (hActive : natListMem pid activeProtectors = true) :
    (rangedBorrowTreeOfMirBorrows (e :: rest) activeProtectors rangeLen).protectedTags =
      e.tag :: (rangedBorrowTreeOfMirBorrows rest activeProtectors rangeLen).protectedTags ∧
    lookupLocState e.tag
      (match (rangedBorrowTreeOfMirBorrows (e :: rest) activeProtectors rangeLen).segments with
       | seg :: _ => seg.nodeStates | [] => []) =
      some ⟨tbPermOfMir e.perm, true⟩ := by
  have hNe : Nat.beq 0 e.tag = false := by
    cases hB : Nat.beq 0 e.tag with
    | false => rfl
    | true => exact False.elim (hTagNe0 (Nat.beq_eq.mp hB).symm)
  unfold rangedBorrowTreeOfMirBorrows
  simp only [List.filter, hProt, hActive, List.map, lookupLocState, List.foldr, hNe,
    Nat.beq_refl, Bool.false_eq_true, ↓reduceIte, and_self]

/-- **Exact `Retag(FnEntry)` → `exitFrameWithProtectors` refinement**: for the
2-tag borrow chain `[child{tag:=2, parentTag:=some 1, protector:=some 1, perm:=pChild},
root{tag:=1, parentTag:=none, protector:=none, perm:=.unique}]` produced by
unmodified `V2026_06_01.MirSemantics.evalFnEntryRetag` + deref write (`pChild = .unique`
or `.reservedFrz false`), projecting via `rangedBorrowTreeOfMirBorrows` and calling
`exitFrameWithProtectors _ [2]` succeeds with `.Released` and strips `protectedTags`
to `[]`, matching `rangedBorrowTreeOfMirBorrows borrows [] rangeLen`. -/
theorem rangedBorrowTreeOfMirBorrows_fnEntry_release_unique
    (child root : BorrowEntry) (rangeLen : Nat)
    (hChildTag : child.tag = 2) (hChildParent : child.parentTag = some 1)
    (hChildProt : child.protector = some 1) (hChildPerm : child.perm = .unique)
    (hRootTag : root.tag = 1) (hRootParent : root.parentTag = none)
    (hRootProt : root.protector = none) (hRootPerm : root.perm = .unique) :
    let tActive := rangedBorrowTreeOfMirBorrows [child, root] [1] rangeLen
    let rel := exitFrameWithProtectors tActive [2]
    tActive.protectedTags = [2] ∧
    rel.status = .Released ∧
    rel.tree.protectedTags = [] ∧
    rel.tree = rangedBorrowTreeOfMirBorrows [child, root] [] rangeLen := by
  cases child; cases root
  dsimp only at hChildTag hChildParent hChildProt hChildPerm hRootTag hRootParent hRootProt hRootPerm
  subst hChildTag; subst hChildParent; subst hChildProt; subst hChildPerm
  subst hRootTag; subst hRootParent; subst hRootProt; subst hRootPerm
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Exact fat-pointer `Retag(FnEntry)` (`attachBorrowProtector`) → `exitFrameWithProtectors`
refinement**: on a `&mut [T]` fat pointer, unmodified `V2026_06_01.MirSemantics.evalStmt (.retag .fnEntry)`
attaches `protector := some 1` directly onto the slice borrow entry (`tag := 1, parentTag := none,
perm := .unique`) and pushes `1` onto `activeProtectors`. Projecting via
`rangedBorrowTreeOfMirBorrows` yields `protectedTags = [1]`, and `exitFrameWithProtectors _ [1]`
succeeds with `.Released` and strips `protectedTags` to `[]`, matching `activeProtectors = []`. -/
theorem rangedBorrowTreeOfMirBorrows_attachProtector_release_unique
    (entry : BorrowEntry) (rangeLen : Nat)
    (hTag : entry.tag = 1) (hParent : entry.parentTag = none)
    (hProt : entry.protector = some 1) (hPerm : entry.perm = .unique) :
    let tActive := rangedBorrowTreeOfMirBorrows [entry] [1] rangeLen
    let rel := exitFrameWithProtectors tActive [1]
    tActive.protectedTags = [1] ∧
    rel.status = .Released ∧
    rel.tree.protectedTags = [] ∧
    rel.tree = rangedBorrowTreeOfMirBorrows [entry] [] rangeLen := by
  cases entry
  dsimp only at hTag hParent hProt hPerm
  subst hTag; subst hParent; subst hProt; subst hPerm
  exact ⟨rfl, rfl, rfl, rfl⟩


/-! ### Per-Allocation `BorrowEntry` → `RangedBorrowTree` Projection

`rangedBorrowTreeOfMirBorrows` places EVERY `BorrowEntry` into ONE tree over ONE byte
span, regardless of `targetFrameDepth` / `targetLocal` / `allocDead`. Unmodified
`V2026_06_01.MirSemantics` keeps borrows of DISTINCT allocations independent (the
`(targetFrameDepth, targetLocal)` pair identifies the allocation), so the unfiltered
projection is unsound on multi-allocation states: two protected `&mut` borrows of
distinct locals become sibling nodes, and a protector-release write through one
spuriously reports `.ProtectedDisabled` on the other (see
`rangedBorrowTreeOfMirBorrows_cross_alloc_spurious` below).
`rangedBorrowTreeOfMirAlloc` restricts the projection to the live borrows of a single
allocation, agreeing with `rangedBorrowTreeOfMirBorrows` whenever every borrow already
targets that allocation. -/

/-- Live borrows of allocation `(depth, localIdx)`. -/
def mirBorrowsOfAlloc (borrows : List BorrowEntry) (depth localIdx : Nat) :
    List BorrowEntry :=
  borrows.filter (fun e =>
    Nat.beq e.targetFrameDepth depth && Nat.beq e.targetLocal localIdx && !e.allocDead)

/-- Sound per-allocation projection of `{BorrowEntry, activeProtectors}` into a
`RangedBorrowTree` over `[0, rangeLen)` of allocation `(depth, localIdx)`. -/
def rangedBorrowTreeOfMirAlloc (borrows : List BorrowEntry) (activeProtectors : List Nat)
    (depth localIdx rangeLen : Nat) : RangedBorrowTree :=
  rangedBorrowTreeOfMirBorrows (mirBorrowsOfAlloc borrows depth localIdx)
    activeProtectors rangeLen

/-- `mirBorrowsOfAlloc` is the identity on borrow lists that only target the live
allocation `(depth, localIdx)`. -/
theorem mirBorrowsOfAlloc_eq_self (borrows : List BorrowEntry) (depth localIdx : Nat)
    (hAll : ∀ e ∈ borrows,
      e.targetFrameDepth = depth ∧ e.targetLocal = localIdx ∧ e.allocDead = false) :
    mirBorrowsOfAlloc borrows depth localIdx = borrows := by
  unfold mirBorrowsOfAlloc
  induction borrows with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨hD, hL, hA⟩ := hAll e (List.mem_cons_self ..)
    have hKeep : (Nat.beq e.targetFrameDepth depth && Nat.beq e.targetLocal localIdx &&
        !e.allocDead) = true := by
      rw [hD, hL, hA, Nat.beq_refl, Nat.beq_refl]; rfl
    simp only [List.filter, hKeep]
    rw [ih (fun e' h' => hAll e' (List.mem_cons_of_mem _ h'))]

/-- On single-allocation borrow lists, the sound projection coincides with
`rangedBorrowTreeOfMirBorrows` (so every A1 single-allocation refinement carries over). -/
theorem rangedBorrowTreeOfMirAlloc_eq_of_single_alloc (borrows : List BorrowEntry)
    (activeProtectors : List Nat) (depth localIdx rangeLen : Nat)
    (hAll : ∀ e ∈ borrows,
      e.targetFrameDepth = depth ∧ e.targetLocal = localIdx ∧ e.allocDead = false) :
    rangedBorrowTreeOfMirAlloc borrows activeProtectors depth localIdx rangeLen =
      rangedBorrowTreeOfMirBorrows borrows activeProtectors rangeLen := by
  unfold rangedBorrowTreeOfMirAlloc
  rw [mirBorrowsOfAlloc_eq_self borrows depth localIdx hAll]

/-- **Cross-allocation isolation**: pushing a borrow of ANY other allocation (or a
dead one) never changes the projected tree of `(depth, localIdx)`. -/
theorem rangedBorrowTreeOfMirAlloc_cons_foreign (e : BorrowEntry)
    (borrows : List BorrowEntry) (activeProtectors : List Nat) (depth localIdx rangeLen : Nat)
    (hForeign : e.targetFrameDepth ≠ depth ∨ e.targetLocal ≠ localIdx ∨ e.allocDead = true) :
    rangedBorrowTreeOfMirAlloc (e :: borrows) activeProtectors depth localIdx rangeLen =
      rangedBorrowTreeOfMirAlloc borrows activeProtectors depth localIdx rangeLen := by
  unfold rangedBorrowTreeOfMirAlloc mirBorrowsOfAlloc
  have hDrop : (Nat.beq e.targetFrameDepth depth && Nat.beq e.targetLocal localIdx &&
      !e.allocDead) = false := by
    rcases hForeign with h | h | h
    · have : Nat.beq e.targetFrameDepth depth = false := by
        cases hB : Nat.beq e.targetFrameDepth depth with
        | false => rfl
        | true => exact False.elim (h (Nat.beq_eq.mp hB))
      rw [this]; rfl
    · have : Nat.beq e.targetLocal localIdx = false := by
        cases hB : Nat.beq e.targetLocal localIdx with
        | false => rfl
        | true => exact False.elim (h (Nat.beq_eq.mp hB))
      rw [this, Bool.and_false, Bool.false_and]
    · rw [h, Bool.not_true, Bool.and_false]
  simp only [List.filter, hDrop]

/-- **Unsoundness witness for the unfiltered projection** (and its repair): two
independently protected `&mut` borrows of DISTINCT locals `1` and `2`. The unfiltered
`rangedBorrowTreeOfMirBorrows` makes them siblings, so releasing tag `2`'s protector
spuriously fails with `.ProtectedDisabled .Unique` on tag `1`; the per-allocation
`rangedBorrowTreeOfMirAlloc` isolates local `2` and releases cleanly. -/
theorem rangedBorrowTreeOfMirBorrows_cross_alloc_spurious :
    let xa : BorrowEntry :=
      { tag := 1, targetLocal := 1, targetFrameDepth := 0, targetProjection := [],
        perm := .unique, protector := some 1 }
    let xb : BorrowEntry :=
      { tag := 2, targetLocal := 2, targetFrameDepth := 0, targetProjection := [],
        perm := .unique, protector := some 2 }
    (exitFrameWithProtectors (rangedBorrowTreeOfMirBorrows [xb, xa] [2, 1] 4) [2]).status =
      .AccessFailure 0 4 1 (.ProtectedDisabled .Unique) ∧
    (exitFrameWithProtectors (rangedBorrowTreeOfMirAlloc [xb, xa] [2, 1] 0 2 4) [2]).status =
      .Released ∧
    (exitFrameWithProtectors (rangedBorrowTreeOfMirAlloc [xb, xa] [2, 1] 0 2 4) [2]).tree =
      rangedBorrowTreeOfMirAlloc [xb, xa] [1] 0 2 4 :=
  ⟨rfl, rfl, rfl⟩

/-! ### Range-Segmented Per-Allocation Projection (`rangeOffset` / `rangeLen`) & General Step Refinement

`rangedBorrowTreeOfMirAlloc` flattens all borrows of allocation `(depth, localIdx)` onto
one segment `[0, rangeLen)`, ignoring per-borrow subslice byte ranges `(rangeOffset,
rangeLen)`. For disjoint partial-range borrows of the SAME allocation (such as `&[u8]` at
`[0..2)` and `&mut [u8]` at `[2..4)` on `callerLocals[12]`), flattening treats them as
overlapping and spuriously reports `.ProtectedDisabled` on protector release.
`rangedBorrowTreeOfMirAllocSegmented` projects each borrow onto its covered byte spans
(marking non-covered spans `(Disabled, false)` exactly as `Anneal.RefFrame.mkSharedTopo3Tree16`
does), reducing identically to `rangedBorrowTreeOfMirAlloc` when all borrows are whole-local. -/

/-- Does `e` cover byte span `[segOff, segOff + segLen)` of its target allocation?
Whole-local borrows (`e.rangeLen = 0`) cover every span; partial-range slice borrows
(`e.rangeLen > 0`) cover spans that overlap `[e.rangeOffset, e.rangeOffset + e.rangeLen)`. -/
def borrowCoversSegment (e : BorrowEntry) (segOff segLen : Nat) : Bool :=
  Nat.beq e.rangeLen 0 ||
    (Nat.blt e.rangeOffset (segOff + segLen) && Nat.blt segOff (e.rangeOffset + e.rangeLen))

/-- **Range-segmented per-allocation projection** of unmodified `V2026_06_01.MirSemantics`
`{BorrowEntry, activeProtectors}` into `Anneal.RefFrame.RangedBorrowTree` across explicit
byte spans `spans : List (Nat × Nat)` of allocation `(depth, localIdx)`. -/
def rangedBorrowTreeOfMirAllocSegmented (borrows : List BorrowEntry)
    (activeProtectors : List Nat) (depth localIdx : Nat)
    (spans : List (Nat × Nat)) : RangedBorrowTree :=
  let allocBorrows := mirBorrowsOfAlloc borrows depth localIdx
  let topo : List TbTopoNode :=
    ⟨0, none⟩ :: allocBorrows.map (fun e => ⟨e.tag, some (e.parentTag.getD 0)⟩)
  let protTags : List Nat :=
    (allocBorrows.filter (fun e =>
      match e.protector with
      | some pid => natListMem pid activeProtectors
      | none => false)).map (fun e => e.tag)
  let segs : List RangeSegment :=
    spans.map (fun (segOff, segLen) =>
      let states : List (Nat × TbLocationState) :=
        (0, ⟨.Unique, true⟩) ::
          allocBorrows.map (fun e =>
            if borrowCoversSegment e segOff segLen then
              (e.tag, ⟨tbPermOfMir e.perm, borrowEntryAccessed e⟩)
            else
              (e.tag, ⟨.Disabled, false⟩))
      ⟨segOff, segLen, states⟩)
  { topology := topo
    protectedTags := protTags
    segments := segs }

/-- When every live borrow on `(depth, localIdx)` is whole-local (`rangeLen = 0`),
the single-span segmented projection equals `rangedBorrowTreeOfMirAlloc` identically. -/
theorem rangedBorrowTreeOfMirAllocSegmented_single_whole (borrows : List BorrowEntry)
    (activeProtectors : List Nat) (depth localIdx rangeLen : Nat)
    (hWhole : ∀ e ∈ mirBorrowsOfAlloc borrows depth localIdx, e.rangeLen = 0) :
    rangedBorrowTreeOfMirAllocSegmented borrows activeProtectors depth localIdx [(0, rangeLen)] =
      rangedBorrowTreeOfMirAlloc borrows activeProtectors depth localIdx rangeLen := by
  unfold rangedBorrowTreeOfMirAllocSegmented rangedBorrowTreeOfMirAlloc rangedBorrowTreeOfMirBorrows
  dsimp only [List.map]
  have hStates :
      ((mirBorrowsOfAlloc borrows depth localIdx).map (fun e =>
        if borrowCoversSegment e 0 rangeLen then
          (e.tag, ({ permission := tbPermOfMir e.perm, accessed := borrowEntryAccessed e } : TbLocationState))
        else (e.tag, ({ permission := .Disabled, accessed := false } : TbLocationState)))) =
      (mirBorrowsOfAlloc borrows depth localIdx).map (fun e =>
        (e.tag, ({ permission := tbPermOfMir e.perm, accessed := borrowEntryAccessed e } : TbLocationState))) := by
    have hAux : ∀ (xs : List BorrowEntry), (∀ e ∈ xs, e.rangeLen = 0) →
        xs.map (fun e =>
          if borrowCoversSegment e 0 rangeLen then
            (e.tag, ({ permission := tbPermOfMir e.perm, accessed := borrowEntryAccessed e } : TbLocationState))
          else (e.tag, ({ permission := .Disabled, accessed := false } : TbLocationState))) =
        xs.map (fun e =>
          (e.tag, ({ permission := tbPermOfMir e.perm, accessed := borrowEntryAccessed e } : TbLocationState))) := by
      intro xs
      induction xs with
      | nil => intro _; rfl
      | cons e rest ih =>
        intro hAll
        have hZero := hAll e (List.mem_cons_self ..)
        have hCov : borrowCoversSegment e 0 rangeLen = true := by
          unfold borrowCoversSegment; rw [hZero]; rfl
        simp only [List.map, hCov, ↓reduceIte]
        rw [ih (fun e' h' => hAll e' (List.mem_cons_of_mem _ h'))]
    exact hAux _ hWhole
  simp only [hStates]

/-- **Cross-allocation isolation for the segmented projection**: pushing any borrow of
another allocation (or a dead borrow) never changes `rangedBorrowTreeOfMirAllocSegmented`. -/
theorem rangedBorrowTreeOfMirAllocSegmented_cons_foreign (e : BorrowEntry)
    (borrows : List BorrowEntry) (activeProtectors : List Nat) (depth localIdx : Nat)
    (spans : List (Nat × Nat))
    (hForeign : e.targetFrameDepth ≠ depth ∨ e.targetLocal ≠ localIdx ∨ e.allocDead = true) :
    rangedBorrowTreeOfMirAllocSegmented (e :: borrows) activeProtectors depth localIdx spans =
      rangedBorrowTreeOfMirAllocSegmented borrows activeProtectors depth localIdx spans := by
  unfold rangedBorrowTreeOfMirAllocSegmented mirBorrowsOfAlloc
  have hDrop : (Nat.beq e.targetFrameDepth depth && Nat.beq e.targetLocal localIdx &&
      !e.allocDead) = false := by
    rcases hForeign with h | h | h
    · have : Nat.beq e.targetFrameDepth depth = false := by
        cases hB : Nat.beq e.targetFrameDepth depth with
        | false => rfl
        | true => exact False.elim (h (Nat.beq_eq.mp hB))
      rw [this]; rfl
    · have : Nat.beq e.targetLocal localIdx = false := by
        cases hB : Nat.beq e.targetLocal localIdx with
        | false => rfl
        | true => exact False.elim (h (Nat.beq_eq.mp hB))
      rw [this, Bool.and_false, Bool.false_and]
    · rw [h, Bool.not_true, Bool.and_false]
  simp only [List.filter, hDrop]

/-- **Partial-range same-allocation disjointness witness (flat vs. segmented)**:
two disjoint protected borrows on the SAME allocation `(0, 12)` (`src` at `[0..2)`
and `dst` at `[2..4)`). The flat 1-segment `rangedBorrowTreeOfMirAlloc` spuriously fails
`exitFrameWithProtectors _ [2]` with `.ProtectedDisabled .Unique`, whereas the
range-segmented `rangedBorrowTreeOfMirAllocSegmented _ _ 0 12 [(0, 2), (2, 2)]`:
1. executes read on `[0..2)` via tag `1` and write on `[2..4)` via tag `2` with
   `.Completed` in BOTH orders and **exact commutation** (`s12.tree = s21.tree`), and
2. releases protector `[2]` cleanly with `.Released`, matching `activeProtectors = [1]`. -/
theorem rangedBorrowTreeOfMirAlloc_partial_range_spurious_vs_segmented :
    let bSrc : BorrowEntry :=
      { tag := 1, targetLocal := 12, targetFrameDepth := 0, targetProjection := [],
        perm := .unique, protector := some 1, rangeOffset := 0, rangeLen := 2 }
    let bDst : BorrowEntry :=
      { tag := 2, targetLocal := 12, targetFrameDepth := 0, targetProjection := [],
        perm := .unique, protector := some 2, rangeOffset := 2, rangeLen := 2 }
    let tFlat := rangedBorrowTreeOfMirAlloc [bDst, bSrc] [2, 1] 0 12 4
    let tSeg := rangedBorrowTreeOfMirAllocSegmented [bDst, bSrc] [2, 1] 0 12 [(0, 2), (2, 2)]
    let s1 := performRangedAccess tSeg 0 2 1 .Read .VisitChildrenOfAccessed
    let s12 := performRangedAccess s1.tree 2 2 2 .Write .VisitChildrenOfAccessed
    let s2 := performRangedAccess tSeg 2 2 2 .Write .VisitChildrenOfAccessed
    let s21 := performRangedAccess s2.tree 0 2 1 .Read .VisitChildrenOfAccessed
    let relSeg := exitFrameWithProtectors s12.tree [2]
    (exitFrameWithProtectors tFlat [2]).status =
      .AccessFailure 0 4 1 (.ProtectedDisabled .Unique) ∧
    s1.status = .Completed ∧ s2.status = .Completed ∧
    s12.status = .Completed ∧ s21.status = .Completed ∧
    s12.tree = s21.tree ∧
    relSeg.status = .Released ∧
    relSeg.tree = rangedBorrowTreeOfMirAllocSegmented [bDst, bSrc] [1] 0 12 [(0, 2), (2, 2)] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `mirBorrowsOfAlloc` drops every list of foreign or dead borrows. -/
theorem mirBorrowsOfAlloc_eq_nil_of_foreign (foreign : List BorrowEntry) (depth localIdx : Nat)
    (hForeign : ∀ e ∈ foreign,
      e.targetFrameDepth ≠ depth ∨ e.targetLocal ≠ localIdx ∨ e.allocDead = true) :
    mirBorrowsOfAlloc foreign depth localIdx = [] := by
  induction foreign with
  | nil => rfl
  | cons e rest ih =>
    have hF := hForeign e (List.mem_cons_self ..)
    have hDrop : (Nat.beq e.targetFrameDepth depth && Nat.beq e.targetLocal localIdx &&
        !e.allocDead) = false := by
      rcases hF with h | h | h
      · have : Nat.beq e.targetFrameDepth depth = false := by
          cases hB : Nat.beq e.targetFrameDepth depth with
          | false => rfl
          | true => exact False.elim (h (Nat.beq_eq.mp hB))
        rw [this]; rfl
      · have : Nat.beq e.targetLocal localIdx = false := by
          cases hB : Nat.beq e.targetLocal localIdx with
          | false => rfl
          | true => exact False.elim (h (Nat.beq_eq.mp hB))
        rw [this, Bool.and_false, Bool.false_and]
      · rw [h, Bool.not_true, Bool.and_false]
    unfold mirBorrowsOfAlloc
    simp only [List.filter, hDrop]
    exact ih (fun e' h' => hForeign e' (List.mem_cons_of_mem _ h'))

/-- **General parametric MIR deref-write ⇒ `performRangedAccess` refinement**:
for ANY allocation `(depth, localIdx)`, ANY positive span `0 < rangeLen`, and ANY tail
`foreign` of borrows on other allocations (or dead borrows), upgrading the two-phase
`Retag(FnEntry)` chain `[child{tag:=2, parentTag:=some 1, protector:=some 1, perm:=.reservedFrz false},
root{tag:=1, parentTag:=none, protector:=none, perm:=.reservedFrz false}] ++ foreign` to
`.unique` (as unmodified `V2026_06_01.MirSemantics` does on a write through tag `2`)
commutes EXACTLY with `performRangedAccess _ 0 rangeLen 2 .Write .VisitChildrenOfAccessed`. -/
theorem rangedBorrowTreeOfMirAlloc_twoTag_write_refines
    (child root : BorrowEntry) (foreign : List BorrowEntry) (depth localIdx rangeLen : Nat)
    (hPos : 0 < rangeLen)
    (hChildAlloc : child.targetFrameDepth = depth ∧ child.targetLocal = localIdx ∧ child.allocDead = false)
    (hChildMeta : child.tag = 2 ∧ child.parentTag = some 1 ∧ child.protector = some 1 ∧
      child.perm = .reservedFrz false)
    (hRootAlloc : root.targetFrameDepth = depth ∧ root.targetLocal = localIdx ∧ root.allocDead = false)
    (hRootMeta : root.tag = 1 ∧ root.parentTag = none ∧ root.protector = none ∧
      root.perm = .reservedFrz false)
    (hForeign : ∀ e ∈ foreign,
      e.targetFrameDepth ≠ depth ∨ e.targetLocal ≠ localIdx ∨ e.allocDead = true) :
    let tPre := rangedBorrowTreeOfMirAlloc (child :: root :: foreign) [1] depth localIdx rangeLen
    let tPost := rangedBorrowTreeOfMirAlloc
      ({ child with perm := .unique } :: { root with perm := .unique } :: foreign)
      [1] depth localIdx rangeLen
    let acc := performRangedAccess tPre 0 rangeLen 2 .Write .VisitChildrenOfAccessed
    tPre.protectedTags = [2] ∧ acc.status = .Completed ∧ acc.tree = tPost := by
  have hNil : mirBorrowsOfAlloc foreign depth localIdx = [] :=
    mirBorrowsOfAlloc_eq_nil_of_foreign foreign depth localIdx hForeign
  cases rangeLen with
  | zero => omega
  | succ n =>
    have hBltSelf : Nat.blt (n + 1) (n + 1) = false :=
      Bool.eq_false_iff.mpr (fun h => Nat.lt_irrefl (n + 1) (Nat.blt_eq.mp h))
    rcases hChildAlloc with ⟨hCD, hCL, hCA⟩
    rcases hChildMeta with ⟨hCT, hCPa, hCPr, hCPe⟩
    rcases hRootAlloc with ⟨hRD, hRL, hRA⟩
    rcases hRootMeta with ⟨hRT, hRPa, hRPr, hRPe⟩
    have hKeepC : (Nat.beq child.targetFrameDepth depth && Nat.beq child.targetLocal localIdx &&
        !child.allocDead) = true := by
      rw [hCD, hCL, hCA, Nat.beq_refl, Nat.beq_refl]; rfl
    have hKeepR : (Nat.beq root.targetFrameDepth depth && Nat.beq root.targetLocal localIdx &&
        !root.allocDead) = true := by
      rw [hRD, hRL, hRA, Nat.beq_refl, Nat.beq_refl]; rfl
    have hFilterPre : mirBorrowsOfAlloc (child :: root :: foreign) depth localIdx = [child, root] := by
      unfold mirBorrowsOfAlloc
      simp only [List.filter, hKeepC, hKeepR]
      exact congrArg (fun rest => child :: root :: rest) hNil
    have hFilterPost : mirBorrowsOfAlloc
        ({ child with perm := .unique } :: { root with perm := .unique } :: foreign) depth localIdx =
        [{ child with perm := .unique }, { root with perm := .unique }] := by
      unfold mirBorrowsOfAlloc
      simp only [List.filter, hKeepC, hKeepR]
      exact congrArg (fun rest => { child with perm := .unique } :: { root with perm := .unique } :: rest) hNil
    dsimp only [rangedBorrowTreeOfMirAlloc]
    rw [hFilterPre, hFilterPost]
    cases child; cases root
    dsimp only at hCT hCPa hCPr hCPe hRT hRPa hRPr hRPe
    subst hCT; subst hCPa; subst hCPr; subst hCPe
    subst hRT; subst hRPa; subst hRPr; subst hRPe
    have hSplit0 : splitSegmentsAt 0
        [{ offset := 0, length := n + 1,
           nodeStates := [(0, ⟨.Unique, true⟩), (2, ⟨.ReservedFrz false, true⟩),
             (1, ⟨.ReservedFrz false, true⟩)] }] =
        [{ offset := 0, length := n + 1,
           nodeStates := [(0, ⟨.Unique, true⟩), (2, ⟨.ReservedFrz false, true⟩),
             (1, ⟨.ReservedFrz false, true⟩)] }] := rfl
    have hSplitEnd : splitSegmentsAt (0 + (n + 1))
        [{ offset := 0, length := n + 1,
           nodeStates := [(0, ⟨.Unique, true⟩), (2, ⟨.ReservedFrz false, true⟩),
             (1, ⟨.ReservedFrz false, true⟩)] }] =
        [{ offset := 0, length := n + 1,
           nodeStates := [(0, ⟨.Unique, true⟩), (2, ⟨.ReservedFrz false, true⟩),
             (1, ⟨.ReservedFrz false, true⟩)] }] := by
      unfold splitSegmentsAt
      simp only [List.foldr, Nat.zero_add, hBltSelf, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    have hDisjF : Anneal.RefFrame.rangesDisjoint 0 (n + 1) 0 (n + 1) = false := by
      unfold Anneal.RefFrame.rangesDisjoint
      simp only [Nat.zero_add]
      rfl
    have hSegAcc :
        performSegmentAccess
          [⟨0, none⟩, ⟨2, some 1⟩, ⟨1, some 0⟩] [2]
          ⟨0, n + 1, [(0, ⟨.Unique, true⟩), (2, ⟨.ReservedFrz false, true⟩), (1, ⟨.ReservedFrz false, true⟩)]⟩
          2 .Write .VisitChildrenOfAccessed =
        .ok ⟨0, n + 1, [(0, ⟨.Unique, true⟩), (2, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩)]⟩ := rfl
    have hFind : findTopoNode 2
        [⟨0, none⟩, ⟨2, some 1⟩, ⟨1, some 0⟩] = some ⟨2, some 1⟩ := rfl
    have hNe0 : Nat.beq (n + 1) 0 = false := rfl
    have hAcc :
        performRangedAccess
          { topology := [⟨0, none⟩, ⟨2, some 1⟩, ⟨1, some 0⟩]
            protectedTags := [2]
            segments := [⟨0, n + 1, [(0, ⟨.Unique, true⟩), (2, ⟨.ReservedFrz false, true⟩),
              (1, ⟨.ReservedFrz false, true⟩)]⟩] }
          0 (n + 1) 2 .Write .VisitChildrenOfAccessed =
        ⟨{ topology := [⟨0, none⟩, ⟨2, some 1⟩, ⟨1, some 0⟩]
           protectedTags := [2]
           segments := [⟨0, n + 1, [(0, ⟨.Unique, true⟩), (2, ⟨.Unique, true⟩),
             (1, ⟨.Unique, true⟩)]⟩] }, .Completed⟩ := by
      unfold performRangedAccess
      dsimp only
      rw [hFind, hNe0]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hSplit0, hSplitEnd]
      dsimp only [List.foldl, stepRangedSegment]
      rw [hDisjF]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      rw [hSegAcc]
      simp only [Nat.beq_refl, List.nil_append]
    exact ⟨rfl, congrArg RangedAccessResult.status hAcc, congrArg RangedAccessResult.tree hAcc⟩

/-- **General parametric MIR `return_` ⇒ `exitFrameWithProtectors` refinement**:
for ANY allocation `(depth, localIdx)`, ANY `rangeLen`, and ANY foreign/dead tail
`foreign`, popping protector `1` on `[child{.unique}, root{.unique}] ++ foreign`
commutes EXACTLY with `exitFrameWithProtectors _ [2]`. -/
theorem rangedBorrowTreeOfMirAlloc_twoTag_return_refines
    (child root : BorrowEntry) (foreign : List BorrowEntry) (depth localIdx rangeLen : Nat)
    (hChildAlloc : child.targetFrameDepth = depth ∧ child.targetLocal = localIdx ∧ child.allocDead = false)
    (hChildMeta : child.tag = 2 ∧ child.parentTag = some 1 ∧ child.protector = some 1 ∧
      child.perm = .unique)
    (hRootAlloc : root.targetFrameDepth = depth ∧ root.targetLocal = localIdx ∧ root.allocDead = false)
    (hRootMeta : root.tag = 1 ∧ root.parentTag = none ∧ root.protector = none ∧
      root.perm = .unique)
    (hForeign : ∀ e ∈ foreign,
      e.targetFrameDepth ≠ depth ∨ e.targetLocal ≠ localIdx ∨ e.allocDead = true) :
    let tActive := rangedBorrowTreeOfMirAlloc (child :: root :: foreign) [1] depth localIdx rangeLen
    let tReleased := rangedBorrowTreeOfMirAlloc (child :: root :: foreign) [] depth localIdx rangeLen
    let rel := exitFrameWithProtectors tActive [2]
    tActive.protectedTags = [2] ∧ rel.status = .Released ∧
    rel.tree.protectedTags = [] ∧ rel.tree = tReleased := by
  have hNil : mirBorrowsOfAlloc foreign depth localIdx = [] :=
    mirBorrowsOfAlloc_eq_nil_of_foreign foreign depth localIdx hForeign
  rcases hChildAlloc with ⟨hCD, hCL, hCA⟩
  rcases hChildMeta with ⟨hCT, hCPa, hCPr, hCPe⟩
  rcases hRootAlloc with ⟨hRD, hRL, hRA⟩
  rcases hRootMeta with ⟨hRT, hRPa, hRPr, hRPe⟩
  have hKeepC : (Nat.beq child.targetFrameDepth depth && Nat.beq child.targetLocal localIdx &&
      !child.allocDead) = true := by
    rw [hCD, hCL, hCA, Nat.beq_refl, Nat.beq_refl]; rfl
  have hKeepR : (Nat.beq root.targetFrameDepth depth && Nat.beq root.targetLocal localIdx &&
      !root.allocDead) = true := by
    rw [hRD, hRL, hRA, Nat.beq_refl, Nat.beq_refl]; rfl
  have hFilter : mirBorrowsOfAlloc (child :: root :: foreign) depth localIdx = [child, root] := by
    unfold mirBorrowsOfAlloc
    simp only [List.filter, hKeepC, hKeepR]
    exact congrArg (fun rest => child :: root :: rest) hNil
  dsimp only [rangedBorrowTreeOfMirAlloc]
  rw [hFilter]
  exact rangedBorrowTreeOfMirBorrows_fnEntry_release_unique child root rangeLen
    hCT hCPa hCPr hCPe hRT hRPa hRPr hRPe

/-! ### Orthogonal Caller-Byte-Store (`List LocalSlot`) + `RangedBorrowTree` Round-Trip -/

/-- `ByteStoreOps` directly on `List LocalSlot` (`Memory.callerLocals`), cleanly separating
caller byte storage from `Memory`'s Tree Borrows / protector metadata so `CallSpecCut`
adapters need never discard or overwrite `Memory.borrows`. -/
instance callerLocalsByteStoreOps : ByteStoreOps (List LocalSlot) CallerLocalAddr UInt8 where
  addrDisjoint := memCallerByteStoreOps.addrDisjoint
  readBytes? cl addr off len :=
    match ParametricCore.listGet? cl addr.localIdx with
    | none => none
    | some slot =>
      match slotAsU8Bytes? slot with
      | none => none
      | some bytes =>
        match Nat.ble (off + len) bytes.length with
        | true => some ((bytes.drop off).take len)
        | false => none
  writeBytes? cl addr off newBytes :=
    match ParametricCore.listGet? cl addr.localIdx with
    | none => none
    | some slot =>
      match slotAsU8Bytes? slot with
      | none => none
      | some bytes =>
        match Nat.ble (off + newBytes.length) bytes.length with
        | true =>
          ParametricCore.listSet? cl addr.localIdx (u8BytesToSlot (listSplice bytes off newBytes))
        | false => none

/-- Reconstruct single-segment `V2026_06_01.MirSemantics.BorrowEntry`s for allocation
`(depth, localIdx)` directly from a `RangedBorrowTree`, so `CalleeMachineAdapter.mkEntry`
builds `Memory.borrows` faithfully from the `RangedBorrowTree` input without hardcoding
or overwriting borrow state. -/
def mirBorrowsOfRangedTree (t : RangedBorrowTree) (depth localIdx rangeOff rangeLen : Nat) :
    List BorrowEntry :=
  let states := match t.segments with | seg :: _ => seg.nodeStates | [] => []
  (t.topology.filter (fun n => !Nat.beq n.tag 0)).map (fun n =>
    let perm :=
      match lookupLocState n.tag states with
      | some st => mirOfTbPerm st.permission
      | none => .disabled
    let parent :=
      match n.parentTag with
      | none => none
      | some 0 => none
      | some p => some p
    let prot :=
      if natListMem n.tag t.protectedTags then some n.tag else none
    { tag := n.tag
      targetLocal := localIdx
      targetFrameDepth := depth
      targetProjection := []
      perm := perm
      protector := prot
      parentTag := parent
      rangeOffset := rangeOff
      rangeLen := rangeLen })

end Anneal.ParametricCore.StageCutV2026Bridge
