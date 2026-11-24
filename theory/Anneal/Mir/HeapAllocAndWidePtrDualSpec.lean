/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.HeapAllocAndWidePtrMR
import Trusted

/-!
# Episode 2 Dual-Authority Heap Allocation & Wide-Pointer Spec (`Anneal.Mir.HeapAllocAndWidePtrDualSpec`)

Cross-authority specification, canonical 30-case (`0..29`) classification, threaded
traces, constructive codec, and a direct bridge to the **unmodified**
`Trusted.Rustc.V2026_06_01.MirSemantics` for Rust heap allocation (`Allocate`,
`Deallocate`, `leak_check`, Tree Borrows protectors — `rust#165833`, `rust#166221`) and
wide-pointer `ptr::addr_eq` vs `==` (`rust#166144`):

- **Authority 1 (MiniRust `d821c6e3`)**: `MiniRustSpec.HeapAllocAndWidePtrMR.mrHeapWideObserve`
  on `Mach` / `MachTB`, reused through Episode 1's kernel-evaluated tables
  (`mrObserve_table`) and universal laws (`ep1_minirust_heap_wide_capstone`).
- **Authority 2 (LeanMiri)**: parameterized over `HeapWideLmAuthority` (root isolation:
  zero `Miri.*` / `LeanMiriSpec.*` imports), closed across roots in
  `tests/mir/HeapAllocAndWidePtrDualSpecTests.lean` over
  `LeanMiriSpec.HeapAllocAndWidePtrLM.lmHeapWideObserve`.
- **Authority 3 (Anneal TCB)**: theorems stated directly on the real
  `preventsDeallocation`, `hasProtectedLocalBorrow`, `hasFrameDeallocProtectorConflict`,
  `evalTerminator`, `evalTailCallTerminator`, `evalCastPtrToPtr`, `ptrAddressScalar?`,
  `ptrToAddrScalar`, `evalRvalue`, and `stepMirFn` (zero shadow evaluators).

Classification (`2 × 30 = 60` cells):
1. **Exact agreement (`0..27`, 56 cells)**, incl. joint Tree Borrows mode sensitivity on
   `19` (strong-protector parent dealloc) and `21` (wrong-tag `Frozen` dealloc).
2. **Exact divergence set (`28`, `29`, 4 cells)**, as an `↔` (`contract_divergence_set_exact`,
   `contract_wire_divergence_exact`): `28` MiniRust `specPanic` vs LeanMiri
   `invalidProgram`; `29` MiniRust accepts `align = 2^30`, Miri's `Align::MAX = 2^29` rejects.
3. **Totality**: both authorities are fail-closed `.invalidOrUnsupported` for `idx ≥ 30`
   (`HeapWideLmAuthority.outOfRange`), so `contract_total_divergence_exact` /
   `contract_total_wire_divergence_exact` hold for EVERY `idx : Nat`.

Trusted bridge scope note: Anneal's `hasFrameDeallocProtectorConflict` governs the
deallocation of *frame locals* at `return` / tail calls (heap `Allocate`/`Deallocate`
are not MIR primitives of `V2026_06_01`); the bridge proves the protector-classification
correspondence with MiniRust universally and ties concrete frame-teardown verdicts to
MiniRust's heap verdicts on cases `19`, `20`, `22`. The wide-pointer bridge is
universal on `evalCastPtrToPtr` / `evalRvalue` and concrete on `stepMirFn` for `23..27`.
-/

namespace Anneal.Mir.HeapAllocAndWidePtrDualSpec

set_option Elab.async false

open MiniRustSpec.HeapAllocAndWidePtrMR (MrHeapWideObs mrHeapWideObserve mrHeapLifecycleTrace
  mrProtectorDeallocTrace mrHeapWideObserve_table mrHeapWideObserve_out_of_range
  mrHeapLifecycleTrace_table mrProtectorDeallocTrace_table ep1_minirust_heap_wide_capstone)

/-! ## §1. Frozen Interface Types -/

/-- Shared authority-independent observation of one heap / wide-pointer scenario
(constructor order frozen identically to `MrHeapWideObs` and `LmHeapWideObs`). -/
inductive HeapWideObs : Type where
  | okAlloc (sizeBytes : Nat) (alignBytes : Nat)
  | okRoundTrip (readBits : Nat)
  | okDealloc
  | okBool (val : Bool)
  | memoryLeak
  | ub
  | specPanic
  | invalidOrUnsupported
  deriving DecidableEq, Repr

/-- Structural translation `MrHeapWideObs → HeapWideObs`. -/
def ofMrObs : MrHeapWideObs → HeapWideObs
  | .okAlloc s a => .okAlloc s a
  | .okRoundTrip b => .okRoundTrip b
  | .okDealloc => .okDealloc
  | .okBool b => .okBool b
  | .memoryLeak => .memoryLeak
  | .ub => .ub
  | .specPanic => .specPanic
  | .invalidOrUnsupported => .invalidOrUnsupported

/-- Structural translation `HeapWideObs → MrHeapWideObs`. -/
def toMrObs : HeapWideObs → MrHeapWideObs
  | .okAlloc s a => .okAlloc s a
  | .okRoundTrip b => .okRoundTrip b
  | .okDealloc => .okDealloc
  | .okBool b => .okBool b
  | .memoryLeak => .memoryLeak
  | .ub => .ub
  | .specPanic => .specPanic
  | .invalidOrUnsupported => .invalidOrUnsupported

theorem ofMrObs_toMrObs (o : HeapWideObs) : ofMrObs (toMrObs o) = o := by
  cases o <;> rfl

theorem toMrObs_ofMrObs (o : MrHeapWideObs) : toMrObs (ofMrObs o) = o := by
  cases o <;> rfl

theorem ofMrObs_injective {a b : MrHeapWideObs} (h : ofMrObs a = ofMrObs b) : a = b := by
  rw [← toMrObs_ofMrObs a, h, toMrObs_ofMrObs]

/-- Shared dual-authority memory mode. -/
inductive HeapWideMemoryMode : Type where
  /-- MiniRust `BasicMemory<x86_64>` / LeanMiri `treeBorrows = false`. -/
  | basic
  /-- MiniRust `TreeBorrowsMemory<x86_64>` / LeanMiri `treeBorrows = true`. -/
  | treeBorrows
  deriving DecidableEq, Repr

def HeapWideMemoryMode.toLmTreeBorrows : HeapWideMemoryMode → Bool
  | .basic => false
  | .treeBorrows => true

def HeapWideMemoryMode.ofLmTreeBorrows : Bool → HeapWideMemoryMode
  | false => .basic
  | true => .treeBorrows

theorem HeapWideMemoryMode.of_toLmTreeBorrows (m : HeapWideMemoryMode) :
    HeapWideMemoryMode.ofLmTreeBorrows m.toLmTreeBorrows = m := by
  cases m <;> rfl

theorem HeapWideMemoryMode.to_ofLmTreeBorrows (b : Bool) :
    (HeapWideMemoryMode.ofLmTreeBorrows b).toLmTreeBorrows = b := by
  cases b <;> rfl

def allHeapWideModes : List HeapWideMemoryMode := [.basic, .treeBorrows]

theorem allHeapWideModes_complete (m : HeapWideMemoryMode) : m ∈ allHeapWideModes := by
  cases m <;> simp [allHeapWideModes]

/-! ## §2. Constructive `HeapWideCodecLaws` (`[propext, Quot.sound]`, zero `Classical.choice`) -/

/-- Constructive round-trip and canonical-representation codec contract. -/
structure HeapWideCodecLaws (A B : Type) : Type where
  encode : A → B
  decode : B → Option A
  ValidRep : B → Prop
  decode_encode : ∀ a, decode (encode a) = some a
  encode_valid : ∀ a, ValidRep (encode a)
  encode_decode_of_valid : ∀ b a, ValidRep b → decode b = some a → encode a = b

/-- Every valid wire representation decodes to some domain value. -/
def HeapWideCodecLaws.TightValidRep {A B : Type} (c : HeapWideCodecLaws A B) : Prop :=
  ∀ b, c.ValidRep b → ∃ a, c.decode b = some a

/-- Wire tuple `(tag, payload₁, payload₂, flag)`. -/
abbrev HeapWideOutcomeRep : Type := Nat × Nat × Nat × Bool

def heapWideEncode : HeapWideObs → HeapWideOutcomeRep
  | .okAlloc sz al => (0, sz, al, false)
  | .okRoundTrip bits => (1, bits, 0, false)
  | .okDealloc => (2, 0, 0, false)
  | .okBool b => (3, 0, 0, b)
  | .memoryLeak => (4, 0, 0, false)
  | .ub => (5, 0, 0, false)
  | .specPanic => (6, 0, 0, false)
  | .invalidOrUnsupported => (7, 0, 0, false)

/-- Canonical-form decoder: accepts exactly the 8 frozen tuple shapes. -/
def heapWideDecode : HeapWideOutcomeRep → Option HeapWideObs
  | (0, sz, al, false) => some (.okAlloc sz al)
  | (1, bits, 0, false) => some (.okRoundTrip bits)
  | (2, 0, 0, false) => some .okDealloc
  | (3, 0, 0, b) => some (.okBool b)
  | (4, 0, 0, false) => some .memoryLeak
  | (5, 0, 0, false) => some .ub
  | (6, 0, 0, false) => some .specPanic
  | (7, 0, 0, false) => some .invalidOrUnsupported
  | _ => none

/-- Decidable canonical-representation predicate. -/
def heapWideValidRep (b : HeapWideOutcomeRep) : Prop := (heapWideDecode b).isSome = true

/-- The decoder only accepts canonical tuples: every accepted tuple is the encoding
of what it decodes to (for every tuple, valid or not). -/
theorem heapWideDecode_canonical (b : HeapWideOutcomeRep) (a : HeapWideObs)
    (h : heapWideDecode b = some a) : heapWideEncode a = b := by
  rcases b with ⟨t, x, y, f⟩
  unfold heapWideDecode at h
  split at h <;> first | (cases h; done) | (cases h; rename_i heq; cases heq; rfl)

/-- Constructive codec instance for `HeapWideObs` (zero `Classical.choice`). -/
def heapWideOutcomeCodec : HeapWideCodecLaws HeapWideObs HeapWideOutcomeRep where
  encode := heapWideEncode
  decode := heapWideDecode
  ValidRep := heapWideValidRep
  decode_encode := fun a => by cases a <;> rfl
  encode_valid := fun a => by cases a <;> rfl
  encode_decode_of_valid := fun b a _ hd => heapWideDecode_canonical b a hd

/-- Tightness of `heapWideValidRep` (zero `Classical.choice`). -/
theorem heapWideOutcomeCodec_tight : heapWideOutcomeCodec.TightValidRep := by
  intro b hv
  change (heapWideDecode b).isSome = true at hv
  cases hd : heapWideDecode b with
  | none => rw [hd] at hv; cases hv
  | some a => exact ⟨a, hd⟩

/-- Constructive injectivity of `heapWideOutcomeCodec.encode`. -/
theorem heapWideOutcomeCodec_encode_injective {a₁ a₂ : HeapWideObs}
    (h : heapWideOutcomeCodec.encode a₁ = heapWideOutcomeCodec.encode a₂) : a₁ = a₂ := by
  have h1 := heapWideOutcomeCodec.decode_encode a₁
  have h2 := heapWideOutcomeCodec.decode_encode a₂
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

/-- Constructive injectivity of `heapWideOutcomeCodec.decode` on valid representations. -/
theorem heapWideOutcomeCodec_decode_injective_on_valid {b₁ b₂ : HeapWideOutcomeRep}
    {a : HeapWideObs}
    (hv₁ : heapWideOutcomeCodec.ValidRep b₁) (hv₂ : heapWideOutcomeCodec.ValidRep b₂)
    (hd₁ : heapWideOutcomeCodec.decode b₁ = some a)
    (hd₂ : heapWideOutcomeCodec.decode b₂ = some a) : b₁ = b₂ := by
  have h1 := heapWideOutcomeCodec.encode_decode_of_valid b₁ a hv₁ hd₁
  have h2 := heapWideOutcomeCodec.encode_decode_of_valid b₂ a hv₂ hd₂
  exact h1.symm.trans h2

/-- Malformed tuples are rejected (the codec is not a total relabelling). -/
theorem heapWideOutcomeCodec_rejects_malformed :
    heapWideOutcomeCodec.decode (8, 0, 0, false) = none ∧
    heapWideOutcomeCodec.decode (2, 1, 0, false) = none ∧
    heapWideOutcomeCodec.decode (1, 5, 1, false) = none ∧
    heapWideOutcomeCodec.decode (0, 0, 1, true) = none ∧
    heapWideOutcomeCodec.decode (5, 0, 0, true) = none ∧
    ¬ heapWideOutcomeCodec.ValidRep (7, 0, 1, false) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro h; cases h

/-! ## §3. Canonical 30-Case Table (`0..29`) and the Real MiniRust Evaluation -/

/-- Number of canonical cross-authority heap / wide-pointer cases. -/
def canonicalCaseCount : Nat := 30

/-- Cross-authority relationship of each canonical case. -/
inductive HeapWideComparisonClass : Type where
  /-- MiniRust and LeanMiri agree identically in both modes. -/
  | exactAgreement
  /-- Case `28`: un-erased `==` on a slice vs. a trait-object pointer — MiniRust
  `Stop.specPanic` (unmatching metadata) vs. LeanMiri `invalidProgram`. -/
  | heteroWideEqErrorKindDivergence
  /-- Case `29`: `Allocate(0, 2^30)` — MiniRust has no `Align::MAX`, vendored
  `Miri.ABI.Align.fromBytes` rejects `2^30 > 2^29`. -/
  | alignMaxDivergence
  deriving DecidableEq, Repr

/-- Comparison class of a canonical case index. -/
def caseClass : Nat → HeapWideComparisonClass
  | 28 => .heteroWideEqErrorKindDivergence
  | 29 => .alignMaxDivergence
  | _ => .exactAgreement

/-- Mode sensitivity of a canonical case index (Tree Borrows cases `19`, `21`). -/
def caseModeSensitive : Nat → Bool
  | 19 | 21 => true
  | _ => false

/-- Real MiniRust observation, translated: `mrHeapWideObserve` runs the interpreted
`Allocate` / `Deallocate` / `leak_check` / `GetThinPointer` + `compare_ptr` scenarios
on `Mach` (`.basic`) and `MachTB` (`.treeBorrows`). -/
def mrObserve (m : HeapWideMemoryMode) (idx : Nat) : HeapWideObs :=
  ofMrObs (mrHeapWideObserve m.toLmTreeBorrows idx)

/-- Frozen expected MiniRust table (`2 modes × 30 cases`). -/
def mrExpected (m : HeapWideMemoryMode) : Nat → HeapWideObs
  | 0 => .okAlloc 0 1
  | 1 => .okAlloc 0 32
  | 2 => .okRoundTrip 3735928559
  | 3 => .okRoundTrip 81985529216486895
  | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 => .ub
  | 15 => .memoryLeak
  | 16 | 17 | 18 => .okDealloc
  | 19 => match m with | .basic => .okDealloc | .treeBorrows => .ub
  | 20 => .okDealloc
  | 21 => match m with | .basic => .okDealloc | .treeBorrows => .ub
  | 22 => .okDealloc
  | 23 => .okBool true
  | 24 => .okBool false
  | 25 => .okBool true
  | 26 => .okBool false
  | 27 => .okBool true
  | 28 => .specPanic
  | 29 => .okAlloc 0 1073741824
  | _ => .invalidOrUnsupported

/-- Frozen expected LeanMiri table (`2 modes × 30 cases`), mirroring
`LeanMiriSpec.HeapAllocAndWidePtrLM.lmHeapWideObserve_table`. -/
def lmExpected (m : HeapWideMemoryMode) : Nat → HeapWideObs
  | 0 => .okAlloc 0 1
  | 1 => .okAlloc 0 32
  | 2 => .okRoundTrip 3735928559
  | 3 => .okRoundTrip 81985529216486895
  | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 => .ub
  | 15 => .memoryLeak
  | 16 | 17 | 18 => .okDealloc
  | 19 => match m with | .basic => .okDealloc | .treeBorrows => .ub
  | 20 => .okDealloc
  | 21 => match m with | .basic => .okDealloc | .treeBorrows => .ub
  | 22 => .okDealloc
  | 23 => .okBool true
  | 24 => .okBool false
  | 25 => .okBool true
  | 26 => .okBool false
  | 27 => .okBool true
  | 28 => .invalidOrUnsupported
  | 29 => .ub
  | _ => .invalidOrUnsupported

/-- Read one cell out of a `List.range`-indexed table equation. -/
theorem range_map_cell {α : Type} {f g : Nat → α} {n : Nat}
    (h : (List.range n).map f = (List.range n).map g) (i : Nat) (hi : i < n) : f i = g i := by
  have h' := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some] at h'
  exact Option.some.inj h'

/-- **The 60-cell MiniRust table**, reusing Episode 1's kernel-evaluated
`mrHeapWideObserve_table` (no re-evaluation, no `native_decide`). -/
theorem mrObserve_table (m : HeapWideMemoryMode) (idx : Nat) (hIdx : idx < canonicalCaseCount) :
    mrObserve m idx = mrExpected m idx := by
  have hL : (List.range 30).map (mrHeapWideObserve m.toLmTreeBorrows) =
      (List.range 30).map (fun i => toMrObs (mrExpected m i)) := by
    cases m
    · exact mrHeapWideObserve_table.1.trans (by decide)
    · exact mrHeapWideObserve_table.2.trans (by decide)
  unfold mrObserve
  rw [range_map_cell hL idx hIdx, ofMrObs_toMrObs]

/-- Out of range both observers are `.invalidOrUnsupported`. -/
theorem mrObserve_out_of_range (m : HeapWideMemoryMode) (idx : Nat) (h : canonicalCaseCount ≤ idx) :
    mrObserve m idx = .invalidOrUnsupported := by
  unfold mrObserve
  rw [mrHeapWideObserve_out_of_range _ _ h]
  rfl

/-- MiniRust Tree Borrows mode sensitivity: exactly cases `19` and `21` flip. -/
theorem mr_mode_sensitivity :
    mrObserve .basic 19 = .okDealloc ∧ mrObserve .treeBorrows 19 = .ub ∧
    mrObserve .basic 21 = .okDealloc ∧ mrObserve .treeBorrows 21 = .ub ∧
    (∀ idx, idx < canonicalCaseCount →
      (mrObserve .basic idx ≠ mrObserve .treeBorrows idx ↔ caseModeSensitive idx = true)) := by
  have key : ((List.range 30).all fun idx =>
      decide ((mrExpected .basic idx ≠ mrExpected .treeBorrows idx) ↔
        caseModeSensitive idx = true)) = true := by decide
  refine ⟨mrObserve_table _ _ (by decide), mrObserve_table _ _ (by decide),
    mrObserve_table _ _ (by decide), mrObserve_table _ _ (by decide), fun idx hIdx => ?_⟩
  rw [mrObserve_table _ _ hIdx, mrObserve_table _ _ hIdx]
  exact of_decide_eq_true (List.all_eq_true.mp key idx (List.mem_range.mpr hIdx))

/-- Every agreement-zone cell has identical expected outcomes. -/
theorem expected_agreement_zone (m : HeapWideMemoryMode) (idx : Nat)
    (hIdx : idx < canonicalCaseCount) (hAgree : caseClass idx = .exactAgreement) :
    mrExpected m idx = lmExpected m idx := by
  have key : (allHeapWideModes.all fun m => (List.range 30).all fun idx =>
      !(decide (caseClass idx = .exactAgreement)) ||
        decide (mrExpected m idx = lmExpected m idx)) = true := by decide
  have h := List.all_eq_true.mp (List.all_eq_true.mp key m (allHeapWideModes_complete m)) idx
    (List.mem_range.mpr hIdx)
  simp only [decide_eq_true hAgree, Bool.not_true, Bool.false_or] at h
  exact of_decide_eq_true h

/-- The agreement zone is exactly `0..27`. -/
theorem caseClass_agreement_iff (idx : Nat) (hIdx : idx < canonicalCaseCount) :
    caseClass idx = .exactAgreement ↔ idx < 28 := by
  have key : ((List.range 30).all fun idx =>
      decide (caseClass idx = .exactAgreement ↔ idx < 28)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp key idx (List.mem_range.mpr hIdx))

/-- MiniRust `BasicMemory` transcription bridge: on `Mach`, the non-polymorphic
`evalBinOp (.Rel .Eq)` (through `comparePtr`) is `evalWideEqM`, and `GetThinPointer` +
`evalBinOp` is `evalAddrEqM` — which compares addresses only for every pair of pointers
and every metadata / provenance. -/
theorem mr_addrEq_wideEq_bm_bridge :
    (type_of% @MiniRustSpec.HeapAllocAndWidePtrMR.evalWideEq_bm) ∧
    (type_of% @MiniRustSpec.HeapAllocAndWidePtrMR.evalAddrEq_bm) ∧
    (type_of% @MiniRustSpec.HeapAllocAndWidePtrMR.evalAddrEqM_metadata_irrelevant) :=
  ⟨@MiniRustSpec.HeapAllocAndWidePtrMR.evalWideEq_bm, @MiniRustSpec.HeapAllocAndWidePtrMR.evalAddrEq_bm,
    @MiniRustSpec.HeapAllocAndWidePtrMR.evalAddrEqM_metadata_irrelevant⟩

/-! ## §4. Threaded Traces -/

/-- Frozen heap lifecycle trace (both modes). -/
def lifecycleExpected : List HeapWideObs :=
  [.okAlloc 32 32, .okRoundTrip 14627333968688404088, .memoryLeak, .okBool true, .okDealloc, .ub]

/-- Frozen mode-sensitive protector trace. -/
def protectorExpected : HeapWideMemoryMode → List HeapWideObs
  | .basic => [.okRoundTrip 42, .okBool true, .okDealloc, .okDealloc]
  | .treeBorrows => [.okRoundTrip 42, .okBool true, .ub]

/-- MiniRust heap lifecycle trace on ONE `Mach` / `MachTB`, translated. -/
def mrLifecycleTrace (m : HeapWideMemoryMode) : List HeapWideObs :=
  (mrHeapLifecycleTrace m.toLmTreeBorrows).map ofMrObs

/-- MiniRust protector trace on ONE `Mach` / `MachTB`, translated. -/
def mrProtectorTrace (m : HeapWideMemoryMode) : List HeapWideObs :=
  (mrProtectorDeallocTrace m.toLmTreeBorrows).map ofMrObs

theorem mrLifecycleTrace_table (m : HeapWideMemoryMode) : mrLifecycleTrace m = lifecycleExpected := by
  unfold mrLifecycleTrace
  cases m
  · rw [show HeapWideMemoryMode.toLmTreeBorrows .basic = false from rfl,
      mrHeapLifecycleTrace_table.1]; rfl
  · rw [show HeapWideMemoryMode.toLmTreeBorrows .treeBorrows = true from rfl,
      mrHeapLifecycleTrace_table.2]; rfl

theorem mrProtectorTrace_table (m : HeapWideMemoryMode) : mrProtectorTrace m = protectorExpected m := by
  unfold mrProtectorTrace
  cases m
  · rw [show HeapWideMemoryMode.toLmTreeBorrows .basic = false from rfl,
      mrProtectorDeallocTrace_table.1]; rfl
  · rw [show HeapWideMemoryMode.toLmTreeBorrows .treeBorrows = true from rfl,
      mrProtectorDeallocTrace_table.2]; rfl

/-- The protector trace is genuinely mode-sensitive. -/
theorem mrProtectorTrace_mode_sensitive : mrProtectorTrace .basic ≠ mrProtectorTrace .treeBorrows := by
  rw [mrProtectorTrace_table, mrProtectorTrace_table]; decide

/-! ## §5. Frozen Cross-Root Authority Interface -/

/-- Authority-agnostic LeanMiri interface, closed in
`tests/mir/HeapAllocAndWidePtrDualSpecTests.lean` over
`LeanMiriSpec.HeapAllocAndWidePtrLM.lmHeapWideObserve`. -/
structure HeapWideLmAuthority : Type where
  observe : Bool → Nat → HeapWideObs
  matchesExpected : ∀ (tb : Bool) (idx : Nat), idx < canonicalCaseCount →
    observe tb idx = lmExpected (HeapWideMemoryMode.ofLmTreeBorrows tb) idx
  /-- Outside the canonical table LeanMiri is fail-closed `.invalidOrUnsupported` (closed
  across roots from `LeanMiriSpec.HeapAllocAndWidePtrLM.lmHeapWideObserve_out_of_range`),
  so the classification below is total over ALL `idx : Nat`, not just `0..29`. -/
  outOfRange : ∀ (tb : Bool) (idx : Nat), canonicalCaseCount ≤ idx →
    observe tb idx = .invalidOrUnsupported

/-- Decidable 60-cell check of a LeanMiri observation function. -/
def lmAuthorityCheck (obs : Bool → Nat → HeapWideObs) : Bool :=
  [false, true].all fun tb =>
    (List.range canonicalCaseCount).all fun idx =>
      decide (obs tb idx = lmExpected (HeapWideMemoryMode.ofLmTreeBorrows tb) idx)

/-- Soundness of `lmAuthorityCheck` (constructive). -/
theorem lmAuthorityCheck_sound (obs : Bool → Nat → HeapWideObs)
    (h : lmAuthorityCheck obs = true) (tb : Bool) (idx : Nat) (hIdx : idx < canonicalCaseCount) :
    obs tb idx = lmExpected (HeapWideMemoryMode.ofLmTreeBorrows tb) idx := by
  have hTb : tb ∈ [false, true] := by cases tb <;> simp
  have h1 := List.all_eq_true.mp h tb hTb
  have h2 := List.all_eq_true.mp h1 idx (List.mem_range.mpr hIdx)
  exact of_decide_eq_true h2

def lmAuthorityOfCheck (obs : Bool → Nat → HeapWideObs) (h : lmAuthorityCheck obs = true)
    (hOut : ∀ (tb : Bool) (idx : Nat), canonicalCaseCount ≤ idx → obs tb idx = .invalidOrUnsupported) :
    HeapWideLmAuthority where
  observe := obs
  matchesExpected := lmAuthorityCheck_sound obs h
  outOfRange := hOut

/-- Cross-authority lifecycle trace check (both modes equal MiniRust's frozen trace). -/
def lmLifecycleTraceAuthorityCheck (obs : Bool → List HeapWideObs) : Bool :=
  decide (obs (HeapWideMemoryMode.toLmTreeBorrows .basic) = lifecycleExpected ∧
    obs (HeapWideMemoryMode.toLmTreeBorrows .treeBorrows) = lifecycleExpected)

/-- Soundness: a passing lifecycle check is step-for-step agreement with the real
MiniRust trace on `Mach` / `MachTB`. -/
theorem lmLifecycleTraceAuthorityCheck_sound (obs : Bool → List HeapWideObs)
    (h : lmLifecycleTraceAuthorityCheck obs = true) (m : HeapWideMemoryMode) :
    obs m.toLmTreeBorrows = mrLifecycleTrace m := by
  rw [mrLifecycleTrace_table]
  unfold lmLifecycleTraceAuthorityCheck at h
  cases m
  · exact (of_decide_eq_true h).1
  · exact (of_decide_eq_true h).2

/-- Mode-sensitive cross-authority protector trace check. -/
def lmProtectorTraceAuthorityCheck (obs : Bool → List HeapWideObs) : Bool :=
  decide (obs (HeapWideMemoryMode.toLmTreeBorrows .basic) = protectorExpected .basic ∧
    obs (HeapWideMemoryMode.toLmTreeBorrows .treeBorrows) = protectorExpected .treeBorrows)

/-- Soundness: agreement with MiniRust's real protector trace in both modes, and the
two modes provably differ. -/
theorem lmProtectorTraceAuthorityCheck_sound (obs : Bool → List HeapWideObs)
    (h : lmProtectorTraceAuthorityCheck obs = true) (m : HeapWideMemoryMode) :
    obs m.toLmTreeBorrows = mrProtectorTrace m ∧ obs false ≠ obs true := by
  unfold lmProtectorTraceAuthorityCheck at h
  have h' := of_decide_eq_true h
  refine ⟨?_, ?_⟩
  · rw [mrProtectorTrace_table]
    cases m
    · exact h'.1
    · exact h'.2
  · intro e
    have e' : protectorExpected .basic = protectorExpected .treeBorrows :=
      h'.1.symm.trans (e.trans h'.2)
    exact absurd e' (by decide)

/-- Exact divergence set (`4/60` cells): cases `28` and `29` in both modes. -/
def divergesAt (_m : HeapWideMemoryMode) (idx : Nat) : Bool :=
  decide (idx = 28 ∨ idx = 29)

theorem divergesAt_iff_class (m : HeapWideMemoryMode) (idx : Nat) :
    divergesAt m idx = false ↔ caseClass idx = .exactAgreement := by
  unfold divergesAt caseClass
  constructor
  · intro h
    have h' := of_decide_eq_false h
    split
    · exact absurd (Or.inl rfl) h'
    · exact absurd (Or.inr rfl) h'
    · rfl
  · intro h
    apply decide_eq_false
    rintro (rfl | rfl) <;> cases h

private theorem divergence_set_exact_aux :
    (allHeapWideModes.all fun m => (List.range 30).all fun idx =>
      decide ((mrExpected m idx ≠ lmExpected m idx) ↔ divergesAt m idx = true)) = true := by
  decide

/-- Dual-authority correspondence contract. -/
structure HeapWideDualContract : Type where
  lm : HeapWideLmAuthority
  lmLifecycle : Bool → List HeapWideObs
  lmProtector : Bool → List HeapWideObs
  mr_ep1_capstone : type_of% @ep1_minirust_heap_wide_capstone
  mr_matches : ∀ (m : HeapWideMemoryMode) (idx : Nat), idx < canonicalCaseCount →
    mrObserve m idx = mrExpected m idx
  agreement_zone_exact : ∀ (m : HeapWideMemoryMode) (idx : Nat), idx < canonicalCaseCount →
    caseClass idx = .exactAgreement → mrObserve m idx = lm.observe m.toLmTreeBorrows idx
  divergence_explicit : ∀ (m : HeapWideMemoryMode),
    mrObserve m 28 = .specPanic ∧ lm.observe m.toLmTreeBorrows 28 = .invalidOrUnsupported ∧
    mrObserve m 29 = .okAlloc 0 1073741824 ∧ lm.observe m.toLmTreeBorrows 29 = .ub
  mode_sensitivity_joint :
    (mrObserve .basic 19 = lm.observe false 19 ∧ mrObserve .basic 19 = .okDealloc ∧
      mrObserve .treeBorrows 19 = lm.observe true 19 ∧ lm.observe true 19 = .ub) ∧
    (mrObserve .basic 21 = lm.observe false 21 ∧ mrObserve .basic 21 = .okDealloc ∧
      mrObserve .treeBorrows 21 = lm.observe true 21 ∧ lm.observe true 21 = .ub)
  lifecycle_matches : ∀ (m : HeapWideMemoryMode), lmLifecycle m.toLmTreeBorrows = mrLifecycleTrace m
  protector_matches : ∀ (m : HeapWideMemoryMode), lmProtector m.toLmTreeBorrows = mrProtectorTrace m
  protector_mode_sensitive : lmProtector false ≠ lmProtector true

/-- Build the contract from a verified authority and two passing trace checks. -/
def mkHeapWideDualContract (lm : HeapWideLmAuthority) (lc pt : Bool → List HeapWideObs)
    (hlc : lmLifecycleTraceAuthorityCheck lc = true)
    (hpt : lmProtectorTraceAuthorityCheck pt = true) : HeapWideDualContract where
  lm := lm
  lmLifecycle := lc
  lmProtector := pt
  mr_ep1_capstone := ep1_minirust_heap_wide_capstone
  mr_matches := mrObserve_table
  agreement_zone_exact := fun m idx hIdx hAgree => by
    rw [mrObserve_table m idx hIdx, lm.matchesExpected m.toLmTreeBorrows idx hIdx,
      HeapWideMemoryMode.of_toLmTreeBorrows m]
    exact expected_agreement_zone m idx hIdx hAgree
  divergence_explicit := fun m => by
    have h28 := lm.matchesExpected m.toLmTreeBorrows 28 (by decide)
    have h29 := lm.matchesExpected m.toLmTreeBorrows 29 (by decide)
    rw [HeapWideMemoryMode.of_toLmTreeBorrows] at h28 h29
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mrObserve_table m 28 (by decide)]; cases m <;> rfl
    · rw [h28]; cases m <;> rfl
    · rw [mrObserve_table m 29 (by decide)]; cases m <;> rfl
    · rw [h29]; cases m <;> rfl
  mode_sensitivity_joint := by
    have a := lm.matchesExpected false 19 (by decide)
    have b := lm.matchesExpected true 19 (by decide)
    have c := lm.matchesExpected false 21 (by decide)
    have d := lm.matchesExpected true 21 (by decide)
    have e := mrObserve_table .basic 19 (by decide)
    have f := mrObserve_table .treeBorrows 19 (by decide)
    have g := mrObserve_table .basic 21 (by decide)
    have k := mrObserve_table .treeBorrows 21 (by decide)
    exact ⟨⟨e.trans a.symm, e, f.trans b.symm, b⟩, ⟨g.trans c.symm, g, k.trans d.symm, d⟩⟩
  lifecycle_matches := lmLifecycleTraceAuthorityCheck_sound lc hlc
  protector_matches := fun m => (lmProtectorTraceAuthorityCheck_sound pt hpt m).1
  protector_mode_sensitive := (lmProtectorTraceAuthorityCheck_sound pt hpt .basic).2

/-- Direct check-to-contract constructor for the cross-root kernel bridge. -/
def heapWideDualContractOfChecks (obs : Bool → Nat → HeapWideObs) (lc pt : Bool → List HeapWideObs)
    (h : lmAuthorityCheck obs = true) (hlc : lmLifecycleTraceAuthorityCheck lc = true)
    (hpt : lmProtectorTraceAuthorityCheck pt = true)
    (hOut : ∀ (tb : Bool) (idx : Nat), canonicalCaseCount ≤ idx → obs tb idx = .invalidOrUnsupported) :
    HeapWideDualContract :=
  mkHeapWideDualContract (lmAuthorityOfCheck obs h hOut) lc pt hlc hpt

/-- **Exact divergence set** (an `↔`, zero wildcards): on every canonical cell, the
authorities differ iff the cell is case `28` or `29`. -/
theorem contract_divergence_set_exact (c : HeapWideDualContract) (m : HeapWideMemoryMode)
    (idx : Nat) (hIdx : idx < canonicalCaseCount) :
    mrObserve m idx ≠ c.lm.observe m.toLmTreeBorrows idx ↔ divergesAt m idx = true := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp divergence_set_exact_aux m
    (allHeapWideModes_complete m)) idx (List.mem_range.mpr hIdx)
  rw [mrObserve_table m idx hIdx, c.lm.matchesExpected m.toLmTreeBorrows idx hIdx,
    HeapWideMemoryMode.of_toLmTreeBorrows m]
  exact of_decide_eq_true h

/-- Agreement half: outside `divergesAt` the authorities agree. -/
theorem contract_agreement_of_not_diverges (c : HeapWideDualContract) (m : HeapWideMemoryMode)
    (idx : Nat) (hIdx : idx < canonicalCaseCount) (hNo : divergesAt m idx = false) :
    mrObserve m idx = c.lm.observe m.toLmTreeBorrows idx := by
  cases hEq : decide (mrObserve m idx = c.lm.observe m.toLmTreeBorrows idx) with
  | true => exact of_decide_eq_true hEq
  | false =>
    have hne := of_decide_eq_false hEq
    have := (contract_divergence_set_exact c m idx hIdx).mp hne
    rw [hNo] at this; cases this

/-- **Wire-level exact divergence set**: the encoded tuples coincide iff the cell is
outside `divergesAt` (the codec neither launders nor invents a divergence). -/
theorem contract_wire_divergence_exact (c : HeapWideDualContract) (m : HeapWideMemoryMode)
    (idx : Nat) (hIdx : idx < canonicalCaseCount) :
    heapWideOutcomeCodec.encode (mrObserve m idx) =
        heapWideOutcomeCodec.encode (c.lm.observe m.toLmTreeBorrows idx) ↔
      divergesAt m idx = false := by
  constructor
  · intro hEnc
    cases hD : divergesAt m idx with
    | false => rfl
    | true =>
      exact absurd (heapWideOutcomeCodec_encode_injective hEnc)
        ((contract_divergence_set_exact c m idx hIdx).mpr hD)
  · intro hNo
    exact congrArg heapWideOutcomeCodec.encode (contract_agreement_of_not_diverges c m idx hIdx hNo)

/-- **Total exact divergence set over ALL `idx : Nat`** (no `idx < 30` side condition):
out of range both authorities are fail-closed `.invalidOrUnsupported` and agree. -/
theorem contract_total_divergence_exact (c : HeapWideDualContract) (m : HeapWideMemoryMode)
    (idx : Nat) :
    mrObserve m idx ≠ c.lm.observe m.toLmTreeBorrows idx ↔ divergesAt m idx = true := by
  cases Nat.lt_or_ge idx canonicalCaseCount with
  | inl hIdx => exact contract_divergence_set_exact c m idx hIdx
  | inr hOut =>
    rw [mrObserve_out_of_range m idx hOut, c.lm.outOfRange _ idx hOut]
    have hD : divergesAt m idx = false := by
      apply decide_eq_false
      have h30 : 30 ≤ idx := hOut
      rintro (rfl | rfl) <;> exact absurd h30 (by decide)
    rw [hD]
    exact ⟨fun h => absurd rfl h, fun h => by cases h⟩

/-- **Total wire-level exact divergence set over ALL `idx : Nat`.** -/
theorem contract_total_wire_divergence_exact (c : HeapWideDualContract) (m : HeapWideMemoryMode)
    (idx : Nat) :
    heapWideOutcomeCodec.encode (mrObserve m idx) =
        heapWideOutcomeCodec.encode (c.lm.observe m.toLmTreeBorrows idx) ↔
      divergesAt m idx = false := by
  constructor
  · intro hEnc
    cases hD : divergesAt m idx with
    | false => rfl
    | true =>
      exact absurd (heapWideOutcomeCodec_encode_injective hEnc)
        ((contract_total_divergence_exact c m idx).mpr hD)
  · intro hNo
    apply congrArg heapWideOutcomeCodec.encode
    cases hEq : decide (mrObserve m idx = c.lm.observe m.toLmTreeBorrows idx) with
    | true => exact of_decide_eq_true hEq
    | false =>
      have := (contract_total_divergence_exact c m idx).mp (of_decide_eq_false hEq)
      rw [hNo] at this; cases this

/-- Out of range both authorities are `.invalidOrUnsupported` in both modes. -/
theorem contract_out_of_range_agreement (c : HeapWideDualContract) (m : HeapWideMemoryMode)
    (idx : Nat) (hOut : canonicalCaseCount ≤ idx) :
    mrObserve m idx = .invalidOrUnsupported ∧
      c.lm.observe m.toLmTreeBorrows idx = .invalidOrUnsupported :=
  ⟨mrObserve_out_of_range m idx hOut, c.lm.outOfRange _ idx hOut⟩

/-- Decidable single-cell wire agreement (for cross-root positive / forged controls). -/
def wireAgreesAt (obs : Bool → Nat → HeapWideObs) (m : HeapWideMemoryMode) (idx : Nat) : Bool :=
  decide (heapWideOutcomeCodec.encode (mrObserve m idx) =
    heapWideOutcomeCodec.encode (obs m.toLmTreeBorrows idx))

/-- Named projections for cross-root instantiation. -/
theorem contract_agreement_zone_exact (c : HeapWideDualContract) :
    ∀ (m : HeapWideMemoryMode) (idx : Nat), idx < canonicalCaseCount →
      caseClass idx = .exactAgreement → mrObserve m idx = c.lm.observe m.toLmTreeBorrows idx :=
  c.agreement_zone_exact

theorem contract_divergence_explicit (c : HeapWideDualContract) :
    ∀ (m : HeapWideMemoryMode),
      mrObserve m 28 = .specPanic ∧ c.lm.observe m.toLmTreeBorrows 28 = .invalidOrUnsupported ∧
      mrObserve m 29 = .okAlloc 0 1073741824 ∧ c.lm.observe m.toLmTreeBorrows 29 = .ub :=
  c.divergence_explicit

theorem contract_mode_sensitivity_joint (c : HeapWideDualContract) :
    (mrObserve .basic 19 = c.lm.observe false 19 ∧ mrObserve .basic 19 = .okDealloc ∧
      mrObserve .treeBorrows 19 = c.lm.observe true 19 ∧ c.lm.observe true 19 = .ub) ∧
    (mrObserve .basic 21 = c.lm.observe false 21 ∧ mrObserve .basic 21 = .okDealloc ∧
      mrObserve .treeBorrows 21 = c.lm.observe true 21 ∧ c.lm.observe true 21 = .ub) :=
  c.mode_sensitivity_joint

theorem contract_traces (c : HeapWideDualContract) :
    (∀ m, c.lmLifecycle m.toLmTreeBorrows = mrLifecycleTrace m) ∧
    (∀ m, c.lmProtector m.toLmTreeBorrows = mrProtectorTrace m) ∧
    c.lmProtector false ≠ c.lmProtector true ∧
    c.lmLifecycle false = lifecycleExpected ∧ c.lmLifecycle true = lifecycleExpected ∧
    c.lmProtector false = protectorExpected .basic ∧
    c.lmProtector true = protectorExpected .treeBorrows := by
  refine ⟨c.lifecycle_matches, c.protector_matches, c.protector_mode_sensitive, ?_, ?_, ?_, ?_⟩
  · exact (c.lifecycle_matches .basic).trans (mrLifecycleTrace_table _)
  · exact (c.lifecycle_matches .treeBorrows).trans (mrLifecycleTrace_table _)
  · exact (c.protector_matches .basic).trans (mrProtectorTrace_table _)
  · exact (c.protector_matches .treeBorrows).trans (mrProtectorTrace_table _)

/-- Specific agreement witnesses: `StaticAllocator` (`rust#166221`: `13, 14, 17`), leak check
(`15, 16, 17`), and wide-pointer `addr_eq` vs `==` (`rust#166144`: `23..27`), in both modes. -/
theorem contract_static_leak_wide_agreement (c : HeapWideDualContract) (m : HeapWideMemoryMode) :
    (mrObserve m 13 = .ub ∧ c.lm.observe m.toLmTreeBorrows 13 = .ub) ∧
    (mrObserve m 14 = .ub ∧ c.lm.observe m.toLmTreeBorrows 14 = .ub) ∧
    (mrObserve m 15 = .memoryLeak ∧ c.lm.observe m.toLmTreeBorrows 15 = .memoryLeak) ∧
    (mrObserve m 16 = .okDealloc ∧ c.lm.observe m.toLmTreeBorrows 16 = .okDealloc) ∧
    (mrObserve m 17 = .okDealloc ∧ c.lm.observe m.toLmTreeBorrows 17 = .okDealloc) ∧
    (mrObserve m 23 = .okBool true ∧ c.lm.observe m.toLmTreeBorrows 23 = .okBool true) ∧
    (mrObserve m 24 = .okBool false ∧ c.lm.observe m.toLmTreeBorrows 24 = .okBool false) ∧
    (mrObserve m 25 = .okBool true ∧ c.lm.observe m.toLmTreeBorrows 25 = .okBool true) ∧
    (mrObserve m 26 = .okBool false ∧ c.lm.observe m.toLmTreeBorrows 26 = .okBool false) ∧
    (mrObserve m 27 = .okBool true ∧ c.lm.observe m.toLmTreeBorrows 27 = .okBool true) := by
  have cell : ∀ idx, idx < 28 → ∀ o, mrExpected m idx = o →
      mrObserve m idx = o ∧ c.lm.observe m.toLmTreeBorrows idx = o := fun idx h o ho => by
    have hIdx : idx < canonicalCaseCount := Nat.lt_trans h (by decide)
    have hA := c.agreement_zone_exact m idx hIdx ((caseClass_agreement_iff idx hIdx).mpr h)
    have hM := (mrObserve_table m idx hIdx).trans ho
    exact ⟨hM, hA.symm.trans hM⟩
  exact ⟨cell 13 (by decide) _ (by cases m <;> rfl), cell 14 (by decide) _ (by cases m <;> rfl),
    cell 15 (by decide) _ (by cases m <;> rfl), cell 16 (by decide) _ (by cases m <;> rfl),
    cell 17 (by decide) _ (by cases m <;> rfl), cell 23 (by decide) _ (by cases m <;> rfl),
    cell 24 (by decide) _ (by cases m <;> rfl), cell 25 (by decide) _ (by cases m <;> rfl),
    cell 26 (by decide) _ (by cases m <;> rfl), cell 27 (by decide) _ (by cases m <;> rfl)⟩

/-! ## §6. Direct Bridge to Unmodified `Trusted.Rustc.V2026_06_01.MirSemantics` -/

section TrustedBridge

open Trusted.Rustc.V2026_06_01.Layout (LayoutTable)
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Sequence

/-! ### §6.1 Protector-preventing-deallocation (`rust#165833`) -/

/-- Embedding of the Anneal Tree Borrows permission into MiniRust's protected
permission. Every Anneal tag performed its initial child access when created, so
MiniRust's `had_local_read` is `true` for `.reservedFrz` / `.reservedIM` / `.frozen`. -/
def trustedPermToMrProt : TreeBorrowPerm → MiniRustSpec.Gen.PermissionProt
  | .cell => .Cell
  | .reservedFrz conflicted => .Reserved true conflicted
  | .reservedIM => .Reserved true false
  | .unique => .Unique
  | .frozen => .Frozen true
  | .disabled => .Disabled

/-- **Exact permission correspondence**: the Trusted `preventsDeallocation` is
MiniRust's `PermissionProt::prevents_deallocation` on the embedded permission. -/
theorem preventsDeallocation_eq_mr (p : TreeBorrowPerm) :
    preventsDeallocation p =
      MiniRustSpec.Interp.PermissionProt.prevents_deallocation (trustedPermToMrProt p) := by
  cases p <;> rfl

/-- Universal classification of `preventsDeallocation`. -/
theorem preventsDeallocation_iff (p : TreeBorrowPerm) :
    preventsDeallocation p = true ↔ p ≠ .cell ∧ p ≠ .disabled := by
  cases p <;> simp [preventsDeallocation]

/-- The embedding hits exactly the deallocation-preventing MiniRust permissions:
a protected MiniRust permission prevents deallocation iff it is the image of a
Trusted permission that prevents deallocation. -/
theorem mr_prevents_deallocation_iff_trusted (q : MiniRustSpec.Gen.PermissionProt) :
    MiniRustSpec.Interp.PermissionProt.prevents_deallocation q = true ↔
      ∃ p, trustedPermToMrProt p = q ∧ preventsDeallocation p = true := by
  constructor
  · intro h
    cases q with
    | Cell => cases h
    | Reserved r f =>
      cases r with
      | false => cases h
      | true => exact ⟨.reservedFrz f, rfl, rfl⟩
    | Unique => exact ⟨.unique, rfl, rfl⟩
    | Frozen r =>
      cases r with
      | false => cases h
      | true => exact ⟨.frozen, rfl, rfl⟩
    | Disabled => cases h
  · rintro ⟨p, rfl, hp⟩
    rw [← preventsDeallocation_eq_mr]; exact hp

/-- And through MiniRust's combined `Permission::prevents_deallocation` (`Prot`). -/
theorem preventsDeallocation_eq_mr_permission (p : TreeBorrowPerm) :
    preventsDeallocation p =
      MiniRustSpec.Interp.Permission.prevents_deallocation (.Prot (trustedPermToMrProt p)) := by
  cases p <;> rfl

/-- Embed a single Trusted `BorrowEntry` under active protector list `ap` as a
MiniRust Tree Borrows leaf `Node`: strongly protected iff `isBorrowProtected ap e`. -/
def trustedBorrowToMrLeaf (ap : List Nat) (e : BorrowEntry) : MiniRustSpec.Gen.Node :=
  ⟨[], [.Prot (trustedPermToMrProt e.perm)], if isBorrowProtected ap e then .Strong else .No⟩

/-- Embed every borrow targeting a local `< nLocals` of frame `depth` as children of an
unprotected root `Node` in MiniRust's Tree Borrows model. -/
def trustedFrameBorrowsToMrNode (borrows : List BorrowEntry) (ap : List Nat)
    (depth nLocals : Nat) : MiniRustSpec.Gen.Node :=
  let matching := borrows.filter fun e =>
    Nat.beq e.targetFrameDepth depth && Nat.blt e.targetLocal nLocals
  ⟨matching.map (trustedBorrowToMrLeaf ap), [.Unprot .Unique], .No⟩

/-- Embed every borrow targeting stack local `loc` of frame `depth` as children of an
unprotected root `Node` in MiniRust's Tree Borrows model. -/
def trustedLocalBorrowsToMrNode (borrows : List BorrowEntry) (ap : List Nat)
    (loc : Local) (depth : Nat) : MiniRustSpec.Gen.Node :=
  let matching := borrows.filter fun e =>
    Nat.beq e.targetFrameDepth depth && Nat.beq e.targetLocal loc
  ⟨matching.map (trustedBorrowToMrLeaf ap), [.Unprot .Unique], .No⟩

/-- Single-leaf equivalence: a leaf `trustedBorrowToMrLeaf ap e` triggers MiniRust's
`Node::contains_strong_protector_preventing_deallocation` iff the Trusted borrow is
protected and its permission prevents deallocation. -/
theorem trustedBorrowToMrLeaf_contains_strong_protector (ap : List Nat) (e : BorrowEntry) :
    MiniRustSpec.Interp.Node.contains_strong_protector_preventing_deallocation
        (trustedBorrowToMrLeaf ap e) =
      (isBorrowProtected ap e && preventsDeallocation e.perm) := by
  unfold trustedBorrowToMrLeaf
  rw [MiniRustSpec.HeapAllocAndWidePtrMR.node_contains_strong_protector_eq]
  simp only [MiniRustSpec.Interp.Node.anyChildPreventsDeallocation, Bool.or_false,
    List.any_cons, List.any_nil, Bool.or_false, ← preventsDeallocation_eq_mr_permission]
  cases isBorrowProtected ap e <;> simp

private theorem anyChildPreventsDeallocation_map_leaf (ap : List Nat) (es : List BorrowEntry) :
    MiniRustSpec.Interp.Node.anyChildPreventsDeallocation (es.map (trustedBorrowToMrLeaf ap)) =
      es.any (fun e => isBorrowProtected ap e && preventsDeallocation e.perm) := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.map_cons, MiniRustSpec.Interp.Node.anyChildPreventsDeallocation,
      trustedBorrowToMrLeaf_contains_strong_protector, ih, List.any_cons]

private theorem isBorrowProtected_nil (e : BorrowEntry) : isBorrowProtected [] e = false := by
  unfold isBorrowProtected
  cases e.protector <;> rfl

/-- **Universal `hasFrameDeallocProtectorConflict` ↔ MiniRust `Node` correspondence**:
for every borrow list, active protector set, frame depth, and local count, Anneal's
`hasFrameDeallocProtectorConflict` equals MiniRust's
`Node::contains_strong_protector_preventing_deallocation` on the embedded borrow tree. -/
theorem hasFrameDeallocProtectorConflict_eq_mr_node (borrows : List BorrowEntry) (ap : List Nat)
    (depth nLocals : Nat) :
    hasFrameDeallocProtectorConflict borrows ap depth nLocals =
      MiniRustSpec.Interp.Node.contains_strong_protector_preventing_deallocation
        (trustedFrameBorrowsToMrNode borrows ap depth nLocals) := by
  unfold trustedFrameBorrowsToMrNode
  rw [MiniRustSpec.HeapAllocAndWidePtrMR.node_contains_strong_protector_eq]
  simp only [reduceCtorEq, decide_false, Bool.false_and, Bool.false_or,
    anyChildPreventsDeallocation_map_leaf]
  cases ap with
  | nil =>
    have hL : hasFrameDeallocProtectorConflict borrows [] depth nLocals = false := by
      cases borrows <;> rfl
    rw [hL]
    symm
    cases h : ((borrows.filter fun e =>
        Nat.beq e.targetFrameDepth depth && Nat.blt e.targetLocal nLocals).any fun e =>
        isBorrowProtected [] e && preventsDeallocation e.perm) with
    | false => rfl
    | true =>
      obtain ⟨e, _, he⟩ := List.any_eq_true.mp h
      rw [isBorrowProtected_nil] at he
      cases he
  | cons a as =>
    induction borrows with
    | nil => rfl
    | cons e rest ih =>
      rw [hasFrameDeallocProtectorConflict, List.filter_cons]
      cases hm : (Nat.beq e.targetFrameDepth depth && Nat.blt e.targetLocal nLocals) with
      | false =>
        simp only [Bool.false_and, Bool.false_eq_true, ite_false]
        exact ih
      | true =>
        simp only [Bool.true_and, ite_true, List.any_cons]
        cases hp : (isBorrowProtected (a :: as) e && preventsDeallocation e.perm) with
        | true => rfl
        | false =>
          simp only [Bool.false_or]
          exact ih

/-- **Universal `hasProtectedLocalBorrow` ↔ MiniRust `Node` correspondence**:
for every borrow list, active protector set, local index, and frame depth, Anneal's
`hasProtectedLocalBorrow` equals MiniRust's
`Node::contains_strong_protector_preventing_deallocation` on the embedded local borrow tree. -/
theorem hasProtectedLocalBorrow_eq_mr_node (borrows : List BorrowEntry) (ap : List Nat)
    (loc : Local) (depth : Nat) :
    hasProtectedLocalBorrow borrows ap loc depth =
      MiniRustSpec.Interp.Node.contains_strong_protector_preventing_deallocation
        (trustedLocalBorrowsToMrNode borrows ap loc depth) := by
  unfold trustedLocalBorrowsToMrNode
  rw [MiniRustSpec.HeapAllocAndWidePtrMR.node_contains_strong_protector_eq]
  simp only [reduceCtorEq, decide_false, Bool.false_and, Bool.false_or,
    anyChildPreventsDeallocation_map_leaf]
  induction borrows with
  | nil => rfl
  | cons e rest ih =>
    rw [hasProtectedLocalBorrow, List.filter_cons]
    cases hm : (Nat.beq e.targetFrameDepth depth && Nat.beq e.targetLocal loc) with
    | false =>
      simp only [Bool.false_and, Bool.false_eq_true, ite_false]
      exact ih
    | true =>
      simp only [Bool.true_and, ite_true, List.any_cons]
      cases hp : (isBorrowProtected ap e && preventsDeallocation e.perm) with
      | true => rfl
      | false =>
        simp only [Bool.false_or]
        exact ih

/-- Universal characterization of `hasFrameDeallocProtectorConflict`: some borrow of a
local `< nLocals` of the frame at `depth` carries a still-active protector whose
permission prevents deallocation. -/
theorem hasFrameDeallocProtectorConflict_iff (borrows : List BorrowEntry) (ap : List Nat)
    (depth nLocals : Nat) :
    hasFrameDeallocProtectorConflict borrows ap depth nLocals = true ↔
      ap ≠ [] ∧ ∃ e ∈ borrows, e.targetFrameDepth = depth ∧ e.targetLocal < nLocals ∧
        isBorrowProtected ap e = true ∧ preventsDeallocation e.perm = true := by
  induction borrows with
  | nil =>
    cases ap <;> simp [hasFrameDeallocProtectorConflict]
  | cons e rest ih =>
    cases ap with
    | nil => simp [hasFrameDeallocProtectorConflict]
    | cons a as =>
      rw [hasFrameDeallocProtectorConflict]
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_and, List.mem_cons,
        exists_eq_or_imp] at ih ⊢
      rw [← ih]
      cases h : (Nat.beq e.targetFrameDepth depth && Nat.blt e.targetLocal nLocals &&
          (isBorrowProtected (a :: as) e && preventsDeallocation e.perm)) <;>
        simp_all [Nat.beq_eq, Nat.blt_eq]

/-- With no active protectors there is never a frame-deallocation conflict. -/
theorem hasFrameDeallocProtectorConflict_nil_protectors (borrows : List BorrowEntry)
    (depth nLocals : Nat) : hasFrameDeallocProtectorConflict borrows [] depth nLocals = false := by
  cases borrows <;> rfl

/-- Universal characterization of `hasProtectedLocalBorrow`. -/
theorem hasProtectedLocalBorrow_iff (borrows : List BorrowEntry) (ap : List Nat) (loc : Local)
    (d : Nat) :
    hasProtectedLocalBorrow borrows ap loc d = true ↔
      ∃ e ∈ borrows, e.targetFrameDepth = d ∧ e.targetLocal = loc ∧
        isBorrowProtected ap e = true ∧ preventsDeallocation e.perm = true := by
  induction borrows with
  | nil => simp [hasProtectedLocalBorrow]
  | cons e rest ih =>
    rw [hasProtectedLocalBorrow]
    simp only [List.mem_cons, exists_eq_or_imp]
    rw [← ih]
    cases h : (Nat.beq e.targetFrameDepth d && Nat.beq e.targetLocal loc &&
        (isBorrowProtected ap e && preventsDeallocation e.perm)) <;>
      simp_all [Nat.beq_eq]

/-- `natListContainsBool` is list membership. -/
theorem natListContainsBool_iff (xs : List Nat) (x : Nat) :
    natListContainsBool xs x = true ↔ x ∈ xs := by
  induction xs with
  | nil => simp [natListContainsBool]
  | cons y ys ih =>
    rw [natListContainsBool]
    cases h : Nat.beq y x with
    | true => simp [Nat.eq_of_beq_eq_true h]
    | false =>
      have hne : y ≠ x := Nat.ne_of_beq_eq_false h
      simp only [ih, List.mem_cons]
      exact ⟨Or.inr, fun h' => h'.elim (fun e => absurd e.symm hne) id⟩

/-- A borrow is protected exactly when its protector id is still active. -/
theorem isBorrowProtected_iff (ap : List Nat) (e : BorrowEntry) :
    isBorrowProtected ap e = true ↔ ∃ pid, e.protector = some pid ∧ pid ∈ ap := by
  unfold isBorrowProtected
  cases e.protector with
  | none => simp
  | some pid => simp [natListContainsBool_iff]

/-- A released protector (`protectorCallId ∉ activeProtectors`) protects nothing. -/
theorem isBorrowProtected_released (ap : List Nat) (e : BorrowEntry) (pid : Nat)
    (hp : e.protector = some pid) (hrel : pid ∉ ap) : isBorrowProtected ap e = false := by
  cases h : isBorrowProtected ap e with
  | false => rfl
  | true =>
    obtain ⟨pid', hp', hm⟩ := (isBorrowProtected_iff ap e).mp h
    rw [hp] at hp'; cases hp'; exact absurd hm hrel

/-- A single protected borrow of a frame local: the frame teardown conflicts exactly when
the protector is still active and the permission prevents deallocation (`.cell` and
`.disabled` never do — the `UnsafeCell` exemption of case `22`). -/
theorem hasFrameDeallocProtectorConflict_single (e : BorrowEntry) (ap : List Nat) (depth nLocals : Nat)
    (hd : e.targetFrameDepth = depth) (hl : e.targetLocal < nLocals) :
    hasFrameDeallocProtectorConflict [e] ap depth nLocals =
      (!ap.isEmpty && isBorrowProtected ap e && preventsDeallocation e.perm) := by
  cases ap with
  | nil => rfl
  | cons a as =>
    rw [hasFrameDeallocProtectorConflict]
    have h1 : Nat.beq e.targetFrameDepth depth = true := by rw [hd]; exact Nat.beq_refl depth
    have h2 : Nat.blt e.targetLocal nLocals = true := Nat.blt_eq.mpr hl
    rw [h1, h2]
    cases isBorrowProtected (a :: as) e <;> cases preventsDeallocation e.perm <;> rfl

/-- **Frame teardown faults on an active protector** (`evalTerminator` `.return_`): for
every machine state whose return place is initialized and whose frame carries an active
deallocation-preventing protected borrow, `return` is `MirStepNode.fail .ub`. -/
theorem evalTerminator_return_protector_ub (s : MachineState) (span : String)
    (cb : Option CapturedMir) (v : Value)
    (h0 : get? s.frame.locals 0 = some (.init v))
    (hc : hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
      (length s.memory.callStack) (length s.frame.locals) = true) :
    evalTerminator s { kind := .return_, span := span } cb = MirStepNode.fail .ub := by
  simp only [evalTerminator, h0, hc]

/-- The same frame teardown with no conflict proceeds past the protector check: at the
root frame with an initialized return value it returns normally after disabling every
tag of the frame's locals (`disableFrameBorrows`). -/
theorem evalTerminator_return_no_conflict_root (s : MachineState) (span : String)
    (cb : Option CapturedMir) (v : Value)
    (h0 : get? s.frame.locals 0 = some (.init v))
    (hc : hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
      (length s.memory.callStack) (length s.frame.locals) = false)
    (hstack : s.memory.callStack = [])
    (hinit : valueContainsUninit v = false) :
    evalTerminator s { kind := .return_, span := span } cb =
      MirStepNode.retNormal v { s.memory with
        borrows := disableFrameBorrows s.memory.borrows 0 (length s.frame.locals) } := by
  have hc' : hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
      (length ([] : List SavedCallerFrame)) (length s.frame.locals) = false := by
    rw [← hstack]; exact hc
  simp only [evalTerminator, h0, hstack, hc', hinit]
  rfl

/-- **Tail calls tear down the frame too** (`evalTailCallTerminator`): once the callee
and arguments resolve, an active deallocation-preventing protector faults with `.ub`. -/
theorem evalTailCallTerminator_protector_ub (s : MachineState) (func : Operand)
    (argOps : List Operand) (body : CapturedMir) (target : ResolvedCallTarget)
    (l₁ : List LocalSlot) (argVals : List Value) (l₂ : List LocalSlot)
    (hr : resolveCallTarget s func (length argOps) body.localDecls body.layouts = .ok target l₁)
    (ha : evalOperands l₁ argOps s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) = .ok argVals l₂)
    (hc : hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
      (length s.memory.callStack) (length s.frame.locals) = true) :
    evalTailCallTerminator s func argOps (some body) = MirStepNode.fail .ub := by
  simp only [evalTailCallTerminator, bodyLocalDeclsOf, hr, ha, hc]

/-- **Tail call without a protector conflict steps directly into `enterTailCalleeFrame`**
after disabling the outgoing frame's borrows (`disableFrameBorrows`): universal positive
counterpart to `evalTailCallTerminator_protector_ub`. -/
theorem evalTailCallTerminator_no_conflict_steps (s : MachineState) (func : Operand)
    (argOps : List Operand) (body calleeBody : CapturedMir) (target : ResolvedCallTarget)
    (l₁ : List LocalSlot) (argVals : List Value) (l₂ : List LocalSlot)
    (hr : resolveCallTarget s func (length argOps) body.localDecls body.layouts = .ok target l₁)
    (ha : evalOperands l₁ argOps s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) = .ok argVals l₂)
    (hc : hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
      (length s.memory.callStack) (length s.frame.locals) = false)
    (hlookup : lookupCallee s.memory.callees body.layouts target.defPath target.typeArgs
      s.memory.traitImpls = .some calleeBody)
    (hcompat : checkCalleeTargetCompatible target calleeBody (length argVals) = true) :
    evalTailCallTerminator s func argOps (some body) =
      MirStepNode.step
        (enterTailCalleeFrame
          { s.memory with
            borrows := disableFrameBorrows s.memory.borrows (length s.memory.callStack)
              (length s.frame.locals) }
          calleeBody argVals) := by
  simp only [evalTailCallTerminator, bodyLocalDeclsOf, hr, ha, hc, hlookup, hcompat]

/-- **Per-local `StorageDead` faults when MiniRust's embedded local borrow tree has a
strong deallocation-preventing protector** (`evalStmt` `.storageDead`, linked directly
through `hasProtectedLocalBorrow_eq_mr_node`). -/
theorem evalStmt_storageDead_protector_ub (s : MachineState) (loc : Local) (slot : LocalSlot)
    (localsDead : List LocalSlot) (span : String) (decls : List LocalDecl) (layouts : LayoutTable)
    (hGet : get? s.frame.locals loc = .some slot)
    (hSet : set? s.frame.locals loc .dead = .some localsDead)
    (hMr : MiniRustSpec.Interp.Node.contains_strong_protector_preventing_deallocation
      (trustedLocalBorrowsToMrNode s.memory.borrows s.memory.activeProtectors loc
        (length s.memory.callStack)) = true) :
    evalStmt s ⟨.storageDead loc, span⟩ decls layouts = MirStepNode.fail .ub := by
  have hProt : hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc
      (length s.memory.callStack) = true := by
    rw [hasProtectedLocalBorrow_eq_mr_node]; exact hMr
  exact (evalStmt_storageDead_purges_borrows s loc slot localsDead span decls layouts).2.1
    hGet hSet hProt

/-- **Per-local `StorageDead` succeeds and purges borrows when no strong protector blocks
deallocation** (including released protectors and protected `.cell` / `.disabled` tags). -/
theorem evalStmt_storageDead_no_conflict_steps (s : MachineState) (loc : Local) (slot : LocalSlot)
    (localsDead : List LocalSlot) (span : String) (decls : List LocalDecl) (layouts : LayoutTable)
    (hGet : get? s.frame.locals loc = .some slot)
    (hSet : set? s.frame.locals loc .dead = .some localsDead)
    (hMr : MiniRustSpec.Interp.Node.contains_strong_protector_preventing_deallocation
      (trustedLocalBorrowsToMrNode s.memory.borrows s.memory.activeProtectors loc
        (length s.memory.callStack)) = false) :
    evalStmt s ⟨.storageDead loc, span⟩ decls layouts =
      MirStepNode.step (advanceStmt s localsDead
        { s.memory with borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) }) := by
  have hProt : hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc
      (length s.memory.callStack) = false := by
    rw [hasProtectedLocalBorrow_eq_mr_node]; exact hMr
  exact ((evalStmt_storageDead_purges_borrows s loc slot localsDead span decls layouts).1
    hGet hSet hProt).1

/-- **Per-local `StorageLive` (implicit prior-storage deallocation) faults on a strong
protector conflict**, matching MiniRust's embedded local borrow tree. -/
theorem evalStmt_storageLive_protector_ub (s : MachineState) (loc : Local) (slot : LocalSlot)
    (localsUninit : List LocalSlot) (span : String) (decls : List LocalDecl) (layouts : LayoutTable)
    (hGet : get? s.frame.locals loc = .some slot)
    (hSet : set? s.frame.locals loc .uninit = .some localsUninit)
    (hMr : MiniRustSpec.Interp.Node.contains_strong_protector_preventing_deallocation
      (trustedLocalBorrowsToMrNode s.memory.borrows s.memory.activeProtectors loc
        (length s.memory.callStack)) = true) :
    evalStmt s ⟨.storageLive loc, span⟩ decls layouts = MirStepNode.fail .ub := by
  have hProt : hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc
      (length s.memory.callStack) = true := by
    rw [hasProtectedLocalBorrow_eq_mr_node]; exact hMr
  exact (evalStmt_storageLive_purges_borrows s loc slot localsUninit span decls layouts).2.1
    hGet hSet hProt

/-- **Callee `return_` releases callee protectors via `restoreCallerProtectors`** (the
Trusted operational counterpart of MiniRust `end_call` / LeanMiri `releaseProtector`,
Case `19 → 20`): once a non-diverging callee frame returns without conflicting on its own
locals, `activeProtectors` becomes `restoreCallerProtectors caller`, so any callee
protector `pid ∉ restoreCallerProtectors caller` no longer protects any borrow entry. -/
theorem evalTerminator_callee_return_releases_protector (s : MachineState) (span : String)
    (cb : Option CapturedMir) (v : Value) (caller : SavedCallerFrame)
    (restStack : List SavedCallerFrame) (updatedCallerLocals : List LocalSlot) (mem' : Memory)
    (h0 : get? s.frame.locals 0 = some (.init v))
    (hstack : s.memory.callStack = caller :: restStack)
    (hc : hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
      (length s.memory.callStack) (length s.frame.locals) = false)
    (hdiv : caller.isDiverging = false)
    (hinit : valueContainsUninit v = false)
    (hwrite : writeReturnDestination caller.frame.locals
      { s.memory with
        borrows := disableFrameBorrows s.memory.borrows (length (caller :: restStack)) (length s.frame.locals)
        callStack := restStack
        activeCallee := .some caller.callerBody
        activeProtectors := restoreCallerProtectors caller }
      caller.destination v caller.callerBody.localDecls caller.callerBody.layouts =
      .ok updatedCallerLocals mem') :
    evalTerminator s { kind := .return_, span := span } cb =
      MirStepNode.step
        { frame := { blockIdx := caller.returnTarget, stmtIdx := 0, locals := updatedCallerLocals }
          memory := mem' } ∧
    (∀ (e : BorrowEntry) (pid : Nat), e.protector = some pid →
      pid ∉ restoreCallerProtectors caller →
      isBorrowProtected (restoreCallerProtectors caller) e = false) := by
  have hc' : hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
      (length (caller :: restStack)) (length s.frame.locals) = false := by
    rw [← hstack]; exact hc
  refine ⟨?_, fun e pid hp hrel => isBorrowProtected_released _ e pid hp hrel⟩
  simp only [evalTerminator, h0, hstack, hc', hdiv, hinit, hwrite]

/-! #### Concrete `evalTerminator` / `stepMirFn` executions (cases `19`, `20`, `22`) -/

/-- A unit return layout for the protector fixture. -/
def hwUnitLayout : Trusted.Rustc.V2026_06_01.Layout.TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }

/-- Minimal `Runtime(PostCleanup)` body builder. -/
def hwMirBody (defPath : String) (decls : List LocalDecl) (argCount : Nat)
    (blocks : List BasicBlockData) : CapturedMir :=
  { defPath, phase := .runtimePostCleanup, role := .subject, argCount, localDecls := decls,
    basicBlocks := blocks, layouts := emptyLayoutTable, allocations := [],
    fnAbi := { args := [], ret := { layout := hwUnitLayout, mode := .direct },
               conv := .rust, canUnwind := true } }

@[reducible] def hwDecl (kind : RigidTy) : LocalDecl :=
  { mutability := .mut, ty := { kind := kind, layoutIdx := 0 }, debugName := none }

/-- `fn f(_1: &u32) -> () { return }`: the frame owns `_1`, whose protected borrow is
the strongly protected child of the scenario. -/
def hwTeardownBody : CapturedMir :=
  hwMirBody "hw::protected_teardown" [hwDecl (.tuple []), hwDecl (.uint .u32)] 1
    [{ statements := [], terminator := { kind := .return_, span := "hw.rs:1:1" }, isCleanup := false }]

/-- A function-entry protected borrow (protector call id `1`) of local `_1` with
Tree Borrows permission `perm`. -/
def hwProtectedEntry (perm : TreeBorrowPerm) : BorrowEntry :=
  { tag := 1, targetLocal := 1, targetProjection := [], perm := perm, protector := some 1 }

/-- Root-frame state at the `return` of `hwTeardownBody`, protector active iff `active`. -/
def hwTeardownState (perm : TreeBorrowPerm) (active : Bool) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0,
               locals := [.init (.aggregate 0 []), .init (.scalar ⟨42, 4⟩)] },
    memory := { borrows := [hwProtectedEntry perm],
                activeProtectors := if active then [1] else [] } }

/-- Observation of one Trusted transition in the shared `HeapWideObs` domain: a root
normal return (the frame was torn down, its locals deallocated) is `.okDealloc`, a
`.ub` fault is `.ub`. -/
def trustedStepObs : MirStepNode → HeapWideObs
  | .ret (.normal _) => .okDealloc
  | .vis (.inl (.fail .ub)) _ => .ub
  | _ => .invalidOrUnsupported

/-- Run `stepMirFn` on the teardown fixture. -/
def trustedTeardownObs (perm : TreeBorrowPerm) (active : Bool) : HeapWideObs :=
  trustedStepObs (stepMirFn hwTeardownBody (hwTeardownState perm active))

/-- Run `evalTerminator` directly on the teardown fixture. -/
def trustedTeardownTermObs (perm : TreeBorrowPerm) (active : Bool) : HeapWideObs :=
  trustedStepObs (evalTerminator (hwTeardownState perm active)
    { kind := .return_, span := "hw.rs:1:1" } (some hwTeardownBody))

/-- **Concrete Trusted protector table**: deallocating (tearing down) the frame while an
active `.frozen` / `.unique` / `.reservedFrz` / `.reservedIM` protector is live is `.ub`
(case `19`); after the protector is released it succeeds (case `20`); a protected `.cell`
(`UnsafeCell`) or `.disabled` tag never blocks it (case `22`). Executed by the real
`stepMirFn` and `evalTerminator`. -/
theorem trustedTeardown_table :
    trustedTeardownObs .frozen true = .ub ∧
    trustedTeardownObs .unique true = .ub ∧
    trustedTeardownObs (.reservedFrz false) true = .ub ∧
    trustedTeardownObs .reservedIM true = .ub ∧
    trustedTeardownObs .frozen false = .okDealloc ∧
    trustedTeardownObs .unique false = .okDealloc ∧
    trustedTeardownObs .cell true = .okDealloc ∧
    trustedTeardownObs .disabled true = .okDealloc ∧
    trustedTeardownTermObs .frozen true = .ub ∧
    trustedTeardownTermObs .frozen false = .okDealloc ∧
    trustedTeardownTermObs .cell true = .okDealloc := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **Trusted ↔ MiniRust protector correspondence on cases `19`, `20`, `22`**: the
Trusted frame-teardown verdicts coincide with MiniRust's `MachTB` verdicts. -/
theorem trusted_protector_cases_match_mr :
    trustedTeardownObs .frozen true = mrObserve .treeBorrows 19 ∧
    trustedTeardownObs .frozen false = mrObserve .treeBorrows 20 ∧
    trustedTeardownObs .cell true = mrObserve .treeBorrows 22 := by
  rw [mrObserve_table _ 19 (by decide), mrObserve_table _ 20 (by decide),
    mrObserve_table _ 22 (by decide)]
  exact ⟨trustedTeardown_table.1, trustedTeardown_table.2.2.2.2.1,
    trustedTeardown_table.2.2.2.2.2.2.1⟩

/-- Bounded multi-step runner for Trusted teardown / `StorageDead` fixtures: a root normal
return is `.okDealloc`, a `.ub` fault is `.ub`. -/
def trustedDeallocRun (body : CapturedMir) : Nat → MachineState → HeapWideObs
  | 0, _ => .invalidOrUnsupported
  | fuel + 1, s =>
    match stepMirFn body s with
    | .tau (.running s') => trustedDeallocRun body fuel s'
    | .ret (.normal _) => .okDealloc
    | .vis (.inl (.fail .ub)) _ => .ub
    | _ => .invalidOrUnsupported

/-- `fn(_1: u32) -> () { StorageDead(_1); return }`: explicit per-local deallocation via
`evalStmt` `.storageDead` (`hasProtectedLocalBorrow`). -/
def hwStorageDeadBody : CapturedMir :=
  hwMirBody "hw::storage_dead" [hwDecl (.tuple []), hwDecl (.uint .u32)] 1
    [{ statements := [{ kind := .storageDead 1, span := "hw.rs:1:1" }],
       terminator := { kind := .return_, span := "hw.rs:1:2" }, isCleanup := false }]

/-- Run `StorageDead(_1)` + `return_` through `stepMirFn`. -/
def trustedStorageDeadObs (perm : TreeBorrowPerm) (active : Bool) : HeapWideObs :=
  trustedDeallocRun hwStorageDeadBody 4 (hwTeardownState perm active)

/-- Trivial callee `fn() -> () { return }` used to execute the real callee-return
protector release (`restoreCallerProtectors`) before caller `StorageDead(_1)`. -/
def hwCalleeBody : CapturedMir :=
  hwMirBody "hw::release_callee" [hwDecl (.tuple [])] 0
    [{ statements := [], terminator := { kind := .return_, span := "hw.rs:2:1" }, isCleanup := false }]

/-- Two-frame state inside `hwCalleeBody` with active protector `1` guarding caller local
`_1` (`targetFrameDepth = 0`, `perm = .frozen`): returning from `hwCalleeBody` releases
protector `1` via `restoreCallerProtectors`, allowing caller `StorageDead(_1)` to succeed
(genuine operational Case `19 → 20` transition). -/
def hwSavedCaller (callerKeeps : Bool) : SavedCallerFrame :=
  { callerBody := hwStorageDeadBody
    frame := { blockIdx := 0, stmtIdx := 0,
               locals := [.init (.aggregate 0 []), .init (.scalar ⟨42, 4⟩)] }
    destination := { local_ := 0, projection := [] }
    returnTarget := 0
    callerProtector := if callerKeeps then some 1 else none
    calleeProtectors := []
    returnUnwind := .continue_
    isDiverging := false }

/-- Two-frame state inside `hwCalleeBody`; the saved caller frame re-installs protector
`1` on return iff `callerKeeps`. -/
def hwCalleeReturnState (callerKeeps : Bool) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.init (.aggregate 0 [])] }
    memory := { borrows := [hwProtectedEntry .frozen]
                activeProtectors := [1]
                callStack := [hwSavedCaller callerKeeps]
                activeCallee := some hwCalleeBody } }

/-- The releasing variant (`callerProtector := none`): returning drops protector `1`. -/
def hwCalleeReleaseState : MachineState := hwCalleeReturnState false

/-- Multi-step execution of callee return (releasing protector `1`) followed by caller
`StorageDead(_1)` + `return_`. -/
def trustedCalleeReleaseThenDeallocObs : HeapWideObs :=
  trustedDeallocRun hwStorageDeadBody 6 hwCalleeReleaseState

/-- Concrete tail-call protector conflict fixture (`evalTailCallTerminator`). -/
def trustedTailCallObs (perm : TreeBorrowPerm) (active : Bool) : HeapWideObs :=
  let fnOp : Operand :=
    .constant { ty := { kind := .fnDef "hw::tail_callee" [], layoutIdx := 0 },
                val := .unevaluated "hw::tail_callee" }
  trustedStepObs (evalTailCallTerminator (hwTeardownState perm active) fnOp [] (some hwTeardownBody))

/-- Callee return when the caller's saved frame re-installs protector `1`
(`callerProtector := some 1`): the same caller `StorageDead(_1)` must still fault. -/
def trustedCalleeKeepThenDeallocObs : HeapWideObs :=
  trustedDeallocRun hwStorageDeadBody 6 (hwCalleeReturnState true)

/-- **Non-vacuity twins** of the protector witnesses: (1) the callee-return release is
the *only* difference between `.okDealloc` and `.ub` — the identical 2-frame run whose
caller frame re-installs protector `1` via `restoreCallerProtectors` faults at
`StorageDead(_1)`; (2) the tail-call `.ub` is caused by the protector check alone —
without an active protector, or with a protected `.cell`, the same `evalTailCallTerminator`
proceeds past teardown to the external tail call (not `.ub`); (3) the teardown `.ub` needs
both an active protector and a deallocation-preventing permission. -/
theorem trusted_protector_twins_table :
    trustedCalleeKeepThenDeallocObs = .ub ∧
    trustedCalleeReleaseThenDeallocObs = .okDealloc ∧
    restoreCallerProtectors (hwSavedCaller true) = [1] ∧
    restoreCallerProtectors (hwSavedCaller false) = [] ∧
    trustedTailCallObs .frozen true = .ub ∧
    trustedTailCallObs .frozen false = .invalidOrUnsupported ∧
    trustedTailCallObs .cell true = .invalidOrUnsupported ∧
    trustedTailCallObs .disabled true = .invalidOrUnsupported ∧
    trustedTeardownObs .reservedIM false = .okDealloc ∧
    trustedStorageDeadObs .disabled true = .okDealloc ∧
    trustedStorageDeadObs (.reservedFrz true) true = .ub := by
  refine ⟨?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Real tail-call callee body `fn hw::tail_callee() -> () { return }` registered in
`memory.callees` so non-conflicting tail calls execute end-to-end to normal return
(`.okDealloc`) instead of collapsing into `.invalidOrUnsupported`. -/
def hwTailCalleeBody : CapturedMir :=
  hwMirBody "hw::tail_callee" [hwDecl (.tuple [])] 0
    [{ statements := [{ kind := .assign { local_ := 0, projection := [] } (.aggregate .tuple []),
                        span := "hw.rs:4:1" }],
       terminator := { kind := .return_, span := "hw.rs:4:2" }, isCleanup := false }]

/-- Caller body whose terminator is `.tailCall hw::tail_callee []`. -/
def hwTailCallBody : CapturedMir :=
  let fnOp : Operand :=
    .constant { ty := { kind := .fnDef "hw::tail_callee" [], layoutIdx := 0 },
                val := .unevaluated "hw::tail_callee" }
  hwMirBody "hw::tail_caller" [hwDecl (.tuple []), hwDecl (.uint .u32)] 1
    [{ statements := [],
       terminator := { kind := .tailCall fnOp [], span := "hw.rs:3:1" }, isCleanup := false }]

/-- Execute `hwTailCallBody` end-to-end through `stepMirFn` → `evalTailCallTerminator` →
`enterTailCalleeFrame` → `hwTailCalleeBody` `return_` with `hwTailCalleeBody` registered. -/
def trustedTailCallRunObs (perm : TreeBorrowPerm) (active : Bool) : HeapWideObs :=
  let s0 := hwTeardownState perm active
  let s := { s0 with memory := { s0.memory with callees := [hwTailCalleeBody] } }
  trustedDeallocRun hwTailCallBody 6 s

/-- **Lossless end-to-end tail-call non-vacuity table**: with `hwTailCalleeBody`
registered, active `.frozen`/`.unique` protectors fault `.ub` at `evalTailCallTerminator`,
whereas released protectors and protected `.cell`/`.disabled` tags genuinely enter
`hwTailCalleeBody` (`enterTailCalleeFrame`) and return normally (`.okDealloc`), matching
MiniRust `MachTB` cases `19`, `20`, `22`. -/
theorem trustedTailCallRun_table :
    trustedTailCallRunObs .frozen true = .ub ∧
    trustedTailCallRunObs .unique true = .ub ∧
    trustedTailCallRunObs .frozen false = .okDealloc ∧
    trustedTailCallRunObs .cell true = .okDealloc ∧
    trustedTailCallRunObs .disabled true = .okDealloc ∧
    trustedTailCallRunObs .frozen true = mrObserve .treeBorrows 19 ∧
    trustedTailCallRunObs .frozen false = mrObserve .treeBorrows 20 ∧
    trustedTailCallRunObs .cell true = mrObserve .treeBorrows 22 := by
  have h1 : trustedTailCallRunObs .frozen true = .ub := by decide +kernel
  have h2 : trustedTailCallRunObs .unique true = .ub := by decide +kernel
  have h3 : trustedTailCallRunObs .frozen false = .okDealloc := by decide +kernel
  have h4 : trustedTailCallRunObs .cell true = .okDealloc := by decide +kernel
  have h5 : trustedTailCallRunObs .disabled true = .okDealloc := by decide +kernel
  rw [mrObserve_table _ 19 (by decide), mrObserve_table _ 20 (by decide),
    mrObserve_table _ 22 (by decide)]
  exact ⟨h1, h2, h3, h4, h5, h1, h3, h4⟩

/-- **Concrete `StorageDead`, 2-frame callee-return protector release (`19 → 20`), and
tail-call protector execution table** through real `stepMirFn` / `evalStmt` /
`evalTailCallTerminator`, matching MiniRust `MachTB` cases `19`, `20`, `22`. -/
theorem trustedStorageDead_and_release_table :
    trustedStorageDeadObs .frozen true = .ub ∧
    trustedStorageDeadObs .unique true = .ub ∧
    trustedStorageDeadObs .frozen false = .okDealloc ∧
    trustedStorageDeadObs .cell true = .okDealloc ∧
    trustedCalleeReleaseThenDeallocObs = .okDealloc ∧
    trustedTailCallObs .frozen true = .ub ∧
    trustedStorageDeadObs .frozen true = mrObserve .treeBorrows 19 ∧
    trustedCalleeReleaseThenDeallocObs = mrObserve .treeBorrows 20 ∧
    trustedStorageDeadObs .cell true = mrObserve .treeBorrows 22 := by
  have h1 : trustedStorageDeadObs .frozen true = .ub := by decide +kernel
  have h2 : trustedStorageDeadObs .unique true = .ub := by decide +kernel
  have h3 : trustedStorageDeadObs .frozen false = .okDealloc := by decide +kernel
  have h4 : trustedStorageDeadObs .cell true = .okDealloc := by decide +kernel
  have h5 : trustedCalleeReleaseThenDeallocObs = .okDealloc := by decide +kernel
  have h6 : trustedTailCallObs .frozen true = .ub := by decide +kernel
  rw [mrObserve_table _ 19 (by decide), mrObserve_table _ 20 (by decide),
    mrObserve_table _ 22 (by decide)]
  exact ⟨h1, h2, h3, h4, h5, h6, h1, h5, h4⟩

/-! ### §6.2 Wide-pointer `addr_eq` metadata erasure (`rust#166144`) -/

/-- **Slice → thin cast erases the length** (`evalCastPtrToPtr`): on a 64-bit layout, a
wide slice pointer `(p, metaSc)` to an unborrowed (heap) allocation cast to any thin raw
pointer type yields exactly `.ptr p 8`, for every `metaSc`. -/
theorem evalCastPtrToPtr_slice_to_thin (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (decls : List LocalDecl) (layouts : LayoutTable) (p : ProvenancePtr)
    (metaSc : ScalarInt) (locals' : List LocalSlot)
    (hPB : layoutPointerBytes layouts = 8)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.aggregate 0 [.ptr p 8, .scalar metaSc]) locals')
    (hMeta : metaSc.sizeBytes = 8) (hThin : isThinRawPtrTy targetTy = true)
    (hB : lookupBorrow mem.borrows p.tag = none) :
    evalCastPtrToPtr locals op targetTy mem decls layouts = .ok (.ptr p 8) locals' mem := by
  unfold evalCastPtrToPtr
  simp only [hPB, hOp, hMeta, hThin, hB, Nat.beq_refl, Bool.and_self]

/-- **Trait-object → thin cast erases the vtable** (no borrow side-condition). -/
theorem evalCastPtrToPtr_dyn_to_thin (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (decls : List LocalDecl) (layouts : LayoutTable) (p vt : ProvenancePtr)
    (locals' : List LocalSlot)
    (hPB : layoutPointerBytes layouts = 8)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.aggregate 0 [.ptr p 8, .ptr vt 8]) locals')
    (hThin : isThinRawPtrTy targetTy = true) :
    evalCastPtrToPtr locals op targetTy mem decls layouts = .ok (.ptr p 8) locals' mem := by
  unfold evalCastPtrToPtr
  simp only [hPB, hOp, hThin, Nat.beq_refl, Bool.and_self]

/-- **Scalar-address wide → thin cast erases the metadata** (wrapped address). -/
theorem evalCastPtrToPtr_scalarPair_to_thin (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (decls : List LocalDecl) (layouts : LayoutTable) (addrSc metaSc : ScalarInt)
    (locals' : List LocalSlot)
    (hPB : layoutPointerBytes layouts = 8)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.aggregate 0 [.scalar addrSc, .scalar metaSc]) locals')
    (hA : addrSc.sizeBytes = 8) (hMeta : metaSc.sizeBytes = 8)
    (hThin : isThinRawPtrTy targetTy = true) :
    evalCastPtrToPtr locals op targetTy mem decls layouts =
      .ok (.scalar ⟨wrapScalarBits addrSc.bits (scalarModulus 8), 8⟩) locals' mem := by
  unfold evalCastPtrToPtr
  simp only [hPB, hOp, hA, hMeta, hThin, Nat.beq_refl, Bool.and_self]

/-- **Scalar-address trait-object → thin cast erases the vtable** (4th wide-pointer shape
of `evalCastPtrToPtr`: `.aggregate 0 [.scalar addrSc, .ptr vt 8]`). -/
theorem evalCastPtrToPtr_scalarDyn_to_thin (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (decls : List LocalDecl) (layouts : LayoutTable) (addrSc : ScalarInt)
    (vt : ProvenancePtr) (locals' : List LocalSlot)
    (hPB : layoutPointerBytes layouts = 8)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.aggregate 0 [.scalar addrSc, .ptr vt 8]) locals')
    (hA : addrSc.sizeBytes = 8) (hThin : isThinRawPtrTy targetTy = true) :
    evalCastPtrToPtr locals op targetTy mem decls layouts =
      .ok (.scalar ⟨wrapScalarBits addrSc.bits (scalarModulus 8), 8⟩) locals' mem := by
  unfold evalCastPtrToPtr
  simp only [hPB, hOp, hA, hThin, Nat.beq_refl, Bool.and_self]

/-- An unborrowed (heap / global) pointer's comparison address is `ptrToAddrScalar`. -/
theorem ptrAddressScalar?_unborrowed (locals : List LocalSlot) (borrows : List BorrowEntry)
    (callerLocals : List LocalSlot) (decls : List LocalDecl) (layouts : LayoutTable)
    (ptrBytes : Nat) (p : ProvenancePtr) (sz : Nat) (callStack : List SavedCallerFrame)
    (hB : lookupBorrow borrows p.tag = none) :
    ptrAddressScalar? locals borrows callerLocals decls layouts ptrBytes p sz callStack =
      some (ptrToAddrScalar p sz) := by
  simp only [ptrAddressScalar?, ptrAddress?, hB, ptrToAddrScalar]

/-- `ptrToAddrScalar` sees only the page address `allocId * 65536 + offsetBytes`: any two
pointers at the same address (whatever their provenance tags) have equal scalars. -/
theorem ptrToAddrScalar_addr_only (p q : ProvenancePtr) (sz : Nat)
    (h : p.allocId * 65536 + p.offsetBytes = q.allocId * 65536 + q.offsetBytes) :
    ptrToAddrScalar p sz = ptrToAddrScalar q sz := by
  simp only [ptrToAddrScalar, Nat.add_eq, Nat.mul_eq, h]

/-- `BinOp.eq` on two 8-byte scalars is bit equality. -/
theorem evalScalarBinOp_eq_ptrAddr (p₁ p₂ : ProvenancePtr) (l : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .eq (ptrToAddrScalar p₁ 8) (ptrToAddrScalar p₂ 8) l mem false =
      .ok (.scalar (boolToScalar (Nat.beq (ptrToAddrScalar p₁ 8).bits (ptrToAddrScalar p₂ 8).bits)))
        l mem := by
  rfl

/-- **Thin-pointer `==` compares only `ptrToAddrScalar`** (`evalRvalue` `.binaryOp`): for two
unborrowed thin pointers, relational `BinOp.eq` is `evalScalarBinOp` on their page
addresses, erasing provenance tags. -/
theorem evalRvalue_thinPtr_eq (locals : List LocalSlot) (mem : Memory) (decls : List LocalDecl)
    (layouts : LayoutTable) (lhsOp rhsOp : Operand) (p₁ p₂ : ProvenancePtr)
    (l₁ l₂ : List LocalSlot)
    (h1 : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.ptr p₁ 8) l₁)
    (h2 : evalOperand l₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.ptr p₂ 8) l₂)
    (hRel : isPtrRelationalBinOp .eq decls layouts lhsOp rhsOp = true)
    (hB1 : lookupBorrow mem.borrows p₁.tag = none) (hB2 : lookupBorrow mem.borrows p₂.tag = none) :
    evalRvalue locals (.binaryOp .eq lhsOp rhsOp) mem decls layouts =
      .ok (.scalar (boolToScalar (Nat.beq (ptrToAddrScalar p₁ 8).bits (ptrToAddrScalar p₂ 8).bits)))
        l₂ mem := by
  rw [← evalScalarBinOp_eq_ptrAddr]
  simp only [evalRvalue, h1, h2, hRel,
    ptrAddressScalar?_unborrowed _ _ _ _ _ _ _ _ _ hB1,
    ptrAddressScalar?_unborrowed _ _ _ _ _ _ _ _ _ hB2]

/-- **Thin 64-bit scalar-address `==` compares only address bits** (composing directly with
`evalCastPtrToPtr_scalarPair_to_thin` and `evalCastPtrToPtr_scalarDyn_to_thin`). -/
theorem evalRvalue_thinScalar_eq (locals : List LocalSlot) (mem : Memory) (decls : List LocalDecl)
    (layouts : LayoutTable) (lhsOp rhsOp : Operand) (sc₁ sc₂ : ScalarInt)
    (l₁ l₂ : List LocalSlot)
    (h1 : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.scalar sc₁) l₁)
    (h2 : evalOperand l₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.scalar sc₂) l₂)
    (hSz1 : sc₁.sizeBytes = 8) (hSz2 : sc₂.sizeBytes = 8) :
    evalRvalue locals (.binaryOp .eq lhsOp rhsOp) mem decls layouts =
      .ok (.scalar (boolToScalar (Nat.beq sc₁.bits sc₂.bits))) l₂ mem := by
  simp only [evalRvalue, h1, h2, evalScalarBinOp, hSz1, hSz2]

private theorem resolveWideWordScalar?_ptr_unborrowed (locals : List LocalSlot)
    (borrows : List BorrowEntry) (callerLocals : List LocalSlot) (decls : List LocalDecl)
    (layouts : LayoutTable) (p : ProvenancePtr) (callStack : List SavedCallerFrame)
    (hB : lookupBorrow borrows p.tag = none) :
    resolveWideWordScalar? (.ptr p 8) locals borrows callerLocals decls layouts 8 callStack =
      some (ptrToAddrScalar p 8) := by
  simp only [resolveWideWordScalar?, ptrAddressScalar?_unborrowed _ _ _ _ _ _ _ _ _ hB]

private theorem resolveWideWordScalar?_scalar8 (locals : List LocalSlot)
    (borrows : List BorrowEntry) (callerLocals : List LocalSlot) (decls : List LocalDecl)
    (layouts : LayoutTable) (sc : ScalarInt) (callStack : List SavedCallerFrame)
    (hSz : sc.sizeBytes = 8) :
    resolveWideWordScalar? (.scalar sc) locals borrows callerLocals decls layouts 8 callStack =
      some ⟨wrapScalarBits sc.bits (scalarModulus 8), 8⟩ := by
  simp only [resolveWideWordScalar?, hSz, Nat.beq_refl]

private theorem evalWidePtrRelBinOp_eq_of_resolved (lhsThin lhsMeta rhsThin rhsMeta : Value)
    (l₂ : List LocalSlot) (mem : Memory) (decls : List LocalDecl) (layouts : LayoutTable)
    (a₁ a₂ m₁ m₂ : ScalarInt)
    (ha₁ : resolveWideWordScalar? lhsThin l₂ mem.borrows mem.callerLocals decls layouts 8 mem.callStack = some a₁)
    (ha₂ : resolveWideWordScalar? rhsThin l₂ mem.borrows mem.callerLocals decls layouts 8 mem.callStack = some a₂)
    (hm₁ : resolveWideWordScalar? lhsMeta l₂ mem.borrows mem.callerLocals decls layouts 8 mem.callStack = some m₁)
    (hm₂ : resolveWideWordScalar? rhsMeta l₂ mem.borrows mem.callerLocals decls layouts 8 mem.callStack = some m₂)
    (hszA1 : a₁.sizeBytes = 8) (hszA2 : a₂.sizeBytes = 8)
    (hszM1 : m₁.sizeBytes = 8) (hszM2 : m₂.sizeBytes = 8) :
    evalWidePtrRelBinOp .eq lhsThin lhsMeta rhsThin rhsMeta l₂ mem decls layouts 8 =
      .ok (.scalar (boolToScalar (Nat.beq a₁.bits a₂.bits && Nat.beq m₁.bits m₂.bits))) l₂ mem := by
  simp only [evalWidePtrRelBinOp, ha₁, ha₂, hm₁, hm₂]
  cases h : Nat.beq a₁.bits a₂.bits with
  | false => simp only [Bool.false_and, evalScalarBinOp, hszA1, hszA2, h]
  | true => simp only [Bool.true_and, evalScalarBinOp, hszM1, hszM2]

/-- **Universal full wide slice-pointer `==` distinguishes length metadata** (`evalRvalue`
→ `evalWidePtrAggregateRelBinOp` → `evalWidePtrRelBinOp`, matching MiniRust
`evalWideEqM_slice` and Case `24`): compares BOTH `ptrToAddrScalar p 8` AND wrapped
`len.bits`. -/
theorem evalRvalue_wideSlice_eq (locals : List LocalSlot) (mem : Memory) (decls : List LocalDecl)
    (layouts : LayoutTable) (lhsOp rhsOp : Operand) (p₁ p₂ : ProvenancePtr)
    (len₁ len₂ : ScalarInt) (l₁ l₂ : List LocalSlot)
    (hPB : layoutPointerBytes layouts = 8)
    (h1 : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.aggregate 0 [.ptr p₁ 8, .scalar len₁]) l₁)
    (h2 : evalOperand l₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.aggregate 0 [.ptr p₂ 8, .scalar len₂]) l₂)
    (hPtrTy : isPtrOrUntypedOperand decls layouts lhsOp = true)
    (hL1 : len₁.sizeBytes = 8) (hL2 : len₂.sizeBytes = 8)
    (hB1 : lookupBorrow mem.borrows p₁.tag = none) (hB2 : lookupBorrow mem.borrows p₂.tag = none) :
    evalRvalue locals (.binaryOp .eq lhsOp rhsOp) mem decls layouts =
      .ok (.scalar (boolToScalar
        (Nat.beq (ptrToAddrScalar p₁ 8).bits (ptrToAddrScalar p₂ 8).bits &&
          Nat.beq (wrapScalarBits len₁.bits (scalarModulus 8))
            (wrapScalarBits len₂.bits (scalarModulus 8))))) l₂ mem := by
  have hStep : evalRvalue locals (.binaryOp .eq lhsOp rhsOp) mem decls layouts =
      evalWidePtrRelBinOp .eq (.ptr p₁ 8) (.scalar len₁) (.ptr p₂ 8) (.scalar len₂)
        l₂ mem decls layouts 8 := by
    simp only [evalRvalue, h1, h2, evalWidePtrAggregateRelBinOp, hPtrTy, hPB]
    cases isExplicitWidePtrTy (operandTy decls layouts lhsOp) <;> rfl
  rw [hStep]
  exact evalWidePtrRelBinOp_eq_of_resolved _ _ _ _ l₂ mem decls layouts
    (ptrToAddrScalar p₁ 8) (ptrToAddrScalar p₂ 8)
    ⟨wrapScalarBits len₁.bits (scalarModulus 8), 8⟩ ⟨wrapScalarBits len₂.bits (scalarModulus 8), 8⟩
    (resolveWideWordScalar?_ptr_unborrowed _ _ _ _ _ _ _ hB1)
    (resolveWideWordScalar?_ptr_unborrowed _ _ _ _ _ _ _ hB2)
    (resolveWideWordScalar?_scalar8 _ _ _ _ _ _ _ hL1)
    (resolveWideWordScalar?_scalar8 _ _ _ _ _ _ _ hL2) rfl rfl rfl rfl

/-- **Universal full wide trait-object `==` distinguishes vtable pointers** (`evalRvalue`
→ `evalWidePtrAggregateRelBinOp` → `evalWidePtrRelBinOp`, matching MiniRust
`evalWideEqM_vtable` and Case `26`): compares BOTH `ptrToAddrScalar p 8` AND
`ptrToAddrScalar vt 8`. -/
theorem evalRvalue_wideDyn_eq (locals : List LocalSlot) (mem : Memory) (decls : List LocalDecl)
    (layouts : LayoutTable) (lhsOp rhsOp : Operand) (p₁ p₂ vt₁ vt₂ : ProvenancePtr)
    (l₁ l₂ : List LocalSlot)
    (hPB : layoutPointerBytes layouts = 8)
    (h1 : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.aggregate 0 [.ptr p₁ 8, .ptr vt₁ 8]) l₁)
    (h2 : evalOperand l₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.aggregate 0 [.ptr p₂ 8, .ptr vt₂ 8]) l₂)
    (hPtrTy : isPtrOrUntypedOperand decls layouts lhsOp = true)
    (hB1 : lookupBorrow mem.borrows p₁.tag = none) (hB2 : lookupBorrow mem.borrows p₂.tag = none)
    (hV1 : lookupBorrow mem.borrows vt₁.tag = none) (hV2 : lookupBorrow mem.borrows vt₂.tag = none) :
    evalRvalue locals (.binaryOp .eq lhsOp rhsOp) mem decls layouts =
      .ok (.scalar (boolToScalar
        (Nat.beq (ptrToAddrScalar p₁ 8).bits (ptrToAddrScalar p₂ 8).bits &&
          Nat.beq (ptrToAddrScalar vt₁ 8).bits (ptrToAddrScalar vt₂ 8).bits))) l₂ mem := by
  have hStep : evalRvalue locals (.binaryOp .eq lhsOp rhsOp) mem decls layouts =
      evalWidePtrRelBinOp .eq (.ptr p₁ 8) (.ptr vt₁ 8) (.ptr p₂ 8) (.ptr vt₂ 8)
        l₂ mem decls layouts 8 := by
    simp only [evalRvalue, h1, h2, evalWidePtrAggregateRelBinOp, hPtrTy, hPB]
    cases isExplicitWidePtrTy (operandTy decls layouts lhsOp) <;> rfl
  rw [hStep]
  exact evalWidePtrRelBinOp_eq_of_resolved _ _ _ _ l₂ mem decls layouts
    (ptrToAddrScalar p₁ 8) (ptrToAddrScalar p₂ 8)
    (ptrToAddrScalar vt₁ 8) (ptrToAddrScalar vt₂ 8)
    (resolveWideWordScalar?_ptr_unborrowed _ _ _ _ _ _ _ hB1)
    (resolveWideWordScalar?_ptr_unborrowed _ _ _ _ _ _ _ hB2)
    (resolveWideWordScalar?_ptr_unborrowed _ _ _ _ _ _ _ hV1)
    (resolveWideWordScalar?_ptr_unborrowed _ _ _ _ _ _ _ hV2) rfl rfl rfl rfl

/-- **Universal 2-step `ptr::addr_eq` composition** (`evalCastPtrToPtr` + `evalRvalue`
`.binaryOp .eq`, polymorphic across EVERY MiniRust memory `M` — `BasicMemory` and
`TreeBorrowsMemory` alike — matching `evalAddrEqM_ptr` across heterogeneous metadata and
distinct provenance tags): casting a slice wide pointer `(p₁, metaSc)` and a trait-object
wide pointer `(p₂, vt)` to thin raw pointers discards both metadata words and compares
strictly `ptrToAddrScalar p₁ 8` vs `ptrToAddrScalar p₂ 8`. -/
theorem evalCast_then_thinEq_erases_meta_and_prov
    (locals locals₁ locals₂ locals₃ : List LocalSlot)
    (wOp₁ wOp₂ tOp₁ tOp₂ : Operand) (targetTy : Ty)
    (mem : Memory) (decls : List LocalDecl) (layouts : LayoutTable)
    (p₁ p₂ vt : ProvenancePtr) (metaSc : ScalarInt)
    (hPB : layoutPointerBytes layouts = 8) (hThin : isThinRawPtrTy targetTy = true)
    (hMeta : metaSc.sizeBytes = 8)
    (hB1 : lookupBorrow mem.borrows p₁.tag = none) (hB2 : lookupBorrow mem.borrows p₂.tag = none)
    (hW1 : evalOperand locals wOp₁ mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.aggregate 0 [.ptr p₁ 8, .scalar metaSc]) locals₁)
    (hW2 : evalOperand locals₁ wOp₂ mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.aggregate 0 [.ptr p₂ 8, .ptr vt 8]) locals₂)
    (hT1 : evalOperand locals₂ tOp₁ mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.ptr p₁ 8) locals₂)
    (hT2 : evalOperand locals₂ tOp₂ mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.ptr p₂ 8) locals₃)
    (hRel : isPtrRelationalBinOp .eq decls layouts tOp₁ tOp₂ = true) :
    evalCastPtrToPtr locals wOp₁ targetTy mem decls layouts = .ok (.ptr p₁ 8) locals₁ mem ∧
    evalCastPtrToPtr locals₁ wOp₂ targetTy mem decls layouts = .ok (.ptr p₂ 8) locals₂ mem ∧
    evalRvalue locals₂ (.binaryOp .eq tOp₁ tOp₂) mem decls layouts =
      .ok (.scalar (boolToScalar
        (Nat.beq (ptrToAddrScalar p₁ 8).bits (ptrToAddrScalar p₂ 8).bits))) locals₃ mem ∧
    (∀ (M : Type) [MiniRustSpec.Gen.Memory M] [MiniRustSpec.Interp.MemoryOps M]
       (prov₁ prov₂ : Option (MiniRustSpec.Gen.Memory.Provenance M))
       (m₁ m₂ : Option (MiniRustSpec.Gen.PointerMeta (MiniRustSpec.Gen.Memory.Provenance M)))
       (ty₁ ty₂ : MiniRustSpec.Gen.«Type»),
      MiniRustSpec.HeapAllocAndWidePtrMR.evalAddrEqM (M := M)
          (.Ptr ⟨⟨Int.ofNat (ptrToAddrScalar p₁ 8).bits, prov₁⟩, m₁⟩, ty₁)
          (.Ptr ⟨⟨Int.ofNat (ptrToAddrScalar p₂ 8).bits, prov₂⟩, m₂⟩, ty₂) =
        Except.ok (.Bool (Nat.beq (ptrToAddrScalar p₁ 8).bits (ptrToAddrScalar p₂ 8).bits), .Bool)) := by
  refine ⟨evalCastPtrToPtr_slice_to_thin _ _ _ _ _ _ _ _ _ hPB hW1 hMeta hThin hB1,
    evalCastPtrToPtr_dyn_to_thin _ _ _ _ _ _ _ _ _ hPB hW2 hThin,
    evalRvalue_thinPtr_eq _ _ _ _ _ _ _ _ _ _ hT1 hT2 hRel hB1 hB2, ?_⟩
  intro M _ _ prov₁ prov₂ m₁ m₂ ty₁ ty₂
  rw [MiniRustSpec.HeapAllocAndWidePtrMR.evalAddrEqM_ptr]
  have hDec : decide (Int.ofNat (ptrToAddrScalar p₁ 8).bits = Int.ofNat (ptrToAddrScalar p₂ 8).bits) =
      Nat.beq (ptrToAddrScalar p₁ 8).bits (ptrToAddrScalar p₂ 8).bits := by
    cases h : Nat.beq (ptrToAddrScalar p₁ 8).bits (ptrToAddrScalar p₂ 8).bits with
    | true =>
      have heq := Nat.eq_of_beq_eq_true h
      rw [heq]; exact decide_eq_true rfl
    | false =>
      have hne := Nat.ne_of_beq_eq_false h
      exact decide_eq_false (fun hi => hne (Int.ofNat.inj hi))
  rw [hDec]

private theorem decide_ofNat_and_eq_beq_and (a b c d : Nat) :
    decide (Int.ofNat a = Int.ofNat b ∧ Int.ofNat c = Int.ofNat d) =
      (Nat.beq a b && Nat.beq c d) := by
  cases hab : Nat.beq a b with
  | false =>
    have hne := Nat.ne_of_beq_eq_false hab
    exact decide_eq_false (fun h => hne (Int.ofNat.inj h.1))
  | true =>
    have heq := Nat.eq_of_beq_eq_true hab
    cases hcd : Nat.beq c d with
    | false =>
      have hne := Nat.ne_of_beq_eq_false hcd
      exact decide_eq_false (fun h => hne (Int.ofNat.inj h.2))
    | true =>
      have heq2 := Nat.eq_of_beq_eq_true hcd
      rw [heq, heq2]; exact decide_eq_true ⟨rfl, rfl⟩

/-- **Universal Trusted ↔ MiniRust full wide slice-pointer `==` correspondence**: across
every MiniRust memory `M`, `evalRvalue (.binaryOp .eq ...)` on two unborrowed wide slice
pointers agrees bit-for-bit with `MiniRustSpec.HeapAllocAndWidePtrMR.evalWideEqM`
(comparing both thin address and slice length, matching Case `24`). -/
theorem evalRvalue_wideSlice_eq_matches_mr (locals : List LocalSlot) (mem : Memory)
    (decls : List LocalDecl) (layouts : LayoutTable) (lhsOp rhsOp : Operand)
    (p₁ p₂ : ProvenancePtr) (len₁ len₂ : ScalarInt) (l₁ l₂ : List LocalSlot)
    (hPB : layoutPointerBytes layouts = 8)
    (h1 : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.aggregate 0 [.ptr p₁ 8, .scalar len₁]) l₁)
    (h2 : evalOperand l₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.aggregate 0 [.ptr p₂ 8, .scalar len₂]) l₂)
    (hPtrTy : isPtrOrUntypedOperand decls layouts lhsOp = true)
    (hL1 : len₁.sizeBytes = 8) (hL2 : len₂.sizeBytes = 8)
    (hB1 : lookupBorrow mem.borrows p₁.tag = none) (hB2 : lookupBorrow mem.borrows p₂.tag = none) :
    let resBool :=
      Nat.beq (ptrToAddrScalar p₁ 8).bits (ptrToAddrScalar p₂ 8).bits &&
        Nat.beq (wrapScalarBits len₁.bits (scalarModulus 8))
          (wrapScalarBits len₂.bits (scalarModulus 8))
    evalRvalue locals (.binaryOp .eq lhsOp rhsOp) mem decls layouts =
      .ok (.scalar (boolToScalar resBool)) l₂ mem ∧
    (∀ (M : Type) [MiniRustSpec.Gen.Memory M] [MiniRustSpec.Interp.MemoryOps M]
       (prov₁ prov₂ : Option (MiniRustSpec.Gen.Memory.Provenance M))
       (pty : MiniRustSpec.Gen.PtrType) (tyr : MiniRustSpec.Gen.«Type»),
      MiniRustSpec.HeapAllocAndWidePtrMR.evalWideEqM (M := M)
          (.Ptr ⟨⟨Int.ofNat (ptrToAddrScalar p₁ 8).bits, prov₁⟩,
            some (.ElementCount (Int.ofNat (wrapScalarBits len₁.bits (scalarModulus 8))))⟩, .Ptr pty)
          (.Ptr ⟨⟨Int.ofNat (ptrToAddrScalar p₂ 8).bits, prov₂⟩,
            some (.ElementCount (Int.ofNat (wrapScalarBits len₂.bits (scalarModulus 8))))⟩, tyr) =
        Except.ok (.Bool resBool, .Bool)) := by
  refine ⟨evalRvalue_wideSlice_eq locals mem decls layouts lhsOp rhsOp p₁ p₂ len₁ len₂ l₁ l₂
    hPB h1 h2 hPtrTy hL1 hL2 hB1 hB2, ?_⟩
  intro M _ _ prov₁ prov₂ pty tyr
  rw [MiniRustSpec.HeapAllocAndWidePtrMR.evalWideEqM_slice, decide_ofNat_and_eq_beq_and]

/-- **Universal Trusted ↔ MiniRust full wide trait-object `==` correspondence**: across
every MiniRust memory `M`, `evalRvalue (.binaryOp .eq ...)` on two unborrowed `dyn Trait`
pointers agrees bit-for-bit with `MiniRustSpec.HeapAllocAndWidePtrMR.evalWideEqM`
(comparing both thin address and vtable address, matching Case `26`). -/
theorem evalRvalue_wideDyn_eq_matches_mr (locals : List LocalSlot) (mem : Memory)
    (decls : List LocalDecl) (layouts : LayoutTable) (lhsOp rhsOp : Operand)
    (p₁ p₂ vt₁ vt₂ : ProvenancePtr) (l₁ l₂ : List LocalSlot)
    (hPB : layoutPointerBytes layouts = 8)
    (h1 : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.aggregate 0 [.ptr p₁ 8, .ptr vt₁ 8]) l₁)
    (h2 : evalOperand l₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.aggregate 0 [.ptr p₂ 8, .ptr vt₂ 8]) l₂)
    (hPtrTy : isPtrOrUntypedOperand decls layouts lhsOp = true)
    (hB1 : lookupBorrow mem.borrows p₁.tag = none) (hB2 : lookupBorrow mem.borrows p₂.tag = none)
    (hV1 : lookupBorrow mem.borrows vt₁.tag = none) (hV2 : lookupBorrow mem.borrows vt₂.tag = none) :
    let resBool :=
      Nat.beq (ptrToAddrScalar p₁ 8).bits (ptrToAddrScalar p₂ 8).bits &&
        Nat.beq (ptrToAddrScalar vt₁ 8).bits (ptrToAddrScalar vt₂ 8).bits
    evalRvalue locals (.binaryOp .eq lhsOp rhsOp) mem decls layouts =
      .ok (.scalar (boolToScalar resBool)) l₂ mem ∧
    (∀ (M : Type) [MiniRustSpec.Gen.Memory M] [MiniRustSpec.Interp.MemoryOps M]
       (prov₁ prov₂ vprov₁ vprov₂ : Option (MiniRustSpec.Gen.Memory.Provenance M))
       (pty : MiniRustSpec.Gen.PtrType) (tyr : MiniRustSpec.Gen.«Type»),
      MiniRustSpec.HeapAllocAndWidePtrMR.evalWideEqM (M := M)
          (.Ptr ⟨⟨Int.ofNat (ptrToAddrScalar p₁ 8).bits, prov₁⟩,
            some (.VTablePointer ⟨Int.ofNat (ptrToAddrScalar vt₁ 8).bits, vprov₁⟩)⟩, .Ptr pty)
          (.Ptr ⟨⟨Int.ofNat (ptrToAddrScalar p₂ 8).bits, prov₂⟩,
            some (.VTablePointer ⟨Int.ofNat (ptrToAddrScalar vt₂ 8).bits, vprov₂⟩)⟩, tyr) =
        Except.ok (.Bool resBool, .Bool)) := by
  refine ⟨evalRvalue_wideDyn_eq locals mem decls layouts lhsOp rhsOp p₁ p₂ vt₁ vt₂ l₁ l₂
    hPB h1 h2 hPtrTy hB1 hB2 hV1 hV2, ?_⟩
  intro M _ _ prov₁ prov₂ vprov₁ vprov₂ pty tyr
  rw [MiniRustSpec.HeapAllocAndWidePtrMR.evalWideEqM_vtable, decide_ofNat_and_eq_beq_and]

/-! #### Concrete `evalRvalue` / `stepMirFn` executions (cases `23..27` + non-vacuity twins) -/

@[reducible] def hwSliceTy : RigidTy := .rawPtr .not (.slice (.uint .u8))
@[reducible] def hwDynTy : RigidTy := .rawPtr .not (.dynamic "hw::Trait")
@[reducible] def hwThinTy : Ty := { kind := .rawPtr .not (.tuple []), layoutIdx := 0 }

/-- Heap pointer at page address `73728` with provenance tag `1`. -/
def hwPtrA : ProvenancePtr := { allocId := 1, offsetBytes := 8192 }
/-- A *different* provenance tag (`0`) at the same page address `73728`. -/
def hwPtrB : ProvenancePtr := { allocId := 0, offsetBytes := 73728 }
/-- A pointer at a *different* page address (`139264 ≠ 73728`) for `addr_eq = false` twins. -/
def hwPtrC : ProvenancePtr := { allocId := 2, offsetBytes := 8192 }
/-- Two vtable pointers (`0x9000`, `0xA000`). -/
def hwVt9 : ProvenancePtr := { allocId := 0, offsetBytes := 36864 }
def hwVtA : ProvenancePtr := { allocId := 0, offsetBytes := 40960 }

/-- Wide operands of the `rust#166144` comparisons (provenance-backed and scalar-address). -/
def hwSlice (p : ProvenancePtr) (len : Nat) : Value := .aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]
def hwDyn (p vt : ProvenancePtr) : Value := .aggregate 0 [.ptr p 8, .ptr vt 8]
def hwScalarSlice (addr len : Nat) : Value := .aggregate 0 [.scalar ⟨addr, 8⟩, .scalar ⟨len, 8⟩]
def hwScalarDyn (addr : Nat) (vt : ProvenancePtr) : Value := .aggregate 0 [.scalar ⟨addr, 8⟩, .ptr vt 8]

/-- `fn(_1: L, _2: R) -> bool { _3 = _1 as *const (); _4 = _2 as *const (); _0 = _3 == _4 }`
(`ptr::addr_eq`) when `addrEq`, otherwise `fn(_1: L, _2: R) -> bool { _0 = _1 == _2 }`. -/
def hwCmpBody (lTy rTy : RigidTy) (addrEq : Bool) : CapturedMir :=
  let st (k : StatementKind) : Statement := { kind := k, span := "hw.rs:2:1" }
  let place (i : Nat) : Place := { local_ := i, projection := [] }
  hwMirBody "hw::cmp" [hwDecl .bool, hwDecl lTy, hwDecl rTy, hwDecl hwThinTy.kind, hwDecl hwThinTy.kind] 2
    [{ statements :=
         if addrEq then
           [st (.assign (place 3) (.cast .ptrToPtr (.copy (place 1)) hwThinTy)),
            st (.assign (place 4) (.cast .ptrToPtr (.copy (place 2)) hwThinTy)),
            st (.assign (place 0) (.binaryOp .eq (.copy (place 3)) (.copy (place 4))))]
         else
           [st (.assign (place 0) (.binaryOp .eq (.copy (place 1)) (.copy (place 2))))],
       terminator := { kind := .return_, span := "hw.rs:3:1" }, isCleanup := false }]

/-- Initial state: arguments `_1 = l`, `_2 = r`, empty borrow table (heap pointers). -/
def hwCmpState (l r : Value) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0,
               locals := [.uninit, .init l, .init r, .uninit, .uninit] },
    memory := {} }

/-- Observe a Trusted return value in the shared domain. -/
def trustedValueObs : Value → HeapWideObs
  | .scalar ⟨1, 1⟩ => .okBool true
  | .scalar ⟨0, 1⟩ => .okBool false
  | _ => .invalidOrUnsupported

/-- Bounded `stepMirFn` runner (fuel-indexed, structurally recursive). -/
def trustedRun (body : CapturedMir) : Nat → MachineState → HeapWideObs
  | 0, _ => .invalidOrUnsupported
  | fuel + 1, s =>
    match stepMirFn body s with
    | .tau (.running s') => trustedRun body fuel s'
    | .ret (.normal r) => trustedValueObs r.1
    | .vis (.inl (.fail .ub)) _ => .ub
    | _ => .invalidOrUnsupported

/-- Run the comparison fixture through `stepMirFn`. -/
def trustedCmpObs (lTy rTy : RigidTy) (addrEq : Bool) (l r : Value) : HeapWideObs :=
  trustedRun (hwCmpBody lTy rTy addrEq) 8 (hwCmpState l r)

/-- **Concrete Trusted `rust#166144` table** executed by the real `stepMirFn` (through
`evalStmt` → `evalRvalue` → `evalCastPtrToPtr` / `.binaryOp .eq`): `addr_eq` erases slice
lengths (`23`), vtables (`25`), and heterogeneous metadata **and provenance tags** (`27`),
while full wide `==` distinguishes lengths (`24`) and vtables (`26`). -/
theorem trustedCmp_table :
    trustedCmpObs hwSliceTy hwSliceTy true (hwSlice hwPtrA 3) (hwSlice hwPtrA 7) = .okBool true ∧
    trustedCmpObs hwSliceTy hwSliceTy false (hwSlice hwPtrA 3) (hwSlice hwPtrA 7) = .okBool false ∧
    trustedCmpObs hwDynTy hwDynTy true (hwDyn hwPtrA hwVt9) (hwDyn hwPtrA hwVtA) = .okBool true ∧
    trustedCmpObs hwDynTy hwDynTy false (hwDyn hwPtrA hwVt9) (hwDyn hwPtrA hwVtA) = .okBool false ∧
    trustedCmpObs hwSliceTy hwDynTy true (hwSlice hwPtrA 5) (hwDyn hwPtrB hwVt9) = .okBool true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Single-step `evalRvalue` witnesses on the cast results: the slice cast is the thin
pointer itself, and thin `==` across distinct tags at one address is `true`. -/
theorem trustedRvalue_witnesses :
    evalCastPtrToPtr [.uninit, .init (hwSlice hwPtrA 3)] (.copy { local_ := 1, projection := [] })
        hwThinTy {} [hwDecl .bool, hwDecl hwSliceTy] emptyLayoutTable =
      .ok (.ptr hwPtrA 8) [.uninit, .init (hwSlice hwPtrA 3)] {} ∧
    evalRvalue [.uninit, .init (.ptr hwPtrA 8), .init (.ptr hwPtrB 8)]
        (.binaryOp .eq (.copy { local_ := 1, projection := [] }) (.copy { local_ := 2, projection := [] }))
        {} [hwDecl .bool, hwDecl hwThinTy.kind, hwDecl hwThinTy.kind] emptyLayoutTable =
      .ok (.scalar ⟨1, 1⟩) [.uninit, .init (.ptr hwPtrA 8), .init (.ptr hwPtrB 8)] {} ∧
    hwPtrA.tag ≠ hwPtrB.tag ∧ ptrToAddrScalar hwPtrA 8 = ptrToAddrScalar hwPtrB 8 := by
  refine ⟨?_, ?_, by decide, rfl⟩
  · exact evalCastPtrToPtr_slice_to_thin _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl
  · have hA : ptrToAddrScalar hwPtrA 8 = ptrToAddrScalar hwPtrB 8 := rfl
    rw [evalRvalue_thinPtr_eq _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl, hA, Nat.beq_refl]
    rfl

/-- **Trusted ↔ MiniRust wide-pointer correspondence on cases `23..27`** (both modes). -/
theorem trusted_wide_cases_match_mr (m : HeapWideMemoryMode) :
    trustedCmpObs hwSliceTy hwSliceTy true (hwSlice hwPtrA 3) (hwSlice hwPtrA 7) = mrObserve m 23 ∧
    trustedCmpObs hwSliceTy hwSliceTy false (hwSlice hwPtrA 3) (hwSlice hwPtrA 7) = mrObserve m 24 ∧
    trustedCmpObs hwDynTy hwDynTy true (hwDyn hwPtrA hwVt9) (hwDyn hwPtrA hwVtA) = mrObserve m 25 ∧
    trustedCmpObs hwDynTy hwDynTy false (hwDyn hwPtrA hwVt9) (hwDyn hwPtrA hwVtA) = mrObserve m 26 ∧
    trustedCmpObs hwSliceTy hwDynTy true (hwSlice hwPtrA 5) (hwDyn hwPtrB hwVt9) = mrObserve m 27 := by
  obtain ⟨h23, h24, h25, h26, h27⟩ := trustedCmp_table
  rw [mrObserve_table m 23 (by decide), mrObserve_table m 24 (by decide),
    mrObserve_table m 25 (by decide), mrObserve_table m 26 (by decide),
    mrObserve_table m 27 (by decide)]
  cases m <;> exact ⟨h23, h24, h25, h26, h27⟩

/-- **Opposite-polarity & scalar-address non-vacuity twins for `trustedCmpObs`**:
(1) `addr_eq` returns `.okBool false` at distinct addresses (`hwPtrA` vs `hwPtrC`) across
slice, dyn, and heterogeneous operands (proving `addr_eq` does not trivially return `true`);
(2) full wide `==` returns `.okBool true` when both address and metadata match (proving
full wide `==` does not trivially return `false`);
(3) concrete `stepMirFn` execution of `evalCastPtrToPtr` on scalar-address wide pointers
(`hwScalarSlice`, `hwScalarDyn`) erases metadata and distinguishes addresses. -/
theorem trustedCmp_nonvacuity_twins_table :
    trustedCmpObs hwSliceTy hwSliceTy true (hwSlice hwPtrA 3) (hwSlice hwPtrC 3) = .okBool false ∧
    trustedCmpObs hwDynTy hwDynTy true (hwDyn hwPtrA hwVt9) (hwDyn hwPtrC hwVt9) = .okBool false ∧
    trustedCmpObs hwSliceTy hwDynTy true (hwSlice hwPtrA 5) (hwDyn hwPtrC hwVt9) = .okBool false ∧
    trustedCmpObs hwSliceTy hwSliceTy false (hwSlice hwPtrA 3) (hwSlice hwPtrA 3) = .okBool true ∧
    trustedCmpObs hwDynTy hwDynTy false (hwDyn hwPtrA hwVt9) (hwDyn hwPtrA hwVt9) = .okBool true ∧
    trustedCmpObs hwSliceTy hwSliceTy true (hwScalarSlice 8192 3) (hwScalarSlice 8192 7) = .okBool true ∧
    trustedCmpObs hwSliceTy hwDynTy true (hwScalarSlice 8192 3) (hwScalarDyn 8192 hwVt9) = .okBool true ∧
    trustedCmpObs hwSliceTy hwSliceTy true (hwScalarSlice 8192 3) (hwScalarSlice 12288 3) = .okBool false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end TrustedBridge

/-! ## §7. Episode 2 Capstone -/

open Trusted.Rustc.V2026_06_01.MirSemantics (preventsDeallocation hasFrameDeallocProtectorConflict
  hasProtectedLocalBorrow evalTerminator evalTailCallTerminator evalStmt restoreCallerProtectors
  evalCastPtrToPtr evalRvalue ptrToAddrScalar ptrAddressScalar? stepMirFn) in
/-- **Episode 2 Dual-Authority Heap Allocation & Wide-Pointer Capstone.** For every
contract `c` (closed across roots over `LeanMiriSpec.HeapAllocAndWidePtrLM` in
`tests/mir/HeapAllocAndWidePtrDualSpecTests.lean`):
1. choice-free codec laws (incl. malformed-tuple rejection and `ofMrObs`/`toMrObs`
   bijection) and the wire-level exact divergence set;
2. Episode 1's universal MiniRust laws (`ep1_minirust_heap_wide_capstone`);
3. the 60-cell MiniRust table, out-of-range guard, exact agreement on `0..27`, the exact
   `↔` divergence set `{28, 29}` with explicit witnesses, joint Tree Borrows mode
   sensitivity on `19`, `21`, full MR mode-sensitivity `↔`, and `StaticAllocator` / leak /
   `addr_eq` agreement (`13..17, 23..27`);
4. both threaded traces (lifecycle and mode-sensitive protector);
5. the direct bridge to unmodified `Trusted.Rustc.V2026_06_01.MirSemantics`:
   `preventsDeallocation` ↔ MiniRust `prevents_deallocation`, universal
   `hasFrameDeallocProtectorConflict` & `hasProtectedLocalBorrow` ↔ MiniRust
   `Node::contains_strong_protector_preventing_deallocation`, `evalTerminator` `.return_`
   (including callee-return `restoreCallerProtectors` release), `evalTailCallTerminator`,
   and `evalStmt` `.storageDead`/`.storageLive` protector laws + concrete `stepMirFn`
   verdicts equal to MiniRust's on `19`, `20`, `22`, universal `evalCastPtrToPtr` metadata
   erasure (all 4 wide shapes), universal `evalRvalue` thin `==` and full wide slice /
   `dyn Trait` `==` (`evalWidePtrAggregateRelBinOp` / `evalWidePtrRelBinOp`), composed
   cast-then-`==` equivalence with MiniRust `evalAddrEqM_ptr`, and concrete `stepMirFn`
   `addr_eq` / `==` verdicts equal to MiniRust's on `23..27`. -/
theorem ep2_heap_alloc_and_wide_ptr_dual_authority_capstone (c : HeapWideDualContract) :
    (heapWideOutcomeCodec.TightValidRep ∧
      (∀ a₁ a₂ : HeapWideObs, heapWideOutcomeCodec.encode a₁ = heapWideOutcomeCodec.encode a₂ →
        a₁ = a₂) ∧
      (∀ (b₁ b₂ : HeapWideOutcomeRep) (a : HeapWideObs), heapWideOutcomeCodec.ValidRep b₁ →
        heapWideOutcomeCodec.ValidRep b₂ → heapWideOutcomeCodec.decode b₁ = some a →
        heapWideOutcomeCodec.decode b₂ = some a → b₁ = b₂) ∧
      (type_of% @heapWideOutcomeCodec_rejects_malformed) ∧
      (type_of% @ofMrObs_toMrObs) ∧ (type_of% @toMrObs_ofMrObs) ∧
      (∀ (m : HeapWideMemoryMode) (idx : Nat), idx < canonicalCaseCount →
        (heapWideOutcomeCodec.encode (mrObserve m idx) =
          heapWideOutcomeCodec.encode (c.lm.observe m.toLmTreeBorrows idx) ↔
            divergesAt m idx = false))) ∧
    ((type_of% @ep1_minirust_heap_wide_capstone) ∧ (type_of% @mr_addrEq_wideEq_bm_bridge)) ∧
    ((∀ (m : HeapWideMemoryMode) (idx : Nat), idx < canonicalCaseCount →
        mrObserve m idx = mrExpected m idx) ∧
      (type_of% @mrObserve_out_of_range) ∧
      (type_of% @mr_mode_sensitivity) ∧
      (∀ (m : HeapWideMemoryMode) (idx : Nat), idx < canonicalCaseCount →
        caseClass idx = .exactAgreement → mrObserve m idx = c.lm.observe m.toLmTreeBorrows idx) ∧
      (∀ (m : HeapWideMemoryMode) (idx : Nat), idx < canonicalCaseCount →
        (mrObserve m idx ≠ c.lm.observe m.toLmTreeBorrows idx ↔ divergesAt m idx = true)) ∧
      (∀ (m : HeapWideMemoryMode),
        mrObserve m 28 = .specPanic ∧ c.lm.observe m.toLmTreeBorrows 28 = .invalidOrUnsupported ∧
        mrObserve m 29 = .okAlloc 0 1073741824 ∧ c.lm.observe m.toLmTreeBorrows 29 = .ub) ∧
      ((mrObserve .basic 19 = c.lm.observe false 19 ∧ mrObserve .basic 19 = .okDealloc ∧
          mrObserve .treeBorrows 19 = c.lm.observe true 19 ∧ c.lm.observe true 19 = .ub) ∧
        (mrObserve .basic 21 = c.lm.observe false 21 ∧ mrObserve .basic 21 = .okDealloc ∧
          mrObserve .treeBorrows 21 = c.lm.observe true 21 ∧ c.lm.observe true 21 = .ub)) ∧
      (∀ m, type_of% (contract_static_leak_wide_agreement c m)) ∧
      (∀ (m : HeapWideMemoryMode) (idx : Nat),
        (mrObserve m idx ≠ c.lm.observe m.toLmTreeBorrows idx ↔ divergesAt m idx = true)) ∧
      (∀ (m : HeapWideMemoryMode) (idx : Nat),
        (heapWideOutcomeCodec.encode (mrObserve m idx) =
            heapWideOutcomeCodec.encode (c.lm.observe m.toLmTreeBorrows idx) ↔
          divergesAt m idx = false)) ∧
      (∀ (m : HeapWideMemoryMode) (idx : Nat), canonicalCaseCount ≤ idx →
        mrObserve m idx = .invalidOrUnsupported ∧
          c.lm.observe m.toLmTreeBorrows idx = .invalidOrUnsupported)) ∧
    ((∀ m, c.lmLifecycle m.toLmTreeBorrows = mrLifecycleTrace m) ∧
      (∀ m, c.lmProtector m.toLmTreeBorrows = mrProtectorTrace m) ∧
      c.lmProtector false ≠ c.lmProtector true ∧
      c.lmLifecycle false = lifecycleExpected ∧ c.lmLifecycle true = lifecycleExpected ∧
      c.lmProtector false = protectorExpected .basic ∧
      c.lmProtector true = protectorExpected .treeBorrows) ∧
    ((type_of% @preventsDeallocation_eq_mr) ∧
      (type_of% @mr_prevents_deallocation_iff_trusted) ∧
      (type_of% @hasFrameDeallocProtectorConflict_eq_mr_node) ∧
      (type_of% @hasProtectedLocalBorrow_eq_mr_node) ∧
      (type_of% @hasFrameDeallocProtectorConflict_iff) ∧
      (type_of% @hasFrameDeallocProtectorConflict_nil_protectors) ∧
      (type_of% @hasProtectedLocalBorrow_iff) ∧
      (type_of% @isBorrowProtected_released) ∧
      (type_of% @evalTerminator_return_protector_ub) ∧
      (type_of% @evalTerminator_return_no_conflict_root) ∧
      (type_of% @evalTerminator_callee_return_releases_protector) ∧
      (type_of% @evalTailCallTerminator_protector_ub) ∧
      (type_of% @evalTailCallTerminator_no_conflict_steps) ∧
      (type_of% @evalStmt_storageDead_protector_ub) ∧
      (type_of% @evalStmt_storageDead_no_conflict_steps) ∧
      (type_of% @evalStmt_storageLive_protector_ub) ∧
      (type_of% @trustedTeardown_table) ∧
      (type_of% @trusted_protector_cases_match_mr) ∧
      (type_of% @trustedStorageDead_and_release_table) ∧
      (type_of% @trusted_protector_twins_table) ∧
      (type_of% @trustedTailCallRun_table) ∧
      (type_of% @evalCastPtrToPtr_slice_to_thin) ∧
      (type_of% @evalCastPtrToPtr_dyn_to_thin) ∧
      (type_of% @evalCastPtrToPtr_scalarPair_to_thin) ∧
      (type_of% @evalCastPtrToPtr_scalarDyn_to_thin) ∧
      (type_of% @ptrAddressScalar?_unborrowed) ∧
      (type_of% @ptrToAddrScalar_addr_only) ∧
      (type_of% @evalRvalue_thinPtr_eq) ∧
      (type_of% @evalRvalue_thinScalar_eq) ∧
      (type_of% @evalRvalue_wideSlice_eq) ∧
      (type_of% @evalRvalue_wideDyn_eq) ∧
      (type_of% @evalRvalue_wideSlice_eq_matches_mr) ∧
      (type_of% @evalRvalue_wideDyn_eq_matches_mr) ∧
      (type_of% @evalCast_then_thinEq_erases_meta_and_prov) ∧
      (type_of% @trustedRvalue_witnesses) ∧
      (type_of% @trusted_wide_cases_match_mr) ∧
      (type_of% @trustedCmp_nonvacuity_twins_table)) :=
  ⟨⟨heapWideOutcomeCodec_tight, fun _ _ h => heapWideOutcomeCodec_encode_injective h,
      fun _ _ _ hv₁ hv₂ hd₁ hd₂ => heapWideOutcomeCodec_decode_injective_on_valid hv₁ hv₂ hd₁ hd₂,
      heapWideOutcomeCodec_rejects_malformed, ofMrObs_toMrObs, toMrObs_ofMrObs,
      contract_wire_divergence_exact c⟩,
    ⟨c.mr_ep1_capstone, mr_addrEq_wideEq_bm_bridge⟩,
    ⟨c.mr_matches, mrObserve_out_of_range, mr_mode_sensitivity, c.agreement_zone_exact,
      contract_divergence_set_exact c, c.divergence_explicit, c.mode_sensitivity_joint,
      contract_static_leak_wide_agreement c, contract_total_divergence_exact c,
      contract_total_wire_divergence_exact c, contract_out_of_range_agreement c⟩,
    contract_traces c,
    ⟨@preventsDeallocation_eq_mr, @mr_prevents_deallocation_iff_trusted,
      @hasFrameDeallocProtectorConflict_eq_mr_node, @hasProtectedLocalBorrow_eq_mr_node,
      @hasFrameDeallocProtectorConflict_iff, @hasFrameDeallocProtectorConflict_nil_protectors,
      @hasProtectedLocalBorrow_iff, @isBorrowProtected_released,
      @evalTerminator_return_protector_ub, @evalTerminator_return_no_conflict_root,
      @evalTerminator_callee_return_releases_protector, @evalTailCallTerminator_protector_ub,
      @evalTailCallTerminator_no_conflict_steps,
      @evalStmt_storageDead_protector_ub, @evalStmt_storageDead_no_conflict_steps,
      @evalStmt_storageLive_protector_ub, @trustedTeardown_table,
      @trusted_protector_cases_match_mr, @trustedStorageDead_and_release_table,
      @trusted_protector_twins_table, @trustedTailCallRun_table,
      @evalCastPtrToPtr_slice_to_thin, @evalCastPtrToPtr_dyn_to_thin,
      @evalCastPtrToPtr_scalarPair_to_thin, @evalCastPtrToPtr_scalarDyn_to_thin,
      @ptrAddressScalar?_unborrowed, @ptrToAddrScalar_addr_only,
      @evalRvalue_thinPtr_eq, @evalRvalue_thinScalar_eq,
      @evalRvalue_wideSlice_eq, @evalRvalue_wideDyn_eq,
      @evalRvalue_wideSlice_eq_matches_mr, @evalRvalue_wideDyn_eq_matches_mr,
      @evalCast_then_thinEq_erases_meta_and_prov, @trustedRvalue_witnesses,
      @trusted_wide_cases_match_mr, @trustedCmp_nonvacuity_twins_table⟩⟩

/-! ## §8. Import-Isolation, Constructive-Codec, Bridge-Reality & Axiom Audit -/

section AxiomAudit
open Lean Elab Command

run_cmd do
  let env ← getEnv
  -- 1. Direct imports are exactly `MiniRustSpec.HeapAllocAndWidePtrMR` and `Trusted`.
  for imp in env.header.imports do
    unless imp.module == `Init || imp.module == `MiniRustSpec.HeapAllocAndWidePtrMR ||
        imp.module == `Trusted do
      throwError "import-isolation violation: direct import of {imp.module}"
  -- 2. Zero `Miri.*` / `LeanMiriSpec.*` modules, even transitively.
  for modName in env.header.moduleNames do
    if (`Miri).isPrefixOf modName || (`LeanMiriSpec).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported"
  -- 3. Constructive codec & authority-check layer is choice-free.
  let ns := `Anneal.Mir.HeapAllocAndWidePtrDualSpec
  let constructiveDecls : List Lean.Name :=
    [ ns ++ `heapWideOutcomeCodec, ns ++ `heapWideOutcomeCodec_tight,
      ns ++ `heapWideOutcomeCodec_encode_injective,
      ns ++ `heapWideOutcomeCodec_decode_injective_on_valid, ns ++ `heapWideDecode_canonical,
      ns ++ `heapWideOutcomeCodec_rejects_malformed,
      ns ++ `ofMrObs_toMrObs, ns ++ `toMrObs_ofMrObs, ns ++ `ofMrObs_injective,
      ns ++ `HeapWideMemoryMode.of_toLmTreeBorrows, ns ++ `HeapWideMemoryMode.to_ofLmTreeBorrows,
      ns ++ `range_map_cell, ns ++ `expected_agreement_zone, ns ++ `caseClass_agreement_iff,
      ns ++ `divergesAt_iff_class, ns ++ `lmAuthorityCheck_sound, ns ++ `lmAuthorityOfCheck ]
  for c in constructiveDecls do
    unless env.contains c do throwError "constructive audit: {c} missing"
    for a in ← liftCoreM <| Lean.collectAxioms c do
      unless a == ``propext || a == ``Quot.sound do
        throwError "constructive codec {c} must not depend on {a}"
  -- 4. The bridge theorems are stated on the REAL Trusted & MiniRust definitions (zero shadow evaluators).
  let bridgeReq : List (Lean.Name × Lean.Name) :=
    [ (ns ++ `preventsDeallocation_eq_mr, `Trusted.Rustc.V2026_06_01.MirSemantics.preventsDeallocation),
      (ns ++ `hasFrameDeallocProtectorConflict_eq_mr_node,
        `Trusted.Rustc.V2026_06_01.MirSemantics.hasFrameDeallocProtectorConflict),
      (ns ++ `hasFrameDeallocProtectorConflict_eq_mr_node,
        `MiniRustSpec.Interp.Node.contains_strong_protector_preventing_deallocation),
      (ns ++ `hasProtectedLocalBorrow_eq_mr_node,
        `Trusted.Rustc.V2026_06_01.MirSemantics.hasProtectedLocalBorrow),
      (ns ++ `hasProtectedLocalBorrow_eq_mr_node,
        `MiniRustSpec.Interp.Node.contains_strong_protector_preventing_deallocation),
      (ns ++ `evalTerminator_return_protector_ub, `Trusted.Rustc.V2026_06_01.MirSemantics.evalTerminator),
      (ns ++ `evalTerminator_callee_return_releases_protector,
        `Trusted.Rustc.V2026_06_01.MirSemantics.restoreCallerProtectors),
      (ns ++ `evalTailCallTerminator_protector_ub,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalTailCallTerminator),
      (ns ++ `evalTailCallTerminator_no_conflict_steps,
        `Trusted.Rustc.V2026_06_01.MirSemantics.enterTailCalleeFrame),
      (ns ++ `evalStmt_storageDead_protector_ub, `Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt),
      (ns ++ `evalStmt_storageLive_protector_ub, `Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt),
      (ns ++ `evalCastPtrToPtr_slice_to_thin, `Trusted.Rustc.V2026_06_01.MirSemantics.evalCastPtrToPtr),
      (ns ++ `evalCastPtrToPtr_scalarDyn_to_thin, `Trusted.Rustc.V2026_06_01.MirSemantics.evalCastPtrToPtr),
      (ns ++ `evalRvalue_thinPtr_eq, `Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue),
      (ns ++ `evalRvalue_thinPtr_eq, `Trusted.Rustc.V2026_06_01.MirSemantics.ptrToAddrScalar),
      (ns ++ `evalRvalue_wideSlice_eq_matches_mr, `MiniRustSpec.HeapAllocAndWidePtrMR.evalWideEqM),
      (ns ++ `evalRvalue_wideDyn_eq_matches_mr, `MiniRustSpec.HeapAllocAndWidePtrMR.evalWideEqM),
      (ns ++ `trustedTeardown_table, `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn),
      (ns ++ `trustedStorageDead_and_release_table, `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn),
      (ns ++ `trustedTailCallRun_table, `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn),
      (ns ++ `trustedCmp_table, `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn),
      (ns ++ `trustedCmp_nonvacuity_twins_table, `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn) ]
  for (thm, req) in bridgeReq do
    let some ci := env.find? thm | throwError "bridge audit: {thm} missing"
    let mut seen : NameSet := {}
    let mut todo : Array Lean.Name := ci.type.getUsedConstants
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      if n == req then break
      if (ns).isPrefixOf n then
        if let some (.defnInfo v) := env.find? n then
          todo := todo ++ v.value.getUsedConstants
    unless seen.contains req do
      throwError "shadow-evaluator audit: {thm} does not reach the real {req}"
  -- 5. Standard-3-axiom purity of every declaration and honest authored theorem-count floor.
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    for a in ← liftCoreM <| Lean.collectAxioms c do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      if a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
        throwError "{c} depends on {a} (compiler-trusting evaluation)"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    checked := checked + 1
    -- Count only genuinely authored public theorems (exclude compiler-generated eq/match/proof/noConfusion/sizeOf).
    let last := c.componentsRev.head!.toString
    let noAuxComp := c.components.all fun comp =>
      let s := comp.toString
      !s.startsWith "eq_" && !s.startsWith "match_" && !s.startsWith "_proof_"
    if (ns).isPrefixOf c && !c.isInternal && noAuxComp &&
        last != "noConfusion" && last != "noConfusionType" && last != "sizeOf_spec" &&
        last != "injEq" && last != "inj" then
      if let .thmInfo _ := info then theorems := theorems + 1
  if theorems < 70 then
    throwError "axiom audit is vacuous: only {theorems} authored theorems seen"
  logInfo m!"Anneal.Mir.HeapAllocAndWidePtrDualSpec: verified {checked} declarations ({theorems} authored theorems), constructive codecs choice-free, bridge on real Trusted.Rustc.V2026_06_01.MirSemantics, import_isolated=true, sorry_free=true, ofReduceBool_free=true"

end AxiomAudit

end Anneal.Mir.HeapAllocAndWidePtrDualSpec
