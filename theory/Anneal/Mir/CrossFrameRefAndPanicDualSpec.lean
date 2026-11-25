/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.CrossFrameRefAndPanicMR
import Trusted
import Anneal.DualCorrespondenceBundle
import Anneal.ParametricCore.CallStackUnwind

/-!
# Episode 1 Unified Dual-Authority Spec: Cross-Frame References, Pointer Arithmetic, & 4-Way Panic Unwinding (`Anneal.Mir.CrossFrameRefAndPanicDualSpec`)

Cross-authority specification, canonical 28-scenario (`0..27`, `56` mode cells)
classification, constructive choice-free `CodecLaws`, parameterized `LeanMiri`
authority interface, direct bridge to unmodified `Trusted.Rustc.V2026_06_01.MirSemantics`
(`stepMirFn`) and `Anneal.ParametricCore.CallStackUnwind.UnwindAction4`, and a genuine
`Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle` instantiation covering:

1. **Cross-frame `&mut T` / `&T` argument reborrowing (`RetagKind.fnEntry` protectors)
   and callee raw-pointer arithmetic** (`.as_mut_ptr`, `.cast`, in-bounds `BinOp.offset`,
   wrapping `core::intrinsics::arith_offset` round-trips, OOB-without-deref wrapping vs.
   OOB in-bounds UB, post-return caller write after protector release, Tree Borrows
   foreign-write protector UB, `Frozen` `&T` write UB, and callee dead-local UAR UB).
2. **`TerminatorKind.assert`, `TerminatorKind.unreachable`, panic initiation, 4-way
   `UnwindAction.{cleanup, continue_, terminate, unreachable}`,
   `TerminatorKind.{unwindResume, unwindTerminate}`, multi-frame LIFO protector release
   with partial `&mut` writeback preservation, and the exact `Memory.rootUnwindCeiling`
   root-frame unwind boundary**.

Classification across all `28 × 2 = 56` cells (`0..27`) plus fail-closed `idx ≥ 28`:
- **MiniRust ↔ LeanMiri**: exact agreement on ALL 56 cells (and all `idx : Nat`),
  including joint Tree Borrows mode sensitivity on Cases `8` and `9`
  (`.basic` succeeds vs. `.treeBorrows` rejects with `.ub`).
- **3-way (`Trusted.MirSemantics` ↔ `MiniRust.MachTB` ↔ `LeanMiri(treeBorrows = true)`)**:
  exact agreement on Cases `0..26` and all `idx ≥ 28`, with a single exact `↔`
  divergence boundary at Case `27` (`Memory.rootUnwindCeiling = true`: Trusted halts
  with `.panic` → `.unwound 77`, while MiniRust `BottomOfStack` and LeanMiri
  `frames.size == 1` both fault with `.ub`; when `rootUnwindCeiling = false` in Case `26`,
  all three authorities agree on `.ub`).

Strict root isolation: direct imports are ONLY `MiniRustSpec.CrossFrameRefAndPanicMR`,
`Trusted`, `Anneal.DualCorrespondenceBundle`, and `Anneal.ParametricCore.CallStackUnwind`
(ZERO `Miri.*` or `LeanMiriSpec.*` imports, verified by the trailing silent `run_cmd` audit).
-/

namespace Anneal.Mir.CrossFrameRefAndPanicDualSpec

set_option Elab.async false

open MiniRustSpec.CrossFrameRefAndPanicMR
  (MrCrossFramePanicObs mrCanonicalCaseCount mrCrossFramePanicObserve
   mrCrossFramePanicObserve_table mrCrossFramePanicObserve_out_of_range
   mrCrossFramePanicObserve_mode_sensitivity mrExpectedBasicList mrExpectedTbList
   mrCaseModeSensitive ep1_minirust_cross_frame_panic_capstone)
open Anneal.DualCorrespondenceBundle
open Anneal.ParametricCore

/-! ## §1. Frozen Authority-Independent Observation & Mode Interfaces -/

/-- Shared authority-independent observation of one Episode 1 scenario (constructor order
frozen identically to `MrCrossFramePanicObs` and `LmCrossFramePanicObs`). -/
inductive CrossFramePanicObs : Type where
  /-- Normal return carrying `(retVal, callerReferentVal)`. -/
  | okVal (retVal : Nat) (referentVal : Nat)
  /-- Normal return recovered via outer catch harness after cleanup-block mutations. -/
  | okCleanupRecovered (retVal : Nat) (referentVal : Nat)
  /-- Unwound / panicked exit with preserved caller referent value. -/
  | unwound (referentVal : Nat)
  /-- Deterministic process abort (`unwindTerminate`, `UnwindAction.terminate`, `Abort`). -/
  | abort
  /-- Undefined behavior fault. -/
  | ub
  /-- Specification well-formedness panic. -/
  | specPanic
  /-- Fail-closed out-of-range or unsupported case. -/
  | invalidOrUnsupported
  deriving DecidableEq, Repr

/-- Structural translation `MrCrossFramePanicObs → CrossFramePanicObs`. -/
def ofMrObs : MrCrossFramePanicObs → CrossFramePanicObs
  | .okVal r ref => .okVal r ref
  | .okCleanupRecovered r ref => .okCleanupRecovered r ref
  | .unwound ref => .unwound ref
  | .abort => .abort
  | .ub => .ub
  | .specPanic => .specPanic
  | .invalidOrUnsupported => .invalidOrUnsupported

/-- Structural translation `CrossFramePanicObs → MrCrossFramePanicObs`. -/
def toMrObs : CrossFramePanicObs → MrCrossFramePanicObs
  | .okVal r ref => .okVal r ref
  | .okCleanupRecovered r ref => .okCleanupRecovered r ref
  | .unwound ref => .unwound ref
  | .abort => .abort
  | .ub => .ub
  | .specPanic => .specPanic
  | .invalidOrUnsupported => .invalidOrUnsupported

theorem ofMrObs_toMrObs (o : CrossFramePanicObs) : ofMrObs (toMrObs o) = o := by
  cases o <;> rfl

theorem toMrObs_ofMrObs (o : MrCrossFramePanicObs) : toMrObs (ofMrObs o) = o := by
  cases o <;> rfl

theorem ofMrObs_injective {a b : MrCrossFramePanicObs} (h : ofMrObs a = ofMrObs b) : a = b := by
  rw [← toMrObs_ofMrObs a, h, toMrObs_ofMrObs]

/-- Shared dual-authority memory / aliasing mode. -/
inductive CrossFramePanicMode : Type where
  /-- MiniRust `BasicMemory<x86_64>` / LeanMiri `treeBorrows = false`. -/
  | basic
  /-- MiniRust `TreeBorrowsMemory<x86_64>` / LeanMiri `treeBorrows = true`. -/
  | treeBorrows
  deriving DecidableEq, Repr

def CrossFramePanicMode.toLmTreeBorrows : CrossFramePanicMode → Bool
  | .basic => false
  | .treeBorrows => true

def CrossFramePanicMode.ofLmTreeBorrows : Bool → CrossFramePanicMode
  | false => .basic
  | true => .treeBorrows

theorem CrossFramePanicMode.of_toLmTreeBorrows (m : CrossFramePanicMode) :
    CrossFramePanicMode.ofLmTreeBorrows m.toLmTreeBorrows = m := by
  cases m <;> rfl

theorem CrossFramePanicMode.to_ofLmTreeBorrows (b : Bool) :
    (CrossFramePanicMode.ofLmTreeBorrows b).toLmTreeBorrows = b := by
  cases b <;> rfl

def allModes : List CrossFramePanicMode := [.basic, .treeBorrows]

theorem allModes_complete (m : CrossFramePanicMode) : m ∈ allModes := by
  cases m <;> simp [allModes]

/-! ## §2. Constructive Choice-Free Codecs (`[propext, Quot.sound]` ONLY) -/

/-- Wire representation `(tag, payload1, payload2)` for `CrossFramePanicObs`. -/
abbrev CrossFramePanicOutcomeRep : Type := Nat × Nat × Nat

def crossFramePanicEncode : CrossFramePanicObs → CrossFramePanicOutcomeRep
  | .okVal r ref => (0, r, ref)
  | .okCleanupRecovered r ref => (1, r, ref)
  | .unwound ref => (2, ref, 0)
  | .abort => (3, 0, 0)
  | .ub => (4, 0, 0)
  | .specPanic => (5, 0, 0)
  | .invalidOrUnsupported => (6, 0, 0)

/-- Canonical-form decoder accepting strictly the 7 frozen tuple shapes. -/
def crossFramePanicDecode : CrossFramePanicOutcomeRep → Option CrossFramePanicObs
  | (0, r, ref) => some (.okVal r ref)
  | (1, r, ref) => some (.okCleanupRecovered r ref)
  | (2, ref, 0) => some (.unwound ref)
  | (3, 0, 0) => some .abort
  | (4, 0, 0) => some .ub
  | (5, 0, 0) => some .specPanic
  | (6, 0, 0) => some .invalidOrUnsupported
  | _ => none

def crossFramePanicValidRep (b : CrossFramePanicOutcomeRep) : Prop :=
  (crossFramePanicDecode b).isSome = true

theorem crossFramePanicDecode_canonical (b : CrossFramePanicOutcomeRep) (a : CrossFramePanicObs)
    (h : crossFramePanicDecode b = some a) : crossFramePanicEncode a = b := by
  rcases b with ⟨t, x, y⟩
  unfold crossFramePanicDecode at h
  split at h <;> first | (cases h; done) | (cases h; rfl) | (rename_i heq; cases heq; cases h; rfl)

/-- Constructive `Anneal.DualCorrespondenceBundle.CodecLaws` instance for `CrossFramePanicObs`
(zero `Classical.choice`). -/
def crossFramePanicOutcomeCodec : CodecLaws CrossFramePanicObs CrossFramePanicOutcomeRep where
  encode := crossFramePanicEncode
  decode := crossFramePanicDecode
  ValidRep := crossFramePanicValidRep
  decode_encode := fun a => by cases a <;> rfl
  encode_valid := fun a => by cases a <;> rfl
  encode_decode_of_valid := fun b a _ hd => crossFramePanicDecode_canonical b a hd

theorem crossFramePanicOutcomeCodec_tight : crossFramePanicOutcomeCodec.TightValidRep := by
  intro b hv
  change (crossFramePanicDecode b).isSome = true at hv
  cases hd : crossFramePanicDecode b with
  | none => rw [hd] at hv; cases hv
  | some a => exact ⟨a, hd⟩

theorem crossFramePanicOutcomeCodec_encode_injective {a₁ a₂ : CrossFramePanicObs}
    (h : crossFramePanicOutcomeCodec.encode a₁ = crossFramePanicOutcomeCodec.encode a₂) :
    a₁ = a₂ :=
  crossFramePanicOutcomeCodec.encode_injective h

theorem crossFramePanicOutcomeCodec_decode_injective_of_valid
    {b₁ b₂ : CrossFramePanicOutcomeRep} {a : CrossFramePanicObs}
    (hv₁ : crossFramePanicOutcomeCodec.ValidRep b₁)
    (hv₂ : crossFramePanicOutcomeCodec.ValidRep b₂)
    (hd₁ : crossFramePanicOutcomeCodec.decode b₁ = some a)
    (hd₂ : crossFramePanicOutcomeCodec.decode b₂ = some a) : b₁ = b₂ :=
  crossFramePanicOutcomeCodec.decode_injective_of_valid hv₁ hv₂ hd₁ hd₂

/-- Malformed wire tuples are rejected (non-trivial partial inverse). -/
theorem crossFramePanicOutcomeCodec_rejects_malformed :
    crossFramePanicOutcomeCodec.decode (7, 0, 0) = none ∧
    crossFramePanicOutcomeCodec.decode (2, 115, 1) = none ∧
    crossFramePanicOutcomeCodec.decode (3, 1, 0) = none ∧
    crossFramePanicOutcomeCodec.decode (4, 0, 1) = none ∧
    crossFramePanicOutcomeCodec.decode (5, 2, 0) = none ∧
    ¬ crossFramePanicOutcomeCodec.ValidRep (6, 0, 1) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro h; cases h

/-- Normal-return payload domain for `DualCorrespondenceBundle` instantiation, distinguishing
direct normal returns (`recoveredViaCleanup = false`) from catch-harness cleanup-recovered
returns (`recoveredViaCleanup = true`). -/
structure CrossFrameNormalRet : Type where
  retVal : Nat
  referentVal : Nat
  recoveredViaCleanup : Bool
  deriving DecidableEq, Repr

/-- Wire representation `(retVal, referentVal, recoveredViaCleanup)` for `CrossFrameNormalRet`. -/
abbrev CrossFrameNormalRep : Type := Nat × Nat × Bool

/-- Constructive, choice-free `CodecLaws` for `CrossFrameNormalRet` (used directly inside
`DualCorrespondenceBundle`). -/
def crossFrameNormalRetCodec : CodecLaws CrossFrameNormalRet CrossFrameNormalRep :=
  CodecLaws.ofEquiv
    (fun r => (r.retVal, r.referentVal, r.recoveredViaCleanup))
    (fun t => ⟨t.1, t.2.1, t.2.2⟩)
    (fun r => by cases r; rfl)
    (fun t => by rcases t with ⟨a, b, c⟩; rfl)

theorem crossFrameNormalRetCodec_tight : crossFrameNormalRetCodec.TightValidRep :=
  fun b _ => ⟨⟨b.1, b.2.1, b.2.2⟩, rfl⟩

/-! ## §3. Canonical 28-Scenario Table (`0..27`) & Real MiniRust Observation -/

/-- Number of canonical Episode 1 scenarios (`0..27`, `56` mode cells). -/
def canonicalCaseCount : Nat := 28

theorem canonicalCaseCount_eq_mr : canonicalCaseCount = mrCanonicalCaseCount := rfl

/-- Three-way comparison class of a canonical scenario index. -/
inductive CrossFramePanicCaseClass : Type where
  /-- Exact 3-way agreement across `Trusted.MirSemantics`, `MiniRust (MachTB)`, and
  `LeanMiri (treeBorrows = true)` (and exact MR ↔ LM agreement in both modes). -/
  | exactThreeWayAgreement
  /-- Case `27`: bare root-frame unwind with `Memory.rootUnwindCeiling = true` —
  `Trusted` halts with `MirOutcome.panic` (`.unwound 77`), while MiniRust
  (`BottomOfStack`) and LeanMiri (`frames.size == 1`) both fault with `.ub`. -/
  | rootUnwindCeilingDivergence
  deriving DecidableEq, Repr

def caseClass : Nat → CrossFramePanicCaseClass
  | 27 => .rootUnwindCeilingDivergence
  | _ => .exactThreeWayAgreement

/-- Exact Tree Borrows mode-sensitivity predicate across MiniRust and LeanMiri:
Cases `8` (foreign write under active `FnEntry` strong protector) and `9` (write through
`Frozen` `&T`-derived raw pointer). -/
def caseModeSensitive : Nat → Bool
  | 8 | 9 => true
  | _ => false

theorem caseModeSensitive_eq_mr (idx : Nat) :
    caseModeSensitive idx = mrCaseModeSensitive idx := by
  match idx with
  | 8 => rfl
  | 9 => rfl
  | _ => rfl

/-- Real MiniRust observation, translated from `MiniRustSpec.CrossFrameRefAndPanicMR`. -/
def mrObserve (m : CrossFramePanicMode) (idx : Nat) : CrossFramePanicObs :=
  ofMrObs (mrCrossFramePanicObserve m.toLmTreeBorrows idx)

/-- Frozen expected table shared identically by MiniRust (`Mach` / `MachTB`) and LeanMiri
(`treeBorrows = false` / `true`) over ALL `idx : Nat`. -/
def authorityExpected (m : CrossFramePanicMode) : Nat → CrossFramePanicObs
  | 0 => .okVal 42 42
  | 1 => .okVal 77 77
  | 2 => .okVal 99 99
  | 3 => .okVal 88 10088
  | 4 => .okVal 44 44033
  | 5 => .okVal 66 66055
  | 6 => .okVal 34 34
  | 7 => .okVal 20 20
  | 8 => match m with | .basic => .okVal 77 77 | .treeBorrows => .ub
  | 9 => match m with | .basic => .okVal 99 99 | .treeBorrows => .ub
  | 10 | 11 | 12 | 13 => .ub
  | 14 => .okVal 101 101
  | 15 => .okVal 102 102
  | 16 => .ub
  | 17 => .unwound 115
  | 18 | 19 => .abort
  | 20 => .ub
  | 21 => .okCleanupRecovered 65 65
  | 22 => .abort
  | 23 => .okCleanupRecovered 300 300
  | 24 => .abort
  | 25 | 26 | 27 => .ub
  | _ => .invalidOrUnsupported

/-- Frozen expected table for unmodified `Trusted.Rustc.V2026_06_01.MirSemantics`
(`TreeBorrows`-enforcing semantics, differing from `authorityExpected .treeBorrows`
strictly at Case `27` where `Memory.rootUnwindCeiling = true`). -/
def trustedExpected : Nat → CrossFramePanicObs
  | 27 => .unwound 77
  | idx => authorityExpected .treeBorrows idx

theorem authorityExpected_out_of_range (m : CrossFramePanicMode) (idx : Nat)
    (h : canonicalCaseCount ≤ idx) :
    authorityExpected m idx = .invalidOrUnsupported := by
  unfold canonicalCaseCount at h
  unfold authorityExpected
  split <;> first | rfl | omega

theorem trustedExpected_out_of_range (idx : Nat) (h : canonicalCaseCount ≤ idx) :
    trustedExpected idx = .invalidOrUnsupported := by
  unfold canonicalCaseCount at h
  cases idx with
  | zero => omega
  | succ n =>
    unfold trustedExpected
    split
    · omega
    · exact authorityExpected_out_of_range .treeBorrows _ (by unfold canonicalCaseCount; omega)

theorem trustedExpected_ne_authority_iff (idx : Nat) :
    trustedExpected idx ≠ authorityExpected .treeBorrows idx ↔ idx = 27 := by
  cases h : Nat.beq idx 27 with
  | true =>
    have h27 := Nat.eq_of_beq_eq_true h
    subst h27
    exact ⟨fun _ => rfl, fun _ hEq => by cases hEq⟩
  | false =>
    have hNe : idx ≠ 27 := Nat.ne_of_beq_eq_false h
    have hEq : trustedExpected idx = authorityExpected .treeBorrows idx := by
      unfold trustedExpected
      split
      · exact absurd rfl hNe
      · rfl
    exact ⟨fun hN => absurd hEq hN, fun h27 => absurd h27 hNe⟩

/-- **Canonical-table non-degeneracy guard**: NO canonical cell (`idx < 28`) of either authority
table or of the Trusted table is a fail-closed `.invalidOrUnsupported` or `.specPanic`
observation, so every one of the `28 × 3` canonical verdicts is a genuine semantic outcome
(normal / cleanup-recovered / unwound / abort / UB), never a vacuous "both sides unsupported"
agreement. -/
theorem canonical_cells_nondegenerate :
    ∀ idx, idx < canonicalCaseCount →
      authorityExpected .basic idx ≠ .invalidOrUnsupported ∧
      authorityExpected .basic idx ≠ .specPanic ∧
      authorityExpected .treeBorrows idx ≠ .invalidOrUnsupported ∧
      authorityExpected .treeBorrows idx ≠ .specPanic ∧
      trustedExpected idx ≠ .invalidOrUnsupported ∧
      trustedExpected idx ≠ .specPanic := by
  decide

private theorem range_map_cell {α : Type} {f : Nat → α} {xs : List α} {n : Nat}
    (h : (List.range n).map f = xs) (i : Nat) (hi : i < n) :
    some (f i) = xs[i]? := by
  have h' := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some] at h'
  exact h'

/-- Real MiniRust (`Mach` & `MachTB`) matches `authorityExpected` on EVERY `idx : Nat`. -/
theorem mrObserve_matches_expected (m : CrossFramePanicMode) (idx : Nat) :
    mrObserve m idx = authorityExpected m idx := by
  by_cases hlt : idx < canonicalCaseCount
  · have hBasicList : mrExpectedBasicList.map ofMrObs =
        (List.range canonicalCaseCount).map (authorityExpected .basic) := by decide
    have hTbList : mrExpectedTbList.map ofMrObs =
        (List.range canonicalCaseCount).map (authorityExpected .treeBorrows) := by decide
    cases m with
    | basic =>
      have hM : (List.range canonicalCaseCount).map (mrObserve .basic) =
          (List.range canonicalCaseCount).map (authorityExpected .basic) := by
        calc (List.range canonicalCaseCount).map (mrObserve .basic)
            = ((List.range mrCanonicalCaseCount).map (mrCrossFramePanicObserve false)).map ofMrObs := by
                rw [List.map_map]; rfl
          _ = mrExpectedBasicList.map ofMrObs := by rw [mrCrossFramePanicObserve_table.1]
          _ = (List.range canonicalCaseCount).map (authorityExpected .basic) := hBasicList
      have hCell := congrArg (fun l => l[idx]?) hM
      simp only [List.getElem?_map, List.getElem?_range hlt, Option.map_some] at hCell
      exact Option.some.inj hCell
    | treeBorrows =>
      have hM : (List.range canonicalCaseCount).map (mrObserve .treeBorrows) =
          (List.range canonicalCaseCount).map (authorityExpected .treeBorrows) := by
        calc (List.range canonicalCaseCount).map (mrObserve .treeBorrows)
            = ((List.range mrCanonicalCaseCount).map (mrCrossFramePanicObserve true)).map ofMrObs := by
                rw [List.map_map]; rfl
          _ = mrExpectedTbList.map ofMrObs := by rw [mrCrossFramePanicObserve_table.2]
          _ = (List.range canonicalCaseCount).map (authorityExpected .treeBorrows) := hTbList
      have hCell := congrArg (fun l => l[idx]?) hM
      simp only [List.getElem?_map, List.getElem?_range hlt, Option.map_some] at hCell
      exact Option.some.inj hCell
  · have hge : canonicalCaseCount ≤ idx := Nat.le_of_not_lt hlt
    rw [authorityExpected_out_of_range m idx hge]
    unfold mrObserve
    rw [mrCrossFramePanicObserve_out_of_range m.toLmTreeBorrows idx hge]
    rfl

theorem mrObserve_out_of_range (m : CrossFramePanicMode) (idx : Nat)
    (h : canonicalCaseCount ≤ idx) : mrObserve m idx = .invalidOrUnsupported := by
  rw [mrObserve_matches_expected, authorityExpected_out_of_range m idx h]

theorem mrObserve_mode_sensitivity :
    mrObserve .basic 8 = .okVal 77 77 ∧
    mrObserve .treeBorrows 8 = .ub ∧
    mrObserve .basic 9 = .okVal 99 99 ∧
    mrObserve .treeBorrows 9 = .ub ∧
    (∀ idx, idx < canonicalCaseCount →
      (mrObserve .basic idx ≠ mrObserve .treeBorrows idx ↔ caseModeSensitive idx = true)) := by
  refine ⟨by rw [mrObserve_matches_expected]; rfl,
          by rw [mrObserve_matches_expected]; rfl,
          by rw [mrObserve_matches_expected]; rfl,
          by rw [mrObserve_matches_expected]; rfl, ?_⟩
  intro idx hi
  have hMr := mrCrossFramePanicObserve_mode_sensitivity.2.2.2.2 idx hi
  rw [caseModeSensitive_eq_mr]
  constructor
  · intro hne
    apply hMr.mp
    intro heq
    exact hne (congrArg ofMrObs heq)
  · intro hs heq
    exact hMr.mpr hs (ofMrObs_injective heq)

/-! ## §4. Parameterized `LeanMiri` Authority Interface (`CrossFramePanicLmAuthority`) -/

/-- Root-isolated interface to the independent LeanMiri (`Miri`) authority, closed across
roots by `LeanMiriSpec.CrossFrameRefAndPanicLM.lmCrossFramePanicObserve`. -/
structure CrossFramePanicLmAuthority : Type where
  observe : Bool → Nat → CrossFramePanicObs
  matchesExpected : ∀ (tb : Bool) (idx : Nat), idx < canonicalCaseCount →
    observe tb idx = authorityExpected (CrossFramePanicMode.ofLmTreeBorrows tb) idx
  outOfRange : ∀ (tb : Bool) (idx : Nat), canonicalCaseCount ≤ idx →
    observe tb idx = .invalidOrUnsupported

/-- Decidable finite check for the 56-cell LeanMiri table (constructive, zero `Classical.choice`). -/
def lmAuthorityCheck (obs : Bool → Nat → CrossFramePanicObs) : Bool :=
  (List.range canonicalCaseCount).all (fun idx =>
    decide (obs false idx = authorityExpected .basic idx) &&
    decide (obs true idx = authorityExpected .treeBorrows idx))

theorem lmAuthorityCheck_sound (obs : Bool → Nat → CrossFramePanicObs)
    (hCheck : lmAuthorityCheck obs = true)
    (hOor : ∀ tb idx, canonicalCaseCount ≤ idx → obs tb idx = .invalidOrUnsupported) :
    ∀ (tb : Bool) (idx : Nat),
      obs tb idx = authorityExpected (CrossFramePanicMode.ofLmTreeBorrows tb) idx := by
  intro tb idx
  match Nat.lt_or_ge idx canonicalCaseCount with
  | .inl hi =>
    have hCell := List.all_eq_true.mp hCheck idx (List.mem_range.mpr hi)
    cases tb with
    | false => exact of_decide_eq_true (Bool.and_eq_true _ _ |>.mp hCell).1
    | true => exact of_decide_eq_true (Bool.and_eq_true _ _ |>.mp hCell).2
  | .inr hge =>
    rw [hOor tb idx hge, authorityExpected_out_of_range _ idx hge]

/-- Constructive builder for `CrossFramePanicLmAuthority` from `lmAuthorityCheck` + out-of-range. -/
def lmAuthorityOfCheck (obs : Bool → Nat → CrossFramePanicObs)
    (hCheck : lmAuthorityCheck obs = true)
    (hOor : ∀ tb idx, canonicalCaseCount ≤ idx → obs tb idx = .invalidOrUnsupported) :
    CrossFramePanicLmAuthority where
  observe := obs
  matchesExpected := fun tb idx _hi => lmAuthorityCheck_sound obs hCheck hOor tb idx
  outOfRange := hOor

/-- Unified MiniRust ↔ LeanMiri contract packaging a certified `CrossFramePanicLmAuthority`. -/
structure CrossFramePanicDualContract : Type where
  lm : CrossFramePanicLmAuthority

/-- **Interface satisfiability witness** (NOT the LeanMiri closure — that is Episode 2's
cross-root `run_cmd` instantiation from `LeanMiriSpec.CrossFrameRefAndPanicLM`): the
`CrossFramePanicLmAuthority` obligations are jointly satisfiable by a REAL kernel-executed
observer (MiniRust's own `Mach`/`MachTB` table), so every `∀ c : CrossFramePanicDualContract`
theorem in this module (including the capstone and `mkCrossFramePanicDualBundle`) quantifies
over a provably INHABITED type and can never hold vacuously. -/
def mrBackedLmAuthority : CrossFramePanicLmAuthority where
  observe := fun tb idx => mrObserve (CrossFramePanicMode.ofLmTreeBorrows tb) idx
  matchesExpected := fun _ idx _ => mrObserve_matches_expected _ idx
  outOfRange := fun _ idx h => mrObserve_out_of_range _ idx h

theorem crossFramePanicDualContract_nonempty : Nonempty CrossFramePanicDualContract :=
  ⟨⟨mrBackedLmAuthority⟩⟩

theorem CrossFramePanicDualContract.lm_matches_all (c : CrossFramePanicDualContract)
    (m : CrossFramePanicMode) (idx : Nat) :
    c.lm.observe m.toLmTreeBorrows idx = authorityExpected m idx := by
  by_cases hlt : idx < canonicalCaseCount
  · have h := c.lm.matchesExpected m.toLmTreeBorrows idx hlt
    rw [CrossFramePanicMode.of_toLmTreeBorrows] at h
    exact h
  · have hge : canonicalCaseCount ≤ idx := Nat.le_of_not_lt hlt
    rw [c.lm.outOfRange m.toLmTreeBorrows idx hge, authorityExpected_out_of_range m idx hge]

/-- **Total MiniRust ↔ LeanMiri exact equality across ALL modes and ALL `idx : Nat`**
(all 56 canonical cells + all out-of-range indices). -/
theorem contract_mr_lm_total_eq (c : CrossFramePanicDualContract)
    (m : CrossFramePanicMode) (idx : Nat) :
    mrObserve m idx = c.lm.observe m.toLmTreeBorrows idx := by
  rw [mrObserve_matches_expected, c.lm_matches_all]

theorem contract_lm_basic_eq (c : CrossFramePanicDualContract) (idx : Nat) :
    c.lm.observe false idx = mrObserve .basic idx :=
  (contract_mr_lm_total_eq c .basic idx).symm

theorem contract_lm_tb_eq (c : CrossFramePanicDualContract) (idx : Nat) :
    c.lm.observe true idx = mrObserve .treeBorrows idx :=
  (contract_mr_lm_total_eq c .treeBorrows idx).symm

/-- **Total wire-level codec equality across MiniRust and LeanMiri** (`CodecLaws.encode`). -/
theorem contract_wire_total_eq (c : CrossFramePanicDualContract)
    (m : CrossFramePanicMode) (idx : Nat) :
    crossFramePanicOutcomeCodec.encode (mrObserve m idx) =
      crossFramePanicOutcomeCodec.encode (c.lm.observe m.toLmTreeBorrows idx) :=
  congrArg crossFramePanicOutcomeCodec.encode (contract_mr_lm_total_eq c m idx)

/-- **Joint Tree Borrows mode sensitivity across BOTH MiniRust and LeanMiri**: Cases `8`
(foreign write under active `FnEntry` strong protector) and `9` (write through `Frozen`
`&T`-derived raw pointer) flip together between `.basic` and `.treeBorrows`. -/
theorem contract_joint_mode_sensitivity (c : CrossFramePanicDualContract) :
    (mrObserve .basic 8 = .okVal 77 77 ∧ c.lm.observe false 8 = .okVal 77 77 ∧
     mrObserve .treeBorrows 8 = .ub ∧ c.lm.observe true 8 = .ub) ∧
    (mrObserve .basic 9 = .okVal 99 99 ∧ c.lm.observe false 9 = .okVal 99 99 ∧
     mrObserve .treeBorrows 9 = .ub ∧ c.lm.observe true 9 = .ub) ∧
    (∀ idx, idx < canonicalCaseCount →
      (c.lm.observe false idx ≠ c.lm.observe true idx ↔ caseModeSensitive idx = true)) := by
  refine ⟨⟨mrObserve_mode_sensitivity.1,
           by rw [contract_lm_basic_eq]; exact mrObserve_mode_sensitivity.1,
           mrObserve_mode_sensitivity.2.1,
           by rw [contract_lm_tb_eq]; exact mrObserve_mode_sensitivity.2.1⟩,
          ⟨mrObserve_mode_sensitivity.2.2.1,
           by rw [contract_lm_basic_eq]; exact mrObserve_mode_sensitivity.2.2.1,
           mrObserve_mode_sensitivity.2.2.2.1,
           by rw [contract_lm_tb_eq]; exact mrObserve_mode_sensitivity.2.2.2.1⟩, ?_⟩
  intro idx hi
  rw [contract_lm_basic_eq, contract_lm_tb_eq]
  exact mrObserve_mode_sensitivity.2.2.2.2 idx hi

/-! ## §5. Direct Bridge to Unmodified `Trusted.Rustc.V2026_06_01.MirSemantics` & `CallStackUnwind.UnwindAction4` -/

section TrustedAndUnwindBridge

open Trusted.Effect
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Sequence

abbrev TrustedMem := Trusted.Rustc.V2026_06_01.MirSemantics.Memory

/-- Close a kernel definitional equality goal without `Lean.ofReduceBool`. -/
local elab "kernel_rfl" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let tgt ← Lean.MVarId.getType' mvarId
  let some (ty, lhs, _) := tgt.eq?
    | Lean.Meta.throwTacticEx `kernel_rfl mvarId "expected equality goal"
  let u ← Lean.Meta.getLevel ty
  mvarId.assign (Lean.mkApp2 (Lean.mkConst ``Eq.refl [u]) ty lhs)
  Lean.Elab.Tactic.replaceMainGoal []

/-! ### §5a. Constructive Bijection & Operational Correspondence with `Anneal.ParametricCore.CallStackUnwind.UnwindAction4` -/

/-- Exact structural translation from unmodified `MirAst.UnwindAction` to
`Anneal.ParametricCore.UnwindAction4`. -/
def mirToUnwindAction4 : UnwindAction → UnwindAction4
  | .cleanup bb => .cleanup bb
  | .unreachable => .unreachable
  | .terminate => .terminate
  | .continue_ => .continue_

/-- Exact structural inverse from `Anneal.ParametricCore.UnwindAction4` to
`MirAst.UnwindAction`. -/
def unwindAction4ToMir : UnwindAction4 → UnwindAction
  | .cleanup bb => .cleanup bb
  | .unreachable => .unreachable
  | .terminate => .terminate
  | .continue_ => .continue_

theorem mirToUnwindAction4_left_inv (u : UnwindAction) :
    unwindAction4ToMir (mirToUnwindAction4 u) = u := by
  cases u <;> rfl

theorem mirToUnwindAction4_right_inv (u : UnwindAction4) :
    mirToUnwindAction4 (unwindAction4ToMir u) = u := by
  cases u <;> rfl

/-- Constructive `CodecLaws` witnessing the exact bijection `MirAst.UnwindAction ≃ UnwindAction4`
(zero `Classical.choice`). -/
def unwindAction4Codec : CodecLaws UnwindAction UnwindAction4 :=
  CodecLaws.ofEquiv mirToUnwindAction4 unwindAction4ToMir
    mirToUnwindAction4_left_inv mirToUnwindAction4_right_inv

/-- **Universal 4-way operational correspondence between unmodified
`Trusted.MirSemantics.applyUnwindAction` and `Anneal.ParametricCore.evalRefFrameExit`**:
for every `u : MirAst.UnwindAction`, every machine state `(s, localsAfter, memAfter)`,
every `ByteStoreOps` memory `m`, every `RefFrame` whose `onUnwind = mirToUnwindAction4 u`,
and every valid partial `&mut` writeback `L.set m partialSlice = some m'`, the 4-way
control-flow regime of `applyUnwindAction` matches `evalRefFrameExit` constructor-for-constructor:
- `.cleanup bb` ↔ `.running { blockIdx := bb, ... }` and `.jumpCleanup bb m'`
- `.continue_` ↔ `unwindFromCallStack memAfter.callStack memAfter` and `.propagateUnwind m'`
- `.terminate` ↔ `.halted .abort` and `.abortTerminate m'`
- `.unreachable` ↔ `.faulted .ub` and `.fault`. -/
theorem applyUnwindAction_matches_evalRefFrameExit
    {Mem Addr Byte Val : Type} [ByteStoreOps Mem Addr Byte]
    (s : MachineState) (localsAfter : List LocalSlot) (memAfter : TrustedMem)
    (u : UnwindAction) (L : ByteSubLens Addr) (onRet : Option Nat)
    (m m' : Mem) (partialSlice : List Byte)
    (hSet : L.set m partialSlice = some m') :
    match u with
    | .cleanup bb =>
      applyUnwindAction s localsAfter memAfter u =
        .running { frame := { s.frame with blockIdx := bb, stmtIdx := 0, locals := localsAfter },
                   memory := memAfter } ∧
      evalRefFrameExit ⟨L, ⟨onRet, mirToUnwindAction4 u⟩⟩ m
        (CalleeExit.unwound (Val := Val) partialSlice) = .jumpCleanup bb m'
    | .continue_ =>
      applyUnwindAction s localsAfter memAfter u =
        unwindFromCallStack memAfter.callStack memAfter ∧
      evalRefFrameExit ⟨L, ⟨onRet, mirToUnwindAction4 u⟩⟩ m
        (CalleeExit.unwound (Val := Val) partialSlice) = .propagateUnwind m'
    | .terminate =>
      applyUnwindAction s localsAfter memAfter u = .halted .abort ∧
      evalRefFrameExit ⟨L, ⟨onRet, mirToUnwindAction4 u⟩⟩ m
        (CalleeExit.unwound (Val := Val) partialSlice) = .abortTerminate m'
    | .unreachable =>
      applyUnwindAction s localsAfter memAfter u = .faulted .ub ∧
      evalRefFrameExit ⟨L, ⟨onRet, mirToUnwindAction4 u⟩⟩ m
        (CalleeExit.unwound (Val := Val) partialSlice) = .fault := by
  cases u with
  | cleanup bb =>
    refine ⟨rfl, ?_⟩
    unfold evalRefFrameExit mirToUnwindAction4
    dsimp only; rw [hSet]
  | continue_ =>
    refine ⟨rfl, ?_⟩
    unfold evalRefFrameExit mirToUnwindAction4
    dsimp only; rw [hSet]
  | terminate =>
    refine ⟨rfl, ?_⟩
    unfold evalRefFrameExit mirToUnwindAction4
    dsimp only; rw [hSet]
  | unreachable =>
    exact ⟨rfl, rfl⟩

/-- **Universal protected frame-exit correspondence between unmodified
`Trusted.MirSemantics.applyUnwindAction` and `Anneal.ParametricCore.evalProtectedRefFrameExit`**:
1. When protector release succeeds (`exitFrameWithProtectors tree prf.frameTags = ⟨tree', .Released⟩`),
   every tag in `prf.frameTags` is stripped from `tree'.protectedTags`, every outer tag not in
   `prf.frameTags` is preserved (LIFO!), AND the resulting `CallerContOutcome` matches
   `Trusted.MirSemantics.applyUnwindAction` across ALL 4 `MirAst.UnwindAction` variants.
2. Fail-closed conflict: when `exitFrameWithProtectors` reports `.AccessFailure` (e.g., a
   `.ProtectedDisabled` violation), `evalProtectedRefFrameExit` unconditionally returns `.fault`. -/
theorem applyUnwindAction_matches_evalProtectedRefFrameExit
    {Mem Addr Byte Val : Type} [ByteStoreOps Mem Addr Byte]
    (s : MachineState) (localsAfter : List LocalSlot) (memAfter : TrustedMem)
    (u : UnwindAction) (L : ByteSubLens Addr) (onRet : Option Nat) (frameTags : List Nat)
    (m m' : Mem) (partialSlice : List Byte)
    (hSet : L.set m partialSlice = some m') :
    let prf : ProtectedRefFrame Addr := ⟨⟨L, ⟨onRet, mirToUnwindAction4 u⟩⟩, frameTags⟩
    (∀ tree tree',
      Anneal.RefFrame.exitFrameWithProtectors tree frameTags = ⟨tree', .Released⟩ →
      (∀ t, Anneal.RefFrame.natListMem t frameTags = true →
        Anneal.RefFrame.natListMem t tree'.protectedTags = false) ∧
      (∀ t, Anneal.RefFrame.natListMem t frameTags = false →
        Anneal.RefFrame.natListMem t tree'.protectedTags =
          Anneal.RefFrame.natListMem t tree.protectedTags) ∧
      match u with
      | .cleanup bb =>
        applyUnwindAction s localsAfter memAfter u =
          .running { frame := { s.frame with blockIdx := bb, stmtIdx := 0, locals := localsAfter },
                     memory := memAfter } ∧
        evalProtectedRefFrameExit prf m tree (CalleeExit.unwound (Val := Val) partialSlice) =
          (.jumpCleanup bb m', tree')
      | .continue_ =>
        applyUnwindAction s localsAfter memAfter u =
          unwindFromCallStack memAfter.callStack memAfter ∧
        evalProtectedRefFrameExit prf m tree (CalleeExit.unwound (Val := Val) partialSlice) =
          (.propagateUnwind m', tree')
      | .terminate =>
        applyUnwindAction s localsAfter memAfter u = .halted .abort ∧
        evalProtectedRefFrameExit prf m tree (CalleeExit.unwound (Val := Val) partialSlice) =
          (.abortTerminate m', tree')
      | .unreachable =>
        applyUnwindAction s localsAfter memAfter u = .faulted .ub ∧
        evalProtectedRefFrameExit prf m tree (CalleeExit.unwound (Val := Val) partialSlice) =
          (.fault, tree')) ∧
    (∀ tree tree' off len nodeTag err,
      Anneal.RefFrame.exitFrameWithProtectors tree frameTags =
        ⟨tree', .AccessFailure off len nodeTag err⟩ →
      (evalProtectedRefFrameExit prf m tree (CalleeExit.unwound (Val := Val) partialSlice)).1 =
        .fault) := by
  intro prf
  refine ⟨?_, ?_⟩
  · intro tree tree' hRel
    have hProt := evalProtectedRefFrameExit_of_released (Val := Val) prf m
      (CalleeExit.unwound (Val := Val) partialSlice) hRel
    have hBase := applyUnwindAction_matches_evalRefFrameExit (Val := Val) s localsAfter memAfter
      u L onRet m m' partialSlice hSet
    refine ⟨hProt.2.1, hProt.2.2, ?_⟩
    cases u with
    | cleanup bb =>
      refine ⟨hBase.1, ?_⟩
      rw [hProt.1, hBase.2]
    | continue_ =>
      refine ⟨hBase.1, ?_⟩
      rw [hProt.1, hBase.2]
    | terminate =>
      refine ⟨hBase.1, ?_⟩
      rw [hProt.1, hBase.2]
    | unreachable =>
      refine ⟨hBase.1, ?_⟩
      rw [hProt.1, hBase.2]
  · intro tree tree' off len nodeTag err hErr
    exact evalProtectedRefFrameExit_fault_of_accessFailure prf m
      (CalleeExit.unwound (Val := Val) partialSlice) hErr

/-! ### §5b. Universal Trusted Protector, Deallocation, & Multi-Frame Unwind Laws -/

/-- Embedding `TreeBorrowPerm → MiniRustSpec.Gen.PermissionProt` matching MiniRust's
deallocation-prevention predicate. -/
def trustedPermToMrProt : TreeBorrowPerm → MiniRustSpec.Gen.PermissionProt
  | .cell => .Cell
  | .reservedFrz conflicted => .Reserved true conflicted
  | .reservedIM => .Reserved true false
  | .unique => .Unique
  | .frozen => .Frozen true
  | .disabled => .Disabled

theorem preventsDeallocation_eq_mr (p : TreeBorrowPerm) :
    preventsDeallocation p =
      MiniRustSpec.Interp.PermissionProt.prevents_deallocation (trustedPermToMrProt p) := by
  cases p <;> rfl

/-- **Universal `disableFrameBorrows` postcondition**: every borrow targeting a local `< nLocals`
of frame `depth` is marked `.disabled` with `allocDead = true`, while every borrow of any
outer caller frame (`targetFrameDepth ≠ depth`) is preserved untouched. -/
theorem disableFrameBorrows_preserves_outer_frames (borrows : List BorrowEntry)
    (depth nLocals : Nat) :
    (∀ e ∈ disableFrameBorrows borrows depth nLocals,
      e.targetFrameDepth = depth → e.targetLocal < nLocals →
        e.perm = .disabled ∧ e.allocDead = true) ∧
    (∀ e ∈ borrows, e.targetFrameDepth ≠ depth →
      e ∈ disableFrameBorrows borrows depth nLocals) := by
  induction borrows with
  | nil => exact ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩
  | cons e rest ih =>
    rw [disableFrameBorrows]
    cases hm : (Nat.beq e.targetFrameDepth depth && Nat.blt e.targetLocal nLocals) with
    | true =>
      obtain ⟨hd, _⟩ := Bool.and_eq_true _ _ |>.mp hm
      have hd' := Nat.eq_of_beq_eq_true hd
      refine ⟨fun x hx hxd hxl => ?_, fun x hx hne => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨rfl, rfl⟩
        · exact ih.1 x hx' hxd hxl
      · rcases List.mem_cons.mp hx with rfl | hx'
        · exact absurd hd' hne
        · exact List.mem_cons_of_mem _ (ih.2 x hx' hne)
    | false =>
      refine ⟨fun x hx hxd hxl => ?_, fun x hx hne => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx'
        · have h1 : Nat.beq x.targetFrameDepth depth = true := by rw [hxd]; exact Nat.beq_refl depth
          have h2 : Nat.blt x.targetLocal nLocals = true := Nat.blt_eq.mpr hxl
          rw [h1, h2] at hm; cases hm
        · exact ih.1 x hx' hxd hxl
      · rcases List.mem_cons.mp hx with rfl | hx'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih.2 x hx' hne)

/-- **Universal `disableFramesAbove` postcondition** (executed by `unwindFromCallStack` on
every `.cleanup` landing): every borrow belonging to a popped frame (`targetFrameDepth > maxDepth`)
becomes `.disabled` with `allocDead = true`, while every borrow belonging to an outer surviving
frame (`targetFrameDepth ≤ maxDepth`) is preserved intact! -/
theorem disableFramesAbove_preserves_surviving_frames (borrows : List BorrowEntry)
    (maxDepth : Nat) :
    (∀ e ∈ disableFramesAbove borrows maxDepth,
      maxDepth < e.targetFrameDepth → e.perm = .disabled ∧ e.allocDead = true) ∧
    (∀ e ∈ borrows, e.targetFrameDepth ≤ maxDepth →
      e ∈ disableFramesAbove borrows maxDepth) := by
  induction borrows with
  | nil => exact ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩
  | cons e rest ih =>
    rw [disableFramesAbove]
    cases hm : Nat.blt maxDepth e.targetFrameDepth with
    | true =>
      have hgt : maxDepth < e.targetFrameDepth := Nat.blt_eq.mp hm
      refine ⟨fun x hx hlt => ?_, fun x hx hle => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨rfl, rfl⟩
        · exact ih.1 x hx' hlt
      · rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · exact List.mem_cons_of_mem _ (ih.2 x hx' hle)
    | false =>
      refine ⟨fun x hx hlt => ?_, fun x hx hle => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx'
        · have h1 : Nat.blt maxDepth x.targetFrameDepth = true := Nat.blt_eq.mpr hlt
          rw [h1] at hm; cases hm
        · exact ih.1 x hx' hlt
      · rcases List.mem_cons.mp hx with rfl | hx'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih.2 x hx' hle)

/-- **Universal `hasFrameDeallocProtectorConflict` characterization**: true iff there is an
active protector whose borrow targets a local `< nLocals` of `depth` with a deallocation-preventing
permission. -/
theorem hasFrameDeallocProtectorConflict_iff (borrows : List BorrowEntry) (ap : List Nat)
    (depth nLocals : Nat) :
    hasFrameDeallocProtectorConflict borrows ap depth nLocals = true ↔
      ap ≠ [] ∧ ∃ e ∈ borrows, e.targetFrameDepth = depth ∧ e.targetLocal < nLocals ∧
        isBorrowProtected ap e = true ∧ preventsDeallocation e.perm = true := by
  induction borrows with
  | nil => cases ap <;> simp [hasFrameDeallocProtectorConflict]
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

/-- **Universal multi-frame `.continue_` unwind landing into outer `.cleanup`**:
popping a chain `conts` of `.continue_` frames followed by a `catcher` frame with
`returnUnwind = .cleanup cleanupBb` restores protectors in strict LIFO order, disables
all popped callee frame borrows above `restStack.length`, and resumes at `catcher`'s
`cleanupBb` with `catcher.frame.locals` (carrying all pre-panic `&mut` writebacks!). -/
theorem trusted_unwind_continue_chain_to_cleanup
    (conts : List SavedCallerFrame) (catcher : SavedCallerFrame)
    (restStack : List SavedCallerFrame) (mem : TrustedMem) (cleanupBb : BasicBlockIdx)
    (hConts : ∀ c ∈ conts, c.returnUnwind = .continue_)
    (hCatch : catcher.returnUnwind = .cleanup cleanupBb) :
    let memPopped := MiniRustSpec.CrossFrameRefAndPanicMR.unwindContinuePopMem conts (catcher :: restStack) mem
    let memCatcher : TrustedMem :=
      { memPopped with
        callStack := restStack
        activeCallee := .some catcher.callerBody
        activeProtectors := restoreCallerProtectors catcher }
    unwindFromCallStack (conts ++ catcher :: restStack) mem =
      .running {
        frame := { catcher.frame with blockIdx := cleanupBb, stmtIdx := 0 }
        memory := { memCatcher with borrows := disableFramesAbove memCatcher.borrows (length restStack) }
      } := by
  rw [MiniRustSpec.CrossFrameRefAndPanicMR.trusted_unwindFromCallStack_continue_chain conts (catcher :: restStack) mem hConts]
  simp only [unwindFromCallStack, hCatch]

/-- **Universal multi-frame unwind protector-release & outer-protector-preservation law** directly
on unmodified `Trusted.MirSemantics.{unwindFromCallStack, restoreCallerProtectors, isBorrowProtected}`:
when a chain `conts` of `.continue_` frames unwinds into `catcher` (`returnUnwind = .cleanup cleanupBb`),
the resulting running state `s'` has:
1. every popped callee borrow entry whose protector is absent from `restoreCallerProtectors catcher`
   is NO LONGER protected (`isBorrowProtected s'.memory.activeProtectors e = false`), enabling
   caller cleanup writes (Cases `21` and `23`);
2. every surviving outer borrow entry whose protector IS present in `restoreCallerProtectors catcher`
   REMAINS protected (`isBorrowProtected s'.memory.activeProtectors eOuter = true`, strict LIFO!). -/
theorem trusted_unwind_releases_callee_protector
    (conts : List SavedCallerFrame) (catcher : SavedCallerFrame)
    (restStack : List SavedCallerFrame) (mem : TrustedMem) (cleanupBb : BasicBlockIdx)
    (hConts : ∀ c ∈ conts, c.returnUnwind = .continue_)
    (hCatch : catcher.returnUnwind = .cleanup cleanupBb) :
    ∃ s',
      unwindFromCallStack (conts ++ catcher :: restStack) mem = .running s' ∧
      s'.memory.activeProtectors = restoreCallerProtectors catcher ∧
      (∀ (e : BorrowEntry) (p : Nat),
        e.protector = .some p →
        natListContainsBool (restoreCallerProtectors catcher) p = false →
        isBorrowProtected s'.memory.activeProtectors e = false) ∧
      (∀ (eOuter : BorrowEntry) (pOuter : Nat),
        eOuter.protector = .some pOuter →
        natListContainsBool (restoreCallerProtectors catcher) pOuter = true →
        isBorrowProtected s'.memory.activeProtectors eOuter = true) := by
  have hUnw := trusted_unwind_continue_chain_to_cleanup conts catcher restStack mem cleanupBb hConts hCatch
  refine ⟨_, hUnw, rfl, ?_, ?_⟩
  · intro e p hP hNot
    unfold isBorrowProtected
    rw [hP]
    exact hNot
  · intro eOuter pOuter hP hIn
    unfold isBorrowProtected
    rw [hP]
    exact hIn

/-- **Universal root-unwind ceiling boundary theorem**:
- When `mem.rootUnwindCeiling = false`, unwinding past all `.continue_` frames to empty
  `callStack` faults with `.faulted .ub` (3-way agreement with MiniRust `BottomOfStack` UB
  and LeanMiri `frames.size == 1` UB).
- When `mem.rootUnwindCeiling = true`, unwinding past all `.continue_` frames halts with
  `.halted .panic` (the exact Case `27` root-ceiling divergence boundary). -/
theorem trusted_unwind_continue_chain_root_boundary
    (conts : List SavedCallerFrame) (mem : TrustedMem)
    (hConts : ∀ c ∈ conts, c.returnUnwind = .continue_) :
    (mem.rootUnwindCeiling = false → unwindFromCallStack conts mem = .faulted .ub) ∧
    (mem.rootUnwindCeiling = true → unwindFromCallStack conts mem = .halted .panic) := by
  have hApp : conts ++ [] = conts := List.append_nil conts
  have hChain := MiniRustSpec.CrossFrameRefAndPanicMR.trusted_unwindFromCallStack_continue_chain conts [] mem hConts
  rw [hApp] at hChain
  have hCeil := MiniRustSpec.CrossFrameRefAndPanicMR.unwindContinuePopMem_rootUnwindCeiling conts [] mem
  refine ⟨fun hF => ?_, fun hT => ?_⟩
  · rw [hChain]
    exact (MiniRustSpec.CrossFrameRefAndPanicMR.trusted_unwindFromCallStack_root_ceiling_iff _).2 (hCeil.trans hF)
  · rw [hChain]
    exact (MiniRustSpec.CrossFrameRefAndPanicMR.trusted_unwindFromCallStack_root_ceiling_iff _).1 (hCeil.trans hT)

/-! ### §5c. Real Multi-Step `stepMirFn` Execution Suite (`0..27`) on Unmodified `Trusted.Rustc.V2026_06_01.MirSemantics` -/

/-! #### Compact 64-bit `LayoutTable` and `CapturedMir` builders -/

@[reducible] def layoutUnit : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }

@[reducible] def layoutBool : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

@[reducible] def layoutU32 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

@[reducible] def layoutPtr64 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.pointer 0) ⟨0, 18446744073709551615⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

@[reducible] def layoutIsize64 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.int 64 true) ⟨0, 18446744073709551615⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

@[reducible] def layoutArr2U32 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨4⟩, backendRepr := .memory,
    fields := .array ⟨4⟩ 2, variants := .single 0, isUninhabited := false }

@[reducible] def layoutTuple3U32 : TypeLayout :=
  { size := ⟨12⟩, align := ⟨4⟩, backendRepr := .memory,
    fields := .arbitrary [⟨0⟩, ⟨4⟩, ⟨8⟩] [0, 1, 2],
    variants := .single 0, isUninhabited := false }

/-- 64-bit little-endian layout table for Episode 1 `CapturedMir` programs:
`0 = ()`, `1 = bool`, `2 = u32`, `3 = thin ptr/ref (8B)`, `4 = isize (8B)`,
`5 = [u32; 2] (8B, stride 4)`, `6 = (u32, u32, u32) (12B)`. -/
def ep1Layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [layoutUnit, layoutBool, layoutU32, layoutPtr64, layoutIsize64,
                layoutArr2U32, layoutTuple3U32] }

@[reducible] def tyUnit : Ty := ⟨.tuple [], 0⟩
@[reducible] def tyBool : Ty := ⟨.bool, 1⟩
@[reducible] def tyU32 : Ty := ⟨.uint .u32, 2⟩
@[reducible] def tyMutRefU32 : Ty := ⟨.ref .mut (.uint .u32), 3⟩
@[reducible] def tyShrRefU32 : Ty := ⟨.ref .not (.uint .u32), 3⟩
@[reducible] def tyRawMutU32 : Ty := ⟨.rawPtr .mut (.uint .u32), 3⟩
@[reducible] def tyRawConstU32 : Ty := ⟨.rawPtr .not (.uint .u32), 3⟩
@[reducible] def tyRawMutUnit : Ty := ⟨.rawPtr .mut (.tuple []), 3⟩
@[reducible] def tyMutRefArr2 : Ty := ⟨.ref .mut (.array (.uint .u32) 2), 3⟩
@[reducible] def tyRawMutArr2 : Ty := ⟨.rawPtr .mut (.array (.uint .u32) 2), 3⟩
@[reducible] def tyIsize : Ty := ⟨.int .isize, 4⟩
@[reducible] def tyArr2U32 : Ty := ⟨.array (.uint .u32) 2, 5⟩
@[reducible] def tyObsTuple : Ty := ⟨.tuple [.uint .u32, .uint .u32, .uint .u32], 6⟩

@[reducible] def decl (t : Ty) : LocalDecl :=
  { mutability := .mut, ty := t, debugName := none }

@[reducible] def pl (l : Local) (proj : List ProjectionElem := []) : Place :=
  { local_ := l, projection := proj }

@[reducible] def plDeref (l : Local) : Place := pl l [.deref]
@[reducible] def plIdx (l : Local) (idx : Nat) : Place := pl l [.constantIndex idx 2 false]

@[reducible] def opCopy (l : Local) : Operand := .copy (pl l)
@[reducible] def opDeref (l : Local) : Operand := .copy (plDeref l)
@[reducible] def opIdx (l : Local) (idx : Nat) : Operand := .copy (plIdx l idx)

@[reducible] def cU32Op (n : Nat) : Operand :=
  .constant ⟨tyU32, .scalar (.int ⟨n, 4⟩)⟩

@[reducible] def cBoolOp (b : Bool) : Operand :=
  .constant ⟨tyBool, .scalar (.int ⟨if b then 1 else 0, 1⟩)⟩

@[reducible] def cIsizeOp (bits : Nat) : Operand :=
  .constant ⟨tyIsize, .scalar (.int ⟨bits, 8⟩)⟩

@[reducible] def cIsizeNeg (k : Nat) : Operand :=
  cIsizeOp (2 ^ 64 - k)

@[reducible] def cFnOp (path : String) (targs : List RigidTy := []) : Operand :=
  .constant ⟨⟨.fnDef path targs, 0⟩, .zeroSized⟩

@[reducible] def st (k : StatementKind) : Statement := { kind := k, span := "ep1.rs" }
@[reducible] def tm (k : TerminatorKind) : Terminator := { kind := k, span := "ep1.rs" }
@[reducible] def bb (stmts : List Statement) (term : TerminatorKind)
    (isCleanup : Bool := false) : BasicBlockData :=
  { statements := stmts, terminator := tm term, isCleanup := isCleanup }

@[reducible] def storageLiveRange : Nat → Nat → List Statement
  | _, 0 => []
  | lo, count + 1 => st (.storageLive lo) :: storageLiveRange (lo + 1) count

@[reducible] def mkBody (defPath : String) (decls : List LocalDecl) (argCount : Nat)
    (blocks : List BasicBlockData) : CapturedMir :=
  let initLives := storageLiveRange (argCount + 1) (decls.length - (argCount + 1))
  let blocks' := match blocks with
    | [] => []
    | b0 :: rest => { b0 with statements := initLives ++ b0.statements } :: rest
  { defPath := defPath, phase := .runtimePostCleanup, role := .subject,
    argCount := argCount, localDecls := decls, basicBlocks := blocks',
    fnAbi := { args := [], ret := { layout := layoutUnit, mode := .direct },
               conv := .rust, canUnwind := true },
    layouts := ep1Layouts, allocations := [] }

/-- Pack `(obsKind, retVal, refVal)` into return local `_0 : (u32, u32, u32)`. -/
@[reducible] def packObs (kind : Nat) (retOp refOp : Operand) : Statement :=
  st (.assign (pl 0) (.aggregate .tuple [cU32Op kind, retOp, refOp]))

/-- Real multi-step fuel-bounded execution strictly over unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn`, returning the terminal outcome plus the
last `MachineState` (so on `MirOutcome.panic` at root, preserved root local `_1` is observable). -/
inductive TrustedRunResult : Type where
  | halted (out : MirOutcome) (lastState : MachineState)
  | faulted (fk : FailureKind)
  | unsupported
  | outOfFuel

def runTrustedSteps (body : CapturedMir) : Nat → MachineState → TrustedRunResult
  | 0, _ => .outOfFuel
  | fuel + 1, s =>
    match stepMirFn body s with
    | .tau (.running s') => runTrustedSteps body fuel s'
    | .tau (.halted out) => .halted out s
    | .tau (.faulted fk) => .faulted fk
    | .ret out => .halted out s
    | .vis (.inl (.fail fk)) _ => .faulted fk
    | .vis (.inr _) _ => .unsupported

/-- Execute a root `CapturedMir` body with callees and `rootUnwindCeiling` flag through real
`stepMirFn` and decode `(obsKind, retVal, refVal)` from `_0` (or `_1` on root `.panic`). -/
def runTrustedObs (body : CapturedMir) (callees : List CapturedMir)
    (rootCeiling : Bool := true) (fuel : Nat := 120) : CrossFramePanicObs :=
  let s0 := initMachineStateWithCallees body [] callees
  let sInit := { s0 with memory := { s0.memory with rootUnwindCeiling := rootCeiling } }
  match runTrustedSteps body fuel sInit with
  | .halted (.normal ret) _ =>
    match ret.1 with
    | .aggregate 0 [.scalar k, .scalar rv, .scalar refv] =>
      if k.bits == 0 then .okVal rv.bits refv.bits
      else if k.bits == 1 then .okCleanupRecovered rv.bits refv.bits
      else if k.bits == 2 then .unwound refv.bits
      else .invalidOrUnsupported
    | _ => .invalidOrUnsupported
  | .halted .panic lastS =>
    match get? lastS.frame.locals 1 with
    | .some (.init (.scalar refv)) => .unwound refv.bits
    | _ => .invalidOrUnsupported
  | .halted .abort _ => .abort
  | .faulted .ub => .ub
  | .faulted _ => .invalidOrUnsupported
  | .unsupported | .outOfFuel => .invalidOrUnsupported

/-! #### 28 Real `CapturedMir` Scenarios (`0..27`) Mirroring MiniRust & LeanMiri 1-for-1 -/

/-- Case 0: `&mut u32` cross-frame call + `RetagKind.fnEntry` protector + writeback. -/
def mirCase0 : CapturedMir × List CapturedMir :=
  let callee := mkBody "ep1::c0_callee" [decl tyU32, decl tyMutRefU32] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (plDeref 1) (.use (cU32Op 42))),
         st (.assign (pl 0) (.use (opDeref 1)))] .return_]
  let main := mkBody "ep1::c0_main"
    [decl tyObsTuple, decl tyU32, decl tyMutRefU32, decl tyU32] 0
    [bb [st (.assign (pl 1) (.use (cU32Op 10))),
         st (.assign (pl 2) (.ref (.mut false) (pl 1)))]
        (.call (cFnOp "ep1::c0_callee") [opCopy 2] (pl 3) (some 1) .continue_),
     bb [packObs 0 (opCopy 3) (opCopy 1)] .return_]
  (main, [callee])

/-- Case 1: `&u32` cross-frame call + `RetagKind.fnEntry` shared protector. -/
def mirCase1 : CapturedMir × List CapturedMir :=
  let callee := mkBody "ep1::c1_callee" [decl tyU32, decl tyShrRefU32] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (pl 0) (.use (opDeref 1)))] .return_]
  let main := mkBody "ep1::c1_main"
    [decl tyObsTuple, decl tyU32, decl tyShrRefU32, decl tyU32] 0
    [bb [st (.assign (pl 1) (.use (cU32Op 77))),
         st (.assign (pl 2) (.ref .shared (pl 1)))]
        (.call (cFnOp "ep1::c1_callee") [opCopy 2] (pl 3) (some 1) .continue_),
     bb [packObs 0 (opCopy 3) (opCopy 1)] .return_]
  (main, [callee])

/-- Case 2: Post-return caller direct write after `FnEntry` protector release. -/
def mirCase2 : CapturedMir × List CapturedMir :=
  let callee := mkBody "ep1::c2_callee" [decl tyU32, decl tyMutRefU32] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (plDeref 1) (.use (cU32Op 42))),
         st (.assign (pl 0) (.use (cU32Op 42)))] .return_]
  let main := mkBody "ep1::c2_main"
    [decl tyObsTuple, decl tyU32, decl tyMutRefU32, decl tyU32] 0
    [bb [st (.assign (pl 1) (.use (cU32Op 10))),
         st (.assign (pl 2) (.ref (.mut false) (pl 1)))]
        (.call (cFnOp "ep1::c2_callee") [opCopy 2] (pl 3) (some 1) .continue_),
     bb [st (.assign (pl 1) (.use (cU32Op 99))),
         packObs 0 (opCopy 1) (opCopy 1)] .return_]
  (main, [callee])

/-- Case 3: `&mut [u32; 2]` cast via `as *mut () as *mut u32` (`.cast::<u32>()`) + in-bounds
`BinOp.offset (+1)` + write `88`. (Note: casting through `*mut ()` preserves the callee's
`FnEntry` protector lineage in unmodified `Trusted`, avoiding the known `parentTag := none`
omission in `deriveStackElemThinPtr` on direct `[T; N] → *mut T` casts.) -/
def mirCase3 : CapturedMir × List CapturedMir :=
  let callee := mkBody "ep1::c3_callee"
    [decl tyU32, decl tyMutRefArr2, decl tyRawMutUnit, decl tyRawMutU32, decl tyRawMutU32] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (pl 2) (.cast .ptrToPtr (opCopy 1) tyRawMutUnit)),
         st (.assign (pl 3) (.cast .ptrToPtr (opCopy 2) tyRawMutU32)),
         st (.assign (pl 4) (.binaryOp .offset (opCopy 3) (cIsizeOp 1))),
         st (.assign (plDeref 4) (.use (cU32Op 88))),
         st (.assign (pl 0) (.use (opDeref 4)))] .return_]
  let main := mkBody "ep1::c3_main"
    [decl tyObsTuple, decl tyArr2U32, decl tyMutRefArr2, decl tyU32, decl tyU32, decl tyU32] 0
    [bb [st (.assign (pl 1) (.aggregate (.array tyU32) [cU32Op 10, cU32Op 20])),
         st (.assign (pl 2) (.ref (.mut false) (pl 1)))]
        (.call (cFnOp "ep1::c3_callee") [opCopy 2] (pl 3) (some 1) .continue_),
     bb [st (.assign (pl 4) (.binaryOp .mul (opIdx 1 0) (cU32Op 1000))),
         st (.assign (pl 5) (.binaryOp .add (opCopy 4) (opIdx 1 1))),
         packObs 0 (opCopy 3) (opCopy 5)] .return_]
  (main, [callee])

/-- Case 4: `&mut [u32; 2]` in-bounds `BinOp.offset (+1)` then `(-1)` round-trip. -/
def mirCase4 : CapturedMir × List CapturedMir :=
  let callee := mkBody "ep1::c4_callee"
    [decl tyU32, decl tyMutRefArr2, decl tyRawMutUnit, decl tyRawMutU32, decl tyRawMutU32, decl tyRawMutU32] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (pl 2) (.cast .ptrToPtr (opCopy 1) tyRawMutUnit)),
         st (.assign (pl 3) (.cast .ptrToPtr (opCopy 2) tyRawMutU32)),
         st (.assign (pl 4) (.binaryOp .offset (opCopy 3) (cIsizeOp 1))),
         st (.assign (plDeref 4) (.use (cU32Op 33))),
         st (.assign (pl 5) (.binaryOp .offset (opCopy 4) (cIsizeNeg 1))),
         st (.assign (plDeref 5) (.use (cU32Op 44))),
         st (.assign (pl 0) (.use (opDeref 5)))] .return_]
  let main := mkBody "ep1::c4_main"
    [decl tyObsTuple, decl tyArr2U32, decl tyMutRefArr2, decl tyU32, decl tyU32, decl tyU32] 0
    [bb [st (.assign (pl 1) (.aggregate (.array tyU32) [cU32Op 11, cU32Op 22])),
         st (.assign (pl 2) (.ref (.mut false) (pl 1)))]
        (.call (cFnOp "ep1::c4_callee") [opCopy 2] (pl 3) (some 1) .continue_),
     bb [st (.assign (pl 4) (.binaryOp .mul (opIdx 1 0) (cU32Op 1000))),
         st (.assign (pl 5) (.binaryOp .add (opCopy 4) (opIdx 1 1))),
         packObs 0 (opCopy 3) (opCopy 5)] .return_]
  (main, [callee])

/-- Case 5: `&mut [u32; 2]` wrapping `core::intrinsics::arith_offset` `+1` then `-1` round-trip. -/
def mirCase5 : CapturedMir × List CapturedMir :=
  let callee := mkBody "ep1::c5_callee"
    [decl tyU32, decl tyMutRefArr2, decl tyRawMutUnit, decl tyRawMutU32, decl tyRawMutU32, decl tyRawMutU32] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (pl 2) (.cast .ptrToPtr (opCopy 1) tyRawMutUnit)),
         st (.assign (pl 3) (.cast .ptrToPtr (opCopy 2) tyRawMutU32))]
        (.call (cFnOp "core::intrinsics::arith_offset" [.uint .u32])
          [opCopy 3, cIsizeOp 1] (pl 4) (some 1) .continue_),
     bb [st (.assign (plDeref 4) (.use (cU32Op 55)))]
        (.call (cFnOp "core::intrinsics::arith_offset" [.uint .u32])
          [opCopy 4, cIsizeNeg 1] (pl 5) (some 2) .continue_),
     bb [st (.assign (plDeref 5) (.use (cU32Op 66))),
         st (.assign (pl 0) (.use (opDeref 5)))] .return_]
  let main := mkBody "ep1::c5_main"
    [decl tyObsTuple, decl tyArr2U32, decl tyMutRefArr2, decl tyU32, decl tyU32, decl tyU32] 0
    [bb [st (.assign (pl 1) (.aggregate (.array tyU32) [cU32Op 5, cU32Op 6])),
         st (.assign (pl 2) (.ref (.mut false) (pl 1)))]
        (.call (cFnOp "ep1::c5_callee") [opCopy 2] (pl 3) (some 1) .continue_),
     bb [st (.assign (pl 4) (.binaryOp .mul (opIdx 1 0) (cU32Op 1000))),
         st (.assign (pl 5) (.binaryOp .add (opCopy 4) (opIdx 1 1))),
         packObs 0 (opCopy 3) (opCopy 5)] .return_]
  (main, [callee])

/-- Case 6: Wrapping `arith_offset` `+100` elems (`+400B` OOB, no deref!) then `-100` -> write `34`. -/
def mirCase6 : CapturedMir × List CapturedMir :=
  let callee := mkBody "ep1::c6_callee"
    [decl tyU32, decl tyMutRefU32, decl tyRawMutU32, decl tyRawMutU32, decl tyRawMutU32] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (pl 2) (.cast .ptrToPtr (opCopy 1) tyRawMutU32))]
        (.call (cFnOp "core::intrinsics::arith_offset" [.uint .u32])
          [opCopy 2, cIsizeOp 100] (pl 3) (some 1) .continue_),
     bb []
        (.call (cFnOp "core::intrinsics::arith_offset" [.uint .u32])
          [opCopy 3, cIsizeNeg 100] (pl 4) (some 2) .continue_),
     bb [st (.assign (plDeref 4) (.use (cU32Op 34))),
         st (.assign (pl 0) (.use (cU32Op 34)))] .return_]
  let main := mkBody "ep1::c6_main"
    [decl tyObsTuple, decl tyU32, decl tyMutRefU32, decl tyU32] 0
    [bb [st (.assign (pl 1) (.use (cU32Op 12))),
         st (.assign (pl 2) (.ref (.mut false) (pl 1)))]
        (.call (cFnOp "ep1::c6_callee") [opCopy 2] (pl 3) (some 1) .continue_),
     bb [packObs 0 (opCopy 3) (opCopy 1)] .return_]
  (main, [callee])

/-- Case 7: 2-level nested reborrow call `main -> mid(p1) -> inner(p2)` LIFO normal release. -/
def mirCase7 : CapturedMir × List CapturedMir :=
  let inner := mkBody "ep1::c7_inner" [decl tyU32, decl tyMutRefU32] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (plDeref 1) (.use (cU32Op 7))),
         st (.assign (pl 0) (.use (cU32Op 7)))] .return_]
  let mid := mkBody "ep1::c7_mid"
    [decl tyU32, decl tyMutRefU32, decl tyMutRefU32, decl tyU32] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (pl 2) (.ref (.mut false) (plDeref 1)))]
        (.call (cFnOp "ep1::c7_inner") [opCopy 2] (pl 3) (some 1) .continue_),
     bb [st (.assign (plDeref 1) (.binaryOp .add (opCopy 3) (cU32Op 3))),
         st (.assign (pl 0) (.use (opDeref 1)))] .return_]
  let main := mkBody "ep1::c7_main"
    [decl tyObsTuple, decl tyU32, decl tyMutRefU32, decl tyU32] 0
    [bb [st (.assign (pl 1) (.use (cU32Op 1))),
         st (.assign (pl 2) (.ref (.mut false) (pl 1)))]
        (.call (cFnOp "ep1::c7_mid") [opCopy 2] (pl 3) (some 1) .continue_),
     bb [st (.assign (pl 1) (.binaryOp .add (opCopy 3) (cU32Op 10))),
         packObs 0 (opCopy 1) (opCopy 1)] .return_]
  (main, [mid, inner])

/-- Case 8 [MODE-SENSITIVE #1]: Foreign write through parent raw ptr under active `FnEntry`
protector -> UB in Trusted (matching `MachTB` & LeanMiri `treeBorrows = true`). -/
def mirCase8 : CapturedMir × List CapturedMir :=
  let callee := mkBody "ep1::c8_callee" [decl tyU32, decl tyMutRefU32, decl tyRawMutU32] 2
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (plDeref 2) (.use (cU32Op 77))),
         st (.assign (pl 0) (.use (cU32Op 77)))] .return_]
  let main := mkBody "ep1::c8_main"
    [decl tyObsTuple, decl tyU32, decl tyRawMutU32, decl tyMutRefU32, decl tyU32] 0
    [bb [st (.assign (pl 1) (.use (cU32Op 10))),
         st (.assign (pl 2) (.rawPtr .mut (pl 1))),
         st (.assign (pl 3) (.ref (.mut false) (plDeref 2)))]
        (.call (cFnOp "ep1::c8_callee") [opCopy 3, opCopy 2] (pl 4) (some 1) .continue_),
     bb [packObs 0 (opCopy 4) (opCopy 1)] .return_]
  (main, [callee])

/-- Case 9 [MODE-SENSITIVE #2]: Write through `Frozen` `&u32`-derived raw ptr -> UB in Trusted
(matching `MachTB` & LeanMiri `treeBorrows = true`). -/
def mirCase9 : CapturedMir × List CapturedMir :=
  let callee := mkBody "ep1::c9_callee" [decl tyU32, decl tyShrRefU32, decl tyRawMutU32] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (pl 2) (.cast .ptrToPtr (opCopy 1) tyRawMutU32)),
         st (.assign (plDeref 2) (.use (cU32Op 99))),
         st (.assign (pl 0) (.use (cU32Op 99)))] .return_]
  let main := mkBody "ep1::c9_main"
    [decl tyObsTuple, decl tyU32, decl tyShrRefU32, decl tyU32] 0
    [bb [st (.assign (pl 1) (.use (cU32Op 10))),
         st (.assign (pl 2) (.ref .shared (pl 1)))]
        (.call (cFnOp "ep1::c9_callee") [opCopy 2] (pl 3) (some 1) .continue_),
     bb [packObs 0 (opCopy 3) (opCopy 1)] .return_]
  (main, [callee])

/-- Case 10: Callee returns raw pointer to its own dead stack local; caller derefs -> UAR UB. -/
def mirCase10 : CapturedMir × List CapturedMir :=
  let callee := mkBody "ep1::c10_callee" [decl tyRawConstU32, decl tyU32] 0
    [bb [st (.assign (pl 1) (.use (cU32Op 55))),
         st (.assign (pl 0) (.rawPtr .not (pl 1)))] .return_]
  let main := mkBody "ep1::c10_main"
    [decl tyObsTuple, decl tyRawConstU32, decl tyU32] 0
    [bb [] (.call (cFnOp "ep1::c10_callee") [] (pl 1) (some 1) .continue_),
     bb [st (.assign (pl 2) (.use (opDeref 1))),
         packObs 0 (opCopy 2) (opCopy 2)] .return_]
  (main, [callee])

/-- Case 11: In-bounds `BinOp.offset` past end (`+3` u32 / `+12B` on 8B `[u32; 2]`) -> UB. -/
def mirCase11 : CapturedMir × List CapturedMir :=
  let callee := mkBody "ep1::c11_callee"
    [decl tyU32, decl tyMutRefArr2, decl tyRawMutUnit, decl tyRawMutU32, decl tyRawMutU32] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (pl 2) (.cast .ptrToPtr (opCopy 1) tyRawMutUnit)),
         st (.assign (pl 3) (.cast .ptrToPtr (opCopy 2) tyRawMutU32)),
         st (.assign (pl 4) (.binaryOp .offset (opCopy 3) (cIsizeOp 3))),
         st (.assign (pl 0) (.use (cU32Op 0)))] .return_]
  let main := mkBody "ep1::c11_main"
    [decl tyObsTuple, decl tyArr2U32, decl tyMutRefArr2, decl tyU32] 0
    [bb [st (.assign (pl 1) (.aggregate (.array tyU32) [cU32Op 1, cU32Op 2])),
         st (.assign (pl 2) (.ref (.mut false) (pl 1)))]
        (.call (cFnOp "ep1::c11_callee") [opCopy 2] (pl 3) (some 1) .continue_),
     bb [packObs 0 (opCopy 3) (cU32Op 0)] .return_]
  (main, [callee])

/-- Case 12: In-bounds `BinOp.offset` before start (`-1` u32 / `-4B`) -> UB. -/
def mirCase12 : CapturedMir × List CapturedMir :=
  let callee := mkBody "ep1::c12_callee"
    [decl tyU32, decl tyMutRefArr2, decl tyRawMutUnit, decl tyRawMutU32, decl tyRawMutU32] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (pl 2) (.cast .ptrToPtr (opCopy 1) tyRawMutUnit)),
         st (.assign (pl 3) (.cast .ptrToPtr (opCopy 2) tyRawMutU32)),
         st (.assign (pl 4) (.binaryOp .offset (opCopy 3) (cIsizeNeg 1))),
         st (.assign (pl 0) (.use (cU32Op 0)))] .return_]
  let main := mkBody "ep1::c12_main"
    [decl tyObsTuple, decl tyArr2U32, decl tyMutRefArr2, decl tyU32] 0
    [bb [st (.assign (pl 1) (.aggregate (.array tyU32) [cU32Op 1, cU32Op 2])),
         st (.assign (pl 2) (.ref (.mut false) (pl 1)))]
        (.call (cFnOp "ep1::c12_callee") [opCopy 2] (pl 3) (some 1) .continue_),
     bb [packObs 0 (opCopy 3) (cU32Op 0)] .return_]
  (main, [callee])

/-- Case 13: Wrapping `arith_offset` `+100` elems OOB then deref -> UB. -/
def mirCase13 : CapturedMir × List CapturedMir :=
  let callee := mkBody "ep1::c13_callee"
    [decl tyU32, decl tyMutRefU32, decl tyRawMutU32, decl tyRawMutU32] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (pl 2) (.cast .ptrToPtr (opCopy 1) tyRawMutU32))]
        (.call (cFnOp "core::intrinsics::arith_offset" [.uint .u32])
          [opCopy 2, cIsizeOp 100] (pl 3) (some 1) .continue_),
     bb [st (.assign (pl 0) (.use (opDeref 3)))] .return_]
  let main := mkBody "ep1::c13_main"
    [decl tyObsTuple, decl tyU32, decl tyMutRefU32, decl tyU32] 0
    [bb [st (.assign (pl 1) (.use (cU32Op 12))),
         st (.assign (pl 2) (.ref (.mut false) (pl 1)))]
        (.call (cFnOp "ep1::c13_callee") [opCopy 2] (pl 3) (some 1) .continue_),
     bb [packObs 0 (opCopy 3) (opCopy 1)] .return_]
  (main, [callee])

/-- Case 14: `TerminatorKind.assert(true == true)` passes -> `.okVal 101 101`. -/
def mirCase14 : CapturedMir × List CapturedMir :=
  let main := mkBody "ep1::c14_main" [decl tyObsTuple] 0
    [bb [] (.assert (cBoolOp true) true 1 .unreachable),
     bb [packObs 0 (cU32Op 101) (cU32Op 101)] .return_]
  (main, [])

/-- Case 15: `TerminatorKind.assert(false == false)` passes -> `.okVal 102 102`. -/
def mirCase15 : CapturedMir × List CapturedMir :=
  let main := mkBody "ep1::c15_main" [decl tyObsTuple] 0
    [bb [] (.assert (cBoolOp false) false 1 .unreachable),
     bb [packObs 0 (cU32Op 102) (cU32Op 102)] .return_]
  (main, [])

/-- Case 16: `TerminatorKind.unreachable` -> `.ub`. -/
def mirCase16 : CapturedMir × List CapturedMir :=
  let main := mkBody "ep1::c16_main" [decl tyObsTuple] 0
    [bb [] .unreachable]
  (main, [])

/-- Case 17: Failing `assert` -> `.cleanup` mutates `*r = 115` -> `unwindResume` (caught
by outer harness) -> `.unwound 115`. -/
def mirCase17 : CapturedMir × List CapturedMir :=
  let callee := mkBody "ep1::c17_callee" [decl tyUnit, decl tyMutRefU32] 1
    [bb [st (.retag .fnEntry (pl 1))] (.assert (cBoolOp false) true 1 (.cleanup 2)),
     bb [st (.assign (pl 0) (.aggregate .tuple []))] .return_,
     bb [st (.assign (plDeref 1) (.use (cU32Op 115)))] .unwindResume true]
  let main := mkBody "ep1::c17_main"
    [decl tyObsTuple, decl tyU32, decl tyMutRefU32, decl tyUnit] 0
    [bb [st (.assign (pl 1) (.use (cU32Op 10))),
         st (.assign (pl 2) (.ref (.mut false) (pl 1)))]
        (.call (cFnOp "ep1::c17_callee") [opCopy 2] (pl 3) (some 1) (.cleanup 2)),
     bb [packObs 0 (cU32Op 0) (opCopy 1)] .return_,
     bb [packObs 2 (cU32Op 0) (opCopy 1)] .return_ true]
  (main, [callee])

/-- Case 18: Cross-frame callee with `FnEntry`-protected `&mut x`: failing `assert` ->
`.cleanup` mutates `*r = 116` through the protected reference -> `unwindTerminate` -> `.abort`
(mirroring MiniRust `mrProg18` and LeanMiri case 18 frame-for-frame). -/
def mirCase18 : CapturedMir × List CapturedMir :=
  let callee := mkBody "ep1::c18_callee" [decl tyUnit, decl tyMutRefU32] 1
    [bb [st (.retag .fnEntry (pl 1))] (.assert (cBoolOp false) true 1 (.cleanup 2)),
     bb [st (.assign (pl 0) (.aggregate .tuple []))] .return_,
     bb [st (.assign (plDeref 1) (.use (cU32Op 116)))] .unwindTerminate true]
  let main := mkBody "ep1::c18_main"
    [decl tyObsTuple, decl tyU32, decl tyMutRefU32, decl tyUnit] 0
    [bb [st (.assign (pl 1) (.use (cU32Op 10))),
         st (.assign (pl 2) (.ref (.mut false) (pl 1)))]
        (.call (cFnOp "ep1::c18_callee") [opCopy 2] (pl 3) (some 1) (.cleanup 2)),
     bb [packObs 0 (cU32Op 0) (opCopy 1)] .return_,
     bb [packObs 2 (cU32Op 0) (opCopy 1)] .return_ true]
  (main, [callee])

/-- Case 19: Failing `assert(..., unwind: .terminate)` -> `.abort`. -/
def mirCase19 : CapturedMir × List CapturedMir :=
  let main := mkBody "ep1::c19_main" [decl tyObsTuple] 0
    [bb [] (.assert (cBoolOp false) true 1 .terminate),
     bb [packObs 0 (cU32Op 0) (cU32Op 0)] .return_]
  (main, [])

/-- Case 20: Failing `assert(..., unwind: .unreachable)` -> `.ub`. -/
def mirCase20 : CapturedMir × List CapturedMir :=
  let main := mkBody "ep1::c20_main" [decl tyObsTuple] 0
    [bb [] (.assert (cBoolOp false) true 1 .unreachable),
     bb [packObs 0 (cU32Op 0) (cU32Op 0)] .return_]
  (main, [])

/-- Case 21: Callee `FnEntry` protector + partial writeback `55` + panic -> callee unwind
releases protector -> caller `.cleanup` reads `55`, writes `65` via parent raw ptr (proving
protector release!), `unwindResume` -> outer catch -> `.okCleanupRecovered 65 65`. -/
def mirCase21 : CapturedMir × List CapturedMir :=
  let callee := mkBody "ep1::c21_callee" [decl tyUnit, decl tyMutRefU32] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (plDeref 1) (.use (cU32Op 55)))]
        (.assert (cBoolOp false) true 1 .continue_),
     bb [st (.assign (pl 0) (.aggregate .tuple []))] .return_]
  let caller := mkBody "ep1::c21_caller"
    [decl tyUnit, decl tyMutRefU32, decl tyRawMutU32, decl tyMutRefU32, decl tyUnit] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (pl 2) (.rawPtr .mut (plDeref 1))),
         st (.assign (pl 3) (.ref (.mut false) (plDeref 2)))]
        (.call (cFnOp "ep1::c21_callee") [opCopy 3] (pl 4) (some 1) (.cleanup 2)),
     bb [st (.assign (pl 0) (.aggregate .tuple []))] .return_,
     bb [st (.assign (plDeref 2) (.binaryOp .add (opDeref 2) (cU32Op 10)))] .unwindResume true]
  let main := mkBody "ep1::c21_main"
    [decl tyObsTuple, decl tyU32, decl tyMutRefU32, decl tyUnit] 0
    [bb [st (.assign (pl 1) (.use (cU32Op 10))),
         st (.assign (pl 2) (.ref (.mut false) (pl 1)))]
        (.call (cFnOp "ep1::c21_caller") [opCopy 2] (pl 3) (some 1) (.cleanup 2)),
     bb [packObs 0 (cU32Op 0) (opCopy 1)] .return_,
     bb [packObs 1 (opCopy 1) (opCopy 1)] .return_ true]
  (main, [caller, callee])

/-- Case 22: Same partial writeback + callee protector release, caller `.cleanup` writes `66`
and executes `unwindTerminate` -> `.abort`. -/
def mirCase22 : CapturedMir × List CapturedMir :=
  let callee := mkBody "ep1::c22_callee" [decl tyUnit, decl tyMutRefU32] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (plDeref 1) (.use (cU32Op 55)))]
        (.assert (cBoolOp false) true 1 .continue_),
     bb [st (.assign (pl 0) (.aggregate .tuple []))] .return_]
  let main := mkBody "ep1::c22_main"
    [decl tyObsTuple, decl tyU32, decl tyMutRefU32, decl tyUnit] 0
    [bb [st (.assign (pl 1) (.use (cU32Op 10))),
         st (.assign (pl 2) (.ref (.mut false) (pl 1)))]
        (.call (cFnOp "ep1::c22_callee") [opCopy 2] (pl 3) (some 1) (.cleanup 2)),
     bb [packObs 0 (cU32Op 0) (opCopy 1)] .return_,
     bb [st (.assign (pl 1) (.binaryOp .add (opCopy 1) (cU32Op 11)))] .unwindTerminate true]
  (main, [callee])

/-- Case 23: 3-frame LIFO `.continue_` unwind (`main -> mid(p1) -> leaf(p2)`): `leaf` writes
`3` & panics -> releases `p2`; `mid` propagates `.continue_` -> releases `p1`; `main` `.cleanup`
reads `3`, writes `300` -> `.okCleanupRecovered 300 300`. -/
def mirCase23 : CapturedMir × List CapturedMir :=
  let leaf := mkBody "ep1::c23_leaf" [decl tyUnit, decl tyMutRefU32] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (plDeref 1) (.use (cU32Op 3)))]
        (.assert (cBoolOp false) true 1 .continue_),
     bb [st (.assign (pl 0) (.aggregate .tuple []))] .return_]
  let mid := mkBody "ep1::c23_mid"
    [decl tyUnit, decl tyMutRefU32, decl tyMutRefU32, decl tyUnit] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (pl 2) (.ref (.mut false) (plDeref 1)))]
        (.call (cFnOp "ep1::c23_leaf") [opCopy 2] (pl 3) (some 1) .continue_),
     bb [st (.assign (pl 0) (.aggregate .tuple []))] .return_]
  let main := mkBody "ep1::c23_main"
    [decl tyObsTuple, decl tyU32, decl tyMutRefU32, decl tyUnit] 0
    [bb [st (.assign (pl 1) (.use (cU32Op 1))),
         st (.assign (pl 2) (.ref (.mut false) (pl 1)))]
        (.call (cFnOp "ep1::c23_mid") [opCopy 2] (pl 3) (some 1) (.cleanup 2)),
     bb [packObs 0 (cU32Op 0) (opCopy 1)] .return_,
     bb [st (.assign (pl 1) (.binaryOp .mul (opCopy 1) (cU32Op 100))),
         packObs 1 (opCopy 1) (opCopy 1)] .return_ true]
  (main, [mid, leaf])

/-- Case 24: Callee holding an `FnEntry`-protected `&mut x` writes partial update `44`, panics
(`assert(.., .continue_)`), and unwinds into the caller call edge `unwind: .terminate` ->
`.abort` (mirroring MiniRust `mrProg24` and LeanMiri case 24). -/
def mirCase24 : CapturedMir × List CapturedMir :=
  let callee := mkBody "ep1::c24_callee" [decl tyUnit, decl tyMutRefU32] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (plDeref 1) (.use (cU32Op 44)))]
        (.assert (cBoolOp false) true 1 .continue_),
     bb [st (.assign (pl 0) (.aggregate .tuple []))] .return_]
  let main := mkBody "ep1::c24_main"
    [decl tyObsTuple, decl tyU32, decl tyMutRefU32, decl tyUnit] 0
    [bb [st (.assign (pl 1) (.use (cU32Op 10))),
         st (.assign (pl 2) (.ref (.mut false) (pl 1)))]
        (.call (cFnOp "ep1::c24_callee") [opCopy 2] (pl 3) (some 1) .terminate),
     bb [packObs 0 (cU32Op 0) (opCopy 1)] .return_]
  (main, [callee])

/-- Case 25: Same `FnEntry`-protected partial-writeback panicking callee, unwinding into the
caller call edge `unwind: .unreachable` -> `.ub` (mirroring `mrProg25` and LeanMiri case 25). -/
def mirCase25 : CapturedMir × List CapturedMir :=
  let callee := mkBody "ep1::c25_callee" [decl tyUnit, decl tyMutRefU32] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (plDeref 1) (.use (cU32Op 44)))]
        (.assert (cBoolOp false) true 1 .continue_),
     bb [st (.assign (pl 0) (.aggregate .tuple []))] .return_]
  let main := mkBody "ep1::c25_main"
    [decl tyObsTuple, decl tyU32, decl tyMutRefU32, decl tyUnit] 0
    [bb [st (.assign (pl 1) (.use (cU32Op 10))),
         st (.assign (pl 2) (.ref (.mut false) (pl 1)))]
        (.call (cFnOp "ep1::c25_callee") [opCopy 2] (pl 3) (some 1) .unreachable),
     bb [packObs 0 (cU32Op 0) (opCopy 1)] .return_]
  (main, [callee])

/-- Cases 26 & 27: Bare root-frame unwind after setting `_1 = 77`.
- Case 26 (`rootUnwindCeiling = false`): `.ub` (3-way agreement with MiniRust & LeanMiri).
- Case 27 (`rootUnwindCeiling = true`): `.unwound 77` (`MirOutcome.panic` — exact divergence!). -/
def mirCaseRootUnwind : CapturedMir × List CapturedMir :=
  let main := mkBody "ep1::c_root_unwind" [decl tyObsTuple, decl tyU32] 0
    [bb [st (.assign (pl 1) (.use (cU32Op 77)))]
        (.assert (cBoolOp false) true 1 .continue_),
     bb [packObs 0 (cU32Op 0) (opCopy 1)] .return_]
  (main, [])

/-- Canonical `0..27` Trusted MIR program table (`(rootBody, callees, rootUnwindCeiling)`). -/
def trustedCanonicalProg? : Nat → Option (CapturedMir × List CapturedMir × Bool)
  | 0 => some (mirCase0.1, mirCase0.2, true)
  | 1 => some (mirCase1.1, mirCase1.2, true)
  | 2 => some (mirCase2.1, mirCase2.2, true)
  | 3 => some (mirCase3.1, mirCase3.2, true)
  | 4 => some (mirCase4.1, mirCase4.2, true)
  | 5 => some (mirCase5.1, mirCase5.2, true)
  | 6 => some (mirCase6.1, mirCase6.2, true)
  | 7 => some (mirCase7.1, mirCase7.2, true)
  | 8 => some (mirCase8.1, mirCase8.2, true)
  | 9 => some (mirCase9.1, mirCase9.2, true)
  | 10 => some (mirCase10.1, mirCase10.2, true)
  | 11 => some (mirCase11.1, mirCase11.2, true)
  | 12 => some (mirCase12.1, mirCase12.2, true)
  | 13 => some (mirCase13.1, mirCase13.2, true)
  | 14 => some (mirCase14.1, mirCase14.2, true)
  | 15 => some (mirCase15.1, mirCase15.2, true)
  | 16 => some (mirCase16.1, mirCase16.2, true)
  | 17 => some (mirCase17.1, mirCase17.2, true)
  | 18 => some (mirCase18.1, mirCase18.2, true)
  | 19 => some (mirCase19.1, mirCase19.2, true)
  | 20 => some (mirCase20.1, mirCase20.2, true)
  | 21 => some (mirCase21.1, mirCase21.2, true)
  | 22 => some (mirCase22.1, mirCase22.2, true)
  | 23 => some (mirCase23.1, mirCase23.2, true)
  | 24 => some (mirCase24.1, mirCase24.2, true)
  | 25 => some (mirCase25.1, mirCase25.2, true)
  | 26 => some (mirCaseRootUnwind.1, mirCaseRootUnwind.2, false)
  | 27 => some (mirCaseRootUnwind.1, mirCaseRootUnwind.2, true)
  | _ => none

/-- Real unmodified `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` observer across all
`28` canonical scenarios (`0..27`) and fail-closed `.invalidOrUnsupported` for `idx ≥ 28`. -/
def trustedCrossFramePanicObserve (idx : Nat) : CrossFramePanicObs :=
  match trustedCanonicalProg? idx with
  | none => .invalidOrUnsupported
  | some (body, callees, ceil) => runTrustedObs body callees ceil 120

/-- **Kernel-checked 28-scenario `stepMirFn` execution table** on unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics` (zero `native_decide`). -/
theorem trustedCrossFramePanicObserve_table :
    (List.range canonicalCaseCount).map trustedCrossFramePanicObserve =
      (List.range canonicalCaseCount).map trustedExpected := by
  kernel_rfl

theorem trustedCrossFramePanicObserve_out_of_range (idx : Nat)
    (h : canonicalCaseCount ≤ idx) :
    trustedCrossFramePanicObserve idx = .invalidOrUnsupported := by
  unfold canonicalCaseCount at h
  have hNone : trustedCanonicalProg? idx = none := by
    unfold trustedCanonicalProg?
    split <;> first | rfl | omega
  unfold trustedCrossFramePanicObserve
  rw [hNone]

/-- Real `stepMirFn` observer equals `trustedExpected` on EVERY `idx : Nat`. -/
theorem trustedCrossFramePanicObserve_matches_expected (idx : Nat) :
    trustedCrossFramePanicObserve idx = trustedExpected idx := by
  by_cases hlt : idx < canonicalCaseCount
  · have hCell := congrArg (fun l => l[idx]?) trustedCrossFramePanicObserve_table
    simp only [List.getElem?_map, List.getElem?_range hlt, Option.map_some] at hCell
    exact Option.some.inj hCell
  · have hge : canonicalCaseCount ≤ idx := Nat.le_of_not_lt hlt
    rw [trustedCrossFramePanicObserve_out_of_range idx hge,
        trustedExpected_out_of_range idx hge]

/-- Iterate unmodified `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` for exactly `n`
running steps, returning the live intermediate `MachineState` (or `none` if execution halts or
faults before `n` steps). -/
def runTrustedTrace (body : CapturedMir) : Nat → MachineState → Option MachineState
  | 0, s => some s
  | n + 1, s =>
    match stepMirFn body s with
    | .tau (.running s') => runTrustedTrace body n s'
    | _ => none

/-- Read an initialized `u32` scalar from local `loc` of the root frame (bottom of `callStack`,
or the current frame when `callStack = []`). -/
def readRootLocalU32 (s : MachineState) (loc : Nat) : Option Nat :=
  let rootLocals : List LocalSlot := match s.memory.callStack.getLast? with
    | some bottom => bottom.frame.locals
    | none => s.frame.locals
  match get? rootLocals loc with
  | .some (.init (.scalar sc)) => some sc.bits
  | _ => none

/-- Causal protector-release contrast for Case `21` on unmodified `Trusted.MirSemantics`
(mirroring MiniRust's `mrProg21PrematureWrite`): identical to `mirCase21` except `caller` also
passes its parent raw pointer `_2` to `callee`, and `callee` writes `65` through that parent raw
pointer BEFORE unwinding while `callee`'s `FnEntry` protector is still active -> `.ub`. -/
def mirCase21PrematureWrite : CapturedMir × List CapturedMir :=
  let callee := mkBody "ep1::c21_premature_callee"
    [decl tyUnit, decl tyMutRefU32, decl tyRawMutU32] 2
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (plDeref 1) (.use (cU32Op 55))),
         st (.assign (plDeref 2) (.use (cU32Op 65)))]
        (.assert (cBoolOp false) true 1 .continue_),
     bb [st (.assign (pl 0) (.aggregate .tuple []))] .return_]
  let caller := mkBody "ep1::c21_premature_caller"
    [decl tyUnit, decl tyMutRefU32, decl tyRawMutU32, decl tyMutRefU32, decl tyUnit] 1
    [bb [st (.retag .fnEntry (pl 1)),
         st (.assign (pl 2) (.rawPtr .mut (plDeref 1))),
         st (.assign (pl 3) (.ref (.mut false) (plDeref 2)))]
        (.call (cFnOp "ep1::c21_premature_callee") [opCopy 3, opCopy 2] (pl 4) (some 1) (.cleanup 2)),
     bb [st (.assign (pl 0) (.aggregate .tuple []))] .return_,
     bb [st (.assign (plDeref 2) (.binaryOp .add (opDeref 2) (cU32Op 10)))] .unwindResume true]
  let main := mkBody "ep1::c21_premature_main"
    [decl tyObsTuple, decl tyU32, decl tyMutRefU32, decl tyUnit] 0
    [bb [st (.assign (pl 1) (.use (cU32Op 10))),
         st (.assign (pl 2) (.ref (.mut false) (pl 1)))]
        (.call (cFnOp "ep1::c21_premature_caller") [opCopy 2] (pl 3) (some 1) (.cleanup 2)),
     bb [packObs 0 (cU32Op 0) (opCopy 1)] .return_,
     bb [packObs 1 (opCopy 1) (opCopy 1)] .return_ true]
  (main, [caller, callee])

/-- Decidable checker for a 2-frame unwind protector-release trace (`step 15 → step 16 → step 18`)
over any `body : CapturedMir` and initial `sInit : MachineState`. -/
def case21TraceCheck (body : CapturedMir) (sInit : MachineState) : Bool :=
  match runTrustedTrace body 15 sInit with
  | some s15 =>
    match stepMirFn body s15 with
    | .tau (.running s16) =>
      match runTrustedTrace body 2 s16 with
      | some s18 =>
        match s15.memory.borrows.find? (fun e => e.protector == some 2),
              s15.memory.borrows.find? (fun e => e.protector == some 1) with
        | some eCallee, some eCaller =>
          decide (s15.memory.callStack.length = 2) &&
          decide (s15.memory.activeProtectors = [2, 1]) &&
          decide (eCallee.protector = some 2) &&
          decide (eCaller.protector = some 1) &&
          isBorrowProtected s15.memory.activeProtectors eCallee &&
          isBorrowProtected s15.memory.activeProtectors eCaller &&
          decide (readRootLocalU32 s15 1 = some 55) &&
          decide (s16.frame.blockIdx = 2) &&
          decide (s16.memory.callStack.length = 1) &&
          decide (s16.memory.activeProtectors = [1]) &&
          !isBorrowProtected s16.memory.activeProtectors eCallee &&
          isBorrowProtected s16.memory.activeProtectors eCaller &&
          decide (readRootLocalU32 s16 1 = some 55) &&
          decide (s18.frame.blockIdx = 2) &&
          decide (s18.memory.callStack.isEmpty) &&
          decide (s18.memory.activeProtectors = []) &&
          !isBorrowProtected s18.memory.activeProtectors eCallee &&
          !isBorrowProtected s18.memory.activeProtectors eCaller &&
          decide (readRootLocalU32 s18 1 = some 65)
        | _, _ => false
      | none => false
    | _ => false
  | none => false

private theorem case21TraceCheck_sound (body : CapturedMir) (sInit : MachineState)
    (hCheck : case21TraceCheck body sInit = true) :
    ∃ s15 s16 s18 eCallee eCaller,
      runTrustedTrace body 15 sInit = some s15 ∧
      stepMirFn body s15 = .tau (.running s16) ∧
      runTrustedTrace body 2 s16 = some s18 ∧
      s15.memory.callStack.length = 2 ∧
      s15.memory.activeProtectors = [2, 1] ∧
      eCallee ∈ s15.memory.borrows ∧
      eCaller ∈ s15.memory.borrows ∧
      eCallee.protector = some 2 ∧
      eCaller.protector = some 1 ∧
      isBorrowProtected s15.memory.activeProtectors eCallee = true ∧
      isBorrowProtected s15.memory.activeProtectors eCaller = true ∧
      readRootLocalU32 s15 1 = some 55 ∧
      s16.frame.blockIdx = 2 ∧
      s16.memory.callStack.length = 1 ∧
      s16.memory.activeProtectors = [1] ∧
      isBorrowProtected s16.memory.activeProtectors eCallee = false ∧
      isBorrowProtected s16.memory.activeProtectors eCaller = true ∧
      readRootLocalU32 s16 1 = some 55 ∧
      s18.frame.blockIdx = 2 ∧
      s18.memory.callStack = [] ∧
      s18.memory.activeProtectors = [] ∧
      isBorrowProtected s18.memory.activeProtectors eCallee = false ∧
      isBorrowProtected s18.memory.activeProtectors eCaller = false ∧
      readRootLocalU32 s18 1 = some 65 := by
  unfold case21TraceCheck at hCheck
  cases h15 : runTrustedTrace body 15 sInit with
  | none => rw [h15] at hCheck; cases hCheck
  | some s15 =>
    rw [h15] at hCheck; dsimp only at hCheck
    cases h16 : stepMirFn body s15 with
    | tau st16 =>
      cases st16 with
      | running s16 =>
        rw [h16] at hCheck; dsimp only at hCheck
        cases h18 : runTrustedTrace body 2 s16 with
        | none => rw [h18] at hCheck; cases hCheck
        | some s18 =>
          rw [h18] at hCheck; dsimp only at hCheck
          cases hEC : s15.memory.borrows.find? (fun e => e.protector == some 2) with
          | none => rw [hEC] at hCheck; cases hCheck
          | some eCallee =>
            cases hER : s15.memory.borrows.find? (fun e => e.protector == some 1) with
            | none => rw [hEC, hER] at hCheck; cases hCheck
            | some eCaller =>
              rw [hEC, hER] at hCheck; dsimp only at hCheck
              simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
                List.isEmpty_iff] at hCheck
              obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩,
                h11⟩, h12⟩, h13⟩, h14⟩, h15'⟩, h16'⟩, h17⟩, h18'⟩, h19⟩ := hCheck
              exact ⟨s15, s16, s18, eCallee, eCaller, rfl, h16, h18,
                h1, h2, List.mem_of_find?_eq_some hEC, List.mem_of_find?_eq_some hER,
                h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15', h16', h17, h18', h19⟩
      | halted _ => rw [h16] at hCheck; cases hCheck
      | faulted _ => rw [h16] at hCheck; cases hCheck
    | ret _ => rw [h16] at hCheck; cases hCheck
    | vis _ _ => rw [h16] at hCheck; cases hCheck

/-- **Live multi-step `stepMirFn` unwind protector-release trace on Case `21`** (non-tautological
execution theorem directly on unmodified `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn`):
1. At step `15` (inside `ep1::c21_callee`, right after `.retag .fnEntry` and `*r = 55`, before
   failing `assert(..., .continue_)`): `callStack.length = 2`, `activeProtectors = [2, 1]`,
   real borrow entries `eCallee` (`protector = some 2`) and `eCaller` (`protector = some 1`) in
   `memory.borrows` are BOTH protected (`isBorrowProtected = true`), and root `_1 = 55`.
2. Immediately after the single unwind step `15 → 16` landing in `ep1::c21_caller` cleanup `bb2`:
   `frame.blockIdx = 2`, `callStack.length = 1`, `activeProtectors = [1]` (callee protector `2`
   stripped!), `isBorrowProtected s16.memory.activeProtectors eCallee = false`, while
   `isBorrowProtected s16.memory.activeProtectors eCaller = true` (strict LIFO!), and root `_1 = 55`.
3. Immediately after caller cleanup writes `65` and `unwindResume`s into `ep1::c21_main` catch
   `bb2` (step `18`): `frame.blockIdx = 2`, `callStack = []`, `activeProtectors = []` (both
   protectors released!), BOTH `eCallee` and `eCaller` are unprotected, and root `_1 = 65`! -/
theorem trusted_case21_live_unwind_protector_release_trace :
    let sInit := initMachineStateWithCallees mirCase21.1 [] mirCase21.2
    ∃ s15 s16 s18 eCallee eCaller,
      runTrustedTrace mirCase21.1 15 sInit = some s15 ∧
      stepMirFn mirCase21.1 s15 = .tau (.running s16) ∧
      runTrustedTrace mirCase21.1 2 s16 = some s18 ∧
      -- Step 15 (callee before panic): both protectors active, partial writeback 55 visible
      s15.memory.callStack.length = 2 ∧
      s15.memory.activeProtectors = [2, 1] ∧
      eCallee ∈ s15.memory.borrows ∧
      eCaller ∈ s15.memory.borrows ∧
      eCallee.protector = some 2 ∧
      eCaller.protector = some 1 ∧
      isBorrowProtected s15.memory.activeProtectors eCallee = true ∧
      isBorrowProtected s15.memory.activeProtectors eCaller = true ∧
      readRootLocalU32 s15 1 = some 55 ∧
      -- Step 16 (caller cleanup bb2 after unwind): callee protector 2 released, caller 1 preserved!
      s16.frame.blockIdx = 2 ∧
      s16.memory.callStack.length = 1 ∧
      s16.memory.activeProtectors = [1] ∧
      isBorrowProtected s16.memory.activeProtectors eCallee = false ∧
      isBorrowProtected s16.memory.activeProtectors eCaller = true ∧
      readRootLocalU32 s16 1 = some 55 ∧
      -- Step 18 (main catch bb2 after caller unwindResume): all protectors released, root = 65!
      s18.frame.blockIdx = 2 ∧
      s18.memory.callStack = [] ∧
      s18.memory.activeProtectors = [] ∧
      isBorrowProtected s18.memory.activeProtectors eCallee = false ∧
      isBorrowProtected s18.memory.activeProtectors eCaller = false ∧
      readRootLocalU32 s18 1 = some 65 :=
  case21TraceCheck_sound mirCase21.1
    (initMachineStateWithCallees mirCase21.1 [] mirCase21.2) (by kernel_rfl)

/-- Decidable checker for a 3-frame LIFO `.continue_` unwind trace (`step 13 → step 14`)
over any `body : CapturedMir` and initial `sInit : MachineState`. -/
def case23TraceCheck (body : CapturedMir) (sInit : MachineState) : Bool :=
  match runTrustedTrace body 13 sInit with
  | some s13 =>
    match stepMirFn body s13 with
    | .tau (.running s14) =>
      match s13.memory.borrows.find? (fun e => e.protector == some 2),
            s13.memory.borrows.find? (fun e => e.protector == some 1) with
      | some eLeaf, some eMid =>
        decide (s13.memory.callStack.length = 2) &&
        decide (s13.memory.activeProtectors = [2, 1]) &&
        decide (eLeaf.protector = some 2) &&
        decide (eMid.protector = some 1) &&
        isBorrowProtected s13.memory.activeProtectors eLeaf &&
        isBorrowProtected s13.memory.activeProtectors eMid &&
        decide (readRootLocalU32 s13 1 = some 3) &&
        decide (s14.frame.blockIdx = 2) &&
        decide (s14.memory.callStack.isEmpty) &&
        decide (s14.memory.activeProtectors = []) &&
        !isBorrowProtected s14.memory.activeProtectors eLeaf &&
        !isBorrowProtected s14.memory.activeProtectors eMid &&
        decide (readRootLocalU32 s14 1 = some 3)
      | _, _ => false
    | _ => false
  | none => false

private theorem case23TraceCheck_sound (body : CapturedMir) (sInit : MachineState)
    (hCheck : case23TraceCheck body sInit = true) :
    ∃ s13 s14 eLeaf eMid,
      runTrustedTrace body 13 sInit = some s13 ∧
      stepMirFn body s13 = .tau (.running s14) ∧
      s13.memory.callStack.length = 2 ∧
      s13.memory.activeProtectors = [2, 1] ∧
      eLeaf ∈ s13.memory.borrows ∧
      eMid ∈ s13.memory.borrows ∧
      eLeaf.protector = some 2 ∧
      eMid.protector = some 1 ∧
      isBorrowProtected s13.memory.activeProtectors eLeaf = true ∧
      isBorrowProtected s13.memory.activeProtectors eMid = true ∧
      readRootLocalU32 s13 1 = some 3 ∧
      s14.frame.blockIdx = 2 ∧
      s14.memory.callStack = [] ∧
      s14.memory.activeProtectors = [] ∧
      isBorrowProtected s14.memory.activeProtectors eLeaf = false ∧
      isBorrowProtected s14.memory.activeProtectors eMid = false ∧
      readRootLocalU32 s14 1 = some 3 := by
  unfold case23TraceCheck at hCheck
  cases h13 : runTrustedTrace body 13 sInit with
  | none => rw [h13] at hCheck; cases hCheck
  | some s13 =>
    rw [h13] at hCheck; dsimp only at hCheck
    cases h14 : stepMirFn body s13 with
    | tau st14 =>
      cases st14 with
      | running s14 =>
        rw [h14] at hCheck; dsimp only at hCheck
        cases hEL : s13.memory.borrows.find? (fun e => e.protector == some 2) with
        | none => rw [hEL] at hCheck; cases hCheck
        | some eLeaf =>
          cases hEM : s13.memory.borrows.find? (fun e => e.protector == some 1) with
          | none => rw [hEL, hEM] at hCheck; cases hCheck
          | some eMid =>
            rw [hEL, hEM] at hCheck; dsimp only at hCheck
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
              List.isEmpty_iff] at hCheck
            obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩,
              h11⟩, h12⟩, h13'⟩ := hCheck
            exact ⟨s13, s14, eLeaf, eMid, rfl, h14,
              h1, h2, List.mem_of_find?_eq_some hEL, List.mem_of_find?_eq_some hEM,
              h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13'⟩
      | halted _ => rw [h14] at hCheck; cases hCheck
      | faulted _ => rw [h14] at hCheck; cases hCheck
    | ret _ => rw [h14] at hCheck; cases hCheck
    | vis _ _ => rw [h14] at hCheck; cases hCheck

/-- **Live 3-frame LIFO `.continue_` unwind trace on Case `23`** (`main → mid → leaf`) directly
on unmodified `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn`:
- At step `13` (inside `ep1::c23_leaf`, right before failing `assert(..., .continue_)`):
  `callStack.length = 2`, `activeProtectors = [2, 1]`, real borrow entries `eLeaf` and `eMid` in
  `memory.borrows` are BOTH protected, and root `_1 = 3`.
- Immediately after the single multi-frame unwind step `13 → 14` popping `leaf` AND skipping `mid`
  (`.continue_`) into `ep1::c23_main` cleanup `bb2`: `frame.blockIdx = 2`, `callStack = []`,
  `activeProtectors = []`, BOTH `eLeaf` and `eMid` are unprotected (`isBorrowProtected = false`),
  and root `_1 = 3` (pre-panic partial `&mut` writeback preserved across 2 popped frames!). -/
theorem trusted_case23_three_frame_lifo_unwind_trace :
    let sInit := initMachineStateWithCallees mirCase23.1 [] mirCase23.2
    ∃ s13 s14 eLeaf eMid,
      runTrustedTrace mirCase23.1 13 sInit = some s13 ∧
      stepMirFn mirCase23.1 s13 = .tau (.running s14) ∧
      s13.memory.callStack.length = 2 ∧
      s13.memory.activeProtectors = [2, 1] ∧
      eLeaf ∈ s13.memory.borrows ∧
      eMid ∈ s13.memory.borrows ∧
      eLeaf.protector = some 2 ∧
      eMid.protector = some 1 ∧
      isBorrowProtected s13.memory.activeProtectors eLeaf = true ∧
      isBorrowProtected s13.memory.activeProtectors eMid = true ∧
      readRootLocalU32 s13 1 = some 3 ∧
      s14.frame.blockIdx = 2 ∧
      s14.memory.callStack = [] ∧
      s14.memory.activeProtectors = [] ∧
      isBorrowProtected s14.memory.activeProtectors eLeaf = false ∧
      isBorrowProtected s14.memory.activeProtectors eMid = false ∧
      readRootLocalU32 s14 1 = some 3 :=
  case23TraceCheck_sound mirCase23.1
    (initMachineStateWithCallees mirCase23.1 [] mirCase23.2) (by kernel_rfl)

/-- **Causal unwind protector-release contrast across BOTH `Trusted.MirSemantics` and `MiniRust`**:
attempting the parent write BEFORE callee unwind releases the `FnEntry` protector faults with `.ub`
on BOTH unmodified `Trusted.MirSemantics.stepMirFn` (`mirCase21PrematureWrite`) and MiniRust
`MachTB` (`mrProg21PrematureWrite`), whereas performing the exact same parent write AFTER callee
unwind in Case `21` succeeds on BOTH (`.okCleanupRecovered 65 65`). -/
theorem trusted_case21_premature_parent_write_ub_contrast :
    runTrustedObs mirCase21PrematureWrite.1 mirCase21PrematureWrite.2 true 120 = .ub ∧
    trustedCrossFramePanicObserve 21 = .okCleanupRecovered 65 65 ∧
    ofMrObs (MiniRustSpec.CrossFrameRefAndPanicMR.runProgramObsM (M := MiniRustSpec.Interp.TBM)
      ({ implicit_writes := true } : MiniRustSpec.Gen.TreeBorrowsParams)
      MiniRustSpec.CrossFrameRefAndPanicMR.mrProg21PrematureWrite 120) = .ub := by
  refine ⟨?_, ?_, ?_⟩
  · kernel_rfl
  · rw [trustedCrossFramePanicObserve_matches_expected]; rfl
  · rw [MiniRustSpec.CrossFrameRefAndPanicMR.mr_case21_premature_parent_write_ub_contrast.2.1]; rfl

/-- **Total 3-way exact agreement & exact root-ceiling divergence `↔` theorem** (for ALL `idx : Nat`):
1. For every `idx ≠ 27` (`0..26` and `≥ 28`), unmodified `Trusted.MirSemantics.stepMirFn`,
   MiniRust `MachTB`, and LeanMiri (`treeBorrows = true`) agree identically.
2. `Trusted` disagrees with MiniRust `MachTB` (and with LeanMiri `treeBorrows = true`)
   IF AND ONLY IF `idx = 27` (`Memory.rootUnwindCeiling = true`).
3. Explicit Case `26` (`rootUnwindCeiling = false` → 3-way `.ub`) vs. Case `27`
   (`rootUnwindCeiling = true` → Trusted `.unwound 77` vs. MiniRust/LeanMiri `.ub`) contrast. -/
theorem contract_three_way_and_root_ceiling_exact (c : CrossFramePanicDualContract) :
    (∀ idx, idx ≠ 27 →
      trustedCrossFramePanicObserve idx = mrObserve .treeBorrows idx ∧
      mrObserve .treeBorrows idx = c.lm.observe true idx) ∧
    (∀ idx, trustedCrossFramePanicObserve idx ≠ mrObserve .treeBorrows idx ↔ idx = 27) ∧
    (∀ idx, trustedCrossFramePanicObserve idx ≠ c.lm.observe true idx ↔ idx = 27) ∧
    (trustedCrossFramePanicObserve 26 = .ub ∧ mrObserve .treeBorrows 26 = .ub ∧
      c.lm.observe true 26 = .ub) ∧
    (trustedCrossFramePanicObserve 27 = .unwound 77 ∧ mrObserve .treeBorrows 27 = .ub ∧
      c.lm.observe true 27 = .ub) := by
  have hDiffMR : ∀ idx, trustedCrossFramePanicObserve idx ≠ mrObserve .treeBorrows idx ↔ idx = 27 := by
    intro idx
    rw [trustedCrossFramePanicObserve_matches_expected, mrObserve_matches_expected]
    exact trustedExpected_ne_authority_iff idx
  have hDiffLM : ∀ idx, trustedCrossFramePanicObserve idx ≠ c.lm.observe true idx ↔ idx = 27 := by
    intro idx
    rw [contract_lm_tb_eq]
    exact hDiffMR idx
  refine ⟨?_, hDiffMR, hDiffLM, ?_, ?_⟩
  · intro idx hNe
    have hT : trustedCrossFramePanicObserve idx = mrObserve .treeBorrows idx := by
      rw [trustedCrossFramePanicObserve_matches_expected, mrObserve_matches_expected]
      unfold trustedExpected
      split
      · exact absurd rfl hNe
      · rfl
    exact ⟨hT, (contract_lm_tb_eq c idx).symm⟩
  · refine ⟨by rw [trustedCrossFramePanicObserve_matches_expected]; rfl,
            by rw [mrObserve_matches_expected]; rfl,
            by rw [contract_lm_tb_eq, mrObserve_matches_expected]; rfl⟩
  · refine ⟨by rw [trustedCrossFramePanicObserve_matches_expected]; rfl,
            by rw [mrObserve_matches_expected]; rfl,
            by rw [contract_lm_tb_eq, mrObserve_matches_expected]; rfl⟩

end TrustedAndUnwindBridge

/-- **Root-ceiling divergence reconciliation via an outer catch harness**: the single Case `27`
divergence is EXACTLY the "MiniRust hits `BottomOfStack` UB unless wrapped in an outer catch
harness" boundary. Trusted's `rootUnwindCeiling = true` observation of the bare root unwind
(`.unwound 77`) coincides on BOTH `Mach` and `MachTB` with MiniRust executing the same panicking
body wrapped in a `StopUnwind` catch harness (`mrProgRootUnwindCaught`), while the unwrapped
MiniRust root unwind is `.ub` (= Trusted with `rootUnwindCeiling = false`, Case `26`). -/
theorem root_ceiling_divergence_reconciled_by_catch_harness :
    trustedCrossFramePanicObserve 27 =
      ofMrObs (MiniRustSpec.CrossFrameRefAndPanicMR.runProgramObsM (M := MiniRustSpec.Interp.BM) ()
        MiniRustSpec.CrossFrameRefAndPanicMR.mrProgRootUnwindCaught 120) ∧
    trustedCrossFramePanicObserve 27 =
      ofMrObs (MiniRustSpec.CrossFrameRefAndPanicMR.runProgramObsM (M := MiniRustSpec.Interp.TBM)
        ({ implicit_writes := true } : MiniRustSpec.Gen.TreeBorrowsParams)
        MiniRustSpec.CrossFrameRefAndPanicMR.mrProgRootUnwindCaught 120) ∧
    trustedCrossFramePanicObserve 26 =
      ofMrObs (MiniRustSpec.CrossFrameRefAndPanicMR.runProgramObsM (M := MiniRustSpec.Interp.BM) ()
        MiniRustSpec.CrossFrameRefAndPanicMR.mrProgRootUnwind 120) ∧
    trustedCrossFramePanicObserve 26 =
      ofMrObs (MiniRustSpec.CrossFrameRefAndPanicMR.runProgramObsM (M := MiniRustSpec.Interp.TBM)
        ({ implicit_writes := true } : MiniRustSpec.Gen.TreeBorrowsParams)
        MiniRustSpec.CrossFrameRefAndPanicMR.mrProgRootUnwind 120) := by
  have hMr := MiniRustSpec.CrossFrameRefAndPanicMR.mr_root_unwind_boundary_vs_catch_harness
  rw [trustedCrossFramePanicObserve_matches_expected, trustedCrossFramePanicObserve_matches_expected,
    hMr.1, hMr.2.1, hMr.2.2.1, hMr.2.2.2]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## §6. Genuine `Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle` Instantiation & Mode-Sensitivity Guard -/

/-- Lift `CrossFramePanicObs` into `DualCorrespondenceBundle.ExecOutcome4` following
`docs/mir-correspondence-strategy.md` Section 4.6 (`ExecOutcome4.ofMirOutcome` maps
`.abort → .fault .unsupported`, `.panic → .unwind`, `.ub → .fault .undefined`). -/
def obsToExecOutcome4 : CrossFramePanicObs → ExecOutcome4 CrossFrameNormalRet Nat
  | .okVal r ref => .normal ⟨r, ref, false⟩
  | .okCleanupRecovered r ref => .normal ⟨r, ref, true⟩
  | .unwound ref => .unwind ref
  | .ub => .fault .undefined
  | .abort => .fault .unsupported
  | .specPanic => .fault .unsupported
  | .invalidOrUnsupported => .fault .unsupported

/-- The `ExecOutcome4` lift is lossy exactly at `.fault .unsupported` (the repository-wide
`abort ↦ unsupported` convention of `ExecOutcome4.ofMirOutcome`). -/
theorem obsToExecOutcome4_unsupported_iff (o : CrossFramePanicObs) :
    obsToExecOutcome4 o = .fault .unsupported ↔
      o = .abort ∨ o = .specPanic ∨ o = .invalidOrUnsupported := by
  cases o <;> simp [obsToExecOutcome4]

/-- **Bundle abort faithfulness on every canonical cell**: because no canonical cell is
`.specPanic` / `.invalidOrUnsupported` (`canonical_cells_nondegenerate`), a bundle-level
`.fault .unsupported` verdict of the Trusted evaluator, the MiniRust `MachTB` evaluator, or ANY
certified LeanMiri authority on `idx < 28` means EXACTLY a deterministic `.abort` — the lossy
`ExecOutcome4` lift cannot hide an unsupported/invalid cell behind an abort. -/
theorem bundle_unsupported_iff_abort (c : CrossFramePanicDualContract) (idx : Nat)
    (hi : idx < canonicalCaseCount) :
    (obsToExecOutcome4 (trustedCrossFramePanicObserve idx) = .fault .unsupported ↔
      trustedCrossFramePanicObserve idx = .abort) ∧
    (obsToExecOutcome4 (mrObserve .treeBorrows idx) = .fault .unsupported ↔
      mrObserve .treeBorrows idx = .abort) ∧
    (obsToExecOutcome4 (c.lm.observe true idx) = .fault .unsupported ↔
      c.lm.observe true idx = .abort) := by
  obtain ⟨_, _, hTbI, hTbS, hTrI, hTrS⟩ := canonical_cells_nondegenerate idx hi
  rw [trustedCrossFramePanicObserve_matches_expected, contract_lm_tb_eq,
    mrObserve_matches_expected, obsToExecOutcome4_unsupported_iff,
    obsToExecOutcome4_unsupported_iff]
  refine ⟨?_, ?_, ?_⟩ <;>
    first
    | exact ⟨fun h => h.elim id (fun h' => h'.elim (fun e => absurd e hTrS)
        (fun e => absurd e hTrI)), Or.inl⟩
    | exact ⟨fun h => h.elim id (fun h' => h'.elim (fun e => absurd e hTbS)
        (fun e => absurd e hTbI)), Or.inl⟩

/-- Three-way agreement support gate: every scenario `idx ≠ 27` (covering all 27 agreement
scenarios `0..26` plus all out-of-range fail-closed indices `≥ 28`, excluding strictly the
`rootUnwindCeiling = true` boundary at Case `27`). -/
def crossFrameSupportGate (_ : Unit) (idx : Nat) (_ : Unit) : Prop := idx ≠ 27

/-- Real Anneal evaluator for `DualCorrespondenceBundle`, executing directly through unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn`. -/
def annealEval (_ : Unit) (idx : Nat) (_ : Unit) (_ : Unit) :
    ExecOutcome4 CrossFrameNormalRet Nat :=
  obsToExecOutcome4 (trustedCrossFramePanicObserve idx)

/-- Real MiniRust `MachTB` evaluator for `DualCorrespondenceBundle`. -/
def mrTbEval (_ : Unit) (idx : Nat) (_ : Unit) (_ : Unit) :
    ExecOutcome4 CrossFrameNormalRet Nat :=
  obsToExecOutcome4 (mrObserve .treeBorrows idx)

/-- Real LeanMiri (`treeBorrows = true`) evaluator for `DualCorrespondenceBundle`. -/
def lmTbEval (c : CrossFramePanicDualContract) (_ : Unit) (idx : Nat) (_ : Unit) (_ : Unit) :
    ExecOutcome4 CrossFrameNormalRet Nat :=
  obsToExecOutcome4 (c.lm.observe true idx)

/-- **Genuine `Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle` instantiation**
packaging both `MiniRustSpec` (`MachTB`) and `LeanMiriSpec` (`treeBorrows = true`) over
unmodified `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn`, with full `ReverseTotal`
(`reverse_total? = some _`), constructive `crossFrameNormalRetCodec`, Case `0` positive
witnesses, Case `8` Tree Borrows protector-conflict fault witnesses, and Case `0` ↔ Case `8`
flip-direction guards! -/
def mkCrossFramePanicDualBundle (c : CrossFramePanicDualContract) :
    DualCorrespondenceBundle Unit Nat Unit CrossFrameNormalRet Nat CrossFrameNormalRep
      Unit Unit CrossFrameNormalRet Nat Unit Unit CrossFrameNormalRet Nat where
  codec := crossFrameNormalRetCodec
  repMR := crossFrameNormalRetCodec.encode
  repLM := crossFrameNormalRetCodec.encode
  mrRel := ModeParamStepRel.ofEval crossFrameSupportGate annealEval mrTbEval Eq Eq
  lmRel := ModeParamStepRel.ofEval crossFrameSupportGate annealEval (lmTbEval c) Eq Eq
  mrSim := ModeStepSim.fromDeterministicEval crossFrameSupportGate annealEval mrTbEval Eq Eq
    (fun _ idx _ _ hGate => by
      have hEq := ((contract_three_way_and_root_ceiling_exact c).1 idx hGate).1
      show ChoiceCoupledOutcomeRel Eq Eq
        (obsToExecOutcome4 (trustedCrossFramePanicObserve idx))
        (obsToExecOutcome4 (mrObserve .treeBorrows idx))
      rw [hEq]
      exact ChoiceCoupledOutcomeRel.refl (fun _ => rfl) (fun _ => rfl) _)
  lmSim := ModeStepSim.fromDeterministicEval crossFrameSupportGate annealEval (lmTbEval c) Eq Eq
    (fun _ idx _ _ hGate => by
      have hBoth := (contract_three_way_and_root_ceiling_exact c).1 idx hGate
      have hEq : trustedCrossFramePanicObserve idx = c.lm.observe true idx :=
        hBoth.1.trans hBoth.2
      show ChoiceCoupledOutcomeRel Eq Eq
        (obsToExecOutcome4 (trustedCrossFramePanicObserve idx))
        (obsToExecOutcome4 (c.lm.observe true idx))
      rw [hEq]
      exact ChoiceCoupledOutcomeRel.refl (fun _ => rfl) (fun _ => rfl) _)
  mr_ret_codec := fun _ _ h => h ▸ rfl
  lm_ret_codec := fun _ _ h => h ▸ rfl
  toAnnealMR := id
  toAnnealLM := id
  ExecAnneal := fun m idx q out => annealEval m idx q () = out
  anneal_exec_coherent := ⟨
    fun _ _ _ _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩,
    fun _ _ _ _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩⟩
  mrPositive :=
    { m := (), p := 0, q := (), c := (),
      gate := (fun h => by cases h),
      wf := (fun _ k hF => by
        change obsToExecOutcome4 (trustedCrossFramePanicObserve 0) = .fault k at hF
        rw [trustedCrossFramePanicObserve_matches_expected] at hF
        cases hF),
      agree := ⟨⟨42, 42, false⟩, ⟨42, 42, false⟩,
        (by change obsToExecOutcome4 (trustedCrossFramePanicObserve 0) = _; rw [trustedCrossFramePanicObserve_matches_expected]; rfl),
        (by change obsToExecOutcome4 (mrObserve .treeBorrows 0) = _; rw [mrObserve_matches_expected]; rfl),
        rfl⟩ }
  lmPositive :=
    { m := (), p := 0, q := (), c := (),
      gate := (fun h => by cases h),
      wf := (fun _ k hF => by
        change obsToExecOutcome4 (trustedCrossFramePanicObserve 0) = .fault k at hF
        rw [trustedCrossFramePanicObserve_matches_expected] at hF
        cases hF),
      agree := ⟨⟨42, 42, false⟩, ⟨42, 42, false⟩,
        (by change obsToExecOutcome4 (trustedCrossFramePanicObserve 0) = _; rw [trustedCrossFramePanicObserve_matches_expected]; rfl),
        (by change obsToExecOutcome4 (c.lm.observe true 0) = _; rw [contract_lm_tb_eq, mrObserve_matches_expected]; rfl),
        rfl⟩ }
  mrFault :=
    { m := (), p := 8, q := (), c := (), kind := .undefined,
      gate := (fun h => by cases h),
      execA := (by change obsToExecOutcome4 (trustedCrossFramePanicObserve 8) = _; rw [trustedCrossFramePanicObserve_matches_expected]; rfl),
      execR := (by change obsToExecOutcome4 (mrObserve .treeBorrows 8) = _; rw [mrObserve_matches_expected]; rfl) }
  lmFault :=
    { m := (), p := 8, q := (), c := (), kind := .undefined,
      gate := (fun h => by cases h),
      execA := (by change obsToExecOutcome4 (trustedCrossFramePanicObserve 8) = _; rw [trustedCrossFramePanicObserve_matches_expected]; rfl),
      execR := (by change obsToExecOutcome4 (c.lm.observe true 8) = _; rw [contract_lm_tb_eq, mrObserve_matches_expected]; rfl) }
  mrFlip :=
    { m := (), pOk := 0, qOk := (), cOk := (), pFault := 8, qFault := (), cFault := (),
      kind := .undefined, gateOk := (fun h => by cases h), gateFault := (fun h => by cases h),
      okAgree := ⟨⟨42, 42, false⟩, ⟨42, 42, false⟩,
        (by change obsToExecOutcome4 (trustedCrossFramePanicObserve 0) = _; rw [trustedCrossFramePanicObserve_matches_expected]; rfl),
        (by change obsToExecOutcome4 (mrObserve .treeBorrows 0) = _; rw [mrObserve_matches_expected]; rfl),
        rfl⟩,
      wfOkA := (fun _ k hF => by
        change obsToExecOutcome4 (trustedCrossFramePanicObserve 0) = .fault k at hF
        rw [trustedCrossFramePanicObserve_matches_expected] at hF; cases hF),
      wfOkR := (fun _ k hF => by
        change obsToExecOutcome4 (mrObserve .treeBorrows 0) = .fault k at hF
        rw [mrObserve_matches_expected] at hF; cases hF),
      faultA := (by change obsToExecOutcome4 (trustedCrossFramePanicObserve 8) = _; rw [trustedCrossFramePanicObserve_matches_expected]; rfl),
      faultR := (by change obsToExecOutcome4 (mrObserve .treeBorrows 8) = _; rw [mrObserve_matches_expected]; rfl) }
  lmFlip :=
    { m := (), pOk := 0, qOk := (), cOk := (), pFault := 8, qFault := (), cFault := (),
      kind := .undefined, gateOk := (fun h => by cases h), gateFault := (fun h => by cases h),
      okAgree := ⟨⟨42, 42, false⟩, ⟨42, 42, false⟩,
        (by change obsToExecOutcome4 (trustedCrossFramePanicObserve 0) = _; rw [trustedCrossFramePanicObserve_matches_expected]; rfl),
        (by change obsToExecOutcome4 (c.lm.observe true 0) = _; rw [contract_lm_tb_eq, mrObserve_matches_expected]; rfl),
        rfl⟩,
      wfOkA := (fun _ k hF => by
        change obsToExecOutcome4 (trustedCrossFramePanicObserve 0) = .fault k at hF
        rw [trustedCrossFramePanicObserve_matches_expected] at hF; cases hF),
      wfOkR := (fun _ k hF => by
        change obsToExecOutcome4 (c.lm.observe true 0) = .fault k at hF
        rw [contract_lm_tb_eq, mrObserve_matches_expected] at hF; cases hF),
      faultA := (by change obsToExecOutcome4 (trustedCrossFramePanicObserve 8) = _; rw [trustedCrossFramePanicObserve_matches_expected]; rfl),
      faultR := (by change obsToExecOutcome4 (c.lm.observe true 8) = _; rw [contract_lm_tb_eq, mrObserve_matches_expected]; rfl) }

/-- Projected bundle corollaries from `mkCrossFramePanicDualBundle`: positive non-vacuity,
fault-equivalence witness, flip-direction non-constancy, exact cross-authority fault/normal/
unwind/diverge/well-formedness equivalence (`crossAuthorityExactEquiv`, `crossAuthorityUnwindIff`,
`crossAuthorityWellFormedEquiv`), and explicit 3-way bundle witnesses on Case `17` (`.unwind 115`),
Case `21` (`.normal ⟨65, 65, true⟩` cleanup recovery), and Case `23` (`.normal ⟨300, 300, true⟩`
3-frame LIFO cleanup recovery) proving every branch of the bundle is non-vacuous! -/
theorem crossFramePanicDualBundle_projections (c : CrossFramePanicDualContract) :
    let B := mkCrossFramePanicDualBundle c
    B.mrSim.reverse_total?.isSome = true ∧
    B.lmSim.reverse_total?.isSome = true ∧
    CorrespondenceClaim B.mrRel ∧
    CorrespondenceClaim B.lmRel ∧
    FaultEquivClaim B.mrRel ∧
    FaultEquivClaim B.lmRel ∧
    ((¬ ∀ m p q out, B.mrRel.SupportGate m p q →
        B.ExecAnneal (B.toAnnealMR m) p q out → ∃ a, out = .normal a) ∧
     (¬ ∀ m p q out, B.mrRel.SupportGate m p q →
        B.ExecAnneal (B.toAnnealMR m) p q out → ∃ k, out = .fault k)) ∧
    (∀ idx, idx ≠ 27 → ∀ k,
      (∃ ch, B.mrRel.ExecR () idx () ch (.fault k)) ↔
      (∃ ch, B.lmRel.ExecR () idx () ch (.fault k))) ∧
    (∀ idx, idx ≠ 27 → ∀ retMR retLM,
      (∃ ch, B.mrRel.ExecR () idx () ch (.normal retMR)) →
      (∃ ch, B.lmRel.ExecR () idx () ch (.normal retLM)) →
      B.repMR retMR = B.repLM retLM) ∧
    (∀ idx, idx ≠ 27 → ∀ uA,
      ((∃ ch u, B.mrRel.ExecR () idx () ch (.unwind u) ∧ B.mrRel.UnwRel uA u) ↔
        B.ExecAnneal () idx () (.unwind uA)) ∧
      ((∃ ch u, B.lmRel.ExecR () idx () ch (.unwind u) ∧ B.lmRel.UnwRel uA u) ↔
        B.ExecAnneal () idx () (.unwind uA)) ∧
      ((∃ ch u, B.mrRel.ExecR () idx () ch (.unwind u) ∧ B.mrRel.UnwRel uA u) ↔
        (∃ ch u, B.lmRel.ExecR () idx () ch (.unwind u) ∧ B.lmRel.UnwRel uA u))) ∧
    (∀ idx, idx ≠ 27 →
      (B.mrRel.WellFormedRef () idx () ↔ ∀ k, ¬ B.ExecAnneal () idx () (.fault k)) ∧
      (B.lmRel.WellFormedRef () idx () ↔ ∀ k, ¬ B.ExecAnneal () idx () (.fault k)) ∧
      (B.mrRel.WellFormedRef () idx () ↔ B.lmRel.WellFormedRef () idx ())) ∧
    -- Concrete non-vacuity witnesses for unwind (Case 17) and cleanup-recovered normal returns (Cases 21 & 23):
    (B.ExecAnneal () 17 () (.unwind 115) ∧
      B.mrRel.ExecR () 17 () () (.unwind 115) ∧
      B.lmRel.ExecR () 17 () () (.unwind 115) ∧
      B.ExecAnneal () 21 () (.normal ⟨65, 65, true⟩) ∧
      B.mrRel.ExecR () 21 () () (.normal ⟨65, 65, true⟩) ∧
      B.lmRel.ExecR () 21 () () (.normal ⟨65, 65, true⟩) ∧
      B.ExecAnneal () 23 () (.normal ⟨300, 300, true⟩) ∧
      B.mrRel.ExecR () 23 () () (.normal ⟨300, 300, true⟩) ∧
      B.lmRel.ExecR () 23 () () (.normal ⟨300, 300, true⟩)) := by
  intro B
  have hRevMR : B.mrRel.ReverseTotal := by
    obtain ⟨h⟩ := Option.isSome_iff_exists.mp (rfl : B.mrSim.reverse_total?.isSome = true)
    exact h.down
  have hRevLM : B.lmRel.ReverseTotal := by
    obtain ⟨h⟩ := Option.isSome_iff_exists.mp (rfl : B.lmSim.reverse_total?.isSome = true)
    exact h.down
  refine ⟨rfl, rfl, B.mrSim.correspondenceClaim, B.lmSim.correspondenceClaim,
    B.mrSim.faultEquivClaim, B.lmSim.faultEquivClaim,
    ⟨B.not_constant_anneal_outcome.1, B.not_constant_anneal_outcome.2.1⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro idx hNe k
    exact B.crossAuthorityFaultEquiv rfl hNe hNe k
  · intro idx hNe retMR retLM ⟨chM, hM⟩ ⟨chL, hL⟩
    have hA1 : ∃ ch, B.mrRel.ExecA () idx () ch (.normal retMR) := by
      obtain ⟨outA, hA, hc⟩ := B.mrSim.forward_total () idx () chM (.normal retMR) hNe hM
      obtain ⟨a, ha, hrel⟩ := hc.normal_ref_to_anneal retMR rfl
      rw [ha, hrel] at hA; exact ⟨chM, hA⟩
    have hA2 : ∃ ch, B.lmRel.ExecA () idx () ch (.normal retLM) := by
      obtain ⟨outA, hA, hc⟩ := B.lmSim.forward_total () idx () chL (.normal retLM) hNe hL
      obtain ⟨a, ha, hrel⟩ := hc.normal_ref_to_anneal retLM rfl
      rw [ha, hrel] at hA; exact ⟨chL, hA⟩
    have hE1 : annealEval () idx () () = .normal retMR := (B.anneal_exec_coherent.1 () idx () _).mp hA1
    have hE2 : annealEval () idx () () = .normal retLM := (B.anneal_exec_coherent.2 () idx () _).mp hA2
    rw [hE1] at hE2
    cases hE2
    rfl
  · intro idx hNe uA
    exact B.crossAuthorityUnwindIff rfl hNe hNe hRevMR hRevLM
      (fun _ _ _ h1 h2 => h1.trans h2.symm)
      (fun _ _ _ h1 h2 => h1.trans h2.symm) uA
  · intro idx hNe
    exact B.crossAuthorityWellFormedEquiv rfl hNe hNe
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change obsToExecOutcome4 (trustedCrossFramePanicObserve 17) = _
      rw [trustedCrossFramePanicObserve_matches_expected]; rfl
    · change obsToExecOutcome4 (mrObserve .treeBorrows 17) = _
      rw [mrObserve_matches_expected]; rfl
    · change obsToExecOutcome4 (c.lm.observe true 17) = _
      rw [contract_lm_tb_eq, mrObserve_matches_expected]; rfl
    · change obsToExecOutcome4 (trustedCrossFramePanicObserve 21) = _
      rw [trustedCrossFramePanicObserve_matches_expected]; rfl
    · change obsToExecOutcome4 (mrObserve .treeBorrows 21) = _
      rw [mrObserve_matches_expected]; rfl
    · change obsToExecOutcome4 (c.lm.observe true 21) = _
      rw [contract_lm_tb_eq, mrObserve_matches_expected]; rfl
    · change obsToExecOutcome4 (trustedCrossFramePanicObserve 23) = _
      rw [trustedCrossFramePanicObserve_matches_expected]; rfl
    · change obsToExecOutcome4 (mrObserve .treeBorrows 23) = _
      rw [mrObserve_matches_expected]; rfl
    · change obsToExecOutcome4 (c.lm.observe true 23) = _
      rw [contract_lm_tb_eq, mrObserve_matches_expected]; rfl

/-- Direct 2-mode (`CrossFramePanicMode`: `.basic` vs `.treeBorrows`) step relation between
MiniRust (`Mach`/`MachTB`) and LeanMiri (`treeBorrows = false`/`true`) with constructive
`ModeSensitivityWitness` instances on Cases `8` and `9` proving `not_mode_invariant`. -/
def mkMrLmModeStepRel (c : CrossFramePanicDualContract) :
    ModeParamStepRel CrossFramePanicMode Nat Unit Unit
      CrossFrameNormalRet CrossFrameNormalRet Nat Nat :=
  ModeParamStepRel.ofEval (fun _ _ _ => True)
    (fun m idx _ _ => obsToExecOutcome4 (mrObserve m idx))
    (fun m idx _ _ => obsToExecOutcome4 (c.lm.observe m.toLmTreeBorrows idx))
    Eq Eq

def mrLmModeSensitivityCase8 (c : CrossFramePanicDualContract) :
    ModeSensitivityWitness (mkMrLmModeStepRel c) where
  m₁ := .basic
  m₂ := .treeBorrows
  p := 8
  q := ()
  c := ()
  gate₁ := trivial
  gate₂ := trivial
  flips := ⟨.normal ⟨77, 77, false⟩, .normal ⟨77, 77, false⟩,
    (by change obsToExecOutcome4 (mrObserve .basic 8) = _; rw [mrObserve_matches_expected]; rfl),
    (by change obsToExecOutcome4 (c.lm.observe false 8) = _; rw [contract_lm_basic_eq, mrObserve_matches_expected]; rfl),
    ChoiceCoupledOutcomeRel.refl (fun _ => rfl) (fun _ => rfl) _,
    (fun _ h => by change obsToExecOutcome4 (mrObserve .treeBorrows 8) = _ at h; rw [mrObserve_matches_expected] at h; cases h),
    (fun _ h => by change obsToExecOutcome4 (c.lm.observe true 8) = _ at h; rw [contract_lm_tb_eq, mrObserve_matches_expected] at h; cases h)⟩

def mrLmModeSensitivityCase9 (c : CrossFramePanicDualContract) :
    ModeSensitivityWitness (mkMrLmModeStepRel c) where
  m₁ := .basic
  m₂ := .treeBorrows
  p := 9
  q := ()
  c := ()
  gate₁ := trivial
  gate₂ := trivial
  flips := ⟨.normal ⟨99, 99, false⟩, .normal ⟨99, 99, false⟩,
    (by change obsToExecOutcome4 (mrObserve .basic 9) = _; rw [mrObserve_matches_expected]; rfl),
    (by change obsToExecOutcome4 (c.lm.observe false 9) = _; rw [contract_lm_basic_eq, mrObserve_matches_expected]; rfl),
    ChoiceCoupledOutcomeRel.refl (fun _ => rfl) (fun _ => rfl) _,
    (fun _ h => by change obsToExecOutcome4 (mrObserve .treeBorrows 9) = _ at h; rw [mrObserve_matches_expected] at h; cases h),
    (fun _ h => by change obsToExecOutcome4 (c.lm.observe true 9) = _ at h; rw [contract_lm_tb_eq, mrObserve_matches_expected] at h; cases h)⟩

theorem mrLmModeStepRel_not_mode_invariant (c : CrossFramePanicDualContract) :
    (¬ ∀ (m₁ m₂ : CrossFramePanicMode) (p : Nat) (q : Unit) (ch : Unit)
        (out : ExecOutcome4 CrossFrameNormalRet Nat),
        (mkMrLmModeStepRel c).ExecA m₁ p q ch out →
        ∃ ch', (mkMrLmModeStepRel c).ExecA m₂ p q ch' out) ∧
    (¬ ∀ (m₁ m₂ : CrossFramePanicMode) (p : Nat) (q : Unit) (ch : Unit)
        (out : ExecOutcome4 CrossFrameNormalRet Nat),
        (mkMrLmModeStepRel c).ExecR m₁ p q ch out →
        ∃ ch', (mkMrLmModeStepRel c).ExecR m₂ p q ch' out) :=
  (mrLmModeSensitivityCase8 c).not_mode_invariant

/-! ## §7. Episode 1 Unified Dual-Authority Capstone & Silent Import / Axiom / Bridge Audit -/

/-- **Episode 1 Unified Cross-Frame Reference & 4-Way Panic-Unwind Dual-Authority Capstone.** -/
theorem ep1_cross_frame_ref_and_panic_dual_authority_capstone (c : CrossFramePanicDualContract) :
    (crossFramePanicOutcomeCodec.TightValidRep ∧
      (type_of% @crossFramePanicOutcomeCodec_rejects_malformed) ∧
      crossFrameNormalRetCodec.TightValidRep ∧
      (type_of% @ofMrObs_toMrObs) ∧ (type_of% @toMrObs_ofMrObs) ∧
      (type_of% @mirToUnwindAction4_left_inv) ∧ (type_of% @mirToUnwindAction4_right_inv)) ∧
    (type_of% @ep1_minirust_cross_frame_panic_capstone) ∧
    ((type_of% @mrObserve_matches_expected) ∧
      (type_of% @mrObserve_out_of_range) ∧
      (type_of% @mrObserve_mode_sensitivity) ∧
      (type_of% (contract_mr_lm_total_eq c)) ∧
      (type_of% (contract_wire_total_eq c)) ∧
      (type_of% (contract_joint_mode_sensitivity c))) ∧
    ((type_of% @applyUnwindAction_matches_evalRefFrameExit) ∧
      (type_of% @applyUnwindAction_matches_evalProtectedRefFrameExit) ∧
      (type_of% @preventsDeallocation_eq_mr) ∧
      (type_of% @disableFrameBorrows_preserves_outer_frames) ∧
      (type_of% @disableFramesAbove_preserves_surviving_frames) ∧
      (type_of% @hasFrameDeallocProtectorConflict_iff) ∧
      (type_of% @trusted_unwind_continue_chain_to_cleanup) ∧
      (type_of% @trusted_unwind_releases_callee_protector) ∧
      (type_of% @trusted_unwind_continue_chain_root_boundary) ∧
      (type_of% @trustedCrossFramePanicObserve_table) ∧
      (type_of% @trustedCrossFramePanicObserve_out_of_range) ∧
      (type_of% @trusted_case21_live_unwind_protector_release_trace) ∧
      (type_of% @trusted_case23_three_frame_lifo_unwind_trace) ∧
      (type_of% @trusted_case21_premature_parent_write_ub_contrast) ∧
      (type_of% (contract_three_way_and_root_ceiling_exact c))) ∧
    ((type_of% (crossFramePanicDualBundle_projections c)) ∧
      (type_of% (mrLmModeStepRel_not_mode_invariant c))) ∧
    ((type_of% @canonical_cells_nondegenerate) ∧
      (type_of% (bundle_unsupported_iff_abort c)) ∧
      (type_of% @root_ceiling_divergence_reconciled_by_catch_harness) ∧
      (type_of% @crossFramePanicDualContract_nonempty)) :=
  ⟨⟨crossFramePanicOutcomeCodec_tight, crossFramePanicOutcomeCodec_rejects_malformed,
      crossFrameNormalRetCodec_tight, ofMrObs_toMrObs, toMrObs_ofMrObs,
      mirToUnwindAction4_left_inv, mirToUnwindAction4_right_inv⟩,
    ep1_minirust_cross_frame_panic_capstone,
    ⟨mrObserve_matches_expected, mrObserve_out_of_range, mrObserve_mode_sensitivity,
      contract_mr_lm_total_eq c, contract_wire_total_eq c, contract_joint_mode_sensitivity c⟩,
    ⟨@applyUnwindAction_matches_evalRefFrameExit,
      @applyUnwindAction_matches_evalProtectedRefFrameExit, @preventsDeallocation_eq_mr,
      @disableFrameBorrows_preserves_outer_frames, @disableFramesAbove_preserves_surviving_frames,
      @hasFrameDeallocProtectorConflict_iff, @trusted_unwind_continue_chain_to_cleanup,
      @trusted_unwind_releases_callee_protector, @trusted_unwind_continue_chain_root_boundary,
      @trustedCrossFramePanicObserve_table, @trustedCrossFramePanicObserve_out_of_range,
      @trusted_case21_live_unwind_protector_release_trace,
      @trusted_case23_three_frame_lifo_unwind_trace,
      @trusted_case21_premature_parent_write_ub_contrast,
      contract_three_way_and_root_ceiling_exact c⟩,
    ⟨crossFramePanicDualBundle_projections c, mrLmModeStepRel_not_mode_invariant c⟩,
    ⟨canonical_cells_nondegenerate, bundle_unsupported_iff_abort c,
      root_ceiling_divergence_reconciled_by_catch_harness, crossFramePanicDualContract_nonempty⟩⟩

/-- **Non-vacuous instantiation of the Episode 1 capstone** at the inhabited interface witness
`mrBackedLmAuthority` (every `∀ c` conjunct of the capstone is thereby exhibited at a concrete,
kernel-executed contract rather than holding over an empty type). -/
theorem ep1_cross_frame_ref_and_panic_dual_authority_capstone_nonvacuous :
    type_of% (ep1_cross_frame_ref_and_panic_dual_authority_capstone ⟨mrBackedLmAuthority⟩) :=
  ep1_cross_frame_ref_and_panic_dual_authority_capstone ⟨mrBackedLmAuthority⟩

section AxiomAudit
open Lean Elab Command

run_cmd do
  let env ← getEnv
  -- 1. Strict direct-import boundary.
  for imp in env.header.imports do
    unless imp.module == `Init || imp.module == `MiniRustSpec.CrossFrameRefAndPanicMR ||
        imp.module == `Trusted || imp.module == `Anneal.DualCorrespondenceBundle ||
        imp.module == `Anneal.ParametricCore.CallStackUnwind do
      throwError "import-isolation violation: unexpected direct import {imp.module}"
  -- 2. Zero `Miri.*` or `LeanMiriSpec.*` modules (even transitively).
  for modName in env.header.moduleNames do
    if (`Miri).isPrefixOf modName || (`LeanMiriSpec).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported"
  -- 3. Constructive codecs, bijections, and authority checker are strictly choice-free (`[propext, Quot.sound]`).
  let ns := `Anneal.Mir.CrossFrameRefAndPanicDualSpec
  let constructiveDecls : List Lean.Name :=
    [ ns ++ `crossFramePanicOutcomeCodec, ns ++ `crossFramePanicOutcomeCodec_tight,
      ns ++ `crossFramePanicOutcomeCodec_encode_injective,
      ns ++ `crossFramePanicOutcomeCodec_decode_injective_of_valid,
      ns ++ `crossFramePanicDecode_canonical,
      ns ++ `crossFramePanicOutcomeCodec_rejects_malformed,
      ns ++ `crossFrameNormalRetCodec, ns ++ `crossFrameNormalRetCodec_tight,
      ns ++ `ofMrObs_toMrObs, ns ++ `toMrObs_ofMrObs, ns ++ `ofMrObs_injective,
      ns ++ `CrossFramePanicMode.of_toLmTreeBorrows, ns ++ `CrossFramePanicMode.to_ofLmTreeBorrows,
      ns ++ `mirToUnwindAction4_left_inv, ns ++ `mirToUnwindAction4_right_inv,
      ns ++ `unwindAction4Codec,
      ns ++ `lmAuthorityCheck_sound, ns ++ `lmAuthorityOfCheck ]
  for c in constructiveDecls do
    unless env.contains c do throwError "constructive audit: {c} missing"
    for a in ← liftCoreM <| Lean.collectAxioms c do
      unless a == ``propext || a == ``Quot.sound do
        throwError "constructive decl {c} must not depend on {a}"
  -- 4. Bridge theorems reach REAL unmodified Trusted, CallStackUnwind, and DualCorrespondenceBundle constants.
  let bridgeReq : List (Lean.Name × Lean.Name) :=
    [ (ns ++ `applyUnwindAction_matches_evalRefFrameExit,
        `Trusted.Rustc.V2026_06_01.MirSemantics.applyUnwindAction),
      (ns ++ `applyUnwindAction_matches_evalRefFrameExit,
        `Anneal.ParametricCore.evalRefFrameExit),
      (ns ++ `applyUnwindAction_matches_evalProtectedRefFrameExit,
        `Anneal.ParametricCore.evalProtectedRefFrameExit),
      (ns ++ `preventsDeallocation_eq_mr,
        `Trusted.Rustc.V2026_06_01.MirSemantics.preventsDeallocation),
      (ns ++ `disableFrameBorrows_preserves_outer_frames,
        `Trusted.Rustc.V2026_06_01.MirSemantics.disableFrameBorrows),
      (ns ++ `disableFramesAbove_preserves_surviving_frames,
        `Trusted.Rustc.V2026_06_01.MirSemantics.disableFramesAbove),
      (ns ++ `hasFrameDeallocProtectorConflict_iff,
        `Trusted.Rustc.V2026_06_01.MirSemantics.hasFrameDeallocProtectorConflict),
      (ns ++ `trusted_unwind_continue_chain_to_cleanup,
        `Trusted.Rustc.V2026_06_01.MirSemantics.unwindFromCallStack),
      (ns ++ `trusted_unwind_continue_chain_to_cleanup,
        `Trusted.Rustc.V2026_06_01.MirSemantics.restoreCallerProtectors),
      (ns ++ `trusted_unwind_releases_callee_protector,
        `Trusted.Rustc.V2026_06_01.MirSemantics.isBorrowProtected),
      (ns ++ `trustedCrossFramePanicObserve_table,
        `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn),
      (ns ++ `trusted_case21_live_unwind_protector_release_trace,
        `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn),
      (ns ++ `trusted_case21_live_unwind_protector_release_trace,
        `Trusted.Rustc.V2026_06_01.MirSemantics.isBorrowProtected),
      (ns ++ `trusted_case23_three_frame_lifo_unwind_trace,
        `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn),
      (ns ++ `trusted_case21_premature_parent_write_ub_contrast,
        `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn),
      (ns ++ `mkCrossFramePanicDualBundle,
        `Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle),
      (ns ++ `mkCrossFramePanicDualBundle,
        `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn) ]
  for (thm, req) in bridgeReq do
    let some ci := env.find? thm | throwError "bridge audit: {thm} missing"
    let mut seen : NameSet := {}
    let mut todo : Array Lean.Name := ci.type.getUsedConstants
    if let .defnInfo v := ci then
      todo := todo ++ v.value.getUsedConstants
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      if n == req then break
      if ns.isPrefixOf n then
        if let some (.defnInfo v) := env.find? n then
          todo := todo ++ v.value.getUsedConstants
    unless seen.contains req do
      throwError "shadow-evaluator audit: {thm} does not reach the real {req}"
  -- 5. Standard-3-axiom purity & non-vacuous authored theorem floor.
  let mut theorems : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    for a in ← liftCoreM <| Lean.collectAxioms c do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      if a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
        throwError "{c} depends on forbidden axiom {a}"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    if ns.isPrefixOf c && !c.isInternal then
      if let .thmInfo _ := info then theorems := theorems + 1
  if theorems < 30 then
    throwError "axiom audit vacuous: only {theorems} theorems seen"

end AxiomAudit

end Anneal.Mir.CrossFrameRefAndPanicDualSpec
