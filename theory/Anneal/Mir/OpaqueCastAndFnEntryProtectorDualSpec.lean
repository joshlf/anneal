/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.DualCorrespondenceBundle
import Anneal.Mir.DropBinderAndSubtypeBundle
import MiniRustSpec.OpaqueCastAndFnEntryProtectorMR

/-!
# Episode 2 Dual-Authority Bundle: `ProjectionElem.opaqueCast`, Callee-Only
# `FnEntry` Protectors (`rust#166253`), and Machine-Backed Dereferenceability
# (`Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec`)

Packages the Episode 1 authorities `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR`
(root Lake, 100% constructive) and `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM`
(`examples/` Lake, reached solely through the parameterized `OcFpLmAuthority`
interface) as genuine `Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle`
witnesses over unmodified `Trusted.Rustc.V2026_06_01.MirSemantics`.

* **Authority 0 (Anneal Trusted MIR)**: `trustedVerdict` is
  `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcTrustedObserve`, executing
  `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` on the frozen `CapturedMir`
  fixture of every case (zero shadow evaluators).
* **Authority 1 (MiniRust `d821c6e3`)**: `mrVerdict` is
  `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcObserve` (`bootProgramM` /
  `runToStopM` over `BasicMemory` `Mach` and `TreeBorrowsMemory` `MachTB`, plus
  machine-backed `checkPtrM _ _ (some mach)` / `ConcurrentMemory.dereferenceable`).
* **Authority 2 (LeanMiri)**: any `OcFpLmAuthority` whose 44-cell certificate
  `lmTableCheckOf A = true` holds; closed in
  `tests/mir/OpaqueCastAndFnEntryProtectorCorrespondenceTests.lean` directly
  over `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.lmOcObserve`.

**Exact 3-way classification** of the 22 cases × 2 modes (`ocClassOf`):
* `threeWay` (`0..7`, `9..21`; 42 cells): Trusted = MiniRust = LeanMiri.
* `castDerefBoundary` (`8`; 2 cells): dereference directly below a leading
  `.opaqueCast` chain (`*(_2 as *const u32)`). Trusted fails closed honestly
  (`.unsupported`), while MiniRust and LeanMiri evaluate the post-borrowck
  cast-erased image to `okScalar 5`.
* `outOfRange` (`idx ≥ 22`): all three authorities fail closed (`.unsupported`).

**100% Constructive purity (`[propext, Quot.sound]`)**: every single declaration
in this module — codecs, corpus combinators, bundle witnesses, lifted domain
theorems, driver identities, and capstones — depends strictly on `[propext,
Quot.sound]` with ZERO `Classical.choice` allowlist entries.

**Strict import isolation**: imports `Anneal.DualCorrespondenceBundle`,
`Anneal.Mir.DropBinderAndSubtypeBundle` (authority-agnostic `Corpus` layer),
and `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR` only; zero `Miri.*` or
`LeanMiriSpec.*` modules (checked by the trailing `run_cmd` audit).
-/

namespace Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec

set_option Elab.async false

open Anneal.DualCorrespondenceBundle
open Anneal.Mir.DropBinderAndSubtypeBundle
open MiniRustSpec.OpaqueCastAndFnEntryProtectorMR

/-! ## §1. Observable Return-Value Domain and Constructive `CodecLaws` -/

/-- Normal-return observations shared by all three authorities (UB and
unsupported are carried by `Corpus.Verdict`). -/
inductive OcFpObs : Type where
  /-- A scalar result (`D1`). -/
  | scalar (val : Nat)
  /-- A cross-frame `(callee result, caller referent)` pair (`D2`). -/
  | retagPair (retVal : Nat) (referentVal : Nat)
  /-- A validated safe pointer (`D3`). -/
  | ptrValid
  deriving DecidableEq, Repr

/-- Tagged wire representation `(tag, a, b)`. -/
abbrev OcFpObsRep : Type := Nat × Nat × Nat

/-- Canonical encoding: unused payload slots are fixed to `0`. -/
def ocEncode : OcFpObs → OcFpObsRep
  | .scalar v => (0, v, 0)
  | .retagPair r v => (1, r, v)
  | .ptrValid => (2, 0, 0)

/-- Decoding rejects unknown tags and non-zero padding in unused slots. -/
def ocDecode : OcFpObsRep → Option OcFpObs
  | (0, v, 0) => some (.scalar v)
  | (1, r, v) => some (.retagPair r v)
  | (2, 0, 0) => some .ptrValid
  | _ => none

/-- Structural validity of a wire triple (independent of `ocDecode`). -/
def ocValidRep : OcFpObsRep → Prop
  | (0, _, 0) => True
  | (1, _, _) => True
  | (2, 0, 0) => True
  | _ => False

theorem ocEncode_decode_of_valid (b : OcFpObsRep) (a : OcFpObs)
    (hv : ocValidRep b) (hd : ocDecode b = some a) : ocEncode a = b := by
  rcases b with ⟨t, x, y⟩
  match t, x, y with
  | 0, _, 0 => cases hd; rfl
  | 0, _, _ + 1 => exact False.elim hv
  | 1, _, _ => cases hd; rfl
  | 2, 0, 0 => cases hd; rfl
  | 2, 0, _ + 1 => exact False.elim hv
  | 2, _ + 1, _ => exact False.elim hv
  | _ + 3, _, _ => exact False.elim hv

/-- Constructive `CodecLaws OcFpObs OcFpObsRep` (`[propext, Quot.sound]` only). -/
def ocCodec : CodecLaws OcFpObs OcFpObsRep where
  encode := ocEncode
  decode := ocDecode
  ValidRep := ocValidRep
  decode_encode := fun a => by cases a <;> rfl
  encode_valid := fun a => by cases a <;> exact True.intro
  encode_decode_of_valid := ocEncode_decode_of_valid

/-- `ValidRep` is tight: every valid triple decodes. -/
theorem ocCodec_tight : ocCodec.TightValidRep := by
  intro b hv
  rcases b with ⟨t, x, y⟩
  match t, x, y with
  | 0, x, 0 => exact ⟨.scalar x, rfl⟩
  | 0, _, _ + 1 => exact False.elim hv
  | 1, x, y => exact ⟨.retagPair x y, rfl⟩
  | 2, 0, 0 => exact ⟨.ptrValid, rfl⟩
  | 2, 0, _ + 1 => exact False.elim hv
  | 2, _ + 1, _ => exact False.elim hv
  | _ + 3, _, _ => exact False.elim hv

/-- Encoding is injective. -/
theorem ocCodec_encode_injective {a₁ a₂ : OcFpObs}
    (h : ocEncode a₁ = ocEncode a₂) : a₁ = a₂ :=
  ocCodec.encode_injective h

/-- Decoding is injective on valid representations. -/
theorem ocCodec_decode_injective_on_valid {b₁ b₂ : OcFpObsRep} {a : OcFpObs}
    (hv₁ : ocValidRep b₁) (hv₂ : ocValidRep b₂)
    (h₁ : ocDecode b₁ = some a) (h₂ : ocDecode b₂ = some a) : b₁ = b₂ :=
  (ocEncode_decode_of_valid b₁ a hv₁ h₁).symm.trans
    (ocEncode_decode_of_valid b₂ a hv₂ h₂)

/-- `ocValidRep` is EXACTLY the decodable set: it neither over- nor
under-approximates `ocDecode`. -/
theorem ocValidRep_iff_decode_isSome (b : OcFpObsRep) :
    ocValidRep b ↔ (ocDecode b).isSome = true := by
  rcases b with ⟨t, x, y⟩
  match t, x, y with
  | 0, _, 0 => exact ⟨fun _ => rfl, fun _ => True.intro⟩
  | 0, _, _ + 1 => exact ⟨False.elim, fun h => Bool.noConfusion h⟩
  | 1, _, _ => exact ⟨fun _ => rfl, fun _ => True.intro⟩
  | 2, 0, 0 => exact ⟨fun _ => rfl, fun _ => True.intro⟩
  | 2, 0, _ + 1 => exact ⟨False.elim, fun h => Bool.noConfusion h⟩
  | 2, _ + 1, _ => exact ⟨False.elim, fun h => Bool.noConfusion h⟩
  | _ + 3, _, _ => exact ⟨False.elim, fun h => Bool.noConfusion h⟩

/-- Malformed wire triples (non-zero padding on unary/nullary tags, unknown
tags) are rejected by both `ocDecode` and `ocValidRep`. -/
theorem ocCodec_rejects_malformed :
    ocDecode (0, 7, 1) = none ∧ ocDecode (2, 1, 0) = none ∧
    ocDecode (2, 0, 1) = none ∧ ocDecode (3, 0, 0) = none ∧
    ocDecode (99, 1, 2) = none ∧
    ¬ ocValidRep (0, 7, 1) ∧ ¬ ocValidRep (2, 1, 0) ∧
    ¬ ocValidRep (2, 0, 1) ∧ ¬ ocValidRep (3, 0, 0) ∧
    ¬ ocValidRep (99, 1, 2) :=
  ⟨rfl, rfl, rfl, rfl, rfl, id, id, id, id, id⟩

/-! ## §2. Modes, Cases, Sub-Domains, and the Exact Classification Predicate -/

/-- Anneal-side execution mode. -/
inductive OcFpMode : Type where
  | basic
  | treeBorrows
  deriving DecidableEq, Repr

/-- Tree Borrows flag of a mode (shared convention of `mrOcObserve` and
`lmOcObserve`). -/
def OcFpMode.toTb : OcFpMode → Bool
  | .basic => false
  | .treeBorrows => true

def OcFpMode.ofTb : Bool → OcFpMode
  | false => .basic
  | true => .treeBorrows

theorem OcFpMode.of_toTb (m : OcFpMode) : OcFpMode.ofTb m.toTb = m := by
  cases m <;> rfl

theorem OcFpMode.to_ofTb (b : Bool) : (OcFpMode.ofTb b).toTb = b := by
  cases b <;> rfl

def allTbModes : List Bool := [false, true]

theorem allTbModes_complete (b : Bool) : b ∈ allTbModes := by
  cases b
  · exact List.Mem.head _
  · exact List.Mem.tail _ (List.Mem.head _)

/-- The 22 canonical cases (`0..21`). -/
abbrev OcFpCase : Type := Fin 22

def allOcFpCases : List OcFpCase := List.finRange 22

theorem allOcFpCases_complete (i : OcFpCase) : i ∈ allOcFpCases :=
  List.mem_finRange i

theorem unit_mem_singleton (u : Unit) : u ∈ [()] := by
  cases u; exact List.Mem.head _

/-- The three sub-domains of the frozen matrix. -/
inductive OcFpDomain : Type where
  /-- `0..9`: `ProjectionElem.opaqueCast` across all place contexts. -/
  | d1
  /-- `10..15`: callee-only `FnEntry` protectors (`rust#166253`). -/
  | d2
  /-- `16..21`: machine-backed safe-pointer dereferenceability. -/
  | d3
  deriving DecidableEq, Repr

def ocDomainOf (idx : Nat) : OcFpDomain :=
  if idx < 10 then .d1 else if idx < 16 then .d2 else .d3

/-- Exact cross-authority classification of a case index. -/
inductive OcFpClass : Type where
  /-- Trusted = MiniRust = LeanMiri (`0..7`, `9..21`; 42 cells). -/
  | threeWay
  /-- MiniRust = LeanMiri = `okScalar 5`; Trusted honestly `.unsupported` (`8`). -/
  | castDerefBoundary
  /-- Fail-closed `.unsupported` everywhere (`idx ≥ 22`). -/
  | outOfRange
  deriving DecidableEq, Repr

def ocClassOf (idx : Nat) : OcFpClass :=
  if idx = 8 then .castDerefBoundary
  else if idx < 22 then .threeWay
  else .outOfRange

/-! ## §3. Verdicts of the Real Authorities and Their Frozen Tables -/

/-- Structural translation of an Episode 1 observation into a `Corpus.Verdict`.
Both `phaseBoundary` (static pre-runtime rejection) and `specPanic` (MiniRust
well-formedness panic) map to `none`, keeping `ocVerdictOf` strictly injective
on every non-`none` verdict. -/
def ocVerdictOf : MrOcFpObs → Option (Corpus.Verdict OcFpObs)
  | .okScalar v => some (.returns (.scalar v))
  | .okRetagPair r v => some (.returns (.retagPair r v))
  | .okPtrValid => some (.returns .ptrValid)
  | .ub => some .undefinedBehavior
  | .phaseBoundary => none
  | .unsupported => some .unsupported
  | .specPanic => none

/-- Authority 0: unmodified Trusted `stepMirFn` (via `mrOcTrustedObserve`). -/
def trustedVerdict (tb : Bool) (idx : Nat) : Option (Corpus.Verdict OcFpObs) :=
  ocVerdictOf (mrOcTrustedObserve tb idx)

/-- Authority 1: unmodified MiniRust `d821c6e3` (via `mrOcObserve`). -/
def mrVerdict (tb : Bool) (idx : Nat) : Option (Corpus.Verdict OcFpObs) :=
  ocVerdictOf (mrOcObserve tb idx)

def trustedTable (tb : Bool) : List MrOcFpObs :=
  if tb then mrOcTrustedExpectedTb else mrOcTrustedExpectedBasic

def mrTable (tb : Bool) : List MrOcFpObs :=
  if tb then mrOcExpectedTb else mrOcExpectedBasic

/-- Frozen LeanMiri table for `tb = false` (identical to `lmOcExpectedBasic`,
transcribed into `MrOcFpObs` so this module never imports `LeanMiriSpec.*`;
locked by `Eq.refl` in the cross-root bridge). -/
def ocLmExpectedBasic : List MrOcFpObs :=
  [.okScalar 7, .okScalar 7, .ub, .okScalar 42, .okScalar 9, .ub, .okScalar 1,
   .ub, .okScalar 5, .ub,
   .okRetagPair 5 5, .okRetagPair 5 5, .okRetagPair 4 9, .okRetagPair 5 5,
   .okRetagPair 5 5, .okRetagPair 3 9,
   .okPtrValid, .okPtrValid, .ub, .ub, .ub, .ub]

/-- Frozen LeanMiri table for `tb = true` (only cases `11`, `13`, `14` differ). -/
def ocLmExpectedTb : List MrOcFpObs :=
  [.okScalar 7, .okScalar 7, .ub, .okScalar 42, .okScalar 9, .ub, .okScalar 1,
   .ub, .okScalar 5, .ub,
   .okRetagPair 5 5, .ub, .okRetagPair 4 9, .ub, .ub, .okRetagPair 3 9,
   .okPtrValid, .okPtrValid, .ub, .ub, .ub, .ub]

def lmTable (tb : Bool) : List MrOcFpObs :=
  if tb then ocLmExpectedTb else ocLmExpectedBasic

/-- Cell lookup into a frozen table. -/
def cellOf (l : List MrOcFpObs) (idx : Nat) : Option (Corpus.Verdict OcFpObs) :=
  ocVerdictOf (l.getD idx .unsupported)

theorem range_map_getD {f : Nat → MrOcFpObs} {n idx : Nat} (hi : idx < n) :
    ((List.range n).map f).getD idx .unsupported = f idx := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem trustedTable_eq (tb : Bool) :
    (List.range mrOcCaseCount).map (mrOcTrustedObserve tb) = trustedTable tb := by
  cases tb
  · exact mrOcTrustedObserve_table.1
  · exact mrOcTrustedObserve_table.2

theorem mrTable_eq (tb : Bool) :
    (List.range mrOcCaseCount).map (mrOcObserve tb) = mrTable tb := by
  cases tb
  · exact mrOcObserve_table.1
  · exact mrOcObserve_table.2

/-- Every in-range Trusted verdict is its frozen-table cell (kernel-executed
`stepMirFn`). -/
theorem trustedVerdict_cell (tb : Bool) (idx : Nat) (hi : idx < mrOcCaseCount) :
    trustedVerdict tb idx = cellOf (trustedTable tb) idx := by
  unfold trustedVerdict cellOf
  rw [← trustedTable_eq tb, range_map_getD hi]

/-- Every in-range MiniRust verdict is its frozen-table cell (kernel-executed
`stepM` / `checkPtrM`). -/
theorem mrVerdict_cell (tb : Bool) (idx : Nat) (hi : idx < mrOcCaseCount) :
    mrVerdict tb idx = cellOf (mrTable tb) idx := by
  unfold mrVerdict cellOf
  rw [← mrTable_eq tb, range_map_getD hi]

theorem trustedVerdict_out_of_range (tb : Bool) (idx : Nat)
    (h : mrOcCaseCount ≤ idx) : trustedVerdict tb idx = some .unsupported := by
  unfold trustedVerdict
  rw [mrOcTrustedObserve_out_of_range tb idx h]
  rfl

theorem mrVerdict_out_of_range (tb : Bool) (idx : Nat)
    (h : mrOcCaseCount ≤ idx) : mrVerdict tb idx = some .unsupported := by
  unfold mrVerdict
  rw [mrOcObserve_out_of_range tb idx h]
  rfl

/-! ## §4. Parameterized LeanMiri Authority Interface (`OcFpLmAuthority`) -/

/-- A LeanMiri observation authority presented through its own observation
type: the cross-root bridge instantiates
`Obs := LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.LmOcFpObs`,
`observe := lmOcObserve`, and `toVerdict` by `LmOcFpObs.rec`. -/
structure OcFpLmAuthority : Type 1 where
  Obs : Type
  observe : Bool → Nat → Obs
  toVerdict : Obs → Option (Corpus.Verdict OcFpObs)

/-- The verdict of a LeanMiri authority on `(tb, idx)`. -/
def OcFpLmAuthority.verdict (A : OcFpLmAuthority) (tb : Bool) (idx : Nat) :
    Option (Corpus.Verdict OcFpObs) :=
  A.toVerdict (A.observe tb idx)

/-- 44-cell validity certificate: every in-range verdict of `A` equals the
frozen LeanMiri table. -/
def lmTableCheckOf (A : OcFpLmAuthority) : Bool :=
  allTbModes.all fun tb => (List.range mrOcCaseCount).all fun idx =>
    decide (A.verdict tb idx = cellOf (lmTable tb) idx)

/-- Fail-closed obligation of a LeanMiri authority outside the canonical
range (`idx ≥ 22`). -/
def OcFpLmFailClosed (A : OcFpLmAuthority) : Prop :=
  ∀ tb idx, mrOcCaseCount ≤ idx → A.verdict tb idx = some .unsupported

theorem lmTableCheckOf_sound (A : OcFpLmAuthority) (hA : lmTableCheckOf A = true)
    (tb : Bool) (idx : Nat) (hi : idx < mrOcCaseCount) :
    A.verdict tb idx = cellOf (lmTable tb) idx := by
  have h₁ := List.all_eq_true.mp hA tb (allTbModes_complete tb)
  exact of_decide_eq_true (List.all_eq_true.mp h₁ idx (List.mem_range.mpr hi))

/-- Certificates transport along equal authorities (used to move the
kernel-evaluated certificate of the loop-unrolled twin `lmOcObserveU` to the
real `lmOcObserve` via `lmOcObserveU.eq_src`). -/
theorem lmTableCheckOf_of_eq {A B : OcFpLmAuthority} (h : A = B)
    (hB : lmTableCheckOf B = true) : lmTableCheckOf A = true :=
  h ▸ hB

/-- Side certificates transport along equal authorities (moves a certificate
kernel-evaluated on the loop-unrolled twin directly onto `lmOcObserve`). -/
theorem cert_transport {A B : OcFpLmAuthority} (h : A = B)
    (p : OcFpLmAuthority → Bool) (hB : p B = true) : p A = true :=
  h ▸ hB

/-! ## §5. The Anneal Corpus Model and the MiniRust / LeanMiri Sides -/

/-- Direct Trusted Anneal execution on every `(mode, case)` key. -/
def ocAnnealEval (m : OcFpMode) (i : OcFpCase) (_q : Unit) (_c : Unit) :
    Option (Corpus.Verdict OcFpObs) :=
  trustedVerdict m.toTb i.val

def ocExpectedAnnealEval (m : OcFpMode) (i : OcFpCase) (_q : Unit) (_c : Unit) :
    Option (Corpus.Verdict OcFpObs) :=
  cellOf (trustedTable m.toTb) i.val

theorem ocAnnealEval_funext : ocAnnealEval = ocExpectedAnnealEval :=
  funext fun m => funext fun i => funext fun _ => funext fun _ =>
    trustedVerdict_cell m.toTb i.val i.isLt

/-- The Anneal corpus model for an arbitrary evaluation function. -/
def ocModelOf
    (evalA : OcFpMode → OcFpCase → Unit → Unit → Option (Corpus.Verdict OcFpObs)) :
    Corpus.Model OcFpMode OcFpCase Unit Unit OcFpObs OcFpObsRep where
  evalA := evalA
  codec := ocCodec
  progs := allOcFpCases
  queries := [()]
  choices := [()]
  progs_complete := allOcFpCases_complete
  queries_complete := unit_mem_singleton
  choices_complete := unit_mem_singleton

/-- The Anneal corpus model evaluated by real Trusted `stepMirFn`. -/
def ocModel : Corpus.Model OcFpMode OcFpCase Unit Unit OcFpObs OcFpObsRep :=
  ocModelOf ocAnnealEval

/-- Optional sub-domain selector (`none` = unified bundle). -/
def domainSel : Option OcFpDomain → OcFpCase → Bool
  | none, _ => true
  | some d, i => ocDomainOf i.val == d

/-- MiniRust support gate: exact 3-way cases of the selected sub-domain
(excludes only case `8`, where Trusted is `.unsupported`). -/
def mrGate (sel : Option OcFpDomain) (i : OcFpCase) : Bool :=
  ocClassOf i.val == .threeWay && domainSel sel i

/-- LeanMiri support gate: exact 3-way cases of the selected sub-domain
(identical to `mrGate` since MiniRust and LeanMiri agree on all 44 cells and
both diverge from Trusted solely at case `8`). -/
def lmGate (sel : Option OcFpDomain) (i : OcFpCase) : Bool :=
  ocClassOf i.val == .threeWay && domainSel sel i

/-- Witness mode of each selection (`treeBorrows` for `D2` so its fault witness
case `11` genuinely hits Tree Borrows UB; `basic` elsewhere). -/
def wModeOf : Option OcFpDomain → Bool
  | some .d2 => true
  | _ => false

/-- Positive witness case of each selection. -/
def okCaseOf : Option OcFpDomain → OcFpCase
  | none => 0
  | some .d1 => 0
  | some .d2 => 10
  | some .d3 => 16

/-- Fault witness case of each selection (every witness is genuine `.undefined`
UB, never `.unsupported`). -/
def faultCaseOf : Option OcFpDomain → OcFpCase
  | none => 2
  | some .d1 => 2
  | some .d2 => 11
  | some .d3 => 18

/-- Tree Borrows mode-sensitivity flip witness (case `11`: pre-`#166253`
caller-retag `okRetagPair 5 5` in `basic`, UB in `treeBorrows`) carried on the
unified and `D2` selections. -/
def flipOf : Option OcFpDomain → Option (Bool × Bool × OcFpCase × Unit × Unit)
  | none => some (false, true, 11, (), ())
  | some .d2 => some (false, true, 11, (), ())
  | some _ => none

/-- A corpus side over an arbitrary gate and reference verdict function. -/
def sideOf (sel : Option OcFpDomain) (gate : Option OcFpDomain → OcFpCase → Bool)
    (verdictR : Bool → OcFpCase → Option (Corpus.Verdict OcFpObs)) :
    Corpus.Side OcFpMode Bool OcFpCase Unit Unit OcFpObs OcFpObsRep where
  toAnneal := OcFpMode.ofTb
  gate := fun _ i _ => gate sel i
  verdictR := fun tb i _ _ => verdictR tb i
  rep := ocEncode
  modes := allTbModes
  modes_complete := allTbModes_complete
  wMode := wModeOf sel
  okProg := okCaseOf sel
  okQuery := ()
  okChoice := ()
  faultProg := faultCaseOf sel
  faultQuery := ()
  faultChoice := ()
  flip := flipOf sel

def mrVerdictFn (tb : Bool) (i : OcFpCase) : Option (Corpus.Verdict OcFpObs) :=
  mrVerdict tb i.val

def mrExpectedFn (tb : Bool) (i : OcFpCase) : Option (Corpus.Verdict OcFpObs) :=
  cellOf (mrTable tb) i.val

theorem mrVerdictFn_funext : mrVerdictFn = mrExpectedFn :=
  funext fun tb => funext fun i => mrVerdict_cell tb i.val i.isLt

/-- MiniRust side of selection `sel`, directly over `mrOcObserve`. -/
def mrSide (sel : Option OcFpDomain) :
    Corpus.Side OcFpMode Bool OcFpCase Unit Unit OcFpObs OcFpObsRep :=
  sideOf sel mrGate mrVerdictFn

/-- MiniRust certificates for the unified and all three per-domain sides. -/
theorem mrSide_check (sel : Option OcFpDomain) : (mrSide sel).check ocModel = true := by
  show (sideOf sel mrGate mrVerdictFn).check (ocModelOf ocAnnealEval) = true
  rw [ocAnnealEval_funext, mrVerdictFn_funext]
  cases sel with
  | none => decide +kernel
  | some d => cases d <;> decide +kernel

def lmVerdictFn (A : OcFpLmAuthority) (tb : Bool) (i : OcFpCase) :
    Option (Corpus.Verdict OcFpObs) :=
  A.verdict tb i.val

def lmExpectedFn (tb : Bool) (i : OcFpCase) : Option (Corpus.Verdict OcFpObs) :=
  cellOf (lmTable tb) i.val

theorem lmVerdictFn_funext (A : OcFpLmAuthority) (hA : lmTableCheckOf A = true) :
    lmVerdictFn A = lmExpectedFn :=
  funext fun tb => funext fun i => lmTableCheckOf_sound A hA tb i.val i.isLt

/-- LeanMiri side of selection `sel` over an arbitrary `OcFpLmAuthority`. -/
def lmSideOf (sel : Option OcFpDomain) (A : OcFpLmAuthority) :
    Corpus.Side OcFpMode Bool OcFpCase Unit Unit OcFpObs OcFpObsRep :=
  sideOf sel lmGate (lmVerdictFn A)

/-- LeanMiri side certificate of selection `sel`. -/
def lmCheckOf (sel : Option OcFpDomain) (A : OcFpLmAuthority) : Bool :=
  (lmSideOf sel A).check ocModel

/-- The 44-cell table certificate implies every LeanMiri side certificate. -/
theorem lmCheckOf_of_table (sel : Option OcFpDomain) (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) : lmCheckOf sel A = true := by
  show (sideOf sel lmGate (lmVerdictFn A)).check (ocModelOf ocAnnealEval) = true
  rw [ocAnnealEval_funext, lmVerdictFn_funext A hA]
  cases sel with
  | none => decide +kernel
  | some d => cases d <;> decide +kernel

/-! ## §6. Genuine `DualCorrespondenceBundle` Witnesses (Unified + `D1`–`D3`) -/

/-- The bundle type shared by all four witnesses (unified + `D1`–`D3`). -/
abbrev OcFpBundle : Type :=
  DualCorrespondenceBundle OcFpMode OcFpCase Unit OcFpObs Unit OcFpObsRep
    Bool Unit OcFpObs Unit Bool Unit OcFpObs Unit

/-- Bundle of selection `sel` from a side certificate. -/
def bundleOfSel (sel : Option OcFpDomain) (A : OcFpLmAuthority)
    (hLM : lmCheckOf sel A = true) : OcFpBundle :=
  Corpus.bundle ocModel (mrSide sel) (lmSideOf sel A) (mrSide_check sel) hLM

/-- **Unified bundle**: both MiniRust and LeanMiri gated on the 21 three-way
cases × 2 modes (`0..7`, `9..21`), excluding only case `8`. -/
def bundleOf (A : OcFpLmAuthority) (hA : lmTableCheckOf A = true) : OcFpBundle :=
  bundleOfSel none A (lmCheckOf_of_table none A hA)

/-- **Per-domain bundle** for `D1`–`D3`. -/
def domainBundleOf (d : OcFpDomain) (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) : OcFpBundle :=
  bundleOfSel (some d) A (lmCheckOf_of_table (some d) A hA)

theorem mrGate_of_threeWay (sel : Option OcFpDomain) (i : OcFpCase)
    (h : ocClassOf i.val = .threeWay) (hd : domainSel sel i = true) :
    mrGate sel i = true := by
  unfold mrGate; rw [h, hd]; rfl

theorem lmGate_of_threeWay (sel : Option OcFpDomain) (i : OcFpCase)
    (h : ocClassOf i.val = .threeWay) (hd : domainSel sel i = true) :
    lmGate sel i = true := by
  unfold lmGate; rw [h, hd]; rfl

/-- Three-way normal agreement (Trusted ↔ MiniRust ↔ LeanMiri) at every 3-way
key of the unified bundle. -/
theorem threeWayNormalAgreement (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) (mMR mLM : Bool) (i : OcFpCase)
    (hMode : OcFpMode.ofTb mMR = OcFpMode.ofTb mLM)
    (hCls : ocClassOf i.val = .threeWay) (vMR vLM : OcFpObs)
    (hRMR : (bundleOf A hA).mrRel.ExecR mMR i () () (.normal vMR))
    (hRLM : (bundleOf A hA).lmRel.ExecR mLM i () () (.normal vLM)) :
    ocEncode vMR = ocEncode vLM ∧
      ∃ a : OcFpObs, ocDecode (ocEncode vMR) = some a ∧
        (bundleOf A hA).ExecAnneal (OcFpMode.ofTb mMR) i () (.normal a) := by
  have hDet : ∀ out out',
      (bundleOf A hA).ExecAnneal ((bundleOf A hA).toAnnealMR mMR) i () out →
      (bundleOf A hA).ExecAnneal ((bundleOf A hA).toAnnealMR mMR) i () out' →
      out = out' := by
    rintro out out' ⟨⟨⟩, h1⟩ ⟨⟨⟩, h2⟩
    exact Option.some.inj (h1.symm.trans h2)
  exact (bundleOf A hA).threeWayNormalAgreement_rep hMode
    (mrGate_of_threeWay none i hCls rfl) (lmGate_of_threeWay none i hCls rfl)
    hDet hRMR hRLM

/-- Cross-authority fault equivalence between MiniRust and LeanMiri at every
3-way key. -/
theorem crossAuthorityFaultEquiv (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) (mMR mLM : Bool) (i : OcFpCase)
    (hMode : OcFpMode.ofTb mMR = OcFpMode.ofTb mLM)
    (hCls : ocClassOf i.val = .threeWay) (k : CorrFaultKind) :
    (∃ c, (bundleOf A hA).mrRel.ExecR mMR i () c (.fault k)) ↔
      (∃ c, (bundleOf A hA).lmRel.ExecR mLM i () c (.fault k)) :=
  (bundleOf A hA).crossAuthorityFaultEquiv hMode
    (mrGate_of_threeWay none i hCls rfl) (lmGate_of_threeWay none i hCls rfl) k

/-- Exact behavioral equivalence on both authorities (reverse totality of both
sides) at every 3-way key. -/
theorem exactBehaviorEq_both (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) (mMR mLM : Bool) (i : OcFpCase)
    (hCls : ocClassOf i.val = .threeWay) :
    ExactBehaviorEq (bundleOf A hA).mrRel mMR i () ∧
    ExactBehaviorEq (bundleOf A hA).lmRel mLM i () :=
  ⟨(bundleOf A hA).mrSim.exactBehaviorEq_of_reverseTotal
      ((mrSide none).reverseTotal ocModel
        (Bool.and_eq_true _ _ ▸ mrSide_check none).1)
      (mrGate_of_threeWay none i hCls rfl),
   (bundleOf A hA).lmSim.exactBehaviorEq_of_reverseTotal
      ((lmSideOf none A).reverseTotal ocModel
        (Bool.and_eq_true _ _ ▸ lmCheckOf_of_table none A hA).1)
      (lmGate_of_threeWay none i hCls rfl)⟩

/-- Positive projection of the unified bundle onto the Anneal model. -/
theorem projectPositive (A : OcFpLmAuthority) (hA : lmTableCheckOf A = true) :
    type_of% (bundleOf A hA).projectPositive :=
  (bundleOf A hA).projectPositive

/-- Fault projection of the unified bundle onto the Anneal model. -/
theorem projectFault (A : OcFpLmAuthority) (hA : lmTableCheckOf A = true) :
    type_of% (bundleOf A hA).projectFault :=
  (bundleOf A hA).projectFault

/-- Non-vacuous Tree Borrows mode-sensitivity witnesses (case `11`, `basic` vs
`treeBorrows`) carried directly by `(bundleOf A hA)` and `(domainBundleOf .d2 A
hA)` on BOTH authorities, while `D1` and `D3` carry `none`. -/
theorem modeSensitivity_present (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) :
    (∃ w, (bundleOf A hA).mrFlip.modeSensitivity? = some w ∧
      w.m₁ = false ∧ w.m₂ = true ∧ w.p = 11) ∧
    (∃ w, (bundleOf A hA).lmFlip.modeSensitivity? = some w ∧
      w.m₁ = false ∧ w.m₂ = true ∧ w.p = 11) ∧
    (∃ w, (domainBundleOf .d2 A hA).mrFlip.modeSensitivity? = some w ∧
      w.m₁ = false ∧ w.m₂ = true ∧ w.p = 11) ∧
    (∃ w, (domainBundleOf .d2 A hA).lmFlip.modeSensitivity? = some w ∧
      w.m₁ = false ∧ w.m₂ = true ∧ w.p = 11) ∧
    (domainBundleOf .d1 A hA).mrFlip.modeSensitivity? = none ∧
    (domainBundleOf .d1 A hA).lmFlip.modeSensitivity? = none ∧
    (domainBundleOf .d3 A hA).mrFlip.modeSensitivity? = none ∧
    (domainBundleOf .d3 A hA).lmFlip.modeSensitivity? = none := by
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- Exact support-gate encoding of the honest Trusted `D1` deref-below-cast
boundary (case `8` excluded from both `mrGate` and `lmGate` on unified and `D1`,
while every `D2` and `D3` case is included with `ExactBehaviorEq`). -/
theorem bundle_gate_castDerefBoundary (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) :
    mrGate none 8 = false ∧ lmGate none 8 = false ∧
    mrGate (some .d1) 8 = false ∧ lmGate (some .d1) 8 = false ∧
    (∀ (i : OcFpCase), i.val ≠ 8 →
      mrGate none i = true ∧ lmGate none i = true ∧
      (∀ mMR mLM : Bool,
        ExactBehaviorEq (bundleOf A hA).mrRel mMR i () ∧
        ExactBehaviorEq (bundleOf A hA).lmRel mLM i ())) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i hne
  have hCls : ocClassOf i.val = .threeWay := by
    unfold ocClassOf
    rw [ite_eq_right_of_eq_false _ _ (eq_false hne),
      ite_eq_left_of_eq_true _ _ (eq_true i.isLt)]
  refine ⟨mrGate_of_threeWay none i hCls rfl, lmGate_of_threeWay none i hCls rfl,
    fun mMR mLM => exactBehaviorEq_both A hA mMR mLM i hCls⟩

/-- Witness polarity and fault-kind pinning on the unified bundle: positive
witness is case `0` and fault witness is genuine `.undefined` UB (case `2`),
never `.unsupported`. -/
theorem unified_bundle_witness_kinds (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) :
    let B := bundleOf A hA
    B.mrPositive.p = 0 ∧ B.lmPositive.p = 0 ∧
    B.mrFault.p = 2 ∧ B.lmFault.p = 2 ∧
    B.mrFault.kind = .undefined ∧ B.lmFault.kind = .undefined ∧
    B.mrFlip.kind = .undefined ∧ B.lmFlip.kind = .undefined :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every per-domain bundle (`D1`–`D3`) carries genuine correspondence and
fault-equivalence claims plus non-vacuous flip-direction guards (positive and
genuine `.undefined` UB fault witnesses) on BOTH authorities. -/
theorem domain_bundle_claims (d : OcFpDomain) (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) :
    let B := domainBundleOf d A hA
    CorrespondenceClaim B.mrRel ∧ FaultEquivClaim B.mrRel ∧
    CorrespondenceClaim B.lmRel ∧ FaultEquivClaim B.lmRel ∧
    B.mrPositive.p = okCaseOf (some d) ∧ B.lmPositive.p = okCaseOf (some d) ∧
    B.mrFault.p = faultCaseOf (some d) ∧ B.lmFault.p = faultCaseOf (some d) ∧
    B.mrFault.kind = .undefined ∧ B.lmFault.kind = .undefined ∧
    B.mrFlip.pOk = okCaseOf (some d) ∧ B.mrFlip.pFault = faultCaseOf (some d) ∧
    B.mrFlip.kind = .undefined ∧
    B.lmFlip.pOk = okCaseOf (some d) ∧ B.lmFlip.pFault = faultCaseOf (some d) ∧
    B.lmFlip.kind = .undefined ∧
    (∃ a r, B.mrRel.ExecA B.mrFlip.m B.mrFlip.pOk B.mrFlip.qOk B.mrFlip.cOk
              (.normal a) ∧
            B.mrRel.ExecR B.mrFlip.m B.mrFlip.pOk B.mrFlip.qOk B.mrFlip.cOk
              (.normal r) ∧
            B.mrRel.RetRel a r) ∧
    B.mrRel.ExecA B.mrFlip.m B.mrFlip.pFault B.mrFlip.qFault B.mrFlip.cFault
      (.fault B.mrFlip.kind) ∧
    B.mrRel.ExecR B.mrFlip.m B.mrFlip.pFault B.mrFlip.qFault B.mrFlip.cFault
      (.fault B.mrFlip.kind) ∧
    (∃ a r, B.lmRel.ExecA B.lmFlip.m B.lmFlip.pOk B.lmFlip.qOk B.lmFlip.cOk
              (.normal a) ∧
            B.lmRel.ExecR B.lmFlip.m B.lmFlip.pOk B.lmFlip.qOk B.lmFlip.cOk
              (.normal r) ∧
            B.lmRel.RetRel a r) ∧
    B.lmRel.ExecA B.lmFlip.m B.lmFlip.pFault B.lmFlip.qFault B.lmFlip.cFault
      (.fault B.lmFlip.kind) ∧
    B.lmRel.ExecR B.lmFlip.m B.lmFlip.pFault B.lmFlip.qFault B.lmFlip.cFault
      (.fault B.lmFlip.kind) := by
  have hKind : ∀ d' : OcFpDomain,
      Corpus.faultKindOf
        (trustedVerdict (OcFpMode.ofTb (wModeOf (some d'))).toTb
          (faultCaseOf (some d')).val) = .undefined := by
    intro d'
    rw [trustedVerdict_cell _ _ (faultCaseOf (some d')).isLt]
    cases d' <;> rfl
  have hk : ∀ d' : OcFpDomain,
      (domainBundleOf d' A hA).mrFault.kind = .undefined ∧
      (domainBundleOf d' A hA).lmFault.kind = .undefined ∧
      (domainBundleOf d' A hA).mrFlip.kind = .undefined ∧
      (domainBundleOf d' A hA).lmFlip.kind = .undefined :=
    fun d' => ⟨hKind d', hKind d', hKind d', hKind d'⟩
  exact ⟨(domainBundleOf d A hA).mrSim.correspondenceClaim,
   (domainBundleOf d A hA).mrSim.faultEquivClaim,
   (domainBundleOf d A hA).lmSim.correspondenceClaim,
   (domainBundleOf d A hA).lmSim.faultEquivClaim,
   rfl, rfl, rfl, rfl,
   (hk d).1, (hk d).2.1,
   rfl, rfl, (hk d).2.2.1,
   rfl, rfl, (hk d).2.2.2,
   (domainBundleOf d A hA).mrFlip.okAgree,
   (domainBundleOf d A hA).mrFlip.faultA,
   (domainBundleOf d A hA).mrFlip.faultR,
   (domainBundleOf d A hA).lmFlip.okAgree,
   (domainBundleOf d A hA).lmFlip.faultA,
   (domainBundleOf d A hA).lmFlip.faultR⟩

/-! ## §7. Exact 44-Cell Classification, Observer-Level Agreement, and Domain Lifts -/

/-- **Exact 3-way classification `↔`** (every in-range cell, both modes): full
agreement iff `threeWay`; MiniRust = LeanMiri with Trusted `.unsupported` iff
`castDerefBoundary` (`8`); and MiniRust = LeanMiri on all 44 in-range cells. -/
theorem dual_exact_three_way_classification (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) (tb : Bool) (idx : Nat)
    (hi : idx < mrOcCaseCount) :
    ((trustedVerdict tb idx = mrVerdict tb idx ∧
        mrVerdict tb idx = A.verdict tb idx) ↔ ocClassOf idx = .threeWay) ∧
    ((trustedVerdict tb idx = some .unsupported ∧
        mrVerdict tb idx ≠ some .unsupported ∧
        mrVerdict tb idx = A.verdict tb idx) ↔
        ocClassOf idx = .castDerefBoundary) ∧
    mrVerdict tb idx = A.verdict tb idx := by
  rw [trustedVerdict_cell tb idx hi, mrVerdict_cell tb idx hi,
    lmTableCheckOf_sound A hA tb idx hi]
  revert hi
  revert idx
  cases tb <;> decide +kernel

/-- **Zero `specPanic` / `phaseBoundary` / stuck cells across all 44 in-range
cells** on all three authorities (ensuring `dual_exact_three_way_classification`
never holds vacuously via `none = none`). -/
theorem dual_no_specPanic_all_cells (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) (tb : Bool) (idx : Nat)
    (hi : idx < mrOcCaseCount) :
    trustedVerdict tb idx ≠ none ∧ mrVerdict tb idx ≠ none ∧
    A.verdict tb idx ≠ none ∧ ocClassOf idx ≠ .outOfRange := by
  rw [trustedVerdict_cell tb idx hi, mrVerdict_cell tb idx hi,
    lmTableCheckOf_sound A hA tb idx hi]
  revert hi
  revert idx
  cases tb <;> decide +kernel

/-- `ocVerdictOf` is injective away from `none` (`phaseBoundary` and
`specPanic` are the only observations without a verdict). -/
theorem ocVerdictOf_injective {a b : MrOcFpObs}
    (h : ocVerdictOf a = ocVerdictOf b) (hne : ocVerdictOf a ≠ none) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact absurd rfl hne
    | (cases h; rfl)
    | cases h

/-- The frozen LeanMiri table agrees cell-for-cell with the MiniRust table on
all 44 cells, agrees with Trusted off `castDerefBoundary` (`8`), and has no
verdict-less cell. -/
theorem lmTable_vs_tables (tb : Bool) (idx : Nat) (hi : idx < mrOcCaseCount) :
    cellOf (lmTable tb) idx = cellOf (mrTable tb) idx ∧
    (ocClassOf idx ≠ .castDerefBoundary →
      cellOf (lmTable tb) idx = cellOf (trustedTable tb) idx) ∧
    cellOf (lmTable tb) idx ≠ none := by
  revert hi
  revert idx
  cases tb <;> decide +kernel

/-- **Observer-level (raw `MrOcFpObs`) 3-way agreement.** For any certified
authority whose translation factors as `ocVerdictOf ∘ f` through
`f : A.Obs → MrOcFpObs`, the raw translated observation equals `mrOcObserve` on
EVERY in-range cell (`0..21`), and equals `mrOcTrustedObserve` on every
non-boundary cell (`idx ≠ 8`). -/
theorem observer_level_three_way (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) (f : A.Obs → MrOcFpObs)
    (hf : ∀ o, A.toVerdict o = ocVerdictOf (f o)) (tb : Bool) (idx : Nat)
    (hi : idx < mrOcCaseCount) :
    f (A.observe tb idx) = mrOcObserve tb idx ∧
    (ocClassOf idx ≠ .castDerefBoundary →
      f (A.observe tb idx) = mrOcTrustedObserve tb idx) := by
  have hTab := lmTable_vs_tables tb idx hi
  have hL : ocVerdictOf (f (A.observe tb idx)) = cellOf (lmTable tb) idx :=
    (hf _).symm.trans (lmTableCheckOf_sound A hA tb idx hi)
  have hne : ocVerdictOf (f (A.observe tb idx)) ≠ none := hL ▸ hTab.2.2
  refine ⟨ocVerdictOf_injective ?_ hne, fun h => ocVerdictOf_injective ?_ hne⟩
  · exact hL.trans (hTab.1.trans (mrVerdict_cell tb idx hi).symm)
  · exact hL.trans ((hTab.2.1 h).trans (trustedVerdict_cell tb idx hi).symm)

/-- **Unconditional all-`Nat` observer-level `↔` classification.** For EVERY
`tb : Bool` and EVERY `idx : Nat` (canonical `0..21` and fail-closed `≥ 22`),
a certified fail-closed authority factoring as `ocVerdictOf ∘ f` agrees with
raw `mrOcObserve` unconditionally, agrees with raw `mrOcTrustedObserve` iff
`idx ≠ 8`, and enjoys full 3-way raw-observer agreement iff `idx ≠ 8`. -/
theorem observer_level_exact_all_nat (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) (hOob : OcFpLmFailClosed A)
    (f : A.Obs → MrOcFpObs) (hf : ∀ o, A.toVerdict o = ocVerdictOf (f o))
    (tb : Bool) (idx : Nat) :
    f (A.observe tb idx) = mrOcObserve tb idx ∧
    (f (A.observe tb idx) = mrOcTrustedObserve tb idx ↔ idx ≠ 8) ∧
    ((mrOcTrustedObserve tb idx = mrOcObserve tb idx ∧
        mrOcObserve tb idx = f (A.observe tb idx)) ↔ idx ≠ 8) := by
  by_cases hi : idx < mrOcCaseCount
  · have hObs := observer_level_three_way A hA f hf tb idx hi
    have hCls := dual_exact_three_way_classification A hA tb idx hi
    have hNe8 : f (A.observe tb idx) = mrOcTrustedObserve tb idx → idx ≠ 8 := by
      intro heq h8
      subst h8
      have hv : A.verdict tb 8 = trustedVerdict tb 8 := by
        show A.toVerdict (A.observe tb 8) = ocVerdictOf (mrOcTrustedObserve tb 8)
        rw [hf, heq]
      have hBnd := hCls.2.1.mpr (by decide : ocClassOf 8 = .castDerefBoundary)
      exact hBnd.2.1 (hBnd.2.2.trans (hv.trans hBnd.1))
    have hOfNe8 : idx ≠ 8 → f (A.observe tb idx) = mrOcTrustedObserve tb idx := by
      intro h8
      apply hObs.2
      unfold ocClassOf
      have hi22 : idx < 22 := hi
      rw [ite_eq_right_of_eq_false _ _ (eq_false h8),
        ite_eq_left_of_eq_true _ _ (eq_true hi22)]
      decide
    refine ⟨hObs.1, ⟨hNe8, hOfNe8⟩, ?_⟩
    constructor
    · rintro ⟨hTM, hML⟩
      exact hNe8 (hML.symm.trans hTM.symm)
    · intro h8
      have hLT := hOfNe8 h8
      exact ⟨hLT.symm.trans hObs.1, hObs.1.symm⟩
  · have hge : mrOcCaseCount ≤ idx := Nat.le_of_not_lt hi
    have hMr : mrOcObserve tb idx = .unsupported :=
      mrOcObserve_out_of_range tb idx hge
    have hTr : mrOcTrustedObserve tb idx = .unsupported :=
      mrOcTrustedObserve_out_of_range tb idx hge
    have hLmV : ocVerdictOf (f (A.observe tb idx)) = ocVerdictOf .unsupported :=
      (hf _).symm.trans (hOob tb idx hge)
    have hLm : f (A.observe tb idx) = .unsupported :=
      ocVerdictOf_injective hLmV (by rw [hLmV]; decide)
    have h8 : idx ≠ 8 := by unfold mrOcCaseCount at hge; omega
    refine ⟨hLm.trans hMr.symm,
      ⟨fun _ => h8, fun _ => hLm.trans hTr.symm⟩,
      ⟨fun _ => h8, fun _ => ⟨hTr.trans hMr.symm, hMr.trans hLm.symm⟩⟩⟩

/-- **Fail-closed `idx ≥ 22`** on all three authorities. -/
theorem dual_fail_closed_out_of_range (A : OcFpLmAuthority)
    (hOob : OcFpLmFailClosed A) (tb : Bool) (idx : Nat)
    (h : mrOcCaseCount ≤ idx) :
    trustedVerdict tb idx = some .unsupported ∧
    mrVerdict tb idx = some .unsupported ∧
    A.verdict tb idx = some .unsupported ∧
    ocClassOf idx = .outOfRange := by
  refine ⟨trustedVerdict_out_of_range tb idx h, mrVerdict_out_of_range tb idx h,
    hOob tb idx h, ?_⟩
  unfold mrOcCaseCount at h
  have h1 : ¬ idx = 8 := by omega
  have h2 : ¬ idx < 22 := by omega
  unfold ocClassOf
  rw [ite_eq_right_of_eq_false _ _ (eq_false h1),
    ite_eq_right_of_eq_false _ _ (eq_false h2)]

/-- **Exact Tree Borrows mode sensitivity on all three authorities**: `tb = false`
and `tb = true` disagree on an in-range case iff `idx ∈ {11, 13, 14}`
(`ocCaseModeSensitive idx = true`). -/
theorem dual_mode_sensitivity_exact (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) (idx : Nat) (hi : idx < mrOcCaseCount) :
    (trustedVerdict false idx ≠ trustedVerdict true idx ↔
      ocCaseModeSensitive idx = true) ∧
    (mrVerdict false idx ≠ mrVerdict true idx ↔
      ocCaseModeSensitive idx = true) ∧
    (A.verdict false idx ≠ A.verdict true idx ↔
      ocCaseModeSensitive idx = true) := by
  rw [trustedVerdict_cell false idx hi, trustedVerdict_cell true idx hi,
    mrVerdict_cell false idx hi, mrVerdict_cell true idx hi,
    lmTableCheckOf_sound A hA false idx hi, lmTableCheckOf_sound A hA true idx hi]
  revert hi
  revert idx
  decide +kernel

/-- **`D2` concrete pinning of all 6 cases (`10..15`) on all three authorities**,
highlighting the `rust#166253` callee-only (`10`: succeeds in BOTH modes) vs
pre-`#166253` caller-signature (`11`: `basic` OK, Tree Borrows UB) contrast,
the direct `&mut u8` (`12` OK / `13` flip) and `&u8` (`14` flip / `15` OK)
cases, and the exact mode-sensitive subset `{11, 13, 14}`. -/
theorem dual_d2_mode_sensitivity_all_three (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) :
    (∀ tb, trustedVerdict tb 10 = some (.returns (.retagPair 5 5)) ∧
      mrVerdict tb 10 = some (.returns (.retagPair 5 5)) ∧
      A.verdict tb 10 = some (.returns (.retagPair 5 5))) ∧
    (trustedVerdict false 11 = some (.returns (.retagPair 5 5)) ∧
      trustedVerdict true 11 = some .undefinedBehavior ∧
      mrVerdict false 11 = some (.returns (.retagPair 5 5)) ∧
      mrVerdict true 11 = some .undefinedBehavior ∧
      A.verdict false 11 = some (.returns (.retagPair 5 5)) ∧
      A.verdict true 11 = some .undefinedBehavior) ∧
    (∀ tb, trustedVerdict tb 12 = some (.returns (.retagPair 4 9)) ∧
      mrVerdict tb 12 = some (.returns (.retagPair 4 9)) ∧
      A.verdict tb 12 = some (.returns (.retagPair 4 9))) ∧
    (trustedVerdict false 13 = some (.returns (.retagPair 5 5)) ∧
      trustedVerdict true 13 = some .undefinedBehavior ∧
      mrVerdict false 13 = some (.returns (.retagPair 5 5)) ∧
      mrVerdict true 13 = some .undefinedBehavior ∧
      A.verdict false 13 = some (.returns (.retagPair 5 5)) ∧
      A.verdict true 13 = some .undefinedBehavior) ∧
    (trustedVerdict false 14 = some (.returns (.retagPair 5 5)) ∧
      trustedVerdict true 14 = some .undefinedBehavior ∧
      mrVerdict false 14 = some (.returns (.retagPair 5 5)) ∧
      mrVerdict true 14 = some .undefinedBehavior ∧
      A.verdict false 14 = some (.returns (.retagPair 5 5)) ∧
      A.verdict true 14 = some .undefinedBehavior) ∧
    (∀ tb, trustedVerdict tb 15 = some (.returns (.retagPair 3 9)) ∧
      mrVerdict tb 15 = some (.returns (.retagPair 3 9)) ∧
      A.verdict tb 15 = some (.returns (.retagPair 3 9))) ∧
    (trustedVerdict true 10 ≠ trustedVerdict true 11 ∧
      mrVerdict true 10 ≠ mrVerdict true 11 ∧
      A.verdict true 10 ≠ A.verdict true 11) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tb
    rw [trustedVerdict_cell tb 10 (by decide), mrVerdict_cell tb 10 (by decide),
      lmTableCheckOf_sound A hA tb 10 (by decide)]
    cases tb <;> exact ⟨rfl, rfl, rfl⟩
  · rw [trustedVerdict_cell false 11 (by decide), trustedVerdict_cell true 11 (by decide),
      mrVerdict_cell false 11 (by decide), mrVerdict_cell true 11 (by decide),
      lmTableCheckOf_sound A hA false 11 (by decide),
      lmTableCheckOf_sound A hA true 11 (by decide)]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro tb
    rw [trustedVerdict_cell tb 12 (by decide), mrVerdict_cell tb 12 (by decide),
      lmTableCheckOf_sound A hA tb 12 (by decide)]
    cases tb <;> exact ⟨rfl, rfl, rfl⟩
  · rw [trustedVerdict_cell false 13 (by decide), trustedVerdict_cell true 13 (by decide),
      mrVerdict_cell false 13 (by decide), mrVerdict_cell true 13 (by decide),
      lmTableCheckOf_sound A hA false 13 (by decide),
      lmTableCheckOf_sound A hA true 13 (by decide)]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [trustedVerdict_cell false 14 (by decide), trustedVerdict_cell true 14 (by decide),
      mrVerdict_cell false 14 (by decide), mrVerdict_cell true 14 (by decide),
      lmTableCheckOf_sound A hA false 14 (by decide),
      lmTableCheckOf_sound A hA true 14 (by decide)]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro tb
    rw [trustedVerdict_cell tb 15 (by decide), mrVerdict_cell tb 15 (by decide),
      lmTableCheckOf_sound A hA tb 15 (by decide)]
    cases tb <;> exact ⟨rfl, rfl, rfl⟩
  · rw [trustedVerdict_cell true 10 (by decide), trustedVerdict_cell true 11 (by decide),
      mrVerdict_cell true 10 (by decide), mrVerdict_cell true 11 (by decide),
      lmTableCheckOf_sound A hA true 10 (by decide),
      lmTableCheckOf_sound A hA true 11 (by decide)]
    decide

/-- **`D1` cast erasure, honest Trusted deref-below-cast boundary (`8`), and
all `D1` companions**:
1. case `8` is the unique in-range Trusted `.unsupported` cell (`↔`), while
   MiniRust and LeanMiri both return `okScalar 5`;
2. `mrOcTrusted_cast_erasure_agree` and `mr_ocEraseBody_cast_free`;
3. `mr_translate_opaqueCast_fail_closed` (MiniRustSpec fail-closed boundary);
4. `SetDiscriminant` payload (`ocCase6PayloadMir`), protected-drop
   (`ocCase7ProtectedDropMir`), dead-local (`ocCase9DeadLocalMir`), invalid-bool
   and type-switch erasure boundary (`ocCase9InvalidBoolMir`), and upstream
   `minimize` lowering contrasts (`2`, `7`). -/
theorem dual_d1_cast_erasure_and_boundary (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) :
    (∀ tb, trustedVerdict tb 8 = some .unsupported ∧
      mrVerdict tb 8 = some (.returns (.scalar 5)) ∧
      A.verdict tb 8 = some (.returns (.scalar 5))) ∧
    (∀ tb idx, idx < mrOcCaseCount →
      (trustedVerdict tb idx = some .unsupported ↔ idx = 8)) ∧
    type_of% mrOcTrusted_cast_erasure_agree ∧
    type_of% @mr_ocEraseBody_cast_free ∧
    type_of% @mr_translate_opaqueCast_fail_closed ∧
    type_of% @trusted_evalOperand_cast_deref_unsupported ∧
    type_of% @trusted_evalStmt_assign_pure_cast_eq ∧
    type_of% mr_oc_setDiscriminant_payload_agreement ∧
    type_of% mr_oc_protected_drop_mode_sensitive ∧
    type_of% mr_oc_dead_local_ub_non_masking ∧
    type_of% mr_oc_invalid_bool_ub_non_masking ∧
    type_of% mr_oc_type_switch_erasure_boundary ∧
    type_of% mr_oc_minimize_lowering_contrasts := by
  refine ⟨?_, ?_, mrOcTrusted_cast_erasure_agree, @mr_ocEraseBody_cast_free,
    @mr_translate_opaqueCast_fail_closed,
    @trusted_evalOperand_cast_deref_unsupported,
    @trusted_evalStmt_assign_pure_cast_eq,
    mr_oc_setDiscriminant_payload_agreement,
    mr_oc_protected_drop_mode_sensitive,
    mr_oc_dead_local_ub_non_masking,
    mr_oc_invalid_bool_ub_non_masking,
    mr_oc_type_switch_erasure_boundary,
    mr_oc_minimize_lowering_contrasts⟩
  · intro tb
    rw [trustedVerdict_cell tb 8 (by decide), mrVerdict_cell tb 8 (by decide),
      lmTableCheckOf_sound A hA tb 8 (by decide)]
    cases tb <;> exact ⟨rfl, rfl, rfl⟩
  · intro tb idx hi
    rw [trustedVerdict_cell tb idx hi]
    revert hi
    revert idx
    cases tb <;> decide +kernel

/-- **`D2` `rust#166253` callee-only protectors, reverse-transmute companion,
and Trusted indirect fn-ptr transmute boundary**: lifts the reverse-transmute
mode-sensitivity witness, end-to-end Trusted indirect fn-ptr calls, and the
universal Trusted + MiniRust protector/retag laws. -/
theorem dual_d2_fnentry_protectors_and_transmute_boundary (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) :
    type_of% (dual_d2_mode_sensitivity_all_three A hA) ∧
    type_of% mr_oc_d2_rev_transmute_mode_sensitive ∧
    type_of% trusted_d2_indirect_fnptr_calls ∧
    type_of% @trusted_fnEntryCompatibleWithCallSite_transmute_boundary ∧
    type_of% @trusted_evalFnEntryRetag_attach ∧
    type_of% @trusted_evalFnEntryRetag_ref_creates_protected_child ∧
    type_of% @trusted_restoreCallerProtectors_law ∧
    type_of% @trusted_fnEntryRetagPerm ∧
    type_of% @mr_basic_retag_fnEntry_irrelevant ∧
    type_of% @mr_tb_retag_raw_noop ∧
    type_of% @mr_reborrowSettings_ref_protector ∧
    type_of% @mr_reborrowSettings_box_weak_protector ∧
    type_of% mr_reborrowSettings_nonvacuity ∧
    type_of% @mr_end_call_laws :=
  ⟨dual_d2_mode_sensitivity_all_three A hA,
   mr_oc_d2_rev_transmute_mode_sensitive,
   trusted_d2_indirect_fnptr_calls,
   @trusted_fnEntryCompatibleWithCallSite_transmute_boundary,
   @trusted_evalFnEntryRetag_attach,
   @trusted_evalFnEntryRetag_ref_creates_protected_child,
   @trusted_restoreCallerProtectors_law,
   @trusted_fnEntryRetagPerm,
   @mr_basic_retag_fnEntry_irrelevant,
   @mr_tb_retag_raw_noop,
   @mr_reborrowSettings_ref_protector,
   @mr_reborrowSettings_box_weak_protector,
   mr_reborrowSettings_nonvacuity,
   @mr_end_call_laws⟩

/-- **`D3` safe-pointer validity, `some mach` vs `none` `CM.dereferenceable`
separation, and ZST dangling/null companions**: pins all 6 `D3` cells (`16..21`)
across all three authorities plus the exact `Mach`/`MachTB` contrasts and
universal non-`unsupported` / exact-dereferenceable laws. -/
theorem dual_d3_dereferenceable_and_zst_boundary (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) :
    (∀ tb,
      trustedVerdict tb 16 = some (.returns .ptrValid) ∧
      mrVerdict tb 16 = some (.returns .ptrValid) ∧
      A.verdict tb 16 = some (.returns .ptrValid) ∧
      trustedVerdict tb 17 = some (.returns .ptrValid) ∧
      mrVerdict tb 17 = some (.returns .ptrValid) ∧
      A.verdict tb 17 = some (.returns .ptrValid) ∧
      trustedVerdict tb 18 = some .undefinedBehavior ∧
      mrVerdict tb 18 = some .undefinedBehavior ∧
      A.verdict tb 18 = some .undefinedBehavior ∧
      trustedVerdict tb 19 = some .undefinedBehavior ∧
      mrVerdict tb 19 = some .undefinedBehavior ∧
      A.verdict tb 19 = some .undefinedBehavior ∧
      trustedVerdict tb 20 = some .undefinedBehavior ∧
      mrVerdict tb 20 = some .undefinedBehavior ∧
      A.verdict tb 20 = some .undefinedBehavior ∧
      trustedVerdict tb 21 = some .undefinedBehavior ∧
      mrVerdict tb 21 = some .undefinedBehavior ∧
      A.verdict tb 21 = some .undefinedBehavior) ∧
    type_of% mr_checkPtr_some_vs_none_contrast ∧
    type_of% mr_checkPtrM_tb_some_vs_none_contrast ∧
    type_of% @mr_checkPtr_sized_never_unsupported ∧
    type_of% mr_checkPtrM_sized_never_unsupported_bm_tbm ∧
    type_of% @mr_checkPtr_dereferenceable_exact ∧
    type_of% @mr_checkPtrM_dereferenceable_exact ∧
    type_of% @mr_checkPtrM_zst_always_ok ∧
    type_of% @mr_checkPtrM_null_always_ub ∧
    type_of% @mr_checkPtrM_unaligned_always_ub ∧
    type_of% @mr_checkPtrM_none_sized_prov_unsupported ∧
    type_of% mr_checkPtrM_nonvacuity ∧
    type_of% mr_oc_d3_zst_dangling_and_null := by
  refine ⟨?_, mr_checkPtr_some_vs_none_contrast,
    mr_checkPtrM_tb_some_vs_none_contrast,
    @mr_checkPtr_sized_never_unsupported,
    mr_checkPtrM_sized_never_unsupported_bm_tbm,
    @mr_checkPtr_dereferenceable_exact,
    @mr_checkPtrM_dereferenceable_exact,
    @mr_checkPtrM_zst_always_ok,
    @mr_checkPtrM_null_always_ub,
    @mr_checkPtrM_unaligned_always_ub,
    @mr_checkPtrM_none_sized_prov_unsupported,
    mr_checkPtrM_nonvacuity,
    mr_oc_d3_zst_dangling_and_null⟩
  intro tb
  rw [trustedVerdict_cell tb 16 (by decide), mrVerdict_cell tb 16 (by decide),
    lmTableCheckOf_sound A hA tb 16 (by decide),
    trustedVerdict_cell tb 17 (by decide), mrVerdict_cell tb 17 (by decide),
    lmTableCheckOf_sound A hA tb 17 (by decide),
    trustedVerdict_cell tb 18 (by decide), mrVerdict_cell tb 18 (by decide),
    lmTableCheckOf_sound A hA tb 18 (by decide),
    trustedVerdict_cell tb 19 (by decide), mrVerdict_cell tb 19 (by decide),
    lmTableCheckOf_sound A hA tb 19 (by decide),
    trustedVerdict_cell tb 20 (by decide), mrVerdict_cell tb 20 (by decide),
    lmTableCheckOf_sound A hA tb 20 (by decide),
    trustedVerdict_cell tb 21 (by decide), mrVerdict_cell tb 21 (by decide),
    lmTableCheckOf_sound A hA tb 21 (by decide)]
  cases tb <;> decide

open MiniRustSpec.CrossFrameRefAndPanicMR in
/-- Exact `Stop.machineStop` detector directly over unmodified
`MiniRustSpec.Interp.steps` (`Mach`) and `stepsTB` (`MachTB`): returns `true`
iff `bootProgramM` succeeds AND the unmodified MiniRust step driver halts
specifically with `Stop.machineStop`. -/
def ocTerminatesCleanly (tb : Bool) (prog : MiniRustSpec.Gen.Program)
    (fuel : Nat := 120) : Bool :=
  if tb then
    match bootProgramM (M := MiniRustSpec.Interp.TBM)
        ({ implicit_writes := true } : MiniRustSpec.Gen.TreeBorrowsParams) prog with
    | .ok m0 =>
      match MiniRustSpec.Interp.stepsTB fuel m0 with
      | .error .machineStop => true
      | _ => false
    | .error _ => false
  else
    match bootProgramM (M := MiniRustSpec.Interp.BM) () prog with
    | .ok m0 =>
      match MiniRustSpec.Interp.steps fuel m0 with
      | .error .machineStop => true
      | _ => false
    | .error _ => false

/-- **Machine-level termination contrast directly over unmodified `steps` /
`stepsTB`**: callee-only `ocMrProg10` terminates cleanly on BOTH `Mach` and
`MachTB`, while protected foreign-write programs `ocMrProg11`/`13`/`14`
terminate cleanly on `Mach` and halt with UB (not `machineStop`) on `MachTB`,
and `D1` use-after-move `ocMrProg2` fails on both. -/
theorem dual_d2_machine_termination_contrast :
    ocTerminatesCleanly false ocMrProg10 = true ∧
    ocTerminatesCleanly true ocMrProg10 = true ∧
    ocTerminatesCleanly false ocMrProg11 = true ∧
    ocTerminatesCleanly true ocMrProg11 = false ∧
    ocTerminatesCleanly false ocMrProg13 = true ∧
    ocTerminatesCleanly true ocMrProg13 = false ∧
    ocTerminatesCleanly false ocMrProg14 = true ∧
    ocTerminatesCleanly true ocMrProg14 = false ∧
    ocTerminatesCleanly false ocMrProg2 = false ∧
    ocTerminatesCleanly true ocMrProg2 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ### The MiniRust observer's driver is MiniRust's own `stepsM` / `stepsTB`

`mrOcObserve` executes programs with
`MiniRustSpec.CrossFrameRefAndPanicMR.runToStopM`. Projected to `Stop`, it is
definitionally the unmodified `MiniRustSpec.Interp.stepsM` iteration (covering
both `BM` and `TBM`, hence `stepsTB` on `MachTB`), 100% choice-free. -/

section MiniRustDriver
open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp

/-- Forget the stopping machine of a `runToStopM` result. -/
def stopProj {α : Type} : Except (Stop × α) α → Interp α
  | .ok m => .ok m
  | .error (s, _) => .error s

theorem stepsM_eq_runToStopM {M : Type} [Memory M] [MemoryOps M]
    (fuel : Nat) (m : Machine M) :
    stepsM fuel m =
      stopProj (MiniRustSpec.CrossFrameRefAndPanicMR.runToStopM fuel m) := by
  induction fuel generalizing m with
  | zero => rfl
  | succ n ih =>
    unfold stepsM MiniRustSpec.CrossFrameRefAndPanicMR.runToStopM
    cases stepM m with
    | ok m' => exact ih m'
    | error s => rfl

theorem stepsTB_eq_runToStopM (fuel : Nat) (m : MachTB) :
    stepsTB fuel m =
      stopProj (MiniRustSpec.CrossFrameRefAndPanicMR.runToStopM fuel m) :=
  stepsM_eq_runToStopM fuel m

end MiniRustDriver

/-! ## §8. Non-Vacuity of the LeanMiri Hypotheses (Root-Side Witness) -/

/-- A root-side authority satisfying `lmTableCheckOf` and `OcFpLmFailClosed`,
built from the REAL Trusted (`mrOcTrustedObserve`) and MiniRust (`mrOcObserve`)
observers: MiniRust on the case-`8` deref-below-cast boundary, Trusted
elsewhere. It solely witnesses non-vacuity of the capstone's hypotheses; the
semantic LeanMiri closure lives in the cross-root bridge over `lmOcObserve`. -/
def rootBackedLmAuthority : OcFpLmAuthority where
  Obs := MrOcFpObs
  observe := fun tb idx =>
    if idx = 8 then mrOcObserve tb idx else mrOcTrustedObserve tb idx
  toVerdict := ocVerdictOf

theorem rootBackedLmAuthority_tableCheck :
    lmTableCheckOf rootBackedLmAuthority = true := by
  have hcell : ∀ tb idx, idx < mrOcCaseCount →
      rootBackedLmAuthority.verdict tb idx =
        (if idx = 8 then cellOf (mrTable tb) idx
         else cellOf (trustedTable tb) idx) := by
    intro tb idx hi
    show ocVerdictOf
      (if idx = 8 then mrOcObserve tb idx else mrOcTrustedObserve tb idx) = _
    by_cases h : idx = 8
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h),
        ite_eq_left_of_eq_true _ _ (eq_true h)]
      exact mrVerdict_cell tb idx hi
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
        ite_eq_right_of_eq_false _ _ (eq_false h)]
      exact trustedVerdict_cell tb idx hi
  unfold lmTableCheckOf
  apply List.all_eq_true.mpr
  intro tb _
  apply List.all_eq_true.mpr
  intro idx hmem
  have hi := List.mem_range.mp hmem
  rw [hcell tb idx hi]
  revert hi
  revert idx
  cases tb <;> decide +kernel

theorem rootBackedLmAuthority_failClosed :
    OcFpLmFailClosed rootBackedLmAuthority := by
  intro tb idx h
  have h8 : idx ≠ 8 := by unfold mrOcCaseCount at h; omega
  show ocVerdictOf
    (if idx = 8 then mrOcObserve tb idx else mrOcTrustedObserve tb idx) = _
  rw [ite_eq_right_of_eq_false _ _ (eq_false h8)]
  exact trustedVerdict_out_of_range tb idx h

/-- Non-vacuity of `observer_level_exact_all_nat` at the root-backed authority
with `f := id` for every `idx : Nat`. -/
theorem rootBacked_observer_level (tb : Bool) (idx : Nat) :
    type_of% (observer_level_exact_all_nat rootBackedLmAuthority
      rootBackedLmAuthority_tableCheck rootBackedLmAuthority_failClosed
      (fun o => o) (fun _ => rfl) tb idx) :=
  observer_level_exact_all_nat rootBackedLmAuthority
    rootBackedLmAuthority_tableCheck rootBackedLmAuthority_failClosed
    (fun o => o) (fun _ => rfl) tb idx

/-! ## §9. Capstones -/

/-- **Episode 2 capstone (100% constructive, `[propext, Quot.sound]` only)**:
for EVERY LeanMiri authority `A` passing the 44-cell certificate and fail-closed
obligation:
1. the constructive codec is tight, exact, and rejects malformed wires;
2. MiniRust certificates hold for the unified and all three per-domain sides,
   and LeanMiri certificates follow from `hA`;
3. three-way normal agreement, cross-authority fault equivalence, exact
   behavioral equivalence, and positive / fault projections of the unified
   bundle;
4. non-vacuous Tree Borrows mode sensitivity (case `11`) on unified and `D2`;
5. per-domain bundle claims and flip-direction guards for `D1`–`D3`;
6. exact 44-cell classification, zero `specPanic`/`phaseBoundary`, observer-level
   all-`Nat` agreement, fail-closed range, exact mode sensitivity (`{11, 13, 14}`),
   and all lifted `D1` / `D2` / `D3` boundary, companion, and universal laws;
7. machine-level termination contrast, MiniRust driver identities (`stepsM` /
   `stepsTB`), and both Episode 1 MiniRust capstones. -/
theorem ep2_opaquecast_fnentry_dual_authority_capstone (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) (hOob : OcFpLmFailClosed A) :
    ocCodec.TightValidRep ∧
    (∀ b, ocValidRep b ↔ (ocDecode b).isSome = true) ∧
    type_of% ocCodec_rejects_malformed ∧
    (∀ sel, (mrSide sel).check ocModel = true) ∧
    (∀ sel, lmCheckOf sel A = true) ∧
    (∀ (mMR mLM : Bool) (i : OcFpCase),
      OcFpMode.ofTb mMR = OcFpMode.ofTb mLM →
      ocClassOf i.val = .threeWay → ∀ (vMR vLM : OcFpObs),
        (bundleOf A hA).mrRel.ExecR mMR i () () (.normal vMR) →
        (bundleOf A hA).lmRel.ExecR mLM i () () (.normal vLM) →
        ocEncode vMR = ocEncode vLM ∧
          ∃ a : OcFpObs, ocDecode (ocEncode vMR) = some a ∧
            (bundleOf A hA).ExecAnneal (OcFpMode.ofTb mMR) i () (.normal a)) ∧
    (∀ (mMR mLM : Bool) (i : OcFpCase),
      OcFpMode.ofTb mMR = OcFpMode.ofTb mLM →
      ocClassOf i.val = .threeWay → ∀ (k : CorrFaultKind),
        ((∃ c, (bundleOf A hA).mrRel.ExecR mMR i () c (.fault k)) ↔
          (∃ c, (bundleOf A hA).lmRel.ExecR mLM i () c (.fault k)))) ∧
    (∀ (mMR mLM : Bool) (i : OcFpCase), ocClassOf i.val = .threeWay →
      ExactBehaviorEq (bundleOf A hA).mrRel mMR i () ∧
      ExactBehaviorEq (bundleOf A hA).lmRel mLM i ()) ∧
    type_of% (bundleOf A hA).projectPositive ∧
    type_of% (bundleOf A hA).projectFault ∧
    type_of% (modeSensitivity_present A hA) ∧
    type_of% (bundle_gate_castDerefBoundary A hA) ∧
    type_of% (unified_bundle_witness_kinds A hA) ∧
    (∀ d, type_of% (domain_bundle_claims d A hA)) ∧
    (∀ tb idx (hi : idx < mrOcCaseCount),
      type_of% (dual_exact_three_way_classification A hA tb idx hi)) ∧
    (∀ tb idx (hi : idx < mrOcCaseCount),
      type_of% (dual_no_specPanic_all_cells A hA tb idx hi)) ∧
    (∀ (f : A.Obs → MrOcFpObs) (hf : ∀ o, A.toVerdict o = ocVerdictOf (f o))
      tb idx, type_of% (observer_level_exact_all_nat A hA hOob f hf tb idx)) ∧
    (∀ tb idx (h : mrOcCaseCount ≤ idx),
      type_of% (dual_fail_closed_out_of_range A hOob tb idx h)) ∧
    (∀ idx (hi : idx < mrOcCaseCount),
      type_of% (dual_mode_sensitivity_exact A hA idx hi)) ∧
    type_of% (dual_d1_cast_erasure_and_boundary A hA) ∧
    type_of% (dual_d2_fnentry_protectors_and_transmute_boundary A hA) ∧
    type_of% (dual_d3_dereferenceable_and_zst_boundary A hA) ∧
    type_of% dual_d2_machine_termination_contrast ∧
    type_of% @stepsM_eq_runToStopM ∧ type_of% stepsTB_eq_runToStopM ∧
    type_of% ep1_minirust_opaquecast_fnentry_capstone ∧
    type_of% ep1_minirust_opaquecast_fnentry_universal_capstone :=
  ⟨ocCodec_tight, ocValidRep_iff_decode_isSome, ocCodec_rejects_malformed,
   mrSide_check, fun sel => lmCheckOf_of_table sel A hA,
   threeWayNormalAgreement A hA, crossAuthorityFaultEquiv A hA,
   exactBehaviorEq_both A hA,
   (bundleOf A hA).projectPositive, (bundleOf A hA).projectFault,
   modeSensitivity_present A hA, bundle_gate_castDerefBoundary A hA,
   unified_bundle_witness_kinds A hA, fun d => domain_bundle_claims d A hA,
   dual_exact_three_way_classification A hA, dual_no_specPanic_all_cells A hA,
   observer_level_exact_all_nat A hA hOob,
   dual_fail_closed_out_of_range A hOob,
   dual_mode_sensitivity_exact A hA,
   dual_d1_cast_erasure_and_boundary A hA,
   dual_d2_fnentry_protectors_and_transmute_boundary A hA,
   dual_d3_dereferenceable_and_zst_boundary A hA,
   dual_d2_machine_termination_contrast,
   @stepsM_eq_runToStopM, stepsTB_eq_runToStopM,
   ep1_minirust_opaquecast_fnentry_capstone,
   ep1_minirust_opaquecast_fnentry_universal_capstone⟩

/-- The capstone is non-vacuous: its hypotheses are inhabited by a root-side
authority built from the real Trusted and MiniRust observers. -/
theorem ep2_opaquecast_fnentry_dual_authority_capstone_nonvacuous :
    type_of% (ep2_opaquecast_fnentry_dual_authority_capstone
      rootBackedLmAuthority rootBackedLmAuthority_tableCheck
      rootBackedLmAuthority_failClosed) :=
  ep2_opaquecast_fnentry_dual_authority_capstone rootBackedLmAuthority
    rootBackedLmAuthority_tableCheck rootBackedLmAuthority_failClosed

/-! ## §10. Import-Isolation, 100% Constructive Purity, Reachability & Audit -/

section AxiomAudit
open Lean Elab Command

run_cmd do
  let env ← getEnv
  -- 1. Strict direct-import boundary.
  for imp in env.header.imports do
    unless imp.module == `Init ||
        imp.module == `Anneal.DualCorrespondenceBundle ||
        imp.module == `Anneal.Mir.DropBinderAndSubtypeBundle ||
        imp.module == `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR do
      throwError "import-isolation violation: unexpected direct import {imp.module}"
  -- 2. Zero `Miri.*` / `LeanMiriSpec.*` modules (even transitively).
  for modName in env.header.moduleNames do
    if (`Miri).isPrefixOf modName || (`LeanMiriSpec).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported"
  -- 3. 100% constructive `[propext, Quot.sound]` purity across the ENTIRE
  -- module (ZERO `Classical.choice` allowlist entries!).
  let ns := `Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec
  let spotlightDecls : List Lean.Name :=
    [ ns ++ `ocCodec, ns ++ `ocEncode_decode_of_valid, ns ++ `ocCodec_tight,
      ns ++ `ocCodec_encode_injective, ns ++ `ocCodec_decode_injective_on_valid,
      ns ++ `ocValidRep_iff_decode_isSome, ns ++ `ocCodec_rejects_malformed,
      ns ++ `OcFpMode.of_toTb, ns ++ `OcFpMode.to_ofTb,
      ns ++ `allTbModes_complete, ns ++ `allOcFpCases_complete,
      ns ++ `ocVerdictOf, ns ++ `ocClassOf, ns ++ `ocDomainOf,
      ns ++ `lmTableCheckOf, ns ++ `lmTableCheckOf_sound,
      ns ++ `lmTableCheckOf_of_eq, ns ++ `cert_transport,
      ns ++ `ocModelOf, ns ++ `ocModel, ns ++ `ocAnnealEval,
      ns ++ `ocExpectedAnnealEval, ns ++ `mrVerdict, ns ++ `trustedVerdict,
      ns ++ `mrVerdictFn, ns ++ `lmVerdictFn, ns ++ `sideOf, ns ++ `mrSide,
      ns ++ `lmSideOf, ns ++ `lmCheckOf, ns ++ `bundleOfSel,
      ns ++ `range_map_getD, ns ++ `trustedTable_eq, ns ++ `mrTable_eq,
      ns ++ `trustedVerdict_cell, ns ++ `mrVerdict_cell,
      ns ++ `trustedVerdict_out_of_range, ns ++ `mrVerdict_out_of_range,
      ns ++ `ocAnnealEval_funext, ns ++ `mrVerdictFn_funext,
      ns ++ `lmVerdictFn_funext, ns ++ `mrSide_check, ns ++ `lmCheckOf_of_table,
      ns ++ `bundleOf, ns ++ `domainBundleOf, ns ++ `mrGate_of_threeWay,
      ns ++ `lmGate_of_threeWay, ns ++ `threeWayNormalAgreement,
      ns ++ `crossAuthorityFaultEquiv, ns ++ `exactBehaviorEq_both,
      ns ++ `projectPositive, ns ++ `projectFault,
      ns ++ `modeSensitivity_present, ns ++ `bundle_gate_castDerefBoundary,
      ns ++ `unified_bundle_witness_kinds, ns ++ `domain_bundle_claims,
      ns ++ `dual_exact_three_way_classification,
      ns ++ `dual_no_specPanic_all_cells, ns ++ `ocVerdictOf_injective,
      ns ++ `lmTable_vs_tables, ns ++ `observer_level_three_way,
      ns ++ `observer_level_exact_all_nat, ns ++ `dual_fail_closed_out_of_range,
      ns ++ `dual_mode_sensitivity_exact,
      ns ++ `dual_d2_mode_sensitivity_all_three,
      ns ++ `dual_d1_cast_erasure_and_boundary,
      ns ++ `dual_d2_fnentry_protectors_and_transmute_boundary,
      ns ++ `dual_d3_dereferenceable_and_zst_boundary,
      ns ++ `ocTerminatesCleanly, ns ++ `dual_d2_machine_termination_contrast,
      ns ++ `stopProj, ns ++ `stepsM_eq_runToStopM,
      ns ++ `stepsTB_eq_runToStopM,
      ns ++ `rootBackedLmAuthority, ns ++ `rootBackedLmAuthority_tableCheck,
      ns ++ `rootBackedLmAuthority_failClosed, ns ++ `rootBacked_observer_level,
      ns ++ `ep2_opaquecast_fnentry_dual_authority_capstone,
      ns ++ `ep2_opaquecast_fnentry_dual_authority_capstone_nonvacuous ]
  for c in spotlightDecls do
    unless env.contains c do throwError "constructive audit: {c} missing"
    for a in ← liftCoreM <| Lean.collectAxioms c do
      unless a == ``propext || a == ``Quot.sound do
        throwError "constructive decl {c} must not depend on {a}"
  let mut exhaustiveChoiceFree : Nat := 0
  for (c, _) in env.constants.map₂.toList do
    if ns.isPrefixOf c then
      for a in ← liftCoreM <| Lean.collectAxioms c do
        unless a == ``propext || a == ``Quot.sound do
          throwError "exhaustive constructive audit failure: {c} depends on {a}"
      exhaustiveChoiceFree := exhaustiveChoiceFree + 1
  if exhaustiveChoiceFree < 280 then
    throwError "exhaustive constructive audit vacuous: only {exhaustiveChoiceFree} decls checked"
  -- Auditor self-tests: Classical.em, sorryAx, and Lean.ofReduceBool are caught.
  if (← liftCoreM <| Lean.collectAxioms ``Classical.em).all
      (fun a => a == ``propext || a == ``Quot.sound) then
    throwError "constructive audit self-test failed: Classical.em not caught"
  if (← liftCoreM <| Lean.collectAxioms ``sorryAx).all
      (fun a => a == ``propext || a == ``Quot.sound || a == ``Classical.choice) then
    throwError "axiom audit self-test failed: sorryAx not caught"
  if (← liftCoreM <| Lean.collectAxioms ``Lean.ofReduceBool).all
      (fun a => a == ``propext || a == ``Quot.sound || a == ``Classical.choice) then
    throwError "axiom audit self-test failed: Lean.ofReduceBool not caught"
  -- 4. Zero shadow evaluators: bundleOf & capstone reach the REAL interpreters.
  let reachFrom (root : Lean.Name) : NameSet := Id.run do
    let mut seen : NameSet := {}
    let mut todo : Array Lean.Name := #[root]
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      if let some ci := env.find? n then
        for d in ci.getUsedConstantsAsSet do
          if !seen.contains d then todo := todo.push d
    return seen
  let reqs : List (Lean.Name × List Lean.Name) :=
    [ (ns ++ `bundleOf,
        [ `Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle,
          `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcTrustedObserve,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcObserve,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcTrustedObserve_table,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcObserve_table,
          `MiniRustSpec.Interp.stepM,
          `MiniRustSpec.Interp.checkPtrM,
          `MiniRustSpec.Interp.ConcurrentMemory.dereferenceable ]),
      (ns ++ `ep2_opaquecast_fnentry_dual_authority_capstone,
        [ `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
          `Trusted.Rustc.V2026_06_01.MirSemantics.stripLeadingOpaqueCast,
          `Trusted.Rustc.V2026_06_01.MirSemantics.eraseLeadingOpaqueCastDecls,
          `Trusted.Rustc.V2026_06_01.MirSemantics.evalFnEntryRetag,
          `MiniRustSpec.Interp.stepM,
          `MiniRustSpec.Interp.steps,
          `MiniRustSpec.Interp.stepsTB,
          `MiniRustSpec.Interp.checkPtr,
          `MiniRustSpec.Interp.checkPtrM,
          `MiniRustSpec.Interp.CM.dereferenceable,
          `MiniRustSpec.Interp.ConcurrentMemory.dereferenceable,
          `MiniRustSpec.Interp.ReborrowSettings.new,
          `MiniRustSpec.Interp.TreeBorrowsMemory.retag_ptr,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ep1_minirust_opaquecast_fnentry_capstone,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ep1_minirust_opaquecast_fnentry_universal_capstone ]) ]
  for (root, rs) in reqs do
    let seen := reachFrom root
    for r in rs do
      unless seen.contains r do
        throwError "shadow-evaluator audit: {root} does not reach the real {r}"
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
  if theorems < 50 then
    throwError "axiom audit vacuous: only {theorems} theorems seen"
  logInfo m!"oc/fp DualSpec audit: {exhaustiveChoiceFree} decls ({theorems} theorems) 100% constructive in [propext, Quot.sound], zero Classical.choice"

end AxiomAudit

end Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec
