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

**Companions, phase boundary, and shared-runner locks** (beyond the matrix):
* §7b pins exact 3-way raw-observer agreement on the 14 companion cells
  (`ocCase6PayloadMir`, `ocCase7ProtectedDropMir`, `ocCase9DeadLocalMir`,
  `ocCase9InvalidBoolMir`, `ocCase13RevTransmuteMir`, `ocCase17DanglingZstMir`,
  `ocCase18ZstNullMir`) with the single Trusted no-forge boundary
  `zstDangling`, plus the type-switch erasure boundary.
* §7c pins the `D1` static phase boundary on MiniRust (real `translatePlace`)
  and LeanMiri (parameterized phase observer) against runtime execution.
* §7d closes case `8` on the post-borrowck (cast-erased) image: Trusted
  `stepMirFn` on `ocEraseBody` agrees with MiniRust and LeanMiri on ALL 44
  cells, packaged as bundles whose support gate has no boundary.
* §7e exports the universal copy laws through which the cross-root bridge
  locks the shared Trusted runner of `section Fixtures` for EVERY body.

**Honest lowering note for cases `2` / `7`** (§7f): their 3-way `.ub`
agreement holds only under Anneal's move-deinit / drop-deinit lowering
(MiniRust's case `7` program IS its case `5` program; LeanMiri's case `7` is
its case `5` harness; upstream `minimize` returns `7` on both).

**Fuel audit** (§7g): every observer folds fuel exhaustion into
`.unsupported`; Trusted's case `8` is a genuine `.unsupported` step node, no
Trusted run exhausts its fuel, and no in-range MiniRust / LeanMiri cell is
`.unsupported`.

**Honest fixture note for case `17`**: Trusted's canonical fixture builds a
live `&()`, whereas MiniRust and LeanMiri check a dangling provenance-less ZST
pointer; on the identical dangling program Trusted is conservatively `.ub`
(`dual_d3_zst_fixture_divergence`).

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
both `BM` and `TBM`, hence `stepsTB` on `MachTB`), 100% choice-free; on `Mach`
it is moreover MiniRust's own `steps` relative to the upstream `stepM = step`
specialization law (`steps_eq_runToStopM_bm_of`). -/

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

/-- **`Mach` driver identity, relative to the upstream specialization law.**
On `Mach` the observer's driver is MiniRust's own `steps`, GIVEN that the
polymorphic `stepM` specializes to `step` on `BasicMemory`. That law is the
pre-existing upstream lemma `MiniRustSpec.Correspondence.stepM_bm_eq`, which is
NOT choice-free; it is taken as a hypothesis here so this module stays 100%
constructive with zero allowlist entries, and is discharged unconditionally in
the test bridge (`bm_driver_is_minirust_steps`). -/
theorem steps_eq_runToStopM_bm_of
    (h : ∀ m : Mach, stepM (M := BM) m = step m) (fuel : Nat) (m : Mach) :
    steps fuel m =
      stopProj
        (MiniRustSpec.CrossFrameRefAndPanicMR.runToStopM (M := BM) fuel m) := by
  induction fuel generalizing m with
  | zero => rfl
  | succ n ih =>
    unfold steps MiniRustSpec.CrossFrameRefAndPanicMR.runToStopM
    rw [h]
    cases step m with
    | ok m' => exact ih m'
    | error s => rfl

end MiniRustDriver

/-! ## §7b. Companion Fixtures: Exact 3-Way Raw-Observer Agreement

The Episode 1 companions live outside the frozen 22-case matrix. Their Trusted
(`stepMirFn`) and MiniRust (`stepM` / `checkPtrM`) observations are executed
here directly by the kernel, and the LeanMiri side is any companion observer
whose cells satisfy `OcFpLmCompanionCells` (closed in the cross-root bridge over
the real vendored-Miri companion harnesses). -/

/-- The Episode 1 companion fixtures (outside the frozen 22-case matrix). -/
inductive OcFpCompanion : Type where
  /-- `ocCase6PayloadMir`: `SetDiscriminant` payload read (`D1`). -/
  | payload
  /-- `ocCase7ProtectedDropMir`: drop under an active protector (`D1`). -/
  | protectedDrop
  /-- `ocCase9DeadLocalMir`: dead-local read through the cast (`D1`). -/
  | deadLocal
  /-- `ocCase9InvalidBoolMir`: invalid-`bool` type-switching cast (`D1`). -/
  | invalidBool
  /-- `ocCase13RevTransmuteMir`: reverse fn-ptr transmutation (`D2`). -/
  | revTransmute
  /-- `ocCase17DanglingZstMir`: dangling provenance-less `&()` (`D3`). -/
  | zstDangling
  /-- `ocCase18ZstNullMir`: null `&()` (`D3`). -/
  | zstNull
  deriving DecidableEq, Repr

/-- Authority 0 on a companion: unmodified Trusted `stepMirFn` on its
`CapturedMir` (`tb = false` runs the no-borrow-tracker image `ocEraseRetags`,
matching the convention of `mrOcTrustedObserve`). -/
def trustedCompanion (tb : Bool) : OcFpCompanion → MrOcFpObs
  | .payload => mrOcTrustedObsOf .scalar (ocRunTrustedRaw ocCase6PayloadMir [])
  | .protectedDrop =>
    mrOcTrustedObsOf .scalar
      (ocRunTrustedRaw
        (if tb then ocCase7ProtectedDropMir
         else ocEraseRetags ocCase7ProtectedDropMir) [])
  | .deadLocal =>
    mrOcTrustedObsOf .scalar (ocRunTrustedRaw ocCase9DeadLocalMir [])
  | .invalidBool =>
    mrOcTrustedObsOf .scalar (ocRunTrustedRaw ocCase9InvalidBoolMir [])
  | .revTransmute =>
    mrOcTrustedObsOf .pair
      (ocRunTrustedRaw ocCase13RevTransmuteMir
        [if tb then ocCase13Callee else ocEraseRetags ocCase13Callee])
  | .zstDangling =>
    mrOcTrustedObsOf .ptrValid (ocRunTrustedRaw ocCase17DanglingZstMir [])
  | .zstNull =>
    mrOcTrustedObsOf .ptrValid (ocRunTrustedRaw ocCase18ZstNullMir [])

/-- Authority 1 on a companion: unmodified MiniRust on `Mach` / `MachTB`. -/
def mrCompanion (tb : Bool) : OcFpCompanion → MrOcFpObs
  | .payload => ocRun tb [] ocMrProg6Payload
  | .protectedDrop => ocRun tb [] ocMrProg7ProtectedDrop
  | .deadLocal => ocRun tb [] ocMrProg9DeadLocal
  | .invalidBool => ocRun tb [] ocMrProg9InvalidBool
  | .revTransmute => ocRun tb [] ocMrProg13RevTransmute
  | .zstDangling => ocRun tb ocMrZstPtrTys ocMrProg17
  | .zstNull => ocRun tb ocMrZstPtrTys ocMrProg18

/-- Frozen MiniRust = LeanMiri companion table. -/
def ocCompanionExpected (tb : Bool) : OcFpCompanion → MrOcFpObs
  | .payload => .okScalar 7
  | .protectedDrop => if tb then .ub else .okScalar 7
  | .deadLocal => .ub
  | .invalidBool => .ub
  | .revTransmute => if tb then .ub else .okRetagPair 5 5
  | .zstDangling => .okPtrValid
  | .zstNull => .ub

/-- Frozen Trusted companion table: identical except the conservative no-forge
boundary `zstDangling` (Trusted rejects provenance-less reference transmutes
with `.ub`, while MiniRust and LeanMiri accept the dangling ZST pointer). -/
def ocCompanionTrustedExpected (tb : Bool) (c : OcFpCompanion) : MrOcFpObs :=
  if c = .zstDangling then .ub else ocCompanionExpected tb c

/-- Kernel-executed Trusted companion table (`stepMirFn` on all 14 cells). -/
theorem trustedCompanion_table (tb : Bool) (c : OcFpCompanion) :
    trustedCompanion tb c = ocCompanionTrustedExpected tb c := by
  cases tb <;> cases c <;> decide +kernel

/-- Kernel-executed MiniRust companion table (`stepM` / `checkPtrM` on all 14
cells). -/
theorem mrCompanion_table (tb : Bool) (c : OcFpCompanion) :
    mrCompanion tb c = ocCompanionExpected tb c := by
  cases tb <;> cases c <;> decide +kernel

/-- All seven Episode 1 companion fixtures in constructor order. -/
def allOcFpCompanions : List OcFpCompanion :=
  [.payload, .protectedDrop, .deadLocal, .invalidBool, .revTransmute,
   .zstDangling, .zstNull]

theorem allOcFpCompanions_complete (c : OcFpCompanion) :
    c ∈ allOcFpCompanions := by
  cases c <;> decide

/-- 14-cell certificate of a LeanMiri companion observer `obs` presented
through the observation translation `f` (the cross-root bridge instantiates
`f := lmToMr` and `obs` by the real vendored-Miri companion harnesses). -/
def OcFpLmCompanionCells {Obs : Type} (f : Obs → MrOcFpObs)
    (obs : Bool → OcFpCompanion → Obs) : Prop :=
  ∀ tb c, f (obs tb c) = ocCompanionExpected tb c

/-- Decidable 14-cell boolean certificate of a LeanMiri companion observer
(mirroring `lmTableCheckOf`, kernel-evaluated on loop-unrolled twins in the
cross-root bridge). -/
def lmCompanionCheckOf {Obs : Type} (f : Obs → MrOcFpObs)
    (obs : Bool → OcFpCompanion → Obs) : Bool :=
  allTbModes.all fun tb => allOcFpCompanions.all fun c =>
    decide (f (obs tb c) = ocCompanionExpected tb c)

theorem lmCompanionCheckOf_sound {Obs : Type} (f : Obs → MrOcFpObs)
    (obs : Bool → OcFpCompanion → Obs) (h : lmCompanionCheckOf f obs = true) :
    OcFpLmCompanionCells f obs := by
  intro tb c
  have h₁ := List.all_eq_true.mp h tb (allTbModes_complete tb)
  exact of_decide_eq_true
    (List.all_eq_true.mp h₁ c (allOcFpCompanions_complete c))

/-- Companion certificates transport along equal observers (used to move the
kernel-evaluated certificate from loop-unrolled twins to real Miri harnesses). -/
theorem lmCompanionCheckOf_of_eq {Obs : Type} (f : Obs → MrOcFpObs)
    {obs obs' : Bool → OcFpCompanion → Obs} (h : obs = obs')
    (h' : lmCompanionCheckOf f obs' = true) :
    lmCompanionCheckOf f obs = true :=
  h ▸ h'

/-- **Exact 3-way raw-observer agreement on every companion cell.** A
certified LeanMiri companion observer equals raw MiniRust on all 14 cells,
equals raw Trusted iff the companion is not the conservative no-forge boundary
`zstDangling`, full 3-way agreement holds iff `c ≠ .zstDangling`, and no cell
is verdict-less or fail-closed on any authority (so nothing agrees vacuously
through `phaseBoundary` / `specPanic` / `unsupported`). -/
theorem dual_companion_three_way {Obs : Type} (f : Obs → MrOcFpObs)
    (obs : Bool → OcFpCompanion → Obs) (hC : OcFpLmCompanionCells f obs)
    (tb : Bool) (c : OcFpCompanion) :
    f (obs tb c) = mrCompanion tb c ∧
    (f (obs tb c) = trustedCompanion tb c ↔ c ≠ .zstDangling) ∧
    ((trustedCompanion tb c = mrCompanion tb c ∧
        mrCompanion tb c = f (obs tb c)) ↔ c ≠ .zstDangling) ∧
    ocVerdictOf (f (obs tb c)) ≠ none ∧
    ocVerdictOf (f (obs tb c)) ≠ some .unsupported ∧
    ocVerdictOf (trustedCompanion tb c) ≠ none ∧
    ocVerdictOf (trustedCompanion tb c) ≠ some .unsupported := by
  rw [hC tb c, mrCompanion_table tb c, trustedCompanion_table tb c]
  cases tb <;> cases c <;> decide

/-- **Exact companion mode sensitivity on all three authorities**: `basic` and
`treeBorrows` disagree on a companion iff it is the protected drop
(`ocCase7ProtectedDropMir`) or the reverse fn-ptr transmutation
(`ocCase13RevTransmuteMir`). -/
theorem dual_companion_mode_sensitivity {Obs : Type} (f : Obs → MrOcFpObs)
    (obs : Bool → OcFpCompanion → Obs) (hC : OcFpLmCompanionCells f obs)
    (c : OcFpCompanion) :
    (trustedCompanion false c ≠ trustedCompanion true c ↔
      (c = .protectedDrop ∨ c = .revTransmute)) ∧
    (mrCompanion false c ≠ mrCompanion true c ↔
      (c = .protectedDrop ∨ c = .revTransmute)) ∧
    (f (obs false c) ≠ f (obs true c) ↔
      (c = .protectedDrop ∨ c = .revTransmute)) := by
  rw [hC false c, hC true c, mrCompanion_table false c, mrCompanion_table true c,
    trustedCompanion_table false c, trustedCompanion_table true c]
  cases c <;> decide

/-- **Honest fixture divergence at `D3` case `17`.** On MiniRust the
`zstDangling` companion is not an independent program: it IS canonical cell
`17` (`ocMrProg17` checks the provenance-less pointer `4` at `&()` / `Box<()>`),
and a certified LeanMiri companion observes the same value. Trusted's canonical
case `17` instead builds a LIVE `&()` (`okPtrValid`), because on the identical
dangling program (`ocCase17DanglingZstMir`) Trusted conservatively rejects the
provenance-less reference transmute with `.ub`. So the 3-way agreement of
canonical cell `17` relates Trusted on a live ZST reference to MiniRust and
LeanMiri on a dangling one. -/
theorem dual_d3_zst_fixture_divergence {Obs : Type} (f : Obs → MrOcFpObs)
    (obs : Bool → OcFpCompanion → Obs) (hC : OcFpLmCompanionCells f obs)
    (tb : Bool) :
    mrCompanion tb .zstDangling = mrOcObserve tb 17 ∧
    f (obs tb .zstDangling) = mrOcObserve tb 17 ∧
    mrOcTrustedObserve tb 17 = .okPtrValid ∧
    trustedCompanion tb .zstDangling = .ub ∧
    trustedCompanion tb .zstDangling ≠ mrOcTrustedObserve tb 17 := by
  have hT : mrOcTrustedObserve tb 17 = .okPtrValid := by
    cases tb <;> decide +kernel
  have hC17 : trustedCompanion tb .zstDangling = .ub := by
    rw [trustedCompanion_table tb .zstDangling]; rfl
  refine ⟨rfl, (hC tb .zstDangling).trans
    (mrCompanion_table tb .zstDangling).symm, hT, hC17, ?_⟩
  rw [hT, hC17]
  decide

/-- **Type-switch erasure boundary on all three authorities**
(`ocCase9InvalidBoolMir`, `move (_1 as bool)` with `_1 : u8 = 2`). The cast
fixture is `.ub` on Trusted, MiniRust, and LeanMiri, whereas the cast-ERASED
image returns the invalid byte `2` without UB both on Trusted `stepMirFn` and on
any LeanMiri erased-image observation `erased` with `f erased = .okScalar 2`
(vendored `Step.step` in the bridge): erasing a type-switching cast would mask
the UB, so cast erasure is faithful only for type-preserving casts. -/
theorem dual_type_switch_erasure_boundary {Obs : Type} (f : Obs → MrOcFpObs)
    (obs : Bool → OcFpCompanion → Obs) (hC : OcFpLmCompanionCells f obs)
    (erased : Obs) (hE : f erased = .okScalar 2) (tb : Bool) :
    mrOcTrustedObsOf .scalar
        (ocRunTrustedRaw (ocEraseBody ocCase9InvalidBoolMir) []) = f erased ∧
    f erased ≠ f (obs tb .invalidBool) ∧
    trustedCompanion tb .invalidBool = .ub ∧
    mrCompanion tb .invalidBool = .ub ∧
    f (obs tb .invalidBool) = .ub := by
  rw [hE, hC tb .invalidBool, mrCompanion_table tb .invalidBool,
    trustedCompanion_table tb .invalidBool]
  cases tb <;> refine ⟨?_, ?_, rfl, rfl, rfl⟩ <;> decide +kernel

/-! ## §7c. `D1` Static Phase Boundary on MiniRust and LeanMiri

`ProjectionElem.opaqueCast` exists only before `MirPhase::Runtime`. Trusted
executes it value-transparently, whereas BOTH reference authorities reject
every cast-bearing place statically and execute the cast-erased image. -/

/-- **MiniRust static phase observer on one `CapturedMir` body**: a body is
rejected at the phase boundary when it addresses at least one cast-bearing
place and EVERY such place fails closed in real
`MiniRustSpec.Correspondence.translatePlace` (upstream `minimize` has no
`OpaqueCast` lowering). Mirrors LeanMiri's `lmOcPhaseObserveBody`. -/
def mrOcPhaseObserveBody
    (body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir) : MrOcFpObs :=
  match (ocBodyPlaces body).filter ocPlaceHasCast with
  | [] => .unsupported
  | ps =>
    if ps.all (fun p =>
        (MiniRustSpec.Correspondence.translatePlace body.localDecls p).isNone)
    then .phaseBoundary else .unsupported

/-- **MiniRust static phase observer by canonical case index (`0..21`)**:
`.unsupported` outside `0..21` or when no place carries a cast. -/
def mrOcPhaseObserve (idx : Nat) : MrOcFpObs :=
  match ocCaseFixture? idx with
  | none => .unsupported
  | some (body, _) => mrOcPhaseObserveBody body

/-- Out-of-range indices are fail-closed `.unsupported` for `mrOcPhaseObserve`. -/
theorem mrOcPhaseObserve_out_of_range (idx : Nat) (h : mrOcCaseCount ≤ idx) :
    mrOcPhaseObserve idx = .unsupported := by
  unfold mrOcCaseCount at h
  have hNone : ocCaseFixture? idx = none := by
    unfold ocCaseFixture?
    split <;> first | rfl | omega
  unfold mrOcPhaseObserve
  rw [hNone]

/-- Frozen phase table: `phaseBoundary` on `D1` (`0..9`); the `D2` / `D3`
fixtures carry no cast. -/
def ocPhaseExpected : List MrOcFpObs :=
  [.phaseBoundary, .phaseBoundary, .phaseBoundary, .phaseBoundary,
   .phaseBoundary, .phaseBoundary, .phaseBoundary, .phaseBoundary,
   .phaseBoundary, .phaseBoundary,
   .unsupported, .unsupported, .unsupported, .unsupported, .unsupported,
   .unsupported, .unsupported, .unsupported, .unsupported, .unsupported,
   .unsupported, .unsupported]

/-- Kernel-executed MiniRust phase table over the real `translatePlace`. -/
theorem mrOcPhaseObserve_table :
    (List.range mrOcCaseCount).map mrOcPhaseObserve = ocPhaseExpected := by
  decide +kernel

/-- The shared `CapturedMir` body of each Episode 1 companion fixture. -/
def ocCompanionBody : OcFpCompanion → Trusted.Rustc.V2026_06_01.MirAst.CapturedMir
  | .payload => ocCase6PayloadMir
  | .protectedDrop => ocCase7ProtectedDropMir
  | .deadLocal => ocCase9DeadLocalMir
  | .invalidBool => ocCase9InvalidBoolMir
  | .revTransmute => ocCase13RevTransmuteMir
  | .zstDangling => ocCase17DanglingZstMir
  | .zstNull => ocCase18ZstNullMir

/-- Whether a companion fixture belongs to `D1` (carries `.opaqueCast`). -/
def ocCompanionIsD1 : OcFpCompanion → Bool
  | .payload | .protectedDrop | .deadLocal | .invalidBool => true
  | .revTransmute | .zstDangling | .zstNull => false

/-- MiniRust static phase observer on all 7 companion fixtures. -/
def mrOcPhaseCompanion (c : OcFpCompanion) : MrOcFpObs :=
  mrOcPhaseObserveBody (ocCompanionBody c)

/-- Frozen static phase classification of the 7 companions: `D1` companions are
rejected at the phase boundary; `D2`/`D3` companions carry no cast. -/
def ocPhaseCompanionExpected (c : OcFpCompanion) : MrOcFpObs :=
  if ocCompanionIsD1 c then .phaseBoundary else .unsupported

/-- Kernel-executed MiniRust static phase table on all 7 companion fixtures. -/
theorem mrOcPhaseCompanion_table (c : OcFpCompanion) :
    mrOcPhaseCompanion c = ocPhaseCompanionExpected c := by
  cases c <;> decide +kernel

/-- 7-cell static phase certificate for a LeanMiri companion phase observer
(instantiated in the bridge by `lmOcPhaseObserveBody` on all 7 shared companion
fixtures). -/
def lmPhaseCompanionCheckOf {Obs : Type} (f : Obs → MrOcFpObs)
    (phaseC : OcFpCompanion → Obs) : Bool :=
  allOcFpCompanions.all fun c =>
    decide (f (phaseC c) = ocPhaseCompanionExpected c)

/-- **`D1` companion static phase boundary on MiniRust and LeanMiri vs runtime
execution on all three authorities**: all 4 `D1` companions (`payload`,
`protectedDrop`, `deadLocal`, `invalidBool`) are rejected at the static phase
boundary by BOTH MiniRust (`translatePlace`) and LeanMiri
(`Miri.Interpreter.project` + `PlaceDynamic.project`), while the 3 `D2`/`D3`
companions carry no cast (`.unsupported`), and NO runtime companion observer
ever reports `.phaseBoundary`. -/
theorem dual_d1_companion_phase_boundary (A : OcFpLmAuthority)
    (f : A.Obs → MrOcFpObs) (hf : ∀ o, A.toVerdict o = ocVerdictOf (f o))
    (obs : Bool → OcFpCompanion → A.Obs) (hC : OcFpLmCompanionCells f obs)
    (phaseC : OcFpCompanion → A.Obs)
    (hPC : lmPhaseCompanionCheckOf f phaseC = true)
    (tb : Bool) (c : OcFpCompanion) :
    f (phaseC c) = mrOcPhaseCompanion c ∧
    (mrOcPhaseCompanion c = .phaseBoundary ↔ ocCompanionIsD1 c = true) ∧
    (A.toVerdict (phaseC c) = none ↔ ocCompanionIsD1 c = true) ∧
    f (obs tb c) ≠ .phaseBoundary ∧
    mrCompanion tb c ≠ .phaseBoundary ∧
    trustedCompanion tb c ≠ .phaseBoundary := by
  have hL : f (phaseC c) = ocPhaseCompanionExpected c :=
    of_decide_eq_true
      (List.all_eq_true.mp hPC c (allOcFpCompanions_complete c))
  have hM : mrOcPhaseCompanion c = ocPhaseCompanionExpected c :=
    mrOcPhaseCompanion_table c
  have hObs := dual_companion_three_way f obs hC tb c
  have hLmNe : f (obs tb c) ≠ .phaseBoundary := fun h =>
    hObs.2.2.2.1 (congrArg ocVerdictOf h)
  have hMrNe : mrCompanion tb c ≠ .phaseBoundary := hObs.1 ▸ hLmNe
  have hTrNe : trustedCompanion tb c ≠ .phaseBoundary := fun h =>
    hObs.2.2.2.2.2.1 (congrArg ocVerdictOf h)
  refine ⟨hL.trans hM.symm, ?_, ?_, hLmNe, hMrNe, hTrNe⟩
  · rw [hM]; cases c <;> decide
  · rw [hf, hL]; cases c <;> decide

/-- The frozen phase table is `phaseBoundary` (and hence verdict-less) exactly
on the `D1` cases, and `.unsupported` on `10 ≤ idx`. -/
theorem ocPhaseExpected_cell (idx : Nat) (hi : idx < mrOcCaseCount) :
    (ocPhaseExpected.getD idx .unsupported = .phaseBoundary ↔
      ocDomainOf idx = .d1) ∧
    (ocVerdictOf (ocPhaseExpected.getD idx .unsupported) = none ↔
      ocDomainOf idx = .d1) ∧
    (ocPhaseExpected.getD idx .unsupported = .unsupported ↔ 10 ≤ idx) := by
  revert hi
  revert idx
  decide +kernel

/-- 22-cell certificate of a LeanMiri static phase observer `phase` presented
through `f` (the bridge instantiates `phase := lmOcPhaseObserve`, built on the
real vendored `Miri.Interpreter.project` and `PlaceDynamic.project`). -/
def lmPhaseCheckOf {Obs : Type} (f : Obs → MrOcFpObs) (phase : Nat → Obs) :
    Bool :=
  (List.range mrOcCaseCount).all fun idx =>
    decide (f (phase idx) = ocPhaseExpected.getD idx .unsupported)

/-- **`D1` static phase boundary on MiniRust and LeanMiri vs runtime
execution on all three authorities.** For every in-range case: the LeanMiri
phase observation equals the MiniRust phase observation; both are
`phaseBoundary` (no runtime verdict) iff the case lies in `D1`; and yet NO
runtime observer of any authority ever reports `phaseBoundary` (Trusted
dispatches the cast value-transparently, MiniRust and LeanMiri run the
cast-erased image). -/
theorem dual_d1_phase_boundary (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) (f : A.Obs → MrOcFpObs)
    (hf : ∀ o, A.toVerdict o = ocVerdictOf (f o)) (phase : Nat → A.Obs)
    (hP : lmPhaseCheckOf f phase = true) (tb : Bool) (idx : Nat)
    (hi : idx < mrOcCaseCount) :
    f (phase idx) = mrOcPhaseObserve idx ∧
    (mrOcPhaseObserve idx = .phaseBoundary ↔ ocDomainOf idx = .d1) ∧
    (A.toVerdict (phase idx) = none ↔ ocDomainOf idx = .d1) ∧
    f (A.observe tb idx) ≠ .phaseBoundary ∧
    mrOcObserve tb idx ≠ .phaseBoundary ∧
    mrOcTrustedObserve tb idx ≠ .phaseBoundary := by
  have hL : f (phase idx) = ocPhaseExpected.getD idx .unsupported :=
    of_decide_eq_true (List.all_eq_true.mp hP idx (List.mem_range.mpr hi))
  have hM : mrOcPhaseObserve idx = ocPhaseExpected.getD idx .unsupported := by
    rw [← mrOcPhaseObserve_table, range_map_getD hi]
  have hCell := ocPhaseExpected_cell idx hi
  have hObs := observer_level_three_way A hA f hf tb idx hi
  have hNoPanic := dual_no_specPanic_all_cells A hA tb idx hi
  have hMrNe : mrOcObserve tb idx ≠ .phaseBoundary := fun h =>
    hNoPanic.2.1 (congrArg ocVerdictOf h)
  have hTrNe : mrOcTrustedObserve tb idx ≠ .phaseBoundary := fun h =>
    hNoPanic.1 (congrArg ocVerdictOf h)
  refine ⟨hL.trans hM.symm, ?_, ?_, hObs.1 ▸ hMrNe, hMrNe, hTrNe⟩
  · rw [hM]; exact hCell.1
  · rw [hf, hL]; exact hCell.2.1

/-- The shared fixture table is empty outside the canonical range. -/
theorem ocCaseFixture?_out_of_range (idx : Nat) (h : mrOcCaseCount ≤ idx) :
    ocCaseFixture? idx = none := by
  unfold mrOcCaseCount at h
  unfold ocCaseFixture?
  split <;> first | rfl | omega

theorem ocDomainOf_d1_iff (idx : Nat) : ocDomainOf idx = .d1 ↔ idx < 10 := by
  unfold ocDomainOf
  by_cases h : idx < 10
  · rw [ite_eq_left h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [ite_eq_right h]
    by_cases h2 : idx < 16
    · rw [ite_eq_left h2]; exact ⟨(fun e => nomatch e), fun e => absurd e h⟩
    · rw [ite_eq_right h2]; exact ⟨(fun e => nomatch e), fun e => absurd e h⟩

/-- **Fail-closedness of a fixture-indexed phase observer.** Any phase
observer that factors as `k ∘ fixture'` through a copy `fixture'` of the shared
fixture table (locked to `ocCaseFixture?` by `Eq.refl` in the cross-root
bridge), with `k none` translating to `.unsupported`, is fail-closed outside
the canonical range. The bridge instantiates it with LeanMiri's
`lmOcPhaseObserve`, discharging `hphase` by `Eq.refl`. -/
theorem phase_fail_closed_of_fixture {Obs : Type} (f : Obs → MrOcFpObs)
    (fixture' : Nat → Option
      (Trusted.Rustc.V2026_06_01.MirAst.CapturedMir ×
        List Trusted.Rustc.V2026_06_01.MirAst.CapturedMir))
    (hfix : ocCaseFixture? = fixture')
    (k : Option
      (Trusted.Rustc.V2026_06_01.MirAst.CapturedMir ×
        List Trusted.Rustc.V2026_06_01.MirAst.CapturedMir) → Obs)
    (hk : f (k none) = .unsupported)
    (phase : Nat → Obs) (hphase : ∀ idx, phase idx = k (fixture' idx))
    (idx : Nat) (h : mrOcCaseCount ≤ idx) :
    f (phase idx) = .unsupported := by
  rw [hphase idx, ← hfix, ocCaseFixture?_out_of_range idx h]
  exact hk

/-- **All-`Nat` static phase agreement.** For EVERY `idx : Nat` (canonical
`0..21` and fail-closed `≥ 22`) a certified, fail-closed LeanMiri phase
observer equals the MiniRust phase observer; the phase boundary (verdict-less)
is hit iff `idx < 10`, and `.unsupported` holds iff `10 ≤ idx`. -/
theorem dual_d1_phase_boundary_all_nat {Obs : Type} (f : Obs → MrOcFpObs)
    (phase : Nat → Obs) (hP : lmPhaseCheckOf f phase = true)
    (hPOob : ∀ idx, mrOcCaseCount ≤ idx → f (phase idx) = .unsupported)
    (idx : Nat) :
    f (phase idx) = mrOcPhaseObserve idx ∧
    (mrOcPhaseObserve idx = .phaseBoundary ↔ idx < 10) ∧
    (ocVerdictOf (f (phase idx)) = none ↔ idx < 10) ∧
    (f (phase idx) = .unsupported ↔ 10 ≤ idx) := by
  by_cases hi : idx < mrOcCaseCount
  · have hL : f (phase idx) = ocPhaseExpected.getD idx .unsupported :=
      of_decide_eq_true (List.all_eq_true.mp hP idx (List.mem_range.mpr hi))
    have hM : mrOcPhaseObserve idx = ocPhaseExpected.getD idx .unsupported := by
      rw [← mrOcPhaseObserve_table, range_map_getD hi]
    have hCell := ocPhaseExpected_cell idx hi
    refine ⟨hL.trans hM.symm, ?_, ?_, ?_⟩
    · rw [hM]; exact hCell.1.trans (ocDomainOf_d1_iff idx)
    · rw [hL]; exact hCell.2.1.trans (ocDomainOf_d1_iff idx)
    · rw [hL]; exact hCell.2.2
  · have hge : mrOcCaseCount ≤ idx := Nat.le_of_not_lt hi
    have h10 : ¬ idx < 10 := by unfold mrOcCaseCount at hge; omega
    have hGe10 : 10 ≤ idx := by unfold mrOcCaseCount at hge; omega
    rw [hPOob idx hge, mrOcPhaseObserve_out_of_range idx hge]
    exact ⟨rfl,
      ⟨(fun e => nomatch e), (fun e => absurd e h10)⟩,
      ⟨(fun e => nomatch e), (fun e => absurd e h10)⟩,
      ⟨(fun _ => hGe10), (fun _ => rfl)⟩⟩

/-! ## §7d. The Post-Borrowck (Cast-Erased) Image: Closing Case `8`

The `castDerefBoundary` class is a limitation of Trusted's dispatch of a
dereference directly below a leading cast chain, not a semantic disagreement:
on the post-borrowck image (the MIR that exists at `MirPhase::Runtime`, where
`ProjectionElem.opaqueCast` has been erased) Trusted `stepMirFn` agrees with
MiniRust and LeanMiri on ALL 44 cells, case `8` included. This section packages
that fact as a second family of genuine `DualCorrespondenceBundle` witnesses
whose support gate has NO boundary. -/

/-- **Trusted observer on the post-borrowck image**: unmodified `stepMirFn` on
the cast-erased image `ocEraseBody` of every `D1` fixture (`idx < 10`,
`mrOcTrustedErasedObserve`), and on the cast-free `D2` / `D3` fixtures
unchanged. -/
def trustedPostBorrowckObserve (tb : Bool) (idx : Nat) : MrOcFpObs :=
  if idx < 10 then mrOcTrustedErasedObserve idx else mrOcTrustedObserve tb idx

/-- **Kernel-executed 44-cell table**: on the post-borrowck image Trusted
`stepMirFn` coincides with the frozen MiniRust table on EVERY cell (the
deref-below-cast case `8` reads `okScalar 5`). -/
theorem trustedPostBorrowckObserve_table (tb : Bool) :
    (List.range mrOcCaseCount).map (trustedPostBorrowckObserve tb) =
      mrTable tb := by
  cases tb <;> decide +kernel

theorem trustedPostBorrowckObserve_out_of_range (tb : Bool) (idx : Nat)
    (h : mrOcCaseCount ≤ idx) :
    trustedPostBorrowckObserve tb idx = .unsupported := by
  have h10 : ¬ idx < 10 := by unfold mrOcCaseCount at h; omega
  unfold trustedPostBorrowckObserve
  rw [ite_eq_right h10]
  exact mrOcTrustedObserve_out_of_range tb idx h

/-- Authority 0 on the post-borrowck image. -/
def trustedPostBorrowckVerdict (tb : Bool) (idx : Nat) :
    Option (Corpus.Verdict OcFpObs) :=
  ocVerdictOf (trustedPostBorrowckObserve tb idx)

theorem trustedPostBorrowckVerdict_cell (tb : Bool) (idx : Nat)
    (hi : idx < mrOcCaseCount) :
    trustedPostBorrowckVerdict tb idx = cellOf (mrTable tb) idx := by
  unfold trustedPostBorrowckVerdict cellOf
  rw [← trustedPostBorrowckObserve_table tb, range_map_getD hi]

/-- Trusted Anneal execution on the post-borrowck image of every key. -/
def ocPostBorrowckAnnealEval (m : OcFpMode) (i : OcFpCase) (_q : Unit)
    (_c : Unit) : Option (Corpus.Verdict OcFpObs) :=
  trustedPostBorrowckVerdict m.toTb i.val

def ocPostBorrowckExpectedEval (m : OcFpMode) (i : OcFpCase) (_q : Unit)
    (_c : Unit) : Option (Corpus.Verdict OcFpObs) :=
  cellOf (mrTable m.toTb) i.val

theorem ocPostBorrowckAnnealEval_funext :
    ocPostBorrowckAnnealEval = ocPostBorrowckExpectedEval :=
  funext fun m => funext fun i => funext fun _ => funext fun _ =>
    trustedPostBorrowckVerdict_cell m.toTb i.val i.isLt

/-- The Anneal corpus model evaluated by Trusted `stepMirFn` on the
post-borrowck image. -/
def ocPostBorrowckModel :
    Corpus.Model OcFpMode OcFpCase Unit Unit OcFpObs OcFpObsRep :=
  ocModelOf ocPostBorrowckAnnealEval

/-- Support gate on the post-borrowck image: EVERY case of the selected
sub-domain (no `castDerefBoundary` exclusion). -/
def postBorrowckGate (sel : Option OcFpDomain) (i : OcFpCase) : Bool :=
  domainSel sel i

/-- MiniRust side on the post-borrowck image (same `mrOcObserve` verdicts). -/
def mrPostBorrowckSide (sel : Option OcFpDomain) :
    Corpus.Side OcFpMode Bool OcFpCase Unit Unit OcFpObs OcFpObsRep :=
  sideOf sel postBorrowckGate mrVerdictFn

theorem mrPostBorrowckSide_check (sel : Option OcFpDomain) :
    (mrPostBorrowckSide sel).check ocPostBorrowckModel = true := by
  show (sideOf sel postBorrowckGate mrVerdictFn).check
    (ocModelOf ocPostBorrowckAnnealEval) = true
  rw [ocPostBorrowckAnnealEval_funext, mrVerdictFn_funext]
  cases sel with
  | none => decide +kernel
  | some d => cases d <;> decide +kernel

/-- LeanMiri side on the post-borrowck image over an arbitrary authority. -/
def lmPostBorrowckSideOf (sel : Option OcFpDomain) (A : OcFpLmAuthority) :
    Corpus.Side OcFpMode Bool OcFpCase Unit Unit OcFpObs OcFpObsRep :=
  sideOf sel postBorrowckGate (lmVerdictFn A)

def lmPostBorrowckCheckOf (sel : Option OcFpDomain) (A : OcFpLmAuthority) :
    Bool :=
  (lmPostBorrowckSideOf sel A).check ocPostBorrowckModel

theorem lmPostBorrowckCheckOf_of_table (sel : Option OcFpDomain)
    (A : OcFpLmAuthority) (hA : lmTableCheckOf A = true) :
    lmPostBorrowckCheckOf sel A = true := by
  show (sideOf sel postBorrowckGate (lmVerdictFn A)).check
    (ocModelOf ocPostBorrowckAnnealEval) = true
  rw [ocPostBorrowckAnnealEval_funext, lmVerdictFn_funext A hA]
  cases sel with
  | none => decide +kernel
  | some d => cases d <;> decide +kernel

/-- Post-borrowck bundle of selection `sel` from a side certificate. -/
def postBorrowckBundleOfSel (sel : Option OcFpDomain) (A : OcFpLmAuthority)
    (hLM : lmPostBorrowckCheckOf sel A = true) : OcFpBundle :=
  Corpus.bundle ocPostBorrowckModel (mrPostBorrowckSide sel)
    (lmPostBorrowckSideOf sel A) (mrPostBorrowckSide_check sel) hLM

/-- **Unified post-borrowck bundle**: MiniRust and LeanMiri gated on ALL 22
cases × 2 modes against Trusted on the cast-erased image. -/
def postBorrowckBundleOf (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) : OcFpBundle :=
  postBorrowckBundleOfSel none A (lmPostBorrowckCheckOf_of_table none A hA)

/-- **Per-domain post-borrowck bundle** (`D1` gates all ten cases `0..9`). -/
def postBorrowckDomainBundleOf (d : OcFpDomain) (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) : OcFpBundle :=
  postBorrowckBundleOfSel (some d) A
    (lmPostBorrowckCheckOf_of_table (some d) A hA)

/-- **The post-borrowck bundle has no boundary.** Case `8` is excluded from
the cast-image gates (`mrGate` / `lmGate`) but admitted by `postBorrowckGate`;
EVERY case is gated, carries exact behavioral equivalence (reverse totality)
on BOTH authorities, and the bundle makes genuine correspondence and
fault-equivalence claims with a real UB fault witness. -/
theorem post_borrowck_bundle_closes_case8 (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) :
    postBorrowckGate none 8 = true ∧ mrGate none 8 = false ∧
    lmGate none 8 = false ∧ postBorrowckGate (some .d1) 8 = true ∧
    (∀ i : OcFpCase, postBorrowckGate none i = true) ∧
    (∀ (i : OcFpCase) (mMR mLM : Bool),
      ExactBehaviorEq (postBorrowckBundleOf A hA).mrRel mMR i () ∧
      ExactBehaviorEq (postBorrowckBundleOf A hA).lmRel mLM i ()) ∧
    CorrespondenceClaim (postBorrowckBundleOf A hA).mrRel ∧
    FaultEquivClaim (postBorrowckBundleOf A hA).mrRel ∧
    CorrespondenceClaim (postBorrowckBundleOf A hA).lmRel ∧
    FaultEquivClaim (postBorrowckBundleOf A hA).lmRel ∧
    (postBorrowckBundleOf A hA).mrFault.p = 2 ∧
    (postBorrowckBundleOf A hA).lmFault.p = 2 :=
  ⟨rfl, rfl, rfl, rfl, fun _ => rfl,
   fun i _ _ =>
    ⟨(postBorrowckBundleOf A hA).mrSim.exactBehaviorEq_of_reverseTotal
        ((mrPostBorrowckSide none).reverseTotal ocPostBorrowckModel
          (Bool.and_eq_true _ _ ▸ mrPostBorrowckSide_check none).1)
        (rfl : postBorrowckGate none i = true),
     (postBorrowckBundleOf A hA).lmSim.exactBehaviorEq_of_reverseTotal
        ((lmPostBorrowckSideOf none A).reverseTotal ocPostBorrowckModel
          (Bool.and_eq_true _ _ ▸
            lmPostBorrowckCheckOf_of_table none A hA).1)
        (rfl : postBorrowckGate none i = true)⟩,
   (postBorrowckBundleOf A hA).mrSim.correspondenceClaim,
   (postBorrowckBundleOf A hA).mrSim.faultEquivClaim,
   (postBorrowckBundleOf A hA).lmSim.correspondenceClaim,
   (postBorrowckBundleOf A hA).lmSim.faultEquivClaim, rfl, rfl⟩

/-- **Case `8` on both images (verdict level)**: Trusted is honestly
`.unsupported` on the cast fixture, yet returns `5` on its post-borrowck
image, exactly as MiniRust and LeanMiri do. -/
theorem dual_post_borrowck_case8 (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) (tb : Bool) :
    trustedVerdict tb 8 = some .unsupported ∧
    trustedPostBorrowckVerdict tb 8 = some (.returns (.scalar 5)) ∧
    mrVerdict tb 8 = some (.returns (.scalar 5)) ∧
    A.verdict tb 8 = some (.returns (.scalar 5)) := by
  rw [trustedVerdict_cell tb 8 (by decide),
    trustedPostBorrowckVerdict_cell tb 8 (by decide),
    mrVerdict_cell tb 8 (by decide), lmTableCheckOf_sound A hA tb 8 (by decide)]
  cases tb <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Exact post-borrowck agreement for EVERY `tb` and EVERY `idx : Nat`
(raw observers).** Trusted on the post-borrowck image equals raw MiniRust and
the raw (translated) LeanMiri observation unconditionally, and cast erasure is
faithful on Trusted (cast fixture = post-borrowck image) iff `idx ≠ 8`. -/
theorem dual_post_borrowck_exact_all_nat (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) (hOob : OcFpLmFailClosed A)
    (f : A.Obs → MrOcFpObs) (hf : ∀ o, A.toVerdict o = ocVerdictOf (f o))
    (tb : Bool) (idx : Nat) :
    trustedPostBorrowckObserve tb idx = mrOcObserve tb idx ∧
    trustedPostBorrowckObserve tb idx = f (A.observe tb idx) ∧
    (mrOcTrustedObserve tb idx = trustedPostBorrowckObserve tb idx ↔
      idx ≠ 8) := by
  have hAll := observer_level_exact_all_nat A hA hOob f hf tb idx
  have hPB : trustedPostBorrowckObserve tb idx = mrOcObserve tb idx := by
    by_cases hi : idx < mrOcCaseCount
    · have h1 : trustedPostBorrowckObserve tb idx =
          (mrTable tb).getD idx .unsupported := by
        rw [← trustedPostBorrowckObserve_table tb, range_map_getD hi]
      have h2 : mrOcObserve tb idx = (mrTable tb).getD idx .unsupported := by
        rw [← mrTable_eq tb, range_map_getD hi]
      exact h1.trans h2.symm
    · have hge : mrOcCaseCount ≤ idx := Nat.le_of_not_lt hi
      rw [trustedPostBorrowckObserve_out_of_range tb idx hge,
        mrOcObserve_out_of_range tb idx hge]
  refine ⟨hPB, hPB.trans hAll.1.symm, ?_, ?_⟩
  · intro h
    exact hAll.2.2.mp ⟨h.trans hPB, hAll.1.symm⟩
  · intro h8
    exact (hAll.2.2.mpr h8).1.trans hPB.symm

/-- **Uniform post-borrowck Trusted observer**: applies `ocEraseBody`
unconditionally to EVERY fixture body and its callees (with `ocEraseRetags` in
`tb = false`, mirroring `mrOcTrustedObserve`), with ZERO `if idx < 10` case
split. -/
def trustedUniformErasedObserve (tb : Bool) (idx : Nat) : MrOcFpObs :=
  match ocCaseFixture? idx with
  | none => .unsupported
  | some (body, callees) =>
    let cs := (if tb then callees else callees.map ocEraseRetags).map ocEraseBody
    mrOcTrustedObsOf (ocRetKindOf idx) (ocRunTrustedRaw (ocEraseBody body) cs)

/-- Any body carrying a `.opaqueCast` place whose erased image has none is
strictly transformed by `ocEraseBody`. -/
theorem ocEraseBody_ne_of_hasCast
    (b : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir)
    (hHas : (ocBodyPlaces b).any ocPlaceHasCast = true)
    (hErased : (ocBodyPlaces (ocEraseBody b)).any ocPlaceHasCast = false) :
    ocEraseBody b ≠ b := by
  intro h
  have : false = true :=
    hErased ▸ (congrArg (fun x => (ocBodyPlaces x).any ocPlaceHasCast) h).trans hHas
  exact Bool.noConfusion this

/-- **Exact cast-erasure fixed-point characterization on all 22 canonical
fixtures**: `ocEraseBody` is the syntactic identity on a fixture body iff
`10 ≤ idx` (`D2`/`D3`), strictly changes every `D1` body (`0..9`, which carry
no callees), and leaves every `D2`/`D3` callee (both raw and `ocEraseRetags`)
syntactically fixed. -/
theorem ocEraseBody_fixture_fixed_iff (idx : Nat) (hi : idx < mrOcCaseCount) :
    match ocCaseFixture? idx with
    | none => False
    | some (body, callees) =>
      (ocEraseBody body = body ↔ 10 ≤ idx) ∧
      callees.map ocEraseBody = callees ∧
      (callees.map ocEraseRetags).map ocEraseBody = callees.map ocEraseRetags ∧
      (idx < 10 → callees = []) := by
  match idx, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ =>
    exact ⟨⟨fun h => absurd h (ocEraseBody_ne_of_hasCast _
        (by decide +kernel) (by decide +kernel)),
      fun h => absurd h (by decide)⟩, rfl, rfl, fun _ => rfl⟩
  | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _
  | 19, _ | 20, _ | 21, _ =>
    exact ⟨⟨fun _ => by decide, fun _ => rfl⟩, rfl, rfl,
      fun h => absurd h (by decide)⟩
  | n + 22, hi =>
    exact False.elim (Nat.not_lt.mpr (Nat.le_add_left 22 n) hi)

/-- **Exact cast-erasure fixed-point characterization on all 7 companions**:
`ocEraseBody` fixes a companion body iff it is cast-free (`D2`/`D3`). -/
theorem ocEraseBody_companion_fixed_iff (c : OcFpCompanion) :
    ocEraseBody (ocCompanionBody c) = ocCompanionBody c ↔
      ocCompanionIsD1 c = false := by
  cases c with
  | payload | protectedDrop | deadLocal | invalidBool =>
    exact ⟨fun h => absurd h (ocEraseBody_ne_of_hasCast _
        (by decide +kernel) (by decide +kernel)),
      fun h => Bool.noConfusion h⟩
  | revTransmute | zstDangling | zstNull =>
    exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- **Piecewise = Uniform cast erasure for EVERY `tb` and EVERY `idx : Nat`.**
Because `ocEraseBody` fixes every cast-free `D2`/`D3` fixture and callee
syntactically, `trustedPostBorrowckObserve` equals the unconditional
`trustedUniformErasedObserve` everywhere. -/
theorem trustedPostBorrowckObserve_eq_uniform_erased (tb : Bool) (idx : Nat) :
    trustedPostBorrowckObserve tb idx = trustedUniformErasedObserve tb idx := by
  by_cases hi : idx < mrOcCaseCount
  · have hF := ocEraseBody_fixture_fixed_iff idx hi
    unfold trustedPostBorrowckObserve trustedUniformErasedObserve
      mrOcTrustedErasedObserve mrOcTrustedObserve
    cases hEq : ocCaseFixture? idx with
    | none => rw [hEq] at hF; exact False.elim hF
    | some bc =>
      rcases bc with ⟨body, callees⟩
      rw [hEq] at hF
      by_cases h10 : idx < 10
      · rw [ite_eq_left h10]
        have hNil : callees = [] := hF.2.2.2 h10
        subst hNil
        cases tb <;> rfl
      · have hGe10 : 10 ≤ idx := Nat.le_of_not_lt h10
        rw [ite_eq_right h10]
        have hBody : ocEraseBody body = body := hF.1.mpr hGe10
        cases tb with
        | true => dsimp only; rw [ite_eq_left rfl, hBody, hF.2.1]
        | false => dsimp only; rw [ite_eq_right Bool.false_ne_true, hBody, hF.2.2.1]
  · have hGe : mrOcCaseCount ≤ idx := Nat.le_of_not_lt hi
    have h10 : ¬ idx < 10 := by unfold mrOcCaseCount at hGe; omega
    unfold trustedPostBorrowckObserve trustedUniformErasedObserve
      mrOcTrustedObserve
    rw [ite_eq_right h10, ocCaseFixture?_out_of_range idx hGe]

/-- **Per-domain post-borrowck bundle claims (`D1`–`D3`)**: every per-domain
post-borrowck bundle carries correspondence, fault-equivalence, genuine
`.undefined` UB witnesses, and `ExactBehaviorEq` on ALL cases of its domain
(including all 10 `D1` cases `0..9` with case `8` closed); `D1` strictly
expands support over the cast-image bundle at case `8`, while `D2` and `D3`
gates match identically. -/
theorem postBorrowckDomain_bundle_claims (d : OcFpDomain) (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) :
    let B := postBorrowckDomainBundleOf d A hA
    CorrespondenceClaim B.mrRel ∧ FaultEquivClaim B.mrRel ∧
    CorrespondenceClaim B.lmRel ∧ FaultEquivClaim B.lmRel ∧
    B.mrPositive.p = okCaseOf (some d) ∧ B.lmPositive.p = okCaseOf (some d) ∧
    B.mrFault.p = faultCaseOf (some d) ∧ B.lmFault.p = faultCaseOf (some d) ∧
    B.mrFault.kind = .undefined ∧ B.lmFault.kind = .undefined ∧
    B.mrFlip.kind = .undefined ∧ B.lmFlip.kind = .undefined ∧
    (∀ (i : OcFpCase), ocDomainOf i.val = d →
      postBorrowckGate (some d) i = true ∧
      ∀ mMR mLM : Bool,
        ExactBehaviorEq B.mrRel mMR i () ∧
        ExactBehaviorEq B.lmRel mLM i ()) ∧
    (d = .d1 → postBorrowckGate (some .d1) 8 = true ∧ mrGate (some .d1) 8 = false) ∧
    (d ≠ .d1 → ∀ i : OcFpCase, postBorrowckGate (some d) i = mrGate (some d) i) := by
  have hKind : ∀ d' : OcFpDomain,
      Corpus.faultKindOf
        (trustedPostBorrowckVerdict (OcFpMode.ofTb (wModeOf (some d'))).toTb
          (faultCaseOf (some d')).val) = .undefined := by
    intro d'
    rw [trustedPostBorrowckVerdict_cell _ _ (faultCaseOf (some d')).isLt]
    cases d' <;> rfl
  refine ⟨(postBorrowckDomainBundleOf d A hA).mrSim.correspondenceClaim,
    (postBorrowckDomainBundleOf d A hA).mrSim.faultEquivClaim,
    (postBorrowckDomainBundleOf d A hA).lmSim.correspondenceClaim,
    (postBorrowckDomainBundleOf d A hA).lmSim.faultEquivClaim,
    rfl, rfl, rfl, rfl,
    hKind d, hKind d, hKind d, hKind d, ?_, ?_, ?_⟩
  · intro i hd
    have hGate : postBorrowckGate (some d) i = true := by
      unfold postBorrowckGate domainSel
      exact decide_eq_true hd
    refine ⟨hGate, fun _ _ =>
      ⟨(postBorrowckDomainBundleOf d A hA).mrSim.exactBehaviorEq_of_reverseTotal
          ((mrPostBorrowckSide (some d)).reverseTotal ocPostBorrowckModel
            (Bool.and_eq_true _ _ ▸ mrPostBorrowckSide_check (some d)).1) hGate,
       (postBorrowckDomainBundleOf d A hA).lmSim.exactBehaviorEq_of_reverseTotal
          ((lmPostBorrowckSideOf (some d) A).reverseTotal ocPostBorrowckModel
            (Bool.and_eq_true _ _ ▸
              lmPostBorrowckCheckOf_of_table (some d) A hA).1) hGate⟩⟩
  · intro _; exact ⟨rfl, rfl⟩
  · intro hNe i
    cases d with
    | d1 => exact absurd rfl hNe
    | d2 => revert i; decide +kernel
    | d3 => revert i; decide +kernel

/-- Non-vacuous Tree Borrows mode sensitivity (case `11`) is preserved on the
unified and `D2` post-borrowck bundles on BOTH authorities (`D1`/`D3` `none`). -/
theorem postBorrowck_modeSensitivity_present (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) :
    (∃ w, (postBorrowckBundleOf A hA).mrFlip.modeSensitivity? = some w ∧
      w.m₁ = false ∧ w.m₂ = true ∧ w.p = 11) ∧
    (∃ w, (postBorrowckBundleOf A hA).lmFlip.modeSensitivity? = some w ∧
      w.m₁ = false ∧ w.m₂ = true ∧ w.p = 11) ∧
    (∃ w, (postBorrowckDomainBundleOf .d2 A hA).mrFlip.modeSensitivity? = some w ∧
      w.m₁ = false ∧ w.m₂ = true ∧ w.p = 11) ∧
    (∃ w, (postBorrowckDomainBundleOf .d2 A hA).lmFlip.modeSensitivity? = some w ∧
      w.m₁ = false ∧ w.m₂ = true ∧ w.p = 11) ∧
    (postBorrowckDomainBundleOf .d1 A hA).mrFlip.modeSensitivity? = none ∧
    (postBorrowckDomainBundleOf .d1 A hA).lmFlip.modeSensitivity? = none ∧
    (postBorrowckDomainBundleOf .d3 A hA).mrFlip.modeSensitivity? = none ∧
    (postBorrowckDomainBundleOf .d3 A hA).lmFlip.modeSensitivity? = none := by
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, rfl, rfl, rfl, rfl⟩

/-! ## §7e. Verbatim-Copy Locks for the Shared Trusted Runner

`section Fixtures` of `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR` is shared
verbatim with `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM`. Its 93 plain
definitions are locked by `Eq.refl` in the cross-root bridge. The four runner
declarations mention the per-namespace outcome inductives: the bridge relates
the two inductives (`OcTrustedOutcome`, `OcTrustedRun`) by constructor
bijections and locks the two functions (`ocTrustedStep`, `ocRunTrustedRaw`)
UNIVERSALLY (for every body, run state, and callee list) through the generic
copy laws below, instantiated with the LeanMiri-side copy using `Eq.refl`
hypotheses only. -/

section RunnerLock
open Trusted.Rustc.V2026_06_01 Trusted.Rustc.V2026_06_01.MirAst

/-- The `.running` transition of the shared `ocTrustedStep`, abstracted over
the run / outcome representation (same `match` text as `ocTrustedStep`, so
both the MiniRust-side and the LeanMiri-side copies unfold to it by
`Eq.refl`). -/
def ocStepG {R O : Type} (running : MirSemantics.MachineState → R)
    (done : O → R) (ret : MirSemantics.Value → O) (ub unsupported : O)
    (body : CapturedMir) (s : MirSemantics.MachineState) : R :=
  match MirSemantics.stepMirFn body s with
  | .tau (.running s') => running s'
  | .tau (.halted (.normal r)) => done (ret r.1)
  | .tau (.faulted .ub) => done ub
  | .vis (.inr (.inl (.emit _))) cont =>
    match cont PUnit.unit with
    | .running s' => running s'
    | _ => done unsupported
  | .ret (.normal r) => done (ret r.1)
  | .vis (.inl (.fail .ub)) _ => done ub
  | _ => done unsupported

/-- The MiniRust-side `ocTrustedStep` is definitionally the generic step. -/
theorem ocTrustedStep_running_eq (body : CapturedMir)
    (s : MirSemantics.MachineState) :
    ocTrustedStep body (.running s) =
      ocStepG OcTrustedRun.running OcTrustedRun.done OcTrustedOutcome.ret
        OcTrustedOutcome.ub OcTrustedOutcome.unsupported body s := rfl

/-- The generic step is natural in constructor-preserving maps. -/
theorem ocStepG_natural {R O R' O' : Type}
    (running : MirSemantics.MachineState → R) (done : O → R)
    (ret : MirSemantics.Value → O) (ub unsupported : O)
    (running' : MirSemantics.MachineState → R') (done' : O' → R')
    (ret' : MirSemantics.Value → O') (ub' unsupported' : O')
    (g : R → R') (f : O → O')
    (hr : ∀ s, g (running s) = running' s)
    (hd : ∀ o, g (done o) = done' (f o))
    (hret : ∀ v, f (ret v) = ret' v) (hub : f ub = ub')
    (hun : f unsupported = unsupported')
    (body : CapturedMir) (s : MirSemantics.MachineState) :
    g (ocStepG running done ret ub unsupported body s) =
      ocStepG running' done' ret' ub' unsupported' body s := by
  unfold ocStepG
  split
  all_goals first
    | exact hr _
    | rw [hd, hret]
    | rw [hd, hub]
    | rw [hd, hun]
    | (split <;> first | exact hr _ | rw [hd, hun])

/-- `Nat.repeat` is natural in step-commuting maps. -/
theorem repeat_natural {R R' : Type} (g : R → R') (step : R → R)
    (step' : R' → R') (h : ∀ r, g (step r) = step' (g r)) :
    ∀ (n : Nat) (r : R), g (Nat.repeat step n r) = Nat.repeat step' n (g r)
  | 0, _ => rfl
  | n + 1, r => by
    show g (step (Nat.repeat step n r)) = step' (Nat.repeat step' n (g r))
    rw [h, repeat_natural g step step' h n r]

/-- **Universal runner lock.** Any foreign copy `(R', O', step', runRaw')` of
the shared bounded Trusted runner whose constructors correspond under
`g : OcTrustedRun → R'` / `f : OcTrustedOutcome → O'` and whose definitions
unfold to the same text (hypotheses discharged by `Eq.refl` in the bridge)
simulates the MiniRust-side runner in lockstep on EVERY body and run state,
and returns the corresponding raw outcome on EVERY body and callee list. -/
theorem ocRunner_copy_lock {R' O' : Type}
    (running' : MirSemantics.MachineState → R') (done' : O' → R')
    (ret' : MirSemantics.Value → O') (ub' unsupported' outOfFuel' : O')
    (g : OcTrustedRun → R') (f : OcTrustedOutcome → O')
    (step' : CapturedMir → R' → R') (finish' : R' → O')
    (runRaw' : CapturedMir → List CapturedMir → O')
    (hgRun : ∀ s, g (.running s) = running' s)
    (hgDone : ∀ o, g (.done o) = done' (f o))
    (hfRet : ∀ v, f (.ret v) = ret' v) (hfUb : f .ub = ub')
    (hfUns : f .unsupported = unsupported')
    (hfFuel : f .outOfFuel = outOfFuel')
    (hStepRun : ∀ body s, step' body (running' s) =
      ocStepG running' done' ret' ub' unsupported' body s)
    (hStepDone : ∀ body o, step' body (done' o) = done' o)
    (hFinDone : ∀ o, finish' (done' o) = o)
    (hFinRun : ∀ s, finish' (running' s) = outOfFuel')
    (hRaw : ∀ body callees, runRaw' body callees =
      finish' (Nat.repeat (step' body) ocTrustedFuel
        (running'
          (MirSemantics.initMachineStateWithCallees body [] callees)))) :
    (∀ body r, g (ocTrustedStep body r) = step' body (g r)) ∧
    (∀ body callees, f (ocRunTrustedRaw body callees) = runRaw' body callees) := by
  have hStep : ∀ body r, g (ocTrustedStep body r) = step' body (g r) := by
    intro body r
    cases r with
    | done o =>
      show g (.done o) = step' body (g (.done o))
      rw [hgDone, hStepDone]
    | running s =>
      rw [ocTrustedStep_running_eq, hgRun, hStepRun]
      exact ocStepG_natural _ _ _ _ _ _ _ _ _ _ g f hgRun hgDone hfRet hfUb
        hfUns body s
  refine ⟨hStep, ?_⟩
  intro body callees
  rw [hRaw]
  have hRep := repeat_natural g (ocTrustedStep body) (step' body) (hStep body)
    ocTrustedFuel
    (.running (MirSemantics.initMachineStateWithCallees body [] callees))
  rw [hgRun] at hRep
  rw [← hRep]
  unfold ocRunTrustedRaw
  cases Nat.repeat (ocTrustedStep body) ocTrustedFuel
      (.running (MirSemantics.initMachineStateWithCallees body [] callees)) with
  | done o => show f o = finish' (g (.done o)); rw [hgDone, hFinDone]
  | running s =>
    show f .outOfFuel = finish' (g (.running s))
    rw [hgRun, hFinRun, hfFuel]

end RunnerLock

/-- **Universal `ocCombine` lock.** Any foreign copy `combine'` of the shared
half-combiner over an observation type `L` in bijection with `MrOcFpObs`
commutes with the translation `g` on EVERY pair of observations. -/
theorem ocCombine_copy_lock {L : Type} [DecidableEq L] (g : L → MrOcFpObs)
    (g' : MrOcFpObs → L) (hrt : ∀ o, g' (g o) = o) (uns : L)
    (hu : g uns = .unsupported) (combine' : L → L → L)
    (hc : ∀ a b, combine' a b = if a = b then a else uns) (a b : L) :
    g (combine' a b) = ocCombine (g a) (g b) := by
  rw [hc]
  unfold ocCombine
  by_cases h : a = b
  · subst h; rw [ite_eq_left rfl, ite_eq_left rfl]
  · have hne : g a ≠ g b := fun e =>
      h ((hrt a).symm.trans ((congrArg g' e).trans (hrt b)))
    rw [ite_eq_right h, ite_eq_right hne, hu]

/-! ## §7f. Lowering-Dependent `D1` Cells (`2`, `7`)

The 3-way `.ub` agreement of `D1` cases `2` (use after move) and `7` (use after
a glue-free drop) is NOT a fact about upstream MiniRust or vendored Miri: it
holds only under Anneal's move-deinit / drop-deinit lowering, which the
MiniRust programs and the LeanMiri adapter adopt to mirror Trusted.
* MiniRust lowers the move of case `2` as `Load` + `Deinit` and the drop of
  case `7` as `Deinit`, so `ocMrProg7` IS `ocMrProg5` (the `Deinit` case);
  under upstream `minimize` lowering both programs return `7`, NOT `.ub`.
* LeanMiri's case `7` runs the very same `lmOcDeinitThenRead` harness as case
  `5` (locked definitionally in the cross-root bridge), and its case `2` UB
  comes from the Anneal adapter `annealEvalOperand`, which invalidates moved
  locals, whereas vendored `Miri.Interpreter.evalOperand` treats `.Move`
  definitionally identically to `.Copy` (proved universally by `Eq.refl` in
  the cross-root bridge).
* On Trusted `stepMirFn`, replacing `.move` with `.copy` in `ocCase2Mir`
  (`ocMoveToCopyBody`) or replacing `.drop` with `.goto` in `ocCase7Mir`
  (`ocDropToNopBody`) yields `.okScalar 7`, proving the Trusted UB comes
  strictly from move / drop invalidation.
* Among all 22 canonical fixtures ONLY fixture `7` has a `Drop` terminator;
  among all 7 companions ONLY `protectedDrop` (`ocCase7ProtectedDropMir`) does. -/

/-- Whether a `CapturedMir` body contains a `Drop` terminator. -/
def ocBodyHasDrop (b : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir) : Bool :=
  b.basicBlocks.any fun bb =>
    match bb.terminator.kind with
    | .drop _ _ _ => true
    | _ => false

/-- Replace `.move p` with `.copy p` in an operand (modeling vendored
`Miri.Interpreter.evalOperand`, which treats `.Move` and `.Copy` identically). -/
def ocMoveToCopyOperand :
    Trusted.Rustc.V2026_06_01.MirAst.Operand →
      Trusted.Rustc.V2026_06_01.MirAst.Operand
  | .move p => .copy p
  | op => op

/-- Replace `.move` operands with `.copy` inside an rvalue. -/
def ocMoveToCopyRvalue :
    Trusted.Rustc.V2026_06_01.MirAst.Rvalue →
      Trusted.Rustc.V2026_06_01.MirAst.Rvalue
  | .use op => .use (ocMoveToCopyOperand op)
  | .repeat op n => .repeat (ocMoveToCopyOperand op) n
  | .cast k op t => .cast k (ocMoveToCopyOperand op) t
  | .binaryOp o a b => .binaryOp o (ocMoveToCopyOperand a) (ocMoveToCopyOperand b)
  | .unaryOp o a => .unaryOp o (ocMoveToCopyOperand a)
  | .aggregate k ops => .aggregate k (ops.map ocMoveToCopyOperand)
  | .shallowInitBox op t => .shallowInitBox (ocMoveToCopyOperand op) t
  | .wrapUnsafeBinder op t => .wrapUnsafeBinder (ocMoveToCopyOperand op) t
  | rv => rv

/-- Replace `.move` operands with `.copy` inside a statement. -/
def ocMoveToCopyStmt :
    Trusted.Rustc.V2026_06_01.MirAst.StatementKind →
      Trusted.Rustc.V2026_06_01.MirAst.StatementKind
  | .assign p rv => .assign p (ocMoveToCopyRvalue rv)
  | k => k

/-- Replace `.move` with `.copy` across all statements of a `CapturedMir`. -/
def ocMoveToCopyBody (b : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir) :
    Trusted.Rustc.V2026_06_01.MirAst.CapturedMir :=
  { b with basicBlocks := b.basicBlocks.map fun bb =>
      { bb with statements := bb.statements.map fun s =>
          { s with kind := ocMoveToCopyStmt s.kind } } }

/-- Replace glue-free `.drop _ target _` terminators with `.goto target`
(modeling upstream `minimize`, which skips deinitialization on glue-free drops). -/
def ocDropToNopBody (b : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir) :
    Trusted.Rustc.V2026_06_01.MirAst.CapturedMir :=
  { b with basicBlocks := b.basicBlocks.map fun bb =>
      { bb with terminator :=
          { bb.terminator with kind := match bb.terminator.kind with
              | .drop _ target _ => .goto target
              | k => k } } }

/-- Exact predicate for the lowering-dependent `D1` cells (`2` and `7`). -/
def ocLoweringDependent (idx : Nat) : Bool :=
  idx == 2 || idx == 7

/-- **Lowering-dependent `D1` cells (`2`, `7`)**, for every certified LeanMiri
authority and both modes:
1. MiniRust's case `7` program is literally its case `5` (`Deinit`) program;
2. among the 22 shared fixtures ONLY fixture `7` has a `Drop` terminator, and
   among the 7 companions ONLY `protectedDrop` does;
3. cases `2` and `7` are `.ub` on all three authorities;
4. under upstream `minimize` lowering MiniRust returns `7` on both;
5. on Trusted `stepMirFn`, rewriting `.move → .copy` (`ocMoveToCopyBody`) on
   case `2` or `.drop → .goto` (`ocDropToNopBody`) on case `7` yields `7`. -/
theorem dual_d1_lowering_dependent_cells (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) (tb : Bool) :
    ocMrProg7 = ocMrProg5 ∧
    mrOcObserve tb 7 = mrOcObserve tb 5 ∧
    ocBodyHasDrop ocCase7Mir = true ∧ ocBodyHasDrop ocCase5Mir = false ∧
    (List.range mrOcCaseCount).filter (fun i =>
      match ocCaseFixture? i with
      | some (b, _) => ocBodyHasDrop b
      | none => false) = [7] ∧
    allOcFpCompanions.filter (fun c => ocBodyHasDrop (ocCompanionBody c)) =
      [.protectedDrop] ∧
    trustedVerdict tb 2 = some .undefinedBehavior ∧
    mrVerdict tb 2 = some .undefinedBehavior ∧
    A.verdict tb 2 = some .undefinedBehavior ∧
    trustedVerdict tb 7 = some .undefinedBehavior ∧
    mrVerdict tb 7 = some .undefinedBehavior ∧
    A.verdict tb 7 = some .undefinedBehavior ∧
    ocRun tb [] ocMrProg2Minimize = .okScalar 7 ∧
    ocRun tb [] ocMrProg7Minimize = .okScalar 7 ∧
    ocVerdictOf (ocRun tb [] ocMrProg2Minimize) ≠ trustedVerdict tb 2 ∧
    ocVerdictOf (ocRun tb [] ocMrProg7Minimize) ≠ trustedVerdict tb 7 ∧
    mrOcTrustedObsOf .scalar
      (ocRunTrustedRaw (ocMoveToCopyBody ocCase2Mir) []) = .okScalar 7 ∧
    mrOcTrustedObsOf .scalar
      (ocRunTrustedRaw (ocDropToNopBody ocCase7Mir) []) = .okScalar 7 := by
  have hMin := mr_oc_minimize_lowering_contrasts
  have h2M : ocRun tb [] ocMrProg2Minimize = .okScalar 7 := by
    cases tb
    · exact hMin.1
    · exact hMin.2.1
  have h7M : ocRun tb [] ocMrProg7Minimize = .okScalar 7 := by
    cases tb
    · exact hMin.2.2.1
    · exact hMin.2.2.2.1
  have hT2 : trustedVerdict tb 2 = some .undefinedBehavior := by
    rw [trustedVerdict_cell tb 2 (by decide)]; cases tb <;> rfl
  have hT7 : trustedVerdict tb 7 = some .undefinedBehavior := by
    rw [trustedVerdict_cell tb 7 (by decide)]; cases tb <;> rfl
  refine ⟨rfl, rfl, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, hT2, ?_, ?_, hT7, ?_, ?_, h2M, h7M, ?_, ?_,
    by decide +kernel, by decide +kernel⟩
  · rw [mrVerdict_cell tb 2 (by decide)]; cases tb <;> rfl
  · rw [lmTableCheckOf_sound A hA tb 2 (by decide)]; cases tb <;> rfl
  · rw [mrVerdict_cell tb 7 (by decide)]; cases tb <;> rfl
  · rw [lmTableCheckOf_sound A hA tb 7 (by decide)]; cases tb <;> rfl
  · rw [h2M, hT2]; decide
  · rw [h7M, hT7]; decide

/-- Exact characterization of `ocLoweringDependent`: true iff `idx ∈ {2, 7}`,
both in `D1` and `threeWay`, and `.ub` across all three authorities. -/
theorem ocLoweringDependent_characterization (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) (tb : Bool) (idx : Nat) :
    (ocLoweringDependent idx = true ↔ idx = 2 ∨ idx = 7) ∧
    (ocLoweringDependent idx = true →
      ocDomainOf idx = .d1 ∧ ocClassOf idx = .threeWay ∧
      trustedVerdict tb idx = some .undefinedBehavior ∧
      mrVerdict tb idx = some .undefinedBehavior ∧
      A.verdict tb idx = some .undefinedBehavior) := by
  have hIff : ocLoweringDependent idx = true ↔ idx = 2 ∨ idx = 7 := by
    unfold ocLoweringDependent
    rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq]
  refine ⟨hIff, fun h => ?_⟩
  have hCells := dual_d1_lowering_dependent_cells A hA tb
  rcases hIff.mp h with rfl | rfl
  · exact ⟨rfl, rfl, hCells.2.2.2.2.2.2.1, hCells.2.2.2.2.2.2.2.1,
      hCells.2.2.2.2.2.2.2.2.1⟩
  · exact ⟨rfl, rfl, hCells.2.2.2.2.2.2.2.2.2.1, hCells.2.2.2.2.2.2.2.2.2.2.1,
      hCells.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-! ## §7g. Fuel Audit: No `.unsupported` Cell Hides Fuel Exhaustion

All three observers fold fuel exhaustion into `.unsupported`: Trusted maps
`OcTrustedOutcome.outOfFuel` to `.unsupported` (`mrOcTrustedObsOf`), MiniRust
maps a `runToStopM` run that never stops to `.unsupported` (`ocRunM`), and
LeanMiri's `Step.step` driver reports `StepError.unsupported "out of fuel"`.
The honest Trusted boundary at case `8` would be vacuous if it were merely
fuel exhaustion. This section rules that out: Trusted's raw outcome at case
`8` is the genuine `.unsupported` step node, no Trusted run of any canonical,
companion, or cast-erased fixture exhausts its fuel, and no in-range MiniRust or
LeanMiri cell is `.unsupported` at all. -/

/-- Raw bounded Trusted outcome of a canonical case (`none` out of range),
with the same callee convention as `mrOcTrustedObserve`. -/
def trustedRawOutcome (tb : Bool) (idx : Nat) : Option OcTrustedOutcome :=
  match ocCaseFixture? idx with
  | none => none
  | some (body, callees) =>
    some (ocRunTrustedRaw body (if tb then callees else callees.map ocEraseRetags))

/-- Constructor tag of a raw Trusted outcome (`3` = fuel exhausted). -/
def ocOutcomeTag : OcTrustedOutcome → Nat
  | .ret _ => 0
  | .ub => 1
  | .unsupported => 2
  | .outOfFuel => 3

/-- `mrOcTrustedObserve` is exactly the observation of the raw outcome. -/
theorem mrOcTrustedObserve_eq_raw (tb : Bool) (idx : Nat) :
    mrOcTrustedObserve tb idx =
      (trustedRawOutcome tb idx).elim .unsupported
        (mrOcTrustedObsOf (ocRetKindOf idx)) := by
  unfold mrOcTrustedObserve trustedRawOutcome
  cases ocCaseFixture? idx <;> rfl

/-- Raw Trusted outcomes of the 7 companion fixtures in both modes and of the
10 cast-erased `D1` fixtures (the post-borrowck image). -/
def trustedRawAuxOutcomes : List OcTrustedOutcome :=
  [ocRunTrustedRaw ocCase6PayloadMir [],
   ocRunTrustedRaw ocCase7ProtectedDropMir [],
   ocRunTrustedRaw (ocEraseRetags ocCase7ProtectedDropMir) [],
   ocRunTrustedRaw ocCase9DeadLocalMir [],
   ocRunTrustedRaw ocCase9InvalidBoolMir [],
   ocRunTrustedRaw ocCase13RevTransmuteMir [ocCase13Callee],
   ocRunTrustedRaw ocCase13RevTransmuteMir [ocEraseRetags ocCase13Callee],
   ocRunTrustedRaw ocCase17DanglingZstMir [],
   ocRunTrustedRaw ocCase18ZstNullMir []] ++
  (List.range 10).filterMap fun idx =>
    (ocCaseFixture? idx).map fun bc => ocRunTrustedRaw (ocEraseBody bc.1) bc.2

/-- **Fuel audit on all three authorities.** For every certified LeanMiri
authority:
1. no Trusted run of the 44 canonical cells, the companion fixtures, or the
   cast-erased `D1` fixtures exhausts `ocTrustedFuel`;
2. Trusted's raw outcome at case `8` is the genuine `.unsupported` step node in
   both modes, and case `8` is the ONLY in-range case with that outcome;
3. no in-range MiniRust or LeanMiri verdict is `.unsupported`, so neither can
   hide fuel exhaustion either. -/
theorem dual_fuel_and_unsupported_audit (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) :
    (allTbModes.all fun tb => (List.range mrOcCaseCount).all fun idx =>
      (trustedRawOutcome tb idx).map ocOutcomeTag != some 3) = true ∧
    (trustedRawAuxOutcomes.all fun o => ocOutcomeTag o != 3) = true ∧
    trustedRawAuxOutcomes.length = 19 ∧
    (trustedRawOutcome false 8).map ocOutcomeTag = some 2 ∧
    (trustedRawOutcome true 8).map ocOutcomeTag = some 2 ∧
    (allTbModes.all fun tb =>
      ((List.range mrOcCaseCount).filter fun idx =>
        (trustedRawOutcome tb idx).map ocOutcomeTag == some 2) == [8]) = true ∧
    (∀ tb idx, idx < mrOcCaseCount →
      mrVerdict tb idx ≠ some .unsupported ∧
      A.verdict tb idx ≠ some .unsupported) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro tb idx hi
  rw [mrVerdict_cell tb idx hi, lmTableCheckOf_sound A hA tb idx hi]
  revert hi
  revert idx
  cases tb <;> decide +kernel

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

/-- Root-side companion observer built from the REAL Trusted and MiniRust
companion observers (MiniRust on the `zstDangling` no-forge boundary, Trusted
elsewhere); it solely witnesses non-vacuity of `OcFpLmCompanionCells`. -/
def rootBackedCompanion (tb : Bool) (c : OcFpCompanion) : MrOcFpObs :=
  if c = .zstDangling then mrCompanion tb c else trustedCompanion tb c

theorem rootBackedCompanion_cells :
    OcFpLmCompanionCells (fun o => o) rootBackedCompanion := by
  intro tb c
  show (if c = .zstDangling then mrCompanion tb c else trustedCompanion tb c) = _
  rw [mrCompanion_table tb c, trustedCompanion_table tb c]
  cases tb <;> cases c <;> decide

theorem rootBackedCompanion_check :
    lmCompanionCheckOf (fun o => o) rootBackedCompanion = true := by
  unfold lmCompanionCheckOf
  apply List.all_eq_true.mpr
  intro tb _
  apply List.all_eq_true.mpr
  intro c _
  exact decide_eq_true (rootBackedCompanion_cells tb c)

/-- The REAL MiniRust phase observer passes the LeanMiri phase certificate
(non-vacuity of `lmPhaseCheckOf`). -/
theorem rootBackedPhase_check :
    lmPhaseCheckOf (fun o => o) mrOcPhaseObserve = true := by
  decide +kernel

/-- The REAL MiniRust companion phase observer passes `lmPhaseCompanionCheckOf`
(non-vacuity of `lmPhaseCompanionCheckOf`). -/
theorem rootBackedPhaseCompanion_check :
    lmPhaseCompanionCheckOf (fun o => o) mrOcPhaseCompanion = true := by
  decide +kernel

/-- Trusted `stepMirFn` on the cast-ERASED invalid-`bool` companion returns
the invalid byte `2` (the erased-image witness of
`dual_type_switch_erasure_boundary`). -/
theorem rootBackedErased_eq :
    mrOcTrustedObsOf .scalar
      (ocRunTrustedRaw (ocEraseBody ocCase9InvalidBoolMir) []) = .okScalar 2 := by
  decide +kernel

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
    (∀ tb, type_of% (dual_d1_lowering_dependent_cells A hA tb)) ∧
    type_of% (dual_fuel_and_unsupported_audit A hA) ∧
    (∀ tb idx, type_of% (ocLoweringDependent_characterization A hA tb idx)) ∧
    type_of% (dual_d2_fnentry_protectors_and_transmute_boundary A hA) ∧
    type_of% (dual_d3_dereferenceable_and_zst_boundary A hA) ∧
    type_of% dual_d2_machine_termination_contrast ∧
    type_of% @stepsM_eq_runToStopM ∧ type_of% stepsTB_eq_runToStopM ∧
    type_of% steps_eq_runToStopM_bm_of ∧
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
   dual_d1_lowering_dependent_cells A hA,
   dual_fuel_and_unsupported_audit A hA,
   ocLoweringDependent_characterization A hA,
   dual_d2_fnentry_protectors_and_transmute_boundary A hA,
   dual_d3_dereferenceable_and_zst_boundary A hA,
   dual_d2_machine_termination_contrast,
   @stepsM_eq_runToStopM, stepsTB_eq_runToStopM, steps_eq_runToStopM_bm_of,
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

/-- **Episode 2 companion and phase-boundary capstone (100% constructive)**:
for EVERY certified LeanMiri authority `A` whose translation factors through
`f`, every companion observer `obs` passing the 14-cell companion certificate,
every erased-image observation `erased` of the invalid-`bool` companion, and
every static phase observer `phase` passing the 22-cell phase certificate:
1. exact 3-way raw-observer agreement on all 14 companion cells, with the
   single documented Trusted no-forge boundary (`zstDangling`);
2. exact companion mode sensitivity (protected drop, reverse transmutation);
3. the type-switch erasure boundary (`ocCase9InvalidBoolMir`);
4. the `D1` static phase boundary on MiniRust and LeanMiri vs runtime
   execution on all three authorities;
5. the universal MiniRust translation fail-closed law for `.opaqueCast`. -/
theorem ep2_opaquecast_fnentry_companion_phase_capstone (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) (f : A.Obs → MrOcFpObs)
    (hf : ∀ o, A.toVerdict o = ocVerdictOf (f o))
    (obs : Bool → OcFpCompanion → A.Obs) (hC : OcFpLmCompanionCells f obs)
    (erased : A.Obs) (hE : f erased = .okScalar 2)
    (phase : Nat → A.Obs) (hP : lmPhaseCheckOf f phase = true)
    (hPOob : ∀ idx, mrOcCaseCount ≤ idx → f (phase idx) = .unsupported)
    (phaseC : OcFpCompanion → A.Obs)
    (hPC : lmPhaseCompanionCheckOf f phaseC = true) :
    (∀ tb c, type_of% (dual_companion_three_way f obs hC tb c)) ∧
    (∀ c, type_of% (dual_companion_mode_sensitivity f obs hC c)) ∧
    (∀ tb, type_of% (dual_d3_zst_fixture_divergence f obs hC tb)) ∧
    (∀ tb, type_of% (dual_type_switch_erasure_boundary f obs hC erased hE tb)) ∧
    (∀ tb idx (hi : idx < mrOcCaseCount),
      type_of% (dual_d1_phase_boundary A hA f hf phase hP tb idx hi)) ∧
    (∀ idx, type_of% (dual_d1_phase_boundary_all_nat f phase hP hPOob idx)) ∧
    (∀ tb c,
      type_of% (dual_d1_companion_phase_boundary A f hf obs hC phaseC hPC tb c)) ∧
    (∀ idx, mrOcCaseCount ≤ idx → mrOcPhaseObserve idx = .unsupported) ∧
    type_of% @mr_translate_opaqueCast_fail_closed :=
  ⟨dual_companion_three_way f obs hC, dual_companion_mode_sensitivity f obs hC,
   dual_d3_zst_fixture_divergence f obs hC,
   dual_type_switch_erasure_boundary f obs hC erased hE,
   dual_d1_phase_boundary A hA f hf phase hP,
   dual_d1_phase_boundary_all_nat f phase hP hPOob,
   dual_d1_companion_phase_boundary A f hf obs hC phaseC hPC,
   mrOcPhaseObserve_out_of_range,
   @mr_translate_opaqueCast_fail_closed⟩

/-- The companion and phase-boundary capstone is non-vacuous: all of its
hypotheses are inhabited by the REAL root-side Trusted / MiniRust observers. -/
theorem ep2_opaquecast_fnentry_companion_phase_capstone_nonvacuous :
    type_of% (ep2_opaquecast_fnentry_companion_phase_capstone
      rootBackedLmAuthority rootBackedLmAuthority_tableCheck
      (fun o => o) (fun _ => rfl) rootBackedCompanion rootBackedCompanion_cells
      (mrOcTrustedObsOf .scalar
        (ocRunTrustedRaw (ocEraseBody ocCase9InvalidBoolMir) []))
      rootBackedErased_eq mrOcPhaseObserve rootBackedPhase_check
      mrOcPhaseObserve_out_of_range
      mrOcPhaseCompanion rootBackedPhaseCompanion_check) :=
  ep2_opaquecast_fnentry_companion_phase_capstone
    rootBackedLmAuthority rootBackedLmAuthority_tableCheck
    (fun o => o) (fun _ => rfl) rootBackedCompanion rootBackedCompanion_cells
    (mrOcTrustedObsOf .scalar
      (ocRunTrustedRaw (ocEraseBody ocCase9InvalidBoolMir) []))
    rootBackedErased_eq mrOcPhaseObserve rootBackedPhase_check
    mrOcPhaseObserve_out_of_range
    mrOcPhaseCompanion rootBackedPhaseCompanion_check

/-- **Episode 2 post-borrowck capstone (100% constructive)**: for EVERY
certified fail-closed LeanMiri authority `A` whose translation factors through
`f`:
1. the MiniRust and LeanMiri post-borrowck side certificates hold for the
   unified and all three per-domain selections;
2. the unified post-borrowck bundle gates ALL 22 cases with exact behavioral
   equivalence on both authorities (case `8` closed), and every per-domain
   post-borrowck bundle (`D1`–`D3`) carries full claims & mode sensitivity;
3. case `8` is `.unsupported` on Trusted's cast fixture yet `5` on its
   post-borrowck image, as on MiniRust and LeanMiri;
4. for all `tb` and all `idx : Nat`, Trusted on the post-borrowck image equals
   the unconditional uniform cast-erased runner `trustedUniformErasedObserve`,
   raw MiniRust, and raw LeanMiri, `ocEraseBody` fixes all cast-free `D2`/`D3`
   fixtures, callees, and companions syntactically, and cast erasure is
   faithful on Trusted iff `idx ≠ 8`. -/
theorem ep2_opaquecast_fnentry_post_borrowck_capstone (A : OcFpLmAuthority)
    (hA : lmTableCheckOf A = true) (hOob : OcFpLmFailClosed A)
    (f : A.Obs → MrOcFpObs) (hf : ∀ o, A.toVerdict o = ocVerdictOf (f o)) :
    (∀ sel, (mrPostBorrowckSide sel).check ocPostBorrowckModel = true) ∧
    (∀ sel, lmPostBorrowckCheckOf sel A = true) ∧
    type_of% (post_borrowck_bundle_closes_case8 A hA) ∧
    (∀ d, type_of% (postBorrowckDomain_bundle_claims d A hA)) ∧
    type_of% (postBorrowck_modeSensitivity_present A hA) ∧
    (∀ tb, type_of% (dual_post_borrowck_case8 A hA tb)) ∧
    (∀ tb idx,
      type_of% (dual_post_borrowck_exact_all_nat A hA hOob f hf tb idx)) ∧
    (∀ idx (hi : idx < mrOcCaseCount),
      type_of% (ocEraseBody_fixture_fixed_iff idx hi)) ∧
    (∀ c, type_of% (ocEraseBody_companion_fixed_iff c)) ∧
    (∀ tb idx,
      type_of% (trustedPostBorrowckObserve_eq_uniform_erased tb idx)) :=
  ⟨mrPostBorrowckSide_check,
   fun sel => lmPostBorrowckCheckOf_of_table sel A hA,
   post_borrowck_bundle_closes_case8 A hA,
   fun d => postBorrowckDomain_bundle_claims d A hA,
   postBorrowck_modeSensitivity_present A hA,
   dual_post_borrowck_case8 A hA,
   dual_post_borrowck_exact_all_nat A hA hOob f hf,
   ocEraseBody_fixture_fixed_iff,
   ocEraseBody_companion_fixed_iff,
   trustedPostBorrowckObserve_eq_uniform_erased⟩

/-- The post-borrowck capstone is non-vacuous (root-backed authority). -/
theorem ep2_opaquecast_fnentry_post_borrowck_capstone_nonvacuous :
    type_of% (ep2_opaquecast_fnentry_post_borrowck_capstone
      rootBackedLmAuthority rootBackedLmAuthority_tableCheck
      rootBackedLmAuthority_failClosed (fun o => o) (fun _ => rfl)) :=
  ep2_opaquecast_fnentry_post_borrowck_capstone
    rootBackedLmAuthority rootBackedLmAuthority_tableCheck
    rootBackedLmAuthority_failClosed (fun o => o) (fun _ => rfl)

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
      ns ++ `stepsTB_eq_runToStopM, ns ++ `steps_eq_runToStopM_bm_of,
      ns ++ `rootBackedLmAuthority, ns ++ `rootBackedLmAuthority_tableCheck,
      ns ++ `rootBackedLmAuthority_failClosed, ns ++ `rootBacked_observer_level,
      ns ++ `allOcFpCompanions, ns ++ `allOcFpCompanions_complete,
      ns ++ `trustedCompanion, ns ++ `mrCompanion, ns ++ `ocCompanionExpected,
      ns ++ `ocCompanionTrustedExpected, ns ++ `trustedCompanion_table,
      ns ++ `mrCompanion_table, ns ++ `OcFpLmCompanionCells,
      ns ++ `lmCompanionCheckOf, ns ++ `lmCompanionCheckOf_sound,
      ns ++ `lmCompanionCheckOf_of_eq,
      ns ++ `dual_companion_three_way, ns ++ `dual_companion_mode_sensitivity,
      ns ++ `dual_type_switch_erasure_boundary,
      ns ++ `mrOcPhaseObserveBody, ns ++ `mrOcPhaseObserve,
      ns ++ `mrOcPhaseObserve_out_of_range, ns ++ `ocPhaseExpected,
      ns ++ `mrOcPhaseObserve_table, ns ++ `ocPhaseExpected_cell,
      ns ++ `ocCompanionBody, ns ++ `ocCompanionIsD1,
      ns ++ `mrOcPhaseCompanion, ns ++ `ocPhaseCompanionExpected,
      ns ++ `mrOcPhaseCompanion_table, ns ++ `lmPhaseCompanionCheckOf,
      ns ++ `dual_d1_companion_phase_boundary,
      ns ++ `lmPhaseCheckOf, ns ++ `dual_d1_phase_boundary,
      ns ++ `ocStepG, ns ++ `ocTrustedStep_running_eq, ns ++ `ocStepG_natural,
      ns ++ `repeat_natural, ns ++ `ocRunner_copy_lock,
      ns ++ `ocCombine_copy_lock,
      ns ++ `rootBackedCompanion, ns ++ `rootBackedCompanion_cells,
      ns ++ `rootBackedCompanion_check,
      ns ++ `rootBackedPhase_check, ns ++ `rootBackedPhaseCompanion_check,
      ns ++ `rootBackedErased_eq,
      ns ++ `ep2_opaquecast_fnentry_dual_authority_capstone,
      ns ++ `ep2_opaquecast_fnentry_dual_authority_capstone_nonvacuous,
      ns ++ `ep2_opaquecast_fnentry_companion_phase_capstone,
      ns ++ `ep2_opaquecast_fnentry_companion_phase_capstone_nonvacuous,
      ns ++ `dual_d3_zst_fixture_divergence,
      ns ++ `ocCaseFixture?_out_of_range, ns ++ `ocDomainOf_d1_iff,
      ns ++ `phase_fail_closed_of_fixture,
      ns ++ `dual_d1_phase_boundary_all_nat,
      ns ++ `trustedPostBorrowckObserve,
      ns ++ `trustedPostBorrowckObserve_table,
      ns ++ `trustedPostBorrowckObserve_out_of_range,
      ns ++ `trustedPostBorrowckVerdict, ns ++ `trustedPostBorrowckVerdict_cell,
      ns ++ `ocPostBorrowckAnnealEval_funext, ns ++ `ocPostBorrowckModel,
      ns ++ `postBorrowckGate, ns ++ `mrPostBorrowckSide,
      ns ++ `mrPostBorrowckSide_check, ns ++ `lmPostBorrowckSideOf,
      ns ++ `lmPostBorrowckCheckOf, ns ++ `lmPostBorrowckCheckOf_of_table,
      ns ++ `postBorrowckBundleOfSel, ns ++ `postBorrowckBundleOf,
      ns ++ `postBorrowckDomainBundleOf,
      ns ++ `post_borrowck_bundle_closes_case8, ns ++ `dual_post_borrowck_case8,
      ns ++ `dual_post_borrowck_exact_all_nat,
      ns ++ `trustedUniformErasedObserve, ns ++ `ocEraseBody_ne_of_hasCast,
      ns ++ `ocEraseBody_fixture_fixed_iff,
      ns ++ `ocEraseBody_companion_fixed_iff,
      ns ++ `trustedPostBorrowckObserve_eq_uniform_erased,
      ns ++ `postBorrowckDomain_bundle_claims,
      ns ++ `postBorrowck_modeSensitivity_present,
      ns ++ `ocBodyHasDrop, ns ++ `ocMoveToCopyOperand,
      ns ++ `ocMoveToCopyRvalue, ns ++ `ocMoveToCopyStmt,
      ns ++ `ocMoveToCopyBody, ns ++ `ocDropToNopBody,
      ns ++ `ocLoweringDependent, ns ++ `dual_d1_lowering_dependent_cells,
      ns ++ `trustedRawOutcome, ns ++ `ocOutcomeTag,
      ns ++ `mrOcTrustedObserve_eq_raw, ns ++ `trustedRawAuxOutcomes,
      ns ++ `dual_fuel_and_unsupported_audit,
      ns ++ `ocLoweringDependent_characterization,
      ns ++ `ep2_opaquecast_fnentry_post_borrowck_capstone,
      ns ++ `ep2_opaquecast_fnentry_post_borrowck_capstone_nonvacuous ]
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
  if exhaustiveChoiceFree < 500 then
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
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ep1_minirust_opaquecast_fnentry_universal_capstone ]),
      -- Every per-domain bundle reaches the same real interpreters.
      (ns ++ `domainBundleOf,
        [ `Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle,
          `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
          `Trusted.Rustc.V2026_06_01.MirSemantics.stripLeadingOpaqueCast,
          `Trusted.Rustc.V2026_06_01.MirSemantics.eraseLeadingOpaqueCastDecls,
          `Trusted.Rustc.V2026_06_01.MirSemantics.evalFnEntryRetag,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcTrustedObserve,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcObserve,
          `MiniRustSpec.Interp.stepM,
          `MiniRustSpec.Interp.checkPtrM,
          `MiniRustSpec.Interp.ConcurrentMemory.dereferenceable,
          `MiniRustSpec.Interp.TreeBorrowsMemory.retag_ptr ]),
      -- Companion observers and their 3-way theorem run the real engines.
      (ns ++ `trustedCompanion,
        [ `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
          `Trusted.Rustc.V2026_06_01.MirSemantics.evalFnEntryRetag,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocCase6PayloadMir,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocCase7ProtectedDropMir,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocCase9DeadLocalMir,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocCase9InvalidBoolMir,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocCase13RevTransmuteMir,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocCase17DanglingZstMir,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocCase18ZstNullMir ]),
      (ns ++ `mrCompanion,
        [ `MiniRustSpec.Interp.stepM,
          `MiniRustSpec.Interp.checkPtrM,
          `MiniRustSpec.Interp.ConcurrentMemory.dereferenceable,
          `MiniRustSpec.Interp.TreeBorrowsMemory.retag_ptr ]),
      (ns ++ `mrOcPhaseObserve,
        [ `MiniRustSpec.Correspondence.translatePlace,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocCaseFixture?,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocBodyPlaces,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocPlaceHasCast ]),
      (ns ++ `mrOcPhaseCompanion,
        [ `MiniRustSpec.Correspondence.translatePlace,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocCase6PayloadMir,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocCase7ProtectedDropMir,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocCase9DeadLocalMir,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocCase9InvalidBoolMir ]),
      (ns ++ `ocRunner_copy_lock,
        [ `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocTrustedStep,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocRunTrustedRaw,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocTrustedFuel ]),
      (ns ++ `ep2_opaquecast_fnentry_companion_phase_capstone,
        [ `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
          `MiniRustSpec.Interp.stepM,
          `MiniRustSpec.Interp.checkPtrM,
          `MiniRustSpec.Correspondence.translatePlace,
          `MiniRustSpec.Correspondence.translateStatement,
          ns ++ `trustedCompanion, ns ++ `mrCompanion,
          ns ++ `mrOcPhaseObserve, ns ++ `mrOcPhaseCompanion ]),
      -- Post-borrowck bundles: Trusted `stepMirFn` on the cast-erased image.
      (ns ++ `postBorrowckBundleOf,
        [ `Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle,
          `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcTrustedErasedObserve,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocEraseBody,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcTrustedObserve,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcObserve,
          `MiniRustSpec.Interp.stepM,
          `MiniRustSpec.Interp.checkPtrM,
          `MiniRustSpec.Interp.ConcurrentMemory.dereferenceable ]),
      (ns ++ `postBorrowckDomainBundleOf,
        [ `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcTrustedErasedObserve,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcObserve ]),
      (ns ++ `trustedUniformErasedObserve,
        [ `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocEraseBody,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocEraseRetags,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocRunTrustedRaw ]),
      (ns ++ `dual_d1_lowering_dependent_cells,
        [ `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocMrProg2Minimize,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocMrProg7Minimize,
          ns ++ `ocMoveToCopyBody, ns ++ `ocDropToNopBody ]),
      (ns ++ `ep2_opaquecast_fnentry_post_borrowck_capstone,
        [ `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcTrustedErasedObserve,
          `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocEraseBody,
          `MiniRustSpec.Interp.stepM,
          ns ++ `trustedPostBorrowckObserve, ns ++ `trustedUniformErasedObserve,
          ns ++ `postBorrowckBundleOf, ns ++ `postBorrowckDomainBundleOf ]) ]
  for (root, rs) in reqs do
    let seen := reachFrom root
    for r in rs do
      unless seen.contains r do
        throwError "shadow-evaluator audit: {root} does not reach the real {r}"
  -- Mutual authority independence (anti-contamination): Trusted observers never
  -- reach MiniRust `stepM`, and MiniRust observers never reach Trusted `stepMirFn`.
  for trObs in [ `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcTrustedObserve,
                 ns ++ `trustedPostBorrowckObserve,
                 ns ++ `trustedUniformErasedObserve,
                 ns ++ `trustedCompanion ] do
    if (reachFrom trObs).contains `MiniRustSpec.Interp.stepM then
      throwError "authority-independence audit failed: Trusted {trObs} reaches MiniRust stepM"
  for mrObs in [ `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcObserve,
                 ns ++ `mrCompanion,
                 ns ++ `mrOcPhaseObserve,
                 ns ++ `mrOcPhaseCompanion ] do
    if (reachFrom mrObs).contains `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn then
      throwError "authority-independence audit failed: MiniRust {mrObs} reaches Trusted stepMirFn"
  -- Reachability self-tests: the detector is not vacuously true (the pure
  -- codec reaches no interpreter, and the cast-image bundle never touches the
  -- cast-erased Trusted observer).
  if (reachFrom (ns ++ `ocCodec)).contains
      `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn then
    throwError "shadow-evaluator audit self-test failed: ocCodec reaches stepMirFn"
  if (reachFrom (ns ++ `bundleOf)).contains
      `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcTrustedErasedObserve then
    throwError "shadow-evaluator audit self-test failed: bundleOf reaches the erased observer"
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
  if theorems < 120 then
    throwError "axiom audit vacuous: only {theorems} theorems seen"
  logInfo m!"oc/fp DualSpec audit: {exhaustiveChoiceFree} decls ({theorems} theorems) 100% constructive in [propext, Quot.sound], zero Classical.choice"

end AxiomAudit

end Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec
