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
import MiniRustSpec.WideDstAndMaybeUninitMR

/-!
# Episode 2 Dual-Authority Bundle: Wide DSTs, `MaybeUninit<T>` Transport, Pointer-Offset Chains,
# and the `minirust#300` Non-Null `FnPtr` Pin Delta (`Anneal.Mir.WideDstAndMaybeUninitDualSpec`)

Packages the Episode 1 authorities `MiniRustSpec.WideDstAndMaybeUninitMR` (root Lake) and
`LeanMiriSpec.WideDstAndMaybeUninitLM` (`examples/` Lake, reached only through the parameterized
`WdLmAuthority` interface) as genuine `Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle`
witnesses over unmodified `Trusted.Rustc.V2026_06_01.MirSemantics`.

* **Authority 0 (Anneal Trusted MIR)**: `trustedVerdict` is
  `MiniRustSpec.WideDstAndMaybeUninitMR.mrTrustedWdObserve`, which executes
  `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` on the frozen `CapturedMir` fixture of every
  case (zero shadow evaluators).
* **Authority 1 (MiniRust `d821c6e3`)**: `mrVerdict` is
  `MiniRustSpec.WideDstAndMaybeUninitMR.mrWdObserve` (`bootProgramM` / `runToStopM` over
  `BasicMemory` `Mach` and `TreeBorrowsMemory` `MachTB`, `checkPtrM` / `checkPtrFnNonNullM`).
* **Authority 2 (LeanMiri)**: any `WdLmAuthority` whose 48-cell certificate
  `lmTableCheckOf A = true` holds; closed in `tests/mir/WideDstAndMaybeUninitCorrespondenceTests.lean`
  directly over `LeanMiriSpec.WideDstAndMaybeUninitLM.lmWdObserve`.

The interpreter executions are evaluated once, by the kernel, in the Episode 1 table theorems
`mrTrustedWdObserve_table` and `mrWdObserve_table`; this module rewrites with those tables and
closes every finite certificate by kernel evaluation of small table lookups.

**Exact 3-way classification** of the 24 cases × 2 modes (`wdClassOf`):
* `threeWay` (`0..5`, `8..21`, `23`; 42 cells): Trusted = MiniRust = LeanMiri.
* `dstBoundary` (`6`, `7`; 4 cells): MiniRust = LeanMiri = `okSizeAlign`, Trusted honest
  `.unsupported` (`intrinsicWidePointeeStep` on a custom unsized ADT).
* `pinDelta` (`22`; 2 cells): pinned `d821c6e3` `checkPtr` accepts a null `FnPtr`
  (`okFnPtr 0`), while Trusted and LeanMiri reject it (`.ub`).
  The pinned MiniRust machine runs the null-`fn()` transmute to completion in cases `21` and `22`
  alike (`dual_minirust300_machine_level_pin_delta`). Case `21`'s MiniRust `.ub` comes from the
  Episode 1 post-`#300` emulation predicate `checkPtrFnNonNullM`, applied at observation time.
* `outOfRange` (`idx ≥ 24`): all three authorities fail closed (`.unsupported`).

Strict import isolation: imports `Anneal.DualCorrespondenceBundle`,
`Anneal.Mir.DropBinderAndSubtypeBundle` (authority-agnostic `Corpus` layer), and
`MiniRustSpec.WideDstAndMaybeUninitMR` only; zero `Miri.*` / `LeanMiriSpec.*` modules (checked by
the trailing `run_cmd` audit).
-/

namespace Anneal.Mir.WideDstAndMaybeUninitDualSpec

set_option Elab.async false

open Anneal.DualCorrespondenceBundle
open Anneal.Mir.DropBinderAndSubtypeBundle
open MiniRustSpec.WideDstAndMaybeUninitMR

/-! ## §1. Observable Return-Value Domain and Constructive `CodecLaws` -/

/-- Normal-return observations shared by all three authorities (UB / unsupported are carried by
`Corpus.Verdict`). -/
inductive WdObs : Type where
  /-- A scalar result. -/
  | scalar (val : Nat)
  /-- A dynamic `(size, align)` pair. -/
  | sizeAlign (sizeBytes : Nat) (alignBytes : Nat)
  /-- A whole-value byte transport of `byteCount` bytes, `initCount` of them initialized. -/
  | uninitPreserved (byteCount : Nat) (initCount : Nat)
  /-- A validated pointer: function identifier or address. -/
  | fnPtr (addrOrId : Nat)
  deriving DecidableEq, Repr

/-- Tagged wire representation `(tag, a, b)`. -/
abbrev WdObsRep : Type := Nat × Nat × Nat

/-- Canonical encoding: unary payloads put `0` in the unused third slot. -/
def wdEncode : WdObs → WdObsRep
  | .scalar v => (0, v, 0)
  | .sizeAlign s a => (1, s, a)
  | .uninitPreserved b i => (2, b, i)
  | .fnPtr a => (3, a, 0)

/-- Decoding rejects unknown tags and non-zero padding in unary payloads. -/
def wdDecode : WdObsRep → Option WdObs
  | (0, v, 0) => some (.scalar v)
  | (1, s, a) => some (.sizeAlign s a)
  | (2, b, i) => some (.uninitPreserved b i)
  | (3, a, 0) => some (.fnPtr a)
  | _ => none

/-- Structural validity of a wire triple (independent of `wdDecode`). -/
def wdValidRep : WdObsRep → Prop
  | (0, _, 0) => True
  | (1, _, _) => True
  | (2, _, _) => True
  | (3, _, 0) => True
  | _ => False

theorem wdEncode_decode_of_valid (b : WdObsRep) (a : WdObs) (hv : wdValidRep b)
    (hd : wdDecode b = some a) : wdEncode a = b := by
  rcases b with ⟨t, x, y⟩
  match t, y with
  | 0, 0 => cases hd; rfl
  | 0, _ + 1 => exact False.elim hv
  | 1, _ => cases hd; rfl
  | 2, _ => cases hd; rfl
  | 3, 0 => cases hd; rfl
  | 3, _ + 1 => exact False.elim hv
  | _ + 4, _ => exact False.elim hv

/-- Constructive `CodecLaws WdObs WdObsRep` (`[propext, Quot.sound]` only). -/
def wdCodec : CodecLaws WdObs WdObsRep where
  encode := wdEncode
  decode := wdDecode
  ValidRep := wdValidRep
  decode_encode := fun a => by cases a <;> rfl
  encode_valid := fun a => by cases a <;> exact True.intro
  encode_decode_of_valid := wdEncode_decode_of_valid

/-- `ValidRep` is tight: every valid triple decodes. -/
theorem wdCodec_tight : wdCodec.TightValidRep := by
  intro b hv
  rcases b with ⟨t, x, y⟩
  match t, y with
  | 0, 0 => exact ⟨.scalar x, rfl⟩
  | 0, _ + 1 => exact False.elim hv
  | 1, y => exact ⟨.sizeAlign x y, rfl⟩
  | 2, y => exact ⟨.uninitPreserved x y, rfl⟩
  | 3, 0 => exact ⟨.fnPtr x, rfl⟩
  | 3, _ + 1 => exact False.elim hv
  | _ + 4, _ => exact False.elim hv

/-- Encoding is injective. -/
theorem wdCodec_encode_injective {a₁ a₂ : WdObs} (h : wdEncode a₁ = wdEncode a₂) : a₁ = a₂ :=
  wdCodec.encode_injective h

/-- Decoding is injective on valid representations. -/
theorem wdCodec_decode_injective_on_valid {b₁ b₂ : WdObsRep} {a : WdObs}
    (hv₁ : wdValidRep b₁) (hv₂ : wdValidRep b₂)
    (h₁ : wdDecode b₁ = some a) (h₂ : wdDecode b₂ = some a) : b₁ = b₂ :=
  (wdEncode_decode_of_valid b₁ a hv₁ h₁).symm.trans (wdEncode_decode_of_valid b₂ a hv₂ h₂)

/-- `wdValidRep` is EXACTLY the decodable set: it neither over- nor under-approximates
`wdDecode` (so the structural predicate cannot silently admit a wire `wdDecode` rejects). -/
theorem wdValidRep_iff_decode_isSome (b : WdObsRep) : wdValidRep b ↔ (wdDecode b).isSome = true := by
  rcases b with ⟨t, x, y⟩
  match t, y with
  | 0, 0 => exact ⟨fun _ => rfl, fun _ => True.intro⟩
  | 0, _ + 1 => exact ⟨False.elim, fun h => Bool.noConfusion h⟩
  | 1, _ => exact ⟨fun _ => rfl, fun _ => True.intro⟩
  | 2, _ => exact ⟨fun _ => rfl, fun _ => True.intro⟩
  | 3, 0 => exact ⟨fun _ => rfl, fun _ => True.intro⟩
  | 3, _ + 1 => exact ⟨False.elim, fun h => Bool.noConfusion h⟩
  | _ + 4, _ => exact ⟨False.elim, fun h => Bool.noConfusion h⟩

/-- Malformed wire triples (non-zero padding, unknown tags) are rejected by both `wdDecode` and
`wdValidRep`. -/
theorem wdCodec_rejects_malformed :
    wdDecode (0, 5, 1) = none ∧ wdDecode (3, 7, 9) = none ∧ wdDecode (4, 0, 0) = none ∧
    wdDecode (99, 1, 2) = none ∧
    ¬ wdValidRep (0, 5, 1) ∧ ¬ wdValidRep (3, 7, 9) ∧ ¬ wdValidRep (4, 0, 0) ∧
    ¬ wdValidRep (99, 1, 2) :=
  ⟨rfl, rfl, rfl, rfl, id, id, id, id⟩

/-! ## §2. Modes, Cases, Sub-Domains, and the Exact Classification Predicate -/

/-- Anneal-side execution mode. -/
inductive WdMode : Type where
  | basic
  | treeBorrows
  deriving DecidableEq, Repr

/-- The Tree Borrows flag of a mode (shared convention of `mrWdObserve` and `lmWdObserve`). -/
def WdMode.toTb : WdMode → Bool
  | .basic => false
  | .treeBorrows => true

def WdMode.ofTb : Bool → WdMode
  | false => .basic
  | true => .treeBorrows

theorem WdMode.of_toTb (m : WdMode) : WdMode.ofTb m.toTb = m := by cases m <;> rfl
theorem WdMode.to_ofTb (b : Bool) : (WdMode.ofTb b).toTb = b := by cases b <;> rfl

def allTbModes : List Bool := [false, true]

theorem allTbModes_complete (b : Bool) : b ∈ allTbModes := by
  cases b
  · exact List.Mem.head _
  · exact List.Mem.tail _ (List.Mem.head _)

/-- The 24 canonical cases. -/
abbrev WdCase : Type := Fin 24

def allWdCases : List WdCase := List.finRange 24

theorem allWdCases_complete (i : WdCase) : i ∈ allWdCases := List.mem_finRange i

theorem unit_mem_singleton (u : Unit) : u ∈ [()] := by cases u; exact List.Mem.head _

/-- The four sub-domains of the frozen matrix. -/
inductive WdDomain : Type where
  /-- `0..7`: wide slices / `str` / trailing-slice DSTs. -/
  | d1
  /-- `8..13`: `MaybeUninit` / `ManuallyDrop` byte transport. -/
  | d2
  /-- `14..19`: pointer-offset chains and Tree Borrows. -/
  | d3
  /-- `20..23`: function pointers and the `minirust#300` delta. -/
  | d4
  deriving DecidableEq, Repr

def wdDomainOf (idx : Nat) : WdDomain :=
  if idx < 8 then .d1 else if idx < 14 then .d2 else if idx < 20 then .d3 else .d4

/-- Exact cross-authority classification of a case index. -/
inductive WdClass : Type where
  /-- Trusted = MiniRust = LeanMiri. -/
  | threeWay
  /-- MiniRust = LeanMiri, Trusted honestly `.unsupported` (trailing-slice DST structs). -/
  | dstBoundary
  /-- Pinned MiniRust accepts a null `FnPtr`; Trusted = LeanMiri reject it. -/
  | pinDelta
  /-- Fail-closed `.unsupported` everywhere. -/
  | outOfRange
  deriving DecidableEq, Repr

def wdClassOf (idx : Nat) : WdClass :=
  if idx = 6 ∨ idx = 7 then .dstBoundary
  else if idx = 22 then .pinDelta
  else if idx < 24 then .threeWay
  else .outOfRange

/-! ## §3. Verdicts of the Real Authorities and Their Frozen Tables -/

/-- Structural translation of an Episode 1 observation into a `Corpus.Verdict`
(`specPanic` has no verdict). -/
def wdVerdictOf : MrWdObs → Option (Corpus.Verdict WdObs)
  | .okScalar v => some (.returns (.scalar v))
  | .okSizeAlign s a => some (.returns (.sizeAlign s a))
  | .okUninitPreserved b i => some (.returns (.uninitPreserved b i))
  | .okFnPtr a => some (.returns (.fnPtr a))
  | .ub => some .undefinedBehavior
  | .unsupported => some .unsupported
  | .specPanic => none

/-- Authority 0: unmodified Trusted `stepMirFn` (via `mrTrustedWdObserve`). -/
def trustedVerdict (tb : Bool) (idx : Nat) : Option (Corpus.Verdict WdObs) :=
  wdVerdictOf (mrTrustedWdObserve tb idx)

/-- Authority 1: unmodified MiniRust `d821c6e3` (via `mrWdObserve`). -/
def mrVerdict (tb : Bool) (idx : Nat) : Option (Corpus.Verdict WdObs) :=
  wdVerdictOf (mrWdObserve tb idx)

def trustedTable (tb : Bool) : List MrWdObs :=
  if tb then mrTrustedExpectedTb else mrTrustedExpectedBasic

def mrTable (tb : Bool) : List MrWdObs :=
  if tb then mrWdExpectedTb else mrWdExpectedBasic

/-- Frozen LeanMiri table for `tb = false` (identical to `lmWdExpectedBasic`, transcribed into
`MrWdObs` because this module may not import `LeanMiriSpec.*`). -/
def wdLmExpectedBasic : List MrWdObs :=
  [.okScalar 22, .okSizeAlign 12 4, .okSizeAlign 0 1, .okSizeAlign 9223372036854775804 4, .ub, .ub,
   .okSizeAlign 16 4, .okSizeAlign 16 8,
   .okUninitPreserved 4 0, .okUninitPreserved 4 1, .okScalar 305419896, .okScalar 77, .ub, .ub,
   .okScalar 200, .okScalar 200, .ub, .ub, .okScalar 100, .okScalar 999,
   .okFnPtr 1, .ub, .ub, .okFnPtr 0]

/-- Frozen LeanMiri table for `tb = true` (only case `19` differs). -/
def wdLmExpectedTb : List MrWdObs :=
  [.okScalar 22, .okSizeAlign 12 4, .okSizeAlign 0 1, .okSizeAlign 9223372036854775804 4, .ub, .ub,
   .okSizeAlign 16 4, .okSizeAlign 16 8,
   .okUninitPreserved 4 0, .okUninitPreserved 4 1, .okScalar 305419896, .okScalar 77, .ub, .ub,
   .okScalar 200, .okScalar 200, .ub, .ub, .okScalar 100, .ub,
   .okFnPtr 1, .ub, .ub, .okFnPtr 0]

def lmTable (tb : Bool) : List MrWdObs :=
  if tb then wdLmExpectedTb else wdLmExpectedBasic

/-- Cell lookup into a frozen table. -/
def cellOf (l : List MrWdObs) (idx : Nat) : Option (Corpus.Verdict WdObs) :=
  wdVerdictOf (l.getD idx .unsupported)

theorem range_map_getD {f : Nat → MrWdObs} {n idx : Nat} (hi : idx < n) :
    ((List.range n).map f).getD idx .unsupported = f idx := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem trustedTable_eq (tb : Bool) :
    (List.range mrWdCaseCount).map (mrTrustedWdObserve tb) = trustedTable tb := by
  cases tb
  · exact mrTrustedWdObserve_table.1
  · exact mrTrustedWdObserve_table.2

theorem mrTable_eq (tb : Bool) :
    (List.range mrWdCaseCount).map (mrWdObserve tb) = mrTable tb := by
  cases tb
  · exact mrWdObserve_table.1
  · exact mrWdObserve_table.2

/-- Every in-range Trusted verdict is its frozen-table cell (kernel-executed `stepMirFn`). -/
theorem trustedVerdict_cell (tb : Bool) (idx : Nat) (hi : idx < mrWdCaseCount) :
    trustedVerdict tb idx = cellOf (trustedTable tb) idx := by
  unfold trustedVerdict cellOf
  rw [← trustedTable_eq tb, range_map_getD hi]

/-- Every in-range MiniRust verdict is its frozen-table cell (kernel-executed `stepM`). -/
theorem mrVerdict_cell (tb : Bool) (idx : Nat) (hi : idx < mrWdCaseCount) :
    mrVerdict tb idx = cellOf (mrTable tb) idx := by
  unfold mrVerdict cellOf
  rw [← mrTable_eq tb, range_map_getD hi]

theorem trustedVerdict_out_of_range (tb : Bool) (idx : Nat) (h : mrWdCaseCount ≤ idx) :
    trustedVerdict tb idx = some .unsupported := by
  unfold trustedVerdict
  rw [mrTrustedWdObserve_out_of_range tb idx h]
  rfl

theorem mrVerdict_out_of_range (tb : Bool) (idx : Nat) (h : mrWdCaseCount ≤ idx) :
    mrVerdict tb idx = some .unsupported := by
  unfold mrVerdict
  rw [mrWdObserve_out_of_range tb idx h]
  rfl

/-! ## §4. Parameterized LeanMiri Authority Interface (`WdLmAuthority`) -/

/-- A LeanMiri observation authority presented through its own observation type: the cross-root
bridge instantiates `Obs := LeanMiriSpec.WideDstAndMaybeUninitLM.LmWdObs`,
`observe := lmWdObserve`, and `toVerdict` by `LmWdObs.rec`. -/
structure WdLmAuthority : Type 1 where
  Obs : Type
  observe : Bool → Nat → Obs
  toVerdict : Obs → Option (Corpus.Verdict WdObs)

/-- The verdict of a LeanMiri authority on `(tb, idx)`. -/
def WdLmAuthority.verdict (A : WdLmAuthority) (tb : Bool) (idx : Nat) :
    Option (Corpus.Verdict WdObs) :=
  A.toVerdict (A.observe tb idx)

/-- 48-cell validity certificate: every in-range verdict of `A` equals the frozen LeanMiri table. -/
def lmTableCheckOf (A : WdLmAuthority) : Bool :=
  allTbModes.all fun tb => (List.range mrWdCaseCount).all fun idx =>
    decide (A.verdict tb idx = cellOf (lmTable tb) idx)

/-- Fail-closed obligation of a LeanMiri authority outside the canonical range. -/
def WdLmFailClosed (A : WdLmAuthority) : Prop :=
  ∀ tb idx, mrWdCaseCount ≤ idx → A.verdict tb idx = some .unsupported

theorem lmTableCheckOf_sound (A : WdLmAuthority) (hA : lmTableCheckOf A = true)
    (tb : Bool) (idx : Nat) (hi : idx < mrWdCaseCount) :
    A.verdict tb idx = cellOf (lmTable tb) idx := by
  have h₁ := List.all_eq_true.mp hA tb (allTbModes_complete tb)
  exact of_decide_eq_true (List.all_eq_true.mp h₁ idx (List.mem_range.mpr hi))

/-- Certificates transport along equal authorities (used to move the kernel-evaluated certificate
of the loop-unrolled twin `lmWdObserveU` to the real `lmWdObserve` via `lmWdObserveU.eq_src`). -/
theorem lmTableCheckOf_of_eq {A B : WdLmAuthority} (h : A = B) (hB : lmTableCheckOf B = true) :
    lmTableCheckOf A = true :=
  h ▸ hB

/-- Side certificates transport along equal authorities (moves a certificate kernel-evaluated on
the loop-unrolled twin directly onto the real `lmWdObserve` authority). -/
theorem cert_transport {A B : WdLmAuthority} (h : A = B)
    (p : WdLmAuthority → Bool) (hB : p B = true) : p A = true :=
  h ▸ hB

/-! ## §5. The Anneal Corpus Model and the MiniRust / LeanMiri Sides -/

/-- Direct Trusted Anneal execution on every `(mode, case)` key. -/
def wdAnnealEval (m : WdMode) (i : WdCase) (_q : Unit) (_c : Unit) :
    Option (Corpus.Verdict WdObs) :=
  trustedVerdict m.toTb i.val

def wdExpectedAnnealEval (m : WdMode) (i : WdCase) (_q : Unit) (_c : Unit) :
    Option (Corpus.Verdict WdObs) :=
  cellOf (trustedTable m.toTb) i.val

theorem wdAnnealEval_funext : wdAnnealEval = wdExpectedAnnealEval :=
  funext fun m => funext fun i => funext fun _ => funext fun _ =>
    trustedVerdict_cell m.toTb i.val i.isLt

/-- The Anneal corpus model for an arbitrary evaluation function. -/
def wdModelOf (evalA : WdMode → WdCase → Unit → Unit → Option (Corpus.Verdict WdObs)) :
    Corpus.Model WdMode WdCase Unit Unit WdObs WdObsRep where
  evalA := evalA
  codec := wdCodec
  progs := allWdCases
  queries := [()]
  choices := [()]
  progs_complete := allWdCases_complete
  queries_complete := unit_mem_singleton
  choices_complete := unit_mem_singleton

/-- The Anneal corpus model evaluated by real Trusted `stepMirFn`. -/
def wdModel : Corpus.Model WdMode WdCase Unit Unit WdObs WdObsRep :=
  wdModelOf wdAnnealEval

/-- Optional sub-domain selector (`none` = unified bundle). -/
def domainSel : Option WdDomain → WdCase → Bool
  | none, _ => true
  | some d, i => wdDomainOf i.val == d

/-- MiniRust support gate: exact 3-way cases of the selected sub-domain. -/
def mrGate (sel : Option WdDomain) (i : WdCase) : Bool :=
  wdClassOf i.val == .threeWay && domainSel sel i

/-- LeanMiri support gate: 3-way cases plus the Trusted-agreeing pin-delta case `22`. -/
def lmGate (sel : Option WdDomain) (i : WdCase) : Bool :=
  (wdClassOf i.val == .threeWay || wdClassOf i.val == .pinDelta) && domainSel sel i

/-- Positive witness case of each selection. -/
def okCaseOf : Option WdDomain → WdCase
  | none => 0
  | some .d1 => 0
  | some .d2 => 8
  | some .d3 => 14
  | some .d4 => 20

/-- Fault witness case of each selection. -/
def faultCaseOf : Option WdDomain → WdCase
  | none => 4
  | some .d1 => 4
  | some .d2 => 12
  | some .d3 => 16
  | some .d4 => 21

/-- Tree Borrows flip (case `19`) for the unified and `D3` selections. -/
def flipOf : Option WdDomain → Option (Bool × Bool × WdCase × Unit × Unit)
  | none => some (false, true, 19, (), ())
  | some .d3 => some (false, true, 19, (), ())
  | some _ => none

/-- A corpus side over an arbitrary gate and reference verdict function. -/
def sideOf (sel : Option WdDomain) (gate : Option WdDomain → WdCase → Bool)
    (verdictR : Bool → WdCase → Option (Corpus.Verdict WdObs)) :
    Corpus.Side WdMode Bool WdCase Unit Unit WdObs WdObsRep where
  toAnneal := WdMode.ofTb
  gate := fun _ i _ => gate sel i
  verdictR := fun tb i _ _ => verdictR tb i
  rep := wdEncode
  modes := allTbModes
  modes_complete := allTbModes_complete
  wMode := false
  okProg := okCaseOf sel
  okQuery := ()
  okChoice := ()
  faultProg := faultCaseOf sel
  faultQuery := ()
  faultChoice := ()
  flip := flipOf sel

def mrVerdictFn (tb : Bool) (i : WdCase) : Option (Corpus.Verdict WdObs) := mrVerdict tb i.val

def mrExpectedFn (tb : Bool) (i : WdCase) : Option (Corpus.Verdict WdObs) :=
  cellOf (mrTable tb) i.val

theorem mrVerdictFn_funext : mrVerdictFn = mrExpectedFn :=
  funext fun tb => funext fun i => mrVerdict_cell tb i.val i.isLt

/-- MiniRust side of selection `sel`, directly over `mrWdObserve`. -/
def mrSide (sel : Option WdDomain) : Corpus.Side WdMode Bool WdCase Unit Unit WdObs WdObsRep :=
  sideOf sel mrGate mrVerdictFn

/-- MiniRust certificates for the unified and all four per-domain sides. -/
theorem mrSide_check (sel : Option WdDomain) : (mrSide sel).check wdModel = true := by
  show (sideOf sel mrGate mrVerdictFn).check (wdModelOf wdAnnealEval) = true
  rw [wdAnnealEval_funext, mrVerdictFn_funext]
  cases sel with
  | none => decide +kernel
  | some d => cases d <;> decide +kernel

def lmVerdictFn (A : WdLmAuthority) (tb : Bool) (i : WdCase) : Option (Corpus.Verdict WdObs) :=
  A.verdict tb i.val

def lmExpectedFn (tb : Bool) (i : WdCase) : Option (Corpus.Verdict WdObs) :=
  cellOf (lmTable tb) i.val

theorem lmVerdictFn_funext (A : WdLmAuthority) (hA : lmTableCheckOf A = true) :
    lmVerdictFn A = lmExpectedFn :=
  funext fun tb => funext fun i => lmTableCheckOf_sound A hA tb i.val i.isLt

/-- LeanMiri side of selection `sel` over an arbitrary `WdLmAuthority`. -/
def lmSideOf (sel : Option WdDomain) (A : WdLmAuthority) :
    Corpus.Side WdMode Bool WdCase Unit Unit WdObs WdObsRep :=
  sideOf sel lmGate (lmVerdictFn A)

/-- LeanMiri side certificate of selection `sel`. -/
def lmCheckOf (sel : Option WdDomain) (A : WdLmAuthority) : Bool :=
  (lmSideOf sel A).check wdModel

/-- The 48-cell table certificate implies every LeanMiri side certificate. -/
theorem lmCheckOf_of_table (sel : Option WdDomain) (A : WdLmAuthority)
    (hA : lmTableCheckOf A = true) : lmCheckOf sel A = true := by
  show (sideOf sel lmGate (lmVerdictFn A)).check (wdModelOf wdAnnealEval) = true
  rw [wdAnnealEval_funext, lmVerdictFn_funext A hA]
  cases sel with
  | none => decide +kernel
  | some d => cases d <;> decide +kernel

/-! ## §6. Genuine `DualCorrespondenceBundle` Witnesses (Unified + `D1`–`D4`) -/

/-- The bundle type shared by all five witnesses. -/
abbrev WdBundle : Type :=
  DualCorrespondenceBundle WdMode WdCase Unit WdObs Unit WdObsRep Bool Unit WdObs Unit Bool Unit
    WdObs Unit

/-- Bundle of selection `sel` from a side certificate. -/
def bundleOfSel (sel : Option WdDomain) (A : WdLmAuthority) (hLM : lmCheckOf sel A = true) :
    WdBundle :=
  Corpus.bundle wdModel (mrSide sel) (lmSideOf sel A) (mrSide_check sel) hLM

/-- **Unified 3-way bundle** over all 21 Trusted-agreeing cases × 2 modes. -/
def bundleOf (A : WdLmAuthority) (hA : lmTableCheckOf A = true) : WdBundle :=
  bundleOfSel none A (lmCheckOf_of_table none A hA)

/-- **Per-domain bundle** for `D1`–`D4`. -/
def domainBundleOf (d : WdDomain) (A : WdLmAuthority) (hA : lmTableCheckOf A = true) : WdBundle :=
  bundleOfSel (some d) A (lmCheckOf_of_table (some d) A hA)

theorem mrGate_of_threeWay (sel : Option WdDomain) (i : WdCase)
    (h : wdClassOf i.val = .threeWay) (hd : domainSel sel i = true) : mrGate sel i = true := by
  unfold mrGate; rw [h, hd]; rfl

theorem lmGate_of_threeWay (sel : Option WdDomain) (i : WdCase)
    (h : wdClassOf i.val = .threeWay) (hd : domainSel sel i = true) : lmGate sel i = true := by
  unfold lmGate; rw [h, hd]; rfl

/-- Three-way normal agreement (Trusted ↔ MiniRust ↔ LeanMiri) at every 3-way key of the
unified bundle. -/
theorem threeWayNormalAgreement (A : WdLmAuthority) (hA : lmTableCheckOf A = true)
    (mMR mLM : Bool) (i : WdCase) (hMode : WdMode.ofTb mMR = WdMode.ofTb mLM)
    (hCls : wdClassOf i.val = .threeWay) (vMR vLM : WdObs)
    (hRMR : (bundleOf A hA).mrRel.ExecR mMR i () () (.normal vMR))
    (hRLM : (bundleOf A hA).lmRel.ExecR mLM i () () (.normal vLM)) :
    wdEncode vMR = wdEncode vLM ∧
      ∃ a : WdObs, wdDecode (wdEncode vMR) = some a ∧
        (bundleOf A hA).ExecAnneal (WdMode.ofTb mMR) i () (.normal a) := by
  have hDet : ∀ out out',
      (bundleOf A hA).ExecAnneal ((bundleOf A hA).toAnnealMR mMR) i () out →
      (bundleOf A hA).ExecAnneal ((bundleOf A hA).toAnnealMR mMR) i () out' →
      out = out' := by
    rintro out out' ⟨⟨⟩, h1⟩ ⟨⟨⟩, h2⟩
    exact Option.some.inj (h1.symm.trans h2)
  exact (bundleOf A hA).threeWayNormalAgreement_rep hMode
    (mrGate_of_threeWay none i hCls rfl) (lmGate_of_threeWay none i hCls rfl) hDet hRMR hRLM

/-- Cross-authority fault equivalence between MiniRust and LeanMiri at every 3-way key. -/
theorem crossAuthorityFaultEquiv (A : WdLmAuthority) (hA : lmTableCheckOf A = true)
    (mMR mLM : Bool) (i : WdCase) (hMode : WdMode.ofTb mMR = WdMode.ofTb mLM)
    (hCls : wdClassOf i.val = .threeWay) (k : CorrFaultKind) :
    (∃ c, (bundleOf A hA).mrRel.ExecR mMR i () c (.fault k)) ↔
      (∃ c, (bundleOf A hA).lmRel.ExecR mLM i () c (.fault k)) :=
  (bundleOf A hA).crossAuthorityFaultEquiv hMode
    (mrGate_of_threeWay none i hCls rfl) (lmGate_of_threeWay none i hCls rfl) k

/-- Exact behavioral equivalence on both authorities (reverse totality of both sides). -/
theorem exactBehaviorEq_both (A : WdLmAuthority) (hA : lmTableCheckOf A = true)
    (mMR mLM : Bool) (i : WdCase) (hCls : wdClassOf i.val = .threeWay) :
    ExactBehaviorEq (bundleOf A hA).mrRel mMR i () ∧
    ExactBehaviorEq (bundleOf A hA).lmRel mLM i () :=
  ⟨(bundleOf A hA).mrSim.exactBehaviorEq_of_reverseTotal
      ((mrSide none).reverseTotal wdModel (Bool.and_eq_true _ _ ▸ mrSide_check none).1)
      (mrGate_of_threeWay none i hCls rfl),
   (bundleOf A hA).lmSim.exactBehaviorEq_of_reverseTotal
      ((lmSideOf none A).reverseTotal wdModel
        (Bool.and_eq_true _ _ ▸ lmCheckOf_of_table none A hA).1)
      (lmGate_of_threeWay none i hCls rfl)⟩

/-- Positive projection of the unified bundle onto the Anneal model. -/
theorem projectPositive (A : WdLmAuthority) (hA : lmTableCheckOf A = true) :
    type_of% (bundleOf A hA).projectPositive :=
  (bundleOf A hA).projectPositive

/-- Fault projection of the unified bundle onto the Anneal model. -/
theorem projectFault (A : WdLmAuthority) (hA : lmTableCheckOf A = true) :
    type_of% (bundleOf A hA).projectFault :=
  (bundleOf A hA).projectFault

/-- Non-vacuous Tree Borrows mode-sensitivity witnesses (case `19`, `basic` vs `treeBorrows`)
carried directly by `(bundleOf A hA)` and `(domainBundleOf .d3 A hA)` on BOTH authorities,
while sub-domains `D1`, `D2`, `D4` carry `none` (case `19` is the unique mode-sensitive case). -/
theorem modeSensitivity_present (A : WdLmAuthority) (hA : lmTableCheckOf A = true) :
    (∃ w, (bundleOf A hA).mrFlip.modeSensitivity? = some w ∧ w.m₁ = false ∧ w.m₂ = true ∧ w.p = 19) ∧
    (∃ w, (bundleOf A hA).lmFlip.modeSensitivity? = some w ∧ w.m₁ = false ∧ w.m₂ = true ∧ w.p = 19) ∧
    (∃ w, (domainBundleOf .d3 A hA).mrFlip.modeSensitivity? = some w ∧ w.m₁ = false ∧ w.m₂ = true ∧ w.p = 19) ∧
    (∃ w, (domainBundleOf .d3 A hA).lmFlip.modeSensitivity? = some w ∧ w.m₁ = false ∧ w.m₂ = true ∧ w.p = 19) ∧
    (domainBundleOf .d1 A hA).mrFlip.modeSensitivity? = none ∧
    (domainBundleOf .d1 A hA).lmFlip.modeSensitivity? = none ∧
    (domainBundleOf .d2 A hA).mrFlip.modeSensitivity? = none ∧
    (domainBundleOf .d2 A hA).lmFlip.modeSensitivity? = none ∧
    (domainBundleOf .d4 A hA).mrFlip.modeSensitivity? = none ∧
    (domainBundleOf .d4 A hA).lmFlip.modeSensitivity? = none := by
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- Exact support-gate encoding of the honest Trusted DST boundary (`6`, `7`: excluded from both
`mrGate` and `lmGate`) and the `minirust#300` pin-delta (`22`: excluded from `mrGate` because
pinned `d821c6e3` MiniRust diverges, yet included in `lmGate` with full `ExactBehaviorEq` on
LeanMiri in both the unified and `D4` bundles). -/
theorem bundle_gate_pinDelta_and_dstBoundary (A : WdLmAuthority) (hA : lmTableCheckOf A = true) :
    mrGate none 6 = false ∧ lmGate none 6 = false ∧
    mrGate none 7 = false ∧ lmGate none 7 = false ∧
    mrGate (some .d1) 6 = false ∧ lmGate (some .d1) 6 = false ∧
    mrGate (some .d1) 7 = false ∧ lmGate (some .d1) 7 = false ∧
    mrGate none 22 = false ∧ lmGate none 22 = true ∧
    mrGate (some .d4) 22 = false ∧ lmGate (some .d4) 22 = true ∧
    (∀ mLM : Bool, ExactBehaviorEq (bundleOf A hA).lmRel mLM 22 () ∧
      ExactBehaviorEq (domainBundleOf .d4 A hA).lmRel mLM 22 ()) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro mLM
  exact ⟨(bundleOf A hA).lmSim.exactBehaviorEq_of_reverseTotal
      ((lmSideOf none A).reverseTotal wdModel
        (Bool.and_eq_true _ _ ▸ lmCheckOf_of_table none A hA).1) rfl,
    (domainBundleOf .d4 A hA).lmSim.exactBehaviorEq_of_reverseTotal
      ((lmSideOf (some .d4) A).reverseTotal wdModel
        (Bool.and_eq_true _ _ ▸ lmCheckOf_of_table (some .d4) A hA).1) rfl⟩

/-- Witness polarity and fault-kind pinning on the unified bundle: positive witnesses are case `0`
and fault witnesses are genuine `.undefined` UB (case `4`), never `.unsupported`. -/
theorem unified_bundle_witness_kinds (A : WdLmAuthority) (hA : lmTableCheckOf A = true) :
    let B := bundleOf A hA
    B.mrPositive.p = 0 ∧ B.lmPositive.p = 0 ∧
    B.mrFault.p = 4 ∧ B.lmFault.p = 4 ∧
    B.mrFault.kind = .undefined ∧ B.lmFault.kind = .undefined ∧
    B.mrFlip.kind = .undefined ∧ B.lmFlip.kind = .undefined :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every per-domain bundle carries genuine correspondence / fault-equivalence claims and
non-vacuous flip-direction guards (positive and genuine `.undefined` UB fault witnesses) on BOTH
authorities. -/
theorem domain_bundle_claims (d : WdDomain) (A : WdLmAuthority) (hA : lmTableCheckOf A = true) :
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
    (∃ a r, B.mrRel.ExecA B.mrFlip.m B.mrFlip.pOk B.mrFlip.qOk B.mrFlip.cOk (.normal a) ∧
            B.mrRel.ExecR B.mrFlip.m B.mrFlip.pOk B.mrFlip.qOk B.mrFlip.cOk (.normal r) ∧
            B.mrRel.RetRel a r) ∧
    B.mrRel.ExecA B.mrFlip.m B.mrFlip.pFault B.mrFlip.qFault B.mrFlip.cFault
      (.fault B.mrFlip.kind) ∧
    B.mrRel.ExecR B.mrFlip.m B.mrFlip.pFault B.mrFlip.qFault B.mrFlip.cFault
      (.fault B.mrFlip.kind) ∧
    (∃ a r, B.lmRel.ExecA B.lmFlip.m B.lmFlip.pOk B.lmFlip.qOk B.lmFlip.cOk (.normal a) ∧
            B.lmRel.ExecR B.lmFlip.m B.lmFlip.pOk B.lmFlip.qOk B.lmFlip.cOk (.normal r) ∧
            B.lmRel.RetRel a r) ∧
    B.lmRel.ExecA B.lmFlip.m B.lmFlip.pFault B.lmFlip.qFault B.lmFlip.cFault
      (.fault B.lmFlip.kind) ∧
    B.lmRel.ExecR B.lmFlip.m B.lmFlip.pFault B.lmFlip.qFault B.lmFlip.cFault
      (.fault B.lmFlip.kind) := by
  have hk : ∀ d' : WdDomain,
      (domainBundleOf d' A hA).mrFault.kind = .undefined ∧
      (domainBundleOf d' A hA).lmFault.kind = .undefined ∧
      (domainBundleOf d' A hA).mrFlip.kind = .undefined ∧
      (domainBundleOf d' A hA).lmFlip.kind = .undefined := by
    intro d'
    cases d' <;> exact ⟨rfl, rfl, rfl, rfl⟩
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

/-! ## §7. Exact 48-Cell 3-Way Classification, Honest Trusted Boundary, and `#300` Pin Delta -/

/-- **Exact 3-way classification `↔`** (every in-range cell, both modes): full agreement iff
`threeWay`; MiniRust = LeanMiri with Trusted `.unsupported` iff `dstBoundary` (`6`, `7`);
Trusted = LeanMiri with MiniRust divergent iff `pinDelta` (`22`). -/
theorem dual_exact_three_way_classification (A : WdLmAuthority) (hA : lmTableCheckOf A = true)
    (tb : Bool) (idx : Nat) (hi : idx < mrWdCaseCount) :
    ((trustedVerdict tb idx = mrVerdict tb idx ∧ mrVerdict tb idx = A.verdict tb idx) ↔
        wdClassOf idx = .threeWay) ∧
    ((trustedVerdict tb idx = some .unsupported ∧ mrVerdict tb idx ≠ some .unsupported ∧
        mrVerdict tb idx = A.verdict tb idx) ↔ wdClassOf idx = .dstBoundary) ∧
    ((trustedVerdict tb idx = A.verdict tb idx ∧ mrVerdict tb idx ≠ A.verdict tb idx) ↔
        wdClassOf idx = .pinDelta) := by
  rw [trustedVerdict_cell tb idx hi, mrVerdict_cell tb idx hi, lmTableCheckOf_sound A hA tb idx hi]
  revert hi
  revert idx
  cases tb <;> decide +kernel

/-- **Zero `specPanic` / stuck cells across all 48 in-range cells** on all three authorities
(ensuring `dual_exact_three_way_classification` never holds vacuously via `none = none`). -/
theorem dual_no_specPanic_all_cells (A : WdLmAuthority) (hA : lmTableCheckOf A = true)
    (tb : Bool) (idx : Nat) (hi : idx < mrWdCaseCount) :
    trustedVerdict tb idx ≠ none ∧ mrVerdict tb idx ≠ none ∧
    A.verdict tb idx ≠ none ∧ wdClassOf idx ≠ .outOfRange := by
  rw [trustedVerdict_cell tb idx hi, mrVerdict_cell tb idx hi, lmTableCheckOf_sound A hA tb idx hi]
  revert hi
  revert idx
  cases tb <;> decide +kernel

/-- **Fail-closed `idx ≥ 24`** on all three authorities. -/
theorem dual_fail_closed_out_of_range (A : WdLmAuthority) (hOob : WdLmFailClosed A)
    (tb : Bool) (idx : Nat) (h : mrWdCaseCount ≤ idx) :
    trustedVerdict tb idx = some .unsupported ∧ mrVerdict tb idx = some .unsupported ∧
    A.verdict tb idx = some .unsupported ∧ wdClassOf idx = .outOfRange := by
  refine ⟨trustedVerdict_out_of_range tb idx h, mrVerdict_out_of_range tb idx h, hOob tb idx h, ?_⟩
  unfold mrWdCaseCount at h
  have h1 : ¬(idx = 6 ∨ idx = 7) := by omega
  have h2 : ¬idx = 22 := by omega
  have h3 : ¬idx < 24 := by omega
  unfold wdClassOf
  rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2),
    ite_eq_right_of_eq_false _ _ (eq_false h3)]

/-- **Exact Tree Borrows mode sensitivity on all three authorities**: `tb = false` and `tb = true`
disagree on an in-range case iff it is case `19`. -/
theorem dual_mode_sensitivity_exact (A : WdLmAuthority) (hA : lmTableCheckOf A = true)
    (idx : Nat) (hi : idx < mrWdCaseCount) :
    (trustedVerdict false idx ≠ trustedVerdict true idx ↔ idx = 19) ∧
    (mrVerdict false idx ≠ mrVerdict true idx ↔ idx = 19) ∧
    (A.verdict false idx ≠ A.verdict true idx ↔ idx = 19) := by
  rw [trustedVerdict_cell false idx hi, trustedVerdict_cell true idx hi,
    mrVerdict_cell false idx hi, mrVerdict_cell true idx hi,
    lmTableCheckOf_sound A hA false idx hi, lmTableCheckOf_sound A hA true idx hi]
  revert hi
  revert idx
  decide +kernel

/-- **Case `19` mode sensitivity (concrete)**: `basic` returns `999`, Tree Borrows is UB, on all
three authorities. -/
theorem dual_case19_mode_sensitivity (A : WdLmAuthority) (hA : lmTableCheckOf A = true) :
    trustedVerdict false 19 = some (.returns (.scalar 999)) ∧
    trustedVerdict true 19 = some .undefinedBehavior ∧
    mrVerdict false 19 = some (.returns (.scalar 999)) ∧
    mrVerdict true 19 = some .undefinedBehavior ∧
    A.verdict false 19 = some (.returns (.scalar 999)) ∧
    A.verdict true 19 = some .undefinedBehavior := by
  rw [trustedVerdict_cell false 19 (by decide), trustedVerdict_cell true 19 (by decide),
    mrVerdict_cell false 19 (by decide), mrVerdict_cell true 19 (by decide),
    lmTableCheckOf_sound A hA false 19 (by decide), lmTableCheckOf_sound A hA true 19 (by decide)]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Honest Trusted boundary on trailing-slice DST structs (`6`, `7`)**: MiniRust
`compute_size_and_align` and LeanMiri `sizeAndAlignFromMeta` agree on `okSizeAlign 16 4` /
`okSizeAlign 16 8`, Trusted is `.unsupported` exactly there (`↔`), rooted in
`intrinsicWidePointeeStep` rejecting every custom ADT pointee. -/
theorem dual_dst_honest_trusted_boundary (A : WdLmAuthority) (hA : lmTableCheckOf A = true) :
    (∀ tb, trustedVerdict tb 6 = some .unsupported ∧ trustedVerdict tb 7 = some .unsupported ∧
      mrVerdict tb 6 = some (.returns (.sizeAlign 16 4)) ∧
      mrVerdict tb 7 = some (.returns (.sizeAlign 16 8)) ∧
      A.verdict tb 6 = some (.returns (.sizeAlign 16 4)) ∧
      A.verdict tb 7 = some (.returns (.sizeAlign 16 8))) ∧
    (∀ tb idx, idx < mrWdCaseCount →
      (trustedVerdict tb idx = some .unsupported ↔ (idx = 6 ∨ idx = 7))) ∧
    (∀ (name : Trusted.Rustc.V2026_06_01.MirAst.DefPath)
        (args : List Trusted.Rustc.V2026_06_01.MirAst.RigidTy),
      Trusted.Rustc.V2026_06_01.MirSemantics.intrinsicWidePointeeStep (.adt name args) =
        .unsupported) ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.intrinsicWidePointeeStep wdHeaderSliceRigid =
      .unsupported ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.intrinsicWidePointeeStep wdAlign8TailU16Rigid =
      .unsupported := by
  refine ⟨?_, ?_, trusted_intrinsicWidePointeeStep_adt_unsupported,
    trusted_intrinsicWidePointeeStep_dst_unsupported.1,
    trusted_intrinsicWidePointeeStep_dst_unsupported.2⟩
  · intro tb
    rw [trustedVerdict_cell tb 6 (by decide), trustedVerdict_cell tb 7 (by decide),
      mrVerdict_cell tb 6 (by decide), mrVerdict_cell tb 7 (by decide),
      lmTableCheckOf_sound A hA tb 6 (by decide), lmTableCheckOf_sound A hA tb 7 (by decide)]
    cases tb <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro tb idx hi
    rw [trustedVerdict_cell tb idx hi]
    revert hi
    revert idx
    cases tb <;> decide +kernel

/-- **`minirust#300` pin delta + flip-ready canary.** Case `22`: pinned `d821c6e3` `checkPtr`
accepts the null `FnPtr` (`okFnPtr 0`) while Trusted and LeanMiri reject it (`.ub`). Case `21`:
the post-`#300` predicate `checkPtrFnNonNullM` rejects it, agreeing with Trusted and LeanMiri.
Case `23`: a raw null `*const u8` is accepted by all three. The pinned predicate is pinned by
`mr_minirust300_flip_canary`: after the next `minirust/vendor/` bump past `374bf855`, the
`checkPtr` conjunct and the `mrWdObserve _ 22` cells fail, signalling the flip. -/
theorem dual_minirust300_pin_delta_and_flip_ready (A : WdLmAuthority)
    (hA : lmTableCheckOf A = true) :
    (∀ tb, mrVerdict tb 22 = some (.returns (.fnPtr 0)) ∧
      trustedVerdict tb 22 = some .undefinedBehavior ∧
      A.verdict tb 22 = some .undefinedBehavior) ∧
    (∀ tb, mrVerdict tb 21 = some .undefinedBehavior ∧
      trustedVerdict tb 21 = some .undefinedBehavior ∧
      A.verdict tb 21 = some .undefinedBehavior) ∧
    (∀ tb, mrVerdict tb 23 = some (.returns (.fnPtr 0)) ∧
      trustedVerdict tb 23 = some (.returns (.fnPtr 0)) ∧
      A.verdict tb 23 = some (.returns (.fnPtr 0))) ∧
    (∀ tb, mrVerdict tb 22 ≠ trustedVerdict tb 22 ∧ A.verdict tb 22 = trustedVerdict tb 22) ∧
    type_of% mr_minirust300_flip_canary := by
  refine ⟨?_, ?_, ?_, ?_, mr_minirust300_flip_canary⟩ <;> intro tb <;>
    rw [trustedVerdict_cell tb _ (by decide), mrVerdict_cell tb _ (by decide),
      lmTableCheckOf_sound A hA tb _ (by decide)] <;>
    cases tb <;> decide

/-- **Case `13` (`kani#5205` / `#5196`) contrast**: copying the whole `MaybeUninit<bool>` holding
raw byte `2` succeeds in Trusted and MiniRust (both modes), while the typed `bool` read is UB on
all three authorities; case `12` (typed read of an uninit `MaybeUninit<u32>`) is UB everywhere. -/
theorem dual_case13_union_copy_vs_typed_read (A : WdLmAuthority) (hA : lmTableCheckOf A = true) :
    type_of% mrTrusted_case13_union_copy_of_invalid_bool_byte_ok ∧
    type_of% mr_case13_union_copy_of_invalid_bool_byte_ok ∧
    (∀ tb, trustedVerdict tb 13 = some .undefinedBehavior ∧
      mrVerdict tb 13 = some .undefinedBehavior ∧ A.verdict tb 13 = some .undefinedBehavior) ∧
    (∀ tb, trustedVerdict tb 12 = some .undefinedBehavior ∧
      mrVerdict tb 12 = some .undefinedBehavior ∧ A.verdict tb 12 = some .undefinedBehavior) := by
  refine ⟨mrTrusted_case13_union_copy_of_invalid_bool_byte_ok,
    mr_case13_union_copy_of_invalid_bool_byte_ok, ?_, ?_⟩ <;> intro tb <;>
    rw [trustedVerdict_cell tb _ (by decide), mrVerdict_cell tb _ (by decide),
      lmTableCheckOf_sound A hA tb _ (by decide)] <;>
    cases tb <;> decide

/-- **Case `2` two-query anti-masking.** Case `2` is the `wdCombine` of two queries: a ZST slice
`[()]` of length `5` and an empty `str`. A combined `okSizeAlign 0 1` could in principle hide a
half that `wdCombine` failed closed. This theorem pins EACH half separately: Trusted
(`stepMirFn` on `wdCase2Mir` and `wdCase2StrMir`) and MiniRust (`mrWdProg2` and `mrWdProg2Str` on
`Mach` and `MachTB`) both compute `okSizeAlign 0 1`. The cross-root bridge pins the LeanMiri
halves. -/
theorem dual_case2_two_query_halves_agree :
    wdRunTrusted .sizeAlign wdCase2Mir wdTrustedFuel (wdLiveState wdCase2Mir [wdArrD1]) =
      .okSizeAlign 0 1 ∧
    wdRunTrusted .sizeAlign wdCase2StrMir wdTrustedFuel (wdLiveState wdCase2StrMir [wdArrD1]) =
      .okSizeAlign 0 1 ∧
    wdRun false mrWdProg2 = .okSizeAlign 0 1 ∧ wdRun true mrWdProg2 = .okSizeAlign 0 1 ∧
    wdRun false mrWdProg2Str = .okSizeAlign 0 1 ∧ wdRun true mrWdProg2Str = .okSizeAlign 0 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

open MiniRustSpec.CrossFrameRefAndPanicMR in
/-- **Machine-level `#300` pin delta (where the case 21/22 verdicts come from).** On both `Mach`
and `MachTB`, the pinned `d821c6e3` machine runs the null-`fn()` transmute programs of cases
`21`, `22`, and `23` to completion with NO stop message. So unmodified MiniRust's own execution
accepts the null function pointer. The two cases differ only in the observer's re-validation
predicate: pinned `checkPtrM` for `22` (→ `okFnPtr 0`) versus the Episode 1 post-`#300`
emulation `checkPtrFnNonNullM` for `21` (→ `.ub`). Case `21`'s MiniRust `.ub` is therefore the
`#300` predicate (defined in `WideDstAndMaybeUninitMR`, zero `Interp.lean` edits), not a pinned
interpreter verdict. -/
theorem dual_minirust300_machine_level_pin_delta :
    runStopMsgBasic mrWdProg21 = none ∧ runStopMsgTB mrWdProg21 = none ∧
    runStopMsgBasic mrWdProg22 = none ∧ runStopMsgTB mrWdProg22 = none ∧
    runStopMsgBasic mrWdProg23 = none ∧ runStopMsgTB mrWdProg23 = none ∧
    wdRun false mrWdProg21 = .ub ∧ wdRun true mrWdProg21 = .ub ∧
    wdRun false mrWdProg22 = .okFnPtr 0 ∧ wdRun true mrWdProg22 = .okFnPtr 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ### The MiniRust observer's driver is MiniRust's own `steps` / `stepsTB`

`mrWdObserve` executes programs with `MiniRustSpec.CrossFrameRefAndPanicMR.runToStopM` (which also
returns the machine at the stopping point). These identities show that, projected to the `Stop`,
it is exactly the unmodified `MiniRustSpec.Interp.stepsM` iteration, hence `stepsTB` on `MachTB`
and (through `stepM_bm_eq`) `steps` on `Mach`: no shadow driver. -/

section MiniRustDriver
open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp

/-- Forget the stopping machine of a `runToStopM` result. -/
def stopProj {α : Type} : Except (Stop × α) α → Interp α
  | .ok m => .ok m
  | .error (s, _) => .error s

theorem stepsM_eq_runToStopM {M : Type} [Memory M] [MemoryOps M] (fuel : Nat) (m : Machine M) :
    stepsM fuel m = stopProj (MiniRustSpec.CrossFrameRefAndPanicMR.runToStopM fuel m) := by
  induction fuel generalizing m with
  | zero => rfl
  | succ n ih =>
    unfold stepsM MiniRustSpec.CrossFrameRefAndPanicMR.runToStopM
    cases stepM m with
    | ok m' => exact ih m'
    | error s => rfl

theorem stepsTB_eq_runToStopM (fuel : Nat) (m : MachTB) :
    stepsTB fuel m = stopProj (MiniRustSpec.CrossFrameRefAndPanicMR.runToStopM fuel m) :=
  stepsM_eq_runToStopM fuel m

/-- On `Mach`, the driver is MiniRust's own `steps`. This is the only driver identity that is not
choice-free: it inherits `Classical.choice` from the pre-existing upstream specialization lemma
`MiniRustSpec.Correspondence.stepM_bm_eq`, which is outside this episode's file boundary. For that
reason it is left out of the constructive audit list, while `stepsM_eq_runToStopM` /
`stepsTB_eq_runToStopM` are included. -/
theorem steps_eq_runToStopM_bm (fuel : Nat) (m : Mach) :
    steps fuel m = stopProj (MiniRustSpec.CrossFrameRefAndPanicMR.runToStopM (M := BM) fuel m) := by
  induction fuel generalizing m with
  | zero => rfl
  | succ n ih =>
    unfold steps MiniRustSpec.CrossFrameRefAndPanicMR.runToStopM
    rw [MiniRustSpec.Correspondence.stepM_bm_eq]
    cases step m with
    | ok m' => exact ih m'
    | error s => rfl

end MiniRustDriver

/-! ## §8. Non-Vacuity of the LeanMiri Hypotheses (Root-Side Witness) -/

/-- A root-side authority satisfying `lmTableCheckOf` and `WdLmFailClosed`, built from the REAL
Trusted (`mrTrustedWdObserve`) and MiniRust (`mrWdObserve`) observers: MiniRust on the DST cells
`6` / `7`, Trusted elsewhere. It only witnesses that the capstone's hypotheses are satisfiable;
the semantic LeanMiri closure is in the cross-root bridge over `lmWdObserve`. -/
def rootBackedLmAuthority : WdLmAuthority where
  Obs := MrWdObs
  observe := fun tb idx => if idx = 6 ∨ idx = 7 then mrWdObserve tb idx else mrTrustedWdObserve tb idx
  toVerdict := wdVerdictOf

theorem rootBackedLmAuthority_tableCheck : lmTableCheckOf rootBackedLmAuthority = true := by
  have hcell : ∀ tb idx, idx < mrWdCaseCount →
      rootBackedLmAuthority.verdict tb idx =
        (if idx = 6 ∨ idx = 7 then cellOf (mrTable tb) idx else cellOf (trustedTable tb) idx) := by
    intro tb idx hi
    show wdVerdictOf (if idx = 6 ∨ idx = 7 then mrWdObserve tb idx else mrTrustedWdObserve tb idx) = _
    by_cases h : idx = 6 ∨ idx = 7
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h)]
      exact mrVerdict_cell tb idx hi
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h)]
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

theorem rootBackedLmAuthority_failClosed : WdLmFailClosed rootBackedLmAuthority := by
  intro tb idx h
  have h67 : ¬(idx = 6 ∨ idx = 7) := by unfold mrWdCaseCount at h; omega
  show wdVerdictOf (if idx = 6 ∨ idx = 7 then mrWdObserve tb idx else mrTrustedWdObserve tb idx) = _
  rw [ite_eq_right_of_eq_false _ _ (eq_false h67)]
  exact trustedVerdict_out_of_range tb idx h

/-! ## §9. Capstone -/

/-- **Episode 2 capstone**: for EVERY LeanMiri authority `A` passing the 48-cell certificate and
the fail-closed obligation:
1. the constructive codec is tight and rejects malformed wires;
2. MiniRust certificates hold for the unified and all four per-domain sides, and LeanMiri
   certificates follow from `hA`;
3. three-way normal agreement, cross-authority fault equivalence, exact behavioral equivalence,
   and the positive / fault projections of the unified bundle;
4. non-vacuous Tree Borrows mode sensitivity (case `19`) on both authorities;
5. per-domain bundle claims and flip-direction guards for `D1`–`D4`;
6. the exact 48-cell classification, fail-closed range, exact mode sensitivity, honest DST
   boundary, `#300` pin delta + flip canary, and the case `13` contrast;
7. the MiniRust driver identities (`runToStopM` is `stepsM` / `stepsTB` / `steps`) and the
   Episode 1 MiniRust capstones (real interpreter tables and universal laws). -/
theorem ep2_widedst_maybeuninit_dual_authority_capstone (A : WdLmAuthority)
    (hA : lmTableCheckOf A = true) (hOob : WdLmFailClosed A) :
    wdCodec.TightValidRep ∧
    (∀ b, wdValidRep b ↔ (wdDecode b).isSome = true) ∧
    type_of% wdCodec_rejects_malformed ∧
    (∀ sel, (mrSide sel).check wdModel = true) ∧
    (∀ sel, lmCheckOf sel A = true) ∧
    (∀ (mMR mLM : Bool) (i : WdCase), WdMode.ofTb mMR = WdMode.ofTb mLM →
      wdClassOf i.val = .threeWay → ∀ (vMR vLM : WdObs),
        (bundleOf A hA).mrRel.ExecR mMR i () () (.normal vMR) →
        (bundleOf A hA).lmRel.ExecR mLM i () () (.normal vLM) →
        wdEncode vMR = wdEncode vLM ∧
          ∃ a : WdObs, wdDecode (wdEncode vMR) = some a ∧
            (bundleOf A hA).ExecAnneal (WdMode.ofTb mMR) i () (.normal a)) ∧
    (∀ (mMR mLM : Bool) (i : WdCase), WdMode.ofTb mMR = WdMode.ofTb mLM →
      wdClassOf i.val = .threeWay → ∀ (k : CorrFaultKind),
        ((∃ c, (bundleOf A hA).mrRel.ExecR mMR i () c (.fault k)) ↔
          (∃ c, (bundleOf A hA).lmRel.ExecR mLM i () c (.fault k)))) ∧
    (∀ (mMR mLM : Bool) (i : WdCase), wdClassOf i.val = .threeWay →
      ExactBehaviorEq (bundleOf A hA).mrRel mMR i () ∧
      ExactBehaviorEq (bundleOf A hA).lmRel mLM i ()) ∧
    type_of% (bundleOf A hA).projectPositive ∧
    type_of% (bundleOf A hA).projectFault ∧
    type_of% (modeSensitivity_present A hA) ∧
    type_of% (bundle_gate_pinDelta_and_dstBoundary A hA) ∧
    type_of% (unified_bundle_witness_kinds A hA) ∧
    (∀ d, type_of% (domain_bundle_claims d A hA)) ∧
    (∀ tb idx (hi : idx < mrWdCaseCount), type_of% (dual_exact_three_way_classification A hA tb idx hi)) ∧
    (∀ tb idx (hi : idx < mrWdCaseCount), type_of% (dual_no_specPanic_all_cells A hA tb idx hi)) ∧
    (∀ tb idx (h : mrWdCaseCount ≤ idx), type_of% (dual_fail_closed_out_of_range A hOob tb idx h)) ∧
    (∀ idx (hi : idx < mrWdCaseCount), type_of% (dual_mode_sensitivity_exact A hA idx hi)) ∧
    type_of% (dual_case19_mode_sensitivity A hA) ∧
    type_of% (dual_dst_honest_trusted_boundary A hA) ∧
    type_of% (dual_minirust300_pin_delta_and_flip_ready A hA) ∧
    type_of% (dual_case13_union_copy_vs_typed_read A hA) ∧
    type_of% dual_case2_two_query_halves_agree ∧
    type_of% dual_minirust300_machine_level_pin_delta ∧
    type_of% @stepsM_eq_runToStopM ∧ type_of% stepsTB_eq_runToStopM ∧
    type_of% steps_eq_runToStopM_bm ∧
    type_of% ep1_minirust_widedst_maybeuninit_capstone ∧
    type_of% ep1_minirust_universal_laws_capstone :=
  ⟨wdCodec_tight, wdValidRep_iff_decode_isSome, wdCodec_rejects_malformed,
   mrSide_check, fun sel => lmCheckOf_of_table sel A hA,
   threeWayNormalAgreement A hA, crossAuthorityFaultEquiv A hA, exactBehaviorEq_both A hA,
   (bundleOf A hA).projectPositive, (bundleOf A hA).projectFault,
   modeSensitivity_present A hA, bundle_gate_pinDelta_and_dstBoundary A hA,
   unified_bundle_witness_kinds A hA, fun d => domain_bundle_claims d A hA,
   dual_exact_three_way_classification A hA, dual_no_specPanic_all_cells A hA,
   dual_fail_closed_out_of_range A hOob,
   dual_mode_sensitivity_exact A hA, dual_case19_mode_sensitivity A hA,
   dual_dst_honest_trusted_boundary A hA, dual_minirust300_pin_delta_and_flip_ready A hA,
   dual_case13_union_copy_vs_typed_read A hA,
   dual_case2_two_query_halves_agree, dual_minirust300_machine_level_pin_delta,
   @stepsM_eq_runToStopM, stepsTB_eq_runToStopM, steps_eq_runToStopM_bm,
   ep1_minirust_widedst_maybeuninit_capstone, ep1_minirust_universal_laws_capstone⟩

/-- The capstone is non-vacuous: its hypotheses are inhabited by a root-side authority built
from the real Trusted and MiniRust observers. -/
theorem ep2_widedst_maybeuninit_dual_authority_capstone_nonvacuous :
    type_of% (ep2_widedst_maybeuninit_dual_authority_capstone rootBackedLmAuthority
      rootBackedLmAuthority_tableCheck rootBackedLmAuthority_failClosed) :=
  ep2_widedst_maybeuninit_dual_authority_capstone rootBackedLmAuthority
    rootBackedLmAuthority_tableCheck rootBackedLmAuthority_failClosed

/-! ## §10. Import-Isolation, Constructive-Purity, Reachability, and Axiom Audit -/

section AxiomAudit
open Lean Elab Command

run_cmd do
  let env ← getEnv
  -- 1. Strict direct-import boundary.
  for imp in env.header.imports do
    unless imp.module == `Init || imp.module == `Anneal.DualCorrespondenceBundle ||
        imp.module == `Anneal.Mir.DropBinderAndSubtypeBundle ||
        imp.module == `MiniRustSpec.WideDstAndMaybeUninitMR do
      throwError "import-isolation violation: unexpected direct import {imp.module}"
  -- 2. Zero `Miri.*` / `LeanMiriSpec.*` modules (even transitively).
  for modName in env.header.moduleNames do
    if (`Miri).isPrefixOf modName || (`LeanMiriSpec).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported"
  -- 3. Codecs, classification, side/bundle combinators, certificates, and every lifted dual-authority
  -- theorem except the capstone (which re-exports the Episode 1 MiniRust capstones) are choice-free.
  let ns := `Anneal.Mir.WideDstAndMaybeUninitDualSpec
  let constructiveDecls : List Lean.Name :=
    [ ns ++ `wdCodec, ns ++ `wdEncode_decode_of_valid, ns ++ `wdCodec_tight,
      ns ++ `wdCodec_encode_injective, ns ++ `wdCodec_decode_injective_on_valid,
      ns ++ `wdCodec_rejects_malformed, ns ++ `WdMode.of_toTb, ns ++ `WdMode.to_ofTb,
      ns ++ `allTbModes_complete, ns ++ `allWdCases_complete, ns ++ `wdVerdictOf,
      ns ++ `wdClassOf, ns ++ `wdDomainOf, ns ++ `lmTableCheckOf, ns ++ `lmTableCheckOf_sound,
      ns ++ `lmTableCheckOf_of_eq, ns ++ `cert_transport, ns ++ `wdValidRep_iff_decode_isSome,
      ns ++ `wdModelOf, ns ++ `wdModel, ns ++ `wdAnnealEval,
      ns ++ `wdExpectedAnnealEval, ns ++ `mrVerdict, ns ++ `trustedVerdict,
      ns ++ `mrVerdictFn, ns ++ `lmVerdictFn, ns ++ `sideOf, ns ++ `mrSide,
      ns ++ `lmSideOf, ns ++ `lmCheckOf, ns ++ `bundleOfSel,
      ns ++ `range_map_getD, ns ++ `trustedTable_eq, ns ++ `mrTable_eq,
      ns ++ `trustedVerdict_cell, ns ++ `mrVerdict_cell, ns ++ `trustedVerdict_out_of_range,
      ns ++ `mrVerdict_out_of_range, ns ++ `wdAnnealEval_funext, ns ++ `mrVerdictFn_funext,
      ns ++ `lmVerdictFn_funext, ns ++ `mrSide_check, ns ++ `lmCheckOf_of_table, ns ++ `bundleOf,
      ns ++ `domainBundleOf, ns ++ `mrGate_of_threeWay, ns ++ `lmGate_of_threeWay,
      ns ++ `threeWayNormalAgreement, ns ++ `crossAuthorityFaultEquiv, ns ++ `exactBehaviorEq_both,
      ns ++ `projectPositive, ns ++ `projectFault, ns ++ `modeSensitivity_present,
      ns ++ `bundle_gate_pinDelta_and_dstBoundary, ns ++ `unified_bundle_witness_kinds,
      ns ++ `domain_bundle_claims, ns ++ `dual_exact_three_way_classification,
      ns ++ `dual_no_specPanic_all_cells,
      ns ++ `dual_fail_closed_out_of_range, ns ++ `dual_mode_sensitivity_exact,
      ns ++ `dual_case19_mode_sensitivity, ns ++ `dual_dst_honest_trusted_boundary,
      ns ++ `dual_minirust300_pin_delta_and_flip_ready, ns ++ `dual_case13_union_copy_vs_typed_read,
      ns ++ `rootBackedLmAuthority, ns ++ `rootBackedLmAuthority_tableCheck,
      ns ++ `rootBackedLmAuthority_failClosed,
      ns ++ `stopProj, ns ++ `stepsM_eq_runToStopM, ns ++ `stepsTB_eq_runToStopM ]
  for c in constructiveDecls do
    unless env.contains c do throwError "constructive audit: {c} missing"
    for a in ← liftCoreM <| Lean.collectAxioms c do
      unless a == ``propext || a == ``Quot.sound do
        throwError "constructive decl {c} must not depend on {a}"
  -- Exhaustive constructive purity across the ENTIRE module: every declaration in `ns` except the
  -- exact 3 declarations that re-export upstream Classical.choice (`steps_eq_runToStopM_bm` via
  -- `stepM_bm_eq`, and the two Episode 2 capstones that re-export Episode 1 capstones) MUST lie
  -- strictly in `[propext, Quot.sound]`.
  let choiceAllowlist : List Lean.Name :=
    [ ns ++ `steps_eq_runToStopM_bm,
      ns ++ `ep2_widedst_maybeuninit_dual_authority_capstone,
      ns ++ `ep2_widedst_maybeuninit_dual_authority_capstone_nonvacuous ]
  let mut exhaustiveChoiceFree : Nat := 0
  for (c, _) in env.constants.map₂.toList do
    if ns.isPrefixOf c && !choiceAllowlist.contains c then
      for a in ← liftCoreM <| Lean.collectAxioms c do
        unless a == ``propext || a == ``Quot.sound do
          throwError "exhaustive constructive audit failure: {c} depends on {a}"
      exhaustiveChoiceFree := exhaustiveChoiceFree + 1
  if exhaustiveChoiceFree < 250 then
    throwError "exhaustive constructive audit vacuous: only {exhaustiveChoiceFree} decls checked"
  -- Auditor self-tests: confirm Classical.choice, sorryAx, and Lean.ofReduceBool are caught.
  if (← liftCoreM <| Lean.collectAxioms ``Classical.em).all
      (fun a => a == ``propext || a == ``Quot.sound) then
    throwError "constructive audit self-test failed: Classical.em not caught"
  if (← liftCoreM <| Lean.collectAxioms ``sorryAx).all
      (fun a => a == ``propext || a == ``Quot.sound || a == ``Classical.choice) then
    throwError "axiom audit self-test failed: sorryAx not caught"
  if (← liftCoreM <| Lean.collectAxioms ``Lean.ofReduceBool).all
      (fun a => a == ``propext || a == ``Quot.sound || a == ``Classical.choice) then
    throwError "axiom audit self-test failed: Lean.ofReduceBool not caught"
  -- 4. Zero shadow evaluators: the bundles / capstone reach the REAL interpreters.
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
          `MiniRustSpec.WideDstAndMaybeUninitMR.mrTrustedWdObserve,
          `MiniRustSpec.WideDstAndMaybeUninitMR.mrWdObserve,
          `MiniRustSpec.WideDstAndMaybeUninitMR.mrTrustedWdObserve_table,
          `MiniRustSpec.WideDstAndMaybeUninitMR.mrWdObserve_table,
          `MiniRustSpec.Interp.checkPtrM,
          `MiniRustSpec.WideDstAndMaybeUninitMR.checkPtrFnNonNullM ]),
      (ns ++ `ep2_widedst_maybeuninit_dual_authority_capstone,
        [ `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
          `Trusted.Rustc.V2026_06_01.MirSemantics.decodePtrBytesNoForge,
          `Trusted.Rustc.V2026_06_01.MirSemantics.decodeTypedValueFromBytes,
          `Trusted.Rustc.V2026_06_01.MirSemantics.intrinsicWidePointeeStep,
          `MiniRustSpec.Interp.checkPtrM,
          `MiniRustSpec.Interp.steps,
          `MiniRustSpec.Interp.stepsTB,
          `MiniRustSpec.Interp.stepM,
          `MiniRustSpec.Interp.LayoutStrategy.compute_size_and_align,
          `MiniRustSpec.Interp.ptrOffsetInboundsM,
          `MiniRustSpec.WideDstAndMaybeUninitMR.ep1_minirust_widedst_maybeuninit_capstone ]) ]
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
  if theorems < 30 then
    throwError "axiom audit vacuous: only {theorems} theorems seen"

end AxiomAudit

end Anneal.Mir.WideDstAndMaybeUninitDualSpec
