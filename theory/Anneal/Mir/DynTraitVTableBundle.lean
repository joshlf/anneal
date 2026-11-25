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
import MiniRustSpec.DynTraitVTableMR

/-!
# Episode 2 Dual-Authority Correspondence Bundle (`Anneal.Mir.DynTraitVTableBundle`)

Constructive (`[propext, Quot.sound]`, zero `Classical.choice` in codecs and
bundle combinators) dual-authority correspondence packaging for the 4
`dyn Trait` variants admitted to the Trusted MIR model by Episode 1:

1. `thinUnsize` — `PointerCoercion::Unsize` to `dyn Trait` (`&T`, `&mut T`,
   `*const T`), including the raw-vs-reference validity split
2. `dynUpcastAndNop` — trait upcasting (primary prefix and `TraitVPtr`
   supertrait) and NOP `dyn A -> dyn A` coercions
3. `virtualDispatchAndProtector` — `InstanceKind::Virtual` dispatch on two
   receiver layouts, a wrong-trait receiver vtable, and the Crubit `c16`
   receiver call protector with genuine `basic` vs. `protectedTB` mode
   sensitivity
4. `dynLayoutRawBorrowAndAddrEq` — dynamic `size_of_val`, `core::ptr::addr_eq`
   (`rust#166144`), and wide-pointer `==`

Design:
- **Cross-authority observation domain**: `DynTraitVTableObs` (`u32Val`,
  `usizeVal`, `boolVal`, `widePtr dataId dataOff vtableAllocId`) with the tight
  constructive wire codec `dvCodec`.
- **Authority 0 (Anneal Trusted MIR)**: `dvAnnealEval` runs `runTrustedVerdict`,
  which executes `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` (through
  `MiniRustSpec.DynTraitVTableMR.dvRunTrusted`) on the concrete `CapturedMir`
  fixture of every key (zero shadow evaluators).
- **Authority 1 (MiniRust)**: `mrAuthority` observes
  `MiniRustSpec.DynTraitVTableMR.dvMrObserveClass`, the class (index in the
  duplicate-free dictionary `dvMrObsDict`) of the raw return bytes produced by
  `MiniRustSpec.Interp.{steps, stepsTB}` on `Mach` and `MachTB`.
- **Authority 2 (LeanMiri)**: parameterized over any
  `ObsAuthority DynVtKey DynTraitVTableObs` satisfying
  `lmCheckOf lmAuth = true` (closed in the cross-root kernel bridge in
  `tests/mir/DynTraitVTableTests.lean` directly over
  `LeanMiriSpec.DynTraitVTableLM.dvLmObserve`).
- **Proof architecture**: the interpreter executions are evaluated once, by the
  kernel, in the two 32-key table theorems `dvTrustedObserve_table` and
  `dvMrObserveClass_table` of `MiniRustSpec.DynTraitVTableMR`. This module
  rewrites with those tables and closes every finite certificate with the plain
  `decide` tactic on small table lookups.
- **Strict Import Isolation**: imports `Anneal.DualCorrespondenceBundle`,
  `Anneal.Mir.DropBinderAndSubtypeBundle` (for the authority-agnostic `Corpus`
  layer), and `MiniRustSpec.DynTraitVTableMR`, with NO `LeanMiriSpec.*` import.
-/

namespace Anneal.Mir.DynTraitVTableBundle

open Anneal.DualCorrespondenceBundle
open Anneal.Mir.DropBinderAndSubtypeBundle
open Trusted.Rustc.V2026_06_01 Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec.DynTraitVTableMR

/-! ## §1. Observable Value Domain & Constructive `CodecLaws` -/

/-- Shared cross-authority observable value domain for the 4 `dyn Trait`
variants. A wide pointer is observed as the identity and byte offset of its data
pointer (Trusted allocation / borrow-tag identifier) and the `vtableAllocId` of
its vtable pointer. -/
inductive DynTraitVTableObs : Type where
  | u32Val (bits : Nat)
  | usizeVal (bits : Nat)
  | boolVal (bits : Nat)
  | widePtr (dataId : Nat) (dataOff : Nat) (vtableAllocId : Nat)
  deriving DecidableEq, Repr

/-- Canonical tagged wire representation `(tag, a, b, c)` for
`DynTraitVTableObs`, strictly constructive with tight `ValidRep`. -/
abbrev DynVtRep : Type := Nat × Nat × Nat × Nat

def dvEncode : DynTraitVTableObs → DynVtRep
  | .u32Val n => (0, n, 0, 0)
  | .usizeVal n => (1, n, 0, 0)
  | .boolVal n => (2, n, 0, 0)
  | .widePtr d o v => (3, d, o, v)

def dvDecode (r : DynVtRep) : Option DynTraitVTableObs :=
  match r.1 with
  | 0 => some (.u32Val r.2.1)
  | 1 => some (.usizeVal r.2.1)
  | 2 => some (.boolVal r.2.1)
  | 3 => some (.widePtr r.2.1 r.2.2.1 r.2.2.2)
  | _ => none

/-- A representation is valid when its tag is a scalar tag (`0`, `1`, `2`) with
both padding components zero, or the wide-pointer tag `3`. -/
def dvValidRep (r : DynVtRep) : Prop :=
  (r.1 < 3 ∧ r.2.2.1 = 0 ∧ r.2.2.2 = 0) ∨ r.1 = 3

instance (r : DynVtRep) : Decidable (dvValidRep r) := by
  unfold dvValidRep
  exact inferInstance

/-- Constructive `CodecLaws DynTraitVTableObs (Nat × Nat × Nat × Nat)` (uses
only `[propext, Quot.sound]`, zero `Classical.choice`, with tight `ValidRep`). -/
def dvCodec : CodecLaws DynTraitVTableObs DynVtRep where
  encode := dvEncode
  decode := dvDecode
  ValidRep := dvValidRep
  decode_encode := fun a => by cases a <;> rfl
  encode_valid := fun a => by
    cases a
    · exact Or.inl ⟨(by decide : (0 : Nat) < 3), rfl, rfl⟩
    · exact Or.inl ⟨(by decide : (1 : Nat) < 3), rfl, rfl⟩
    · exact Or.inl ⟨(by decide : (2 : Nat) < 3), rfl, rfl⟩
    · exact Or.inr rfl
  encode_decode_of_valid := fun b a hv hd => by
    rcases b with ⟨t, x, y, z⟩
    rcases hv with ⟨hLt, hy, hz⟩ | h3
    · have hy' : y = 0 := hy
      have hz' : z = 0 := hz
      subst hy' hz'
      match t, hLt with
      | 0, _ => cases hd; rfl
      | 1, _ => cases hd; rfl
      | 2, _ => cases hd; rfl
    · have h3' : t = 3 := h3
      subst h3'
      cases hd
      rfl

theorem dvCodec_tight : dvCodec.TightValidRep := by
  intro b hv
  rcases b with ⟨t, x, y, z⟩
  rcases hv with ⟨hLt, hy, hz⟩ | h3
  · have hy' : y = 0 := hy
    have hz' : z = 0 := hz
    subst hy' hz'
    match t, hLt with
    | 0, _ => exact ⟨.u32Val x, rfl⟩
    | 1, _ => exact ⟨.usizeVal x, rfl⟩
    | 2, _ => exact ⟨.boolVal x, rfl⟩
  · have h3' : t = 3 := h3
    subst h3'
    exact ⟨.widePtr x y z, rfl⟩

/-! ## §2. Mode, Key Enumerations, & Executable Trusted Anneal Model (`dvAnnealEval`) -/

/-- Dual-authority execution mode: basic memory / unprotected borrows vs.
Tree Borrows active-protector enforcement. -/
inductive DynVtMode : Type where
  | basic
  | protectedTB
  deriving DecidableEq, Repr

/-- Unified corpus key across all 2 modes × 4 variants × 4 cases = 32 keys. -/
abbrev DynVtKey : Type := DynVtMode × DynVtVariant × DynVtCase

def dvModeToMr : DynVtMode → DynVtMrMode
  | .basic => .basicMemory
  | .protectedTB => .treeBorrows

def dvMrToMode : DynVtMrMode → DynVtMode
  | .basicMemory => .basic
  | .treeBorrows => .protectedTB

def dvModeToLmTreeBorrows : DynVtMode → Bool
  | .basic => false
  | .protectedTB => true

def dvLmTreeBorrowsToMode : Bool → DynVtMode
  | false => .basic
  | true => .protectedTB

/-- Whether the Trusted initial state installs the active protector. -/
def dvModeProtected : DynVtMode → Bool
  | .basic => false
  | .protectedTB => true

def allDvModes : List DynVtMode := [.basic, .protectedTB]
def allDvMrModes : List DynVtMrMode := [.basicMemory, .treeBorrows]
def allDvLmModes : List Bool := [false, true]

def allDvVariants : List DynVtVariant :=
  [.thinUnsize, .dynUpcastAndNop, .virtualDispatchAndProtector, .dynLayoutRawBorrowAndAddrEq]

def allDvCases : List DynVtCase := [.okPrimary, .okSecondary, .ubFault, .modeCase]

def allDvKeys : List DynVtKey :=
  allDvModes.flatMap fun m =>
    allDvVariants.flatMap fun v =>
      allDvCases.map fun c => (m, v, c)

theorem allDvModes_complete (m : DynVtMode) : m ∈ allDvModes := by
  cases m <;> simp [allDvModes]

theorem allDvMrModes_complete (m : DynVtMrMode) : m ∈ allDvMrModes := by
  cases m <;> simp [allDvMrModes]

theorem allDvLmModes_complete (b : Bool) : b ∈ allDvLmModes := by
  cases b <;> simp [allDvLmModes]

theorem allDvVariants_complete (v : DynVtVariant) : v ∈ allDvVariants := by
  cases v <;> simp [allDvVariants]

theorem allDvCases_complete (c : DynVtCase) : c ∈ allDvCases := by
  cases c <;> simp [allDvCases]

/-- The verdict denoted by a normalized Trusted observation; an execution that
runs out of fuel or returns outside the observable domain has no verdict. -/
def trustedObsVerdict : DynVtTrustedObs → Option (Corpus.Verdict DynTraitVTableObs)
  | .u32Val n => some (.returns (.u32Val n))
  | .usizeVal n => some (.returns (.usizeVal n))
  | .boolVal n => some (.returns (.boolVal n))
  | .widePtr d o v => some (.returns (.widePtr d o v))
  | .ub => some .undefinedBehavior
  | .unsupported => some .unsupported
  | .stuck => none

/-- Execute `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` directly for up to
`fuel` steps and return the observable `Corpus.Verdict DynTraitVTableObs`. -/
def runTrustedVerdict (body : CapturedMir) (fuel : Nat) (s : MachineState) :
    Option (Corpus.Verdict DynTraitVTableObs) :=
  trustedObsVerdict (dvRunTrusted body fuel s)

/-- Direct Trusted Anneal execution for EVERY `(mode, variant, case)` key. Zero
shadow evaluators: every key invokes `runTrustedVerdict` ->
`Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` on the actual `CapturedMir`
fixture (`dvTrustedFixture`) from its initial state (`dvTrustedInit`). -/
def dvAnnealEval (mode : DynVtMode) (v : DynVtVariant) (c : DynVtCase)
    (_ch : Unit) : Option (Corpus.Verdict DynTraitVTableObs) :=
  runTrustedVerdict (dvTrustedFixture (dvModeProtected mode) v c) dvTrustedFuel
    (dvTrustedInit (dvModeProtected mode) v c)

/-- The frozen 32-key verdict table shared by all three authorities. -/
def dvExpectedVerdict (mode : DynVtMode) :
    DynVtVariant → DynVtCase → Option (Corpus.Verdict DynTraitVTableObs)
  | .thinUnsize, .okPrimary => some (.returns (.widePtr 1 0 16384))
  | .thinUnsize, .okSecondary => some (.returns (.widePtr 5 1 16384))
  | .thinUnsize, .ubFault => some .undefinedBehavior
  | .thinUnsize, .modeCase => some (.returns (.widePtr 1 0 16385))
  | .dynUpcastAndNop, .okPrimary => some (.returns (.widePtr 1 0 16388))
  | .dynUpcastAndNop, .okSecondary => some (.returns (.widePtr 1 0 16389))
  | .dynUpcastAndNop, .ubFault => some .undefinedBehavior
  | .dynUpcastAndNop, .modeCase => some (.returns (.widePtr 5 1 16384))
  | .virtualDispatchAndProtector, .okPrimary => some (.returns (.u32Val 2))
  | .virtualDispatchAndProtector, .okSecondary => some (.returns (.u32Val 69))
  | .virtualDispatchAndProtector, .ubFault => some .undefinedBehavior
  | .virtualDispatchAndProtector, .modeCase =>
    match mode with
    | .basic => some (.returns (.u32Val 77))
    | .protectedTB => some .undefinedBehavior
  | .dynLayoutRawBorrowAndAddrEq, .okPrimary => some (.returns (.usizeVal 4))
  | .dynLayoutRawBorrowAndAddrEq, .okSecondary => some (.returns (.boolVal 1))
  | .dynLayoutRawBorrowAndAddrEq, .ubFault => some .undefinedBehavior
  | .dynLayoutRawBorrowAndAddrEq, .modeCase => some (.returns (.boolVal 0))

/-- **Trusted Anneal verdicts are exactly the frozen table**: every key's
`stepMirFn` execution (kernel-checked in `dvTrustedObserve_table`) denotes the
frozen verdict. -/
theorem dvAnnealEval_eq (mode : DynVtMode) (v : DynVtVariant) (c : DynVtCase)
    (u : Unit) : dvAnnealEval mode v c u = dvExpectedVerdict mode v c := by
  show trustedObsVerdict (dvTrustedObserve (dvModeProtected mode) v c) =
    dvExpectedVerdict mode v c
  rw [dvTrustedObserve_table]
  cases mode <;> cases v <;> cases c <;> rfl

/-- The frozen verdict table as an Anneal evaluation function. -/
def dvExpectedEval (mode : DynVtMode) (v : DynVtVariant) (c : DynVtCase)
    (_ch : Unit) : Option (Corpus.Verdict DynTraitVTableObs) :=
  dvExpectedVerdict mode v c

theorem dvAnnealEval_funext : dvAnnealEval = dvExpectedEval :=
  funext fun m => funext fun v => funext fun c => funext fun u => dvAnnealEval_eq m v c u

/-- Anneal corpus model over the 4 `dyn Trait` variants, for an arbitrary
evaluation function. -/
def dvModelOf
    (evalA : DynVtMode → DynVtVariant → DynVtCase → Unit →
      Option (Corpus.Verdict DynTraitVTableObs)) :
    Corpus.Model DynVtMode DynVtVariant DynVtCase Unit DynTraitVTableObs
      DynVtRep where
  evalA := evalA
  codec := dvCodec
  progs := allDvVariants
  queries := allDvCases
  choices := [()]
  progs_complete := allDvVariants_complete
  queries_complete := allDvCases_complete
  choices_complete := fun u => by cases u; simp

/-- Anneal corpus model over the 4 `dyn Trait` variants, evaluated by `dvAnnealEval`. -/
def dvModel :
    Corpus.Model DynVtMode DynVtVariant DynVtCase Unit DynTraitVTableObs
      DynVtRep :=
  dvModelOf dvAnnealEval

/-! ## §3. Concrete MiniRust Authority (`mrAuthority`) Directly Over `MiniRustSpec.Interp` -/

/-- Non-colliding denotation table for the observation classes of
`MiniRustSpec.DynTraitVTableMR.dvMrObserveClass`. The class `i` is the index of
the raw return-byte observation in the kernel-checked duplicate-free dictionary
`dvMrObsDict` (`dvMrObsDict_distinct`). A MiniRust wide pointer denotes the
Trusted wide pointer to the corresponding object: the live data object (at
`640`) is the pointee of Trusted borrow tag `1` (offset `0`), the provenance-free
dangling address `641` is byte offset `1` of the untracked Trusted allocation
`5`, and MiniRust vtable `i` is the Trusted vtable allocation `16384 + i`:

| class | raw MiniRust observation                              | verdict                |
|------:|-------------------------------------------------------|------------------------|
| 0     | wide pointer: data object, vtable `0` (`(u32, Tr)`)   | `widePtr 1 0 16384`    |
| 1     | wide pointer: dangling `641`, vtable `0`              | `widePtr 5 1 16384`    |
| 2     | wide pointer: data object, vtable `1` (`(u64, Tr)`)   | `widePtr 1 0 16385`    |
| 3     | wide pointer: data object, vtable `4` (`(u32, Super)`)| `widePtr 1 0 16388`    |
| 4     | wide pointer: data object, vtable `5` (`(u32, Side)`) | `widePtr 1 0 16389`    |
| 5     | `u32` `2`                                             | `u32Val 2`             |
| 6     | `u32` `69`                                            | `u32Val 69`            |
| 7     | `u32` `77`                                            | `u32Val 77`            |
| 8     | `usize` `4`                                           | `usizeVal 4`           |
| 9     | `bool` `true`                                         | `boolVal 1`            |
| 10    | `bool` `false`                                        | `boolVal 0`            |
| 11    | undefined behavior                                    | `undefinedBehavior`    |
| 12    | unsupported                                           | `unsupported`          | -/
def mrDenote : List (Corpus.Verdict DynTraitVTableObs × Nat) :=
  [ (.returns (.widePtr 1 0 16384), 0),
    (.returns (.widePtr 5 1 16384), 1),
    (.returns (.widePtr 1 0 16385), 2),
    (.returns (.widePtr 1 0 16388), 3),
    (.returns (.widePtr 1 0 16389), 4),
    (.returns (.u32Val 2), 5),
    (.returns (.u32Val 69), 6),
    (.returns (.u32Val 77), 7),
    (.returns (.usizeVal 4), 8),
    (.returns (.boolVal 1), 9),
    (.returns (.boolVal 0), 10),
    (.undefinedBehavior, 11),
    (.unsupported, 12) ]

/-- MiniRust `ObsAuthority` directly invoking
`MiniRustSpec.DynTraitVTableMR.dvMrObserveClass` (which runs
`MiniRustSpec.Interp.steps` / `stepsTB` on `Mach` / `MachTB` and classifies the
raw return bytes). -/
def mrAuthority : Corpus.ObsAuthority DynVtKey DynTraitVTableObs where
  Obs := Nat
  decEq := inferInstance
  observe := fun k => dvMrObserveClass (dvModeToMr k.1) k.2.1 k.2.2
  denote := mrDenote

/-- Checked non-shadowing / injectivity of `mrAuthority.denote`. -/
theorem mrAuthority_denoteConsistent : mrAuthority.denoteConsistent = true := by
  first | decide | rfl

/-- **MiniRust verdicts are exactly the frozen table**: every key's
`MiniRustSpec.Interp` execution (kernel-checked in `dvMrObserveClass_table`)
denotes the frozen verdict. -/
theorem mrAuthority_verdict_eq (mode : DynVtMode) (v : DynVtVariant)
    (c : DynVtCase) :
    mrAuthority.verdict (mode, v, c) = dvExpectedVerdict mode v c := by
  show (dvMrObserveClass (dvModeToMr mode) v c).bind mrAuthority.decode =
    dvExpectedVerdict mode v c
  rw [dvMrObserveClass_table]
  cases mode <;> cases v <;> cases c <;> rfl

/-- The MiniRust reference verdict function of the corpus sides. -/
def mrVerdictFn (m : DynVtMrMode) (v : DynVtVariant) (c : DynVtCase)
    (_ch : Unit) : Option (Corpus.Verdict DynTraitVTableObs) :=
  mrAuthority.verdict (dvMrToMode m, v, c)

/-- The frozen verdict table as a MiniRust reference verdict function. -/
def dvExpectedMrVerdict (m : DynVtMrMode) (v : DynVtVariant) (c : DynVtCase)
    (_ch : Unit) : Option (Corpus.Verdict DynTraitVTableObs) :=
  dvExpectedVerdict (dvMrToMode m) v c

theorem mrVerdictFn_funext : mrVerdictFn = dvExpectedMrVerdict :=
  funext fun m => funext fun v => funext fun c => funext fun _ =>
    mrAuthority_verdict_eq (dvMrToMode m) v c

/-- Unified MiniRust corpus side over an arbitrary reference verdict function,
including the `basicMemory` vs. `treeBorrows` flip on
`virtualDispatchAndProtector.modeCase`. -/
def mrSideOf
    (verdictR : DynVtMrMode → DynVtVariant → DynVtCase → Unit →
      Option (Corpus.Verdict DynTraitVTableObs)) :
    Corpus.Side DynVtMode DynVtMrMode DynVtVariant DynVtCase Unit
      DynTraitVTableObs DynVtRep where
  toAnneal := dvMrToMode
  gate := fun _ _ _ => true
  verdictR := verdictR
  rep := dvEncode
  modes := allDvMrModes
  modes_complete := allDvMrModes_complete
  wMode := .basicMemory
  okProg := .virtualDispatchAndProtector
  okQuery := .okPrimary
  okChoice := ()
  faultProg := .virtualDispatchAndProtector
  faultQuery := .ubFault
  faultChoice := ()
  flip := some (.basicMemory, .treeBorrows, .virtualDispatchAndProtector, .modeCase, ())

/-- Unified MiniRust corpus side covering all 4 variants, including genuine
`basicMemory` vs. `treeBorrows` mode sensitivity on
`virtualDispatchAndProtector.modeCase`. -/
def mrSide :
    Corpus.Side DynVtMode DynVtMrMode DynVtVariant DynVtCase Unit
      DynTraitVTableObs DynVtRep :=
  mrSideOf mrVerdictFn

/-- Full simulation + positive + fault + mode-sensitivity certificate for
MiniRust across ALL 32 `(mode, variant, case)` keys: the Trusted and MiniRust
executions are the kernel-checked tables of
`MiniRustSpec.DynTraitVTableMR`, and the certificate over those tables
is decided here. -/
theorem mrSide_check : mrSide.check dvModel = true := by
  show (mrSideOf mrVerdictFn).check (dvModelOf dvAnnealEval) = true
  rw [dvAnnealEval_funext, mrVerdictFn_funext]
  first | decide | rfl

/-- Per-variant MiniRust side over an arbitrary reference verdict function,
focusing the support gate strictly on variant `v`. -/
def mrVariantSideOf (v : DynVtVariant)
    (verdictR : DynVtMrMode → DynVtVariant → DynVtCase → Unit →
      Option (Corpus.Verdict DynTraitVTableObs)) :
    Corpus.Side DynVtMode DynVtMrMode DynVtVariant DynVtCase Unit
      DynTraitVTableObs DynVtRep where
  toAnneal := dvMrToMode
  gate := fun _ p _ => decide (p = v)
  verdictR := verdictR
  rep := dvEncode
  modes := allDvMrModes
  modes_complete := allDvMrModes_complete
  wMode := .basicMemory
  okProg := v
  okQuery := .okPrimary
  okChoice := ()
  faultProg := v
  faultQuery := .ubFault
  faultChoice := ()
  flip := match v with
    | .virtualDispatchAndProtector =>
      some (.basicMemory, .treeBorrows, .virtualDispatchAndProtector, .modeCase, ())
    | _ => none

/-- Per-variant MiniRust side focusing the support gate strictly on variant `v`,
so each of the 4 `dyn Trait` variants gets its own dedicated `DualCorrespondenceBundle`
with non-vacuous positive and fault witnesses. -/
def mrVariantSide (v : DynVtVariant) :
    Corpus.Side DynVtMode DynVtMrMode DynVtVariant DynVtCase Unit
      DynTraitVTableObs DynVtRep :=
  mrVariantSideOf v mrVerdictFn

/-- Per-variant MiniRust certificates for all 4 variants. -/
theorem mrVariantSide_check (v : DynVtVariant) :
    (mrVariantSide v).check dvModel = true := by
  show (mrVariantSideOf v mrVerdictFn).check (dvModelOf dvAnnealEval) = true
  rw [dvAnnealEval_funext, mrVerdictFn_funext]
  cases v <;> first | decide | rfl

/-! ## §4. Parameterized LeanMiri Side & Dual-Authority `DualCorrespondenceBundle` Builders -/

/-- Unified LeanMiri side parameterized over any
`ObsAuthority DynVtKey DynTraitVTableObs` (closed in the cross-root kernel
bridge over `LeanMiriSpec.DynTraitVTableLM.dvLmObserve`). -/
def lmSideOf (lmAuth : Corpus.ObsAuthority DynVtKey DynTraitVTableObs) :
    Corpus.Side DynVtMode Bool DynVtVariant DynVtCase Unit DynTraitVTableObs
      DynVtRep where
  toAnneal := dvLmTreeBorrowsToMode
  gate := fun _ _ _ => true
  verdictR := fun b v c _ => lmAuth.verdict (dvLmTreeBorrowsToMode b, v, c)
  rep := dvEncode
  modes := allDvLmModes
  modes_complete := allDvLmModes_complete
  wMode := false
  okProg := .virtualDispatchAndProtector
  okQuery := .okPrimary
  okChoice := ()
  faultProg := .virtualDispatchAndProtector
  faultQuery := .ubFault
  faultChoice := ()
  flip := some (false, true, .virtualDispatchAndProtector, .modeCase, ())

/-- Boolean certificate predicate for closing the unified dual-authority bundle
against an arbitrary LeanMiri `ObsAuthority`. -/
def lmCheckOf (lmAuth : Corpus.ObsAuthority DynVtKey DynTraitVTableObs) : Bool :=
  (lmSideOf lmAuth).check dvModel

/-- Extensional congruence for `lmCheckOf`: two LeanMiri `ObsAuthority` records
that produce identical verdicts on every key yield identical `lmCheckOf`
certificates (constructive, `[propext, Quot.sound]` only). -/
theorem lmCheckOf_congr (a1 a2 : Corpus.ObsAuthority DynVtKey DynTraitVTableObs)
    (h : ∀ k, a1.verdict k = a2.verdict k) :
    lmCheckOf a1 = lmCheckOf a2 := by
  have hSide : lmSideOf a1 = lmSideOf a2 := by
    unfold lmSideOf
    congr 1
    funext b v c u
    exact h (dvLmTreeBorrowsToMode b, v, c)
  unfold lmCheckOf
  rw [hSide]

/-- Per-variant LeanMiri side focusing the support gate strictly on variant `v`. -/
def lmVariantSideOf (v : DynVtVariant)
    (lmAuth : Corpus.ObsAuthority DynVtKey DynTraitVTableObs) :
    Corpus.Side DynVtMode Bool DynVtVariant DynVtCase Unit DynTraitVTableObs
      DynVtRep where
  toAnneal := dvLmTreeBorrowsToMode
  gate := fun _ p _ => decide (p = v)
  verdictR := fun b p c _ => lmAuth.verdict (dvLmTreeBorrowsToMode b, p, c)
  rep := dvEncode
  modes := allDvLmModes
  modes_complete := allDvLmModes_complete
  wMode := false
  okProg := v
  okQuery := .okPrimary
  okChoice := ()
  faultProg := v
  faultQuery := .ubFault
  faultChoice := ()
  flip := match v with
    | .virtualDispatchAndProtector =>
      some (false, true, .virtualDispatchAndProtector, .modeCase, ())
    | _ => none

/-- Per-variant LeanMiri certificate predicate. -/
def lmVariantCheckOf (v : DynVtVariant)
    (lmAuth : Corpus.ObsAuthority DynVtKey DynTraitVTableObs) : Bool :=
  (lmVariantSideOf v lmAuth).check dvModel

/-- Extensional congruence for `lmVariantCheckOf`. -/
theorem lmVariantCheckOf_congr (v : DynVtVariant)
    (a1 a2 : Corpus.ObsAuthority DynVtKey DynTraitVTableObs)
    (h : ∀ k, a1.verdict k = a2.verdict k) :
    lmVariantCheckOf v a1 = lmVariantCheckOf v a2 := by
  have hSide : lmVariantSideOf v a1 = lmVariantSideOf v a2 := by
    unfold lmVariantSideOf
    congr 1
    funext b p c u
    exact h (dvLmTreeBorrowsToMode b, p, c)
  unfold lmVariantCheckOf
  rw [hSide]

/-- Unified `DualCorrespondenceBundle` over the 4 `dyn Trait` variants,
parameterized by a verified LeanMiri `ObsAuthority`. -/
def bundleOf (lmAuth : Corpus.ObsAuthority DynVtKey DynTraitVTableObs)
    (hLM : lmCheckOf lmAuth = true) :
    DualCorrespondenceBundle DynVtMode DynVtVariant DynVtCase DynTraitVTableObs
      Unit DynVtRep DynVtMrMode Unit DynTraitVTableObs Unit Bool Unit DynTraitVTableObs
      Unit :=
  Corpus.bundle dvModel mrSide (lmSideOf lmAuth) mrSide_check hLM

/-- Per-variant `DualCorrespondenceBundle` for each of the 4 `dyn Trait` variants. -/
def variantBundleOf (v : DynVtVariant)
    (lmAuth : Corpus.ObsAuthority DynVtKey DynTraitVTableObs)
    (hLM : lmVariantCheckOf v lmAuth = true) :
    DualCorrespondenceBundle DynVtMode DynVtVariant DynVtCase DynTraitVTableObs
      Unit DynVtRep DynVtMrMode Unit DynTraitVTableObs Unit Bool Unit DynTraitVTableObs
      Unit :=
  Corpus.bundle dvModel (mrVariantSide v) (lmVariantSideOf v lmAuth)
    (mrVariantSide_check v) hLM

/-! ## §5. Lifted Dual-Authority Theorems & Flip-Direction / Mode-Sensitivity Witnesses -/

/-- Three-way normal agreement across Anneal (`Trusted`), MiniRust
(`Mach`/`MachTB`), and LeanMiri (`Miri.Interpreter`) at every gated key. -/
theorem threeWayNormalAgreement (lmAuth : Corpus.ObsAuthority DynVtKey DynTraitVTableObs)
    (hLM : lmCheckOf lmAuth = true)
    (mMR : DynVtMrMode) (mLM : Bool) (p : DynVtVariant) (q : DynVtCase)
    (hMode : dvMrToMode mMR = dvLmTreeBorrowsToMode mLM)
    (cMR cLM : Unit) (vMR vLM : DynTraitVTableObs)
    (hRMR : (bundleOf lmAuth hLM).mrRel.ExecR mMR p q cMR (.normal vMR))
    (hRLM : (bundleOf lmAuth hLM).lmRel.ExecR mLM p q cLM (.normal vLM)) :
    dvEncode vMR = dvEncode vLM := by
  have hDet : ∀ out out',
      (bundleOf lmAuth hLM).ExecAnneal ((bundleOf lmAuth hLM).toAnnealMR mMR) p q out →
      (bundleOf lmAuth hLM).ExecAnneal ((bundleOf lmAuth hLM).toAnnealMR mMR) p q out' →
      out = out' := by
    rintro out out' ⟨⟨⟩, h1⟩ ⟨⟨⟩, h2⟩
    exact Option.some.inj (h1.symm.trans h2)
  exact ((bundleOf lmAuth hLM).threeWayNormalAgreement_rep hMode rfl rfl hDet hRMR hRLM).1

/-- Cross-authority fault equivalence between MiniRust and LeanMiri at every
gated key. -/
theorem crossAuthorityFaultEquiv (lmAuth : Corpus.ObsAuthority DynVtKey DynTraitVTableObs)
    (hLM : lmCheckOf lmAuth = true)
    (mMR : DynVtMrMode) (mLM : Bool) (p : DynVtVariant) (q : DynVtCase)
    (hMode : dvMrToMode mMR = dvLmTreeBorrowsToMode mLM) (k : CorrFaultKind) :
    (∃ c, (bundleOf lmAuth hLM).mrRel.ExecR mMR p q c (.fault k)) ↔
    (∃ c, (bundleOf lmAuth hLM).lmRel.ExecR mLM p q c (.fault k)) :=
  (bundleOf lmAuth hLM).crossAuthorityFaultEquiv hMode rfl rfl k

/-- Exact behavioral equivalence on BOTH MiniRust and LeanMiri (reverse totality). -/
theorem exactBehaviorEq_both (lmAuth : Corpus.ObsAuthority DynVtKey DynTraitVTableObs)
    (hLM : lmCheckOf lmAuth = true)
    (mMR : DynVtMrMode) (mLM : Bool) (p : DynVtVariant) (q : DynVtCase) :
    ExactBehaviorEq (bundleOf lmAuth hLM).mrRel mMR p q ∧
    ExactBehaviorEq (bundleOf lmAuth hLM).lmRel mLM p q :=
  ⟨(bundleOf lmAuth hLM).mrSim.exactBehaviorEq_of_reverseTotal
      (mrSide.reverseTotal dvModel (Bool.and_eq_true _ _ ▸ mrSide_check).1) rfl,
   (bundleOf lmAuth hLM).lmSim.exactBehaviorEq_of_reverseTotal
      ((lmSideOf lmAuth).reverseTotal dvModel (Bool.and_eq_true _ _ ▸ hLM).1) rfl⟩

/-- Non-vacuous MiniRust `ModeSensitivityWitness` on
`virtualDispatchAndProtector.modeCase` (`BasicMemory` returns `77`,
`TreeBorrowsMemory` faults with the receiver-protector UB). -/
theorem mr_modeSensitivity_present :
    (mrSide.flipW dvModel mrSide_check).isSome = true := by
  unfold Corpus.Side.flipW
  rfl

/-- Non-vacuous LeanMiri `ModeSensitivityWitness` on
`virtualDispatchAndProtector.modeCase` (`treeBorrows = false` returns `77`;
`treeBorrows = true` faults with a Tree Borrows write conflict on the protected
`Frozen` receiver of the virtual call). -/
theorem lm_modeSensitivity_present
    (lmAuth : Corpus.ObsAuthority DynVtKey DynTraitVTableObs)
    (hLM : lmCheckOf lmAuth = true) :
    ((lmSideOf lmAuth).flipW dvModel hLM).isSome = true := by
  unfold Corpus.Side.flipW
  rfl

/-- Every per-variant bundle carries genuine `correspondenceClaim`,
`faultEquivClaim`, and non-vacuous flip-direction guards (`okAgree`, `faultA`,
`faultR`) on BOTH authorities (ruling out constant-outcome collapse for all 4
variants). -/
theorem variant_bundle_claims (v : DynVtVariant)
    (lmAuth : Corpus.ObsAuthority DynVtKey DynTraitVTableObs)
    (hLM : lmVariantCheckOf v lmAuth = true) :
    let B := variantBundleOf v lmAuth hLM
    CorrespondenceClaim B.mrRel ∧
    FaultEquivClaim B.mrRel ∧
    CorrespondenceClaim B.lmRel ∧
    FaultEquivClaim B.lmRel ∧
    B.mrFlip.m = .basicMemory ∧
    B.lmFlip.m = false ∧
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
      (.fault B.lmFlip.kind) :=
  ⟨(variantBundleOf v lmAuth hLM).mrSim.correspondenceClaim,
   (variantBundleOf v lmAuth hLM).mrSim.faultEquivClaim,
   (variantBundleOf v lmAuth hLM).lmSim.correspondenceClaim,
   (variantBundleOf v lmAuth hLM).lmSim.faultEquivClaim,
   rfl, rfl,
   (variantBundleOf v lmAuth hLM).mrFlip.okAgree,
   (variantBundleOf v lmAuth hLM).mrFlip.faultA,
   (variantBundleOf v lmAuth hLM).mrFlip.faultR,
   (variantBundleOf v lmAuth hLM).lmFlip.okAgree,
   (variantBundleOf v lmAuth hLM).lmFlip.faultA,
   (variantBundleOf v lmAuth hLM).lmFlip.faultR⟩

/-- **Constructive Per-Variant Outcome Distinctness & Non-Degeneracy**:
for EVERY one of the 4 `dyn Trait` variants (`thinUnsize`, `dynUpcastAndNop`,
`virtualDispatchAndProtector`, `dynLayoutRawBorrowAndAddrEq`):
1. `okPrimary` and `okSecondary` return strictly distinct observable values
   (`a ≠ b`) with strictly distinct `dvEncode` wire encodings
   (`dvEncode a ≠ dvEncode b`) on BOTH Trusted Anneal (`dvAnnealEval`) and
   MiniRust (`mrAuthority`);
2. `ubFault` produces `.undefinedBehavior` distinct from both normal return
   verdicts on both authorities;
3. on `virtualDispatchAndProtector.modeCase`, `basic` and `protectedTB` produce strictly
   distinct verdicts on BOTH Trusted Anneal and MiniRust.
Proof is strictly constructive (`[propext, Quot.sound]` only, zero
`Classical.choice`). -/
theorem dv_variant_outcomes_distinct (v : DynVtVariant) :
    (∃ a b,
      dvAnnealEval .basic v .okPrimary () = some (.returns a) ∧
      dvAnnealEval .basic v .okSecondary () = some (.returns b) ∧
      mrAuthority.verdict (.basic, v, .okPrimary) = some (.returns a) ∧
      mrAuthority.verdict (.basic, v, .okSecondary) = some (.returns b) ∧
      a ≠ b ∧
      dvEncode a ≠ dvEncode b) ∧
    dvAnnealEval .basic v .okPrimary () ≠ dvAnnealEval .basic v .ubFault () ∧
    dvAnnealEval .basic v .okSecondary () ≠ dvAnnealEval .basic v .ubFault () ∧
    mrAuthority.verdict (.basic, v, .okPrimary) ≠ mrAuthority.verdict (.basic, v, .ubFault) ∧
    mrAuthority.verdict (.basic, v, .okSecondary) ≠ mrAuthority.verdict (.basic, v, .ubFault) ∧
    dvAnnealEval .basic .virtualDispatchAndProtector .modeCase () ≠
      dvAnnealEval .protectedTB .virtualDispatchAndProtector .modeCase () ∧
    mrAuthority.verdict (.basic, .virtualDispatchAndProtector, .modeCase) ≠
      mrAuthority.verdict (.protectedTB, .virtualDispatchAndProtector, .modeCase) := by
  have hModeA :
      dvAnnealEval .basic .virtualDispatchAndProtector .modeCase () ≠
        dvAnnealEval .protectedTB .virtualDispatchAndProtector .modeCase () := by
    rw [dvAnnealEval_eq, dvAnnealEval_eq]
    intro h
    dsimp only [dvExpectedVerdict] at h
    cases h
  have hModeM :
      mrAuthority.verdict (.basic, .virtualDispatchAndProtector, .modeCase) ≠
        mrAuthority.verdict (.protectedTB, .virtualDispatchAndProtector, .modeCase) := by
    rw [mrAuthority_verdict_eq, mrAuthority_verdict_eq]
    intro h
    dsimp only [dvExpectedVerdict] at h
    cases h
  cases v with
  | thinUnsize =>
    refine ⟨⟨.widePtr 1 0 16384, .widePtr 5 1 16384,
        dvAnnealEval_eq _ _ _ _, dvAnnealEval_eq _ _ _ _,
        mrAuthority_verdict_eq _ _ _, mrAuthority_verdict_eq _ _ _,
        by decide, by decide⟩,
      ?_, ?_, ?_, ?_, hModeA, hModeM⟩
    · rw [dvAnnealEval_eq, dvAnnealEval_eq]; intro h; dsimp only [dvExpectedVerdict] at h; cases h
    · rw [dvAnnealEval_eq, dvAnnealEval_eq]; intro h; dsimp only [dvExpectedVerdict] at h; cases h
    · rw [mrAuthority_verdict_eq, mrAuthority_verdict_eq]; intro h
      dsimp only [dvExpectedVerdict] at h; cases h
    · rw [mrAuthority_verdict_eq, mrAuthority_verdict_eq]; intro h
      dsimp only [dvExpectedVerdict] at h; cases h
  | dynUpcastAndNop =>
    refine ⟨⟨.widePtr 1 0 16388, .widePtr 1 0 16389,
        dvAnnealEval_eq _ _ _ _, dvAnnealEval_eq _ _ _ _,
        mrAuthority_verdict_eq _ _ _, mrAuthority_verdict_eq _ _ _,
        by decide, by decide⟩,
      ?_, ?_, ?_, ?_, hModeA, hModeM⟩
    · rw [dvAnnealEval_eq, dvAnnealEval_eq]; intro h; dsimp only [dvExpectedVerdict] at h; cases h
    · rw [dvAnnealEval_eq, dvAnnealEval_eq]; intro h; dsimp only [dvExpectedVerdict] at h; cases h
    · rw [mrAuthority_verdict_eq, mrAuthority_verdict_eq]; intro h
      dsimp only [dvExpectedVerdict] at h; cases h
    · rw [mrAuthority_verdict_eq, mrAuthority_verdict_eq]; intro h
      dsimp only [dvExpectedVerdict] at h; cases h
  | virtualDispatchAndProtector =>
    refine ⟨⟨.u32Val 2, .u32Val 69,
        dvAnnealEval_eq _ _ _ _, dvAnnealEval_eq _ _ _ _,
        mrAuthority_verdict_eq _ _ _, mrAuthority_verdict_eq _ _ _,
        by decide, by decide⟩,
      ?_, ?_, ?_, ?_, hModeA, hModeM⟩
    · rw [dvAnnealEval_eq, dvAnnealEval_eq]; intro h; dsimp only [dvExpectedVerdict] at h; cases h
    · rw [dvAnnealEval_eq, dvAnnealEval_eq]; intro h; dsimp only [dvExpectedVerdict] at h; cases h
    · rw [mrAuthority_verdict_eq, mrAuthority_verdict_eq]; intro h
      dsimp only [dvExpectedVerdict] at h; cases h
    · rw [mrAuthority_verdict_eq, mrAuthority_verdict_eq]; intro h
      dsimp only [dvExpectedVerdict] at h; cases h
  | dynLayoutRawBorrowAndAddrEq =>
    refine ⟨⟨.usizeVal 4, .boolVal 1,
        dvAnnealEval_eq _ _ _ _, dvAnnealEval_eq _ _ _ _,
        mrAuthority_verdict_eq _ _ _, mrAuthority_verdict_eq _ _ _,
        by decide, by decide⟩,
      ?_, ?_, ?_, ?_, hModeA, hModeM⟩
    · rw [dvAnnealEval_eq, dvAnnealEval_eq]; intro h; dsimp only [dvExpectedVerdict] at h; cases h
    · rw [dvAnnealEval_eq, dvAnnealEval_eq]; intro h; dsimp only [dvExpectedVerdict] at h; cases h
    · rw [mrAuthority_verdict_eq, mrAuthority_verdict_eq]; intro h
      dsimp only [dvExpectedVerdict] at h; cases h
    · rw [mrAuthority_verdict_eq, mrAuthority_verdict_eq]; intro h
      dsimp only [dvExpectedVerdict] at h; cases h

/-- **Episode 2 Capstone**: for EVERY LeanMiri observation authority `lmAuth`
that passes the unified 32-key check (`lmCheckOf lmAuth = true`), the 4
`dyn Trait` variants `thinUnsize`, `dynUpcastAndNop`,
`virtualDispatchAndProtector`, and `dynLayoutRawBorrowAndAddrEq` satisfy, in one
statement:
1. the observation codec is tight (`dvCodec.TightValidRep`) and the MiniRust
   authority's denotation table is consistent;
2. the unified 32-key MiniRust side check and all 4 per-variant side checks hold
   against the Trusted model `dvModel`;
3. three-way normal agreement, cross-authority fault equivalence, and exact
   behavioral equivalence on both authorities, at the unified bundle
   `bundleOf lmAuth hLM`;
4. non-vacuous mode sensitivity on both authorities (the Crubit `c16` receiver
   protector);
5. for every variant whose per-variant LeanMiri check holds, the per-variant
   bundle carries the correspondence and fault-equivalence claims and the
   flip-direction guards of `variant_bundle_claims`;
6. per-variant outcome distinctness (`dv_variant_outcomes_distinct`).
Each conjunct is the statement of the named theorem of this module; the proof
adds no reasoning of its own. -/
theorem ep2_dyn_trait_vtable_capstone
    (lmAuth : Corpus.ObsAuthority DynVtKey DynTraitVTableObs)
    (hLM : lmCheckOf lmAuth = true) :
    dvCodec.TightValidRep ∧
    mrAuthority.denoteConsistent = true ∧
    mrSide.check dvModel = true ∧
    (∀ v, (mrVariantSide v).check dvModel = true) ∧
    (∀ (mMR : DynVtMrMode) (mLM : Bool) (p : DynVtVariant) (q : DynVtCase),
      dvMrToMode mMR = dvLmTreeBorrowsToMode mLM →
      ∀ (cMR cLM : Unit) (vMR vLM : DynTraitVTableObs),
        (bundleOf lmAuth hLM).mrRel.ExecR mMR p q cMR (.normal vMR) →
        (bundleOf lmAuth hLM).lmRel.ExecR mLM p q cLM (.normal vLM) →
        dvEncode vMR = dvEncode vLM) ∧
    (∀ (mMR : DynVtMrMode) (mLM : Bool) (p : DynVtVariant) (q : DynVtCase),
      dvMrToMode mMR = dvLmTreeBorrowsToMode mLM →
      ∀ (k : CorrFaultKind),
        ((∃ c, (bundleOf lmAuth hLM).mrRel.ExecR mMR p q c (.fault k)) ↔
         (∃ c, (bundleOf lmAuth hLM).lmRel.ExecR mLM p q c (.fault k)))) ∧
    (∀ (mMR : DynVtMrMode) (mLM : Bool) (p : DynVtVariant) (q : DynVtCase),
      ExactBehaviorEq (bundleOf lmAuth hLM).mrRel mMR p q ∧
      ExactBehaviorEq (bundleOf lmAuth hLM).lmRel mLM p q) ∧
    (mrSide.flipW dvModel mrSide_check).isSome = true ∧
    ((lmSideOf lmAuth).flipW dvModel hLM).isSome = true ∧
    (∀ (v : DynVtVariant) (hV : lmVariantCheckOf v lmAuth = true),
      let B := variantBundleOf v lmAuth hV
      CorrespondenceClaim B.mrRel ∧
      FaultEquivClaim B.mrRel ∧
      CorrespondenceClaim B.lmRel ∧
      FaultEquivClaim B.lmRel ∧
      B.mrFlip.m = .basicMemory ∧
      B.lmFlip.m = false ∧
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
        (.fault B.lmFlip.kind)) ∧
    (∀ v : DynVtVariant,
      (∃ a b,
        dvAnnealEval .basic v .okPrimary () = some (.returns a) ∧
        dvAnnealEval .basic v .okSecondary () = some (.returns b) ∧
        mrAuthority.verdict (.basic, v, .okPrimary) = some (.returns a) ∧
        mrAuthority.verdict (.basic, v, .okSecondary) = some (.returns b) ∧
        a ≠ b ∧
        dvEncode a ≠ dvEncode b) ∧
      dvAnnealEval .basic v .okPrimary () ≠ dvAnnealEval .basic v .ubFault () ∧
      dvAnnealEval .basic v .okSecondary () ≠ dvAnnealEval .basic v .ubFault () ∧
      mrAuthority.verdict (.basic, v, .okPrimary) ≠ mrAuthority.verdict (.basic, v, .ubFault) ∧
      mrAuthority.verdict (.basic, v, .okSecondary) ≠ mrAuthority.verdict (.basic, v, .ubFault) ∧
      dvAnnealEval .basic .virtualDispatchAndProtector .modeCase () ≠
        dvAnnealEval .protectedTB .virtualDispatchAndProtector .modeCase () ∧
      mrAuthority.verdict (.basic, .virtualDispatchAndProtector, .modeCase) ≠
        mrAuthority.verdict (.protectedTB, .virtualDispatchAndProtector, .modeCase)) :=
  ⟨dvCodec_tight, mrAuthority_denoteConsistent, mrSide_check, mrVariantSide_check,
   threeWayNormalAgreement lmAuth hLM,
   crossAuthorityFaultEquiv lmAuth hLM,
   exactBehaviorEq_both lmAuth hLM,
   mr_modeSensitivity_present,
   lm_modeSensitivity_present lmAuth hLM,
   fun v hV => variant_bundle_claims v lmAuth hV,
   dv_variant_outcomes_distinct⟩

end Anneal.Mir.DynTraitVTableBundle
