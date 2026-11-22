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
import MiniRustSpec.NullaryAndPtrCoercionMR

/-!
# Episode 2 Dual-Authority Correspondence Bundle (`Anneal.Mir.NullaryAndPtrCoercionBundle`)

Constructive (`[propext, Quot.sound]`, zero `Classical.choice` in codecs and
bundle combinators) dual-authority correspondence packaging for 4
already-trusted MIR variants:

1. `Rvalue.nullaryOp` (`size_of`, `align_of`, `offset_of!`, `ub_checks`)
2. `CastKind.pointerCoercion` (`ReifyFnPointer -> UnsafeFnPointer`, `Unsize`,
   `MutToConstPointer`, `ArrayToPointer`)
3. `CastKind.fnPtrToPtr`
4. `ProjectionElem.unwrapUnsafeBinder` (round-trip, binder struct, dead-local
   UB, and genuine `basic` vs. `protectedTB` active-protector mode sensitivity)

Design:
- **Authority 0 (Anneal Trusted MIR)**: `npAnnealEval` runs `runTrustedVerdict`,
  which executes `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` (through
  `MiniRustSpec.NullaryAndPtrCoercionMR.npRunTrusted`) on the concrete
  `CapturedMir` fixture of every key (zero shadow evaluators).
- **Authority 1 (MiniRust)**: `mrAuthority` observes
  `MiniRustSpec.NullaryAndPtrCoercionMR.npMrObserveClass`, the class (index in
  the duplicate-free dictionary `npMrObsDict`) of the raw return bytes produced
  by `MiniRustSpec.Interp.{steps, stepsTB}` on `Mach` and `MachTB`.
- **Authority 2 (LeanMiri)**: parameterized over any
  `ObsAuthority NullaryPtrKey NullaryPtrObsVal` satisfying
  `lmCheckOf lmAuth = true` (closed in the cross-root kernel bridge in
  `tests/mir/NullaryAndPtrCoercionCorrTests.lean` directly over
  `LeanMiriSpec.NullaryAndPtrCoercionLM.npLmObserve`).
- **Proof architecture**: the interpreter executions are evaluated once, by the
  kernel, in the two 32-key table theorems `npTrustedObserve_table` and
  `npMrObserveClass_table` of `MiniRustSpec.NullaryAndPtrCoercionMR`. This
  module rewrites with those tables and closes every finite certificate with
  the plain `decide` tactic on small table lookups.
- **Strict Import Isolation**: imports `Anneal.DualCorrespondenceBundle`,
  `Anneal.Mir.DropBinderAndSubtypeBundle` (for the authority-agnostic `Corpus`
  layer), and `MiniRustSpec.NullaryAndPtrCoercionMR`, with NO `LeanMiriSpec.*`
  import.
-/

namespace Anneal.Mir.NullaryAndPtrCoercionBundle

open Anneal.DualCorrespondenceBundle
open Anneal.Mir.DropBinderAndSubtypeBundle
open Trusted.Rustc.V2026_06_01 Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec.NullaryAndPtrCoercionMR

/-! ## §1. Observable Value Domain & Constructive `CodecLaws` -/

/-- Shared observable value domain for the 4 MIR variants. -/
inductive NullaryPtrObsVal : Type where
  | u32Val (bits : Nat)
  | u8Val (bits : Nat)
  | usizeVal (bits : Nat)
  | ptrAlloc (allocId : Nat)
  deriving DecidableEq, Repr

/-- Canonical tagged-pair wire representation (`tag, payload`) for
`NullaryPtrObsVal`, strictly constructive with tight `ValidRep`. -/
abbrev NullaryPtrRep : Type := Nat × Nat

def npEncode : NullaryPtrObsVal → NullaryPtrRep
  | .u32Val n => (0, n)
  | .u8Val n => (1, n)
  | .usizeVal n => (2, n)
  | .ptrAlloc aid => (3, aid)

def npDecode : NullaryPtrRep → Option NullaryPtrObsVal
  | (0, n) => some (.u32Val n)
  | (1, n) => some (.u8Val n)
  | (2, n) => some (.usizeVal n)
  | (3, aid) => some (.ptrAlloc aid)
  | _ => none

def npValidRep : NullaryPtrRep → Prop
  | (0, _) => True
  | (1, _) => True
  | (2, _) => True
  | (3, _) => True
  | _ => False

/-- Constructive `CodecLaws NullaryPtrObsVal (Nat × Nat)` (uses only
`[propext, Quot.sound]`, zero `Classical.choice`, with tight `ValidRep`). -/
def npCodec : CodecLaws NullaryPtrObsVal NullaryPtrRep where
  encode := npEncode
  decode := npDecode
  ValidRep := npValidRep
  decode_encode := fun a => by cases a <;> rfl
  encode_valid := fun a => by cases a <;> exact True.intro
  encode_decode_of_valid := fun b a hv hd => by
    rcases b with ⟨t, x⟩
    match t with
    | 0 => cases hd; rfl
    | 1 => cases hd; rfl
    | 2 => cases hd; rfl
    | 3 => cases hd; rfl
    | n + 4 => exact False.elim hv

theorem npCodec_tight : npCodec.TightValidRep := by
  intro b hv
  rcases b with ⟨t, x⟩
  match t with
  | 0 => exact ⟨.u32Val x, rfl⟩
  | 1 => exact ⟨.u8Val x, rfl⟩
  | 2 => exact ⟨.usizeVal x, rfl⟩
  | 3 => exact ⟨.ptrAlloc x, rfl⟩
  | n + 4 => exact False.elim hv

/-! ## §2. Mode, Key Enumerations, & Executable Trusted Anneal Model (`npAnnealEval`) -/

/-- Dual-authority execution mode: basic memory / unprotected borrows vs.
Tree Borrows active-protector enforcement. -/
inductive NullaryPtrMode : Type where
  | basic
  | protectedTB
  deriving DecidableEq, Repr

/-- Unified corpus key across all 2 modes × 4 variants × 4 cases = 32 keys. -/
abbrev NullaryPtrKey : Type := NullaryPtrMode × NullaryPtrVariant × NullaryPtrCase

def npModeToMr : NullaryPtrMode → NullaryPtrMrMode
  | .basic => .basicMemory
  | .protectedTB => .treeBorrows

def npMrToMode : NullaryPtrMrMode → NullaryPtrMode
  | .basicMemory => .basic
  | .treeBorrows => .protectedTB

def npModeToLmTreeBorrows : NullaryPtrMode → Bool
  | .basic => false
  | .protectedTB => true

def npLmTreeBorrowsToMode : Bool → NullaryPtrMode
  | false => .basic
  | true => .protectedTB

/-- Whether the Trusted initial state installs the active protector. -/
def npModeProtected : NullaryPtrMode → Bool
  | .basic => false
  | .protectedTB => true

def allNpModes : List NullaryPtrMode := [.basic, .protectedTB]
def allNpMrModes : List NullaryPtrMrMode := [.basicMemory, .treeBorrows]
def allNpLmModes : List Bool := [false, true]

def allNpVariants : List NullaryPtrVariant :=
  [.nullaryOp, .pointerCoercion, .fnPtrToPtr, .unwrapUnsafeBinder]

def allNpCases : List NullaryPtrCase := [.okPrimary, .okSecondary, .ubFault, .modeCase]

def allNpKeys : List NullaryPtrKey :=
  allNpModes.flatMap fun m =>
    allNpVariants.flatMap fun v =>
      allNpCases.map fun c => (m, v, c)

theorem allNpModes_complete (m : NullaryPtrMode) : m ∈ allNpModes := by
  cases m <;> simp [allNpModes]

theorem allNpMrModes_complete (m : NullaryPtrMrMode) : m ∈ allNpMrModes := by
  cases m <;> simp [allNpMrModes]

theorem allNpLmModes_complete (b : Bool) : b ∈ allNpLmModes := by
  cases b <;> simp [allNpLmModes]

theorem allNpVariants_complete (v : NullaryPtrVariant) : v ∈ allNpVariants := by
  cases v <;> simp [allNpVariants]

theorem allNpCases_complete (c : NullaryPtrCase) : c ∈ allNpCases := by
  cases c <;> simp [allNpCases]

/-- The verdict denoted by a normalized Trusted observation; an execution that
runs out of fuel or returns outside the observable domain has no verdict. -/
def trustedObsVerdict : NullaryPtrTrustedObs → Option (Corpus.Verdict NullaryPtrObsVal)
  | .u32Val n => some (.returns (.u32Val n))
  | .u8Val n => some (.returns (.u8Val n))
  | .usizeVal n => some (.returns (.usizeVal n))
  | .ptrAlloc aid => some (.returns (.ptrAlloc aid))
  | .ub => some .undefinedBehavior
  | .unsupported => some .unsupported
  | .stuck => none

/-- Execute `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` directly for up to
`fuel` steps and return the observable `Corpus.Verdict NullaryPtrObsVal`. -/
def runTrustedVerdict (body : CapturedMir) (fuel : Nat) (s : MachineState) :
    Option (Corpus.Verdict NullaryPtrObsVal) :=
  trustedObsVerdict (npRunTrusted body fuel s)

/-- Direct Trusted Anneal execution for EVERY `(mode, variant, case)` key. Zero
shadow evaluators: every key invokes `runTrustedVerdict` ->
`Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` on the actual `CapturedMir`
fixture (`npTrustedFixture`) from its initial state (`npTrustedInit`). -/
def npAnnealEval (mode : NullaryPtrMode) (v : NullaryPtrVariant) (c : NullaryPtrCase)
    (_ch : Unit) : Option (Corpus.Verdict NullaryPtrObsVal) :=
  runTrustedVerdict (npTrustedFixture v c) npTrustedFuel
    (npTrustedInit (npModeProtected mode) v c)

/-- The frozen 32-key verdict table shared by all three authorities. -/
def npExpectedVerdict (mode : NullaryPtrMode) :
    NullaryPtrVariant → NullaryPtrCase → Option (Corpus.Verdict NullaryPtrObsVal)
  | .nullaryOp, .okPrimary => some (.returns (.usizeVal 36))
  | .nullaryOp, .okSecondary => some (.returns (.u8Val 1))
  | .nullaryOp, .ubFault => some .undefinedBehavior
  | .nullaryOp, .modeCase => some (.returns (.usizeVal 4))
  | .pointerCoercion, .okPrimary => some (.returns (.ptrAlloc 65536))
  | .pointerCoercion, .okSecondary => some (.returns (.usizeVal 3))
  | .pointerCoercion, .ubFault => some .undefinedBehavior
  | .pointerCoercion, .modeCase => some (.returns (.ptrAlloc 5))
  | .fnPtrToPtr, .okPrimary => some (.returns (.ptrAlloc 65536))
  | .fnPtrToPtr, .okSecondary => some (.returns (.ptrAlloc 65537))
  | .fnPtrToPtr, .ubFault => some .undefinedBehavior
  | .fnPtrToPtr, .modeCase => some .undefinedBehavior
  | .unwrapUnsafeBinder, .okPrimary => some (.returns (.u32Val 73))
  | .unwrapUnsafeBinder, .okSecondary => some (.returns (.u8Val 7))
  | .unwrapUnsafeBinder, .ubFault => some .undefinedBehavior
  | .unwrapUnsafeBinder, .modeCase =>
    match mode with
    | .basic => some (.returns (.u32Val 42))
    | .protectedTB => some .undefinedBehavior

/-- **Trusted Anneal verdicts are exactly the frozen table**: every key's
`stepMirFn` execution (kernel-checked in `npTrustedObserve_table`) denotes the
frozen verdict. -/
theorem npAnnealEval_eq (mode : NullaryPtrMode) (v : NullaryPtrVariant) (c : NullaryPtrCase)
    (u : Unit) : npAnnealEval mode v c u = npExpectedVerdict mode v c := by
  show trustedObsVerdict (npTrustedObserve (npModeProtected mode) v c) =
    npExpectedVerdict mode v c
  rw [npTrustedObserve_table]
  cases mode <;> cases v <;> cases c <;> rfl

/-- The frozen verdict table as an Anneal evaluation function. -/
def npExpectedEval (mode : NullaryPtrMode) (v : NullaryPtrVariant) (c : NullaryPtrCase)
    (_ch : Unit) : Option (Corpus.Verdict NullaryPtrObsVal) :=
  npExpectedVerdict mode v c

theorem npAnnealEval_funext : npAnnealEval = npExpectedEval :=
  funext fun m => funext fun v => funext fun c => funext fun u => npAnnealEval_eq m v c u

/-- Anneal corpus model over the 4 MIR variants, for an arbitrary evaluation
function. -/
def npModelOf
    (evalA : NullaryPtrMode → NullaryPtrVariant → NullaryPtrCase → Unit →
      Option (Corpus.Verdict NullaryPtrObsVal)) :
    Corpus.Model NullaryPtrMode NullaryPtrVariant NullaryPtrCase Unit NullaryPtrObsVal
      NullaryPtrRep where
  evalA := evalA
  codec := npCodec
  progs := allNpVariants
  queries := allNpCases
  choices := [()]
  progs_complete := allNpVariants_complete
  queries_complete := allNpCases_complete
  choices_complete := fun u => by cases u; simp

/-- Anneal corpus model over the 4 MIR variants, evaluated by `npAnnealEval`. -/
def npModel :
    Corpus.Model NullaryPtrMode NullaryPtrVariant NullaryPtrCase Unit NullaryPtrObsVal
      NullaryPtrRep :=
  npModelOf npAnnealEval

/-! ## §3. Concrete MiniRust Authority (`mrAuthority`) Directly Over `MiniRustSpec.Interp` -/

/-- Non-colliding denotation table for the observation classes of
`MiniRustSpec.NullaryAndPtrCoercionMR.npMrObserveClass`. The class `i` is the
index of the raw return-byte observation in the kernel-checked duplicate-free
dictionary `npMrObsDict` (`npMrObsDict_distinct`):

| class | raw MiniRust observation                        | verdict            |
|------:|-------------------------------------------------|--------------------|
| 0     | `usize` `36`                                    | `usizeVal 36`      |
| 1     | `bool` `true`                                   | `u8Val 1`          |
| 2     | `usize` `4`                                     | `usizeVal 4`       |
| 3     | pointer to function allocation `0` (at `4096`)  | `ptrAlloc 65536`   |
| 4     | `usize` `3`                                     | `usizeVal 3`       |
| 5     | pointer to the array allocation `2` (at `1024`) | `ptrAlloc 5`       |
| 6     | pointer to function allocation `1` (at `8192`)  | `ptrAlloc 65537`   |
| 7     | `u32` `73`                                      | `u32Val 73`        |
| 8     | `u8` `7`                                        | `u8Val 7`          |
| 9     | `u32` `42`                                      | `u32Val 42`        |
| 10    | undefined behavior                              | `undefinedBehavior`|
| 11    | unsupported                                     | `unsupported`      | -/
def mrDenote : List (Corpus.Verdict NullaryPtrObsVal × Nat) :=
  [ (.returns (.usizeVal 36), 0),
    (.returns (.u8Val 1), 1),
    (.returns (.usizeVal 4), 2),
    (.returns (.ptrAlloc 65536), 3),
    (.returns (.usizeVal 3), 4),
    (.returns (.ptrAlloc 5), 5),
    (.returns (.ptrAlloc 65537), 6),
    (.returns (.u32Val 73), 7),
    (.returns (.u8Val 7), 8),
    (.returns (.u32Val 42), 9),
    (.undefinedBehavior, 10),
    (.unsupported, 11) ]

/-- MiniRust `ObsAuthority` directly invoking
`MiniRustSpec.NullaryAndPtrCoercionMR.npMrObserveClass` (which runs
`MiniRustSpec.Interp.steps` / `stepsTB` on `Mach` / `MachTB` and classifies the
raw return bytes). -/
def mrAuthority : Corpus.ObsAuthority NullaryPtrKey NullaryPtrObsVal where
  Obs := Nat
  decEq := inferInstance
  observe := fun k => npMrObserveClass (npModeToMr k.1) k.2.1 k.2.2
  denote := mrDenote

/-- Checked non-shadowing / injectivity of `mrAuthority.denote`. -/
theorem mrAuthority_denoteConsistent : mrAuthority.denoteConsistent = true := by
  first | decide | rfl

/-- **MiniRust verdicts are exactly the frozen table**: every key's
`MiniRustSpec.Interp` execution (kernel-checked in `npMrObserveClass_table`)
denotes the frozen verdict. -/
theorem mrAuthority_verdict_eq (mode : NullaryPtrMode) (v : NullaryPtrVariant)
    (c : NullaryPtrCase) :
    mrAuthority.verdict (mode, v, c) = npExpectedVerdict mode v c := by
  show (npMrObserveClass (npModeToMr mode) v c).bind mrAuthority.decode =
    npExpectedVerdict mode v c
  rw [npMrObserveClass_table]
  cases mode <;> cases v <;> cases c <;> rfl

/-- The MiniRust reference verdict function of the corpus sides. -/
def mrVerdictFn (m : NullaryPtrMrMode) (v : NullaryPtrVariant) (c : NullaryPtrCase)
    (_ch : Unit) : Option (Corpus.Verdict NullaryPtrObsVal) :=
  mrAuthority.verdict (npMrToMode m, v, c)

/-- The frozen verdict table as a MiniRust reference verdict function. -/
def npExpectedMrVerdict (m : NullaryPtrMrMode) (v : NullaryPtrVariant) (c : NullaryPtrCase)
    (_ch : Unit) : Option (Corpus.Verdict NullaryPtrObsVal) :=
  npExpectedVerdict (npMrToMode m) v c

theorem mrVerdictFn_funext : mrVerdictFn = npExpectedMrVerdict :=
  funext fun m => funext fun v => funext fun c => funext fun _ =>
    mrAuthority_verdict_eq (npMrToMode m) v c

/-- Unified MiniRust corpus side over an arbitrary reference verdict function,
including the `basicMemory` vs. `treeBorrows` flip on
`unwrapUnsafeBinder.modeCase`. -/
def mrSideOf
    (verdictR : NullaryPtrMrMode → NullaryPtrVariant → NullaryPtrCase → Unit →
      Option (Corpus.Verdict NullaryPtrObsVal)) :
    Corpus.Side NullaryPtrMode NullaryPtrMrMode NullaryPtrVariant NullaryPtrCase Unit
      NullaryPtrObsVal NullaryPtrRep where
  toAnneal := npMrToMode
  gate := fun _ _ _ => true
  verdictR := verdictR
  rep := npEncode
  modes := allNpMrModes
  modes_complete := allNpMrModes_complete
  wMode := .basicMemory
  okProg := .unwrapUnsafeBinder
  okQuery := .okPrimary
  okChoice := ()
  faultProg := .unwrapUnsafeBinder
  faultQuery := .ubFault
  faultChoice := ()
  flip := some (.basicMemory, .treeBorrows, .unwrapUnsafeBinder, .modeCase, ())

/-- Unified MiniRust corpus side covering all 4 variants, including genuine
`basicMemory` vs. `treeBorrows` mode sensitivity on `unwrapUnsafeBinder.modeCase`. -/
def mrSide :
    Corpus.Side NullaryPtrMode NullaryPtrMrMode NullaryPtrVariant NullaryPtrCase Unit
      NullaryPtrObsVal NullaryPtrRep :=
  mrSideOf mrVerdictFn

/-- Full simulation + positive + fault + mode-sensitivity certificate for
MiniRust across ALL 32 `(mode, variant, case)` keys: the Trusted and MiniRust
executions are the kernel-checked tables of
`MiniRustSpec.NullaryAndPtrCoercionMR`, and the certificate over those tables
is decided here. -/
theorem mrSide_check : mrSide.check npModel = true := by
  show (mrSideOf mrVerdictFn).check (npModelOf npAnnealEval) = true
  rw [npAnnealEval_funext, mrVerdictFn_funext]
  first | decide | rfl

/-- Per-variant MiniRust side over an arbitrary reference verdict function,
focusing the support gate strictly on variant `v`. -/
def mrVariantSideOf (v : NullaryPtrVariant)
    (verdictR : NullaryPtrMrMode → NullaryPtrVariant → NullaryPtrCase → Unit →
      Option (Corpus.Verdict NullaryPtrObsVal)) :
    Corpus.Side NullaryPtrMode NullaryPtrMrMode NullaryPtrVariant NullaryPtrCase Unit
      NullaryPtrObsVal NullaryPtrRep where
  toAnneal := npMrToMode
  gate := fun _ p _ => decide (p = v)
  verdictR := verdictR
  rep := npEncode
  modes := allNpMrModes
  modes_complete := allNpMrModes_complete
  wMode := .basicMemory
  okProg := v
  okQuery := .okPrimary
  okChoice := ()
  faultProg := v
  faultQuery := .ubFault
  faultChoice := ()
  flip := match v with
    | .unwrapUnsafeBinder =>
      some (.basicMemory, .treeBorrows, .unwrapUnsafeBinder, .modeCase, ())
    | _ => none

/-- Per-variant MiniRust side focusing the support gate strictly on variant `v`,
so each of the 4 MIR variants gets its own dedicated `DualCorrespondenceBundle`
with non-vacuous positive and fault witnesses. -/
def mrVariantSide (v : NullaryPtrVariant) :
    Corpus.Side NullaryPtrMode NullaryPtrMrMode NullaryPtrVariant NullaryPtrCase Unit
      NullaryPtrObsVal NullaryPtrRep :=
  mrVariantSideOf v mrVerdictFn

/-- Per-variant MiniRust certificates for all 4 variants. -/
theorem mrVariantSide_check (v : NullaryPtrVariant) :
    (mrVariantSide v).check npModel = true := by
  show (mrVariantSideOf v mrVerdictFn).check (npModelOf npAnnealEval) = true
  rw [npAnnealEval_funext, mrVerdictFn_funext]
  cases v <;> first | decide | rfl

/-! ## §4. Parameterized LeanMiri Side & Dual-Authority `DualCorrespondenceBundle` Builders -/

/-- Unified LeanMiri side parameterized over any
`ObsAuthority NullaryPtrKey NullaryPtrObsVal` (closed in the cross-root kernel
bridge over `LeanMiriSpec.NullaryAndPtrCoercionLM.npLmObserve`). -/
def lmSideOf (lmAuth : Corpus.ObsAuthority NullaryPtrKey NullaryPtrObsVal) :
    Corpus.Side NullaryPtrMode Bool NullaryPtrVariant NullaryPtrCase Unit NullaryPtrObsVal
      NullaryPtrRep where
  toAnneal := npLmTreeBorrowsToMode
  gate := fun _ _ _ => true
  verdictR := fun b v c _ => lmAuth.verdict (npLmTreeBorrowsToMode b, v, c)
  rep := npEncode
  modes := allNpLmModes
  modes_complete := allNpLmModes_complete
  wMode := false
  okProg := .unwrapUnsafeBinder
  okQuery := .okPrimary
  okChoice := ()
  faultProg := .unwrapUnsafeBinder
  faultQuery := .ubFault
  faultChoice := ()
  flip := some (false, true, .unwrapUnsafeBinder, .modeCase, ())

/-- Boolean certificate predicate for closing the unified dual-authority bundle
against an arbitrary LeanMiri `ObsAuthority`. -/
def lmCheckOf (lmAuth : Corpus.ObsAuthority NullaryPtrKey NullaryPtrObsVal) : Bool :=
  (lmSideOf lmAuth).check npModel

/-- Extensional congruence for `lmCheckOf`: two LeanMiri `ObsAuthority` records
that produce identical verdicts on every key yield identical `lmCheckOf`
certificates (constructive, `[propext, Quot.sound]` only). -/
theorem lmCheckOf_congr (a1 a2 : Corpus.ObsAuthority NullaryPtrKey NullaryPtrObsVal)
    (h : ∀ k, a1.verdict k = a2.verdict k) :
    lmCheckOf a1 = lmCheckOf a2 := by
  have hSide : lmSideOf a1 = lmSideOf a2 := by
    unfold lmSideOf
    congr 1
    funext b v c u
    exact h (npLmTreeBorrowsToMode b, v, c)
  unfold lmCheckOf
  rw [hSide]

/-- Per-variant LeanMiri side focusing the support gate strictly on variant `v`. -/
def lmVariantSideOf (v : NullaryPtrVariant)
    (lmAuth : Corpus.ObsAuthority NullaryPtrKey NullaryPtrObsVal) :
    Corpus.Side NullaryPtrMode Bool NullaryPtrVariant NullaryPtrCase Unit NullaryPtrObsVal
      NullaryPtrRep where
  toAnneal := npLmTreeBorrowsToMode
  gate := fun _ p _ => decide (p = v)
  verdictR := fun b p c _ => lmAuth.verdict (npLmTreeBorrowsToMode b, p, c)
  rep := npEncode
  modes := allNpLmModes
  modes_complete := allNpLmModes_complete
  wMode := false
  okProg := v
  okQuery := .okPrimary
  okChoice := ()
  faultProg := v
  faultQuery := .ubFault
  faultChoice := ()
  flip := match v with
    | .unwrapUnsafeBinder => some (false, true, .unwrapUnsafeBinder, .modeCase, ())
    | _ => none

/-- Per-variant LeanMiri certificate predicate. -/
def lmVariantCheckOf (v : NullaryPtrVariant)
    (lmAuth : Corpus.ObsAuthority NullaryPtrKey NullaryPtrObsVal) : Bool :=
  (lmVariantSideOf v lmAuth).check npModel

/-- Extensional congruence for `lmVariantCheckOf`. -/
theorem lmVariantCheckOf_congr (v : NullaryPtrVariant)
    (a1 a2 : Corpus.ObsAuthority NullaryPtrKey NullaryPtrObsVal)
    (h : ∀ k, a1.verdict k = a2.verdict k) :
    lmVariantCheckOf v a1 = lmVariantCheckOf v a2 := by
  have hSide : lmVariantSideOf v a1 = lmVariantSideOf v a2 := by
    unfold lmVariantSideOf
    congr 1
    funext b p c u
    exact h (npLmTreeBorrowsToMode b, p, c)
  unfold lmVariantCheckOf
  rw [hSide]

/-- Unified `DualCorrespondenceBundle` over the 4 already-trusted MIR variants,
parameterized by a verified LeanMiri `ObsAuthority`. -/
def bundleOf (lmAuth : Corpus.ObsAuthority NullaryPtrKey NullaryPtrObsVal)
    (hLM : lmCheckOf lmAuth = true) :
    DualCorrespondenceBundle NullaryPtrMode NullaryPtrVariant NullaryPtrCase NullaryPtrObsVal
      Unit NullaryPtrRep NullaryPtrMrMode Unit NullaryPtrObsVal Unit Bool Unit NullaryPtrObsVal
      Unit :=
  Corpus.bundle npModel mrSide (lmSideOf lmAuth) mrSide_check hLM

/-- Per-variant `DualCorrespondenceBundle` for each of the 4 MIR variants. -/
def variantBundleOf (v : NullaryPtrVariant)
    (lmAuth : Corpus.ObsAuthority NullaryPtrKey NullaryPtrObsVal)
    (hLM : lmVariantCheckOf v lmAuth = true) :
    DualCorrespondenceBundle NullaryPtrMode NullaryPtrVariant NullaryPtrCase NullaryPtrObsVal
      Unit NullaryPtrRep NullaryPtrMrMode Unit NullaryPtrObsVal Unit Bool Unit NullaryPtrObsVal
      Unit :=
  Corpus.bundle npModel (mrVariantSide v) (lmVariantSideOf v lmAuth)
    (mrVariantSide_check v) hLM

/-! ## §5. Lifted Dual-Authority Theorems & Flip-Direction / Mode-Sensitivity Witnesses -/

/-- Three-way normal agreement across Anneal (`Trusted`), MiniRust
(`Mach`/`MachTB`), and LeanMiri (`Miri.Interpreter`) at every gated key. -/
theorem threeWayNormalAgreement (lmAuth : Corpus.ObsAuthority NullaryPtrKey NullaryPtrObsVal)
    (hLM : lmCheckOf lmAuth = true)
    (mMR : NullaryPtrMrMode) (mLM : Bool) (p : NullaryPtrVariant) (q : NullaryPtrCase)
    (hMode : npMrToMode mMR = npLmTreeBorrowsToMode mLM)
    (cMR cLM : Unit) (vMR vLM : NullaryPtrObsVal)
    (hRMR : (bundleOf lmAuth hLM).mrRel.ExecR mMR p q cMR (.normal vMR))
    (hRLM : (bundleOf lmAuth hLM).lmRel.ExecR mLM p q cLM (.normal vLM)) :
    npEncode vMR = npEncode vLM := by
  have hDet : ∀ out out',
      (bundleOf lmAuth hLM).ExecAnneal ((bundleOf lmAuth hLM).toAnnealMR mMR) p q out →
      (bundleOf lmAuth hLM).ExecAnneal ((bundleOf lmAuth hLM).toAnnealMR mMR) p q out' →
      out = out' := by
    rintro out out' ⟨⟨⟩, h1⟩ ⟨⟨⟩, h2⟩
    exact Option.some.inj (h1.symm.trans h2)
  exact ((bundleOf lmAuth hLM).threeWayNormalAgreement_rep hMode rfl rfl hDet hRMR hRLM).1

/-- Cross-authority fault equivalence between MiniRust and LeanMiri at every
gated key. -/
theorem crossAuthorityFaultEquiv (lmAuth : Corpus.ObsAuthority NullaryPtrKey NullaryPtrObsVal)
    (hLM : lmCheckOf lmAuth = true)
    (mMR : NullaryPtrMrMode) (mLM : Bool) (p : NullaryPtrVariant) (q : NullaryPtrCase)
    (hMode : npMrToMode mMR = npLmTreeBorrowsToMode mLM) (k : CorrFaultKind) :
    (∃ c, (bundleOf lmAuth hLM).mrRel.ExecR mMR p q c (.fault k)) ↔
    (∃ c, (bundleOf lmAuth hLM).lmRel.ExecR mLM p q c (.fault k)) :=
  (bundleOf lmAuth hLM).crossAuthorityFaultEquiv hMode rfl rfl k

/-- Exact behavioral equivalence on BOTH MiniRust and LeanMiri (reverse totality). -/
theorem exactBehaviorEq_both (lmAuth : Corpus.ObsAuthority NullaryPtrKey NullaryPtrObsVal)
    (hLM : lmCheckOf lmAuth = true)
    (mMR : NullaryPtrMrMode) (mLM : Bool) (p : NullaryPtrVariant) (q : NullaryPtrCase) :
    ExactBehaviorEq (bundleOf lmAuth hLM).mrRel mMR p q ∧
    ExactBehaviorEq (bundleOf lmAuth hLM).lmRel mLM p q :=
  ⟨(bundleOf lmAuth hLM).mrSim.exactBehaviorEq_of_reverseTotal
      (mrSide.reverseTotal npModel (Bool.and_eq_true _ _ ▸ mrSide_check).1) rfl,
   (bundleOf lmAuth hLM).lmSim.exactBehaviorEq_of_reverseTotal
      ((lmSideOf lmAuth).reverseTotal npModel (Bool.and_eq_true _ _ ▸ hLM).1) rfl⟩

/-- Non-vacuous MiniRust `ModeSensitivityWitness` on `unwrapUnsafeBinder.modeCase`
(`BasicMemory` returns `42`, `TreeBorrowsMemory` faults with protector UB). -/
theorem mr_modeSensitivity_present :
    (mrSide.flipW npModel mrSide_check).isSome = true := by
  unfold Corpus.Side.flipW
  rfl

/-- Non-vacuous LeanMiri `ModeSensitivityWitness` on `unwrapUnsafeBinder.modeCase`
(`treeBorrows = false` returns `42`; `treeBorrows = true` faults with a Tree
Borrows write conflict on the protected borrow of the binder local). -/
theorem lm_modeSensitivity_present
    (lmAuth : Corpus.ObsAuthority NullaryPtrKey NullaryPtrObsVal)
    (hLM : lmCheckOf lmAuth = true) :
    ((lmSideOf lmAuth).flipW npModel hLM).isSome = true := by
  unfold Corpus.Side.flipW
  rfl

/-- Every per-variant bundle carries genuine `correspondenceClaim`,
`faultEquivClaim`, and non-vacuous flip-direction guards (`okAgree`, `faultA`,
`faultR`) on BOTH authorities (ruling out constant-outcome collapse for all 4
variants). -/
theorem variant_bundle_claims (v : NullaryPtrVariant)
    (lmAuth : Corpus.ObsAuthority NullaryPtrKey NullaryPtrObsVal)
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
for EVERY one of the 4 MIR variants (`nullaryOp`, `pointerCoercion`,
`fnPtrToPtr`, `unwrapUnsafeBinder`):
1. `okPrimary` and `okSecondary` return strictly distinct observable values
   (`a ≠ b`) with strictly distinct `npEncode` wire encodings
   (`npEncode a ≠ npEncode b`) on BOTH Trusted Anneal (`npAnnealEval`) and
   MiniRust (`mrAuthority`);
2. `ubFault` produces `.undefinedBehavior` distinct from both normal return
   verdicts on both authorities;
3. on `unwrapUnsafeBinder.modeCase`, `basic` and `protectedTB` produce strictly
   distinct verdicts on BOTH Trusted Anneal and MiniRust.
Proof is strictly constructive (`[propext, Quot.sound]` only, zero
`Classical.choice`). -/
theorem np_variant_outcomes_distinct (v : NullaryPtrVariant) :
    (∃ a b,
      npAnnealEval .basic v .okPrimary () = some (.returns a) ∧
      npAnnealEval .basic v .okSecondary () = some (.returns b) ∧
      mrAuthority.verdict (.basic, v, .okPrimary) = some (.returns a) ∧
      mrAuthority.verdict (.basic, v, .okSecondary) = some (.returns b) ∧
      a ≠ b ∧
      npEncode a ≠ npEncode b) ∧
    npAnnealEval .basic v .okPrimary () ≠ npAnnealEval .basic v .ubFault () ∧
    npAnnealEval .basic v .okSecondary () ≠ npAnnealEval .basic v .ubFault () ∧
    mrAuthority.verdict (.basic, v, .okPrimary) ≠ mrAuthority.verdict (.basic, v, .ubFault) ∧
    mrAuthority.verdict (.basic, v, .okSecondary) ≠ mrAuthority.verdict (.basic, v, .ubFault) ∧
    npAnnealEval .basic .unwrapUnsafeBinder .modeCase () ≠
      npAnnealEval .protectedTB .unwrapUnsafeBinder .modeCase () ∧
    mrAuthority.verdict (.basic, .unwrapUnsafeBinder, .modeCase) ≠
      mrAuthority.verdict (.protectedTB, .unwrapUnsafeBinder, .modeCase) := by
  have hModeA :
      npAnnealEval .basic .unwrapUnsafeBinder .modeCase () ≠
        npAnnealEval .protectedTB .unwrapUnsafeBinder .modeCase () := by
    rw [npAnnealEval_eq, npAnnealEval_eq]
    intro h
    dsimp only [npExpectedVerdict] at h
    cases h
  have hModeM :
      mrAuthority.verdict (.basic, .unwrapUnsafeBinder, .modeCase) ≠
        mrAuthority.verdict (.protectedTB, .unwrapUnsafeBinder, .modeCase) := by
    rw [mrAuthority_verdict_eq, mrAuthority_verdict_eq]
    intro h
    dsimp only [npExpectedVerdict] at h
    cases h
  cases v with
  | nullaryOp =>
    refine ⟨⟨.usizeVal 36, .u8Val 1,
        npAnnealEval_eq _ _ _ _, npAnnealEval_eq _ _ _ _,
        mrAuthority_verdict_eq _ _ _, mrAuthority_verdict_eq _ _ _,
        by decide, by decide⟩,
      ?_, ?_, ?_, ?_, hModeA, hModeM⟩
    · rw [npAnnealEval_eq, npAnnealEval_eq]; intro h; dsimp only [npExpectedVerdict] at h; cases h
    · rw [npAnnealEval_eq, npAnnealEval_eq]; intro h; dsimp only [npExpectedVerdict] at h; cases h
    · rw [mrAuthority_verdict_eq, mrAuthority_verdict_eq]; intro h; dsimp only [npExpectedVerdict] at h; cases h
    · rw [mrAuthority_verdict_eq, mrAuthority_verdict_eq]; intro h; dsimp only [npExpectedVerdict] at h; cases h
  | pointerCoercion =>
    refine ⟨⟨.ptrAlloc 65536, .usizeVal 3,
        npAnnealEval_eq _ _ _ _, npAnnealEval_eq _ _ _ _,
        mrAuthority_verdict_eq _ _ _, mrAuthority_verdict_eq _ _ _,
        by decide, by decide⟩,
      ?_, ?_, ?_, ?_, hModeA, hModeM⟩
    · rw [npAnnealEval_eq, npAnnealEval_eq]; intro h; dsimp only [npExpectedVerdict] at h; cases h
    · rw [npAnnealEval_eq, npAnnealEval_eq]; intro h; dsimp only [npExpectedVerdict] at h; cases h
    · rw [mrAuthority_verdict_eq, mrAuthority_verdict_eq]; intro h; dsimp only [npExpectedVerdict] at h; cases h
    · rw [mrAuthority_verdict_eq, mrAuthority_verdict_eq]; intro h; dsimp only [npExpectedVerdict] at h; cases h
  | fnPtrToPtr =>
    refine ⟨⟨.ptrAlloc 65536, .ptrAlloc 65537,
        npAnnealEval_eq _ _ _ _, npAnnealEval_eq _ _ _ _,
        mrAuthority_verdict_eq _ _ _, mrAuthority_verdict_eq _ _ _,
        by decide, by decide⟩,
      ?_, ?_, ?_, ?_, hModeA, hModeM⟩
    · rw [npAnnealEval_eq, npAnnealEval_eq]; intro h; dsimp only [npExpectedVerdict] at h; cases h
    · rw [npAnnealEval_eq, npAnnealEval_eq]; intro h; dsimp only [npExpectedVerdict] at h; cases h
    · rw [mrAuthority_verdict_eq, mrAuthority_verdict_eq]; intro h; dsimp only [npExpectedVerdict] at h; cases h
    · rw [mrAuthority_verdict_eq, mrAuthority_verdict_eq]; intro h; dsimp only [npExpectedVerdict] at h; cases h
  | unwrapUnsafeBinder =>
    refine ⟨⟨.u32Val 73, .u8Val 7,
        npAnnealEval_eq _ _ _ _, npAnnealEval_eq _ _ _ _,
        mrAuthority_verdict_eq _ _ _, mrAuthority_verdict_eq _ _ _,
        by decide, by decide⟩,
      ?_, ?_, ?_, ?_, hModeA, hModeM⟩
    · rw [npAnnealEval_eq, npAnnealEval_eq]; intro h; dsimp only [npExpectedVerdict] at h; cases h
    · rw [npAnnealEval_eq, npAnnealEval_eq]; intro h; dsimp only [npExpectedVerdict] at h; cases h
    · rw [mrAuthority_verdict_eq, mrAuthority_verdict_eq]; intro h; dsimp only [npExpectedVerdict] at h; cases h
    · rw [mrAuthority_verdict_eq, mrAuthority_verdict_eq]; intro h; dsimp only [npExpectedVerdict] at h; cases h

end Anneal.Mir.NullaryAndPtrCoercionBundle
