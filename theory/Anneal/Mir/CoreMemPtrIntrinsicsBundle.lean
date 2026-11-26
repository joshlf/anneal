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
import MiniRustSpec.CoreMemPtrIntrinsicsMR

/-!
# Episode 2 Dual-Authority Correspondence Bundle (`Anneal.Mir.CoreMemPtrIntrinsicsBundle`)

Constructive (`[propext, Quot.sound]`, zero `Classical.choice` in codecs and
bundle combinators) dual-authority correspondence packaging for the 8 core
memory & pointer intrinsics promoted into
`Trusted.Rustc.{V2026_06_01,V2026_08_01}.MirSemantics` in Episode 1:

1. `core::intrinsics::copy`
2. `core::intrinsics::compare_bytes`
3. `core::intrinsics::raw_eq`
4. `core::intrinsics::typed_swap_nonoverlapping`
5. `core::intrinsics::ptr_offset_from`
6. `core::intrinsics::ptr_offset_from_unsigned`
7. `core::intrinsics::ptr_mask`
8. `core::intrinsics::black_box`

Design:
- **Authority 0 (Anneal Trusted MIR)**: `cmAnnealEval` runs `runTrustedVerdict`,
  which executes `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` (through
  `MiniRustSpec.CoreMemPtrIntrinsicsMR.cmRunTrusted`) on the concrete
  `CapturedMir` fixture of every key (zero shadow evaluators).
- **Authority 1 (MiniRust)**: `mrAuthority` observes
  `MiniRustSpec.CoreMemPtrIntrinsicsMR.cmMrObserveClass`, the class of the raw
  return bytes produced by `MiniRustSpec.Interp.{steps, stepsTB}` on `Mach`
  and `MachTB`.
- **Authority 2 (LeanMiri)**: parameterized over any
  `ObsAuthority CmKey CmObsVal` satisfying `lmCheckOf lmAuth = true` (closed in
  the cross-root kernel bridge in `tests/mir/CoreMemPtrIntrinsicsTests.lean`
  directly over `LeanMiriSpec.CoreMemPtrIntrinsicsLM.cmLmObserve`).
- **Proof architecture**: the interpreter executions are evaluated once, by the
  kernel, in the two 64-key table theorems `cmTrustedObserve_table` and
  `cmMrObserveClass_table` of `MiniRustSpec.CoreMemPtrIntrinsicsMR`. This
  module rewrites with those tables and closes every finite certificate with
  `decide` on small table lookups.
- **Strict Import Isolation**: imports `Anneal.DualCorrespondenceBundle`,
  `Anneal.Mir.DropBinderAndSubtypeBundle` (authority-agnostic `Corpus` layer),
  and `MiniRustSpec.CoreMemPtrIntrinsicsMR`, with NO `LeanMiriSpec.*` / `Miri.*`
  import.
-/

namespace Anneal.Mir.CoreMemPtrIntrinsicsBundle

open Anneal.DualCorrespondenceBundle
open Anneal.Mir.DropBinderAndSubtypeBundle
open Trusted.Rustc.V2026_06_01 Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec.CoreMemPtrIntrinsicsMR

/-! ## §1. Observable Value Domain & Constructive `CodecLaws` -/

/-- Shared observable value domain for the 8 intrinsics: a scalar return value
(`bits`, width in bytes) or a thin pointer return value (`allocId`, offset). -/
inductive CmObsVal : Type where
  | scalar (bits size : Nat)
  | ptr (allocId off : Nat)
  deriving DecidableEq, Repr

/-- Canonical tagged-triple wire representation `(tag, a, b)`. -/
abbrev CmRep : Type := Nat × Nat × Nat

def cmEncode : CmObsVal → CmRep
  | .scalar b s => (0, b, s)
  | .ptr a o => (1, a, o)

def cmDecode : CmRep → Option CmObsVal
  | (0, b, s) => some (.scalar b s)
  | (1, a, o) => some (.ptr a o)
  | _ => none

def cmValidRep : CmRep → Prop
  | (0, _, _) => True
  | (1, _, _) => True
  | _ => False

/-- Constructive `CodecLaws CmObsVal (Nat × Nat × Nat)` (uses only
`[propext, Quot.sound]`, zero `Classical.choice`, with tight `ValidRep`). -/
def cmCodec : CodecLaws CmObsVal CmRep where
  encode := cmEncode
  decode := cmDecode
  ValidRep := cmValidRep
  decode_encode := fun a => by cases a <;> rfl
  encode_valid := fun a => by cases a <;> exact True.intro
  encode_decode_of_valid := fun b a hv hd => by
    rcases b with ⟨t, x, y⟩
    match t with
    | 0 => cases hd; rfl
    | 1 => cases hd; rfl
    | n + 2 => exact False.elim hv

theorem cmCodec_tight : cmCodec.TightValidRep := by
  intro b hv
  rcases b with ⟨t, x, y⟩
  match t with
  | 0 => exact ⟨.scalar x y, rfl⟩
  | 1 => exact ⟨.ptr x y, rfl⟩
  | n + 2 => exact False.elim hv

/-! ## §2. Mode, Key Enumerations, & Executable Trusted Anneal Model (`cmAnnealEval`) -/

/-- Dual-authority execution mode: basic memory / unprotected borrows vs.
Tree Borrows active-protector enforcement. -/
inductive CmMode : Type where
  | basic
  | protectedTB
  deriving DecidableEq, Repr

/-- Unified corpus key across all 2 modes × 8 intrinsics × 4 cases = 64 keys. -/
abbrev CmKey : Type := CmMode × CmVariant × CmCase

def cmModeToMr : CmMode → CmMrMode
  | .basic => .basicMemory
  | .protectedTB => .treeBorrows

def cmMrToMode : CmMrMode → CmMode
  | .basicMemory => .basic
  | .treeBorrows => .protectedTB

def cmModeToLmTreeBorrows : CmMode → Bool
  | .basic => false
  | .protectedTB => true

def cmLmTreeBorrowsToMode : Bool → CmMode
  | false => .basic
  | true => .protectedTB

/-- Whether the Trusted initial state installs the active protector. -/
def cmModeProtected : CmMode → Bool
  | .basic => false
  | .protectedTB => true

def allCmModes : List CmMode := [.basic, .protectedTB]
def allCmMrModes : List CmMrMode := [.basicMemory, .treeBorrows]
def allCmLmModes : List Bool := [false, true]

def allCmVariants : List CmVariant :=
  [.copy, .compareBytes, .rawEq, .typedSwap, .ptrOffsetFrom, .ptrOffsetFromUnsigned, .ptrMask,
   .blackBox]

def allCmCases : List CmCase := [.okPrimary, .okSecondary, .ubFault, .modeCase]

def allCmKeys : List CmKey :=
  allCmModes.flatMap fun m =>
    allCmVariants.flatMap fun v =>
      allCmCases.map fun c => (m, v, c)

theorem allCmModes_complete (m : CmMode) : m ∈ allCmModes := by
  cases m <;> simp [allCmModes]

theorem allCmMrModes_complete (m : CmMrMode) : m ∈ allCmMrModes := by
  cases m <;> simp [allCmMrModes]

theorem allCmLmModes_complete (b : Bool) : b ∈ allCmLmModes := by
  cases b <;> simp [allCmLmModes]

theorem allCmVariants_complete (v : CmVariant) : v ∈ allCmVariants := by
  cases v <;> simp [allCmVariants]

theorem allCmCases_complete (c : CmCase) : c ∈ allCmCases := by
  cases c <;> simp [allCmCases]

/-- The verdict denoted by a normalized Trusted observation; an execution that
runs out of fuel or returns outside the observable domain has no verdict. -/
def trustedObsVerdict : CmTrustedObs → Option (Corpus.Verdict CmObsVal)
  | .scalar b s => some (.returns (.scalar b s))
  | .ptr a o => some (.returns (.ptr a o))
  | .ub => some .undefinedBehavior
  | .unsupported => some .unsupported
  | .stuck => none

/-- Execute `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` directly for up to
`fuel` steps and return the observable `Corpus.Verdict CmObsVal`. -/
def runTrustedVerdict (body : CapturedMir) (fuel : Nat) (s : MachineState) :
    Option (Corpus.Verdict CmObsVal) :=
  trustedObsVerdict (cmRunTrusted body fuel s)

/-- Direct Trusted Anneal execution for EVERY `(mode, variant, case)` key. Zero
shadow evaluators: every key invokes `runTrustedVerdict` ->
`Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` on the actual `CapturedMir`
fixture (`cmTrustedFixture`) from its initial state (`cmTrustedInit`). -/
def cmAnnealEval (mode : CmMode) (v : CmVariant) (c : CmCase) (_ch : Unit) :
    Option (Corpus.Verdict CmObsVal) :=
  runTrustedVerdict (cmTrustedFixture v c) cmTrustedFuel (cmTrustedInit (cmModeProtected mode) v c)

/-- The frozen 64-key verdict table shared by all three authorities. -/
def cmExpectedVerdict (mode : CmMode) :
    CmVariant → CmCase → Option (Corpus.Verdict CmObsVal)
  | .copy, .okPrimary => some (.returns (.scalar 42 4))
  | .copy, .okSecondary => some (.returns (.scalar 0x08070403 4))
  | .copy, .ubFault => some .undefinedBehavior
  | .copy, .modeCase =>
    match mode with
    | .basic => some (.returns (.scalar 42 4))
    | .protectedTB => some .undefinedBehavior
  | .compareBytes, .okPrimary => some (.returns (.scalar 0xFFFFFFFF 4))
  | .compareBytes, .okSecondary => some (.returns (.scalar 1 4))
  | .compareBytes, .ubFault => some .undefinedBehavior
  | .compareBytes, .modeCase => some (.returns (.scalar 0 4))
  | .rawEq, .okPrimary => some (.returns (.scalar 1 1))
  | .rawEq, .okSecondary => some (.returns (.scalar 0 1))
  | .rawEq, .ubFault => some .undefinedBehavior
  | .rawEq, .modeCase => some (.returns (.scalar 1 1))
  | .typedSwap, .okPrimary => some (.returns (.scalar 9 4))
  | .typedSwap, .okSecondary => some (.returns (.scalar 6 4))
  | .typedSwap, .ubFault => some .undefinedBehavior
  | .typedSwap, .modeCase =>
    match mode with
    | .basic => some (.returns (.scalar 9 4))
    | .protectedTB => some .undefinedBehavior
  | .ptrOffsetFrom, .okPrimary => some (.returns (.scalar 2 8))
  | .ptrOffsetFrom, .okSecondary => some (.returns (.scalar (2 ^ 64 - 2) 8))
  | .ptrOffsetFrom, .ubFault => some .undefinedBehavior
  | .ptrOffsetFrom, .modeCase => some (.returns (.scalar 0 8))
  | .ptrOffsetFromUnsigned, .okPrimary => some (.returns (.scalar 2 8))
  | .ptrOffsetFromUnsigned, .okSecondary => some (.returns (.scalar 4 8))
  | .ptrOffsetFromUnsigned, .ubFault => some .undefinedBehavior
  | .ptrOffsetFromUnsigned, .modeCase => some .undefinedBehavior
  | .ptrMask, .okPrimary => some (.returns (.ptr 100 8))
  | .ptrMask, .okSecondary => some (.returns (.ptr 100 12))
  | .ptrMask, .ubFault => some .undefinedBehavior
  | .ptrMask, .modeCase => some (.returns (.ptr 100 4))
  | .blackBox, .okPrimary => some (.returns (.scalar 77 4))
  | .blackBox, .okSecondary => some (.returns (.ptr 100 4))
  | .blackBox, .ubFault => some .undefinedBehavior
  | .blackBox, .modeCase => some (.returns (.scalar 1 1))

/-- **Trusted Anneal verdicts are exactly the frozen table**: every key's
`stepMirFn` execution (kernel-checked in `cmTrustedObserve_table`) denotes the
frozen verdict. -/
theorem cmAnnealEval_eq (mode : CmMode) (v : CmVariant) (c : CmCase) (u : Unit) :
    cmAnnealEval mode v c u = cmExpectedVerdict mode v c := by
  show trustedObsVerdict (cmTrustedObserve (cmModeProtected mode) v c) =
    cmExpectedVerdict mode v c
  rw [cmTrustedObserve_table]
  cases mode <;> cases v <;> cases c <;> rfl

/-- The frozen verdict table as an Anneal evaluation function. -/
def cmExpectedEval (mode : CmMode) (v : CmVariant) (c : CmCase) (_ch : Unit) :
    Option (Corpus.Verdict CmObsVal) :=
  cmExpectedVerdict mode v c

theorem cmAnnealEval_funext : cmAnnealEval = cmExpectedEval :=
  funext fun m => funext fun v => funext fun c => funext fun u => cmAnnealEval_eq m v c u

/-- Anneal corpus model over the 8 intrinsics, for an arbitrary evaluation function. -/
def cmModelOf
    (evalA : CmMode → CmVariant → CmCase → Unit → Option (Corpus.Verdict CmObsVal)) :
    Corpus.Model CmMode CmVariant CmCase Unit CmObsVal CmRep where
  evalA := evalA
  codec := cmCodec
  progs := allCmVariants
  queries := allCmCases
  choices := [()]
  progs_complete := allCmVariants_complete
  queries_complete := allCmCases_complete
  choices_complete := fun u => by cases u; simp

/-- Anneal corpus model over the 8 intrinsics, evaluated by `cmAnnealEval`. -/
def cmModel : Corpus.Model CmMode CmVariant CmCase Unit CmObsVal CmRep :=
  cmModelOf cmAnnealEval

/-! ## §3. Concrete MiniRust Authority (`mrAuthority`) Directly Over `MiniRustSpec.Interp` -/

/-- Non-colliding denotation table for the observation classes of
`MiniRustSpec.CoreMemPtrIntrinsicsMR.cmMrObserveClass` (the class `i` is the
index of the raw return-byte observation in the kernel-checked duplicate-free
dictionary `cmMrObsDict`). MiniRust allocation `3` at address `1024` is the
counterpart of the Trusted global allocation `100`. -/
def mrDenote : List (Corpus.Verdict CmObsVal × Nat) :=
  [ (.returns (.scalar 42 4), 0),
    (.returns (.scalar 0x08070403 4), 1),
    (.returns (.scalar 0xFFFFFFFF 4), 2),
    (.returns (.scalar 1 4), 3),
    (.returns (.scalar 0 4), 4),
    (.returns (.scalar 1 1), 5),
    (.returns (.scalar 0 1), 6),
    (.returns (.scalar 9 4), 7),
    (.returns (.scalar 7 4), 8),
    (.returns (.scalar 6 4), 9),
    (.returns (.scalar 2 8), 10),
    (.returns (.scalar (2 ^ 64 - 2) 8), 11),
    (.returns (.scalar 0 8), 12),
    (.returns (.scalar 4 8), 13),
    (.returns (.ptr 100 8), 14),
    (.returns (.ptr 100 12), 15),
    (.returns (.ptr 100 4), 16),
    (.returns (.scalar 77 4), 17),
    (.undefinedBehavior, 18),
    (.unsupported, 19) ]

/-- MiniRust `ObsAuthority` directly invoking
`MiniRustSpec.CoreMemPtrIntrinsicsMR.cmMrObserveClass`. -/
def mrAuthority : Corpus.ObsAuthority CmKey CmObsVal where
  Obs := Nat
  decEq := inferInstance
  observe := fun k => cmMrObserveClass (cmModeToMr k.1) k.2.1 k.2.2
  denote := mrDenote

/-- Checked non-shadowing of `mrAuthority.denote`. -/
theorem mrAuthority_denoteConsistent : mrAuthority.denoteConsistent = true := by
  first | decide | rfl

/-- **MiniRust verdicts are exactly the frozen table**. -/
theorem mrAuthority_verdict_eq (mode : CmMode) (v : CmVariant) (c : CmCase) :
    mrAuthority.verdict (mode, v, c) = cmExpectedVerdict mode v c := by
  show (cmMrObserveClass (cmModeToMr mode) v c).bind mrAuthority.decode =
    cmExpectedVerdict mode v c
  rw [cmMrObserveClass_table]
  cases mode <;> cases v <;> cases c <;> rfl

/-- The MiniRust reference verdict function of the corpus sides. -/
def mrVerdictFn (m : CmMrMode) (v : CmVariant) (c : CmCase) (_ch : Unit) :
    Option (Corpus.Verdict CmObsVal) :=
  mrAuthority.verdict (cmMrToMode m, v, c)

/-- The frozen verdict table as a MiniRust reference verdict function. -/
def cmExpectedMrVerdict (m : CmMrMode) (v : CmVariant) (c : CmCase) (_ch : Unit) :
    Option (Corpus.Verdict CmObsVal) :=
  cmExpectedVerdict (cmMrToMode m) v c

theorem mrVerdictFn_funext : mrVerdictFn = cmExpectedMrVerdict :=
  funext fun m => funext fun v => funext fun c => funext fun _ =>
    mrAuthority_verdict_eq (cmMrToMode m) v c

/-- Unified MiniRust corpus side over an arbitrary reference verdict function,
including the `basicMemory` vs. `treeBorrows` flip on `copy.modeCase`. -/
def mrSideOf
    (verdictR : CmMrMode → CmVariant → CmCase → Unit → Option (Corpus.Verdict CmObsVal)) :
    Corpus.Side CmMode CmMrMode CmVariant CmCase Unit CmObsVal CmRep where
  toAnneal := cmMrToMode
  gate := fun _ _ _ => true
  verdictR := verdictR
  rep := cmEncode
  modes := allCmMrModes
  modes_complete := allCmMrModes_complete
  wMode := .basicMemory
  okProg := .copy
  okQuery := .okPrimary
  okChoice := ()
  faultProg := .copy
  faultQuery := .ubFault
  faultChoice := ()
  flip := some (.basicMemory, .treeBorrows, .copy, .modeCase, ())

/-- Unified MiniRust corpus side covering all 8 intrinsics. -/
def mrSide : Corpus.Side CmMode CmMrMode CmVariant CmCase Unit CmObsVal CmRep :=
  mrSideOf mrVerdictFn

/-- Full simulation + positive + fault + mode-sensitivity certificate for
MiniRust across ALL 64 keys. -/
theorem mrSide_check : mrSide.check cmModel = true := by
  show (mrSideOf mrVerdictFn).check (cmModelOf cmAnnealEval) = true
  rw [cmAnnealEval_funext, mrVerdictFn_funext]
  first | decide | rfl

/-- Per-variant MiniRust side focusing the support gate strictly on variant `v`. -/
def mrVariantSideOf (v : CmVariant)
    (verdictR : CmMrMode → CmVariant → CmCase → Unit → Option (Corpus.Verdict CmObsVal)) :
    Corpus.Side CmMode CmMrMode CmVariant CmCase Unit CmObsVal CmRep where
  toAnneal := cmMrToMode
  gate := fun _ p _ => decide (p = v)
  verdictR := verdictR
  rep := cmEncode
  modes := allCmMrModes
  modes_complete := allCmMrModes_complete
  wMode := .basicMemory
  okProg := v
  okQuery := .okPrimary
  okChoice := ()
  faultProg := v
  faultQuery := .ubFault
  faultChoice := ()
  flip := match v with
    | .copy => some (.basicMemory, .treeBorrows, .copy, .modeCase, ())
    | .typedSwap => some (.basicMemory, .treeBorrows, .typedSwap, .modeCase, ())
    | _ => none

/-- Per-variant MiniRust side for each of the 8 intrinsics. -/
def mrVariantSide (v : CmVariant) :
    Corpus.Side CmMode CmMrMode CmVariant CmCase Unit CmObsVal CmRep :=
  mrVariantSideOf v mrVerdictFn

/-- Per-variant MiniRust certificates for all 8 intrinsics. -/
theorem mrVariantSide_check (v : CmVariant) :
    (mrVariantSide v).check cmModel = true := by
  show (mrVariantSideOf v mrVerdictFn).check (cmModelOf cmAnnealEval) = true
  rw [cmAnnealEval_funext, mrVerdictFn_funext]
  cases v <;> first | decide | rfl

/-! ## §4. Parameterized LeanMiri Side & Dual-Authority `DualCorrespondenceBundle` Builders -/

/-- Unified LeanMiri side parameterized over any `ObsAuthority CmKey CmObsVal`
(closed in the cross-root kernel bridge over
`LeanMiriSpec.CoreMemPtrIntrinsicsLM.cmLmObserve`). -/
def lmSideOf (lmAuth : Corpus.ObsAuthority CmKey CmObsVal) :
    Corpus.Side CmMode Bool CmVariant CmCase Unit CmObsVal CmRep where
  toAnneal := cmLmTreeBorrowsToMode
  gate := fun _ _ _ => true
  verdictR := fun b v c _ => lmAuth.verdict (cmLmTreeBorrowsToMode b, v, c)
  rep := cmEncode
  modes := allCmLmModes
  modes_complete := allCmLmModes_complete
  wMode := false
  okProg := .copy
  okQuery := .okPrimary
  okChoice := ()
  faultProg := .copy
  faultQuery := .ubFault
  faultChoice := ()
  flip := some (false, true, .copy, .modeCase, ())

/-- Boolean certificate predicate for closing the unified dual-authority bundle
against an arbitrary LeanMiri `ObsAuthority`. -/
def lmCheckOf (lmAuth : Corpus.ObsAuthority CmKey CmObsVal) : Bool :=
  (lmSideOf lmAuth).check cmModel

/-- Extensional congruence for `lmCheckOf` (constructive). -/
theorem lmCheckOf_congr (a1 a2 : Corpus.ObsAuthority CmKey CmObsVal)
    (h : ∀ k, a1.verdict k = a2.verdict k) :
    lmCheckOf a1 = lmCheckOf a2 := by
  have hSide : lmSideOf a1 = lmSideOf a2 := by
    unfold lmSideOf
    congr 1
    funext b v c u
    exact h (cmLmTreeBorrowsToMode b, v, c)
  unfold lmCheckOf
  rw [hSide]

/-- Per-variant LeanMiri side focusing the support gate strictly on variant `v`. -/
def lmVariantSideOf (v : CmVariant) (lmAuth : Corpus.ObsAuthority CmKey CmObsVal) :
    Corpus.Side CmMode Bool CmVariant CmCase Unit CmObsVal CmRep where
  toAnneal := cmLmTreeBorrowsToMode
  gate := fun _ p _ => decide (p = v)
  verdictR := fun b p c _ => lmAuth.verdict (cmLmTreeBorrowsToMode b, p, c)
  rep := cmEncode
  modes := allCmLmModes
  modes_complete := allCmLmModes_complete
  wMode := false
  okProg := v
  okQuery := .okPrimary
  okChoice := ()
  faultProg := v
  faultQuery := .ubFault
  faultChoice := ()
  flip := match v with
    | .copy => some (false, true, .copy, .modeCase, ())
    | .typedSwap => some (false, true, .typedSwap, .modeCase, ())
    | _ => none

/-- Per-variant LeanMiri certificate predicate. -/
def lmVariantCheckOf (v : CmVariant) (lmAuth : Corpus.ObsAuthority CmKey CmObsVal) : Bool :=
  (lmVariantSideOf v lmAuth).check cmModel

/-- Extensional congruence for `lmVariantCheckOf`. -/
theorem lmVariantCheckOf_congr (v : CmVariant) (a1 a2 : Corpus.ObsAuthority CmKey CmObsVal)
    (h : ∀ k, a1.verdict k = a2.verdict k) :
    lmVariantCheckOf v a1 = lmVariantCheckOf v a2 := by
  have hSide : lmVariantSideOf v a1 = lmVariantSideOf v a2 := by
    unfold lmVariantSideOf
    congr 1
    funext b p c u
    exact h (cmLmTreeBorrowsToMode b, p, c)
  unfold lmVariantCheckOf
  rw [hSide]

/-- Unified `DualCorrespondenceBundle` over the 8 intrinsics, parameterized by a
verified LeanMiri `ObsAuthority`. -/
def bundleOf (lmAuth : Corpus.ObsAuthority CmKey CmObsVal) (hLM : lmCheckOf lmAuth = true) :
    DualCorrespondenceBundle CmMode CmVariant CmCase CmObsVal Unit CmRep CmMrMode Unit CmObsVal
      Unit Bool Unit CmObsVal Unit :=
  Corpus.bundle cmModel mrSide (lmSideOf lmAuth) mrSide_check hLM

/-- Per-variant `DualCorrespondenceBundle` for each of the 8 intrinsics. -/
def variantBundleOf (v : CmVariant) (lmAuth : Corpus.ObsAuthority CmKey CmObsVal)
    (hLM : lmVariantCheckOf v lmAuth = true) :
    DualCorrespondenceBundle CmMode CmVariant CmCase CmObsVal Unit CmRep CmMrMode Unit CmObsVal
      Unit Bool Unit CmObsVal Unit :=
  Corpus.bundle cmModel (mrVariantSide v) (lmVariantSideOf v lmAuth) (mrVariantSide_check v) hLM

/-! ## §5. Lifted Dual-Authority Theorems & Flip-Direction / Mode-Sensitivity Witnesses -/

/-- Three-way normal agreement across Anneal (`Trusted`), MiniRust
(`Mach`/`MachTB`), and LeanMiri (`Miri.Interpreter`) at every gated key. -/
theorem threeWayNormalAgreement (lmAuth : Corpus.ObsAuthority CmKey CmObsVal)
    (hLM : lmCheckOf lmAuth = true)
    (mMR : CmMrMode) (mLM : Bool) (p : CmVariant) (q : CmCase)
    (hMode : cmMrToMode mMR = cmLmTreeBorrowsToMode mLM)
    (cMR cLM : Unit) (vMR vLM : CmObsVal)
    (hRMR : (bundleOf lmAuth hLM).mrRel.ExecR mMR p q cMR (.normal vMR))
    (hRLM : (bundleOf lmAuth hLM).lmRel.ExecR mLM p q cLM (.normal vLM)) :
    cmEncode vMR = cmEncode vLM := by
  have hDet : ∀ out out',
      (bundleOf lmAuth hLM).ExecAnneal ((bundleOf lmAuth hLM).toAnnealMR mMR) p q out →
      (bundleOf lmAuth hLM).ExecAnneal ((bundleOf lmAuth hLM).toAnnealMR mMR) p q out' →
      out = out' := by
    rintro out out' ⟨⟨⟩, h1⟩ ⟨⟨⟩, h2⟩
    exact Option.some.inj (h1.symm.trans h2)
  exact ((bundleOf lmAuth hLM).threeWayNormalAgreement_rep hMode rfl rfl hDet hRMR hRLM).1

/-- Cross-authority fault equivalence between MiniRust and LeanMiri at every gated key. -/
theorem crossAuthorityFaultEquiv (lmAuth : Corpus.ObsAuthority CmKey CmObsVal)
    (hLM : lmCheckOf lmAuth = true)
    (mMR : CmMrMode) (mLM : Bool) (p : CmVariant) (q : CmCase)
    (hMode : cmMrToMode mMR = cmLmTreeBorrowsToMode mLM) (k : CorrFaultKind) :
    (∃ c, (bundleOf lmAuth hLM).mrRel.ExecR mMR p q c (.fault k)) ↔
    (∃ c, (bundleOf lmAuth hLM).lmRel.ExecR mLM p q c (.fault k)) :=
  (bundleOf lmAuth hLM).crossAuthorityFaultEquiv hMode rfl rfl k

/-- Exact behavioral equivalence on BOTH MiniRust and LeanMiri (reverse totality). -/
theorem exactBehaviorEq_both (lmAuth : Corpus.ObsAuthority CmKey CmObsVal)
    (hLM : lmCheckOf lmAuth = true) (mMR : CmMrMode) (mLM : Bool) (p : CmVariant) (q : CmCase) :
    ExactBehaviorEq (bundleOf lmAuth hLM).mrRel mMR p q ∧
    ExactBehaviorEq (bundleOf lmAuth hLM).lmRel mLM p q :=
  ⟨(bundleOf lmAuth hLM).mrSim.exactBehaviorEq_of_reverseTotal
      (mrSide.reverseTotal cmModel (Bool.and_eq_true _ _ ▸ mrSide_check).1) rfl,
   (bundleOf lmAuth hLM).lmSim.exactBehaviorEq_of_reverseTotal
      ((lmSideOf lmAuth).reverseTotal cmModel (Bool.and_eq_true _ _ ▸ hLM).1) rfl⟩

/-- Non-vacuous MiniRust `ModeSensitivityWitness` on `copy.modeCase`
(`BasicMemory` returns `42`, `TreeBorrowsMemory` faults with protector UB). -/
theorem mr_modeSensitivity_present : (mrSide.flipW cmModel mrSide_check).isSome = true := by
  unfold Corpus.Side.flipW
  rfl

/-- Non-vacuous MiniRust `ModeSensitivityWitness` on `typedSwap.modeCase`
(`BasicMemory` returns `9`, `TreeBorrowsMemory` faults with protector UB). -/
theorem mr_typedSwap_modeSensitivity_present :
    ((mrVariantSide .typedSwap).flipW cmModel (mrVariantSide_check .typedSwap)).isSome = true := by
  unfold Corpus.Side.flipW
  rfl

/-- Non-vacuous LeanMiri `ModeSensitivityWitness` on `copy.modeCase`. -/
theorem lm_modeSensitivity_present (lmAuth : Corpus.ObsAuthority CmKey CmObsVal)
    (hLM : lmCheckOf lmAuth = true) :
    ((lmSideOf lmAuth).flipW cmModel hLM).isSome = true := by
  unfold Corpus.Side.flipW
  rfl

/-- Non-vacuous LeanMiri `ModeSensitivityWitness` on `typedSwap.modeCase`. -/
theorem lm_typedSwap_modeSensitivity_present (lmAuth : Corpus.ObsAuthority CmKey CmObsVal)
    (hLM : lmVariantCheckOf .typedSwap lmAuth = true) :
    ((lmVariantSideOf .typedSwap lmAuth).flipW cmModel hLM).isSome = true := by
  unfold Corpus.Side.flipW
  rfl

/-- Every per-variant bundle carries genuine `correspondenceClaim`,
`faultEquivClaim`, and non-vacuous flip-direction guards (`okAgree`, `faultA`,
`faultR`) on BOTH authorities. -/
theorem variant_bundle_claims (v : CmVariant) (lmAuth : Corpus.ObsAuthority CmKey CmObsVal)
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

/-- The positive return values of `okPrimary` and `okSecondary` per intrinsic. -/
def cmOkValues : CmVariant → CmObsVal × CmObsVal
  | .copy => (.scalar 42 4, .scalar 0x08070403 4)
  | .compareBytes => (.scalar 0xFFFFFFFF 4, .scalar 1 4)
  | .rawEq => (.scalar 1 1, .scalar 0 1)
  | .typedSwap => (.scalar 9 4, .scalar 6 4)
  | .ptrOffsetFrom => (.scalar 2 8, .scalar (2 ^ 64 - 2) 8)
  | .ptrOffsetFromUnsigned => (.scalar 2 8, .scalar 4 8)
  | .ptrMask => (.ptr 100 8, .ptr 100 12)
  | .blackBox => (.scalar 77 4, .ptr 100 4)

/-- **Constructive Per-Intrinsic Outcome Distinctness & Non-Degeneracy**: for
EVERY one of the 8 intrinsics, `okPrimary` and `okSecondary` return strictly
distinct values (with distinct wire encodings) on BOTH Trusted Anneal and
MiniRust, `ubFault` is `.undefinedBehavior` on both, and BOTH `copy.modeCase`
and `typedSwap.modeCase` are mode-sensitive on both. -/
theorem cm_variant_outcomes_distinct (v : CmVariant) :
    (∃ a b,
      cmAnnealEval .basic v .okPrimary () = some (.returns a) ∧
      cmAnnealEval .basic v .okSecondary () = some (.returns b) ∧
      mrAuthority.verdict (.basic, v, .okPrimary) = some (.returns a) ∧
      mrAuthority.verdict (.basic, v, .okSecondary) = some (.returns b) ∧
      a ≠ b ∧
      cmEncode a ≠ cmEncode b) ∧
    cmAnnealEval .basic v .ubFault () = some .undefinedBehavior ∧
    mrAuthority.verdict (.basic, v, .ubFault) = some .undefinedBehavior ∧
    cmAnnealEval .basic .copy .modeCase () ≠ cmAnnealEval .protectedTB .copy .modeCase () ∧
    mrAuthority.verdict (.basic, .copy, .modeCase) ≠
      mrAuthority.verdict (.protectedTB, .copy, .modeCase) ∧
    cmAnnealEval .basic .typedSwap .modeCase () ≠ cmAnnealEval .protectedTB .typedSwap .modeCase () ∧
    mrAuthority.verdict (.basic, .typedSwap, .modeCase) ≠
      mrAuthority.verdict (.protectedTB, .typedSwap, .modeCase) := by
  rw [cmAnnealEval_eq, cmAnnealEval_eq, cmAnnealEval_eq, cmAnnealEval_eq, cmAnnealEval_eq,
    cmAnnealEval_eq, cmAnnealEval_eq,
    mrAuthority_verdict_eq, mrAuthority_verdict_eq, mrAuthority_verdict_eq,
    mrAuthority_verdict_eq, mrAuthority_verdict_eq, mrAuthority_verdict_eq, mrAuthority_verdict_eq]
  refine ⟨⟨(cmOkValues v).1, (cmOkValues v).2, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    cases v <;> first | rfl | decide

/-- **Episode 2 Capstone**: for EVERY LeanMiri observation authority `lmAuth`
that passes the unified 64-key check, the 8 intrinsics satisfy, in one
statement: tight codec and consistent MiniRust denotation; the unified and all
8 per-variant MiniRust side checks; three-way normal agreement, cross-authority
fault equivalence, and exact behavioral equivalence on both authorities;
non-vacuous mode sensitivity on both authorities; per-variant claims and
flip-direction guards; per-intrinsic outcome distinctness. Each conjunct is the
statement of the named theorem of this module. -/
theorem ep2_core_mem_ptr_intrinsics_capstone
    (lmAuth : Corpus.ObsAuthority CmKey CmObsVal) (hLM : lmCheckOf lmAuth = true) :
    cmCodec.TightValidRep ∧
    mrAuthority.denoteConsistent = true ∧
    mrSide.check cmModel = true ∧
    (∀ v, (mrVariantSide v).check cmModel = true) ∧
    (∀ (mMR : CmMrMode) (mLM : Bool) (p : CmVariant) (q : CmCase),
      cmMrToMode mMR = cmLmTreeBorrowsToMode mLM →
      ∀ (cMR cLM : Unit) (vMR vLM : CmObsVal),
        (bundleOf lmAuth hLM).mrRel.ExecR mMR p q cMR (.normal vMR) →
        (bundleOf lmAuth hLM).lmRel.ExecR mLM p q cLM (.normal vLM) →
        cmEncode vMR = cmEncode vLM) ∧
    (∀ (mMR : CmMrMode) (mLM : Bool) (p : CmVariant) (q : CmCase),
      cmMrToMode mMR = cmLmTreeBorrowsToMode mLM →
      ∀ (k : CorrFaultKind),
        ((∃ c, (bundleOf lmAuth hLM).mrRel.ExecR mMR p q c (.fault k)) ↔
         (∃ c, (bundleOf lmAuth hLM).lmRel.ExecR mLM p q c (.fault k)))) ∧
    (∀ (mMR : CmMrMode) (mLM : Bool) (p : CmVariant) (q : CmCase),
      ExactBehaviorEq (bundleOf lmAuth hLM).mrRel mMR p q ∧
      ExactBehaviorEq (bundleOf lmAuth hLM).lmRel mLM p q) ∧
    (mrSide.flipW cmModel mrSide_check).isSome = true ∧
    ((lmSideOf lmAuth).flipW cmModel hLM).isSome = true ∧
    (∀ (v : CmVariant) (hV : lmVariantCheckOf v lmAuth = true),
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
    (∀ v : CmVariant,
      (∃ a b,
        cmAnnealEval .basic v .okPrimary () = some (.returns a) ∧
        cmAnnealEval .basic v .okSecondary () = some (.returns b) ∧
        mrAuthority.verdict (.basic, v, .okPrimary) = some (.returns a) ∧
        mrAuthority.verdict (.basic, v, .okSecondary) = some (.returns b) ∧
        a ≠ b ∧
        cmEncode a ≠ cmEncode b) ∧
      cmAnnealEval .basic v .ubFault () = some .undefinedBehavior ∧
      mrAuthority.verdict (.basic, v, .ubFault) = some .undefinedBehavior ∧
      cmAnnealEval .basic .copy .modeCase () ≠ cmAnnealEval .protectedTB .copy .modeCase () ∧
      mrAuthority.verdict (.basic, .copy, .modeCase) ≠
        mrAuthority.verdict (.protectedTB, .copy, .modeCase) ∧
      cmAnnealEval .basic .typedSwap .modeCase () ≠ cmAnnealEval .protectedTB .typedSwap .modeCase () ∧
      mrAuthority.verdict (.basic, .typedSwap, .modeCase) ≠
        mrAuthority.verdict (.protectedTB, .typedSwap, .modeCase)) :=
  ⟨cmCodec_tight, mrAuthority_denoteConsistent, mrSide_check, mrVariantSide_check,
   threeWayNormalAgreement lmAuth hLM,
   crossAuthorityFaultEquiv lmAuth hLM,
   exactBehaviorEq_both lmAuth hLM,
   mr_modeSensitivity_present,
   lm_modeSensitivity_present lmAuth hLM,
   fun v hV => variant_bundle_claims v lmAuth hV,
   cm_variant_outcomes_distinct⟩

end Anneal.Mir.CoreMemPtrIntrinsicsBundle
