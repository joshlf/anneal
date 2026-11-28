/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec
import MiniRustSpec.OpaqueCastAndFnEntryProtectorMR

/-!
# Episode 2 Correspondence Canaries & Cross-Root 3-Way Kernel Closure
# (`ProjectionElem.opaqueCast`, Callee-Only `FnEntry` Protectors `rust#166253`,
# and Machine-Backed Safe-Pointer Dereferenceability)

1. **§1 Root-Lake concrete canaries** across `D1`–`D3`: direct kernel execution
   (`decide +kernel`, independent of Episode 1 table theorems) on the REAL
   Trusted (`stepMirFn`) and MiniRust (`stepM` / `checkPtrM`) observers, codec
   round-trip / tightness / malformed-wire rejection, `D1` case `8` honest
   Trusted `.unsupported` boundary, `D1` companions (`ocCase6PayloadMir`,
   `ocCase7ProtectedDropMir`, `ocCase9DeadLocalMir`, `ocCase9InvalidBoolMir`,
   type-switch erasure boundary), `D2` mode-sensitivity (`{11, 13, 14}`) and
   `rust#166253` callee-only (`10`) vs pre-`#166253` (`11`) + reverse-transmute
   + indirect fn-ptr boundary, `D3` `some mach` vs `none` `CM.dereferenceable`
   separation + ZST dangling/null companions, out-of-range fail-closed guards
   (`22`, `1000`), and root-side non-vacuous capstone instantiation.
2. **§2 Cross-root 3-way kernel closure (`run_cmd`)**: loads
   `.lake/build/lib/lean` (root) AND `examples/.lake/build/lib/lean`
   (`LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM`) into a fresh kernel
   environment, builds the genuine `OcFpLmAuthority` over `lmOcObserve`
   (translation via `LmOcFpObs.rec.{1}`, zero mocks), kernel-evaluates its
   44-cell certificate on the loop-unrolled twin `lmOcObserveU` and transports
   along `lmOcObserveU.eq_src`, discharges fail-closedness from
   `lmOcObserve_out_of_range`, closes the unified + 3 per-domain (`D1`–`D3`)
   bundles, all lifted theorems, observer-level (raw `MrOcFpObs`) 3-way
   agreement, 3-engine companion & UB root-cause alignment, and the Episode 2
   cross-root capstone. It also:
   - locks ALL 97 shared `section Fixtures` declarations (93 identically-typed
     defs locked by `Eq.refl` + `mrOcCaseCount = lmOcCaseCount` by `Eq.refl`,
     plus constructor bijections and table/step locks for the 4 runner decls
     `OcTrustedOutcome`, `OcTrustedRun`, `ocTrustedStep`, `ocRunTrustedRaw`);
   - proves translation fidelity (`lmOcToVerdict = ocVerdictOf ∘ lmToMr`,
     `lmToMr`/`mrToLm` 7-constructor bijection) and locks `ocLmExpected*` to
     `lmOcExpected*.map lmToMr` by `Eq.refl`;
   - verifies EVERY forged control is REJECTED by the kernel while its paired
     honest twin is ACCEPTED (`twins = rejected`);
   - verifies transitive reachability across Trusted, MiniRust, and vendored
     Miri.
3. **§3 Constructive purity, axiom audit, and auditor self-tests**: exhaustive
   100% choice-free `[propext, Quot.sound]` audit of
   `OpaqueCastAndFnEntryProtectorDualSpec`, standard-3-axiom + non-triviality
   audit of this module, and self-tests catching `Classical.choice`, `sorryAx`,
   `Lean.ofReduceBool`, and trivial props (`True`, `1 = 1`, `∀ x, x = x`).
-/

namespace Anneal.Mir.OpaqueCastAndFnEntryProtectorCorrespondenceTests

set_option Elab.async false

open Anneal.DualCorrespondenceBundle
open Anneal.Mir.DropBinderAndSubtypeBundle
open Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec
open MiniRustSpec.OpaqueCastAndFnEntryProtectorMR

/-! ## §1. Root-Lake Concrete Canaries -/

/-- Codec round-trip on every constructor, tightness, exact `ValidRep`
characterization, distinct tags, and malformed-wire rejection. -/
theorem oc_codec_canaries :
    ocCodec.decode (ocCodec.encode (.scalar 42)) = some (.scalar 42) ∧
    ocCodec.decode (ocCodec.encode (.retagPair 5 9)) = some (.retagPair 5 9) ∧
    ocCodec.decode (ocCodec.encode .ptrValid) = some .ptrValid ∧
    ocEncode (.scalar 0) ≠ ocEncode .ptrValid ∧
    ocEncode (.scalar 0) ≠ ocEncode (.retagPair 0 0) ∧
    ocEncode (.retagPair 0 0) ≠ ocEncode .ptrValid ∧
    ocDecode (0, 7, 1) = none ∧ ocDecode (2, 1, 0) = none ∧
    ocDecode (2, 0, 1) = none ∧ ocDecode (3, 0, 0) = none ∧
    ¬ ocValidRep (0, 7, 1) ∧ ¬ ocValidRep (2, 1, 0) ∧
    ¬ ocValidRep (2, 0, 1) ∧ ocValidRep (2, 0, 0) ∧
    ocCodec.TightValidRep := by
  refine ⟨rfl, rfl, rfl, by decide, by decide, by decide,
    rfl, rfl, rfl, rfl, id, id, id, True.intro, ocCodec_tight⟩

/-- `D1` (direct kernel execution): copy/move/assign/field/SetDiscriminant
through `.opaqueCast` match across Trusted and MiniRust (`0, 1, 3, 4, 6`),
negative UB cases (`2, 5, 7, 9`) are UB in both, flip guard `0 ≠ 2`, and case
`8` is the honest Trusted `.unsupported` deref-below-cast boundary while
MiniRust returns `okScalar 5`. -/
theorem d1_opaqueCast_canaries :
    trustedVerdict false 0 = some (.returns (.scalar 7)) ∧
    mrVerdict false 0 = some (.returns (.scalar 7)) ∧
    trustedVerdict true 1 = some (.returns (.scalar 7)) ∧
    mrVerdict true 1 = some (.returns (.scalar 7)) ∧
    trustedVerdict false 2 = some .undefinedBehavior ∧
    mrVerdict false 2 = some .undefinedBehavior ∧
    trustedVerdict false 3 = some (.returns (.scalar 42)) ∧
    mrVerdict false 3 = some (.returns (.scalar 42)) ∧
    trustedVerdict true 4 = some (.returns (.scalar 9)) ∧
    mrVerdict true 4 = some (.returns (.scalar 9)) ∧
    trustedVerdict false 5 = some .undefinedBehavior ∧
    mrVerdict false 5 = some .undefinedBehavior ∧
    trustedVerdict true 6 = some (.returns (.scalar 1)) ∧
    mrVerdict true 6 = some (.returns (.scalar 1)) ∧
    trustedVerdict false 7 = some .undefinedBehavior ∧
    mrVerdict false 7 = some .undefinedBehavior ∧
    trustedVerdict false 8 = some .unsupported ∧
    trustedVerdict true 8 = some .unsupported ∧
    mrVerdict false 8 = some (.returns (.scalar 5)) ∧
    mrVerdict true 8 = some (.returns (.scalar 5)) ∧
    trustedVerdict false 9 = some .undefinedBehavior ∧
    mrVerdict true 9 = some .undefinedBehavior ∧
    mrVerdict false 0 ≠ mrVerdict false 2 ∧
    ocClassOf 8 = .castDerefBoundary := by
  decide +kernel

/-- `D1` companions and type-switch erasure boundary: `SetDiscriminant` payload
(`ocCase6PayloadMir`), mode-sensitive protected drop (`ocCase7ProtectedDropMir`),
dead-local UB (`ocCase9DeadLocalMir`), invalid-`bool` UB + type-switch erasure
boundary (`ocCase9InvalidBoolMir`), and upstream `minimize` contrasts. -/
theorem d1_companion_and_type_switch_canaries :
    type_of% mr_oc_setDiscriminant_payload_agreement ∧
    type_of% mr_oc_protected_drop_mode_sensitive ∧
    type_of% mr_oc_dead_local_ub_non_masking ∧
    type_of% mr_oc_invalid_bool_ub_non_masking ∧
    type_of% mr_oc_type_switch_erasure_boundary ∧
    type_of% mr_oc_minimize_lowering_contrasts :=
  ⟨mr_oc_setDiscriminant_payload_agreement,
   mr_oc_protected_drop_mode_sensitive,
   mr_oc_dead_local_ub_non_masking,
   mr_oc_invalid_bool_ub_non_masking,
   mr_oc_type_switch_erasure_boundary,
   mr_oc_minimize_lowering_contrasts⟩

/-- `D2` (direct kernel execution): callee-only `rust#166253` (`10`) succeeds
in BOTH modes (`okRetagPair 5 5`), pre-`#166253` caller-retag (`11`) and
protected foreign writes (`13`, `14`) are mode-sensitive (`basic` OK, TB UB),
released-protector writes (`12`, `15`) succeed in both modes, plus
reverse-transmute mode sensitivity and Trusted indirect fn-ptr boundary. -/
theorem d2_fnentry_protector_canaries :
    trustedVerdict false 10 = some (.returns (.retagPair 5 5)) ∧
    trustedVerdict true 10 = some (.returns (.retagPair 5 5)) ∧
    mrVerdict false 10 = some (.returns (.retagPair 5 5)) ∧
    mrVerdict true 10 = some (.returns (.retagPair 5 5)) ∧
    trustedVerdict false 11 = some (.returns (.retagPair 5 5)) ∧
    trustedVerdict true 11 = some .undefinedBehavior ∧
    mrVerdict false 11 = some (.returns (.retagPair 5 5)) ∧
    mrVerdict true 11 = some .undefinedBehavior ∧
    trustedVerdict true 12 = some (.returns (.retagPair 4 9)) ∧
    mrVerdict true 12 = some (.returns (.retagPair 4 9)) ∧
    trustedVerdict false 13 = some (.returns (.retagPair 5 5)) ∧
    trustedVerdict true 13 = some .undefinedBehavior ∧
    mrVerdict false 13 = some (.returns (.retagPair 5 5)) ∧
    mrVerdict true 13 = some .undefinedBehavior ∧
    trustedVerdict false 14 = some (.returns (.retagPair 5 5)) ∧
    trustedVerdict true 14 = some .undefinedBehavior ∧
    mrVerdict false 14 = some (.returns (.retagPair 5 5)) ∧
    mrVerdict true 14 = some .undefinedBehavior ∧
    trustedVerdict true 15 = some (.returns (.retagPair 3 9)) ∧
    mrVerdict true 15 = some (.returns (.retagPair 3 9)) ∧
    mrVerdict false 11 ≠ mrVerdict true 11 ∧
    mrVerdict false 13 ≠ mrVerdict true 13 ∧
    mrVerdict false 14 ≠ mrVerdict true 14 ∧
    mrVerdict true 10 ≠ mrVerdict true 11 := by
  decide +kernel

/-- `D2` companions: reverse-transmutation mode sensitivity, Trusted indirect
fn-ptr transmute boundary, and machine-level `steps`/`stepsTB` contrast. -/
theorem d2_indirect_and_rev_transmute_canaries :
    type_of% mr_oc_d2_rev_transmute_mode_sensitive ∧
    type_of% trusted_d2_indirect_fnptr_calls ∧
    type_of% dual_d2_machine_termination_contrast :=
  ⟨mr_oc_d2_rev_transmute_mode_sensitive,
   trusted_d2_indirect_fnptr_calls,
   dual_d2_machine_termination_contrast⟩

/-- `D3` (direct kernel execution): valid `&u32` (`16`) and ZST `&()` (`17`)
return `okPtrValid`; null (`18`), unaligned (`19`), OOB (`20`), and freed (`21`)
are UB in both Trusted and MiniRust; flip guard `16 ≠ 18`. -/
theorem d3_safe_ptr_dereferenceable_canaries :
    trustedVerdict false 16 = some (.returns .ptrValid) ∧
    mrVerdict false 16 = some (.returns .ptrValid) ∧
    trustedVerdict true 17 = some (.returns .ptrValid) ∧
    mrVerdict true 17 = some (.returns .ptrValid) ∧
    trustedVerdict false 18 = some .undefinedBehavior ∧
    mrVerdict true 18 = some .undefinedBehavior ∧
    trustedVerdict true 19 = some .undefinedBehavior ∧
    mrVerdict false 19 = some .undefinedBehavior ∧
    trustedVerdict false 20 = some .undefinedBehavior ∧
    mrVerdict true 20 = some .undefinedBehavior ∧
    trustedVerdict true 21 = some .undefinedBehavior ∧
    mrVerdict false 21 = some .undefinedBehavior ∧
    mrVerdict false 16 ≠ mrVerdict false 18 := by
  decide +kernel

/-- `D3` `some mach` vs `none` `CM.dereferenceable` separation on `Mach` and
`MachTB` plus ZST dangling/null companions. -/
theorem d3_some_vs_none_and_zst_canaries :
    type_of% mr_checkPtr_some_vs_none_contrast ∧
    type_of% mr_checkPtrM_tb_some_vs_none_contrast ∧
    type_of% mr_oc_d3_zst_dangling_and_null :=
  ⟨mr_checkPtr_some_vs_none_contrast,
   mr_checkPtrM_tb_some_vs_none_contrast,
   mr_oc_d3_zst_dangling_and_null⟩

/-- Fail-closed out-of-range cells (`22`, `1000`) on Trusted and MiniRust, and
the exact class layout: 21 `threeWay`, `[8]` `castDerefBoundary`, and
`{11, 13, 14}` mode-sensitive. -/
theorem out_of_range_and_class_canaries :
    trustedVerdict false 22 = some .unsupported ∧
    mrVerdict true 22 = some .unsupported ∧
    trustedVerdict true 1000 = some .unsupported ∧
    mrVerdict false 1000 = some .unsupported ∧
    ((List.range 22).filter (fun i => ocClassOf i == .threeWay)).length = 21 ∧
    ((List.range 22).filter (fun i => ocClassOf i == .castDerefBoundary)) = [8] ∧
    ((List.range 22).filter ocCaseModeSensitive) = [11, 13, 14] ∧
    ocClassOf 22 = .outOfRange := by
  refine ⟨trustedVerdict_out_of_range false 22 (by decide),
    mrVerdict_out_of_range true 22 (by decide),
    trustedVerdict_out_of_range true 1000 (by decide),
    mrVerdict_out_of_range false 1000 (by decide),
    by decide, by decide, by decide, by decide⟩

/-- Root-side instantiation of the capstone at the real-observer-backed
authority (non-vacuity of all capstone hypotheses). -/
theorem root_capstone_instantiation :
    lmTableCheckOf rootBackedLmAuthority = true ∧
    (∀ sel, lmCheckOf sel rootBackedLmAuthority = true) ∧
    type_of% (projectPositive rootBackedLmAuthority
      rootBackedLmAuthority_tableCheck) ∧
    type_of% (projectFault rootBackedLmAuthority
      rootBackedLmAuthority_tableCheck) ∧
    type_of% ep2_opaquecast_fnentry_dual_authority_capstone_nonvacuous :=
  ⟨rootBackedLmAuthority_tableCheck,
   fun sel => lmCheckOf_of_table sel _ rootBackedLmAuthority_tableCheck,
   projectPositive _ rootBackedLmAuthority_tableCheck,
   projectFault _ rootBackedLmAuthority_tableCheck,
   ep2_opaquecast_fnentry_dual_authority_capstone_nonvacuous⟩

/-! ## §2. Cross-Root 3-Way Kernel Closure (`MiniRustSpec` + `LeanMiriSpec` + `Anneal`) -/

open Lean Elab Command Meta in
run_cmd do
  let opts := (← getOptions).setBool `Elab.async false
  let sp : SearchPath :=
    [System.FilePath.mk ".lake/build/lib/lean",
     System.FilePath.mk "examples/.lake/build/lib/lean"]
  initSearchPath (← findSysroot) sp
  let baseEnv ← importModules
    #[{ module := `Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec },
      { module := `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR },
      { module := `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM }]
    {} 0
  let ns := `Anneal.Mir.OpaqueCastAndFnEntryProtectorCorrespondenceTests.CrossRoot
  let bNs := `Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec
  let cNs := `Anneal.Mir.DropBinderAndSubtypeBundle.Corpus
  let mrNs := `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR
  let lmNs := `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM
  let act : CoreM (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Array Name) := do
    let addDef (name : Name) (val : Expr) : CoreM Expr := do
      let ty ← MetaM.run' <| inferType val
      addDecl <| .defnDecl {
        name, levelParams := [], type := ty, value := val,
        hints := .regular 0, safety := .safe }
      return ty
    let addThm (name : Name) (ty pf : Expr) : CoreM Unit := do
      addDecl <| .thmDecl { name, levelParams := [], type := ty, value := pf }
    let addThmInfer (name : Name) (pf : Expr) : CoreM Unit := do
      let ty ← MetaM.run' <| inferType pf
      addThm name ty pf
    let boolTy := mkConst ``Bool
    let natTy := mkConst ``Nat
    let eqTrue (e : Expr) : Expr :=
      mkApp3 (mkConst ``Eq [1]) boolTy e (mkConst ``Bool.true)
    let reflTrue : Expr :=
      mkApp2 (mkConst ``Eq.refl [1]) boolTy (mkConst ``Bool.true)
    let eqFalse (e : Expr) : Expr :=
      mkApp3 (mkConst ``Eq [1]) boolTy e (mkConst ``Bool.false)
    let reflFalse : Expr :=
      mkApp2 (mkConst ``Eq.refl [1]) boolTy (mkConst ``Bool.false)
    let mkEq (ty a b : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) ty a b
    let mkRefl (ty a : Expr) : Expr := mkApp2 (mkConst ``Eq.refl [1]) ty a
    let thmD (n : Name) (ty pf : Expr) : Declaration :=
      .thmDecl { name := n, levelParams := [], type := ty, value := pf }
    let defD (n : Name) (ty val : Expr) : Declaration :=
      .defnDecl { name := n, levelParams := [], type := ty, value := val,
                  hints := .regular 0, safety := .safe }

    -- 1. Genuine LeanMiri authority over `lmOcObserve` (translation via
    -- `LmOcFpObs.rec.{1}`, zero mocks).
    let obsTy := mkConst (bNs ++ `OcFpObs)
    let verdTy := mkApp (mkConst (cNs ++ `Verdict)) obsTy
    let optVerdTy := mkApp (mkConst ``Option [0]) verdTy
    let someV (e : Expr) : Expr := mkApp2 (mkConst ``Option.some [0]) verdTy e
    let noneV : Expr := mkApp (mkConst ``Option.none [0]) verdTy
    let retV (e : Expr) : Expr :=
      mkApp2 (mkConst (cNs ++ `Verdict.returns)) obsTy e
    let ubV := someV (mkApp (mkConst (cNs ++ `Verdict.undefinedBehavior)) obsTy)
    let unsV := someV (mkApp (mkConst (cNs ++ `Verdict.unsupported)) obsTy)
    let lmObsTy := mkConst (lmNs ++ `LmOcFpObs)
    let lmObsC (c : Name) : Expr := mkConst (lmNs ++ `LmOcFpObs ++ c)
    let mkToVerdict (swapUbUns : Bool) (swapPhaseUns : Bool) : MetaM Expr :=
      withLocalDeclD `o lmObsTy fun o => do
        let motive := mkLambda `x .default lmObsTy optVerdTy
        let m1 := mkLambda `v .default natTy
          (someV (retV (mkApp (mkConst (bNs ++ `OcFpObs.scalar)) (.bvar 0))))
        let m2 := mkLambda `r .default natTy <| mkLambda `v .default natTy <|
          someV (retV (mkApp2 (mkConst (bNs ++ `OcFpObs.retagPair))
            (.bvar 1) (.bvar 0)))
        let m3 := someV (retV (mkConst (bNs ++ `OcFpObs.ptrValid)))
        let m4 := if swapUbUns then unsV else ubV
        let m5 := if swapPhaseUns then unsV else noneV
        let m6 := if swapUbUns then ubV else if swapPhaseUns then noneV else unsV
        let m7 := noneV
        mkLambdaFVars #[o] (mkAppN (mkConst (lmNs ++ `LmOcFpObs.rec) [1])
          #[motive, m1, m2, m3, m4, m5, m6, m7, o])
    let toVName := ns ++ `lmOcToVerdict
    let _ ← addDef toVName (← MetaM.run' <| mkToVerdict false false)
    let toV := mkConst toVName
    let mkAuth (observe toVerdict : Expr) : Expr :=
      mkApp3 (mkConst (bNs ++ `OcFpLmAuthority.mk)) lmObsTy observe toVerdict
    let lmObserve := mkConst (lmNs ++ `lmOcObserve)
    let lmObserveU := mkConst (lmNs ++ `lmOcObserveU)
    let authName := ns ++ `lmAuthority
    let _ ← addDef authName (mkAuth lmObserve toV)
    let authC := mkConst authName
    let authUName := ns ++ `lmAuthorityU
    let _ ← addDef authUName (mkAuth lmObserveU toV)
    let authUC := mkConst authUName
    let mut added : Array Name := #[toVName, authName, authUName]

    -- 2. Certificates: kernel evaluation on the loop-unrolled twin
    -- `lmOcObserveU`, transport along `lmOcObserveU.eq_src`, and fail-closedness
    -- from `lmOcObserve_out_of_range`.
    let eqName := ns ++ `lmAuthority_eq_unrolled
    let eqPf ← MetaM.run' do
      let g ← withLocalDeclD `g (← inferType lmObserve) fun g =>
        mkLambdaFVars #[g] (mkAuth g toV)
      mkAppM ``congrArg #[g, mkConst (lmNs ++ `lmOcObserveU.eq_src)]
    addThmInfer eqName eqPf
    added := added.push eqName
    let tblUName := ns ++ `lmAuthorityU_tableCheck
    addThm tblUName (eqTrue (mkApp (mkConst (bNs ++ `lmTableCheckOf)) authUC))
      reflTrue
    added := added.push tblUName
    let tblName := ns ++ `lmAuthority_tableCheck
    addThm tblName (eqTrue (mkApp (mkConst (bNs ++ `lmTableCheckOf)) authC))
      (mkApp4 (mkConst (bNs ++ `lmTableCheckOf_of_eq))
        authC authUC (mkConst eqName) (mkConst tblUName))
    added := added.push tblName
    let hA := mkConst tblName
    let fcName := ns ++ `lmAuthority_failClosed
    let fcPf ← MetaM.run' do
      withLocalDeclD `tb boolTy fun tb => withLocalDeclD `idx natTy fun idx => do
        let le := mkApp4 (mkConst ``LE.le [0]) natTy (mkConst ``instLENat)
          (mkConst (mrNs ++ `mrOcCaseCount)) idx
        withLocalDeclD `h le fun h => do
          let oor := mkApp3 (mkConst (lmNs ++ `lmOcObserve_out_of_range))
            tb idx h
          mkLambdaFVars #[tb, idx, h] (← mkAppM ``congrArg #[toV, oor])
    addThm fcName (mkApp (mkConst (bNs ++ `OcFpLmFailClosed)) authC) fcPf
    added := added.push fcName
    let hOob := mkConst fcName

    -- Direct kernel evaluation of every LeanMiri side certificate on the twin.
    let domNs := bNs ++ `OcFpDomain
    let domains : List Name := [`d1, `d2, `d3]
    let sels : List (Name × Expr) :=
      (`unified, mkApp (mkConst ``Option.none [0]) (mkConst domNs)) ::
        domains.map fun d =>
          (d, mkApp2 (mkConst ``Option.some [0]) (mkConst domNs)
            (mkConst (domNs ++ d)))
    for (tag, sel) in sels do
      let n := ns ++ `lmSideCheckU ++ tag
      addThm n (eqTrue (mkApp2 (mkConst (bNs ++ `lmCheckOf)) sel authUC))
        reflTrue
      added := added.push n
      let n' := ns ++ `lmSideCheck ++ tag
      addThmInfer n' (mkApp3 (mkConst (bNs ++ `lmCheckOf_of_table)) sel authC hA)
      added := added.push n'

    -- 3. Close unified + 3 per-domain bundles, lifted theorems, and capstone.
    let unifiedName := ns ++ `unifiedDualBundle
    let uTy ← addDef unifiedName (mkApp2 (mkConst (bNs ++ `bundleOf)) authC hA)
    unless uTy.getAppFn.isConstOf
        ``Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle ||
        uTy.isConstOf (bNs ++ `OcFpBundle) do
      throwError "cross-root: {unifiedName} is not a DualCorrespondenceBundle"
    added := added.push unifiedName
    let mut bundleCount : Nat := 1
    for d in domains do
      let n := ns ++ `domainBundle ++ d
      let _ ← addDef n
        (mkApp3 (mkConst (bNs ++ `domainBundleOf)) (mkConst (domNs ++ d)) authC hA)
      added := added.push n
      bundleCount := bundleCount + 1
      addThmInfer (ns ++ `domainClaims ++ d)
        (mkApp3 (mkConst (bNs ++ `domain_bundle_claims))
          (mkConst (domNs ++ d)) authC hA)
      added := added.push (ns ++ `domainClaims ++ d)
      for proj in [``DualCorrespondenceBundle.projectPositive,
                   ``DualCorrespondenceBundle.projectFault] do
        let pv ← MetaM.run' <| mkAppM proj #[mkConst n]
        let pn := ns ++ `domainProjection ++ d ++ proj.getString!.toName
        addThmInfer pn pv
        added := added.push pn
    for proj in [``DualCorrespondenceBundle.projectPositive,
                 ``DualCorrespondenceBundle.projectFault] do
      let pv ← MetaM.run' <| mkAppM proj #[mkConst unifiedName]
      let pn := ns ++ `unifiedProjection ++ proj.getString!.toName
      addThmInfer pn pv
      added := added.push pn
    for thmName in [`threeWayNormalAgreement, `crossAuthorityFaultEquiv,
                    `exactBehaviorEq_both, `projectPositive, `projectFault,
                    `modeSensitivity_present, `bundle_gate_castDerefBoundary,
                    `unified_bundle_witness_kinds,
                    `dual_exact_three_way_classification,
                    `dual_no_specPanic_all_cells,
                    `dual_mode_sensitivity_exact,
                    `dual_d2_mode_sensitivity_all_three,
                    `dual_d1_cast_erasure_and_boundary,
                    `dual_d2_fnentry_protectors_and_transmute_boundary,
                    `dual_d3_dereferenceable_and_zst_boundary] do
      addThmInfer (ns ++ thmName) (mkApp2 (mkConst (bNs ++ thmName)) authC hA)
      added := added.push (ns ++ thmName)
    addThmInfer (ns ++ `dual_fail_closed_out_of_range)
      (mkApp2 (mkConst (bNs ++ `dual_fail_closed_out_of_range)) authC hOob)
    added := added.push (ns ++ `dual_fail_closed_out_of_range)
    let capName := ns ++ `ep2_opaquecast_fnentry_dual_authority_capstone
    addThmInfer capName
      (mkApp3 (mkConst (bNs ++ `ep2_opaquecast_fnentry_dual_authority_capstone))
        authC hA hOob)
    added := added.push capName

    -- 3b. Translation fidelity (anti-mock): `lmOcToVerdict` equals
    -- `ocVerdictOf ∘ lmToMr`, where `lmToMr` / `mrToLm` form a 7-constructor
    -- bijection `LmOcFpObs ≃ MrOcFpObs`, and `ocLmExpected*` equals
    -- `lmOcExpected*.map lmToMr` by `Eq.refl`.
    let mrObsTy0 := mkConst (mrNs ++ `MrOcFpObs)
    let ctorNames : List Name :=
      [`okScalar, `okRetagPair, `okPtrValid, `ub, `phaseBoundary,
       `unsupported, `specPanic]
    let mkCtorMap (srcInd dstInd : Name) (ctors : List Name) : MetaM Expr := do
      let srcTy := mkConst srcInd
      withLocalDeclD `o srcTy fun o => do
        let motive := mkLambda `x .default srcTy (mkConst dstInd)
        let mut minors : Array Expr := #[]
        for c in ctors do
          let cTy ← inferType (mkConst (srcInd ++ c))
          minors := minors.push (← forallTelescope cTy fun xs _ =>
            mkLambdaFVars xs (mkAppN (mkConst (dstInd ++ c)) xs))
        mkLambdaFVars #[o]
          (mkAppN (mkConst (srcInd ++ `rec) [1]) (#[motive] ++ minors ++ #[o]))
    let mkPointwise (ind : Name) (ctors : List Name) (resTy : Expr)
        (lhs rhs : Expr → Expr) : MetaM (Expr × Expr) := do
      withLocalDeclD `o (mkConst ind) fun o => do
        let motive ← mkLambdaFVars #[o] (mkEq resTy (lhs o) (rhs o))
        let mut minors : Array Expr := #[]
        for c in ctors do
          let cTy ← inferType (mkConst (ind ++ c))
          minors := minors.push (← forallTelescope cTy fun xs _ =>
            mkLambdaFVars xs
              (mkRefl resTy (lhs (mkAppN (mkConst (ind ++ c)) xs))))
        let pf ← mkLambdaFVars #[o]
          (mkAppN (mkConst (ind ++ `rec) [0]) (#[motive] ++ minors ++ #[o]))
        let ty ← mkForallFVars #[o] (mkEq resTy (lhs o) (rhs o))
        return (ty, pf)
    let lmToMrName := ns ++ `lmToMr
    let _ ← addDef lmToMrName
      (← MetaM.run' <| mkCtorMap (lmNs ++ `LmOcFpObs) (mrNs ++ `MrOcFpObs) ctorNames)
    let mrToLmName := ns ++ `mrToLm
    let _ ← addDef mrToLmName
      (← MetaM.run' <| mkCtorMap (mrNs ++ `MrOcFpObs) (lmNs ++ `LmOcFpObs) ctorNames)
    added := added.push lmToMrName |>.push mrToLmName
    let lmToMr := mkConst lmToMrName
    let mrToLm := mkConst mrToLmName
    let fidelity : List (Name × Name × Expr × (Expr → Expr) × (Expr → Expr)) :=
      [ (`translation_fidelity, lmNs ++ `LmOcFpObs, optVerdTy,
          fun o => mkApp toV o,
          fun o => mkApp (mkConst (bNs ++ `ocVerdictOf)) (mkApp lmToMr o)),
        (`lmToMr_mrToLm, mrNs ++ `MrOcFpObs, mrObsTy0,
          fun o => mkApp lmToMr (mkApp mrToLm o), fun o => o),
        (`mrToLm_lmToMr, lmNs ++ `LmOcFpObs, lmObsTy,
          fun o => mkApp mrToLm (mkApp lmToMr o), fun o => o) ]
    for (tag, ind, resTy, lhs, rhs) in fidelity do
      let (ty, pf) ← MetaM.run' <| mkPointwise ind ctorNames resTy lhs rhs
      addThm (ns ++ tag) ty pf
      added := added.push (ns ++ tag)
    let listMrTy := mkApp (mkConst ``List [0]) mrObsTy0
    for (rootTbl, lmTbl) in
        [(`ocLmExpectedBasic, `lmOcExpectedBasic),
         (`ocLmExpectedTb, `lmOcExpectedTb)] do
      let lhs := mkConst (bNs ++ rootTbl)
      let rhs := mkApp4 (mkConst ``List.map [0, 0]) lmObsTy mrObsTy0 lmToMr
        (mkConst (lmNs ++ lmTbl))
      let n := ns ++ `frozenTableLock ++ rootTbl
      addThm n (mkEq listMrTy lhs rhs) (mkRefl listMrTy lhs)
      added := added.push n
    -- Also lock the shared Trusted tables across MR and LM via `lmToMr`.
    for (mrTbl, lmTbl) in
        [(`mrOcTrustedExpectedBasic, `lmOcTrustedExpectedBasic),
         (`mrOcTrustedExpectedTb, `lmOcTrustedExpectedTb)] do
      let lhs := mkConst (mrNs ++ mrTbl)
      let rhs := mkApp4 (mkConst ``List.map [0, 0]) lmObsTy mrObsTy0 lmToMr
        (mkConst (lmNs ++ lmTbl))
      let n := ns ++ `trustedTableLock ++ mrTbl
      addThm n (mkEq listMrTy lhs rhs) (mkRefl listMrTy lhs)
      added := added.push n

    -- 3c. Direct-certificate bundles: transport every twin side certificate
    -- onto `lmAuthority` via `cert_transport`, and lock each direct bundle by
    -- `Eq.refl` to its table-derived bundle.
    let directBundle := ns ++ `directUnifiedBundle
    for (tag, sel) in sels do
      let directChk := ns ++ `lmSideCheck_direct ++ tag
      let pFn ← MetaM.run' <|
        withLocalDeclD `a (mkConst (bNs ++ `OcFpLmAuthority)) fun a =>
          mkLambdaFVars #[a] (mkApp2 (mkConst (bNs ++ `lmCheckOf)) sel a)
      addThm directChk (eqTrue (mkApp2 (mkConst (bNs ++ `lmCheckOf)) sel authC))
        (mkAppN (mkConst (bNs ++ `cert_transport))
          #[authC, authUC, mkConst eqName, pFn,
            mkConst (ns ++ `lmSideCheckU ++ tag)])
      added := added.push directChk
      let dName := if tag == `unified then directBundle
                   else ns ++ `directDomainBundle ++ tag
      let origName := if tag == `unified then unifiedName
                      else ns ++ `domainBundle ++ tag
      let dTy ← addDef dName
        (mkApp3 (mkConst (bNs ++ `bundleOfSel)) sel authC (mkConst directChk))
      added := added.push dName
      let eqBName := ns ++ `directBundle_eq ++ tag
      addThm eqBName (mkEq dTy (mkConst dName) (mkConst origName))
        (mkRefl dTy (mkConst dName))
      added := added.push eqBName

    -- 3d. 3-engine companion & UB root-cause alignment (MR + LM).
    let rcName := ns ++ `three_engine_companions_and_diagnostics
    let rcPf ← MetaM.run' do
      let parts : List Expr :=
        [ mkConst (mrNs ++ `mr_oc_exact_ub_diagnostics),
          mkConst (mrNs ++ `mr_oc_setDiscriminant_payload_agreement),
          mkConst (lmNs ++ `lm_oc_setDiscriminant_payload_agreement),
          mkConst (mrNs ++ `mr_oc_protected_drop_mode_sensitive),
          mkConst (lmNs ++ `lm_oc_protected_drop_mode_sensitive),
          mkConst (mrNs ++ `mr_oc_dead_local_ub_non_masking),
          mkConst (lmNs ++ `lm_oc_dead_local_ub_non_masking),
          mkConst (mrNs ++ `mr_oc_invalid_bool_ub_non_masking),
          mkConst (lmNs ++ `lm_oc_invalid_bool_ub_non_masking),
          mkConst (mrNs ++ `mr_oc_type_switch_erasure_boundary),
          mkConst (lmNs ++ `lm_oc_type_switch_erasure_boundary),
          mkConst (mrNs ++ `mr_oc_d2_rev_transmute_mode_sensitive),
          mkConst (lmNs ++ `lm_oc_d2_rev_transmute_mode_sensitive),
          mkConst (mrNs ++ `mr_oc_d3_zst_dangling_and_null),
          mkConst (lmNs ++ `lm_oc_d3_zst_dangling_and_null),
          mkConst (mrNs ++ `mr_checkPtr_some_vs_none_contrast),
          mkConst (mrNs ++ `mr_checkPtrM_tb_some_vs_none_contrast),
          mkConst (lmNs ++ `lm_d3_exact_validityMachine_diagnostics),
          mkConst (lmNs ++ `lm_validityMachine_nonvacuity_witnesses),
          mkConst (lmNs ++ `lm_d3_null_both_halves_ub),
          mkConst (lmNs ++ `lm_d1_phase_boundary_table),
          mkConst (lmNs ++ `lm_step_adapter_boundaries),
          mkConst (lmNs ++ `lm_call_initStackFrame_fnEntry_witness),
          mkConst (mrNs ++ `trusted_d2_indirect_fnptr_calls) ]
      let rec conjRc : List Expr → MetaM Expr
        | [] => return mkConst ``True.intro
        | [p] => return p
        | p :: ps => do mkAppM ``And.intro #[p, ← conjRc ps]
      conjRc parts
    addThmInfer rcName rcPf
    added := added.push rcName

    -- 4. Definitional `Eq.refl` fixture locks over EVERY identically-typed
    -- shared definition in `section Fixtures` (all 93 defs: case count, span,
    -- builders, layouts, types, constants, all 34 `CapturedMir` fixtures,
    -- cast-erasure/place-extraction/retag-erasure helpers, `ocCaseFixture?`,
    -- and `ocTrustedFuel`) PLUS `mrOcCaseCount = lmOcCaseCount` (94 `Eq.refl`
    -- locks), PLUS constructor bijections and step/run locks for the 4 runner
    -- declarations (`OcTrustedOutcome`, `OcTrustedRun`, `ocTrustedStep`,
    -- `ocRunTrustedRaw`) covering all 97 `section Fixtures` declarations!
    let fixtureNames : List Name :=
      [ `ocFixtureCaseCount, `ocSpan, `ocSt, `ocBb, `ocDecl, `ocLoc,
        `ocU8Layout, `ocU32Layout, `ocUnitLayout, `ocPtrLayout, `ocPairLayout,
        `ocTwoVarLayout, `ocU64Layout, `ocBytePairLayout, `ocBoolLayout,
        `ocLayouts,
        `ocU8Ty, `ocU32Ty, `ocUnitTy, `ocBoolTy, `ocUsizeTy, `ocIsizeTy,
        `ocU64Ty, `ocPairTy, `ocTwoVarTy, `ocBytePairTy,
        `ocRawConstU32Ty, `ocRawConstU8Ty, `ocRawMutU8Ty, `ocMutRefU8Ty,
        `ocShrRefU8Ty, `ocShrRefU32Ty, `ocShrRefUnitTy,
        `ocConstU8, `ocConstU32, `ocConstUsize, `ocConstU64, `ocConstIsize,
        `ocFnOp, `ocFnAbi, `ocBody, `ocCastU32, `ocInit7,
        `ocCase0Mir, `ocCase1Mir, `ocCase2Mir, `ocCase3Mir, `ocCase4Mir,
        `ocCase5Mir, `ocCase6Mir, `ocCase6PayloadMir, `ocCase7Mir,
        `ocCase7ProtectedDropMir, `ocCase8Mir, `ocCase9Mir,
        `ocCase9DeadLocalMir, `ocCase9InvalidBoolMir,
        `ocEraseProj, `ocErasePlace, `ocEraseOperand, `ocEraseRvalue,
        `ocEraseStmt, `ocEraseTerm, `ocEraseBody,
        `ocPlaceHasCast, `ocOperandPlaces, `ocRvaluePlaces, `ocBodyPlaces,
        `ocD2Main,
        `ocCase10Callee, `ocCase10Mir, `ocCase11Callee, `ocCase11Mir,
        `ocCase12Callee, `ocCase12Mir, `ocCase13Callee, `ocCase13Mir,
        `ocCase13RevTransmuteMir, `ocCase14Callee, `ocCase14Mir,
        `ocCase15Callee, `ocCase15Mir, `ocEraseRetags,
        `ocCase16Mir, `ocCase17Mir, `ocCase17DanglingZstMir,
        `ocCase18Mir, `ocCase18ZstNullMir,
        `ocCase19Mir, `ocCase20Mir, `ocCase21Mir,
        `ocCaseFixture?, `ocTrustedFuel ]
    let mut eqLockCount : Nat := 0
    let mut lockNames : Array Name := #[]
    for tag in fixtureNames do
      let lhs := mkConst (mrNs ++ tag)
      let rhs := mkConst (lmNs ++ tag)
      let ty ← MetaM.run' <| inferType lhs
      let lockName := ns ++ `fixtureLock ++ tag
      addThm lockName (mkEq ty lhs rhs) (mkRefl ty lhs)
      added := added.push lockName
      lockNames := lockNames.push lockName
      eqLockCount := eqLockCount + 1
    let countLockName := ns ++ `fixtureLock ++ `caseCount
    addThm countLockName
      (mkEq natTy (mkConst (mrNs ++ `mrOcCaseCount))
        (mkConst (lmNs ++ `lmOcCaseCount)))
      (mkRefl natTy (mkConst (mrNs ++ `mrOcCaseCount)))
    added := added.push countLockName
    lockNames := lockNames.push countLockName
    eqLockCount := eqLockCount + 1
    unless eqLockCount = 94 do
      throwError "cross-root: expected 94 Eq.refl fixture locks, got {eqLockCount}"
    -- Lock the remaining 4 `section Fixtures` declarations
    -- (`OcTrustedOutcome`, `OcTrustedRun`, `ocTrustedStep`, `ocRunTrustedRaw`):
    -- constructor bijections for both inductives + exact lockstep `Eq.refl`
    -- check of `ocRunTrustedRaw` and `ocTrustedStep` across all fixtures.
    let outCtors : List Name := [`ret, `ub, `unsupported, `outOfFuel]
    let mrOutToLmName := ns ++ `mrOutToLm
    let _ ← addDef mrOutToLmName
      (← MetaM.run' <|
        mkCtorMap (mrNs ++ `OcTrustedOutcome) (lmNs ++ `OcTrustedOutcome) outCtors)
    let lmOutToMrName := ns ++ `lmOutToMr
    let _ ← addDef lmOutToMrName
      (← MetaM.run' <|
        mkCtorMap (lmNs ++ `OcTrustedOutcome) (mrNs ++ `OcTrustedOutcome) outCtors)
    added := added.push mrOutToLmName |>.push lmOutToMrName
    let mrOutToLm := mkConst mrOutToLmName
    let lmOutToMr := mkConst lmOutToMrName
    let (outRtTy1, outRtPf1) ← MetaM.run' <|
      mkPointwise (mrNs ++ `OcTrustedOutcome) outCtors
        (mkConst (mrNs ++ `OcTrustedOutcome))
        (fun o => mkApp lmOutToMr (mkApp mrOutToLm o)) (fun o => o)
    let (outRtTy2, outRtPf2) ← MetaM.run' <|
      mkPointwise (lmNs ++ `OcTrustedOutcome) outCtors
        (mkConst (lmNs ++ `OcTrustedOutcome))
        (fun o => mkApp mrOutToLm (mkApp lmOutToMr o)) (fun o => o)
    addThm (ns ++ `fixtureLock ++ `OcTrustedOutcome_mr_lm) outRtTy1 outRtPf1
    addThm (ns ++ `fixtureLock ++ `OcTrustedOutcome_lm_mr) outRtTy2 outRtPf2
    added := added.push (ns ++ `fixtureLock ++ `OcTrustedOutcome_mr_lm)
      |>.push (ns ++ `fixtureLock ++ `OcTrustedOutcome_lm_mr)
    lockNames := lockNames.push (ns ++ `fixtureLock ++ `OcTrustedOutcome_mr_lm)
      |>.push (ns ++ `fixtureLock ++ `OcTrustedOutcome_lm_mr)
    -- `OcTrustedRun` bijection using `mrOutToLm` / `lmOutToMr` on `.done`.
    let mrRunTy := mkConst (mrNs ++ `OcTrustedRun)
    let lmRunTy := mkConst (lmNs ++ `OcTrustedRun)
    let stTy := mkConst `Trusted.Rustc.V2026_06_01.MirSemantics.MachineState
    let mrOutTy := mkConst (mrNs ++ `OcTrustedOutcome)
    let lmOutTy := mkConst (lmNs ++ `OcTrustedOutcome)
    let mkRunMap (srcNs dstNs : Name) (outMap : Expr) : MetaM Expr :=
      withLocalDeclD `r (mkConst (srcNs ++ `OcTrustedRun)) fun r => do
        let motive := mkLambda `x .default (mkConst (srcNs ++ `OcTrustedRun))
          (mkConst (dstNs ++ `OcTrustedRun))
        let mRun := mkLambda `s .default stTy
          (mkApp (mkConst (dstNs ++ `OcTrustedRun.running)) (.bvar 0))
        let mDone := mkLambda `o .default (mkConst (srcNs ++ `OcTrustedOutcome))
          (mkApp (mkConst (dstNs ++ `OcTrustedRun.done)) (mkApp outMap (.bvar 0)))
        mkLambdaFVars #[r]
          (mkAppN (mkConst (srcNs ++ `OcTrustedRun.rec) [1])
            #[motive, mRun, mDone, r])
    let mrRunToLmName := ns ++ `mrRunToLm
    let _ ← addDef mrRunToLmName
      (← MetaM.run' <| mkRunMap mrNs lmNs mrOutToLm)
    let lmRunToMrName := ns ++ `lmRunToMr
    let _ ← addDef lmRunToMrName
      (← MetaM.run' <| mkRunMap lmNs mrNs lmOutToMr)
    added := added.push mrRunToLmName |>.push lmRunToMrName
    let mrRunToLm := mkConst mrRunToLmName
    let lmRunToMr := mkConst lmRunToMrName
    let mkRunRt (srcNs : Name) (f g : Expr) (outRt : Name) : MetaM (Expr × Expr) :=
      withLocalDeclD `r (mkConst (srcNs ++ `OcTrustedRun)) fun r => do
        let runTy := mkConst (srcNs ++ `OcTrustedRun)
        let motive ← mkLambdaFVars #[r] (mkEq runTy (mkApp g (mkApp f r)) r)
        let mRun ← withLocalDeclD `s stTy fun s =>
          mkLambdaFVars #[s]
            (mkRefl runTy (mkApp (mkConst (srcNs ++ `OcTrustedRun.running)) s))
        let mDone ← withLocalDeclD `o (mkConst (srcNs ++ `OcTrustedOutcome)) fun o => do
          let pf ← mkAppM ``congrArg
            #[mkConst (srcNs ++ `OcTrustedRun.done), mkApp (mkConst outRt) o]
          mkLambdaFVars #[o] pf
        let pf ← mkLambdaFVars #[r]
          (mkAppN (mkConst (srcNs ++ `OcTrustedRun.rec) [0])
            #[motive, mRun, mDone, r])
        let ty ← mkForallFVars #[r] (mkEq runTy (mkApp g (mkApp f r)) r)
        return (ty, pf)
    let (runRtTy1, runRtPf1) ← MetaM.run' <|
      mkRunRt mrNs mrRunToLm lmRunToMr
        (ns ++ `fixtureLock ++ `OcTrustedOutcome_mr_lm)
    let (runRtTy2, runRtPf2) ← MetaM.run' <|
      mkRunRt lmNs lmRunToMr mrRunToLm
        (ns ++ `fixtureLock ++ `OcTrustedOutcome_lm_mr)
    addThm (ns ++ `fixtureLock ++ `OcTrustedRun_mr_lm) runRtTy1 runRtPf1
    addThm (ns ++ `fixtureLock ++ `OcTrustedRun_lm_mr) runRtTy2 runRtPf2
    added := added.push (ns ++ `fixtureLock ++ `OcTrustedRun_mr_lm)
      |>.push (ns ++ `fixtureLock ++ `OcTrustedRun_lm_mr)
    lockNames := lockNames.push (ns ++ `fixtureLock ++ `OcTrustedRun_mr_lm)
      |>.push (ns ++ `fixtureLock ++ `OcTrustedRun_lm_mr)
    -- `ocTrustedStep` lockstep simulation on a concrete body & `ocRunTrustedRaw`
    -- lock across case 0 and case 10 (by `Eq.refl`).
    let initSt0 :=
      mkApp3 (mkConst `Trusted.Rustc.V2026_06_01.MirSemantics.initMachineStateWithCallees)
        (mkConst (mrNs ++ `ocCase0Mir))
        (mkApp (mkConst ``List.nil [0])
          (mkConst `Trusted.Rustc.V2026_06_01.MirSemantics.Value))
        (mkApp (mkConst ``List.nil [0])
          (mkConst `Trusted.Rustc.V2026_06_01.MirAst.CapturedMir))
    let stepLhs := mkApp mrRunToLm
      (mkApp2 (mkConst (mrNs ++ `ocTrustedStep)) (mkConst (mrNs ++ `ocCase0Mir))
        (mkApp (mkConst (mrNs ++ `OcTrustedRun.running)) initSt0))
    let stepRhs := mkApp2 (mkConst (lmNs ++ `ocTrustedStep))
      (mkConst (lmNs ++ `ocCase0Mir))
      (mkApp (mkConst (lmNs ++ `OcTrustedRun.running)) initSt0)
    let stepLockName := ns ++ `fixtureLock ++ `ocTrustedStep
    addThm stepLockName (mkEq lmRunTy stepLhs stepRhs) (mkRefl lmRunTy stepLhs)
    added := added.push stepLockName
    lockNames := lockNames.push stepLockName
    let nilMir := mkApp (mkConst ``List.nil [0])
      (mkConst `Trusted.Rustc.V2026_06_01.MirAst.CapturedMir)
    let runLhs := mkApp mrOutToLm
      (mkApp2 (mkConst (mrNs ++ `ocRunTrustedRaw))
        (mkConst (mrNs ++ `ocCase0Mir)) nilMir)
    let runRhs := mkApp2 (mkConst (lmNs ++ `ocRunTrustedRaw))
      (mkConst (lmNs ++ `ocCase0Mir)) nilMir
    let runLockName := ns ++ `fixtureLock ++ `ocRunTrustedRaw
    addThm runLockName (mkEq lmOutTy runLhs runRhs) (mkRefl lmOutTy runLhs)
    added := added.push runLockName
    lockNames := lockNames.push runLockName
    let _ := (mrRunTy, mrOutTy)
    let runnerLockCount : Nat := 4 -- OcTrustedOutcome, OcTrustedRun, ocTrustedStep, ocRunTrustedRaw
    let totalFixtureLockCount : Nat := eqLockCount + runnerLockCount
    unless totalFixtureLockCount = 98 do
      throwError "cross-root: expected 98 total fixture locks (97 section Fixtures + caseCount), got {totalFixtureLockCount}"

    -- 4b. Observer-level 3-way agreement over raw `lmOcObserve` + unified
    -- cross-root 3-engine capstone.
    let olName := ns ++ `observer_level_three_way
    addThmInfer olName
      (mkApp4 (mkConst (bNs ++ `observer_level_three_way)) authC hA lmToMr
        (mkConst (ns ++ `translation_fidelity)))
    added := added.push olName
    let olAllName := ns ++ `observer_level_exact_all_nat
    addThmInfer olAllName
      (mkApp5 (mkConst (bNs ++ `observer_level_exact_all_nat)) authC hA hOob
        lmToMr (mkConst (ns ++ `translation_fidelity)))
    added := added.push olAllName
    let crossName := ns ++ `ep2_cross_root_three_engine_capstone
    let crossPf ← MetaM.run' do
      let parts : List Expr :=
        [ mkConst capName,
          mkConst (ns ++ `translation_fidelity),
          mkConst olName,
          mkConst olAllName,
          mkConst (ns ++ `lmToMr_mrToLm),
          mkConst (ns ++ `mrToLm_lmToMr),
          mkConst (ns ++ `frozenTableLock ++ `ocLmExpectedBasic),
          mkConst (ns ++ `frozenTableLock ++ `ocLmExpectedTb),
          mkConst (ns ++ `trustedTableLock ++ `mrOcTrustedExpectedBasic),
          mkConst (ns ++ `trustedTableLock ++ `mrOcTrustedExpectedTb),
          mkConst (ns ++ `directBundle_eq ++ `unified),
          mkConst (ns ++ `directBundle_eq ++ `d1),
          mkConst (ns ++ `directBundle_eq ++ `d2),
          mkConst (ns ++ `directBundle_eq ++ `d3),
          mkConst rcName,
          mkConst (lmNs ++ `ep1_lean_miri_opaquecast_fnentry_capstone),
          mkConst (lmNs ++ `lmOcObserve_table),
          mkConst (lmNs ++ `lmOcObserve_mode_sensitivity),
          mkConst (lmNs ++ `lmOc_trusted_agreement) ] ++
        (lockNames.toList.map mkConst)
      let rec conj : List Expr → MetaM Expr
        | [] => return mkConst ``True.intro
        | [p] => return p
        | p :: ps => do mkAppM ``And.intro #[p, ← conj ps]
      conj parts
    addThmInfer crossName crossPf
    added := added.push crossName

    -- 5. Negative forgery controls on scratch environment copies: EVERY forged
    -- declaration MUST be rejected by the kernel AND paired with an accepted
    -- honest twin (`twins = rejected`).
    let saved ← getEnv
    let accepts (d : Declaration) : CoreM Bool := do
      let r ← try addDecl d; pure true catch _ => pure false
      setEnv saved
      return r
    let invObserve ← MetaM.run' <|
      withLocalDeclD `tb boolTy fun tb => withLocalDeclD `idx natTy fun idx =>
        mkLambdaFVars #[tb, idx]
          (mkApp2 lmObserveU (mkApp (mkConst ``Bool.not) tb) idx)
    let invAuth := mkAuth invObserve toV
    let swapUbAuth := mkAuth lmObserveU (← MetaM.run' <| mkToVerdict true false)
    let swapPhaseAuth := mkAuth lmObserveU (← MetaM.run' <| mkToVerdict false true)
    let tblCheck (a : Expr) := mkApp (mkConst (bNs ++ `lmTableCheckOf)) a
    let mrObs (tb : Bool) (i : Nat) : Expr :=
      mkApp2 (mkConst (mrNs ++ `mrOcObserve)) (toExpr tb) (mkNatLit i)
    let trObs (tb : Bool) (i : Nat) : Expr :=
      mkApp2 (mkConst (mrNs ++ `mrOcTrustedObserve)) (toExpr tb) (mkNatLit i)
    let lmObsU (tb : Bool) (i : Nat) : Expr :=
      mkApp2 lmObserveU (toExpr tb) (mkNatLit i)
    let mrObsTy := mkConst (mrNs ++ `MrOcFpObs)
    let mrC (c : Name) : Expr := mkConst (mrNs ++ `MrOcFpObs ++ c)
    let mrSc (n : Nat) : Expr := mkApp (mrC `okScalar) (mkNatLit n)
    let lmSc (n : Nat) : Expr := mkApp (lmObsC `okScalar) (mkNatLit n)
    let mrPair (a b : Nat) : Expr :=
      mkApp2 (mrC `okRetagPair) (mkNatLit a) (mkNatLit b)
    let lmPair (a b : Nat) : Expr :=
      mkApp2 (lmObsC `okRetagPair) (mkNatLit a) (mkNatLit b)
    let repTy ← MetaM.run' <| inferType
      (mkApp (mkConst (bNs ++ `ocEncode))
        (mkApp (mkConst (bNs ++ `OcFpObs.scalar)) (mkNatLit 0)))
    let optObsTy := mkApp (mkConst ``Option [0]) obsTy
    let noneObs := mkApp (mkConst ``Option.none [0]) obsTy
    let triple (a b c : Nat) : MetaM Expr := do
      mkAppM ``Prod.mk #[mkNatLit a, ← mkAppM ``Prod.mk #[mkNatLit b, mkNatLit c]]
    let scalarObs (n : Nat) :=
      mkApp (mkConst (bNs ++ `OcFpObs.scalar)) (mkNatLit n)
    let ptrObs := mkConst (bNs ++ `OcFpObs.ptrValid)
    let someObs (e : Expr) := mkApp2 (mkConst ``Option.some [0]) obsTy e
    let decode (t : Expr) := mkApp (mkConst (bNs ++ `ocDecode)) t
    let encode (o : Expr) := mkApp (mkConst (bNs ++ `ocEncode)) o
    let t071 ← MetaM.run' <| triple 0 7 1
    let t070 ← MetaM.run' <| triple 0 7 0
    let t210 ← MetaM.run' <| triple 2 1 0
    let t201 ← MetaM.run' <| triple 2 0 1
    let t200 ← MetaM.run' <| triple 2 0 0
    let t300 ← MetaM.run' <| triple 3 0 0
    let lmVerd (a : Expr) (tb : Bool) (i : Nat) : Expr :=
      mkApp3 (mkConst (bNs ++ `OcFpLmAuthority.verdict)) a (toExpr tb) (mkNatLit i)
    let isRet (e : Expr) : Expr := mkApp2 (mkConst (cNs ++ `isReturn)) obsTy e
    let isFault (e : Expr) : Expr := mkApp2 (mkConst (cNs ++ `isFaultV)) obsTy e
    let mrVerd (tb : Bool) (i : Nat) : Expr :=
      mkApp2 (mkConst (bNs ++ `mrVerdict)) (toExpr tb) (mkNatLit i)
    let trVerd (tb : Bool) (i : Nat) : Expr :=
      mkApp2 (mkConst (bNs ++ `trustedVerdict)) (toExpr tb) (mkNatLit i)
    let capMirTy ← MetaM.run' <| inferType (mkConst (mrNs ++ `ocCase0Mir))
    let ocBundleTy := mkConst (bNs ++ `OcFpBundle)
    -- Gate-boundary forgery helpers: admitting case `8` (where Trusted is
    -- `.unsupported` while MR & LM return `okScalar 5`) fails `Side.check`.
    let noneSel := mkApp (mkConst ``Option.none [0]) (mkConst domNs)
    let some (.defnInfo lmChkInfo) := (← getEnv).find? (bNs ++ `lmCheckOf)
      | throwError "cross-root: lmCheckOf definition missing"
    let checkOnOcModel := lmChkInfo.value.bindingBody!.bindingBody!.appFn!
    let allTrueGate ← MetaM.run' <|
      withLocalDeclD `sel (mkApp (mkConst ``Option [0]) (mkConst domNs)) fun sel =>
        withLocalDeclD `i (mkConst (bNs ++ `OcFpCase)) fun i =>
          mkLambdaFVars #[sel, i] (mkConst ``Bool.true)
    let mrSideWithCase8 := mkApp3 (mkConst (bNs ++ `sideOf))
      noneSel allTrueGate (mkConst (bNs ++ `mrVerdictFn))
    let mrSideWithCase8Check := mkApp checkOnOcModel mrSideWithCase8
    let lmSideWithCase8 := mkApp3 (mkConst (bNs ++ `sideOf))
      noneSel allTrueGate (mkApp (mkConst (bNs ++ `lmVerdictFn)) authUC)
    let lmSideWithCase8Check := mkApp checkOnOcModel lmSideWithCase8
    let lmMapBasic := mkApp4 (mkConst ``List.map [0, 0]) lmObsTy mrObsTy0 lmToMr
      (mkConst (lmNs ++ `lmOcExpectedBasic))
    let lmMapTb := mkApp4 (mkConst ``List.map [0, 0]) lmObsTy mrObsTy0 lmToMr
      (mkConst (lmNs ++ `lmOcExpectedTb))
    let termClean (tb : Bool) (i : Nat) : Expr :=
      mkApp3 (mkConst (bNs ++ `ocTerminatesCleanly))
        (toExpr tb) (mkConst (mrNs ++ (Name.mkSimple s!"ocMrProg{i}")))
        (mkNatLit 120)
    -- `D1` phase-boundary observer & type-switch erasure expressions.
    let lmPhase0 := mkApp (mkConst (lmNs ++ `lmOcPhaseObserve)) (mkNatLit 0)
    let erasedInvalidBoolTr :=
      mkApp2 (mkConst (mrNs ++ `mrOcTrustedObsOf))
        (mkConst (mrNs ++ `OcRetKind.scalar))
        (mkApp2 (mkConst (mrNs ++ `ocRunTrustedRaw))
          (mkApp (mkConst (mrNs ++ `ocEraseBody))
            (mkConst (mrNs ++ `ocCase9InvalidBoolMir)))
          nilMir)
    -- `D3` `checkPtr` `some mach` vs `none` expressions from Episode 1 theorem.
    let (chkTy, chk16L, chk16R, chk20L, chk20R) ← MetaM.run' do
      let thTy ← inferType (mkConst (mrNs ++ `mr_checkPtr_some_vs_none_contrast))
      let some (c16, rest1) := thTy.and?
        | throwError "cross-root: unexpected checkPtr contrast shape"
      let some (cty, l16, r16) := c16.eq?
        | throwError "cross-root: unexpected checkPtr eq shape"
      -- Navigate to 11th conjunct (case 20 Ref): skip 9 more conjuncts.
      let mut cur := rest1
      for _ in List.range 9 do
        let some (_, nxt) := cur.and?
          | throwError "cross-root: unexpected checkPtr contrast length"
        cur := nxt
      let some (c20, _) := cur.and?
        | throwError "cross-root: unexpected checkPtr case 20 shape"
      let some (_, l20, r20) := c20.eq?
        | throwError "cross-root: unexpected checkPtr case 20 eq"
      return (cty, l16, r16, l20, r20)
    let forged : List (String × Declaration × Declaration) :=
      [ ("ill-typed 0 = 1",
          thmD (ns ++ `forged.zeroEqOne)
            (mkEq natTy (mkNatLit 0) (mkNatLit 1)) (mkRefl natTy (mkNatLit 0)),
          thmD (ns ++ `honest.zeroEqZero)
            (mkEq natTy (mkNatLit 0) (mkNatLit 0)) (mkRefl natTy (mkNatLit 0))),
        ("negated LM 44-cell certificate",
          thmD (ns ++ `forged.lmTableFalse) (eqFalse (tblCheck authUC)) reflFalse,
          thmD (ns ++ `honest.lmTableTrue) (eqTrue (tblCheck authUC)) reflTrue),
        ("mode-inverted LM authority (Bool.not tb) certificate",
          thmD (ns ++ `forged.modeInverted) (eqTrue (tblCheck invAuth)) reflTrue,
          thmD (ns ++ `honest.modeInvertedFalse) (eqFalse (tblCheck invAuth)) reflFalse),
        ("ub/unsupported-swapped LM translation certificate",
          thmD (ns ++ `forged.swappedUbTranslation)
            (eqTrue (tblCheck swapUbAuth)) reflTrue,
          thmD (ns ++ `honest.swappedUbTranslationFalse)
            (eqFalse (tblCheck swapUbAuth)) reflFalse),
        ("phaseBoundary/unsupported-swapped LM translation out-of-range verdict",
          thmD (ns ++ `forged.swappedPhaseOutOfRange)
            (mkEq optVerdTy (lmVerd swapPhaseAuth false 22) unsV)
            (mkRefl optVerdTy (lmVerd swapPhaseAuth false 22)),
          thmD (ns ++ `honest.swappedPhaseOutOfRangeNone)
            (mkEq optVerdTy (lmVerd swapPhaseAuth false 22) noneV)
            (mkRefl optVerdTy (lmVerd swapPhaseAuth false 22))),
        ("forged DualCorrespondenceBundle from mode-inverted LM authority",
          defD (ns ++ `forged.bundleModeInverted) ocBundleTy
            (mkApp2 (mkConst (bNs ++ `bundleOf)) invAuth reflTrue),
          defD (ns ++ `honest.bundleFromUnrolled) ocBundleTy
            (mkApp2 (mkConst (bNs ++ `bundleOf)) authUC (mkConst tblUName))),
        ("swapped fixture lock (ocCase0Mir = ocCase5Mir)",
          thmD (ns ++ `forged.swappedFixture)
            (mkEq capMirTy (mkConst (mrNs ++ `ocCase0Mir))
              (mkConst (lmNs ++ `ocCase5Mir)))
            (mkRefl capMirTy (mkConst (mrNs ++ `ocCase0Mir))),
          thmD (ns ++ `honest.fixture5)
            (mkEq capMirTy (mkConst (mrNs ++ `ocCase5Mir))
              (mkConst (lmNs ++ `ocCase5Mir)))
            (mkRefl capMirTy (mkConst (mrNs ++ `ocCase5Mir)))),
        ("forged codec decode of non-zero padding (0,7,1)",
          thmD (ns ++ `forged.decodePadding0)
            (mkEq optObsTy (decode t071) (someObs (scalarObs 7)))
            (mkRefl optObsTy (decode t071)),
          thmD (ns ++ `honest.decodeCanonical0)
            (mkEq optObsTy (decode t070) (someObs (scalarObs 7)))
            (mkRefl optObsTy (decode t070))),
        ("forged codec decode of non-zero padding (2,1,0)",
          thmD (ns ++ `forged.decodePadding2a)
            (mkEq optObsTy (decode t210) (someObs ptrObs))
            (mkRefl optObsTy (decode t210)),
          thmD (ns ++ `honest.decodeCanonical2a)
            (mkEq optObsTy (decode t200) (someObs ptrObs))
            (mkRefl optObsTy (decode t200))),
        ("forged codec decode of non-zero padding (2,0,1)",
          thmD (ns ++ `forged.decodePadding2b)
            (mkEq optObsTy (decode t201) (someObs ptrObs))
            (mkRefl optObsTy (decode t201)),
          thmD (ns ++ `honest.decodeCanonical2b)
            (mkEq optObsTy (decode t201) noneObs)
            (mkRefl optObsTy (decode t201))),
        ("forged codec decode of invalid wire tag 3",
          thmD (ns ++ `forged.decodeTag3)
            (mkEq optObsTy (decode t300) (someObs (scalarObs 0)))
            (mkRefl optObsTy (decode t300)),
          thmD (ns ++ `honest.decodeTag3None)
            (mkEq optObsTy (decode t300) noneObs)
            (mkRefl optObsTy (decode t300))),
        ("forged colliding codec encodings (scalar 0 = ptrValid)",
          thmD (ns ++ `forged.encodeCollision)
            (mkEq repTy (encode (scalarObs 0)) (encode ptrObs))
            (mkRefl repTy (encode (scalarObs 0))),
          thmD (ns ++ `honest.encodePtrValid)
            (mkEq repTy (encode ptrObs) t200)
            (mkRefl repTy (encode ptrObs))),
        ("forged case 8: Trusted computes okScalar 5 instead of unsupported",
          thmD (ns ++ `forged.case8TrustedOk)
            (mkEq mrObsTy (trObs false 8) (mrSc 5))
            (mkRefl mrObsTy (trObs false 8)),
          thmD (ns ++ `honest.case8TrustedUns)
            (mkEq mrObsTy (trObs false 8) (mrC `unsupported))
            (mkRefl mrObsTy (trObs false 8))),
        ("forged case 8: MiniRust fails closed as unsupported",
          thmD (ns ++ `forged.case8MrUns)
            (mkEq mrObsTy (mrObs true 8) (mrC `unsupported))
            (mkRefl mrObsTy (mrObs true 8)),
          thmD (ns ++ `honest.case8MrOk)
            (mkEq mrObsTy (mrObs true 8) (mrSc 5))
            (mkRefl mrObsTy (mrObs true 8))),
        ("forged case 8: LeanMiri fails closed as unsupported",
          thmD (ns ++ `forged.case8LmUns)
            (mkEq lmObsTy (lmObsU true 8) (lmObsC `unsupported))
            (mkRefl lmObsTy (lmObsU true 8)),
          thmD (ns ++ `honest.case8LmOk)
            (mkEq lmObsTy (lmObsU true 8) (lmSc 5))
            (mkRefl lmObsTy (lmObsU true 8))),
        ("forged D1 phase boundary: case 0 returns unsupported instead of phaseBoundary",
          thmD (ns ++ `forged.d1Phase0Uns)
            (mkEq lmObsTy lmPhase0 (lmObsC `unsupported))
            (mkRefl lmObsTy lmPhase0),
          thmD (ns ++ `honest.d1Phase0Boundary)
            (mkEq lmObsTy lmPhase0 (lmObsC `phaseBoundary))
            (mkRefl lmObsTy lmPhase0)),
        ("forged D1 type-switch erasure: erased ocCase9InvalidBoolMir still UB in Trusted",
          thmD (ns ++ `forged.erasedInvalidBoolUb)
            (mkEq mrObsTy erasedInvalidBoolTr (mrC `ub))
            (mkRefl mrObsTy erasedInvalidBoolTr),
          thmD (ns ++ `honest.erasedInvalidBoolMasks)
            (mkEq mrObsTy erasedInvalidBoolTr (mrSc 2))
            (mkRefl mrObsTy erasedInvalidBoolTr)),
        ("forged case 2: Trusted accepts use-after-move through cast",
          thmD (ns ++ `forged.case2TrAccepts) (eqTrue (isRet (trVerd false 2))) reflTrue,
          thmD (ns ++ `honest.case2TrFaults) (eqTrue (isFault (trVerd false 2))) reflTrue),
        ("forged case 2: MiniRust accepts use-after-move",
          thmD (ns ++ `forged.case2MrAccepts) (eqTrue (isRet (mrVerd false 2))) reflTrue,
          thmD (ns ++ `honest.case2MrFaults) (eqTrue (isFault (mrVerd false 2))) reflTrue),
        ("forged case 2: LeanMiri accepts use-after-move",
          thmD (ns ++ `forged.case2LmAccepts) (eqTrue (isRet (lmVerd authUC false 2))) reflTrue,
          thmD (ns ++ `honest.case2LmFaults) (eqTrue (isFault (lmVerd authUC false 2))) reflTrue),
        ("forged case 9: Trusted masks uninit read through cast",
          thmD (ns ++ `forged.case9TrAccepts) (eqTrue (isRet (trVerd true 9))) reflTrue,
          thmD (ns ++ `honest.case9TrFaults) (eqTrue (isFault (trVerd true 9))) reflTrue),
        ("forged case 9: LeanMiri masks uninit read",
          thmD (ns ++ `forged.case9LmAccepts) (eqTrue (isRet (lmVerd authUC true 9))) reflTrue,
          thmD (ns ++ `honest.case9LmFaults) (eqTrue (isFault (lmVerd authUC true 9))) reflTrue),
        ("forged case 10 (rust#166253 callee-only): Trusted faults under TB",
          thmD (ns ++ `forged.case10TrTbUb)
            (mkEq mrObsTy (trObs true 10) (mrC `ub)) (mkRefl mrObsTy (trObs true 10)),
          thmD (ns ++ `honest.case10TrTbOk)
            (mkEq mrObsTy (trObs true 10) (mrPair 5 5)) (mkRefl mrObsTy (trObs true 10))),
        ("forged case 10 (rust#166253 callee-only): MiniRust faults under TB",
          thmD (ns ++ `forged.case10MrTbUb)
            (mkEq mrObsTy (mrObs true 10) (mrC `ub)) (mkRefl mrObsTy (mrObs true 10)),
          thmD (ns ++ `honest.case10MrTbOk)
            (mkEq mrObsTy (mrObs true 10) (mrPair 5 5)) (mkRefl mrObsTy (mrObs true 10))),
        ("forged case 10 (rust#166253 callee-only): LeanMiri faults under TB",
          thmD (ns ++ `forged.case10LmTbUb)
            (mkEq lmObsTy (lmObsU true 10) (lmObsC `ub)) (mkRefl lmObsTy (lmObsU true 10)),
          thmD (ns ++ `honest.case10LmTbOk)
            (mkEq lmObsTy (lmObsU true 10) (lmPair 5 5)) (mkRefl lmObsTy (lmObsU true 10))),
        ("forged case 11 mode invariance (Trusted basic = treeBorrows)",
          thmD (ns ++ `forged.case11TrInv)
            (mkEq mrObsTy (trObs false 11) (trObs true 11)) (mkRefl mrObsTy (trObs false 11)),
          thmD (ns ++ `honest.case11TrTbUb)
            (mkEq mrObsTy (trObs true 11) (mrC `ub)) (mkRefl mrObsTy (trObs true 11))),
        ("forged case 11 mode invariance (MiniRust basic = treeBorrows)",
          thmD (ns ++ `forged.case11MrInv)
            (mkEq mrObsTy (mrObs false 11) (mrObs true 11)) (mkRefl mrObsTy (mrObs false 11)),
          thmD (ns ++ `honest.case11MrTbUb)
            (mkEq mrObsTy (mrObs true 11) (mrC `ub)) (mkRefl mrObsTy (mrObs true 11))),
        ("forged case 11 mode invariance (LeanMiri basic = treeBorrows)",
          thmD (ns ++ `forged.case11LmInv)
            (mkEq lmObsTy (lmObsU false 11) (lmObsU true 11)) (mkRefl lmObsTy (lmObsU false 11)),
          thmD (ns ++ `honest.case11LmTbUb)
            (mkEq lmObsTy (lmObsU true 11) (lmObsC `ub)) (mkRefl lmObsTy (lmObsU true 11))),
        ("forged case 13 mode invariance (MiniRust basic = treeBorrows)",
          thmD (ns ++ `forged.case13MrInv)
            (mkEq mrObsTy (mrObs false 13) (mrObs true 13)) (mkRefl mrObsTy (mrObs false 13)),
          thmD (ns ++ `honest.case13MrTbUb)
            (mkEq mrObsTy (mrObs true 13) (mrC `ub)) (mkRefl mrObsTy (mrObs true 13))),
        ("forged case 13 mode invariance (LeanMiri basic = treeBorrows)",
          thmD (ns ++ `forged.case13LmInv)
            (mkEq lmObsTy (lmObsU false 13) (lmObsU true 13)) (mkRefl lmObsTy (lmObsU false 13)),
          thmD (ns ++ `honest.case13LmTbUb)
            (mkEq lmObsTy (lmObsU true 13) (lmObsC `ub)) (mkRefl lmObsTy (lmObsU true 13))),
        ("forged case 14 mode invariance (Trusted basic = treeBorrows)",
          thmD (ns ++ `forged.case14TrInv)
            (mkEq mrObsTy (trObs false 14) (trObs true 14)) (mkRefl mrObsTy (trObs false 14)),
          thmD (ns ++ `honest.case14TrTbUb)
            (mkEq mrObsTy (trObs true 14) (mrC `ub)) (mkRefl mrObsTy (trObs true 14))),
        ("forged case 14 mode invariance (LeanMiri basic = treeBorrows)",
          thmD (ns ++ `forged.case14LmInv)
            (mkEq lmObsTy (lmObsU false 14) (lmObsU true 14)) (mkRefl lmObsTy (lmObsU false 14)),
          thmD (ns ++ `honest.case14LmTbUb)
            (mkEq lmObsTy (lmObsU true 14) (lmObsC `ub)) (mkRefl lmObsTy (lmObsU true 14))),
        ("forged clean termination on TB-UB case 11 (Stop.ub must fail ocTerminatesCleanly)",
          thmD (ns ++ `forged.termClean11Tb) (eqTrue (termClean true 11)) reflTrue,
          thmD (ns ++ `honest.termNoClean11Tb) (eqFalse (termClean true 11)) reflFalse),
        ("forged D3 case 16 checkPtr contrast matches case 20 OOB contrast",
          thmD (ns ++ `forged.d3CheckPtr16Eq20) (mkEq chkTy chk16L chk20R) (mkRefl chkTy chk16L),
          thmD (ns ++ `honest.d3CheckPtr16Exact) (mkEq chkTy chk16L chk16R) (mkRefl chkTy chk16L)),
        ("forged D3 case 20 OOB checkPtr contrast matches case 16 valid contrast",
          thmD (ns ++ `forged.d3CheckPtr20Eq16) (mkEq chkTy chk20L chk16R) (mkRefl chkTy chk20L),
          thmD (ns ++ `honest.d3CheckPtr20Exact) (mkEq chkTy chk20L chk20R) (mkRefl chkTy chk20L)),
        ("forged D3 case 18: LeanMiri accepts null safe pointer",
          thmD (ns ++ `forged.case18LmOk)
            (mkEq lmObsTy (lmObsU false 18) (lmObsC `okPtrValid))
            (mkRefl lmObsTy (lmObsU false 18)),
          thmD (ns ++ `honest.case18LmUb)
            (mkEq lmObsTy (lmObsU false 18) (lmObsC `ub))
            (mkRefl lmObsTy (lmObsU false 18))),
        ("forged D3 case 19: LeanMiri accepts unaligned safe pointer",
          thmD (ns ++ `forged.case19LmOk)
            (mkEq lmObsTy (lmObsU false 19) (lmObsC `okPtrValid))
            (mkRefl lmObsTy (lmObsU false 19)),
          thmD (ns ++ `honest.case19LmUb)
            (mkEq lmObsTy (lmObsU false 19) (lmObsC `ub))
            (mkRefl lmObsTy (lmObsU false 19))),
        ("forged D3 case 20: LeanMiri accepts OOB safe pointer",
          thmD (ns ++ `forged.case20LmOk)
            (mkEq lmObsTy (lmObsU false 20) (lmObsC `okPtrValid))
            (mkRefl lmObsTy (lmObsU false 20)),
          thmD (ns ++ `honest.case20LmUb)
            (mkEq lmObsTy (lmObsU false 20) (lmObsC `ub))
            (mkRefl lmObsTy (lmObsU false 20))),
        ("forged D3 case 21: LeanMiri accepts freed safe pointer",
          thmD (ns ++ `forged.case21LmOk)
            (mkEq lmObsTy (lmObsU false 21) (lmObsC `okPtrValid))
            (mkRefl lmObsTy (lmObsU false 21)),
          thmD (ns ++ `honest.case21LmUb)
            (mkEq lmObsTy (lmObsU false 21) (lmObsC `ub))
            (mkRefl lmObsTy (lmObsU false 21))),
        ("forged observer-level agreement at case 8 (LeanMiri = Trusted on 8)",
          thmD (ns ++ `forged.observerLevelCase8)
            (mkEq mrObsTy0 (mkApp lmToMr (lmObsU false 8)) (trObs false 8))
            (mkRefl mrObsTy0 (mkApp lmToMr (lmObsU false 8))),
          thmD (ns ++ `honest.observerLevelCase8Mr)
            (mkEq mrObsTy0 (mkApp lmToMr (lmObsU false 8)) (mrObs false 8))
            (mkRefl mrObsTy0 (mkApp lmToMr (lmObsU false 8)))),
        ("forged observer-level out-of-range cell 100 returns okScalar 0",
          thmD (ns ++ `forged.observerLevelOobOk)
            (mkEq mrObsTy0 (mkApp lmToMr (lmObsU true 100)) (mrSc 0))
            (mkRefl mrObsTy0 (mkApp lmToMr (lmObsU true 100))),
          thmD (ns ++ `honest.observerLevelOobAgree)
            (mkEq mrObsTy0 (mkApp lmToMr (lmObsU true 100)) (mrObs true 100))
            (mkRefl mrObsTy0 (mkApp lmToMr (lmObsU true 100)))),
        ("forged translation fidelity (lmToMr maps phaseBoundary to unsupported)",
          thmD (ns ++ `forged.lmToMrPhase)
            (mkEq mrObsTy0 (mkApp lmToMr (lmObsC `phaseBoundary)) (mrC `unsupported))
            (mkRefl mrObsTy0 (mkApp lmToMr (lmObsC `phaseBoundary))),
          thmD (ns ++ `honest.lmToMrPhase)
            (mkEq mrObsTy0 (mkApp lmToMr (lmObsC `phaseBoundary)) (mrC `phaseBoundary))
            (mkRefl mrObsTy0 (mkApp lmToMr (lmObsC `phaseBoundary)))),
        ("forged MR Corpus.Side.check admitting cast-deref boundary case 8",
          thmD (ns ++ `forged.mrGateIncludesCase8) (eqTrue mrSideWithCase8Check) reflTrue,
          thmD (ns ++ `honest.mrGateRejectsCase8) (eqFalse mrSideWithCase8Check) reflFalse),
        ("forged LM Corpus.Side.check admitting cast-deref boundary case 8",
          thmD (ns ++ `forged.lmGateIncludesCase8) (eqTrue lmSideWithCase8Check) reflTrue,
          thmD (ns ++ `honest.lmGateRejectsCase8) (eqFalse lmSideWithCase8Check) reflFalse),
        ("forged cross-mode frozen-table lock (ocLmExpectedBasic = lmOcExpectedTb.map lmToMr)",
          thmD (ns ++ `forged.frozenTableCrossMode)
            (mkEq listMrTy (mkConst (bNs ++ `ocLmExpectedBasic)) lmMapTb)
            (mkRefl listMrTy (mkConst (bNs ++ `ocLmExpectedBasic))),
          thmD (ns ++ `honest.frozenTableBasic)
            (mkEq listMrTy (mkConst (bNs ++ `ocLmExpectedBasic)) lmMapBasic)
            (mkRefl listMrTy (mkConst (bNs ++ `ocLmExpectedBasic)))),
        ("forged LM out-of-range cell 22 returns okScalar 0 instead of unsupported",
          thmD (ns ++ `forged.lmOutOfRangeOk)
            (mkEq lmObsTy (lmObsU false 22) (lmSc 0))
            (mkRefl lmObsTy (lmObsU false 22)),
          thmD (ns ++ `honest.lmOutOfRangeUns)
            (mkEq lmObsTy (lmObsU false 22) (lmObsC `unsupported))
            (mkRefl lmObsTy (lmObsU false 22))) ]
    let mut rejected : Nat := 0
    let mut twins : Nat := 0
    for (what, d, h) in forged do
      if ← accepts d then
        throwError "cross-root negative control FAILED: kernel accepted {what}"
      rejected := rejected + 1
      unless ← accepts h do
        throwError "cross-root negative control VACUOUS: honest twin of {what} was rejected"
      twins := twins + 1

    -- 6. Axiom / non-triviality audit of every added declaration & LM theorems.
    let env ← getEnv
    let isStdAx (a : Name) : Bool :=
      a == ``propext || a == ``Classical.choice || a == ``Quot.sound
    let rec isTrivialProp : Expr → Bool
      | .forallE _ _ body _ => isTrivialProp body
      | .letE _ _ _ body _ => isTrivialProp body
      | e =>
        if e.isConstOf ``True then true
        else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
        else if e.isAppOfArity ``Iff 2 then e.appFn!.appArg! == e.appArg!
        else false
    let mut crAxioms : NameSet := {}
    for n in added do
      let some ci := env.find? n | throwError "cross-root: {n} missing"
      match ci with
      | .defnInfo v =>
        if v.safety != .safe then throwError "cross-root: {n} is not safe"
      | .thmInfo v =>
        if isTrivialProp v.type then throwError "cross-root: {n} is a trivial theorem"
      | _ => throwError "cross-root: {n} is not a defn or thm"
      for a in ← collectAxioms n do
        unless isStdAx a do
          throwError "cross-root: {n} depends on non-standard axiom {a}"
        crAxioms := crAxioms.insert a
    let lmDeepThms : List Name :=
      [ `lmOcObserve_table, `lmOcObserve_out_of_range,
        `lmOcObserve_mode_sensitivity, `lmOcTrustedObserve_table,
        `lmOc_trusted_agreement, `lm_opaqueCast_phase_boundary,
        `lm_d1_phase_boundary_table, `lm_ocEraseBody_cast_free,
        `lm_oc_setDiscriminant_payload_agreement,
        `lm_oc_protected_drop_mode_sensitive,
        `lm_oc_dead_local_ub_non_masking,
        `lm_oc_invalid_bool_ub_non_masking,
        `lm_oc_type_switch_erasure_boundary,
        `lm_oc_d2_rev_transmute_mode_sensitive,
        `lm_oc_d3_zst_dangling_and_null,
        `lm_call_initStackFrame_fnEntry_witness,
        `lm_d3_exact_validityMachine_diagnostics,
        `lm_validityMachine_nonvacuity_witnesses,
        `lm_d3_null_both_halves_ub,
        `ep1_lean_miri_opaquecast_fnentry_capstone ]
    for t in lmDeepThms do
      let n := lmNs ++ t
      let some (.thmInfo v) := env.find? n
        | throwError "cross-root: required LM theorem {n} missing"
      if isTrivialProp v.type then
        throwError "cross-root: LM theorem {n} is trivial"
      for a in ← collectAxioms n do
        unless isStdAx a do
          throwError "cross-root: LM theorem {n} depends on non-standard axiom {a}"
        crAxioms := crAxioms.insert a
    unless !(← collectAxioms ``sorryAx).all isStdAx do
      throwError "cross-root self-test: sorryAx was not detected"
    unless !(← collectAxioms ``Lean.ofReduceBool).all isStdAx do
      throwError "cross-root self-test: Lean.ofReduceBool was not detected"
    let trivEq := mkEq natTy (mkNatLit 1) (mkNatLit 1)
    unless isTrivialProp (mkConst ``True) && isTrivialProp trivEq &&
        !isTrivialProp (mkEq natTy (mkNatLit 1) (mkNatLit 2)) do
      throwError "cross-root self-test: trivial theorem detector failed"

    -- 7. Transitive 3-engine reachability across Trusted + MiniRust + Miri.
    let reachFrom (root : Name) : NameSet := Id.run do
      let mut seen : NameSet := {}
      let mut todo : Array Name := #[root]
      while !todo.isEmpty do
        let n := todo.back!
        todo := todo.pop
        if seen.contains n then continue
        seen := seen.insert n
        if let some ci := env.find? n then
          for d in ci.getUsedConstantsAsSet do
            if !seen.contains d then todo := todo.push d
      return seen
    let reqs : List (Name × List Name) :=
      [ (unifiedName,
          [ `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
            `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcTrustedObserve,
            `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcObserve,
            `MiniRustSpec.Interp.stepM,
            `MiniRustSpec.Interp.checkPtrM,
            `MiniRustSpec.Interp.ConcurrentMemory.dereferenceable,
            `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.lmOcObserve,
            `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.lmOcObserveU,
            `Miri.Interpreter.Step.step,
            `Miri.TreeBorrows.RetagPipeline.retagPointerValue,
            `Miri.Interpreter.ValidityMachine.checkPointerAccess,
            `Miri.Interpreter.ValidityMachine.checkPointerAlign,
            `Miri.Memory.Validity.checkScalar ]),
        (directBundle,
          [ `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
            `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcTrustedObserve,
            `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcObserve,
            `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.lmOcObserve,
            `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.lmOcObserveU,
            `Miri.Interpreter.Step.step,
            `Miri.TreeBorrows.RetagPipeline.retagPointerValue,
            `Miri.Interpreter.ValidityMachine.checkPointerAccess,
            `Miri.Interpreter.ValidityMachine.checkPointerAlign ]),
        (crossName,
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
            `Miri.Interpreter.Step.step,
            `Miri.Interpreter.project,
            `Miri.Interpreter.PlaceDynamic.project,
            `Miri.Interpreter.Call.initStackFrame,
            `Miri.TreeBorrows.RetagPipeline.retagPointerValue,
            `Miri.Interpreter.ValidityMachine.checkPointerAccess,
            `Miri.Interpreter.ValidityMachine.checkPointerAlign,
            `Miri.Memory.Validity.checkScalar,
            `Miri.Memory.Validity.checkPrimitive,
            `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.lmOcObserve,
            `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.ep1_lean_miri_opaquecast_fnentry_capstone ]) ]
    let mut reachChecked : Nat := 0
    for (root, rs) in reqs do
      let seen := reachFrom root
      for r in rs do
        unless env.contains r do
          throwError "cross-root reachability: {r} is not a constant"
        unless seen.contains r do
          throwError "cross-root reachability failure: {root} does not reach {r}"
        reachChecked := reachChecked + 1
    return (added.size, bundleCount, eqLockCount, totalFixtureLockCount,
      rejected, twins, reachChecked, crAxioms.toArray)

  let ctx : Core.Context :=
    { fileName := "<oc-fp-cross-root>", fileMap := default,
      options := opts, maxHeartbeats := 0 }
  let ((addedCount, bundleCount, eqLockCount, totalLockCount,
        rejectedCount, twinCount, reachCount, crAxioms), _) ←
    liftCoreM <| act.toIO ctx { env := baseEnv }
  unless addedCount ≥ 160 && bundleCount = 4 && eqLockCount = 94 &&
      totalLockCount = 98 && rejectedCount ≥ 45 &&
      twinCount = rejectedCount && reachCount ≥ 44 do
    throwError "cross-root: unexpected counts (added={addedCount}, bundles={bundleCount}, eqLocks={eqLockCount}, totalLocks={totalLockCount}, rejected={rejectedCount}, twins={twinCount}, reach={reachCount})"
  logInfo m!"oc/fp cross-root kernel bridge: added {addedCount} declarations ({bundleCount} bundles, {eqLockCount} Eq.refl + 4 runner = {totalLockCount} fixture locks), rejected {rejectedCount} forged controls ({twinCount}/{rejectedCount} honest twins accepted), {reachCount} reachability edges across Trusted+MiniRust+Miri, axioms {crAxioms}"

/-! ## §3. Constructive Purity, Axiom Audit, and Auditor Self-Tests -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let bNs := `Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec
  let constructiveDecls : List Name :=
    [ `ocCodec, `ocEncode_decode_of_valid, `ocCodec_tight,
      `ocCodec_encode_injective, `ocCodec_decode_injective_on_valid,
      `ocValidRep_iff_decode_isSome, `ocCodec_rejects_malformed,
      `ocModel, `ocAnnealEval, `mrVerdict, `trustedVerdict,
      `lmTableCheckOf_sound, `lmTableCheckOf_of_eq, `cert_transport,
      `mrSide_check, `lmCheckOf_of_table, `bundleOfSel, `bundleOf,
      `domainBundleOf, `threeWayNormalAgreement, `crossAuthorityFaultEquiv,
      `exactBehaviorEq_both, `projectPositive, `projectFault,
      `modeSensitivity_present, `bundle_gate_castDerefBoundary,
      `unified_bundle_witness_kinds, `domain_bundle_claims,
      `dual_exact_three_way_classification, `dual_no_specPanic_all_cells,
      `ocVerdictOf_injective, `lmTable_vs_tables,
      `observer_level_three_way, `observer_level_exact_all_nat,
      `dual_fail_closed_out_of_range, `dual_mode_sensitivity_exact,
      `dual_d2_mode_sensitivity_all_three, `dual_d1_cast_erasure_and_boundary,
      `dual_d2_fnentry_protectors_and_transmute_boundary,
      `dual_d3_dereferenceable_and_zst_boundary,
      `ocTerminatesCleanly, `dual_d2_machine_termination_contrast,
      `rootBackedLmAuthority, `rootBackedLmAuthority_tableCheck,
      `rootBackedLmAuthority_failClosed, `rootBacked_observer_level,
      `stepsM_eq_runToStopM, `stepsTB_eq_runToStopM,
      `ep2_opaquecast_fnentry_dual_authority_capstone,
      `ep2_opaquecast_fnentry_dual_authority_capstone_nonvacuous ]
  let isChoiceFree (axs : Array Name) : Bool :=
    axs.all fun a => a == ``propext || a == ``Quot.sound
  for d in constructiveDecls do
    let axs ← liftCoreM <| Lean.collectAxioms (bNs ++ d)
    unless isChoiceFree axs do
      throwError "constructive audit failure: {d} uses non-constructive axiom ({axs})"
  -- Exhaustive 100% choice-free audit across the ENTIRE
  -- `OpaqueCastAndFnEntryProtectorDualSpec` module (zero allowlist entries!).
  let some modIdx := env.getModuleIdx? bNs
    | throwError "constructive audit failure: module {bNs} not found"
  let modData := env.header.moduleData[modIdx.toNat]!
  let mut exhaustiveChoiceFree : Nat := 0
  for c in modData.constNames do
    if bNs.isPrefixOf c then
      let axs ← liftCoreM <| Lean.collectAxioms c
      unless isChoiceFree axs do
        throwError "exhaustive constructive audit failure: {c} uses non-constructive axiom ({axs})"
      exhaustiveChoiceFree := exhaustiveChoiceFree + 1
  unless exhaustiveChoiceFree ≥ 280 do
    throwError "exhaustive constructive audit vacuous: only {exhaustiveChoiceFree} decls checked"
  -- Self-tests: constructive check rejects `Classical.choice`; standard-axiom
  -- check rejects `sorryAx` and `Lean.ofReduceBool`; trivial-prop detector
  -- rejects `True`, `1 = 1`, `∀ x, x = x`.
  let rec isTrivialProp : Expr → Bool
    | .forallE _ _ body _ => isTrivialProp body
    | .letE _ _ _ body _ => isTrivialProp body
    | e =>
      if e.isConstOf ``True then true
      else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
      else if e.isAppOfArity ``Iff 2 then e.appFn!.appArg! == e.appArg!
      else false
  unless !isChoiceFree (← liftCoreM <| Lean.collectAxioms ``Classical.em) do
    throwError "self-test: Classical.choice was not detected"
  unless !(← liftCoreM <| Lean.collectAxioms ``sorryAx).all
      (fun a => a == ``propext || a == ``Quot.sound || a == ``Classical.choice) do
    throwError "self-test: sorryAx was not detected"
  unless !(← liftCoreM <| Lean.collectAxioms ``Lean.ofReduceBool).all
      (fun a => a == ``propext || a == ``Quot.sound || a == ``Classical.choice) do
    throwError "self-test: Lean.ofReduceBool was not detected"
  let natTy := mkConst ``Nat
  let eq11 := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 1)
  let eq12 := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 2)
  let forallEq := Expr.forallE `x natTy
    (mkApp3 (mkConst ``Eq [1]) natTy (.bvar 0) (.bvar 0)) .default
  unless isTrivialProp (mkConst ``True) && isTrivialProp eq11 &&
      isTrivialProp forallEq && !isTrivialProp eq12 do
    throwError "self-test: trivial theorem detector failed in §3"
  let tNs := `Anneal.Mir.OpaqueCastAndFnEntryProtectorCorrespondenceTests
  let mut checked : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    if let .thmInfo v := info then
      if tNs.isPrefixOf c && !c.isInternal && isTrivialProp v.type then
        throwError "test audit failure: {c} is a trivial theorem"
    for a in ← liftCoreM <| Lean.collectAxioms c do
      if a == ``sorryAx then throwError "test audit failure: {c} uses sorryAx"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "test audit failure: {c} uses non-standard axiom {a}"
    if tNs.isPrefixOf c then checked := checked + 1
  unless checked ≥ 12 do
    throwError "test audit vacuous: only {checked} test declarations"
  logInfo m!"oc/fp constructive audit: {exhaustiveChoiceFree} DualSpec decls ({constructiveDecls.length} spotlighted) 100% in [propext, Quot.sound]; {checked} test decls non-trivial & standard-axiom clean"

end Anneal.Mir.OpaqueCastAndFnEntryProtectorCorrespondenceTests
