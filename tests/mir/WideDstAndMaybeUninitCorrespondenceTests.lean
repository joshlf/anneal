/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Anneal.Mir.WideDstAndMaybeUninitDualSpec
import MiniRustSpec.WideDstAndMaybeUninitMR

/-!
# Episode 2 Correspondence Canaries & Cross-Root 3-Way Kernel Closure
# (Wide DSTs, `MaybeUninit<T>`, Pointer-Offset Chains, `minirust#300` Non-Null `FnPtr`)

1. **§1 Root-Lake canaries** across `D1`–`D4`: positive and negative (UB / OOB / uninit read /
   invalid `bool` read / null `FnPtr`) cells of the REAL Trusted (`stepMirFn`) and MiniRust
   (`stepM`) observers evaluated directly by the kernel (`decide +kernel`, independent of the
   Episode 1 table theorems), flip-direction guards, codec round-trip / tightness / malformed-wire
   rejection, case `19` mode sensitivity, the honest DST boundary (`6`, `7`), the case `13`
   copy-vs-typed-read contrast, and the `#300` flip canaries (`21`, `22`, `23`).
2. **§2 Cross-root kernel bridge (`run_cmd`)**: loads `.lake/build/lib/lean` (root) AND
   `examples/.lake/build/lib/lean` (`LeanMiriSpec.WideDstAndMaybeUninitLM`) into a fresh kernel
   environment, builds the genuine `WdLmAuthority` over `lmWdObserve` (translation by
   `LmWdObs.rec.{1}`, zero mocks), kernel-evaluates its 48-cell certificate on the loop-unrolled
   twin `lmWdObserveU` and transports it along `lmWdObserveU.eq_src`, discharges fail-closedness
   from `lmWdObserve_out_of_range`, and closes the unified + 4 per-domain bundles, all lifted
   theorems, projections, and the Episode 2 capstone; locks every shared `CapturedMir` fixture by
   `Eq.refl`; verifies ≥ 10 forged controls are REJECTED by the kernel (each paired with an
   accepted honest twin where meaningful); and checks transitive reachability of Trusted,
   MiniRust, and vendored Miri.
3. **§3 Audits**: constructive (`[propext, Quot.sound]`) purity of the Episode 2 combinators,
   standard-3-axiom purity of this module, and auditor self-tests.
-/

namespace Anneal.Mir.WideDstAndMaybeUninitCorrespondenceTests

set_option Elab.async false

open Anneal.DualCorrespondenceBundle
open Anneal.Mir.DropBinderAndSubtypeBundle
open Anneal.Mir.WideDstAndMaybeUninitDualSpec
open MiniRustSpec.WideDstAndMaybeUninitMR

/-! ## §1. Root-Lake Concrete Canaries -/

/-- Codec round-trip on every constructor, tightness, canonical encodings, and malformed-wire
rejection. -/
theorem wd_codec_canaries :
    wdCodec.decode (wdCodec.encode (.scalar 22)) = some (.scalar 22) ∧
    wdCodec.decode (wdCodec.encode (.sizeAlign 16 8)) = some (.sizeAlign 16 8) ∧
    wdCodec.decode (wdCodec.encode (.uninitPreserved 4 1)) = some (.uninitPreserved 4 1) ∧
    wdCodec.decode (wdCodec.encode (.fnPtr 0)) = some (.fnPtr 0) ∧
    wdEncode (.scalar 0) ≠ wdEncode (.fnPtr 0) ∧
    wdEncode (.sizeAlign 16 4) ≠ wdEncode (.uninitPreserved 16 4) ∧
    wdDecode (0, 5, 1) = none ∧ wdDecode (3, 7, 9) = none ∧ wdDecode (4, 0, 0) = none ∧
    ¬ wdValidRep (0, 5, 1) ∧ wdValidRep (1, 16, 8) ∧
    wdCodec.TightValidRep := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, by decide, rfl, rfl, rfl, id, True.intro, wdCodec_tight⟩

/-- `D1` (direct kernel execution): checked indexing (`22`), `size_of_val` on `[u32]` and the
exact `isize::MAX` boundary are accepted; the overflowing length (`4`) and OOB index (`5`) are UB
in BOTH Trusted and MiniRust; flip guard: the positive and fault cells differ. -/
theorem d1_wide_slice_canaries :
    trustedVerdict false 0 = some (.returns (.scalar 22)) ∧
    mrVerdict false 0 = some (.returns (.scalar 22)) ∧
    trustedVerdict true 1 = some (.returns (.sizeAlign 12 4)) ∧
    mrVerdict true 1 = some (.returns (.sizeAlign 12 4)) ∧
    trustedVerdict false 3 = some (.returns (.sizeAlign 9223372036854775804 4)) ∧
    mrVerdict false 3 = some (.returns (.sizeAlign 9223372036854775804 4)) ∧
    trustedVerdict false 4 = some .undefinedBehavior ∧ mrVerdict false 4 = some .undefinedBehavior ∧
    trustedVerdict true 5 = some .undefinedBehavior ∧ mrVerdict true 5 = some .undefinedBehavior ∧
    mrVerdict false 0 ≠ mrVerdict false 4 := by
  decide +kernel

/-- `D1` honest boundary (direct kernel execution): Trusted is `.unsupported` on the trailing-slice
DST structs while MiniRust computes `okSizeAlign 16 4` / `okSizeAlign 16 8`. -/
theorem d1_dst_boundary_canaries :
    trustedVerdict false 6 = some .unsupported ∧ trustedVerdict true 7 = some .unsupported ∧
    mrVerdict false 6 = some (.returns (.sizeAlign 16 4)) ∧
    mrVerdict true 7 = some (.returns (.sizeAlign 16 8)) ∧
    wdClassOf 6 = .dstBoundary ∧ wdClassOf 7 = .dstBoundary := by
  decide +kernel

/-- `D2` (direct kernel execution): whole-union copies preserve uninit / partially-init bytes,
`ManuallyDrop` transports `77`, and typed reads of uninit `MaybeUninit<u32>` (`12`) and of an
invalid `bool` byte (`13`) are UB; flip guard: copy cells differ from typed-read cells. -/
theorem d2_maybeuninit_canaries :
    trustedVerdict false 8 = some (.returns (.uninitPreserved 4 0)) ∧
    mrVerdict false 8 = some (.returns (.uninitPreserved 4 0)) ∧
    trustedVerdict true 9 = some (.returns (.uninitPreserved 4 1)) ∧
    mrVerdict true 9 = some (.returns (.uninitPreserved 4 1)) ∧
    mrVerdict false 10 = some (.returns (.scalar 305419896)) ∧
    mrVerdict false 11 = some (.returns (.scalar 77)) ∧
    trustedVerdict false 12 = some .undefinedBehavior ∧ mrVerdict true 12 = some .undefinedBehavior ∧
    trustedVerdict true 13 = some .undefinedBehavior ∧ mrVerdict false 13 = some .undefinedBehavior ∧
    mrVerdict false 8 ≠ mrVerdict false 12 := by
  decide +kernel

/-- `D2` case `13` companion: the whole-union copy of the invalid `bool` byte succeeds in Trusted
and MiniRust (both modes) while the typed read is UB. -/
theorem d2_case13_copy_contrast :
    wdRunTrusted (.unionBytes wdMuBoolTy) wdCase13CopyMir wdTrustedFuel
        (wdLiveState wdCase13CopyMir []) = .okUninitPreserved 1 1 ∧
    wdRun false mrWdProg13Copy = .okUninitPreserved 1 1 ∧
    wdRun true mrWdProg13Copy = .okUninitPreserved 1 1 ∧
    mrWdObserve false 13 = .ub ∧ mrTrustedWdObserve true 13 = .ub :=
  ⟨mrTrusted_case13_union_copy_of_invalid_bool_byte_ok.1,
   mr_case13_union_copy_of_invalid_bool_byte_ok.1, mr_case13_union_copy_of_invalid_bool_byte_ok.2.1,
   mr_case13_union_copy_of_invalid_bool_byte_ok.2.2.1,
   mrTrusted_case13_union_copy_of_invalid_bool_byte_ok.2.2⟩

/-- `D3` (direct kernel execution): in-bounds / wrapping offset chains return `200` / `100`, OOB
dereferences are UB, and case `19` is mode-sensitive in BOTH Trusted and MiniRust. -/
theorem d3_offset_chain_canaries :
    trustedVerdict false 14 = some (.returns (.scalar 200)) ∧
    mrVerdict false 14 = some (.returns (.scalar 200)) ∧
    mrVerdict true 15 = some (.returns (.scalar 200)) ∧
    trustedVerdict false 16 = some .undefinedBehavior ∧ mrVerdict false 16 = some .undefinedBehavior ∧
    mrVerdict true 17 = some .undefinedBehavior ∧
    trustedVerdict true 18 = some (.returns (.scalar 100)) ∧
    mrVerdict true 18 = some (.returns (.scalar 100)) ∧
    trustedVerdict false 19 = some (.returns (.scalar 999)) ∧
    trustedVerdict true 19 = some .undefinedBehavior ∧
    mrVerdict false 19 = some (.returns (.scalar 999)) ∧
    mrVerdict true 19 = some .undefinedBehavior ∧
    mrVerdict false 19 ≠ mrVerdict true 19 ∧ trustedVerdict false 19 ≠ trustedVerdict true 19 := by
  decide +kernel

/-- `D4` (direct kernel execution): valid `FnPtr` (`20`), post-`#300` null `FnPtr` rejection
(`21`), the pinned pre-`#300` divergence (`22`: MiniRust `okFnPtr 0`, Trusted `.ub`), and raw
null `*const u8` acceptance (`23`). -/
theorem d4_fnptr_minirust300_canaries :
    trustedVerdict false 20 = some (.returns (.fnPtr 1)) ∧
    mrVerdict false 20 = some (.returns (.fnPtr 1)) ∧
    trustedVerdict false 21 = some .undefinedBehavior ∧ mrVerdict false 21 = some .undefinedBehavior ∧
    trustedVerdict true 22 = some .undefinedBehavior ∧
    mrVerdict true 22 = some (.returns (.fnPtr 0)) ∧
    trustedVerdict false 23 = some (.returns (.fnPtr 0)) ∧
    mrVerdict true 23 = some (.returns (.fnPtr 0)) ∧
    mrVerdict false 22 ≠ trustedVerdict false 22 ∧ mrVerdict false 21 = trustedVerdict false 21 ∧
    wdClassOf 22 = .pinDelta ∧ wdClassOf 21 = .threeWay := by
  decide +kernel

/-- Fail-closed out-of-range cells (`24`, `1000`) on Trusted and MiniRust, and the class layout:
exactly 21 three-way, 2 DST-boundary, and 1 pin-delta case. -/
theorem out_of_range_and_class_canaries :
    trustedVerdict false 24 = some .unsupported ∧ mrVerdict true 24 = some .unsupported ∧
    trustedVerdict true 1000 = some .unsupported ∧ mrVerdict false 1000 = some .unsupported ∧
    ((List.range 24).filter (fun i => wdClassOf i == .threeWay)).length = 21 ∧
    ((List.range 24).filter (fun i => wdClassOf i == .dstBoundary)) = [6, 7] ∧
    ((List.range 24).filter (fun i => wdClassOf i == .pinDelta)) = [22] ∧
    wdClassOf 24 = .outOfRange := by
  refine ⟨trustedVerdict_out_of_range false 24 (by decide), mrVerdict_out_of_range true 24 (by decide),
    trustedVerdict_out_of_range true 1000 (by decide), mrVerdict_out_of_range false 1000 (by decide),
    by decide, by decide, by decide, by decide⟩

/-- Root-side instantiation of the capstone at the real-observer-backed authority (non-vacuity of
the capstone hypotheses), with its unified bundle's positive / fault projections. -/
theorem root_capstone_instantiation :
    lmTableCheckOf rootBackedLmAuthority = true ∧
    (∀ sel, lmCheckOf sel rootBackedLmAuthority = true) ∧
    type_of% (projectPositive rootBackedLmAuthority rootBackedLmAuthority_tableCheck) ∧
    type_of% (projectFault rootBackedLmAuthority rootBackedLmAuthority_tableCheck) :=
  ⟨rootBackedLmAuthority_tableCheck,
   fun sel => lmCheckOf_of_table sel _ rootBackedLmAuthority_tableCheck,
   projectPositive _ rootBackedLmAuthority_tableCheck,
   projectFault _ rootBackedLmAuthority_tableCheck⟩

/-! ## §2. Cross-Root 3-Way Kernel Closure (`MiniRustSpec` + `LeanMiriSpec` + `Anneal`) -/

open Lean Elab Command Meta in
run_cmd do
  let opts := (← getOptions).setBool `Elab.async false
  let sp : SearchPath := [System.FilePath.mk ".lake/build/lib/lean",
                          System.FilePath.mk "examples/.lake/build/lib/lean"]
  initSearchPath (← findSysroot) sp
  let baseEnv ← importModules
    #[{ module := `Anneal.Mir.WideDstAndMaybeUninitDualSpec },
      { module := `MiniRustSpec.WideDstAndMaybeUninitMR },
      { module := `LeanMiriSpec.WideDstAndMaybeUninitLM }]
    {} 0
  let ns := `Anneal.Mir.WideDstAndMaybeUninitCorrespondenceTests.CrossRoot
  let bNs := `Anneal.Mir.WideDstAndMaybeUninitDualSpec
  let cNs := `Anneal.Mir.DropBinderAndSubtypeBundle.Corpus
  let mrNs := `MiniRustSpec.WideDstAndMaybeUninitMR
  let lmNs := `LeanMiriSpec.WideDstAndMaybeUninitLM
  let act : CoreM (Nat × Nat × Nat × Nat × Nat × Array Name) := do
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
    let eqTrue (e : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) boolTy e (mkConst ``Bool.true)
    let reflTrue : Expr := mkApp2 (mkConst ``Eq.refl [1]) boolTy (mkConst ``Bool.true)
    let eqFalse (e : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) boolTy e (mkConst ``Bool.false)
    let reflFalse : Expr := mkApp2 (mkConst ``Eq.refl [1]) boolTy (mkConst ``Bool.false)
    let mkEq (ty a b : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) ty a b
    let mkRefl (ty a : Expr) : Expr := mkApp2 (mkConst ``Eq.refl [1]) ty a
    let thmD (n : Name) (ty pf : Expr) : Declaration :=
      .thmDecl { name := n, levelParams := [], type := ty, value := pf }

    -- 1. The genuine LeanMiri authority over `lmWdObserve` (translation by `LmWdObs.rec.{1}`).
    let obsTy := mkConst (bNs ++ `WdObs)
    let verdTy := mkApp (mkConst (cNs ++ `Verdict)) obsTy
    let optVerdTy := mkApp (mkConst ``Option [0]) verdTy
    let someV (e : Expr) : Expr := mkApp2 (mkConst ``Option.some [0]) verdTy e
    let retV (e : Expr) : Expr := mkApp2 (mkConst (cNs ++ `Verdict.returns)) obsTy e
    let ubV := someV (mkApp (mkConst (cNs ++ `Verdict.undefinedBehavior)) obsTy)
    let unsV := someV (mkApp (mkConst (cNs ++ `Verdict.unsupported)) obsTy)
    let lmObsTy := mkConst (lmNs ++ `LmWdObs)
    let lmObsC (c : Name) : Expr := mkConst (lmNs ++ `LmWdObs ++ c)
    let mkToVerdict (swapUbUnsupported : Bool) : MetaM Expr :=
      withLocalDeclD `o lmObsTy fun o => do
        let motive := mkLambda `x .default lmObsTy optVerdTy
        let m1 := mkLambda `v .default natTy (someV (retV (mkApp (mkConst (bNs ++ `WdObs.scalar)) (.bvar 0))))
        let m2 := mkLambda `s .default natTy <| mkLambda `a .default natTy <|
          someV (retV (mkApp2 (mkConst (bNs ++ `WdObs.sizeAlign)) (.bvar 1) (.bvar 0)))
        let m3 := mkLambda `b .default natTy <| mkLambda `i .default natTy <|
          someV (retV (mkApp2 (mkConst (bNs ++ `WdObs.uninitPreserved)) (.bvar 1) (.bvar 0)))
        let m4 := mkLambda `a .default natTy (someV (retV (mkApp (mkConst (bNs ++ `WdObs.fnPtr)) (.bvar 0))))
        let m5 := if swapUbUnsupported then unsV else ubV
        let m6 := if swapUbUnsupported then ubV else unsV
        let m7 := mkApp (mkConst ``Option.none [0]) verdTy
        mkLambdaFVars #[o] (mkAppN (mkConst (lmNs ++ `LmWdObs.rec) [1])
          #[motive, m1, m2, m3, m4, m5, m6, m7, o])
    let toVName := ns ++ `lmWdToVerdict
    let _ ← addDef toVName (← MetaM.run' <| mkToVerdict false)
    let toV := mkConst toVName
    let mkAuth (observe toVerdict : Expr) : Expr :=
      mkApp3 (mkConst (bNs ++ `WdLmAuthority.mk)) lmObsTy observe toVerdict
    let lmObserve := mkConst (lmNs ++ `lmWdObserve)
    let lmObserveU := mkConst (lmNs ++ `lmWdObserveU)
    let authName := ns ++ `lmAuthority
    let _ ← addDef authName (mkAuth lmObserve toV)
    let authC := mkConst authName
    let authUName := ns ++ `lmAuthorityU
    let _ ← addDef authUName (mkAuth lmObserveU toV)
    let authUC := mkConst authUName
    let mut added : Array Name := #[toVName, authName, authUName]

    -- 2. Certificates: kernel evaluation on the twin, transport along `lmWdObserveU.eq_src`, and
    -- fail-closedness from `lmWdObserve_out_of_range`.
    let eqName := ns ++ `lmAuthority_eq_unrolled
    let eqPf ← MetaM.run' do
      let g ← withLocalDeclD `g (← inferType lmObserve) fun g => mkLambdaFVars #[g] (mkAuth g toV)
      mkAppM ``congrArg #[g, mkConst (lmNs ++ `lmWdObserveU.eq_src)]
    addThmInfer eqName eqPf
    added := added.push eqName
    let tblUName := ns ++ `lmAuthorityU_tableCheck
    addThm tblUName (eqTrue (mkApp (mkConst (bNs ++ `lmTableCheckOf)) authUC)) reflTrue
    added := added.push tblUName
    let tblName := ns ++ `lmAuthority_tableCheck
    addThm tblName (eqTrue (mkApp (mkConst (bNs ++ `lmTableCheckOf)) authC))
      (mkApp4 (mkConst (bNs ++ `lmTableCheckOf_of_eq)) authC authUC (mkConst eqName) (mkConst tblUName))
    added := added.push tblName
    let hA := mkConst tblName
    let fcName := ns ++ `lmAuthority_failClosed
    let fcPf ← MetaM.run' do
      withLocalDeclD `tb boolTy fun tb => withLocalDeclD `idx natTy fun idx => do
        let le := mkApp4 (mkConst ``LE.le [0]) natTy (mkConst ``instLENat)
          (mkConst (mrNs ++ `mrWdCaseCount)) idx
        withLocalDeclD `h le fun h => do
          let oor := mkApp3 (mkConst (lmNs ++ `lmWdObserve_out_of_range)) tb idx h
          mkLambdaFVars #[tb, idx, h] (← mkAppM ``congrArg #[toV, oor])
    addThm fcName (mkApp (mkConst (bNs ++ `WdLmFailClosed)) authC) fcPf
    added := added.push fcName
    let hOob := mkConst fcName
    -- Direct (non-derived) kernel evaluation of every LeanMiri side certificate on the twin.
    let domNs := bNs ++ `WdDomain
    let domains : List Name := [`d1, `d2, `d3, `d4]
    let selTy := mkApp (mkConst ``Option [0]) (mkConst domNs)
    let sels : List (Name × Expr) :=
      (`unified, mkApp (mkConst ``Option.none [0]) (mkConst domNs)) ::
        domains.map fun d => (d, mkApp2 (mkConst ``Option.some [0]) (mkConst domNs) (mkConst (domNs ++ d)))
    let _ := selTy
    for (tag, sel) in sels do
      let n := ns ++ `lmSideCheckU ++ tag
      addThm n (eqTrue (mkApp2 (mkConst (bNs ++ `lmCheckOf)) sel authUC)) reflTrue
      added := added.push n
      let n' := ns ++ `lmSideCheck ++ tag
      addThmInfer n' (mkApp3 (mkConst (bNs ++ `lmCheckOf_of_table)) sel authC hA)
      added := added.push n'

    -- 3. Close the unified and all 4 per-domain bundles, every lifted theorem, and the capstone.
    let unifiedName := ns ++ `unifiedDualBundle
    let uTy ← addDef unifiedName (mkApp2 (mkConst (bNs ++ `bundleOf)) authC hA)
    unless uTy.getAppFn.isConstOf ``Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle ||
        uTy.isConstOf (bNs ++ `WdBundle) do
      throwError "cross-root: {unifiedName} is not a DualCorrespondenceBundle"
    added := added.push unifiedName
    let mut bundleCount : Nat := 1
    for d in domains do
      let n := ns ++ `domainBundle ++ d
      let _ ← addDef n (mkApp3 (mkConst (bNs ++ `domainBundleOf)) (mkConst (domNs ++ d)) authC hA)
      added := added.push n
      bundleCount := bundleCount + 1
      addThmInfer (ns ++ `domainClaims ++ d)
        (mkApp3 (mkConst (bNs ++ `domain_bundle_claims)) (mkConst (domNs ++ d)) authC hA)
      added := added.push (ns ++ `domainClaims ++ d)
      for proj in [``DualCorrespondenceBundle.projectPositive, ``DualCorrespondenceBundle.projectFault] do
        let pv ← MetaM.run' <| mkAppM proj #[mkConst n]
        let pn := ns ++ `domainProjection ++ d ++ proj.getString!.toName
        addThmInfer pn pv
        added := added.push pn
    for proj in [``DualCorrespondenceBundle.projectPositive, ``DualCorrespondenceBundle.projectFault] do
      let pv ← MetaM.run' <| mkAppM proj #[mkConst unifiedName]
      let pn := ns ++ `unifiedProjection ++ proj.getString!.toName
      addThmInfer pn pv
      added := added.push pn
    for thmName in [`threeWayNormalAgreement, `crossAuthorityFaultEquiv, `exactBehaviorEq_both,
                    `projectPositive, `projectFault, `modeSensitivity_present,
                    `dual_exact_three_way_classification, `dual_mode_sensitivity_exact,
                    `dual_case19_mode_sensitivity, `dual_dst_honest_trusted_boundary,
                    `dual_minirust300_pin_delta_and_flip_ready,
                    `dual_case13_union_copy_vs_typed_read] do
      addThmInfer (ns ++ thmName) (mkApp2 (mkConst (bNs ++ thmName)) authC hA)
      added := added.push (ns ++ thmName)
    addThmInfer (ns ++ `dual_fail_closed_out_of_range)
      (mkApp2 (mkConst (bNs ++ `dual_fail_closed_out_of_range)) authC hOob)
    added := added.push (ns ++ `dual_fail_closed_out_of_range)
    let capName := ns ++ `ep2_widedst_maybeuninit_dual_authority_capstone
    addThmInfer capName
      (mkApp3 (mkConst (bNs ++ `ep2_widedst_maybeuninit_dual_authority_capstone)) authC hA hOob)
    added := added.push capName
    -- The closed capstone conjoined with the Episode 1 LeanMiri capstones (step driver, universal
    -- laws, tables): the root of the 3-engine reachability audit below.
    let crossName := ns ++ `ep2_cross_root_three_engine_capstone
    let crossPf ← MetaM.run' do
      let parts : List Expr :=
        [ mkConst capName,
          mkConst (lmNs ++ `ep1_lean_miri_widedst_maybeuninit_capstone),
          mkConst (lmNs ++ `ep1_lean_miri_universal_laws_capstone),
          mkConst (lmNs ++ `ep1_lean_miri_step_driver_capstone),
          mkConst (lmNs ++ `lmWdObserve_table),
          mkConst (lmNs ++ `lmWdObserve_mode_sensitivity),
          mkConst (lmNs ++ `lm_wd_exact_ub_diagnostics) ]
      let rec conj : List Expr → MetaM Expr
        | [] => return mkConst ``True.intro
        | [p] => return p
        | p :: ps => do mkAppM ``And.intro #[p, ← conj ps]
      conj parts
    addThmInfer crossName crossPf
    added := added.push crossName

    -- 4. Definitional `Eq.refl` fixture locks over every shared fixture.
    let fixtureNames : List Name :=
      [ `wdCase0Mir, `wdCase1Mir, `wdCase2Mir, `wdCase2StrMir, `wdCase3Mir, `wdCase4Mir,
        `wdCase5Mir, `wdCase6Mir, `wdCase7Mir, `wdCase8Mir, `wdCase9Mir, `wdCase10Mir,
        `wdCase11Mir, `wdCase12Mir, `wdCase13Mir, `wdCase13CopyMir, `wdCase14Mir, `wdCase15Mir,
        `wdCase16Mir, `wdCase17Mir, `wdCase18Mir, `wdCase19Mir, `wdCase20Mir, `wdCase21Mir,
        `wdCase23Mir, `wdLayouts ]
    let mut lockCount : Nat := 0
    for tag in fixtureNames do
      let lhs := mkConst (mrNs ++ tag)
      let rhs := mkConst (lmNs ++ tag)
      let ty ← MetaM.run' <| inferType lhs
      let lockName := ns ++ `fixtureLock ++ tag
      addThm lockName (mkEq ty lhs rhs) (mkRefl ty lhs)
      added := added.push lockName
      lockCount := lockCount + 1
    unless lockCount = 26 do
      throwError "cross-root: expected 26 fixture locks, got {lockCount}"

    -- 5. Negative forgery controls on scratch environment copies: each forged declaration MUST be
    -- rejected by the kernel; each honest twin (when present) MUST be accepted, so rejections are
    -- caused by the forged content, not by an unevaluable term.
    let saved ← getEnv
    let accepts (d : Declaration) : CoreM Bool := do
      let r ← try addDecl d; pure true catch _ => pure false
      setEnv saved
      return r
    let invObserve ← MetaM.run' <|
      withLocalDeclD `tb boolTy fun tb => withLocalDeclD `idx natTy fun idx =>
        mkLambdaFVars #[tb, idx] (mkApp2 lmObserveU (mkApp (mkConst ``Bool.not) tb) idx)
    let invAuth := mkAuth invObserve toV
    let swapAuth := mkAuth lmObserveU (← MetaM.run' <| mkToVerdict true)
    let tblCheck (a : Expr) := mkApp (mkConst (bNs ++ `lmTableCheckOf)) a
    let mrObs (tb : Bool) (i : Nat) : Expr :=
      mkApp2 (mkConst (mrNs ++ `mrWdObserve)) (toExpr tb) (mkNatLit i)
    let trObs (tb : Bool) (i : Nat) : Expr :=
      mkApp2 (mkConst (mrNs ++ `mrTrustedWdObserve)) (toExpr tb) (mkNatLit i)
    let lmObsU (tb : Bool) (i : Nat) : Expr := mkApp2 lmObserveU (toExpr tb) (mkNatLit i)
    let mrObsTy := mkConst (mrNs ++ `MrWdObs)
    let mrC (c : Name) : Expr := mkConst (mrNs ++ `MrWdObs ++ c)
    let mrFn (n : Nat) : Expr := mkApp (mrC `okFnPtr) (mkNatLit n)
    let lmFn (n : Nat) : Expr := mkApp (lmObsC `okFnPtr) (mkNatLit n)
    let repTy ← MetaM.run' <| inferType (mkApp (mkConst (bNs ++ `wdEncode)) (mkApp (mkConst (bNs ++ `WdObs.scalar)) (mkNatLit 0)))
    let optObsTy := mkApp (mkConst ``Option [0]) obsTy
    let triple (a b c : Nat) : MetaM Expr := do
      mkAppM ``Prod.mk #[mkNatLit a, ← mkAppM ``Prod.mk #[mkNatLit b, mkNatLit c]]
    let scalarObs (n : Nat) := mkApp (mkConst (bNs ++ `WdObs.scalar)) (mkNatLit n)
    let fnObs (n : Nat) := mkApp (mkConst (bNs ++ `WdObs.fnPtr)) (mkNatLit n)
    let someObs (e : Expr) := mkApp2 (mkConst ``Option.some [0]) obsTy e
    let decode (t : Expr) := mkApp (mkConst (bNs ++ `wdDecode)) t
    let encode (o : Expr) := mkApp (mkConst (bNs ++ `wdEncode)) o
    let t051 ← MetaM.run' <| triple 0 5 1
    let t050 ← MetaM.run' <| triple 0 5 0
    let t400 ← MetaM.run' <| triple 4 0 0
    let t300 ← MetaM.run' <| triple 3 0 0
    let lmVerd (a : Expr) (tb : Bool) (i : Nat) : Expr :=
      mkApp3 (mkConst (bNs ++ `WdLmAuthority.verdict)) a (toExpr tb) (mkNatLit i)
    let isRet (e : Expr) : Expr := mkApp2 (mkConst (cNs ++ `isReturn)) obsTy e
    let isFault (e : Expr) : Expr := mkApp2 (mkConst (cNs ++ `isFaultV)) obsTy e
    let mrVerd (tb : Bool) (i : Nat) : Expr :=
      mkApp2 (mkConst (bNs ++ `mrVerdict)) (toExpr tb) (mkNatLit i)
    let capMirTy ← MetaM.run' <| inferType (mkConst (mrNs ++ `wdCase0Mir))
    let forged : List (String × Declaration × Option Declaration) :=
      [ ("ill-typed 0 = 1",
          thmD (ns ++ `forged.zeroEqOne) (mkEq natTy (mkNatLit 0) (mkNatLit 1)) (mkRefl natTy (mkNatLit 0)),
          some (thmD (ns ++ `honest.zeroEqZero) (mkEq natTy (mkNatLit 0) (mkNatLit 0)) (mkRefl natTy (mkNatLit 0)))),
        ("negated LM 48-cell certificate",
          thmD (ns ++ `forged.lmTableFalse) (eqFalse (tblCheck authUC)) reflFalse, none),
        ("mode-inverted LM authority (Bool.not tb) certificate",
          thmD (ns ++ `forged.modeInverted) (eqTrue (tblCheck invAuth)) reflTrue, none),
        ("ub/unsupported-swapped LM translation certificate",
          thmD (ns ++ `forged.swappedTranslation) (eqTrue (tblCheck swapAuth)) reflTrue, none),
        ("swapped fixture lock (wdCase0Mir = wdCase5Mir)",
          thmD (ns ++ `forged.swappedFixture)
            (mkEq capMirTy (mkConst (mrNs ++ `wdCase0Mir)) (mkConst (lmNs ++ `wdCase5Mir)))
            (mkRefl capMirTy (mkConst (mrNs ++ `wdCase0Mir))),
          some (thmD (ns ++ `honest.fixture5)
            (mkEq capMirTy (mkConst (mrNs ++ `wdCase5Mir)) (mkConst (lmNs ++ `wdCase5Mir)))
            (mkRefl capMirTy (mkConst (mrNs ++ `wdCase5Mir))))),
        ("forged codec decode of non-zero padding (0,5,1)",
          thmD (ns ++ `forged.decodePadding) (mkEq optObsTy (decode t051) (someObs (scalarObs 5)))
            (mkRefl optObsTy (decode t051)),
          some (thmD (ns ++ `honest.decodeCanonical) (mkEq optObsTy (decode t050) (someObs (scalarObs 5)))
            (mkRefl optObsTy (decode t050)))),
        ("forged codec decode of invalid wire tag 4",
          thmD (ns ++ `forged.decodeTag4) (mkEq optObsTy (decode t400) (someObs (scalarObs 0)))
            (mkRefl optObsTy (decode t400)), none),
        ("forged colliding codec encodings (scalar 0 = fnPtr 0)",
          thmD (ns ++ `forged.encodeCollision) (mkEq repTy (encode (scalarObs 0)) (encode (fnObs 0)))
            (mkRefl repTy (encode (scalarObs 0))),
          some (thmD (ns ++ `honest.encodeFnPtr) (mkEq repTy (encode (fnObs 0)) t300)
            (mkRefl repTy (encode (fnObs 0))))),
        ("forged case 22: pinned d821c6e3 MiniRust rejects null FnPtr",
          thmD (ns ++ `forged.case22MrUb) (mkEq mrObsTy (mrObs false 22) (mrC `ub)) (mkRefl mrObsTy (mrObs false 22)),
          some (thmD (ns ++ `honest.case22MrOk) (mkEq mrObsTy (mrObs false 22) (mrFn 0)) (mkRefl mrObsTy (mrObs false 22)))),
        ("forged case 22: LeanMiri follows the pinned MiniRust null FnPtr acceptance",
          thmD (ns ++ `forged.case22LmOk) (mkEq lmObsTy (lmObsU false 22) (lmFn 0)) (mkRefl lmObsTy (lmObsU false 22)),
          some (thmD (ns ++ `honest.case22LmUb) (mkEq lmObsTy (lmObsU false 22) (lmObsC `ub)) (mkRefl lmObsTy (lmObsU false 22)))),
        ("forged case 21: post-#300 checkPtrFnNonNull accepts null FnPtr",
          thmD (ns ++ `forged.case21MrOk) (mkEq mrObsTy (mrObs true 21) (mrFn 0)) (mkRefl mrObsTy (mrObs true 21)),
          some (thmD (ns ++ `honest.case21MrUb) (mkEq mrObsTy (mrObs true 21) (mrC `ub)) (mkRefl mrObsTy (mrObs true 21)))),
        ("forged case 6: unmodified Trusted computes okSizeAlign 16 4",
          thmD (ns ++ `forged.case6TrustedOk)
            (mkEq mrObsTy (trObs false 6) (mkApp2 (mrC `okSizeAlign) (mkNatLit 16) (mkNatLit 4)))
            (mkRefl mrObsTy (trObs false 6)),
          some (thmD (ns ++ `honest.case6TrustedUnsupported) (mkEq mrObsTy (trObs false 6) (mrC `unsupported))
            (mkRefl mrObsTy (trObs false 6)))),
        ("forged case 19 mode invariance (MiniRust basic = treeBorrows)",
          thmD (ns ++ `forged.case19MrInvariant) (mkEq mrObsTy (mrObs false 19) (mrObs true 19))
            (mkRefl mrObsTy (mrObs false 19)),
          some (thmD (ns ++ `honest.case19MrTbUb) (mkEq mrObsTy (mrObs true 19) (mrC `ub)) (mkRefl mrObsTy (mrObs true 19)))),
        ("forged case 19 mode invariance (LeanMiri basic = treeBorrows)",
          thmD (ns ++ `forged.case19LmInvariant) (mkEq lmObsTy (lmObsU false 19) (lmObsU true 19))
            (mkRefl lmObsTy (lmObsU false 19)),
          some (thmD (ns ++ `honest.case19LmTbUb) (mkEq lmObsTy (lmObsU true 19) (lmObsC `ub)) (mkRefl lmObsTy (lmObsU true 19)))),
        ("forged case 12: LeanMiri accepts the uninit MaybeUninit<u32> typed read",
          thmD (ns ++ `forged.case12LmAccepts) (eqTrue (isRet (lmVerd authUC false 12))) reflTrue,
          some (thmD (ns ++ `honest.case12LmFaults) (eqTrue (isFault (lmVerd authUC false 12))) reflTrue)),
        ("forged case 12: MiniRust accepts the uninit MaybeUninit<u32> typed read",
          thmD (ns ++ `forged.case12MrAccepts) (eqTrue (isRet (mrVerd true 12))) reflTrue,
          some (thmD (ns ++ `honest.case12MrFaults) (eqTrue (isFault (mrVerd true 12))) reflTrue)) ]
    let mut rejected : Nat := 0
    let mut twins : Nat := 0
    for (what, d, honest?) in forged do
      if ← accepts d then
        throwError "cross-root negative control FAILED: kernel accepted {what}"
      rejected := rejected + 1
      if let some h := honest? then
        unless ← accepts h do
          throwError "cross-root negative control VACUOUS: honest twin of {what} was rejected"
        twins := twins + 1

    -- 6. Axiom / non-triviality audit of every added declaration and required LM theorems.
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
      [ `lmWdObserve_table, `lmWdObserve_out_of_range, `lmWdObserve_mode_sensitivity,
        `lm_wd_exact_ub_diagnostics, `lm_case13_union_copy_of_invalid_bool_byte_ok,
        `lm_sizeAndAlign_headerSlice, `lm_sizeAndAlign_align8TailU16,
        `lm_allocation_copy_uninit_preserves, `lm_initMask_prepareCopy_lazy_uninit,
        `lm_ptrOffsetInbounds_eq_wrapping, `lm_fnptr_validity_range,
        `ep1_lean_miri_widedst_maybeuninit_capstone, `ep1_lean_miri_universal_laws_capstone,
        `ep1_lean_miri_step_driver_capstone ]
    for t in lmDeepThms do
      let n := lmNs ++ t
      let some (.thmInfo v) := env.find? n | throwError "cross-root: required LM theorem {n} missing"
      if isTrivialProp v.type then throwError "cross-root: LM theorem {n} is trivial"
      for a in ← collectAxioms n do
        unless isStdAx a do throwError "cross-root: LM theorem {n} depends on non-standard axiom {a}"
        crAxioms := crAxioms.insert a
    unless !(← collectAxioms ``sorryAx).all isStdAx do
      throwError "cross-root self-test: sorryAx was not detected"
    unless !(← collectAxioms ``Lean.ofReduceBool).all isStdAx do
      throwError "cross-root self-test: Lean.ofReduceBool was not detected"
    let trivEq := mkEq natTy (mkNatLit 1) (mkNatLit 1)
    unless isTrivialProp (mkConst ``True) && isTrivialProp trivEq &&
        !isTrivialProp (mkEq natTy (mkNatLit 1) (mkNatLit 2)) do
      throwError "cross-root self-test: trivial theorem detector failed"

    -- 7. Transitive 3-engine reachability.
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
            `MiniRustSpec.WideDstAndMaybeUninitMR.mrTrustedWdObserve,
            `MiniRustSpec.WideDstAndMaybeUninitMR.mrWdObserve,
            `MiniRustSpec.Interp.checkPtrM,
            `LeanMiriSpec.WideDstAndMaybeUninitLM.lmWdObserve,
            `LeanMiriSpec.WideDstAndMaybeUninitLM.lmWdObserveU,
            `Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta,
            `Miri.Interpreter.ptrOffsetInbounds,
            `Miri.Memory.Allocation.copy ]),
        (crossName,
          [ `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
            `Trusted.Rustc.V2026_06_01.MirSemantics.decodePtrBytesNoForge,
            `Trusted.Rustc.V2026_06_01.MirSemantics.decodeTypedValueFromBytes,
            `Trusted.Rustc.V2026_06_01.MirSemantics.intrinsicWidePointeeStep,
            `MiniRustSpec.Interp.steps,
            `MiniRustSpec.Interp.stepsTB,
            `MiniRustSpec.Interp.checkPtrM,
            `MiniRustSpec.Interp.LayoutStrategy.compute_size_and_align,
            `MiniRustSpec.Interp.ptrOffsetInboundsM,
            `Miri.Interpreter.Step.step,
            `Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta,
            `Miri.Interpreter.ptrOffsetInbounds,
            `Miri.Memory.Allocation.copy,
            `Miri.Memory.InitMask.prepareCopy,
            `LeanMiriSpec.WideDstAndMaybeUninitLM.lmWdObserve,
            `LeanMiriSpec.WideDstAndMaybeUninitLM.ep1_lean_miri_widedst_maybeuninit_capstone,
            `LeanMiriSpec.WideDstAndMaybeUninitLM.ep1_lean_miri_universal_laws_capstone,
            `LeanMiriSpec.WideDstAndMaybeUninitLM.ep1_lean_miri_step_driver_capstone ]) ]
    let mut reachChecked : Nat := 0
    for (root, rs) in reqs do
      let seen := reachFrom root
      for r in rs do
        unless env.contains r do throwError "cross-root reachability: {r} is not a constant"
        unless seen.contains r do
          throwError "cross-root reachability failure: {root} does not reach {r}"
        reachChecked := reachChecked + 1
    return (added.size, bundleCount, lockCount, rejected, twins, crAxioms.toArray)

  let ctx : Core.Context :=
    { fileName := "<wd-cross-root>", fileMap := default, options := opts, maxHeartbeats := 0 }
  let ((addedCount, bundleCount, lockCount, rejectedCount, twinCount, crAxioms), _) ←
    liftCoreM <| act.toIO ctx { env := baseEnv }
  unless addedCount ≥ 60 && bundleCount = 5 && lockCount = 26 && rejectedCount ≥ 10 &&
      twinCount ≥ 8 do
    throwError "cross-root: unexpected counts (added={addedCount}, bundles={bundleCount}, locks={lockCount}, rejected={rejectedCount}, twins={twinCount})"
  logInfo m!"wd cross-root kernel bridge: added {addedCount} declarations ({bundleCount} bundles, {lockCount} fixture locks), rejected {rejectedCount} forged controls ({twinCount} honest twins accepted), reached Trusted+MiniRust+Miri, axioms {crAxioms}"

/-! ## §3. Constructive Purity, Axiom Audit, and Auditor Self-Tests -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let bNs := `Anneal.Mir.WideDstAndMaybeUninitDualSpec
  let constructiveDecls : List Name :=
    [ `wdCodec, `wdEncode_decode_of_valid, `wdCodec_tight, `wdCodec_encode_injective,
      `wdCodec_decode_injective_on_valid, `wdCodec_rejects_malformed, `lmTableCheckOf_sound,
      `lmTableCheckOf_of_eq, `mrSide_check, `lmCheckOf_of_table, `bundleOf, `domainBundleOf,
      `threeWayNormalAgreement, `crossAuthorityFaultEquiv, `exactBehaviorEq_both,
      `projectPositive, `projectFault, `modeSensitivity_present, `domain_bundle_claims,
      `dual_exact_three_way_classification, `dual_fail_closed_out_of_range,
      `dual_mode_sensitivity_exact, `dual_dst_honest_trusted_boundary,
      `dual_minirust300_pin_delta_and_flip_ready, `dual_case13_union_copy_vs_typed_read,
      `rootBackedLmAuthority_tableCheck ]
  let isChoiceFree (axs : Array Name) : Bool :=
    axs.all fun a => a == ``propext || a == ``Quot.sound
  for d in constructiveDecls do
    let axs ← liftCoreM <| Lean.collectAxioms (bNs ++ d)
    unless isChoiceFree axs do
      throwError "constructive audit failure: {d} uses a non-constructive axiom ({axs})"
  -- Self-tests: the constructive check rejects `Classical.choice`; the axiom audit rejects
  -- `sorryAx` and `Lean.ofReduceBool`.
  unless !isChoiceFree (← liftCoreM <| Lean.collectAxioms ``Classical.em) do
    throwError "self-test: Classical.choice was not detected"
  unless !(← liftCoreM <| Lean.collectAxioms ``sorryAx).all
      (fun a => a == ``propext || a == ``Quot.sound || a == ``Classical.choice) do
    throwError "self-test: sorryAx was not detected"
  unless !(← liftCoreM <| Lean.collectAxioms ``Lean.ofReduceBool).all
      (fun a => a == ``propext || a == ``Quot.sound || a == ``Classical.choice) do
    throwError "self-test: Lean.ofReduceBool was not detected"
  let tNs := `Anneal.Mir.WideDstAndMaybeUninitCorrespondenceTests
  let mut checked : Nat := 0
  for (c, _) in env.constants.map₂.toList do
    for a in ← liftCoreM <| Lean.collectAxioms c do
      if a == ``sorryAx then throwError "test audit failure: {c} uses sorryAx"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "test audit failure: {c} uses non-standard axiom {a}"
    if tNs.isPrefixOf c then checked := checked + 1
  unless checked ≥ 9 do
    throwError "test audit vacuous: only {checked} test declarations"
  logInfo m!"wd constructive audit: {constructiveDecls.length} Episode 2 declarations in [propext, Quot.sound]; {checked} test declarations standard-axiom clean"

end Anneal.Mir.WideDstAndMaybeUninitCorrespondenceTests
