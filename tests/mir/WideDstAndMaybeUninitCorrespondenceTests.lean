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
    trustedVerdict false 2 = some (.returns (.sizeAlign 0 1)) ∧
    mrVerdict false 2 = some (.returns (.sizeAlign 0 1)) ∧
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
    trustedVerdict false 10 = some (.returns (.scalar 305419896)) ∧
    mrVerdict false 10 = some (.returns (.scalar 305419896)) ∧
    trustedVerdict false 11 = some (.returns (.scalar 77)) ∧
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
    trustedVerdict true 15 = some (.returns (.scalar 200)) ∧
    mrVerdict true 15 = some (.returns (.scalar 200)) ∧
    trustedVerdict false 16 = some .undefinedBehavior ∧ mrVerdict false 16 = some .undefinedBehavior ∧
    trustedVerdict true 17 = some .undefinedBehavior ∧
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
    mrVerdict false 22 = some (.returns (.fnPtr 0)) ∧
    mrVerdict true 22 = some (.returns (.fnPtr 0)) ∧
    trustedVerdict false 23 = some (.returns (.fnPtr 0)) ∧
    trustedVerdict true 23 = some (.returns (.fnPtr 0)) ∧
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

/-- Concrete §1 witnesses for Case `2` two-query anti-masking (`wdCase2Mir` + `wdCase2StrMir`) and
exact `Stop.machineStop` termination of pinned MiniRust on `mrWdProg21`/`22`/`23` vs `false` on
OOB UB `mrWdProg16`. -/
theorem d1_case2_halves_and_d4_machine_delta_canary :
    type_of% dual_case2_two_query_halves_agree ∧
    type_of% dual_minirust300_machine_level_pin_delta :=
  ⟨dual_case2_two_query_halves_agree, dual_minirust300_machine_level_pin_delta⟩

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
  let act : CoreM (Nat × Nat × Nat × Nat × Nat × Nat × Array Name) := do
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
                    `bundle_gate_pinDelta_and_dstBoundary, `unified_bundle_witness_kinds,
                    `dual_exact_three_way_classification, `dual_no_specPanic_all_cells,
                    `dual_mode_sensitivity_exact, `dual_case19_mode_sensitivity,
                    `dual_dst_honest_trusted_boundary,
                    `dual_minirust300_pin_delta_and_flip_ready,
                    `dual_case13_union_copy_vs_typed_read] do
      addThmInfer (ns ++ thmName) (mkApp2 (mkConst (bNs ++ thmName)) authC hA)
      added := added.push (ns ++ thmName)
    addThmInfer (ns ++ `dual_fail_closed_out_of_range)
      (mkApp2 (mkConst (bNs ++ `dual_fail_closed_out_of_range)) authC hOob)
    added := added.push (ns ++ `dual_fail_closed_out_of_range)
    -- 3-way Case 13 union-copy vs typed-read contrast (Trusted + MiniRust + LeanMiri).
    let c13Name := ns ++ `dual_case13_three_way_copy_contrast
    let c13Pf ← MetaM.run' <| mkAppM ``And.intro
      #[mkConst (ns ++ `dual_case13_union_copy_vs_typed_read),
        mkConst (lmNs ++ `lm_case13_union_copy_of_invalid_bool_byte_ok)]
    addThmInfer c13Name c13Pf
    added := added.push c13Name
    let capName := ns ++ `ep2_widedst_maybeuninit_dual_authority_capstone
    addThmInfer capName
      (mkApp3 (mkConst (bNs ++ `ep2_widedst_maybeuninit_dual_authority_capstone)) authC hA hOob)
    added := added.push capName

    -- 3b. Translation fidelity (anti-mock): `lmWdToVerdict` is EXACTLY the root translation
    -- `wdVerdictOf` after a constructor-for-constructor bijection `LmWdObs ≃ MrWdObs`; and the frozen
    -- LeanMiri table transcribed in the root (`wdLmExpected*`) IS LeanMiri's own `lmWdExpected*`.
    let mrObsTy0 := mkConst (mrNs ++ `MrWdObs)
    let ctorNames : List Name :=
      [`okScalar, `okSizeAlign, `okUninitPreserved, `okFnPtr, `ub, `unsupported, `specPanic]
    let mkCtorMap (srcInd dstInd : Name) : MetaM Expr := do
      let srcTy := mkConst srcInd
      withLocalDeclD `o srcTy fun o => do
        let motive := mkLambda `x .default srcTy (mkConst dstInd)
        let mut minors : Array Expr := #[]
        for c in ctorNames do
          let cTy ← inferType (mkConst (srcInd ++ c))
          minors := minors.push (← forallTelescope cTy fun xs _ =>
            mkLambdaFVars xs (mkAppN (mkConst (dstInd ++ c)) xs))
        mkLambdaFVars #[o] (mkAppN (mkConst (srcInd ++ `rec) [1]) (#[motive] ++ minors ++ #[o]))
    let mkPointwise (ind : Name) (resTy : Expr) (lhs rhs : Expr → Expr) : MetaM (Expr × Expr) := do
      withLocalDeclD `o (mkConst ind) fun o => do
        let motive ← mkLambdaFVars #[o] (mkEq resTy (lhs o) (rhs o))
        let mut minors : Array Expr := #[]
        for c in ctorNames do
          let cTy ← inferType (mkConst (ind ++ c))
          minors := minors.push (← forallTelescope cTy fun xs _ =>
            mkLambdaFVars xs (mkRefl resTy (lhs (mkAppN (mkConst (ind ++ c)) xs))))
        let pf ← mkLambdaFVars #[o] (mkAppN (mkConst (ind ++ `rec) [0]) (#[motive] ++ minors ++ #[o]))
        let ty ← mkForallFVars #[o] (mkEq resTy (lhs o) (rhs o))
        return (ty, pf)
    let lmToMrName := ns ++ `lmToMr
    let _ ← addDef lmToMrName (← MetaM.run' <| mkCtorMap (lmNs ++ `LmWdObs) (mrNs ++ `MrWdObs))
    let mrToLmName := ns ++ `mrToLm
    let _ ← addDef mrToLmName (← MetaM.run' <| mkCtorMap (mrNs ++ `MrWdObs) (lmNs ++ `LmWdObs))
    added := added.push lmToMrName |>.push mrToLmName
    let lmToMr := mkConst lmToMrName
    let mrToLm := mkConst mrToLmName
    let fidelity : List (Name × Name × Expr × (Expr → Expr) × (Expr → Expr)) :=
      [ (`translation_fidelity, lmNs ++ `LmWdObs, optVerdTy,
          fun o => mkApp toV o, fun o => mkApp (mkConst (bNs ++ `wdVerdictOf)) (mkApp lmToMr o)),
        (`lmToMr_mrToLm, mrNs ++ `MrWdObs, mrObsTy0,
          fun o => mkApp lmToMr (mkApp mrToLm o), fun o => o),
        (`mrToLm_lmToMr, lmNs ++ `LmWdObs, lmObsTy,
          fun o => mkApp mrToLm (mkApp lmToMr o), fun o => o) ]
    for (tag, ind, resTy, lhs, rhs) in fidelity do
      let (ty, pf) ← MetaM.run' <| mkPointwise ind resTy lhs rhs
      addThm (ns ++ tag) ty pf
      added := added.push (ns ++ tag)
    let listMrTy := mkApp (mkConst ``List [0]) mrObsTy0
    for (rootTbl, lmTbl) in [(`wdLmExpectedBasic, `lmWdExpectedBasic), (`wdLmExpectedTb, `lmWdExpectedTb)] do
      let lhs := mkConst (bNs ++ rootTbl)
      let rhs := mkApp4 (mkConst ``List.map [0, 0]) lmObsTy mrObsTy0 lmToMr (mkConst (lmNs ++ lmTbl))
      let n := ns ++ `frozenTableLock ++ rootTbl
      addThm n (mkEq listMrTy lhs rhs) (mkRefl listMrTy lhs)
      added := added.push n
    -- 3c. Direct-certificate bundles: EVERY side certificate kernel-evaluated on the twin (`unified`
    -- and all 4 per-domain `d1..d4`) is transported onto the real authority via `cert_transport`,
    -- and every direct bundle it closes is definitionally equal (`Eq.refl`) to the table-closed one.
    let directBundle := ns ++ `directUnifiedBundle
    for (tag, sel) in sels do
      let directChk := ns ++ `lmSideCheck_direct ++ tag
      let pFn ← MetaM.run' <| withLocalDeclD `a (mkConst (bNs ++ `WdLmAuthority)) fun a =>
        mkLambdaFVars #[a] (mkApp2 (mkConst (bNs ++ `lmCheckOf)) sel a)
      addThm directChk (eqTrue (mkApp2 (mkConst (bNs ++ `lmCheckOf)) sel authC))
        (mkAppN (mkConst (bNs ++ `cert_transport))
          #[authC, authUC, mkConst eqName, pFn, mkConst (ns ++ `lmSideCheckU ++ tag)])
      added := added.push directChk
      let dName := if tag == `unified then directBundle else ns ++ `directDomainBundle ++ tag
      let origName := if tag == `unified then unifiedName else ns ++ `domainBundle ++ tag
      let dTy ← addDef dName (mkApp3 (mkConst (bNs ++ `bundleOfSel)) sel authC (mkConst directChk))
      added := added.push dName
      let eqBName := ns ++ `directBundle_eq ++ tag
      addThm eqBName (mkEq dTy (mkConst dName) (mkConst origName)) (mkRefl dTy (mkConst dName))
      added := added.push eqBName

    -- 3d. Case 2 two-query anti-masking on LeanMiri (each `wdCombine` half pinned separately), and
    -- 3-engine UB root-cause alignment: exact MiniRust stop messages, exact vendored LeanMiri
    -- failure classes, the machine-level `#300` pin delta, and the Trusted root-cause lemmas.
    let lmRunC := mkConst (lmNs ++ `lmWdRun)
    let lmSA (ty lay : Name) (n : Nat) : Expr :=
      mkApp lmRunC (mkApp3 (mkConst (lmNs ++ `lmWdSizeAlign)) (mkConst (lmNs ++ ty)) (mkConst (lmNs ++ lay)) (mkNatLit n))
    let lmSA01 := mkApp2 (mkConst (lmNs ++ `LmWdObs.okSizeAlign)) (mkNatLit 0) (mkNatLit 1)
    for (tag, e) in [(`zstSliceHalf, lmSA `lmWdTySliceUnit `lmWdSliceUnitLay 5),
                     (`emptyStrHalf, lmSA `lmWdTyStr `lmWdStrLay 0)] do
      let n := ns ++ `lmCase2 ++ tag
      addThm n (mkEq lmObsTy e lmSA01) (mkRefl lmObsTy e)
      added := added.push n
    let rcName := ns ++ `ub_root_cause_alignment_three_engines
    let rcPf ← MetaM.run' do
      let parts : List Expr :=
        [ mkConst (mrNs ++ `mr_wd_exact_ub_diagnostics),
          mkConst (lmNs ++ `lm_wd_exact_ub_diagnostics),
          mkConst (bNs ++ `dual_minirust300_machine_level_pin_delta),
          mkConst (bNs ++ `dual_case2_two_query_halves_agree),
          mkConst (mrNs ++ `trusted_decodeTypedValueFromBytes_null_witness),
          mkConst (mrNs ++ `trusted_intrinsicWidePointeeStep_dst_unsupported),
          mkConst (ns ++ `lmCase2 ++ `zstSliceHalf),
          mkConst (ns ++ `lmCase2 ++ `emptyStrHalf) ]
      let rec conjRc : List Expr → MetaM Expr
        | [] => return mkConst ``True.intro
        | [p] => return p
        | p :: ps => do mkAppM ``And.intro #[p, ← conjRc ps]
      conjRc parts
    addThmInfer rcName rcPf
    added := added.push rcName

    -- 4. Definitional `Eq.refl` fixture locks over EVERY shared definition in `section Fixtures`
    -- (38 items: layouts, builders, and all 25 `CapturedMir` fixtures) plus
    -- `mrWdCaseCount = lmWdCaseCount` (39 locks total).
    let fixtureNames : List Name :=
      [ `wdU8Layout, `wdU32Layout, `wdUnitLayout, `wdMaybeUninitU32Layout, `wdBoolLayout,
        `wdMaybeUninitBoolLayout, `wdManuallyDropU32Layout, `wdLayouts,
        `wdFnAbi, `wdBody, `wdSizeAlignMir, `wdUnionCopyMir, `wdUnionReadMir,
        `wdCase0Mir, `wdCase1Mir, `wdCase2Mir, `wdCase2StrMir, `wdCase3Mir, `wdCase4Mir,
        `wdCase5Mir, `wdCase6Mir, `wdCase7Mir, `wdCase8Mir, `wdCase9Mir, `wdCase10Mir,
        `wdCase11Mir, `wdCase12Mir, `wdCase13Mir, `wdCase13CopyMir, `wdCase14Mir, `wdCase15Mir,
        `wdCase16Mir, `wdCase17Mir, `wdCase18Mir, `wdCase19Mir, `wdCase20Mir, `wdCase21Mir,
        `wdCase23Mir ]
    let mut lockCount : Nat := 0
    let mut lockNames : Array Name := #[]
    for tag in fixtureNames do
      let lhs := mkConst (mrNs ++ tag)
      let rhs := mkConst (lmNs ++ tag)
      let ty ← MetaM.run' <| inferType lhs
      let lockName := ns ++ `fixtureLock ++ tag
      addThm lockName (mkEq ty lhs rhs) (mkRefl ty lhs)
      added := added.push lockName
      lockNames := lockNames.push lockName
      lockCount := lockCount + 1
    let countLockName := ns ++ `fixtureLock ++ `caseCount
    addThm countLockName (mkEq natTy (mkConst (mrNs ++ `mrWdCaseCount)) (mkConst (lmNs ++ `lmWdCaseCount)))
      (mkRefl natTy (mkConst (mrNs ++ `mrWdCaseCount)))
    added := added.push countLockName
    lockNames := lockNames.push countLockName
    lockCount := lockCount + 1
    unless lockCount = 39 do
      throwError "cross-root: expected 39 fixture locks, got {lockCount}"

    -- 4b. Unified cross-root 3-engine capstone: conjoins the closed Episode 2 capstone, Case 13
    -- 3-way copy contrast, anti-mock translation fidelity & bijection, frozen-table locks, all 5
    -- direct-certificate bundle equalities, 3-engine UB root-cause alignment, all 39 `Eq.refl`
    -- fixture locks, and the Episode 1 LeanMiri capstones into one single root theorem.
    -- Observer-level 3-way agreement over the RAW `lmWdObserve` (via `lmToMr` + fidelity).
    let olName := ns ++ `observer_level_three_way
    addThmInfer olName (mkApp4 (mkConst (bNs ++ `observer_level_three_way)) authC hA lmToMr
      (mkConst (ns ++ `translation_fidelity)))
    added := added.push olName
    let crossName := ns ++ `ep2_cross_root_three_engine_capstone
    let crossPf ← MetaM.run' do
      let parts : List Expr :=
        [ mkConst capName,
          mkConst c13Name,
          mkConst (ns ++ `translation_fidelity),
          mkConst olName,
          mkConst (ns ++ `lmToMr_mrToLm),
          mkConst (ns ++ `mrToLm_lmToMr),
          mkConst (ns ++ `frozenTableLock ++ `wdLmExpectedBasic),
          mkConst (ns ++ `frozenTableLock ++ `wdLmExpectedTb),
          mkConst (ns ++ `directBundle_eq ++ `unified),
          mkConst (ns ++ `directBundle_eq ++ `d1),
          mkConst (ns ++ `directBundle_eq ++ `d2),
          mkConst (ns ++ `directBundle_eq ++ `d3),
          mkConst (ns ++ `directBundle_eq ++ `d4),
          mkConst rcName,
          mkConst (lmNs ++ `ep1_lean_miri_widedst_maybeuninit_capstone),
          mkConst (lmNs ++ `ep1_lean_miri_universal_laws_capstone),
          mkConst (lmNs ++ `ep1_lean_miri_step_driver_capstone),
          mkConst (lmNs ++ `lmWdObserve_table),
          mkConst (lmNs ++ `lmWdObserve_mode_sensitivity),
          mkConst (lmNs ++ `lm_wd_exact_ub_diagnostics) ] ++
        (lockNames.toList.map mkConst)
      let rec conj : List Expr → MetaM Expr
        | [] => return mkConst ``True.intro
        | [p] => return p
        | p :: ps => do mkAppM ``And.intro #[p, ← conj ps]
      conj parts
    addThmInfer crossName crossPf
    added := added.push crossName

    -- 5. Negative forgery controls on scratch environment copies: EVERY forged declaration MUST be
    -- rejected by the kernel AND paired with an accepted honest twin (100% paired: `twins = rejected`),
    -- proving rejections are caused by the forged content, never by an accidental type/name typo.
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
    let noneObs := mkApp (mkConst ``Option.none [0]) obsTy
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
    let trVerd (tb : Bool) (i : Nat) : Expr :=
      mkApp2 (mkConst (bNs ++ `trustedVerdict)) (toExpr tb) (mkNatLit i)
    let capMirTy ← MetaM.run' <| inferType (mkConst (mrNs ++ `wdCase0Mir))
    let defD (n : Name) (ty val : Expr) : Declaration :=
      .defnDecl { name := n, levelParams := [], type := ty, value := val,
                  hints := .regular 0, safety := .safe }
    let wdBundleTy := mkConst (bNs ++ `WdBundle)
    -- Predicate-level `#300` controls: the pinned `checkPtr` and post-`#300` `checkPtrFnNonNull` on
    -- the null `fn()` pointer, with terms taken from the Episode 1 theorem statements.
    let (cpTy, cpL, cpR, nnL, nnR) ← MetaM.run' do
      let thTy ← inferType (mkConst (mrNs ++ `mr_checkPtr_null_fnptr_ok))
      let dom := thTy.bindingDomain!
      let t1 ← instantiateForall thTy #[mkApp (mkConst ``Option.none [0]) dom.appArg!]
      let some (ity, l1, r1) := t1.eq? | throwError "cross-root: unexpected checkPtr theorem shape"
      let canTy ← inferType (mkConst (mrNs ++ `mr_minirust300_flip_canary))
      let some (_, rest) := canTy.and? | throwError "cross-root: unexpected canary shape"
      let some (b, _) := rest.and? | throwError "cross-root: unexpected canary shape"
      let some (_, l2, r2) := b.eq? | throwError "cross-root: unexpected canary shape"
      return (ity, l1, r1, l2, r2)
    -- Gate-boundary forgery helpers:
    -- (a) MiniRust side with `lmGate` (admitting case `22`, where pinned MiniRust diverges);
    -- (b) LeanMiri side with an always-true gate (admitting cases `6, 7`, where Trusted is `.unsupported`).
    let noneSel := mkApp (mkConst ``Option.none [0]) (mkConst domNs)
    let some (.defnInfo lmChkInfo) := (← getEnv).find? (bNs ++ `lmCheckOf)
      | throwError "cross-root: lmCheckOf definition missing"
    let checkOnWdModel := lmChkInfo.value.bindingBody!.bindingBody!.appFn!
    let mrSideWithCase22 := mkApp3 (mkConst (bNs ++ `sideOf))
      noneSel (mkConst (bNs ++ `lmGate)) (mkConst (bNs ++ `mrVerdictFn))
    let mrSideWithCase22Check := mkApp checkOnWdModel mrSideWithCase22
    let allTrueGate ← MetaM.run' <|
      withLocalDeclD `sel (mkApp (mkConst ``Option [0]) (mkConst domNs)) fun sel =>
        withLocalDeclD `i (mkConst (bNs ++ `WdCase)) fun i =>
          mkLambdaFVars #[sel, i] (mkConst ``Bool.true)
    let lmSideWithCase6 := mkApp3 (mkConst (bNs ++ `sideOf))
      noneSel allTrueGate (mkApp (mkConst (bNs ++ `lmVerdictFn)) authUC)
    let lmSideWithCase6Check := mkApp checkOnWdModel lmSideWithCase6
    let lmMapBasic := mkApp4 (mkConst ``List.map [0, 0]) lmObsTy mrObsTy0 lmToMr (mkConst (lmNs ++ `lmWdExpectedBasic))
    let lmMapTb := mkApp4 (mkConst ``List.map [0, 0]) lmObsTy mrObsTy0 lmToMr (mkConst (lmNs ++ `lmWdExpectedTb))
    let optStrTy := mkApp (mkConst ``Option [0]) (mkConst ``String)
    let stopMsgB (i : Nat) : Expr :=
      mkApp2 (mkConst `MiniRustSpec.CrossFrameRefAndPanicMR.runStopMsgBasic)
        (mkConst (mrNs ++ (Name.mkSimple s!"mrWdProg{i}"))) (mkNatLit 120)
    let termClean (tb : Bool) (i : Nat) : Expr :=
      mkApp3 (mkConst (bNs ++ `mrTerminatesCleanly))
        (toExpr tb) (mkConst (mrNs ++ (Name.mkSimple s!"mrWdProg{i}"))) (mkNatLit 120)
    let forged : List (String × Declaration × Declaration) :=
      [ ("ill-typed 0 = 1",
          thmD (ns ++ `forged.zeroEqOne) (mkEq natTy (mkNatLit 0) (mkNatLit 1)) (mkRefl natTy (mkNatLit 0)),
          thmD (ns ++ `honest.zeroEqZero) (mkEq natTy (mkNatLit 0) (mkNatLit 0)) (mkRefl natTy (mkNatLit 0))),
        ("negated LM 48-cell certificate",
          thmD (ns ++ `forged.lmTableFalse) (eqFalse (tblCheck authUC)) reflFalse,
          thmD (ns ++ `honest.lmTableTrue) (eqTrue (tblCheck authUC)) reflTrue),
        ("mode-inverted LM authority (Bool.not tb) certificate",
          thmD (ns ++ `forged.modeInverted) (eqTrue (tblCheck invAuth)) reflTrue,
          thmD (ns ++ `honest.modeInvertedFalse) (eqFalse (tblCheck invAuth)) reflFalse),
        ("ub/unsupported-swapped LM translation certificate",
          thmD (ns ++ `forged.swappedTranslation) (eqTrue (tblCheck swapAuth)) reflTrue,
          thmD (ns ++ `honest.swappedTranslationFalse) (eqFalse (tblCheck swapAuth)) reflFalse),
        ("forged DualCorrespondenceBundle from mode-inverted LM authority",
          defD (ns ++ `forged.bundleModeInverted) wdBundleTy
            (mkApp2 (mkConst (bNs ++ `bundleOf)) invAuth reflTrue),
          defD (ns ++ `honest.bundleFromUnrolled) wdBundleTy
            (mkApp2 (mkConst (bNs ++ `bundleOf)) authUC (mkConst tblUName))),
        ("swapped fixture lock (wdCase0Mir = wdCase5Mir)",
          thmD (ns ++ `forged.swappedFixture)
            (mkEq capMirTy (mkConst (mrNs ++ `wdCase0Mir)) (mkConst (lmNs ++ `wdCase5Mir)))
            (mkRefl capMirTy (mkConst (mrNs ++ `wdCase0Mir))),
          thmD (ns ++ `honest.fixture5)
            (mkEq capMirTy (mkConst (mrNs ++ `wdCase5Mir)) (mkConst (lmNs ++ `wdCase5Mir)))
            (mkRefl capMirTy (mkConst (mrNs ++ `wdCase5Mir)))),
        ("forged codec decode of non-zero padding (0,5,1)",
          thmD (ns ++ `forged.decodePadding) (mkEq optObsTy (decode t051) (someObs (scalarObs 5)))
            (mkRefl optObsTy (decode t051)),
          thmD (ns ++ `honest.decodeCanonical) (mkEq optObsTy (decode t050) (someObs (scalarObs 5)))
            (mkRefl optObsTy (decode t050))),
        ("forged codec decode of invalid wire tag 4",
          thmD (ns ++ `forged.decodeTag4) (mkEq optObsTy (decode t400) (someObs (scalarObs 0)))
            (mkRefl optObsTy (decode t400)),
          thmD (ns ++ `honest.decodeTag4None) (mkEq optObsTy (decode t400) noneObs)
            (mkRefl optObsTy (decode t400))),
        ("forged colliding codec encodings (scalar 0 = fnPtr 0)",
          thmD (ns ++ `forged.encodeCollision) (mkEq repTy (encode (scalarObs 0)) (encode (fnObs 0)))
            (mkRefl repTy (encode (scalarObs 0))),
          thmD (ns ++ `honest.encodeFnPtr) (mkEq repTy (encode (fnObs 0)) t300)
            (mkRefl repTy (encode (fnObs 0)))),
        ("forged case 22: pinned d821c6e3 MiniRust rejects null FnPtr",
          thmD (ns ++ `forged.case22MrUb) (mkEq mrObsTy (mrObs false 22) (mrC `ub)) (mkRefl mrObsTy (mrObs false 22)),
          thmD (ns ++ `honest.case22MrOk) (mkEq mrObsTy (mrObs false 22) (mrFn 0)) (mkRefl mrObsTy (mrObs false 22))),
        ("forged case 22: LeanMiri follows the pinned MiniRust null FnPtr acceptance",
          thmD (ns ++ `forged.case22LmOk) (mkEq lmObsTy (lmObsU false 22) (lmFn 0)) (mkRefl lmObsTy (lmObsU false 22)),
          thmD (ns ++ `honest.case22LmUb) (mkEq lmObsTy (lmObsU false 22) (lmObsC `ub)) (mkRefl lmObsTy (lmObsU false 22))),
        ("forged case 22: Trusted accepts null FnPtr",
          thmD (ns ++ `forged.case22TrustedOk) (mkEq mrObsTy (trObs false 22) (mrFn 0)) (mkRefl mrObsTy (trObs false 22)),
          thmD (ns ++ `honest.case22TrustedUb) (mkEq mrObsTy (trObs false 22) (mrC `ub)) (mkRefl mrObsTy (trObs false 22))),
        ("forged case 21: post-#300 checkPtrFnNonNull accepts null FnPtr",
          thmD (ns ++ `forged.case21MrOk) (mkEq mrObsTy (mrObs true 21) (mrFn 0)) (mkRefl mrObsTy (mrObs true 21)),
          thmD (ns ++ `honest.case21MrUb) (mkEq mrObsTy (mrObs true 21) (mrC `ub)) (mkRefl mrObsTy (mrObs true 21))),
        ("forged case 6: unmodified Trusted computes okSizeAlign 16 4",
          thmD (ns ++ `forged.case6TrustedOk)
            (mkEq mrObsTy (trObs false 6) (mkApp2 (mrC `okSizeAlign) (mkNatLit 16) (mkNatLit 4)))
            (mkRefl mrObsTy (trObs false 6)),
          thmD (ns ++ `honest.case6TrustedUnsupported) (mkEq mrObsTy (trObs false 6) (mrC `unsupported))
            (mkRefl mrObsTy (trObs false 6))),
        ("forged case 7: unmodified Trusted computes okSizeAlign 16 8",
          thmD (ns ++ `forged.case7TrustedOk)
            (mkEq mrObsTy (trObs true 7) (mkApp2 (mrC `okSizeAlign) (mkNatLit 16) (mkNatLit 8)))
            (mkRefl mrObsTy (trObs true 7)),
          thmD (ns ++ `honest.case7TrustedUnsupported) (mkEq mrObsTy (trObs true 7) (mrC `unsupported))
            (mkRefl mrObsTy (trObs true 7))),
        ("forged case 19 mode invariance (Trusted basic = treeBorrows)",
          thmD (ns ++ `forged.case19TrInvariant) (mkEq mrObsTy (trObs false 19) (trObs true 19))
            (mkRefl mrObsTy (trObs false 19)),
          thmD (ns ++ `honest.case19TrTbUb) (mkEq mrObsTy (trObs true 19) (mrC `ub)) (mkRefl mrObsTy (trObs true 19))),
        ("forged case 19 mode invariance (MiniRust basic = treeBorrows)",
          thmD (ns ++ `forged.case19MrInvariant) (mkEq mrObsTy (mrObs false 19) (mrObs true 19))
            (mkRefl mrObsTy (mrObs false 19)),
          thmD (ns ++ `honest.case19MrTbUb) (mkEq mrObsTy (mrObs true 19) (mrC `ub)) (mkRefl mrObsTy (mrObs true 19))),
        ("forged case 19 mode invariance (LeanMiri basic = treeBorrows)",
          thmD (ns ++ `forged.case19LmInvariant) (mkEq lmObsTy (lmObsU false 19) (lmObsU true 19))
            (mkRefl lmObsTy (lmObsU false 19)),
          thmD (ns ++ `honest.case19LmTbUb) (mkEq lmObsTy (lmObsU true 19) (lmObsC `ub)) (mkRefl lmObsTy (lmObsU true 19))),
        ("forged case 12: Trusted accepts the uninit MaybeUninit<u32> typed read",
          thmD (ns ++ `forged.case12TrAccepts) (eqTrue (isRet (trVerd false 12))) reflTrue,
          thmD (ns ++ `honest.case12TrFaults) (eqTrue (isFault (trVerd false 12))) reflTrue),
        ("forged case 12: LeanMiri accepts the uninit MaybeUninit<u32> typed read",
          thmD (ns ++ `forged.case12LmAccepts) (eqTrue (isRet (lmVerd authUC false 12))) reflTrue,
          thmD (ns ++ `honest.case12LmFaults) (eqTrue (isFault (lmVerd authUC false 12))) reflTrue),
        ("forged case 12: MiniRust accepts the uninit MaybeUninit<u32> typed read",
          thmD (ns ++ `forged.case12MrAccepts) (eqTrue (isRet (mrVerd true 12))) reflTrue,
          thmD (ns ++ `honest.case12MrFaults) (eqTrue (isFault (mrVerd true 12))) reflTrue),
        ("forged case 13: MiniRust typed bool read succeeds like union copy",
          thmD (ns ++ `forged.case13MrOk)
            (mkEq mrObsTy (mrObs false 13) (mkApp2 (mrC `okUninitPreserved) (mkNatLit 1) (mkNatLit 1)))
            (mkRefl mrObsTy (mrObs false 13)),
          thmD (ns ++ `honest.case13MrUb) (mkEq mrObsTy (mrObs false 13) (mrC `ub)) (mkRefl mrObsTy (mrObs false 13))),
        ("forged case 13: LeanMiri typed bool read succeeds like union copy",
          thmD (ns ++ `forged.case13LmOk)
            (mkEq lmObsTy (lmObsU false 13) (mkApp2 (lmObsC `okUninitPreserved) (mkNatLit 1) (mkNatLit 1)))
            (mkRefl lmObsTy (lmObsU false 13)),
          thmD (ns ++ `honest.case13LmUb) (mkEq lmObsTy (lmObsU false 13) (lmObsC `ub)) (mkRefl lmObsTy (lmObsU false 13))),
        ("forged LeanMiri case 2 ZST-slice half: size_of_val [(); 5] = 5",
          thmD (ns ++ `forged.lmCase2ZstSize5) (mkEq lmObsTy (lmSA `lmWdTySliceUnit `lmWdSliceUnitLay 5)
              (mkApp2 (mkConst (lmNs ++ `LmWdObs.okSizeAlign)) (mkNatLit 5) (mkNatLit 1)))
            (mkRefl lmObsTy (lmSA `lmWdTySliceUnit `lmWdSliceUnitLay 5)),
          thmD (ns ++ `honest.lmCase2ZstSize0) (mkEq lmObsTy (lmSA `lmWdTySliceUnit `lmWdSliceUnitLay 5) lmSA01)
            (mkRefl lmObsTy (lmSA `lmWdTySliceUnit `lmWdSliceUnitLay 5))),
        ("forged machine-level pin delta: pinned MiniRust machine stops on the null fn() transmute",
          thmD (ns ++ `forged.machineStopsOnNullFnPtr)
            (mkEq optStrTy (stopMsgB 22) (mkApp2 (mkConst ``Option.some [0]) (mkConst ``String)
              (mkStrLit "Value::Ptr: null function pointer")))
            (mkRefl optStrTy (stopMsgB 22)),
          thmD (ns ++ `honest.machineRunsNullFnPtr) (mkEq optStrTy (stopMsgB 22)
              (mkApp (mkConst ``Option.none [0]) (mkConst ``String)))
            (mkRefl optStrTy (stopMsgB 22))),
        ("forged machine-level pin delta: pinned MiniRust MachTB fails to reach Stop.machineStop on case 22",
          thmD (ns ++ `forged.machineNoCleanStopNullFnPtr) (eqFalse (termClean true 22)) reflFalse,
          thmD (ns ++ `honest.machineCleanStopNullFnPtr) (eqTrue (termClean true 22)) reflTrue),
        ("forged clean termination on OOB UB case 16 (Stop.ub must not pass mrTerminatesCleanly)",
          thmD (ns ++ `forged.machineCleanStopOob16) (eqTrue (termClean false 16)) reflTrue,
          thmD (ns ++ `honest.machineNoCleanStopOob16) (eqFalse (termClean false 16)) reflFalse),
        ("forged observer-level agreement at the pin-delta cell (LeanMiri = pinned MiniRust on 22)",
          thmD (ns ++ `forged.observerLevelPinDelta)
            (mkEq mrObsTy0 (mkApp lmToMr (lmObsU false 22)) (mrObs false 22))
            (mkRefl mrObsTy0 (mkApp lmToMr (lmObsU false 22))),
          thmD (ns ++ `honest.observerLevelPinDeltaTrusted)
            (mkEq mrObsTy0 (mkApp lmToMr (lmObsU false 22)) (trObs false 22))
            (mkRefl mrObsTy0 (mkApp lmToMr (lmObsU false 22)))),
        ("forged observer-level agreement at a DST cell (LeanMiri = Trusted on 6)",
          thmD (ns ++ `forged.observerLevelDst)
            (mkEq mrObsTy0 (mkApp lmToMr (lmObsU true 6)) (trObs true 6))
            (mkRefl mrObsTy0 (mkApp lmToMr (lmObsU true 6))),
          thmD (ns ++ `honest.observerLevelDstMr)
            (mkEq mrObsTy0 (mkApp lmToMr (lmObsU true 6)) (mrObs true 6))
            (mkRefl mrObsTy0 (mkApp lmToMr (lmObsU true 6)))),
        ("forged pin delta: pinned d821c6e3 checkPtr rejects the null FnPtr",
          thmD (ns ++ `forged.pinnedCheckPtrRejectsNull) (mkEq cpTy cpL nnR) (mkRefl cpTy cpL),
          thmD (ns ++ `honest.pinnedCheckPtrAcceptsNull) (mkEq cpTy cpL cpR) (mkRefl cpTy cpL)),
        ("forged #300: checkPtrFnNonNull accepts the null FnPtr",
          thmD (ns ++ `forged.nonNullCheckAcceptsNull) (mkEq cpTy nnL cpR) (mkRefl cpTy nnL),
          thmD (ns ++ `honest.nonNullCheckRejectsNull) (mkEq cpTy nnL nnR) (mkRefl cpTy nnL)),
        ("forged translation fidelity (lmToMr maps ub to unsupported)",
          thmD (ns ++ `forged.lmToMrUb) (mkEq mrObsTy0 (mkApp lmToMr (lmObsC `ub)) (mrC `unsupported))
            (mkRefl mrObsTy0 (mkApp lmToMr (lmObsC `ub))),
          thmD (ns ++ `honest.lmToMrUb) (mkEq mrObsTy0 (mkApp lmToMr (lmObsC `ub)) (mrC `ub))
            (mkRefl mrObsTy0 (mkApp lmToMr (lmObsC `ub)))),
        ("forged MR Corpus.Side.check admitting pin-delta case 22",
          thmD (ns ++ `forged.mrGateIncludesCase22) (eqTrue mrSideWithCase22Check) reflTrue,
          thmD (ns ++ `honest.mrGateRejectsCase22) (eqFalse mrSideWithCase22Check) reflFalse),
        ("forged LM Corpus.Side.check admitting DST-boundary cases 6/7",
          thmD (ns ++ `forged.lmGateIncludesCase6) (eqTrue lmSideWithCase6Check) reflTrue,
          thmD (ns ++ `honest.lmGateRejectsCase6) (eqFalse lmSideWithCase6Check) reflFalse),
        ("forged cross-mode frozen-table lock (wdLmExpectedBasic = lmWdExpectedTb.map lmToMr)",
          thmD (ns ++ `forged.frozenTableCrossMode) (mkEq listMrTy (mkConst (bNs ++ `wdLmExpectedBasic)) lmMapTb)
            (mkRefl listMrTy (mkConst (bNs ++ `wdLmExpectedBasic))),
          thmD (ns ++ `honest.frozenTableBasic) (mkEq listMrTy (mkConst (bNs ++ `wdLmExpectedBasic)) lmMapBasic)
            (mkRefl listMrTy (mkConst (bNs ++ `wdLmExpectedBasic)))),
        ("forged LM out-of-range cell 24 returns okScalar 0 instead of unsupported",
          thmD (ns ++ `forged.lmOutOfRangeOk) (mkEq lmObsTy (lmObsU false 24) (mkApp (lmObsC `okScalar) (mkNatLit 0)))
            (mkRefl lmObsTy (lmObsU false 24)),
          thmD (ns ++ `honest.lmOutOfRangeUnsupported) (mkEq lmObsTy (lmObsU false 24) (lmObsC `unsupported))
            (mkRefl lmObsTy (lmObsU false 24))) ]
    let mut rejected : Nat := 0
    let mut twins : Nat := 0
    for (what, d, h) in forged do
      if ← accepts d then
        throwError "cross-root negative control FAILED: kernel accepted {what}"
      rejected := rejected + 1
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
            `Trusted.Rustc.V2026_06_01.MirSemantics.decodePtrBytesNoForge,
            `Trusted.Rustc.V2026_06_01.MirSemantics.decodeTypedValueFromBytes,
            `Trusted.Rustc.V2026_06_01.MirSemantics.intrinsicWidePointeeStep,
            `MiniRustSpec.WideDstAndMaybeUninitMR.mrTrustedWdObserve,
            `MiniRustSpec.WideDstAndMaybeUninitMR.mrWdObserve,
            `MiniRustSpec.Interp.stepM,
            `MiniRustSpec.Interp.checkPtrM,
            `MiniRustSpec.Interp.LayoutStrategy.compute_size_and_align,
            `MiniRustSpec.Interp.ptrOffsetInboundsM,
            `LeanMiriSpec.WideDstAndMaybeUninitLM.lmWdObserve,
            `LeanMiriSpec.WideDstAndMaybeUninitLM.lmWdObserveU,
            `Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta,
            `Miri.Interpreter.ptrOffsetInbounds,
            `Miri.Memory.Allocation.copy,
            `Miri.Memory.InitMask.prepareCopy,
            `Miri.Memory.Validity.checkScalar,
            `Miri.Memory.Validity.checkPrimitive ]),
        (directBundle,
          [ `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
            `MiniRustSpec.WideDstAndMaybeUninitMR.mrTrustedWdObserve,
            `MiniRustSpec.WideDstAndMaybeUninitMR.mrWdObserve,
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
            `Miri.Interpreter.ValidityMachine.scalarMayBeNull,
            `Miri.Memory.Validity.checkScalar,
            `Miri.Memory.Validity.checkPrimitive,
            `Miri.Memory.Allocation.copy,
            `Miri.Memory.InitMask.prepareCopy,
            `LeanMiriSpec.WideDstAndMaybeUninitLM.lmWdObserve,
            `LeanMiriSpec.WideDstAndMaybeUninitLM.lm_case13_union_copy_of_invalid_bool_byte_ok,
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
    return (added.size, bundleCount, lockCount, rejected, twins, reachChecked, crAxioms.toArray)

  let ctx : Core.Context :=
    { fileName := "<wd-cross-root>", fileMap := default, options := opts, maxHeartbeats := 0 }
  let ((addedCount, bundleCount, lockCount, rejectedCount, twinCount, reachCount, crAxioms), _) ←
    liftCoreM <| act.toIO ctx { env := baseEnv }
  unless addedCount ≥ 120 && bundleCount = 5 && lockCount = 39 && rejectedCount ≥ 36 &&
      twinCount = rejectedCount && reachCount ≥ 48 do
    throwError "cross-root: unexpected counts (added={addedCount}, bundles={bundleCount}, locks={lockCount}, rejected={rejectedCount}, twins={twinCount}, reach={reachCount})"
  logInfo m!"wd cross-root kernel bridge: added {addedCount} declarations ({bundleCount} bundles, {lockCount} fixture locks), rejected {rejectedCount} forged controls ({twinCount}/{rejectedCount} honest twins accepted), {reachCount} reachability edges across Trusted+MiniRust+Miri, axioms {crAxioms}"

/-! ## §3. Constructive Purity, Axiom Audit, and Auditor Self-Tests -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let bNs := `Anneal.Mir.WideDstAndMaybeUninitDualSpec
  let constructiveDecls : List Name :=
    [ `wdCodec, `wdEncode_decode_of_valid, `wdCodec_tight, `wdCodec_encode_injective,
      `wdCodec_decode_injective_on_valid, `wdValidRep_iff_decode_isSome,
      `wdCodec_rejects_malformed, `wdModel, `wdAnnealEval, `mrVerdict, `trustedVerdict,
      `lmTableCheckOf_sound, `lmTableCheckOf_of_eq, `cert_transport,
      `mrSide_check, `lmCheckOf_of_table, `bundleOfSel, `bundleOf, `domainBundleOf,
      `threeWayNormalAgreement, `crossAuthorityFaultEquiv, `exactBehaviorEq_both,
      `projectPositive, `projectFault, `modeSensitivity_present,
      `bundle_gate_pinDelta_and_dstBoundary, `unified_bundle_witness_kinds,
      `domain_bundle_claims, `dual_exact_three_way_classification,
      `dual_no_specPanic_all_cells, `dual_fail_closed_out_of_range,
      `dual_mode_sensitivity_exact, `dual_case19_mode_sensitivity,
      `dual_dst_honest_trusted_boundary, `dual_minirust300_pin_delta_and_flip_ready,
      `dual_case13_union_copy_vs_typed_read, `dual_case2_two_query_halves_agree,
      `mrTerminatesCleanly, `dual_minirust300_machine_level_pin_delta,
      `rootBackedLmAuthority,
      `rootBackedLmAuthority_tableCheck, `rootBackedLmAuthority_failClosed,
      `stepsM_eq_runToStopM, `stepsTB_eq_runToStopM ]
  let isChoiceFree (axs : Array Name) : Bool :=
    axs.all fun a => a == ``propext || a == ``Quot.sound
  for d in constructiveDecls do
    let axs ← liftCoreM <| Lean.collectAxioms (bNs ++ d)
    unless isChoiceFree axs do
      throwError "constructive audit failure: {d} uses a non-constructive axiom ({axs})"
  -- Exhaustive choice-free audit across the entire `WideDstAndMaybeUninitDualSpec` module:
  -- only the exact 3 upstream-Classical.choice re-exports may use `Classical.choice`.
  let choiceAllowlist : List Name :=
    [ bNs ++ `steps_eq_runToStopM_bm,
      bNs ++ `ep2_widedst_maybeuninit_dual_authority_capstone,
      bNs ++ `ep2_widedst_maybeuninit_dual_authority_capstone_nonvacuous ]
  let some modIdx := env.getModuleIdx? bNs
    | throwError "constructive audit failure: module {bNs} not found"
  let modData := env.header.moduleData[modIdx.toNat]!
  let mut exhaustiveChoiceFree : Nat := 0
  for c in modData.constNames do
    if bNs.isPrefixOf c && !choiceAllowlist.contains c then
      let axs ← liftCoreM <| Lean.collectAxioms c
      unless isChoiceFree axs do
        throwError "exhaustive constructive audit failure: {c} uses non-constructive axiom ({axs})"
      exhaustiveChoiceFree := exhaustiveChoiceFree + 1
  unless exhaustiveChoiceFree ≥ 250 do
    throwError "exhaustive constructive audit vacuous: only {exhaustiveChoiceFree} decls checked"
  -- Self-tests: constructive check rejects `Classical.choice`; standard-axiom check rejects
  -- `sorryAx` and `Lean.ofReduceBool`; trivial-prop detector rejects `True`, `1 = 1`, `∀ x, x = x`.
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
  let forallEq := Expr.forallE `x natTy (mkApp3 (mkConst ``Eq [1]) natTy (.bvar 0) (.bvar 0)) .default
  unless isTrivialProp (mkConst ``True) && isTrivialProp eq11 && isTrivialProp forallEq &&
      !isTrivialProp eq12 do
    throwError "self-test: trivial theorem detector failed in §3"
  let tNs := `Anneal.Mir.WideDstAndMaybeUninitCorrespondenceTests
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
  unless checked ≥ 9 do
    throwError "test audit vacuous: only {checked} test declarations"
  logInfo m!"wd constructive audit: {exhaustiveChoiceFree} DualSpec decls ({constructiveDecls.length} spotlighted) in [propext, Quot.sound]; {checked} test decls non-trivial & standard-axiom clean"

end Anneal.Mir.WideDstAndMaybeUninitCorrespondenceTests
