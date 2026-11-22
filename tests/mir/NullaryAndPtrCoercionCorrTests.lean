/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Anneal.Mir.NullaryAndPtrCoercionBundle
import MiniRustSpec.NullaryAndPtrCoercionMR

/-!
# Episode 2 Dual-Authority Correspondence Tests & Cross-Root Kernel Bridge
# (`Rvalue.nullaryOp`, `CastKind.pointerCoercion`, `CastKind.fnPtrToPtr`, `ProjectionElem.unwrapUnsafeBinder`)

Verifies the 4 already-trusted MIR variants end-to-end across BOTH authorities:

1. **Concrete Positive, UB, Flip-Direction, and Mode-Sensitivity Witnesses**
   covering `Rvalue.nullaryOp` (`size_of`/`align_of`/`offset_of!`/`ub_checks`),
   `CastKind.pointerCoercion` (function-pointer pipeline, slice `Unsize`,
   dead-operand UB, `ArrayToPointer`), `CastKind.fnPtrToPtr`, and
   `ProjectionElem.unwrapUnsafeBinder` (round-trip, binder struct, dead-local
   UB, and active-protector `BasicMemory` vs. `TreeBorrowsMemory` mode
   sensitivity).
2. **Cross-Root Dual-Authority Kernel Bridge (`run_cmd`)**:
   Loads BOTH `.lake/build/lib/lean` (root Lake:
   `Anneal.Mir.NullaryAndPtrCoercionBundle` and
   `MiniRustSpec.NullaryAndPtrCoercionMR`) and `examples/.lake/build/lib/lean`
   (`LeanMiriSpec.NullaryAndPtrCoercionLM`) into a fresh Lean kernel
   environment, constructs the genuine LeanMiri `ObsAuthority` directly over
   `LeanMiriSpec.NullaryAndPtrCoercionLM.npLmObserve`, submits and
   kernel-checks:
   - `lmAuthority` + `lmAuthority_denoteConsistent`,
   - `lmSide_check` (unified 32-key certificate) + all 4 per-variant checks,
   - closed unified `DualCorrespondenceBundle` + all 4 per-variant bundles,
   - instantiated `threeWayNormalAgreement`, `crossAuthorityFaultEquiv`,
     `exactBehaviorEq_both`, `lm_modeSensitivity_present`, and per-variant
     claims + flip-direction guards,
   - **definitional `Eq.refl` fixture locks** proving all 16 `CapturedMir`
     fixtures of `MiniRustSpec.NullaryAndPtrCoercionMR` are definitionally
     equal to the fixtures executed in `LeanMiriSpec.NullaryAndPtrCoercionLM`,
   - **negative controls** (forged ill-typed theorem, negated LM certificate,
     mode-inverted LM authority, colliding `denote` table, swapped fixture
     lock) all verified to be REJECTED by the kernel,
   - **transitive constant reachability** proving the closed dual-authority
     bundle genuinely reaches `Trusted.Rustc.V2026_06_01.MirSemantics.{stepMirFn,
     evalNullaryOp, evalReifyFnPointer, evalFnPtrToPtr}`,
     `MiniRustSpec.Interp.{steps, stepsTB}`, AND vendored
     `Miri.Interpreter.Step.step`.
3. **Constructive Axiom & Zero-`sorry` Audit**:
   Verifies that `Anneal.Mir.NullaryAndPtrCoercionBundle` codecs and core
   lemmas depend ONLY on `[propext, Quot.sound]` (zero `Classical.choice`, zero
   `sorryAx`, zero `Lean.ofReduceBool`), and that every cross-root declaration
   uses only standard axioms, plus self-tests confirming the auditor catches
   `sorryAx` and `ofReduceBool`.
-/

namespace Anneal.Mir.NullaryAndPtrCoercionCorrTests

open Anneal.DualCorrespondenceBundle
open Anneal.Mir.NullaryAndPtrCoercionBundle
open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.Interp
open MiniRustSpec.LibSpecr hiding Name
open MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.Witness hiding constU32
open MiniRustSpec.Correspondence.RefWitness
open MiniRustSpec.Correspondence.TbWitness
open MiniRustSpec.UnwindSetDiscrAndFnPtrMR
open MiniRustSpec.NullaryAndPtrCoercionMR

/-! ## §1. Concrete Witnesses, Flip-Direction Guards, & Mode Sensitivity (Root Lake) -/

/-- Constructive codec laws & tight validity witness for `npCodec`. -/
theorem np_codec_constructive_laws :
    npCodec.decode (npCodec.encode (.u32Val 42)) = some (.u32Val 42) ∧
    npCodec.decode (npCodec.encode (.u8Val 7)) = some (.u8Val 7) ∧
    npCodec.decode (npCodec.encode (.usizeVal 36)) = some (.usizeVal 36) ∧
    npCodec.decode (npCodec.encode (.ptrAlloc 65536)) = some (.ptrAlloc 65536) ∧
    npCodec.decode (99, 0) = none ∧
    npCodec.TightValidRep :=
  ⟨rfl, rfl, rfl, rfl, rfl, npCodec_tight⟩

/-- Every single one of the 4 variants has a non-vacuous positive normal return
AND a non-vacuous UB fault on BOTH Trusted Anneal (`npAnnealEval`) and MiniRust
(`mrAuthority`), ruling out vacuous support gates and constant-outcome
collapse. Each conjunct is evaluated independently by the kernel (running
`stepMirFn`, respectively `MiniRustSpec.Interp.steps`). -/
theorem np_all_4_variants_flip_verdict :
    ∀ v : NullaryPtrVariant,
      (∃ a, npAnnealEval .basic v .okPrimary () = some (.returns a) ∧
            mrAuthority.verdict (.basic, v, .okPrimary) = some (.returns a)) ∧
      npAnnealEval .basic v .ubFault () = some .undefinedBehavior ∧
      mrAuthority.verdict (.basic, v, .ubFault) = some .undefinedBehavior := by
  intro v
  cases v with
  | nullaryOp =>
    exact ⟨⟨.usizeVal 36, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | pointerCoercion =>
    exact ⟨⟨.ptrAlloc 65536, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | fnPtrToPtr =>
    exact ⟨⟨.ptrAlloc 65536, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | unwrapUnsafeBinder =>
    exact ⟨⟨.u32Val 73, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩

/-- Genuine mode-sensitivity witness across Trusted Anneal and MiniRust (`Mach`
vs. `MachTB`) on `ProjectionElem.unwrapUnsafeBinder`: `basic` / `BasicMemory`
returns `42` while `protectedTB` / `TreeBorrowsMemory` faults
`.undefinedBehavior`. -/
theorem np_unwrap_mode_sensitivity_root :
    npAnnealEval .basic .unwrapUnsafeBinder .modeCase () = some (.returns (.u32Val 42)) ∧
    mrAuthority.verdict (.basic, .unwrapUnsafeBinder, .modeCase) = some (.returns (.u32Val 42)) ∧
    npAnnealEval .protectedTB .unwrapUnsafeBinder .modeCase () = some .undefinedBehavior ∧
    mrAuthority.verdict (.protectedTB, .unwrapUnsafeBinder, .modeCase) =
      some .undefinedBehavior ∧
    (mrSide.flipW npModel mrSide_check).isSome = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   mr_modeSensitivity_present⟩

/-- Both root-Lake authorities realize the frozen 32-key verdict table on
EVERY key. -/
theorem np_two_authority_table_root (mode : NullaryPtrMode) (v : NullaryPtrVariant)
    (c : NullaryPtrCase) :
    npAnnealEval mode v c () = npExpectedVerdict mode v c ∧
    mrAuthority.verdict (mode, v, c) = npExpectedVerdict mode v c :=
  ⟨npAnnealEval_eq mode v c (), mrAuthority_verdict_eq mode v c⟩

/-- Selected entries of the frozen verdict table, pinned literally. -/
theorem np_expected_verdict_table_pins :
    npExpectedVerdict .basic .nullaryOp .okPrimary = some (.returns (.usizeVal 36)) ∧
    npExpectedVerdict .basic .nullaryOp .okSecondary = some (.returns (.u8Val 1)) ∧
    npExpectedVerdict .basic .nullaryOp .modeCase = some (.returns (.usizeVal 4)) ∧
    npExpectedVerdict .basic .pointerCoercion .okPrimary = some (.returns (.ptrAlloc 65536)) ∧
    npExpectedVerdict .basic .pointerCoercion .okSecondary = some (.returns (.usizeVal 3)) ∧
    npExpectedVerdict .basic .pointerCoercion .modeCase = some (.returns (.ptrAlloc 5)) ∧
    npExpectedVerdict .basic .fnPtrToPtr .okSecondary = some (.returns (.ptrAlloc 65537)) ∧
    npExpectedVerdict .basic .fnPtrToPtr .modeCase = some .undefinedBehavior ∧
    npExpectedVerdict .basic .unwrapUnsafeBinder .okSecondary = some (.returns (.u8Val 7)) ∧
    npExpectedVerdict .protectedTB .unwrapUnsafeBinder .modeCase = some .undefinedBehavior :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Re-exported MR certificates for all 4 variants (ensuring full transitive
reachability from this test module to every MR proof of this episode). -/
theorem np_mr_all_4_variant_witnesses_linked :
    mrAuthority.denoteConsistent = true ∧
    mrSide.check npModel = true ∧
    (∀ v, (mrVariantSide v).check npModel = true) :=
  ⟨mrAuthority_denoteConsistent, mrSide_check, mrVariantSide_check⟩

theorem np_mr_deep_theorems_used :
    (npMrObserve .basicMemory .unwrapUnsafeBinder .modeCase =
      .retBytes ((scalarBytes u32 42).map (projByteTB ∘ liftByteTB))) ∧
    (npMrObserve .treeBorrows .unwrapUnsafeBinder .modeCase = .ub) ∧
    npMrObsDictDistinct = true ∧
    (npAnnealEval .basic .fnPtrToPtr .okPrimary () ≠
      npAnnealEval .basic .fnPtrToPtr .okSecondary ()) := by
  have _ := @np_v1_evalRvalue_nullaryOp_eq
  have _ := @np_v1_nullary_contractChecks_unsupported
  have _ := @np_v1_nullary_ubChecks_universal
  have _ := @np_v1_nullary_sizeOf_of_intrinsic
  have _ := @np_v1_nullary_alignOf_of_intrinsic
  have _ := @np_v1_nullary_offsetOf_of_intrinsic
  have _ := @np_v1_nullary_unsupported_of_unresolved_size
  have _ := @np_v1_nullary_tuple16_universal
  have _ := @np_v1_nullary_padded_offset_universal
  have _ := @np_v1_nullary_unsized_unsupported
  have _ := @np_v1_minirust_layout_and_offset_agreement
  have _ := @np_stepM_of_evalStatementM
  have _ := @np_stepM_error_of_evalStatementM
  have _ := @np_v1_evalValueM_nullaryOp_M
  have _ := @np_v1_nullaryOp_coupled_step_sim_all_four
  have _ := @np_v1_nullaryOp_dead_dst_ub_lockstep
  have _ := @np_v1_nullaryOp_three_way_witness
  have _ := @np_v2_pointerCoercion_dispatch
  have _ := @np_v2_reify_and_closure_fnPointer_lockstep
  have _ := @np_v2_unsafeFnPointer_ground_truth_and_divergences
  have _ := @np_v2_mutToConstPointer_all_shapes_and_ub
  have _ := @np_v2_arrayToPointer_global_stack_scalar_and_ub
  have _ := @np_v2_pointerCoercion_three_way_witness
  have _ := @np_v2_dyn_unsize_wide_pointer_bridge_witness
  have _ := @np_v2_dyn_dispatch_and_invalid_vtable_ub_witness
  have _ := @np_v3_evalRvalue_fnPtrToPtr_eq
  have _ := @np_v3_fnPtrToPtr_lockstep_mach_and_tb
  have _ := @np_v3_fnPtrToPtr_extra_checks_divergence
  have _ := @np_v3_fnPtrToPtr_trusted_step_and_ub_witness
  have _ := @np_v3_fnPtrToPtr_rustIntrinsic_abi_ub
  have _ := @np_v3_fnPtrToPtr_three_way_witness
  have _ := @np_v4_trusted_unwrapUnsafeBinder_transparent
  have _ := @np_v4_unwrapUnsafeBinder_assign_coupled_lockstep_and_wfLive
  have _ := @np_v4_wrapUnsafeBinder_universal_sim
  have _ := @np_v4_unwrapUnsafeBinder_three_way_witness
  have _ := @npTrustedObserve_table
  have _ := @npMrObserveClass_table
  exact ⟨npMrObserve_unwrap_mode_sensitivity.1, npMrObserve_unwrap_mode_sensitivity.2,
    npMrObsDict_distinct, by decide +kernel⟩

/-! ## §2. Cross-Root Dual-Authority Kernel Bridge (`MiniRustSpec` + `LeanMiriSpec`) -/

open Lean Elab Command Meta in
run_cmd do
  let opts := (← getOptions).setBool `Elab.async false
  let sp : SearchPath := [System.FilePath.mk ".lake/build/lib/lean",
                          System.FilePath.mk "examples/.lake/build/lib/lean"]
  initSearchPath (← findSysroot) sp
  let baseEnv ← importModules
    #[{ module := `Anneal.Mir.NullaryAndPtrCoercionBundle },
      { module := `MiniRustSpec.NullaryAndPtrCoercionMR },
      { module := `LeanMiriSpec.NullaryAndPtrCoercionLM }]
    {} 0
  let ns := `Anneal.Mir.NullaryAndPtrCoercionCorrTests.CrossRoot
  let bNs := `Anneal.Mir.NullaryAndPtrCoercionBundle
  let cNs := `Anneal.Mir.DropBinderAndSubtypeBundle.Corpus
  let mrNs := `MiniRustSpec.NullaryAndPtrCoercionMR
  let lmNs := `LeanMiriSpec.NullaryAndPtrCoercionLM
  let act : CoreM (Nat × Nat × Nat × Array Name) := do
    let addDef (name : Name) (val : Expr) : CoreM Expr := do
      let ty ← MetaM.run' <| inferType val
      addDecl <| .defnDecl {
        name, levelParams := [], type := ty, value := val,
        hints := .regular 0, safety := .safe }
      return ty
    let addThm (name : Name) (ty pf : Expr) : CoreM Unit := do
      addDecl <| .thmDecl { name, levelParams := [], type := ty, value := pf }
    let boolTy := mkConst ``Bool
    let boolTrue := mkConst ``Bool.true
    let boolFalse := mkConst ``Bool.false
    let natTy := mkConst ``Nat
    let eqTrue (e : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) boolTy e boolTrue
    let reflTrue : Expr := mkApp2 (mkConst ``Eq.refl [1]) boolTy boolTrue
    let eqFalse (e : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) boolTy e boolFalse
    let reflFalse : Expr := mkApp2 (mkConst ``Eq.refl [1]) boolTy boolFalse

    -- Helper encoders from NullaryPtrVariant / NullaryPtrCase to the Nat indices of
    -- `npLmObserve` (`variantIdx`: nullaryOp = 0, pointerCoercion = 1, fnPtrToPtr = 2,
    -- unwrapUnsafeBinder = 3; `caseIdx`: okPrimary = 0, okSecondary = 1, ubFault = 2,
    -- modeCase = 3).
    let mkVariantToNat : MetaM Expr := do
      let varTy := mkConst (mrNs ++ `NullaryPtrVariant)
      withLocalDeclD `v varTy fun v => do
        let recApp := mkAppN (mkConst (mrNs ++ `NullaryPtrVariant.rec) [1])
          #[mkLambda `x .default varTy natTy,
            mkNatLit 0, mkNatLit 1, mkNatLit 2, mkNatLit 3, v]
        mkLambdaFVars #[v] recApp
    let mkCaseToNat : MetaM Expr := do
      let caseTy := mkConst (mrNs ++ `NullaryPtrCase)
      withLocalDeclD `c caseTy fun c => do
        let recApp := mkAppN (mkConst (mrNs ++ `NullaryPtrCase.rec) [1])
          #[mkLambda `x .default caseTy natTy,
            mkNatLit 0, mkNatLit 1, mkNatLit 2, mkNatLit 3, c]
        mkLambdaFVars #[c] recApp

    let varToNatName := ns ++ `variantToNat
    let caseToNatName := ns ++ `caseToNat
    let _ ← addDef varToNatName (← MetaM.run' mkVariantToNat)
    let _ ← addDef caseToNatName (← MetaM.run' mkCaseToNat)

    -- 1. Build the genuine LeanMiri `ObsAuthority NullaryPtrKey NullaryPtrObsVal` directly
    -- over `LeanMiriSpec.NullaryAndPtrCoercionLM.npLmObserve`.
    let keyTy := mkConst (bNs ++ `NullaryPtrKey)
    let obsValTy := mkConst (bNs ++ `NullaryPtrObsVal)
    let lmObsTy := mkConst (lmNs ++ `NullaryPtrLmObs)
    let mkLmAuth (invertMode : Bool := false) (collideDenote : Bool := false) : MetaM Expr := do
      let decLmObs := mkConst (lmNs ++ `instDecidableEqNullaryPtrLmObs)
      let observeFn ← withLocalDeclD `k keyTy fun k => do
        let mExpr := mkProj ``Prod 0 k
        let rest := mkProj ``Prod 1 k
        let vExpr := mkProj ``Prod 0 rest
        let cExpr := mkProj ``Prod 1 rest
        let tb0 := mkApp (mkConst (bNs ++ `npModeToLmTreeBorrows)) mExpr
        let tb := if invertMode then mkApp (mkConst ``Bool.not) tb0 else tb0
        let vNat := mkApp (mkConst varToNatName) vExpr
        let cNat := mkApp (mkConst caseToNatName) cExpr
        let call := mkApp3 (mkConst (lmNs ++ `npLmObserve)) tb vNat cNat
        let someCall := mkApp2 (mkConst ``Option.some [0]) lmObsTy call
        mkLambdaFVars #[k] someCall
      let verdTy := mkApp (mkConst (cNs ++ `Verdict)) obsValTy
      let mkRet (v : Expr) : Expr := mkApp2 (mkConst (cNs ++ `Verdict.returns)) obsValTy v
      let mkPair (a b : Expr) : Expr := mkApp4 (mkConst ``Prod.mk [0, 0]) verdTy lmObsTy a b
      let mkU32V (n : Nat) : Expr :=
        mkRet (mkApp (mkConst (bNs ++ `NullaryPtrObsVal.u32Val)) (mkNatLit n))
      let mkU8V (n : Nat) : Expr :=
        mkRet (mkApp (mkConst (bNs ++ `NullaryPtrObsVal.u8Val)) (mkNatLit n))
      let mkUsizeV (n : Nat) : Expr :=
        mkRet (mkApp (mkConst (bNs ++ `NullaryPtrObsVal.usizeVal)) (mkNatLit n))
      let mkPtrV (n : Nat) : Expr :=
        mkRet (mkApp (mkConst (bNs ++ `NullaryPtrObsVal.ptrAlloc)) (mkNatLit n))
      let mkU32O (n : Nat) : Expr :=
        mkApp (mkConst (lmNs ++ `NullaryPtrLmObs.u32Val)) (mkNatLit n)
      let mkU8O (n : Nat) : Expr :=
        mkApp (mkConst (lmNs ++ `NullaryPtrLmObs.u8Val)) (mkNatLit n)
      let mkUsizeO (n : Nat) : Expr :=
        mkApp (mkConst (lmNs ++ `NullaryPtrLmObs.usizeVal)) (mkNatLit n)
      let mkPtrO (n : Nat) : Expr :=
        mkApp (mkConst (lmNs ++ `NullaryPtrLmObs.ptrAlloc)) (mkNatLit n)
      let entries : List Expr :=
        [ mkPair (mkUsizeV 36) (mkUsizeO 36),
          mkPair (mkU8V 1) (mkU8O 1),
          mkPair (mkUsizeV 4) (if collideDenote then mkUsizeO 36 else mkUsizeO 4),
          mkPair (mkPtrV 65536) (mkPtrO 65536),
          mkPair (mkUsizeV 3) (mkUsizeO 3),
          mkPair (mkPtrV 5) (mkPtrO 5),
          mkPair (mkPtrV 65537) (mkPtrO 65537),
          mkPair (mkU32V 73) (mkU32O 73),
          mkPair (mkU8V 7) (mkU8O 7),
          mkPair (mkU32V 42) (mkU32O 42),
          mkPair (mkApp (mkConst (cNs ++ `Verdict.undefinedBehavior)) obsValTy)
            (mkConst (lmNs ++ `NullaryPtrLmObs.ub)),
          mkPair (mkApp (mkConst (cNs ++ `Verdict.unsupported)) obsValTy)
            (mkConst (lmNs ++ `NullaryPtrLmObs.unsupported)) ]
      let pairTy := mkApp2 (mkConst ``Prod [0, 0]) verdTy lmObsTy
      let denoteList := entries.foldr (fun h t => mkApp3 (mkConst ``List.cons [0]) pairTy h t)
        (mkApp (mkConst ``List.nil [0]) pairTy)
      return mkApp6 (mkConst (cNs ++ `ObsAuthority.mk))
        keyTy obsValTy lmObsTy decLmObs observeFn denoteList

    let lmAuthName := ns ++ `lmAuthority
    let _ ← addDef lmAuthName (← MetaM.run' <| mkLmAuth false false)
    let lmAuthC := mkConst lmAuthName
    let mut added : Array Name := #[varToNatName, caseToNatName, lmAuthName]

    -- 2. Kernel-checked `denoteConsistent`, unified `lmSide_check`, and all 4 per-variant checks.
    let decObsVal := mkConst (bNs ++ `instDecidableEqNullaryPtrObsVal)
    let denoteConsExpr := mkApp4 (mkConst (cNs ++ `ObsAuthority.denoteConsistent))
      keyTy obsValTy decObsVal lmAuthC
    let denoteConsName := ns ++ `lmAuthority_denoteConsistent
    addThm denoteConsName (eqTrue denoteConsExpr) reflTrue
    added := added.push denoteConsName

    let lmCheckName := ns ++ `lmSide_check
    addThm lmCheckName (eqTrue (mkApp (mkConst (bNs ++ `lmCheckOf)) lmAuthC)) reflTrue
    added := added.push lmCheckName

    let unifiedBundleName := ns ++ `unifiedDualBundle
    let unifiedTy ← addDef unifiedBundleName
      (mkApp2 (mkConst (bNs ++ `bundleOf)) lmAuthC (mkConst lmCheckName))
    unless unifiedTy.getAppFn.isConstOf ``Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle do
      throwError "cross-root: {unifiedBundleName} is not a DualCorrespondenceBundle"
    added := added.push unifiedBundleName

    -- Instantiate lifted cross-authority theorems + projectPositive/projectFault at the closed
    -- unified dual-authority bundle.
    for thmName in [`threeWayNormalAgreement, `crossAuthorityFaultEquiv,
                    `exactBehaviorEq_both, `lm_modeSensitivity_present] do
      let val := mkApp2 (mkConst (bNs ++ thmName)) lmAuthC (mkConst lmCheckName)
      let ty ← MetaM.run' <| inferType val
      let outName := ns ++ thmName
      addThm outName ty val
      added := added.push outName
    let unifiedC := mkConst unifiedBundleName
    let projPosVal ← MetaM.run' <| mkAppM ``DualCorrespondenceBundle.projectPositive #[unifiedC]
    addThm (ns ++ `unified_projectPositive) (← MetaM.run' <| inferType projPosVal) projPosVal
    added := added.push (ns ++ `unified_projectPositive)
    let projFaultVal ← MetaM.run' <| mkAppM ``DualCorrespondenceBundle.projectFault #[unifiedC]
    addThm (ns ++ `unified_projectFault) (← MetaM.run' <| inferType projFaultVal) projFaultVal
    added := added.push (ns ++ `unified_projectFault)

    -- All 4 per-variant bundles, claims, projectPositive, projectFault, & flip-direction guards.
    let variantCtors : List Name :=
      [`nullaryOp, `pointerCoercion, `fnPtrToPtr, `unwrapUnsafeBinder]
    let mut bundleCount : Nat := 1
    for vc in variantCtors do
      let vConst := mkConst (mrNs ++ `NullaryPtrVariant ++ vc)
      let chkName := ns ++ `variantCheck ++ vc
      addThm chkName (eqTrue (mkApp2 (mkConst (bNs ++ `lmVariantCheckOf)) vConst lmAuthC)) reflTrue
      added := added.push chkName
      let vbName := ns ++ `variantBundle ++ vc
      let vbTy ← addDef vbName
        (mkApp3 (mkConst (bNs ++ `variantBundleOf)) vConst lmAuthC (mkConst chkName))
      unless vbTy.getAppFn.isConstOf ``Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle do
        throwError "cross-root: {vbName} is not a DualCorrespondenceBundle"
      added := added.push vbName
      bundleCount := bundleCount + 1
      let clName := ns ++ `variantClaims ++ vc
      let clVal := mkApp3 (mkConst (bNs ++ `variant_bundle_claims)) vConst lmAuthC (mkConst chkName)
      addThm clName (← MetaM.run' <| inferType clVal) clVal
      added := added.push clName
      let vbC := mkConst vbName
      let vpVal ← MetaM.run' <| mkAppM ``DualCorrespondenceBundle.projectPositive #[vbC]
      addThm (ns ++ `variantProjectPositive ++ vc) (← MetaM.run' <| inferType vpVal) vpVal
      added := added.push (ns ++ `variantProjectPositive ++ vc)
      let vfVal ← MetaM.run' <| mkAppM ``DualCorrespondenceBundle.projectFault #[vbC]
      addThm (ns ++ `variantProjectFault ++ vc) (← MetaM.run' <| inferType vfVal) vfVal
      added := added.push (ns ++ `variantProjectFault ++ vc)

    -- 3. Definitional `Eq.refl` fixture locks proving ALL 16 `CapturedMir` fixtures are
    -- definitionally IDENTICAL between `MiniRustSpec` and `LeanMiriSpec`.
    let capMirTy := mkConst `Trusted.Rustc.V2026_06_01.MirAst.CapturedMir
    let fixtureNames : List Name :=
      [ `v1NullaryTupleMir, `v1NullaryUbChecksMir, `v1NullaryUbBranchMir,
        `v1NullaryPaddedOffsetMir,
        `v2CalleeU32Mir, `v2PtrCoerceFnPipelineMir, `v2PtrCoerceUnsizeSliceMir,
        `v2PtrCoerceDeadUbMir, `v2PtrCoerceArrayToPtrMir,
        `v3FnPtrToPtrConstMir, `v3FnPtrToPtrMutChainMir, `v3FnPtrToPtrDeadUbMir,
        `v4UnwrapBinderRoundtripMir, `v4UnwrapBinderNzU8Mir, `v4UnwrapBinderDeadUbMir,
        `v4UnwrapBinderProtectedMir ]
    let mut lockCount : Nat := 0
    for tag in fixtureNames do
      let lockName := ns ++ `fixtureLock ++ tag
      let lhs := mkConst (mrNs ++ tag)
      let rhs := mkConst (lmNs ++ tag)
      addThm lockName (mkApp3 (mkConst ``Eq [1]) capMirTy lhs rhs)
        (mkApp2 (mkConst ``Eq.refl [1]) capMirTy lhs)
      added := added.push lockName
      lockCount := lockCount + 1
    unless lockCount = 16 do
      throwError "cross-root: expected 16 fixture locks, got {lockCount}"

    -- 4. Negative controls on scratch copies of the environment: the Lean kernel MUST reject
    -- every forged theorem, mode-inverted authority, colliding denote table, and swapped
    -- fixture lock.
    let saved ← getEnv
    let rejects (d : Declaration) : CoreM Bool := do
      let r ← try addDecl d; pure false catch _ => pure true
      setEnv saved
      return r
    let invertedAuth ← MetaM.run' <| mkLmAuth true false
    let collidingAuth ← MetaM.run' <| mkLmAuth false true
    let collidingDenote := mkApp4 (mkConst (cNs ++ `ObsAuthority.denoteConsistent))
      keyTy obsValTy decObsVal collidingAuth
    let forged : List (String × Declaration) :=
      [ ("ill-typed 0 = 1 theorem", .thmDecl {
          name := ns ++ `forged.zeroEqOne, levelParams := [],
          type := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 0) (mkNatLit 1),
          value := mkApp2 (mkConst ``Eq.refl [1]) natTy (mkNatLit 0) }),
        ("negated LM check certificate", .thmDecl {
          name := ns ++ `forged.lmCheckFalse, levelParams := [],
          type := eqFalse (mkApp (mkConst (bNs ++ `lmCheckOf)) lmAuthC),
          value := reflFalse }),
        ("mode-inverted LM authority certificate", .thmDecl {
          name := ns ++ `forged.modeInvertedLmCheck, levelParams := [],
          type := eqTrue (mkApp (mkConst (bNs ++ `lmCheckOf)) invertedAuth),
          value := reflTrue }),
        ("colliding LM denote table", .thmDecl {
          name := ns ++ `forged.collidingDenote, levelParams := [],
          type := eqTrue collidingDenote,
          value := reflTrue }),
        ("swapped fixture lock (V1 tuple != V1 ub_checks)", .thmDecl {
          name := ns ++ `forged.swappedFixture, levelParams := [],
          type := mkApp3 (mkConst ``Eq [1]) capMirTy
            (mkConst (mrNs ++ `v1NullaryTupleMir)) (mkConst (lmNs ++ `v1NullaryUbChecksMir)),
          value := mkApp2 (mkConst ``Eq.refl [1]) capMirTy
            (mkConst (mrNs ++ `v1NullaryTupleMir)) }),
        ("forged ill-typed Unsize acceptance (mutability upgrade / element mismatch)", .thmDecl {
          name := ns ++ `forged.illTypedUnsizeAccepted, levelParams := [],
          type := eqTrue (mkConst (lmNs ++ `npIllTypedUnsizeAccepted)),
          value := reflTrue }) ]
    let mut rejected : Nat := 0
    for (what, d) in forged do
      unless ← rejects d do
        throwError "cross-root negative control FAILED: kernel accepted {what}"
      rejected := rejected + 1

    -- 5. Axiom, safety, non-triviality, & transitive reachability audit across ALL THREE
    -- engines (Trusted MIR + MiniRust Interp + vendored Miri.Interpreter).
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
    -- Verify new LM B1 fidelity & Tree Borrows theorems are present, non-trivial, and axiom-clean.
    let lmDeepThms : List Name :=
      [ lmNs ++ `npUnsizeArraySpec?_snd_eq_unsizeArrayLen?,
        lmNs ++ `np_v2_unsize_spec_laws,
        lmNs ++ `lm_np_v2_unsize_fidelity_and_negative_witness,
        lmNs ++ `lm_np_v4_deref_and_subplace_unwrap_tb_witness ]
    for n in lmDeepThms do
      let some (.thmInfo v) := env.find? n
        | throwError "cross-root: required LM theorem {n} missing"
      if isTrivialProp v.type then
        throwError "cross-root: LM theorem {n} is trivial"
      for a in ← collectAxioms n do
        unless isStdAx a do
          throwError "cross-root: LM theorem {n} depends on non-standard axiom {a}"
        crAxioms := crAxioms.insert a
    -- Self-tests: auditor MUST detect sorryAx, Lean.ofReduceBool, and trivial theorems.
    unless !(← collectAxioms ``sorryAx).all isStdAx do
      throwError "cross-root self-test: sorryAx was not detected"
    unless !(← collectAxioms ``Lean.ofReduceBool).all isStdAx do
      throwError "cross-root self-test: Lean.ofReduceBool was not detected"
    let trivEq := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 1)
    let nonTrivEq := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 2)
    unless isTrivialProp (mkConst ``True) && isTrivialProp trivEq && !isTrivialProp nonTrivEq do
      throwError "cross-root self-test: trivial theorem detector failed"

    -- Verify transitive reachability from `unifiedDualBundle` to Trusted, MiniRust, AND
    -- vendored Miri.
    let mut reach : NameSet := {}
    let mut todo : Array Name := #[unifiedBundleName]
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if reach.contains n then continue
      reach := reach.insert n
      if let some ci := env.find? n then
        for d in ci.getUsedConstantsAsSet do
          if !reach.contains d then todo := todo.push d
    let requiredReach : List Name :=
      [ `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalNullaryOp,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalReifyFnPointer,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalFnPtrToPtr,
        `MiniRustSpec.Interp.steps,
        `MiniRustSpec.Interp.stepsTB,
        `MiniRustSpec.NullaryAndPtrCoercionMR.npRunTrusted,
        `MiniRustSpec.NullaryAndPtrCoercionMR.npMrObserve,
        `MiniRustSpec.NullaryAndPtrCoercionMR.npTrustedObserve_table,
        `MiniRustSpec.NullaryAndPtrCoercionMR.npMrObserveClass_table,
        `Miri.Interpreter.Step.step,
        `LeanMiriSpec.NullaryAndPtrCoercionLM.npLmObserve ]
    for req in requiredReach do
      unless reach.contains req do
        throwError "cross-root reachability failure: unifiedDualBundle does not reach {req}"

    return (added.size, bundleCount, rejected, crAxioms.toArray)

  let ctx : Core.Context :=
    { fileName := "<np-cross-root>", fileMap := default, options := opts, maxHeartbeats := 0 }
  let ((addedCount, bundleCount, rejectedCount, crAxioms), _) ←
    liftCoreM <| act.toIO ctx { env := baseEnv }
  unless addedCount ≥ 48 && bundleCount = 5 && rejectedCount = 6 do
    throwError "cross-root: unexpected counts (added={addedCount}, bundles={bundleCount}, rejected={rejectedCount})"
  logInfo m!"np cross-root kernel bridge: added {addedCount} declarations ({bundleCount} bundles, 16 fixture locks), rejected {rejectedCount} forged controls, reached Trusted+MiniRust+Miri, axioms {crAxioms}"

/-! ## §3. Constructive Axiom Audit of `Anneal.Mir.NullaryAndPtrCoercionBundle` & Test Module -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let constructiveDecls : List Name :=
    [ ``Anneal.Mir.NullaryAndPtrCoercionBundle.npCodec,
      ``Anneal.Mir.NullaryAndPtrCoercionBundle.npCodec_tight,
      ``Anneal.Mir.NullaryAndPtrCoercionBundle.npAnnealEval,
      ``Anneal.Mir.NullaryAndPtrCoercionBundle.npAnnealEval_eq,
      ``Anneal.Mir.NullaryAndPtrCoercionBundle.mrAuthority,
      ``Anneal.Mir.NullaryAndPtrCoercionBundle.mrAuthority_denoteConsistent,
      ``Anneal.Mir.NullaryAndPtrCoercionBundle.mrAuthority_verdict_eq,
      ``Anneal.Mir.NullaryAndPtrCoercionBundle.mrSide_check,
      ``Anneal.Mir.NullaryAndPtrCoercionBundle.mrVariantSide_check,
      ``Anneal.Mir.NullaryAndPtrCoercionBundle.lmCheckOf_congr,
      ``Anneal.Mir.NullaryAndPtrCoercionBundle.lmVariantCheckOf_congr,
      ``Anneal.Mir.NullaryAndPtrCoercionBundle.bundleOf,
      ``Anneal.Mir.NullaryAndPtrCoercionBundle.variantBundleOf,
      ``Anneal.Mir.NullaryAndPtrCoercionBundle.threeWayNormalAgreement,
      ``Anneal.Mir.NullaryAndPtrCoercionBundle.crossAuthorityFaultEquiv,
      ``Anneal.Mir.NullaryAndPtrCoercionBundle.exactBehaviorEq_both,
      ``Anneal.Mir.NullaryAndPtrCoercionBundle.mr_modeSensitivity_present,
      ``Anneal.Mir.NullaryAndPtrCoercionBundle.lm_modeSensitivity_present,
      ``Anneal.Mir.NullaryAndPtrCoercionBundle.variant_bundle_claims ]
  for d in constructiveDecls do
    let axs ← liftCoreM <| Lean.collectAxioms d
    for a in axs do
      unless a == ``propext || a == ``Quot.sound do
        throwError "constructive audit failure: {d} uses non-constructive axiom {a}"
  for (c, _) in env.constants.map₂.toList do
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "test audit failure: {c} uses sorryAx"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "test audit failure: {c} uses non-standard axiom {a}"
  logInfo m!"np constructive audit: verified {constructiveDecls.length} bundle declarations in [propext, Quot.sound] (0 Classical.choice, 0 sorryAx, 0 ofReduceBool)"

end Anneal.Mir.NullaryAndPtrCoercionCorrTests
