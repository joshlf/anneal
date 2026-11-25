/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Trusted
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Anneal.Mir.DynTraitVTableBundle
import MiniRustSpec.DynTraitVTableMR

/-!
# Episode 2 Dual-Authority Correspondence Tests & Cross-Root Kernel Bridge
# (`dyn Trait` Unsizing, Trait Upcasting, Virtual Dispatch, Dynamic Layout, Wide-Pointer Queries)

Verifies the 4 `dyn Trait` variants (`thinUnsize`, `dynUpcastAndNop`,
`virtualDispatchAndProtector`, `dynLayoutRawBorrowAndAddrEq`) end-to-end across
BOTH authorities:

1. **Concrete Positive, UB, Flip-Direction, and Mode-Sensitivity Witnesses**
   (§1, root Lake): the codec laws of `DynTraitVTableObs`, a positive return and
   a UB fault for every variant on Trusted Anneal and MiniRust, the Crubit `c16`
   receiver-protector mode sensitivity, the literal 32-key verdict table, and
   the root capstone.
2. **Cross-Root Dual-Authority Kernel Bridge (`run_cmd`)** (§2):
   Loads BOTH `.lake/build/lib/lean` (root Lake:
   `Anneal.Mir.DynTraitVTableBundle` and `MiniRustSpec.DynTraitVTableMR`) and
   `examples/.lake/build/lib/lean` (`LeanMiriSpec.DynTraitVTableLM`) into a
   fresh Lean kernel environment, constructs the genuine LeanMiri
   `ObsAuthority` directly over `LeanMiriSpec.DynTraitVTableLM.dvLmObserve`,
   submits and kernel-checks:
   - `lmAuthority` + `lmAuthority_denoteConsistent`,
   - `lmSide_check` (unified 32-key certificate) + all 4 per-variant checks,
   - closed unified `DualCorrespondenceBundle` + all 4 per-variant bundles,
   - instantiated `threeWayNormalAgreement`, `crossAuthorityFaultEquiv`,
     `exactBehaviorEq_both`, `lm_modeSensitivity_present`, the Episode 2
     capstone `ep2_dyn_trait_vtable_capstone`, and per-variant claims +
     flip-direction guards,
   - **definitional `Eq.refl` fixture locks** proving that the frozen vtable
     table, the virtual-method table, the linked callee table, and every
     `CapturedMir` fixture (and fixture family) of
     `MiniRustSpec.DynTraitVTableMR` are definitionally equal to the ones
     executed in `LeanMiriSpec.DynTraitVTableLM`,
   - **negative controls** (forged ill-typed theorem, negated LM certificate,
     mode-inverted LM authority, colliding `denote` table, swapped fixture
     locks, variant-swapped LM authority, `Super` / `Side` vtable-swapped
     `denote` table, forged LM protector verdict) all verified to be REJECTED
     by the kernel,
   - **transitive constant reachability** proving the closed dual-authority
     bundle genuinely reaches the Trusted `dyn` semantics, `MiniRustSpec.Interp`,
     AND the vendored `Miri.Interpreter` vtable / virtual-call / dynamic-layout
     / cast machinery.
3. **`V2026_06_01` ↔ `V2026_08_01` dialect homomorphism** (§3, Condition `C7`).
4. **Campaign #22 Miri-differential agreement** (§4, Condition `C8`):
   `finding_0000 .. finding_0004` evaluate by `rfl` to Miri's results
   `20 / 182 / 67 / 57 / 5`.
5. **Constructive Axiom & Zero-`sorry` Audit** (§5):
   Verifies that `Anneal.Mir.DynTraitVTableBundle` codecs and core lemmas
   depend ONLY on `[propext, Quot.sound]` (zero `Classical.choice`, zero
   `sorryAx`, zero `Lean.ofReduceBool`), and that every declaration of this
   module uses only standard axioms.
-/

namespace Anneal.Mir.DynTraitVTableTests

open Anneal.DualCorrespondenceBundle
open Anneal.Mir.DynTraitVTableBundle
open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.Interp
open MiniRustSpec.LibSpecr hiding Name
open MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.Witness hiding constU32
open MiniRustSpec.Correspondence.RefWitness
open MiniRustSpec.Correspondence.TbWitness
open MiniRustSpec.UnwindSetDiscrAndFnPtrMR
open MiniRustSpec.DynTraitVTableMR

/-! ## §1. Concrete Witnesses, Flip-Direction Guards, & Mode Sensitivity (Root Lake) -/

/-- Constructive codec laws & tight validity witness for `dvCodec`: every
constructor round-trips, an unknown tag does not decode, a scalar
representation with non-zero padding is not valid, and `ValidRep` is tight. -/
theorem dv_codec_constructive_laws :
    dvCodec.decode (dvCodec.encode (.u32Val 77)) = some (.u32Val 77) ∧
    dvCodec.decode (dvCodec.encode (.usizeVal 4)) = some (.usizeVal 4) ∧
    dvCodec.decode (dvCodec.encode (.boolVal 1)) = some (.boolVal 1) ∧
    dvCodec.decode (dvCodec.encode (.widePtr 1 0 16384)) = some (.widePtr 1 0 16384) ∧
    dvCodec.encode (.widePtr 5 1 16384) = (3, 5, 1, 16384) ∧
    dvCodec.decode (99, 0, 0, 0) = none ∧
    ¬ dvValidRep (0, 2, 1, 0) ∧
    ¬ dvValidRep (4, 0, 0, 0) ∧
    dvValidRep (3, 5, 1, 16384) ∧
    dvCodec.TightValidRep :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide, dvCodec_tight⟩

/-- Every single one of the 4 variants has a non-vacuous positive normal return
AND a non-vacuous UB fault on BOTH Trusted Anneal (`dvAnnealEval`) and MiniRust
(`mrAuthority`), ruling out vacuous support gates and constant-outcome
collapse. Each conjunct is evaluated independently by the kernel (running
`stepMirFn`, respectively `MiniRustSpec.Interp.steps`). -/
theorem dv_all_4_variants_flip_verdict :
    ∀ v : DynVtVariant,
      (∃ a, dvAnnealEval .basic v .okPrimary () = some (.returns a) ∧
            mrAuthority.verdict (.basic, v, .okPrimary) = some (.returns a)) ∧
      dvAnnealEval .basic v .ubFault () = some .undefinedBehavior ∧
      mrAuthority.verdict (.basic, v, .ubFault) = some .undefinedBehavior := by
  intro v
  cases v with
  | thinUnsize =>
    exact ⟨⟨.widePtr 1 0 16384, by decide +kernel, by decide +kernel⟩,
      by decide +kernel, by decide +kernel⟩
  | dynUpcastAndNop =>
    exact ⟨⟨.widePtr 1 0 16388, by decide +kernel, by decide +kernel⟩,
      by decide +kernel, by decide +kernel⟩
  | virtualDispatchAndProtector =>
    exact ⟨⟨.u32Val 2, by decide +kernel, by decide +kernel⟩,
      by decide +kernel, by decide +kernel⟩
  | dynLayoutRawBorrowAndAddrEq =>
    exact ⟨⟨.usizeVal 4, by decide +kernel, by decide +kernel⟩,
      by decide +kernel, by decide +kernel⟩

/-- Genuine mode-sensitivity witness across Trusted Anneal and MiniRust (`Mach`
vs. `MachTB`) on the Crubit `c16` virtual call: `basic` / `BasicMemory` returns
`77` while `protectedTB` / `TreeBorrowsMemory` faults `.undefinedBehavior`
(the aliased write hits the receiver's call protector). -/
theorem dv_c16_mode_sensitivity_root :
    dvAnnealEval .basic .virtualDispatchAndProtector .modeCase () =
      some (.returns (.u32Val 77)) ∧
    mrAuthority.verdict (.basic, .virtualDispatchAndProtector, .modeCase) =
      some (.returns (.u32Val 77)) ∧
    dvAnnealEval .protectedTB .virtualDispatchAndProtector .modeCase () =
      some .undefinedBehavior ∧
    mrAuthority.verdict (.protectedTB, .virtualDispatchAndProtector, .modeCase) =
      some .undefinedBehavior ∧
    (mrSide.flipW dvModel mrSide_check).isSome = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   mr_modeSensitivity_present⟩

/-- Both root-Lake authorities realize the frozen 32-key verdict table on
EVERY key. -/
theorem dv_two_authority_table_root (mode : DynVtMode) (v : DynVtVariant) (c : DynVtCase) :
    dvAnnealEval mode v c () = dvExpectedVerdict mode v c ∧
    mrAuthority.verdict (mode, v, c) = dvExpectedVerdict mode v c :=
  ⟨dvAnnealEval_eq mode v c (), mrAuthority_verdict_eq mode v c⟩

/-- The frozen verdict table, pinned literally on all 16 `basic` keys and on
the mode-sensitive `protectedTB` key. -/
theorem dv_expected_verdict_table_pins :
    dvExpectedVerdict .basic .thinUnsize .okPrimary = some (.returns (.widePtr 1 0 16384)) ∧
    dvExpectedVerdict .basic .thinUnsize .okSecondary = some (.returns (.widePtr 5 1 16384)) ∧
    dvExpectedVerdict .basic .thinUnsize .ubFault = some .undefinedBehavior ∧
    dvExpectedVerdict .basic .thinUnsize .modeCase = some (.returns (.widePtr 1 0 16385)) ∧
    dvExpectedVerdict .basic .dynUpcastAndNop .okPrimary =
      some (.returns (.widePtr 1 0 16388)) ∧
    dvExpectedVerdict .basic .dynUpcastAndNop .okSecondary =
      some (.returns (.widePtr 1 0 16389)) ∧
    dvExpectedVerdict .basic .dynUpcastAndNop .ubFault = some .undefinedBehavior ∧
    dvExpectedVerdict .basic .dynUpcastAndNop .modeCase =
      some (.returns (.widePtr 5 1 16384)) ∧
    dvExpectedVerdict .basic .virtualDispatchAndProtector .okPrimary =
      some (.returns (.u32Val 2)) ∧
    dvExpectedVerdict .basic .virtualDispatchAndProtector .okSecondary =
      some (.returns (.u32Val 69)) ∧
    dvExpectedVerdict .basic .virtualDispatchAndProtector .ubFault = some .undefinedBehavior ∧
    dvExpectedVerdict .basic .virtualDispatchAndProtector .modeCase =
      some (.returns (.u32Val 77)) ∧
    dvExpectedVerdict .protectedTB .virtualDispatchAndProtector .modeCase =
      some .undefinedBehavior ∧
    dvExpectedVerdict .basic .dynLayoutRawBorrowAndAddrEq .okPrimary =
      some (.returns (.usizeVal 4)) ∧
    dvExpectedVerdict .basic .dynLayoutRawBorrowAndAddrEq .okSecondary =
      some (.returns (.boolVal 1)) ∧
    dvExpectedVerdict .basic .dynLayoutRawBorrowAndAddrEq .ubFault = some .undefinedBehavior ∧
    dvExpectedVerdict .basic .dynLayoutRawBorrowAndAddrEq .modeCase =
      some (.returns (.boolVal 0)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Re-exported MR certificates for all 4 variants (ensuring full transitive
reachability from this test module to every MR proof of this episode). -/
theorem dv_mr_all_4_variant_witnesses_linked :
    mrAuthority.denoteConsistent = true ∧
    mrSide.check dvModel = true ∧
    (∀ v, (mrVariantSide v).check dvModel = true) :=
  ⟨mrAuthority_denoteConsistent, mrSide_check, mrVariantSide_check⟩

/-- The universal laws, realizability witnesses, and three-way witnesses of
`MiniRustSpec.DynTraitVTableMR` are referenced from this module, together with
the directly observed Crubit `c16` mode sensitivity and the duplicate-free
observation dictionary. -/
theorem dv_mr_deep_theorems_used :
    (dvMrObserve .basicMemory .virtualDispatchAndProtector .modeCase =
      .retBytes ((scalarBytes u32 77).map (projByteTB ∘ liftByteTB))) ∧
    (dvMrObserve .treeBorrows .virtualDispatchAndProtector .modeCase = .ub) ∧
    dvMrObsDictDistinct = true ∧
    (dvAnnealEval .basic .dynUpcastAndNop .okPrimary () ≠
      dvAnnealEval .basic .dynUpcastAndNop .okSecondary ()) := by
  have _ := @dvVTables_layoutRel
  have _ := @dv_wfVTableEntry_minirust_valid_layout
  have _ := @dv_wfVTableEntry_minirust_valid_layout_nonvacuous
  have _ := @dv_dynSizeAlignOfVal_agrees_computeSizeAlign_M
  have _ := @dv_dynSizeAlignOfVal_agrees_computeSizeAlign_M_nonvacuous
  have _ := @dv_dynSizeAlignOfVal_fault_universal
  have _ := @dv_dynSizeAlignOfVal_fault_universal_nonvacuous
  have _ := @dv_v1_evalThinToDynUnsize_universal
  have _ := @dv_v1_evalThinToDynUnsize_universal_nonvacuous
  have _ := @dv_v1_raw_wide_ptr_checkPtrM_universal
  have _ := @dv_v1_raw_wide_ptr_checkPtrM_universal_nonvacuous
  have _ := @dv_dynRefDataValid_scalar_universal
  have _ := @dv_dynRefDataValid_scalar_universal_nonvacuous
  have _ := @dv_v1_null_ref_unsize_ub_universal_M
  have _ := @dv_v1_misaligned_ref_unsize_ub_universal_M
  have _ := @dv_v1_null_and_misaligned_ref_unsize_ub_universal_M_nonvacuous
  have _ := @dv_v3_evalVirtualCall_slot_universal
  have _ := @dv_v3_evalVirtualCall_slot_universal_nonvacuous
  have _ := @dv_v3_evalVirtualCall_linked_universal
  have _ := @dv_v3_evalVirtualCall_linked_universal_nonvacuous
  have _ := @dv_v3_vtableMethodLookup_universal_M
  have _ := @dv_v3_vtableMethodLookup_universal_M_nonvacuous
  have _ := @dvTrustedObserve_eq_run
  have _ := @dv_v3_trusted_dispatch_gates_witness
  have _ := @dv_v3_nonMethod_slot_ub_vs_minirust_specPanic
  have _ := @dv_v3_c16_callee_entry_matches_corpus_state
  have _ := @dv_v3_c16_trusted_same_body_flip_and_caller_equiv
  have _ := @dv_v3_virtualDispatch_three_way_witness
  have _ := @dv_v1_thinUnsize_three_way_witness
  have _ := @dv_v1_failClosed_boundary_witness
  have _ := @dv_v2_resolveUpcastVTable_diamond_witness
  have _ := @dv_v2_upcast_and_nop_three_way_witness
  have _ := @dv_v4_dynLayout_three_way_witness
  have _ := @dv_v4_rawBorrow_trusted_witness
  have _ := @dv_v4_wideCmp_addrEq_three_way_witness
  have _ := @dv_v1_ref_validity_vs_raw_trusted_witness
  have _ := @dv_v2_autoTrait_boundary_trusted_witness
  have _ := @dv_v3_pin_receiver_rewrap_trusted_witness
  have _ := @dv_vtableEnvOk_universal
  have _ := @dv_vtableEnvOk_universal_nonvacuous
  have _ := @dv_dynRefDataValid_scalar_32bit_universal
  have _ := @dv_v1_uninhabited_ub_universal_M
  have _ := @dv_v1_uninhabited_and_32bit_nonvacuous
  have _ := @dv_v2_evalDynToDynUnsize_universal
  have _ := @dv_v2_evalDynToDynUnsize_universal_nonvacuous
  have _ := @dv_dynRefDataValid_checkTB_false_perm_irrel
  have _ := @dv_checkDynVTablePtr_perm_irrel
  have _ := @dv_v4_evalSafeDynSizeAlignOfValCall_tb_irrel_universal
  have _ := @dv_v4_evalSafeDynSizeAlignOfValCall_nonvacuous
  have _ := @dv_v4_evalAddrEqCall_meta_irrel_universal
  have _ := @dv_v4_evalAddrEqCall_nonvacuous
  have _ := @dv_v3_linked_pin_receiver_protector_witness
  have _ := @dv_variant_outcomes_distinct
  have _ := @dvTrustedObserve_table
  have _ := @dvMrObserveClass_table
  exact ⟨dvMrObserve_c16_mode_sensitivity.1, dvMrObserve_c16_mode_sensitivity.2,
    dvMrObsDict_distinct, by decide +kernel⟩

/-- **Episode 2 Root Capstone**: for EVERY LeanMiri observation authority
`lmAuth` passing the unified 32-key check, the root-Lake projection of
`ep2_dyn_trait_vtable_capstone`: tight codec, consistent MiniRust authority,
the unified and all 4 per-variant MiniRust side checks, mode sensitivity on
both authorities, exact behavioral equivalence on both authorities, and
pairwise distinct MiniRust observation classes. The proof destructures the
bundle capstone and references the universal MiniRust laws of this episode, so
they are reachable from this theorem's proof. -/
theorem ep2_dyn_trait_vtable_root_capstone
    (lmAuth : Anneal.Mir.DropBinderAndSubtypeBundle.Corpus.ObsAuthority DynVtKey
      DynTraitVTableObs)
    (hLM : lmCheckOf lmAuth = true) :
    dvCodec.TightValidRep ∧
    mrAuthority.denoteConsistent = true ∧
    mrSide.check dvModel = true ∧
    (∀ v, (mrVariantSide v).check dvModel = true) ∧
    (mrSide.flipW dvModel mrSide_check).isSome = true ∧
    ((lmSideOf lmAuth).flipW dvModel hLM).isSome = true ∧
    (∀ (mMR : DynVtMrMode) (mLM : Bool) (p : DynVtVariant) (q : DynVtCase),
      ExactBehaviorEq (bundleOf lmAuth hLM).mrRel mMR p q ∧
      ExactBehaviorEq (bundleOf lmAuth hLM).lmRel mLM p q) ∧
    dvMrObsDictDistinct = true := by
  have _ := @dv_dynSizeAlignOfVal_agrees_computeSizeAlign_M
  have _ := @dv_v1_evalThinToDynUnsize_universal
  have _ := @dv_v1_raw_wide_ptr_checkPtrM_universal
  have _ := @dv_v3_evalVirtualCall_slot_universal
  have _ := @dv_v3_vtableMethodLookup_universal_M
  obtain ⟨hTight, hDen, hSide, hVar, _, _, hExact, hMrFlip, hLmFlip, _, _⟩ :=
    ep2_dyn_trait_vtable_capstone lmAuth hLM
  exact ⟨hTight, hDen, hSide, hVar, hMrFlip, hLmFlip, hExact, dvMrObsDict_distinct⟩

/-! ## §2. Cross-Root Dual-Authority Kernel Bridge (`MiniRustSpec` + `LeanMiriSpec`) -/

open Lean Elab Command Meta in
run_cmd do
  let opts := (← getOptions).setBool `Elab.async false
  let sp : SearchPath := [System.FilePath.mk ".lake/build/lib/lean",
                          System.FilePath.mk "examples/.lake/build/lib/lean"]
  initSearchPath (← findSysroot) sp
  let baseEnv ← importModules
    #[{ module := `Anneal.Mir.DynTraitVTableBundle },
      { module := `MiniRustSpec.DynTraitVTableMR },
      { module := `LeanMiriSpec.DynTraitVTableLM }]
    {} 0
  let ns := `Anneal.Mir.DynTraitVTableTests.CrossRoot
  let bNs := `Anneal.Mir.DynTraitVTableBundle
  let cNs := `Anneal.Mir.DropBinderAndSubtypeBundle.Corpus
  let mrNs := `MiniRustSpec.DynTraitVTableMR
  let lmNs := `LeanMiriSpec.DynTraitVTableLM
  let act : CoreM (Nat × Nat × Nat × Nat × Array Name) := do
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

    -- Helper encoders from DynVtVariant / DynVtCase to the Nat indices of `dvLmObserve`
    -- (`variantIdx`: thinUnsize = 0, dynUpcastAndNop = 1, virtualDispatchAndProtector = 2,
    -- dynLayoutRawBorrowAndAddrEq = 3; `caseIdx`: okPrimary = 0, okSecondary = 1, ubFault = 2,
    -- modeCase = 3).
    let mkVariantToNat (i0 i1 i2 i3 : Nat) : MetaM Expr := do
      let varTy := mkConst (mrNs ++ `DynVtVariant)
      withLocalDeclD `v varTy fun v => do
        let recApp := mkAppN (mkConst (mrNs ++ `DynVtVariant.rec) [1])
          #[mkLambda `x .default varTy natTy,
            mkNatLit i0, mkNatLit i1, mkNatLit i2, mkNatLit i3, v]
        mkLambdaFVars #[v] recApp
    let mkCaseToNat : MetaM Expr := do
      let caseTy := mkConst (mrNs ++ `DynVtCase)
      withLocalDeclD `c caseTy fun c => do
        let recApp := mkAppN (mkConst (mrNs ++ `DynVtCase.rec) [1])
          #[mkLambda `x .default caseTy natTy,
            mkNatLit 0, mkNatLit 1, mkNatLit 2, mkNatLit 3, c]
        mkLambdaFVars #[c] recApp

    let varToNatName := ns ++ `variantToNat
    let caseToNatName := ns ++ `caseToNat
    let _ ← addDef varToNatName (← MetaM.run' <| mkVariantToNat 0 1 2 3)
    let _ ← addDef caseToNatName (← MetaM.run' mkCaseToNat)
    -- The swapped encoder (`thinUnsize <-> dynUpcastAndNop`) used by a negative control only.
    let swappedVarToNat ← MetaM.run' <| mkVariantToNat 1 0 2 3

    -- 1. Build the genuine LeanMiri `ObsAuthority DynVtKey DynTraitVTableObs` directly over
    -- `LeanMiriSpec.DynTraitVTableLM.dvLmObserve`.
    let keyTy := mkConst (bNs ++ `DynVtKey)
    let obsValTy := mkConst (bNs ++ `DynTraitVTableObs)
    let lmObsTy := mkConst (lmNs ++ `DynVtLmObs)
    let mkLmAuth (invertMode : Bool := false) (collideDenote : Bool := false)
        (swapVariants : Bool := false) (swapUpcastDenote : Bool := false) : MetaM Expr := do
      let decLmObs := mkConst (lmNs ++ `instDecidableEqDynVtLmObs)
      let observeFn ← withLocalDeclD `k keyTy fun k => do
        let mExpr := mkProj ``Prod 0 k
        let rest := mkProj ``Prod 1 k
        let vExpr := mkProj ``Prod 0 rest
        let cExpr := mkProj ``Prod 1 rest
        let tb0 := mkApp (mkConst (bNs ++ `dvModeToLmTreeBorrows)) mExpr
        let tb := if invertMode then mkApp (mkConst ``Bool.not) tb0 else tb0
        let vNat := if swapVariants then mkApp swappedVarToNat vExpr
          else mkApp (mkConst varToNatName) vExpr
        let cNat := mkApp (mkConst caseToNatName) cExpr
        let call := mkApp3 (mkConst (lmNs ++ `dvLmObserve)) tb vNat cNat
        let someCall := mkApp2 (mkConst ``Option.some [0]) lmObsTy call
        mkLambdaFVars #[k] someCall
      let verdTy := mkApp (mkConst (cNs ++ `Verdict)) obsValTy
      let mkRet (v : Expr) : Expr := mkApp2 (mkConst (cNs ++ `Verdict.returns)) obsValTy v
      let mkPair (a b : Expr) : Expr := mkApp4 (mkConst ``Prod.mk [0, 0]) verdTy lmObsTy a b
      let mkU32V (n : Nat) : Expr :=
        mkRet (mkApp (mkConst (bNs ++ `DynTraitVTableObs.u32Val)) (mkNatLit n))
      let mkUsizeV (n : Nat) : Expr :=
        mkRet (mkApp (mkConst (bNs ++ `DynTraitVTableObs.usizeVal)) (mkNatLit n))
      let mkBoolV (n : Nat) : Expr :=
        mkRet (mkApp (mkConst (bNs ++ `DynTraitVTableObs.boolVal)) (mkNatLit n))
      let mkWideV (d o v : Nat) : Expr :=
        mkRet (mkApp3 (mkConst (bNs ++ `DynTraitVTableObs.widePtr))
          (mkNatLit d) (mkNatLit o) (mkNatLit v))
      let mkU32O (n : Nat) : Expr :=
        mkApp (mkConst (lmNs ++ `DynVtLmObs.u32Val)) (mkNatLit n)
      let mkUsizeO (n : Nat) : Expr :=
        mkApp (mkConst (lmNs ++ `DynVtLmObs.usizeVal)) (mkNatLit n)
      let mkBoolO (n : Nat) : Expr :=
        mkApp (mkConst (lmNs ++ `DynVtLmObs.boolVal)) (mkNatLit n)
      let mkWideO (d o v : Nat) : Expr :=
        mkApp3 (mkConst (lmNs ++ `DynVtLmObs.widePtr)) (mkNatLit d) (mkNatLit o) (mkNatLit v)
      let superO := if swapUpcastDenote then mkWideO 1 0 16389 else mkWideO 1 0 16388
      let sideO := if swapUpcastDenote then mkWideO 1 0 16388 else mkWideO 1 0 16389
      let entries : List Expr :=
        [ mkPair (mkWideV 1 0 16384) (mkWideO 1 0 16384),
          mkPair (mkWideV 5 1 16384) (mkWideO 5 1 16384),
          mkPair (mkWideV 1 0 16385)
            (if collideDenote then mkWideO 1 0 16384 else mkWideO 1 0 16385),
          mkPair (mkWideV 1 0 16388) superO,
          mkPair (mkWideV 1 0 16389) sideO,
          mkPair (mkU32V 2) (mkU32O 2),
          mkPair (mkU32V 69) (mkU32O 69),
          mkPair (mkU32V 77) (mkU32O 77),
          mkPair (mkUsizeV 4) (mkUsizeO 4),
          mkPair (mkBoolV 1) (mkBoolO 1),
          mkPair (mkBoolV 0) (mkBoolO 0),
          mkPair (mkApp (mkConst (cNs ++ `Verdict.undefinedBehavior)) obsValTy)
            (mkConst (lmNs ++ `DynVtLmObs.ub)),
          mkPair (mkApp (mkConst (cNs ++ `Verdict.unsupported)) obsValTy)
            (mkConst (lmNs ++ `DynVtLmObs.unsupported)) ]
      let pairTy := mkApp2 (mkConst ``Prod [0, 0]) verdTy lmObsTy
      let denoteList := entries.foldr (fun h t => mkApp3 (mkConst ``List.cons [0]) pairTy h t)
        (mkApp (mkConst ``List.nil [0]) pairTy)
      return mkApp6 (mkConst (cNs ++ `ObsAuthority.mk))
        keyTy obsValTy lmObsTy decLmObs observeFn denoteList

    let lmAuthName := ns ++ `lmAuthority
    let _ ← addDef lmAuthName (← MetaM.run' <| mkLmAuth false false false false)
    let lmAuthC := mkConst lmAuthName
    let mut added : Array Name := #[varToNatName, caseToNatName, lmAuthName]

    -- 2. Kernel-checked `denoteConsistent`, unified `lmSide_check`, and all 4 per-variant checks.
    let decObsVal := mkConst (bNs ++ `instDecidableEqDynTraitVTableObs)
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
    unless unifiedTy.getAppFn.isConstOf
        ``Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle do
      throwError "cross-root: {unifiedBundleName} is not a DualCorrespondenceBundle"
    added := added.push unifiedBundleName

    -- Instantiate lifted cross-authority theorems + projectPositive/projectFault at the closed
    -- unified dual-authority bundle.
    for thmName in [`threeWayNormalAgreement, `crossAuthorityFaultEquiv,
                    `exactBehaviorEq_both, `lm_modeSensitivity_present,
                    `ep2_dyn_trait_vtable_capstone] do
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

    -- The LeanMiri Crubit `c16` verdicts, re-checked by `Eq.refl` in this kernel environment
    -- (the positive counterparts of the forged protector verdict below).
    let lmObserveAt (tb : Bool) (v c : Nat) : Expr :=
      mkApp3 (mkConst (lmNs ++ `dvLmObserve)) (if tb then boolTrue else boolFalse)
        (mkNatLit v) (mkNatLit c)
    let lmUb := mkConst (lmNs ++ `DynVtLmObs.ub)
    let lmU32 (n : Nat) : Expr := mkApp (mkConst (lmNs ++ `DynVtLmObs.u32Val)) (mkNatLit n)
    addThm (ns ++ `lmC16ProtectedUb)
      (mkApp3 (mkConst ``Eq [1]) lmObsTy (lmObserveAt true 2 3) lmUb)
      (mkApp2 (mkConst ``Eq.refl [1]) lmObsTy lmUb)
    added := added.push (ns ++ `lmC16ProtectedUb)
    addThm (ns ++ `lmC16BasicReturns77)
      (mkApp3 (mkConst ``Eq [1]) lmObsTy (lmObserveAt false 2 3) (lmU32 77))
      (mkApp2 (mkConst ``Eq.refl [1]) lmObsTy (lmU32 77))
    added := added.push (ns ++ `lmC16BasicReturns77)

    -- All 4 per-variant bundles, claims, projectPositive, projectFault, & flip-direction guards.
    let variantCtors : List Name :=
      [`thinUnsize, `dynUpcastAndNop, `virtualDispatchAndProtector,
       `dynLayoutRawBorrowAndAddrEq]
    let mut bundleCount : Nat := 1
    for vc in variantCtors do
      let vConst := mkConst (mrNs ++ `DynVtVariant ++ vc)
      let chkName := ns ++ `variantCheck ++ vc
      addThm chkName (eqTrue (mkApp2 (mkConst (bNs ++ `lmVariantCheckOf)) vConst lmAuthC)) reflTrue
      added := added.push chkName
      let vbName := ns ++ `variantBundle ++ vc
      let vbTy ← addDef vbName
        (mkApp3 (mkConst (bNs ++ `variantBundleOf)) vConst lmAuthC (mkConst chkName))
      unless vbTy.getAppFn.isConstOf
          ``Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle do
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

    -- 3. Definitional `Eq.refl` fixture locks proving that the frozen vtable table, the
    -- virtual-method table, the callee table, and ALL `CapturedMir` fixtures and fixture
    -- families are definitionally IDENTICAL between `MiniRustSpec` and `LeanMiriSpec`.
    let capMirTy := mkConst `Trusted.Rustc.V2026_06_01.MirAst.CapturedMir
    let fixtureNames : List Name :=
      [ `dvVTables, `dvVirtualMethods, `dvCallees, `dvKeyInitSpec, `dvKeyCallees,
        `dvV1RefUnsizeMir, `dvV1RawUnsizeMir, `dvV1RefArgUnsizeMir, `dvV1MutUnsizeMir,
        `dvV1PinUnsizeMir, `dvV1ArgUnsizeMir, `dvV2UpcastMir, `dvV2UpcastSuperMir,
        `dvV2UpcastSideMir, `dvV2UpcastBaseMir, `dvV2UpcastAltMir, `dvV2NopRefMir,
        `dvV2NopRawMir, `dvGetU32Mir, `dvGetU64Mir, `dvPokeU32Mir, `dvV3CallU32Mir,
        `dvV3CallU64Mir, `dvV3CallOobMir, `dvV3CallHdrMir, `dvV3ArgCallMir,
        `dvRawGetU32Mir, `dvV3RawCallMir,
        `dvV3ProtectedPokeMir, `dvV3PokeCallerMir, `dvV4SizeSafeMir, `dvV4AlignSafeMir,
        `dvV4IntrLayoutMir, `dvV4RawBorrowMir, `dvV4WideCmpMir, `dvV4WideEqMir,
        `dvV4AddrEqMir ]
    let mut lockCount : Nat := 0
    for tag in fixtureNames do
      let lockName := ns ++ `fixtureLock ++ tag
      let lhs := mkConst (mrNs ++ tag)
      let rhs := mkConst (lmNs ++ tag)
      let ty ← MetaM.run' <| inferType lhs
      addThm lockName (mkApp3 (mkConst ``Eq [1]) ty lhs rhs)
        (mkApp2 (mkConst ``Eq.refl [1]) ty lhs)
      added := added.push lockName
      lockCount := lockCount + 1
    -- 3b. Per-key fixture, initial-state spec, and callee locks:
    --   * In `protectedTB` mode (`true`), ALL 16/16 keys — including Crubit `c16` (`(2, 3)` =
    --     `dvV3PokeCallerMir`) — satisfy `MR.dvTrustedFixture true v c = LM.dvLmFixture vi ci`
    --     by `Eq.refl`.
    --   * In `basic` mode (`false`), all 15 non-c16 keys satisfy `MR.dvTrustedFixture false v c =
    --     LM.dvLmFixture vi ci`, while `(false, 2, 3)` is pinned to `dvV3ProtectedPokeMir`
    --     (bridged to `dvV3PokeCallerMir` by `dv_v3_c16_callee_entry_matches_corpus_state`).
    --   * For ALL 16/16 keys, both `MR.dvKeyInitSpec vi ci = LM.dvKeyInitSpec vi ci` and
    --     `MR.dvKeyCallees vi ci = LM.dvKeyCallees vi ci` hold by `Eq.refl`.
    let caseCtors : List (Name × Nat) :=
      [(`okPrimary, 0), (`okSecondary, 1), (`ubFault, 2), (`modeCase, 3)]
    let variantPairs : List (Name × Nat) :=
      [(`thinUnsize, 0), (`dynUpcastAndNop, 1), (`virtualDispatchAndProtector, 2),
       (`dynLayoutRawBorrowAndAddrEq, 3)]
    for (vc, vi) in variantPairs do
      let vConst := mkConst (mrNs ++ `DynVtVariant ++ vc)
      for (cc, ci) in caseCtors do
        let cConst := mkConst (mrNs ++ `DynVtCase ++ cc)
        let mrFixTB := mkApp3 (mkConst (mrNs ++ `dvTrustedFixture)) boolTrue vConst cConst
        let mrFixBasic := mkApp3 (mkConst (mrNs ++ `dvTrustedFixture)) boolFalse vConst cConst
        let lmFix := mkApp2 (mkConst (lmNs ++ `dvLmFixture)) (mkNatLit vi) (mkNatLit ci)
        -- ProtectedTB body lock (16/16 identical, including c16!)
        let lockTB := ns ++ `keyLockTB ++ vc ++ cc
        addThm lockTB (mkApp3 (mkConst ``Eq [1]) capMirTy mrFixTB lmFix)
          (mkApp2 (mkConst ``Eq.refl [1]) capMirTy mrFixTB)
        added := added.push lockTB
        lockCount := lockCount + 1
        -- Basic body lock (15/16 identical + explicit c16 pin)
        if vi == 2 && ci == 3 then
          let lockBasic := ns ++ `keyLockBasic ++ `c16Trusted
          addThm lockBasic (mkApp3 (mkConst ``Eq [1]) capMirTy mrFixBasic
              (mkConst (mrNs ++ `dvV3ProtectedPokeMir)))
            (mkApp2 (mkConst ``Eq.refl [1]) capMirTy mrFixBasic)
          added := added.push lockBasic
          lockCount := lockCount + 1
        else
          let lockBasic := ns ++ `keyLockBasic ++ vc ++ cc
          addThm lockBasic (mkApp3 (mkConst ``Eq [1]) capMirTy mrFixBasic lmFix)
            (mkApp2 (mkConst ``Eq.refl [1]) capMirTy mrFixBasic)
          added := added.push lockBasic
          lockCount := lockCount + 1
        -- Per-key initial-state spec lock (16/16 identical)
        let mrSpec := mkApp2 (mkConst (mrNs ++ `dvKeyInitSpec)) (mkNatLit vi) (mkNatLit ci)
        let lmSpec := mkApp2 (mkConst (lmNs ++ `dvKeyInitSpec)) (mkNatLit vi) (mkNatLit ci)
        let specTy ← MetaM.run' <| inferType mrSpec
        let lockSpec := ns ++ `keyInitSpecLock ++ vc ++ cc
        addThm lockSpec (mkApp3 (mkConst ``Eq [1]) specTy mrSpec lmSpec)
          (mkApp2 (mkConst ``Eq.refl [1]) specTy mrSpec)
        added := added.push lockSpec
        lockCount := lockCount + 1
        -- Per-key callee list lock (16/16 identical)
        let mrCal := mkApp2 (mkConst (mrNs ++ `dvKeyCallees)) (mkNatLit vi) (mkNatLit ci)
        let lmCal := mkApp2 (mkConst (lmNs ++ `dvKeyCallees)) (mkNatLit vi) (mkNatLit ci)
        let calTy ← MetaM.run' <| inferType mrCal
        let lockCal := ns ++ `keyCalleeLock ++ vc ++ cc
        addThm lockCal (mkApp3 (mkConst ``Eq [1]) calTy mrCal lmCal)
          (mkApp2 (mkConst ``Eq.refl [1]) calTy mrCal)
        added := added.push lockCal
        lockCount := lockCount + 1
    unless lockCount = 101 do
      throwError "cross-root: expected 101 fixture/spec locks (37 named + 64 per-key), got {lockCount}"

    -- 4. Negative controls on scratch copies of the environment: the Lean kernel MUST reject
    -- every forged theorem, mode-inverted / variant-swapped authority, colliding or
    -- vtable-swapped denote table, swapped fixture lock, and forged protector verdict.
    let saved ← getEnv
    let rejects (d : Declaration) : CoreM Bool := do
      let r ← try addDecl d; pure false catch _ => pure true
      setEnv saved
      return r
    let invertedAuth ← MetaM.run' <| mkLmAuth true false false false
    let collidingAuth ← MetaM.run' <| mkLmAuth false true false false
    let swappedAuth ← MetaM.run' <| mkLmAuth false false true false
    let upcastSwappedAuth ← MetaM.run' <| mkLmAuth false false false true
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
        ("swapped fixture lock (`&T -> &dyn` != `*const T -> *const dyn`)", .thmDecl {
          name := ns ++ `forged.swappedFixture, levelParams := [],
          type := mkApp3 (mkConst ``Eq [1]) capMirTy
            (mkConst (mrNs ++ `dvV1RefUnsizeMir)) (mkConst (lmNs ++ `dvV1RawUnsizeMir)),
          value := mkApp2 (mkConst ``Eq.refl [1]) capMirTy
            (mkConst (mrNs ++ `dvV1RefUnsizeMir)) }),
        ("swapped fixture lock (u32 receiver != u64 receiver)", .thmDecl {
          name := ns ++ `forged.swappedReceiverFixture, levelParams := [],
          type := mkApp3 (mkConst ``Eq [1]) capMirTy
            (mkConst (mrNs ++ `dvV3CallU32Mir)) (mkConst (lmNs ++ `dvV3CallU64Mir)),
          value := mkApp2 (mkConst ``Eq.refl [1]) capMirTy
            (mkConst (mrNs ++ `dvV3CallU32Mir)) }),
        ("mode-inverted per-variant LM certificate (virtualDispatchAndProtector)", .thmDecl {
          name := ns ++ `forged.modeInvertedVirtualVariantCheck, levelParams := [],
          type := eqTrue (mkApp2 (mkConst (bNs ++ `lmVariantCheckOf))
            (mkConst (mrNs ++ `DynVtVariant.virtualDispatchAndProtector)) invertedAuth),
          value := reflTrue }),
        ("variant-swapped LM authority certificate (thinUnsize <-> dynUpcastAndNop)", .thmDecl {
          name := ns ++ `forged.variantSwappedLmCheck, levelParams := [],
          type := eqTrue (mkApp (mkConst (bNs ++ `lmCheckOf)) swappedAuth),
          value := reflTrue }),
        ("Super/Side vtable-swapped LM denote table (unified certificate)", .thmDecl {
          name := ns ++ `forged.upcastVTableSwappedLmCheck, levelParams := [],
          type := eqTrue (mkApp (mkConst (bNs ++ `lmCheckOf)) upcastSwappedAuth),
          value := reflTrue }),
        ("Super/Side vtable-swapped LM denote table (dynUpcastAndNop certificate)", .thmDecl {
          name := ns ++ `forged.upcastVTableSwappedVariantCheck, levelParams := [],
          type := eqTrue (mkApp2 (mkConst (bNs ++ `lmVariantCheckOf))
            (mkConst (mrNs ++ `DynVtVariant.dynUpcastAndNop)) upcastSwappedAuth),
          value := reflTrue }),
        ("forged LeanMiri verdict: Crubit c16 returns 77 under Tree Borrows", .thmDecl {
          name := ns ++ `forged.lmC16ProtectorIgnored, levelParams := [],
          type := mkApp3 (mkConst ``Eq [1]) lmObsTy (lmObserveAt true 2 3) (lmU32 77),
          value := mkApp2 (mkConst ``Eq.refl [1]) lmObsTy (lmU32 77) }),
        ("forged LeanMiri verdict: wrong-trait receiver vtable dispatches", .thmDecl {
          name := ns ++ `forged.lmWrongVTableDispatches, levelParams := [],
          type := mkApp3 (mkConst ``Eq [1]) lmObsTy (lmObserveAt false 2 2) (lmU32 2),
          value := mkApp2 (mkConst ``Eq.refl [1]) lmObsTy (lmU32 2) }),
        ("swapped per-key fixture lock (thinUnsize.okPrimary != thinUnsize.okSecondary)", .thmDecl {
          name := ns ++ `forged.swappedKeyLock, levelParams := [],
          type := mkApp3 (mkConst ``Eq [1]) capMirTy
            (mkApp3 (mkConst (mrNs ++ `dvTrustedFixture)) boolTrue
              (mkConst (mrNs ++ `DynVtVariant ++ `thinUnsize))
              (mkConst (mrNs ++ `DynVtCase ++ `okPrimary)))
            (mkApp2 (mkConst (lmNs ++ `dvLmFixture)) (mkNatLit 0) (mkNatLit 1)),
          value := mkApp2 (mkConst ``Eq.refl [1]) capMirTy
            (mkApp3 (mkConst (mrNs ++ `dvTrustedFixture)) boolTrue
              (mkConst (mrNs ++ `DynVtVariant ++ `thinUnsize))
              (mkConst (mrNs ++ `DynVtCase ++ `okPrimary))) }),
        ("forged basic-mode c16 key fixture identity (ProtectedPoke != PokeCaller)", .thmDecl {
          name := ns ++ `forged.c16FixtureConflation, levelParams := [],
          type := mkApp3 (mkConst ``Eq [1]) capMirTy
            (mkApp3 (mkConst (mrNs ++ `dvTrustedFixture)) boolFalse
              (mkConst (mrNs ++ `DynVtVariant ++ `virtualDispatchAndProtector))
              (mkConst (mrNs ++ `DynVtCase ++ `modeCase)))
            (mkApp2 (mkConst (lmNs ++ `dvLmFixture)) (mkNatLit 2) (mkNatLit 3)),
          value := mkApp2 (mkConst ``Eq.refl [1]) capMirTy
            (mkApp3 (mkConst (mrNs ++ `dvTrustedFixture)) boolFalse
              (mkConst (mrNs ++ `DynVtVariant ++ `virtualDispatchAndProtector))
              (mkConst (mrNs ++ `DynVtCase ++ `modeCase))) }),
        ("forged LM execution of a non-locked fixture at key (0, 0)", .thmDecl {
          name := ns ++ `forged.lmRunsUnlockedFixture, levelParams := [],
          type := mkApp3 (mkConst ``Eq [1]) lmObsTy (lmObserveAt false 0 0)
            (mkApp4 (mkConst (lmNs ++ `dvLmRun))
              (mkApp2 (mkConst (lmNs ++ `dvLmFixture)) (mkNatLit 0) (mkNatLit 1))
              (mkApp2 (mkConst (lmNs ++ `dvLmCallees)) (mkNatLit 0) (mkNatLit 0)) boolFalse
              (mkApp2 (mkConst (lmNs ++ `dvLmInit)) (mkNatLit 0) (mkNatLit 0))),
          value := mkApp2 (mkConst ``Eq.refl [1]) lmObsTy (lmObserveAt false 0 0) }),
        ("forged Trusted execution of a non-locked fixture at key (0, 0)", .thmDecl {
          name := ns ++ `forged.trustedRunsUnlockedFixture, levelParams := [],
          type :=
            let trObsTy := mkConst (mrNs ++ `DynVtTrustedObs)
            let v0 := mkConst (mrNs ++ `DynVtVariant ++ `thinUnsize)
            let c0 := mkConst (mrNs ++ `DynVtCase ++ `okPrimary)
            let c1 := mkConst (mrNs ++ `DynVtCase ++ `okSecondary)
            let lhs := mkApp3 (mkConst (mrNs ++ `dvTrustedObserve)) boolFalse v0 c0
            let rhs := mkApp3 (mkConst (mrNs ++ `dvRunTrusted))
              (mkApp3 (mkConst (mrNs ++ `dvTrustedFixture)) boolFalse v0 c1)
              (mkConst (mrNs ++ `dvTrustedFuel))
              (mkApp3 (mkConst (mrNs ++ `dvTrustedInit)) boolFalse v0 c0)
            mkApp3 (mkConst ``Eq [1]) trObsTy lhs rhs,
          value :=
            let trObsTy := mkConst (mrNs ++ `DynVtTrustedObs)
            let v0 := mkConst (mrNs ++ `DynVtVariant ++ `thinUnsize)
            let c0 := mkConst (mrNs ++ `DynVtCase ++ `okPrimary)
            mkApp2 (mkConst ``Eq.refl [1]) trObsTy
              (mkApp3 (mkConst (mrNs ++ `dvTrustedObserve)) boolFalse v0 c0) }),
        ("swapped per-key init-spec lock (disabled live (3,0) != frozen dead (3,2))", .thmDecl {
          name := ns ++ `forged.swappedInitSpecLock, levelParams := [],
          type :=
            let spTy := mkConst (mrNs ++ `DvKeyInitSpec)
            mkApp3 (mkConst ``Eq [1]) spTy
              (mkApp2 (mkConst (mrNs ++ `dvKeyInitSpec)) (mkNatLit 3) (mkNatLit 0))
              (mkApp2 (mkConst (lmNs ++ `dvKeyInitSpec)) (mkNatLit 3) (mkNatLit 2)),
          value :=
            let spTy := mkConst (mrNs ++ `DvKeyInitSpec)
            mkApp2 (mkConst ``Eq.refl [1]) spTy
              (mkApp2 (mkConst (mrNs ++ `dvKeyInitSpec)) (mkNatLit 3) (mkNatLit 0)) }) ]
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
    -- Verify the LM conservative-extension law, the vtable / method-slot / dynamic-layout
    -- agreement laws, their realizability witnesses, and the table theorems are present,
    -- non-trivial, and axiom-clean.
    let lmDeepThms : List Name :=
      [ lmNs ++ `dvAssign_conservative,
        lmNs ++ `dvTerminator_conservative,
        lmNs ++ `step_dynTraitVTable_overlay_conservative,
        lmNs ++ `dvFor_hooks_eq,
        lmNs ++ `dvKeyIdx_eq_iff,
        lmNs ++ `dvVTableEntries_method_iff,
        lmNs ++ `dvVTableEntries_not_method,
        lmNs ++ `dv_vtableEnvOk_allocId_bounds,
        lmNs ++ `dvRegistryLookup_eq_lookupVTableByAllocId,
        lmNs ++ `dvCheckForTypeRead_eq,
        lmNs ++ `dvGetPtrVTableTypeRead_eq,
        lmNs ++ `dvVTablePtrCheck_eq_trusted,
        lmNs ++ `dv_checkDynVTablePtr_found,
        lmNs ++ `dvVTablePtrCheck_agrees_checkDynVTablePtr,
        lmNs ++ `dvGetSizeAndAlignRead_eq,
        lmNs ++ `dvSizeAndAlignFromMeta_eq,
        lmNs ++ `dvSizeAlign_agrees_trusted_entry,
        lmNs ++ `dv_wfVTableEntry_align,
        lmNs ++ `dv_resolveUpcastVTable_eq_lookupVTableFor,
        lmNs ++ `dvGetMethod_eq,
        lmNs ++ `dvGetMethod_nonMethod_ub,
        lmNs ++ `dvRegistryReserve_eq_lookupVTableFor,
        lmNs ++ `dvGetPointer_eq,
        lmNs ++ `dvPtrCouples_iff_dvDecodePtr,
        lmNs ++ `dvUnsizeIntoPointer_thin_agrees_trusted,
        lmNs ++ `dvUnsizeIntoPointer_dynToDyn_agrees_trusted,
        lmNs ++ `dvResolveVirtual_agrees_trusted,
        lmNs ++ `dvResolveVirtual_safeRef_agrees_trusted,
        lmNs ++ `dvLmObserve_v1_thinUnsize_table,
        lmNs ++ `dvLmObserve_v2_dynUpcastAndNop_table,
        lmNs ++ `dvLmObserve_v3_virtualDispatchAndProtector_table,
        lmNs ++ `dvLmObserve_v4_dynLayoutRawBorrowAndAddrEq_table,
        lmNs ++ `dvLmObserve_all_32_table,
        lmNs ++ `dvLmObserve_c16_mode_sensitivity,
        lmNs ++ `dvLmObserve_out_of_range,
        lmNs ++ `dvLmObserve_eq_run,
        lmNs ++ `dvLmInit_c16,
        lmNs ++ `dv_table_hypotheses_realizable,
        lmNs ++ `dv_table_laws_instances,
        lmNs ++ `dv_conservative_law_realizable,
        lmNs ++ `dv_vtable_check_agreement_realizable,
        lmNs ++ `dv_getMethod_realizable,
        lmNs ++ `dv_unsize_agrees_realizable,
        lmNs ++ `dv_dynToDyn_agrees_realizable,
        lmNs ++ `dv_resolveVirtual_agrees_realizable,
        lmNs ++ `dv_resolveVirtual_safeRef_agrees_realizable,
        lmNs ++ `dv_extra_witnesses,
        lmNs ++ `dv_c16_witnesses,
        lmNs ++ `dv_kani5216_uninhabited_witness,
        lmNs ++ `dv_c2_tb_unsize_and_raw_mut_witness,
        lmNs ++ `dv_c3_and_raw_intrinsics_witness,
        lmNs ++ `dv_pin_adt_unsize_and_dispatch_from_dyn_witness ]
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
    let closure (root : Name) : NameSet := Id.run do
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
    let reach := closure unifiedBundleName
    let requiredReach : List Name :=
      [ `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalUnsizeCoercion,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalThinToDynUnsize,
        `Trusted.Rustc.V2026_06_01.MirSemantics.checkDynVTablePtr,
        `Trusted.Rustc.V2026_06_01.MirSemantics.resolveUpcastVTable?,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalVirtualCall,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalDynSizeAlignOfVal,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalAddrEqCall,
        `MiniRustSpec.Interp.steps,
        `MiniRustSpec.Interp.stepsTB,
        `MiniRustSpec.DynTraitVTableMR.dvRunTrusted,
        `MiniRustSpec.DynTraitVTableMR.dvMrObserve,
        `MiniRustSpec.DynTraitVTableMR.dvTrustedObserve_table,
        `MiniRustSpec.DynTraitVTableMR.dvMrObserveClass_table,
        `Miri.Interpreter.Step.step,
        `Miri.Interpreter.Cast.cast,
        `Miri.Interpreter.Cast.unsizeInto,
        `Miri.Interpreter.Cast.unsizeIntoPointer,
        `Miri.Interpreter.VTable.getPtrVTableType,
        `Miri.Interpreter.VTable.getPtrVTableTypeRead,
        `Miri.Interpreter.VTable.getPointer,
        `Miri.Interpreter.VTable.checkForTypeRead,
        `Miri.Interpreter.VTableMachine.Registry,
        `Miri.Interpreter.VTable.getSizeAndAlignRead,
        `Miri.Interpreter.VirtualCalls.resolveVirtual,
        `Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta,
        `LeanMiriSpec.DynTraitVTableLM.dvLmObserve,
        `LeanMiriSpec.DynTraitVTableLM.dvLmFixture,
        `LeanMiriSpec.DynTraitVTableLM.dvLmCallees,
        `LeanMiriSpec.DynTraitVTableLM.dvLmInit,
        `LeanMiriSpec.DynTraitVTableLM.dvKeyInitSpec,
        `LeanMiriSpec.DynTraitVTableLM.dvKeyCallees,
        `MiniRustSpec.DynTraitVTableMR.dvTrustedFixture,
        `MiniRustSpec.DynTraitVTableMR.dvTrustedInit,
        `MiniRustSpec.DynTraitVTableMR.dvKeyInitSpec,
        `MiniRustSpec.DynTraitVTableMR.dvKeyCallees,
        `LeanMiriSpec.DynTraitVTableLM.annealStepHooksDynTraitVTableFor ]
    for req in requiredReach do
      unless (env.find? req).isSome do
        throwError "cross-root reachability failure: {req} does not exist"
      unless reach.contains req do
        throwError "cross-root reachability failure: unifiedDualBundle does not reach {req}"
    -- The vendored trait-predicate normalization `VTable.sortedPredicates` is a private
    -- definition of module `Miri.Interpreter.VTable`; it must be reached under its private name.
    let sortedPreds := Lean.mkPrivateNameCore `Miri.Interpreter.VTable
      `Miri.Interpreter.VTable.sortedPredicates
    unless (env.find? sortedPreds).isSome && reach.contains sortedPreds do
      throwError "cross-root reachability failure: unifiedDualBundle does not reach {sortedPreds}"
    -- Self-test of the reachability check: a fixture that no corpus key runs must NOT be
    -- reachable from the bundle.
    if reach.contains (mrNs ++ `dvV1PinUnsizeMir) then
      throwError "cross-root self-test: reachability over-approximates (dvV1PinUnsizeMir reached)"
    -- The production virtual-call pipeline (`VirtualCalls.resolveVirtual`, reached above)
    -- selects the method slot inline; the checked utility `VTable.getMethod` is executed by
    -- the LM method-selection witness and related to the same slot table by `dvGetMethod_eq`.
    for root in [lmNs ++ `dv_getMethod_realizable, lmNs ++ `dvGetMethod_eq,
                 lmNs ++ `dvGetMethod_nonMethod_ub] do
      unless (closure root).contains `Miri.Interpreter.VTable.getMethod do
        throwError "cross-root reachability failure: {root} does not reach VTable.getMethod"

    return (added.size, bundleCount, lockCount, rejected, crAxioms.toArray)

  let ctx : Core.Context :=
    { fileName := "<dv-cross-root>", fileMap := default, options := opts, maxHeartbeats := 0 }
  let ((addedCount, bundleCount, lockCount, rejectedCount, crAxioms), _) ←
    liftCoreM <| act.toIO ctx { env := baseEnv }
  unless addedCount = 136 && bundleCount = 5 && lockCount = 101 && rejectedCount = 17 do
    throwError "cross-root: unexpected counts (added={addedCount}, bundles={bundleCount}, locks={lockCount}, rejected={rejectedCount})"
  logInfo m!"dv cross-root kernel bridge: added {addedCount} declarations ({bundleCount} bundles, {lockCount} fixture/spec locks), rejected {rejectedCount} forged controls, reached Trusted+MiniRust+Miri, axioms {crAxioms}"

end Anneal.Mir.DynTraitVTableTests

/-! ## §3. `V2026_06_01` ↔ `V2026_08_01` Dialect Homomorphism (Condition `C7`) -/

namespace Anneal.Mir.DynTraitVTableTests.Hom

/-!
## Condition C7: `V2026_06_01 ↔ V2026_08_01` dialect homomorphism for the `dyn` fragment

Structural embeddings `hom* : V2026_08_01 → V2026_06_01` (constructor-for-constructor,
field-for-field) for `UintTy`, `IntTy`, `FloatTy`, `Mutability`, `Safety`, `CallConv`,
`RigidTy`, `CapturedVTableSlot`, `CapturedVTable`, `CapturedDynType`, `ScalarInt`,
`ProvenancePtr`, `Value`, `DynUnsizeTarget`, `DynReceiverKind`, and `DynCheck`.

Universal commuting & injectivity theorems (∀ inputs of the 08 dialect):
`homTy_injective`, `homSlot_injective`, `homVTable_injective`, `homValue_injective`,
`wfVTableEntry_hom`, `resolveUpcastVTable?_hom`, `dynUnsizeTarget?_hom`,
`classifyDynReceiver?_hom`, `narrowDynReceiver_hom`, `unpackDynReceiver?_hom`,
`dynRefDataValid_scalar_hom`
(arbitrary pointer width, including 32-bit and `kani#5216` uninhabited checks), plus the
supporting lemmas (`rigidTyEqAux_hom_both`, the lookup lemmas, `OptBodyRel`-generalized
`dynVTableEnv?_opt_hom` and `checkDynVTablePtr_opt_hom` covering both `currentBody = .none`
and `currentBody = .some _`, `evalThinToDynUnsize_raw_hom`, `defPathsSubset_hom`, and
`evalDynToDynUnsize_raw_hom` covering NOP, primary/secondary `TraitVPtr` upcasting, and
auto-trait subset checks).

Relational theorems: `evalDynSizeAlignOfVal_hom` (under `DynMemRel` + equal pointer width) and
`evalAddrEqCall_hom` (under `AddrRel` + equal pointer width) state that both dialects take the
SAME `DynStepClass` (`.ub` / `.unsupported` / intrinsic return of the same scalar). Every
relation and hypothesis is realized by concrete witnesses (`wState_dynMemRel`,
`wBare_dynMemRel`, `wBody_optBodyRel`, `wLayouts_ptrBytes`, `wState_addrRel`,
`addrRel_of_no_borrows`, `addrRel_of_root_borrows`, `wBorrowState_addrRel`), and every
outcome class is realized in both dialects (`evalDynSizeAlignOfVal_witness_*`,
`evalAddrEqCall_witness_*`, `checkDynVTablePtr_opt_witness`,
`evalThinToDynUnsize_raw_witness_32bit_64bit`,
`dynRefDataValid_scalar_witness_32bit_uninhabited`, `witness_written_values`).

Scope and dialect differences (none of them is a divergence on the `dyn` fragment):
- `V2026_06_01.MirSemantics.Value` has the extra constructor `.uninit`, outside the image of
  `homValue` (`homValue_ne_uninit`); on 06-only `.uninit` arguments the 06 dialect faults `.ub`
  (fall-through arms of `evalDynSizeAlignOfVal`, `ptrArgDataWord?`, `checkDynVTablePtr`).
- `V2026_06_01.Layout.TypeLayout` has the extra field `variantDiscriminants`; the `dyn`
  operations consult a `LayoutTable` only through `layoutPointerBytes`, hence the equal pointer
  width hypothesis instead of a `LayoutTable` embedding.
- `evalAddrEqCall` resolves data words with the non-`dyn` resolver `ptrAddress?` (frame locals,
  borrow base addresses, `LocalDecl` layouts); its agreement is the hypothesis `AddrRel`, proven
  for empty borrow tables (`addrRel_of_no_borrows`) and arbitrary non-empty root-local borrow
  tables (`addrRel_of_root_borrows`, realized by `wBorrowState_addrRel` with two distinct tags
  aliasing the same local `_1`), leaving only non-empty sub-place projection chains out of scope.
- `V2026_08_01` additionally defines `initProtectedReborrowPerm` (function-entry Tree Borrows
  retag), which is not consulted by any `dyn` operation.
-/

/-! ## Structural embeddings `V2026_08_01 → V2026_06_01` -/

/-- `UintTy` embedding. -/
def homUint : Trusted.Rustc.V2026_08_01.MirAst.UintTy → Trusted.Rustc.V2026_06_01.MirAst.UintTy
  | .u8 => .u8 | .u16 => .u16 | .u32 => .u32 | .u64 => .u64 | .u128 => .u128 | .usize => .usize

/-- `IntTy` embedding. -/
def homInt : Trusted.Rustc.V2026_08_01.MirAst.IntTy → Trusted.Rustc.V2026_06_01.MirAst.IntTy
  | .i8 => .i8 | .i16 => .i16 | .i32 => .i32 | .i64 => .i64 | .i128 => .i128 | .isize => .isize

/-- `FloatTy` embedding. -/
def homFloat : Trusted.Rustc.V2026_08_01.MirAst.FloatTy → Trusted.Rustc.V2026_06_01.MirAst.FloatTy
  | .f16 => .f16 | .f32 => .f32 | .f64 => .f64 | .f128 => .f128

/-- `Mutability` embedding. -/
def homMut : Trusted.Rustc.V2026_08_01.MirAst.Mutability → Trusted.Rustc.V2026_06_01.MirAst.Mutability
  | .not => .not | .mut => .mut

/-- `Safety` embedding. -/
def homSafety : Trusted.Rustc.V2026_08_01.MirAst.Safety → Trusted.Rustc.V2026_06_01.MirAst.Safety
  | .safe => .safe | .unsafe_ => .unsafe_

/-- `CallConv` embedding. -/
def homCallConv : Trusted.Rustc.V2026_08_01.Layout.CallConv → Trusted.Rustc.V2026_06_01.Layout.CallConv
  | .rust => .rust | .c => .c | .rustIntrinsic => .rustIntrinsic | .other s => .other s

mutual
/-- `RigidTy` embedding (constructor-for-constructor). -/
def homTy : Trusted.Rustc.V2026_08_01.MirAst.RigidTy → Trusted.Rustc.V2026_06_01.MirAst.RigidTy
  | .param i n => .param i n
  | .alias d as => .alias d (homTys as)
  | .bool => .bool
  | .char => .char
  | .int w => .int (homInt w)
  | .uint w => .uint (homUint w)
  | .float w => .float (homFloat w)
  | .never => .never
  | .str => .str
  | .tuple fs => .tuple (homTys fs)
  | .array e n => .array (homTy e) n
  | .slice e => .slice (homTy e)
  | .ref m p => .ref (homMut m) (homTy p)
  | .rawPtr m p => .rawPtr (homMut m) (homTy p)
  | .adt d as => .adt d (homTys as)
  | .fnDef d as => .fnDef d (homTys as)
  | .fnPtr ins out s abi => .fnPtr (homTys ins) (homTy out) (homSafety s) (homCallConv abi)
  | .closure d ups => .closure d (homTys ups)
  | .dynamic k => .dynamic k
  | .foreign d => .foreign d
  | .other r => .other r
/-- Pointwise `RigidTy` embedding on lists. -/
def homTys : List Trusted.Rustc.V2026_08_01.MirAst.RigidTy → List Trusted.Rustc.V2026_06_01.MirAst.RigidTy
  | [] => []
  | t :: ts => homTy t :: homTys ts
end

/-- `CapturedVTableSlot` embedding. -/
def homSlot : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTableSlot → Trusted.Rustc.V2026_06_01.MirAst.CapturedVTableSlot
  | .dropInPlace d => .dropInPlace d
  | .size => .size
  | .align => .align
  | .vacant => .vacant
  | .method p as => .method p (homTys as)
  | .unmodeledMethod => .unmodeledMethod
  | .traitVPtr i => .traitVPtr i

/-- `CapturedVTable` embedding (field-for-field). -/
def homVTable (v : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) : Trusted.Rustc.V2026_06_01.MirAst.CapturedVTable :=
  { vtableId := v.vtableId, vtableAllocId := v.vtableAllocId, concreteTy := homTy v.concreteTy,
    dynKey := v.dynKey, sizeBytes := v.sizeBytes, alignBytes := v.alignBytes,
    isUninhabited := v.isUninhabited, primarySuperVTableId? := v.primarySuperVTableId?,
    extraSuperVTableIds := v.extraSuperVTableIds, slots := v.slots.map homSlot }

/-- `CapturedDynType` embedding (field-for-field). -/
def homDynType (d : Trusted.Rustc.V2026_08_01.MirAst.CapturedDynType) : Trusted.Rustc.V2026_06_01.MirAst.CapturedDynType :=
  { dynKey := d.dynKey, predicateKey := d.predicateKey, principalTrait? := d.principalTrait?,
    typeArgs := homTys d.typeArgs, assocBindings := d.assocBindings.map (fun b => (b.1, homTy b.2)),
    autoTraits := d.autoTraits, hasUnresolvedExistentialBinder := d.hasUnresolvedExistentialBinder,
    supertraitOutlivesOk := d.supertraitOutlivesOk }

/-- `ScalarInt` embedding. -/
def homScalar (s : Trusted.Rustc.V2026_08_01.MirAst.ScalarInt) : Trusted.Rustc.V2026_06_01.MirAst.ScalarInt := { bits := s.bits, sizeBytes := s.sizeBytes }

/-- `ProvenancePtr` embedding. -/
def homPtr (p : Trusted.Rustc.V2026_08_01.MirAst.ProvenancePtr) : Trusted.Rustc.V2026_06_01.MirAst.ProvenancePtr :=
  { allocId := p.allocId, offsetBytes := p.offsetBytes }

mutual
/-- `Value` embedding. Its image misses exactly `Trusted.Rustc.V2026_06_01.MirSemantics.Value.uninit` (`homValue_ne_uninit`). -/
def homValue : Trusted.Rustc.V2026_08_01.MirSemantics.Value → Trusted.Rustc.V2026_06_01.MirSemantics.Value
  | .unit => .unit
  | .scalar s => .scalar (homScalar s)
  | .ptr p n => .ptr (homPtr p) n
  | .aggregate i fs => .aggregate i (homValues fs)
/-- Pointwise `Value` embedding on lists. -/
def homValues : List Trusted.Rustc.V2026_08_01.MirSemantics.Value → List Trusted.Rustc.V2026_06_01.MirSemantics.Value
  | [] => []
  | v :: vs => homValue v :: homValues vs
end

/-- `DynUnsizeTarget` embedding. -/
def homDUT : Trusted.Rustc.V2026_08_01.MirSemantics.DynUnsizeTarget → Trusted.Rustc.V2026_06_01.MirSemantics.DynUnsizeTarget
  | .ref m k => .ref (homMut m) k
  | .raw m k => .raw (homMut m) k
  | .pinRef m k => .pinRef (homMut m) k
  | .unmodeled => .unmodeled

/-- `DynReceiverKind` embedding. -/
def homDRK : Trusted.Rustc.V2026_08_01.MirSemantics.DynReceiverKind → Trusted.Rustc.V2026_06_01.MirSemantics.DynReceiverKind
  | .ref m => .ref (homMut m)
  | .raw m => .raw (homMut m)
  | .pinRef m => .pinRef (homMut m)

/-! ## Injectivity of the structural embeddings (no dialect-08 terms are collapsed) -/

theorem homUint_injective {a b : Trusted.Rustc.V2026_08_01.MirAst.UintTy} (h : homUint a = homUint b) : a = b := by
  cases a <;> cases b <;> cases h <;> rfl

theorem homInt_injective {a b : Trusted.Rustc.V2026_08_01.MirAst.IntTy} (h : homInt a = homInt b) : a = b := by
  cases a <;> cases b <;> cases h <;> rfl

theorem homFloat_injective {a b : Trusted.Rustc.V2026_08_01.MirAst.FloatTy} (h : homFloat a = homFloat b) : a = b := by
  cases a <;> cases b <;> cases h <;> rfl

theorem homMut_injective {a b : Trusted.Rustc.V2026_08_01.MirAst.Mutability} (h : homMut a = homMut b) : a = b := by
  cases a <;> cases b <;> cases h <;> rfl

theorem homSafety_injective {a b : Trusted.Rustc.V2026_08_01.MirAst.Safety} (h : homSafety a = homSafety b) : a = b := by
  cases a <;> cases b <;> cases h <;> rfl

theorem homCallConv_injective {a b : Trusted.Rustc.V2026_08_01.Layout.CallConv} (h : homCallConv a = homCallConv b) : a = b := by
  cases a <;> cases b <;> cases h <;> rfl

mutual
/-- `homTy` is injective: no distinct `V2026_08_01.MirAst.RigidTy` values collapse. -/
theorem homTy_injective : ∀ {a b : Trusted.Rustc.V2026_08_01.MirAst.RigidTy}, homTy a = homTy b → a = b
  | a, b, h => by
    cases a <;> cases b <;> simp [homTy] at h
    all_goals try rfl
    · rcases h with ⟨h1, h2⟩; rw [h1, h2]
    · rcases h with ⟨h1, h2⟩; rw [h1, homTys_injective h2]
    · rw [homInt_injective h]
    · rw [homUint_injective h]
    · rw [homFloat_injective h]
    · rw [homTys_injective h]
    · rcases h with ⟨h1, h2⟩; rw [homTy_injective h1, h2]
    · rw [homTy_injective h]
    · rcases h with ⟨h1, h2⟩; rw [homMut_injective h1, homTy_injective h2]
    · rcases h with ⟨h1, h2⟩; rw [homMut_injective h1, homTy_injective h2]
    · rcases h with ⟨h1, h2⟩; rw [h1, homTys_injective h2]
    · rcases h with ⟨h1, h2⟩; rw [h1, homTys_injective h2]
    · rcases h with ⟨h1, h2, h3, h4⟩
      rw [homTys_injective h1, homTy_injective h2, homSafety_injective h3, homCallConv_injective h4]
    · rcases h with ⟨h1, h2⟩; rw [h1, homTys_injective h2]
    · rw [h]
    · rw [h]
    · rw [h]

theorem homTys_injective : ∀ {as bs : List Trusted.Rustc.V2026_08_01.MirAst.RigidTy}, homTys as = homTys bs → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp [homTys] at h
    rcases h with ⟨h1, h2⟩
    rw [homTy_injective h1, homTys_injective h2]
  | [], _ :: _, h => by simp [homTys] at h
  | _ :: _, [], h => by simp [homTys] at h
end

/-- `homSlot` is injective. -/
theorem homSlot_injective {a b : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTableSlot}
    (h : homSlot a = homSlot b) : a = b := by
  cases a <;> cases b <;> simp [homSlot] at h
  all_goals try rfl
  · rw [h]
  · rcases h with ⟨h1, h2⟩; rw [h1, homTys_injective h2]
  · rw [h]

private theorem list_map_injective {α β : Type} {f : α → β} (hf : ∀ {x y}, f x = f y → x = y) :
    ∀ {xs ys : List α}, xs.map f = ys.map f → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp at h
    rcases h with ⟨h1, h2⟩
    rw [hf h1, list_map_injective hf h2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- `homVTable` is injective. -/
theorem homVTable_injective {a b : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable}
    (h : homVTable a = homVTable b) : a = b := by
  cases a; cases b
  simp [homVTable] at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  rw [h1, h2, homTy_injective h3, h4, h5, h6, h7, h8, h9, list_map_injective homSlot_injective h10]

theorem homScalar_injective {a b : Trusted.Rustc.V2026_08_01.MirAst.ScalarInt}
    (h : homScalar a = homScalar b) : a = b := by
  cases a; cases b; cases h; rfl

theorem homPtr_injective {a b : Trusted.Rustc.V2026_08_01.MirAst.ProvenancePtr}
    (h : homPtr a = homPtr b) : a = b := by
  cases a; cases b; cases h; rfl

mutual
/-- `homValue` is injective. -/
theorem homValue_injective : ∀ {a b : Trusted.Rustc.V2026_08_01.MirSemantics.Value}, homValue a = homValue b → a = b
  | a, b, h => by
    cases a <;> cases b <;> simp [homValue] at h
    all_goals try rfl
    · rw [homScalar_injective h]
    · rcases h with ⟨h1, h2⟩; rw [homPtr_injective h1, h2]
    · rcases h with ⟨h1, h2⟩; rw [h1, homValues_injective h2]

theorem homValues_injective : ∀ {as bs : List Trusted.Rustc.V2026_08_01.MirSemantics.Value}, homValues as = homValues bs → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp [homValues] at h
    rcases h with ⟨h1, h2⟩
    rw [homValue_injective h1, homValues_injective h2]
  | [], _ :: _, h => by simp [homValues] at h
  | _ :: _, [], h => by simp [homValues] at h
end

/-! ## Basic commuting lemmas -/

theorem listByteEq_hom : ∀ xs ys : List UInt8, Trusted.Rustc.V2026_06_01.MirSemantics.listByteEq xs ys = Trusted.Rustc.V2026_08_01.MirSemantics.listByteEq xs ys
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    cases h : Nat.beq x.toBitVec.toNat y.toBitVec.toNat <;>
      simp only [Trusted.Rustc.V2026_06_01.MirSemantics.listByteEq, Trusted.Rustc.V2026_08_01.MirSemantics.listByteEq, h, listByteEq_hom xs ys]

theorem stringEq_hom (a b : String) : Trusted.Rustc.V2026_06_01.MirSemantics.stringEq a b = Trusted.Rustc.V2026_08_01.MirSemantics.stringEq a b := by
  simp only [Trusted.Rustc.V2026_06_01.MirSemantics.stringEq, Trusted.Rustc.V2026_08_01.MirSemantics.stringEq, listByteEq_hom]

theorem homTys_eq_map : ∀ ts : List Trusted.Rustc.V2026_08_01.MirAst.RigidTy, homTys ts = ts.map homTy
  | [] => rfl
  | t :: ts => by simp [homTys, homTys_eq_map ts]

theorem intTyEq_hom (a b : Trusted.Rustc.V2026_08_01.MirAst.IntTy) : Trusted.Rustc.V2026_06_01.MirSemantics.intTyEq (homInt a) (homInt b) = Trusted.Rustc.V2026_08_01.MirSemantics.intTyEq a b := by
  cases a <;> cases b <;> rfl

theorem uintTyEq_hom (a b : Trusted.Rustc.V2026_08_01.MirAst.UintTy) : Trusted.Rustc.V2026_06_01.MirSemantics.uintTyEq (homUint a) (homUint b) = Trusted.Rustc.V2026_08_01.MirSemantics.uintTyEq a b := by
  cases a <;> cases b <;> rfl

theorem floatTyEq_hom (a b : Trusted.Rustc.V2026_08_01.MirAst.FloatTy) :
    Trusted.Rustc.V2026_06_01.MirSemantics.floatTyEq (homFloat a) (homFloat b) = Trusted.Rustc.V2026_08_01.MirSemantics.floatTyEq a b := by
  cases a <;> cases b <;> rfl

theorem mutabilityEq_hom (a b : Trusted.Rustc.V2026_08_01.MirAst.Mutability) :
    Trusted.Rustc.V2026_06_01.MirSemantics.mutabilityEq (homMut a) (homMut b) = Trusted.Rustc.V2026_08_01.MirSemantics.mutabilityEq a b := by
  cases a <;> cases b <;> rfl

theorem safetyEq_hom (a b : Trusted.Rustc.V2026_08_01.MirAst.Safety) : Trusted.Rustc.V2026_06_01.MirSemantics.safetyEq (homSafety a) (homSafety b) = Trusted.Rustc.V2026_08_01.MirSemantics.safetyEq a b := by
  cases a <;> cases b <;> rfl

theorem callConvEq_hom (a b : Trusted.Rustc.V2026_08_01.Layout.CallConv) :
    Trusted.Rustc.V2026_06_01.MirSemantics.callConvEq (homCallConv a) (homCallConv b) = Trusted.Rustc.V2026_08_01.MirSemantics.callConvEq a b := by
  cases a <;> cases b <;> simp only [homCallConv, Trusted.Rustc.V2026_06_01.MirSemantics.callConvEq, Trusted.Rustc.V2026_08_01.MirSemantics.callConvEq, stringEq_hom]

/-- Fuel-bounded structural `RigidTy` equality commutes with the embedding, at every fuel. -/
theorem rigidTyEqAux_hom_both (n : Nat) :
    (∀ a b : Trusted.Rustc.V2026_08_01.MirAst.RigidTy, Trusted.Rustc.V2026_06_01.MirSemantics.rigidTyEqAux n (homTy a) (homTy b) = Trusted.Rustc.V2026_08_01.MirSemantics.rigidTyEqAux n a b) ∧
    (∀ as bs : List Trusted.Rustc.V2026_08_01.MirAst.RigidTy,
      Trusted.Rustc.V2026_06_01.MirSemantics.rigidTyListEqAux n (homTys as) (homTys bs) = Trusted.Rustc.V2026_08_01.MirSemantics.rigidTyListEqAux n as bs) := by
  induction n with
  | zero =>
    exact ⟨fun a b => by cases a <;> rfl, fun as bs => by cases as <;> cases bs <;> rfl⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have h1 : ∀ a b : Trusted.Rustc.V2026_08_01.MirAst.RigidTy,
        Trusted.Rustc.V2026_06_01.MirSemantics.rigidTyEqAux (n + 1) (homTy a) (homTy b) = Trusted.Rustc.V2026_08_01.MirSemantics.rigidTyEqAux (n + 1) a b := by
      intro a b
      cases a <;> cases b <;>
        first
        | rfl
        | simp only [homTy, Trusted.Rustc.V2026_06_01.MirSemantics.rigidTyEqAux, Trusted.Rustc.V2026_08_01.MirSemantics.rigidTyEqAux, ih1, ih2, intTyEq_hom, uintTyEq_hom,
            floatTyEq_hom, mutabilityEq_hom, safetyEq_hom, callConvEq_hom, stringEq_hom]
    refine ⟨h1, ?_⟩
    intro as
    induction as with
    | nil => intro bs; cases bs <;> rfl
    | cons a as iha =>
      intro bs
      cases bs with
      | nil => rfl
      | cons b bs =>
        show Bool.and (Trusted.Rustc.V2026_06_01.MirSemantics.rigidTyEqAux (n + 1) (homTy a) (homTy b))
            (Trusted.Rustc.V2026_06_01.MirSemantics.rigidTyListEqAux (n + 1) (homTys as) (homTys bs)) =
          Bool.and (Trusted.Rustc.V2026_08_01.MirSemantics.rigidTyEqAux (n + 1) a b) (Trusted.Rustc.V2026_08_01.MirSemantics.rigidTyListEqAux (n + 1) as bs)
        rw [h1 a b, iha bs]

theorem rigidTyEq_hom (a b : Trusted.Rustc.V2026_08_01.MirAst.RigidTy) : Trusted.Rustc.V2026_06_01.MirSemantics.rigidTyEq (homTy a) (homTy b) = Trusted.Rustc.V2026_08_01.MirSemantics.rigidTyEq a b :=
  (rigidTyEqAux_hom_both 16).1 a b

theorem rigidTyListEq_hom (as bs : List Trusted.Rustc.V2026_08_01.MirAst.RigidTy) :
    Trusted.Rustc.V2026_06_01.MirSemantics.rigidTyListEq (homTys as) (homTys bs) = Trusted.Rustc.V2026_08_01.MirSemantics.rigidTyListEq as bs :=
  (rigidTyEqAux_hom_both 16).2 as bs

theorem homVTable_vtableId (v : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) : (homVTable v).vtableId = v.vtableId := rfl
theorem homVTable_vtableAllocId (v : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) :
    (homVTable v).vtableAllocId = v.vtableAllocId := rfl
theorem homVTable_concreteTy (v : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) :
    (homVTable v).concreteTy = homTy v.concreteTy := rfl
theorem homVTable_dynKey (v : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) : (homVTable v).dynKey = v.dynKey := rfl
theorem homVTable_sizeBytes (v : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) : (homVTable v).sizeBytes = v.sizeBytes := rfl
theorem homVTable_alignBytes (v : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) :
    (homVTable v).alignBytes = v.alignBytes := rfl
theorem homVTable_isUninhabited (v : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) :
    (homVTable v).isUninhabited = v.isUninhabited := rfl
theorem homVTable_primarySuperVTableId? (v : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) :
    (homVTable v).primarySuperVTableId? = v.primarySuperVTableId? := rfl
theorem homVTable_extraSuperVTableIds (v : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) :
    (homVTable v).extraSuperVTableIds = v.extraSuperVTableIds := rfl
theorem homVTable_slots (v : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) : (homVTable v).slots = v.slots.map homSlot := rfl
theorem homDynType_dynKey (d : Trusted.Rustc.V2026_08_01.MirAst.CapturedDynType) : (homDynType d).dynKey = d.dynKey := rfl
theorem homDynType_predicateKey (d : Trusted.Rustc.V2026_08_01.MirAst.CapturedDynType) :
    (homDynType d).predicateKey = d.predicateKey := rfl
theorem homDynType_autoTraits (d : Trusted.Rustc.V2026_08_01.MirAst.CapturedDynType) :
    (homDynType d).autoTraits = d.autoTraits := rfl
theorem homDynType_hasUnresolvedExistentialBinder (d : Trusted.Rustc.V2026_08_01.MirAst.CapturedDynType) :
    (homDynType d).hasUnresolvedExistentialBinder = d.hasUnresolvedExistentialBinder := rfl
theorem homDynType_supertraitOutlivesOk (d : Trusted.Rustc.V2026_08_01.MirAst.CapturedDynType) :
    (homDynType d).supertraitOutlivesOk = d.supertraitOutlivesOk := rfl

/-! ## C7 universal commuting theorems: `wfVTableEntry`, `dynUnsizeTarget?`,
`classifyDynReceiver?`, `narrowDynReceiver` -/

/-- **C7** `wfVTableEntry` commutes with the embedding (every pointer width, every vtable). -/
theorem wfVTableEntry_hom (ptrBytes : Nat) (v : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) :
    Trusted.Rustc.V2026_06_01.MirSemantics.wfVTableEntry ptrBytes (homVTable v) = Trusted.Rustc.V2026_08_01.MirSemantics.wfVTableEntry ptrBytes v := by
  obtain ⟨id, aid, ty, k, sz, al, un, ps, es, slots⟩ := v
  simp only [Trusted.Rustc.V2026_06_01.MirSemantics.wfVTableEntry, Trusted.Rustc.V2026_08_01.MirSemantics.wfVTableEntry, homVTable, Trusted.Rustc.V2026_06_01.MirSemantics.isPowerOfTwoNat, Trusted.Rustc.V2026_08_01.MirSemantics.isPowerOfTwoNat]
  rcases slots with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rfl
  · cases a <;> rfl
  · cases a <;> cases b <;> rfl
  · cases a <;> cases b <;> cases c <;> rfl

theorem isPinDefPath_hom (p : String) : Trusted.Rustc.V2026_06_01.MirSemantics.isPinDefPath p = Trusted.Rustc.V2026_08_01.MirSemantics.isPinDefPath p := by
  simp only [Trusted.Rustc.V2026_06_01.MirSemantics.isPinDefPath, Trusted.Rustc.V2026_08_01.MirSemantics.isPinDefPath, stringEq_hom]

/-- **C7** `dynUnsizeTarget?` commutes with the embedding (every `RigidTy`). -/
theorem dynUnsizeTarget?_hom (t : Trusted.Rustc.V2026_08_01.MirAst.RigidTy) :
    Trusted.Rustc.V2026_06_01.MirSemantics.dynUnsizeTarget? (homTy t) = (Trusted.Rustc.V2026_08_01.MirSemantics.dynUnsizeTarget? t).map homDUT := by
  cases t
  all_goals try rfl
  case ref m p => cases p <;> rfl
  case rawPtr m p => cases p <;> rfl
  case adt d args =>
    match args with
    | [] => rfl
    | [x] =>
      cases x
      all_goals try rfl
      case ref m p =>
        cases p
        all_goals try rfl
        case dynamic k =>
          simp only [homTy, homTys, Trusted.Rustc.V2026_06_01.MirSemantics.dynUnsizeTarget?, Trusted.Rustc.V2026_08_01.MirSemantics.dynUnsizeTarget?, isPinDefPath_hom]
          cases Trusted.Rustc.V2026_08_01.MirSemantics.isPinDefPath d <;> rfl
    | x :: y :: rest =>
      cases x
      all_goals try rfl
      case ref m p => cases p <;> rfl

/-- **C7** `classifyDynReceiver?` commutes with the embedding (every `RigidTy`). -/
theorem classifyDynReceiver?_hom (t : Trusted.Rustc.V2026_08_01.MirAst.RigidTy) :
    Trusted.Rustc.V2026_06_01.MirSemantics.classifyDynReceiver? (homTy t) = (Trusted.Rustc.V2026_08_01.MirSemantics.classifyDynReceiver? t).map (fun r => (homDRK r.1, r.2)) := by
  cases t
  all_goals try rfl
  case ref m p => cases p <;> rfl
  case rawPtr m p => cases p <;> rfl
  case adt d args =>
    match args with
    | [] => rfl
    | [x] =>
      cases x
      all_goals try rfl
      case ref m p =>
        cases p
        all_goals try rfl
        case dynamic k =>
          simp only [homTy, homTys, Trusted.Rustc.V2026_06_01.MirSemantics.classifyDynReceiver?, Trusted.Rustc.V2026_08_01.MirSemantics.classifyDynReceiver?, isPinDefPath_hom]
          cases Trusted.Rustc.V2026_08_01.MirSemantics.isPinDefPath d <;> rfl
    | x :: y :: rest =>
      cases x
      all_goals try rfl
      case ref m p => cases p <;> rfl

/-- **C7** `narrowDynReceiver` commutes with the embedding (every receiver kind and value). -/
theorem narrowDynReceiver_hom (k : Trusted.Rustc.V2026_08_01.MirSemantics.DynReceiverKind) (v : Trusted.Rustc.V2026_08_01.MirSemantics.Value) :
    Trusted.Rustc.V2026_06_01.MirSemantics.narrowDynReceiver (homDRK k) (homValue v) = homValue (Trusted.Rustc.V2026_08_01.MirSemantics.narrowDynReceiver k v) := by
  cases k <;> rfl

/-- `DynCheck (Value × Value)` embedding for `unpackDynReceiver?`. -/
def homDynCheckPair :
    Trusted.Rustc.V2026_08_01.MirSemantics.DynCheck
        (Trusted.Rustc.V2026_08_01.MirSemantics.Value × Trusted.Rustc.V2026_08_01.MirSemantics.Value) →
      Trusted.Rustc.V2026_06_01.MirSemantics.DynCheck
        (Trusted.Rustc.V2026_06_01.MirSemantics.Value × Trusted.Rustc.V2026_06_01.MirSemantics.Value)
  | .ok (d, m) => .ok (homValue d, homValue m)
  | .ub => .ub
  | .unsupported => .unsupported

/-- **C7** `unpackDynReceiver?` commutes with the embedding for EVERY `DynReceiverKind`
(`.ref`, `.raw`, `.pinRef`) and EVERY value of the 08 dialect (including nested `Pin`
aggregates, malformed `.pinRef` values returning `.unsupported`, and malformed `.ref`/`.raw`
values returning `.ub`). -/
theorem unpackDynReceiver?_hom (k : Trusted.Rustc.V2026_08_01.MirSemantics.DynReceiverKind)
    (v : Trusted.Rustc.V2026_08_01.MirSemantics.Value) :
    Trusted.Rustc.V2026_06_01.MirSemantics.unpackDynReceiver? (homDRK k) (homValue v) =
      homDynCheckPair (Trusted.Rustc.V2026_08_01.MirSemantics.unpackDynReceiver? k v) := by
  cases k with
  | ref _ | raw _ =>
    rcases v with _ | _ | _ | ⟨i, fs⟩
    · rfl
    · rfl
    · rfl
    · rcases i with _ | i
      · rcases fs with _ | ⟨d, _ | ⟨m, _ | ⟨x, rest⟩⟩⟩ <;> rfl
      · rfl
  | pinRef _ =>
    rcases v with _ | _ | _ | ⟨i, fs⟩
    · rfl
    · rfl
    · rfl
    · rcases i with _ | i
      · rcases fs with _ | ⟨inner, _ | ⟨y, rest⟩⟩
        · rfl
        · rcases inner with _ | _ | _ | ⟨j, gs⟩
          · rfl
          · rfl
          · rfl
          · rcases j with _ | j
            · rcases gs with _ | ⟨d, _ | ⟨m, _ | ⟨x, rest'⟩⟩⟩ <;> rfl
            · rfl
        · rcases inner with _ | _ | _ | ⟨j, gs⟩
          · rfl
          · rfl
          · rfl
          · rcases j with _ | j
            · rcases gs with _ | ⟨d, _ | ⟨m, _ | ⟨x, rest'⟩⟩⟩ <;> rfl
            · rfl
      · rfl

/-- The only `Trusted.Rustc.V2026_06_01.MirSemantics.Value` constructor outside the embedding's image is `.uninit`. -/
theorem homValue_ne_uninit (v : Trusted.Rustc.V2026_08_01.MirSemantics.Value) : homValue v ≠ Trusted.Rustc.V2026_06_01.MirSemantics.Value.uninit := by
  cases v <;> simp [homValue]

/-! ## Lookup lemmas -/

theorem lookupVTableById_hom (vts : List Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) (i : Nat) :
    Trusted.Rustc.V2026_06_01.MirSemantics.lookupVTableById (vts.map homVTable) i = (Trusted.Rustc.V2026_08_01.MirSemantics.lookupVTableById vts i).map homVTable := by
  induction vts with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, Trusted.Rustc.V2026_06_01.MirSemantics.lookupVTableById, Trusted.Rustc.V2026_08_01.MirSemantics.lookupVTableById, homVTable_vtableId]
    cases Nat.beq v.vtableId i <;> simp only [ih, Option.map_some]

theorem lookupVTableByAllocId_hom (vts : List Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) (a : Nat) :
    Trusted.Rustc.V2026_06_01.MirSemantics.lookupVTableByAllocId (vts.map homVTable) a =
      (Trusted.Rustc.V2026_08_01.MirSemantics.lookupVTableByAllocId vts a).map homVTable := by
  induction vts with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, Trusted.Rustc.V2026_06_01.MirSemantics.lookupVTableByAllocId, Trusted.Rustc.V2026_08_01.MirSemantics.lookupVTableByAllocId,
      homVTable_vtableAllocId]
    cases Nat.beq v.vtableAllocId a <;> simp only [ih, Option.map_some]

theorem lookupVTableFor_hom (vts : List Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) (t : Trusted.Rustc.V2026_08_01.MirAst.RigidTy) (k : String) :
    Trusted.Rustc.V2026_06_01.MirSemantics.lookupVTableFor (vts.map homVTable) (homTy t) k =
      (Trusted.Rustc.V2026_08_01.MirSemantics.lookupVTableFor vts t k).map homVTable := by
  induction vts with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, Trusted.Rustc.V2026_06_01.MirSemantics.lookupVTableFor, Trusted.Rustc.V2026_08_01.MirSemantics.lookupVTableFor, homVTable_dynKey,
      homVTable_concreteTy, stringEq_hom, rigidTyEq_hom]
    cases Bool.and (Trusted.Rustc.V2026_08_01.MirSemantics.stringEq v.dynKey k) (Trusted.Rustc.V2026_08_01.MirSemantics.rigidTyEq v.concreteTy t) <;>
      simp only [ih, Option.map_some]

theorem lookupDynType_hom (dts : List Trusted.Rustc.V2026_08_01.MirAst.CapturedDynType) (k : String) :
    Trusted.Rustc.V2026_06_01.MirSemantics.lookupDynType (dts.map homDynType) k = (Trusted.Rustc.V2026_08_01.MirSemantics.lookupDynType dts k).map homDynType := by
  induction dts with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.map_cons, Trusted.Rustc.V2026_06_01.MirSemantics.lookupDynType, Trusted.Rustc.V2026_08_01.MirSemantics.lookupDynType, homDynType_dynKey, stringEq_hom]
    cases Trusted.Rustc.V2026_08_01.MirSemantics.stringEq d.dynKey k <;> simp only [ih, Option.map_some]

theorem dynPredicateKeyOf_hom (dts : List Trusted.Rustc.V2026_08_01.MirAst.CapturedDynType) (k : String) :
    Trusted.Rustc.V2026_06_01.MirSemantics.dynPredicateKeyOf (dts.map homDynType) k = Trusted.Rustc.V2026_08_01.MirSemantics.dynPredicateKeyOf dts k := by
  simp only [Trusted.Rustc.V2026_06_01.MirSemantics.dynPredicateKeyOf, Trusted.Rustc.V2026_08_01.MirSemantics.dynPredicateKeyOf, lookupDynType_hom]
  cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupDynType dts k <;> rfl

theorem dynKeysCompatible_hom (dts : List Trusted.Rustc.V2026_08_01.MirAst.CapturedDynType) (a b : String) :
    Trusted.Rustc.V2026_06_01.MirSemantics.dynKeysCompatible (dts.map homDynType) a b = Trusted.Rustc.V2026_08_01.MirSemantics.dynKeysCompatible dts a b := by
  simp only [Trusted.Rustc.V2026_06_01.MirSemantics.dynKeysCompatible, Trusted.Rustc.V2026_08_01.MirSemantics.dynKeysCompatible, dynPredicateKeyOf_hom, stringEq_hom]

theorem dynTypeModeled_hom (dts : List Trusted.Rustc.V2026_08_01.MirAst.CapturedDynType) (k : String) :
    Trusted.Rustc.V2026_06_01.MirSemantics.dynTypeModeled (dts.map homDynType) k = Trusted.Rustc.V2026_08_01.MirSemantics.dynTypeModeled dts k := by
  simp only [Trusted.Rustc.V2026_06_01.MirSemantics.dynTypeModeled, Trusted.Rustc.V2026_08_01.MirSemantics.dynTypeModeled, lookupDynType_hom]
  cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupDynType dts k <;> rfl

theorem vtableDirectSuperIds_hom (v : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) :
    Trusted.Rustc.V2026_06_01.MirSemantics.vtableDirectSuperIds (homVTable v) = Trusted.Rustc.V2026_08_01.MirSemantics.vtableDirectSuperIds v := by
  obtain ⟨id, aid, ty, k, sz, al, un, ps, es, slots⟩ := v
  cases ps
  · simp only [Trusted.Rustc.V2026_06_01.MirSemantics.vtableDirectSuperIds, Trusted.Rustc.V2026_08_01.MirSemantics.vtableDirectSuperIds, homVTable]
    congr 1
    induction slots with
    | nil => rfl
    | cons s ss ih => cases s <;> simp only [List.map_cons, List.foldr_cons, homSlot, ih]
  · simp only [Trusted.Rustc.V2026_06_01.MirSemantics.vtableDirectSuperIds, Trusted.Rustc.V2026_08_01.MirSemantics.vtableDirectSuperIds, homVTable]
    congr 2
    induction slots with
    | nil => rfl
    | cons s ss ih => cases s <;> simp only [List.map_cons, List.foldr_cons, homSlot, ih]

theorem vtableSuperLinkCount_hom (vts : List Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) :
    Trusted.Rustc.V2026_06_01.MirSemantics.vtableSuperLinkCount (vts.map homVTable) = Trusted.Rustc.V2026_08_01.MirSemantics.vtableSuperLinkCount vts := by
  simp only [Trusted.Rustc.V2026_06_01.MirSemantics.vtableSuperLinkCount, Trusted.Rustc.V2026_08_01.MirSemantics.vtableSuperLinkCount, List.foldl_map,
    vtableDirectSuperIds_hom]

theorem vtableReachesSuperKeyAux_hom (vts : List Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) (dts : List Trusted.Rustc.V2026_08_01.MirAst.CapturedDynType)
    (k : String) (fuel : Nat) (work visited : List Nat) :
    Trusted.Rustc.V2026_06_01.MirSemantics.vtableReachesSuperKeyAux (vts.map homVTable) (dts.map homDynType) k fuel work visited =
      Trusted.Rustc.V2026_08_01.MirSemantics.vtableReachesSuperKeyAux vts dts k fuel work visited := by
  induction fuel generalizing work visited with
  | zero => rfl
  | succ n ih =>
    cases work with
    | nil => rfl
    | cons c rest =>
      simp only [Trusted.Rustc.V2026_06_01.MirSemantics.vtableReachesSuperKeyAux, Trusted.Rustc.V2026_08_01.MirSemantics.vtableReachesSuperKeyAux]
      cases visited.any (fun v => Nat.beq v c)
      · simp only [lookupVTableById_hom]
        cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupVTableById vts c with
        | none => simp only [Option.map_none, ih]
        | some cur =>
          simp only [Option.map_some, homVTable_dynKey, dynKeysCompatible_hom]
          cases Trusted.Rustc.V2026_08_01.MirSemantics.dynKeysCompatible dts cur.dynKey k
          · simp only [vtableDirectSuperIds_hom, ih]
          · rfl
      · simp only [ih]

/-- **C7** `resolveUpcastVTable?` commutes with the embedding (every vtable table, `dyn`
descriptor table, source vtable, and target key). -/
theorem resolveUpcastVTable?_hom (vts : List Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) (dts : List Trusted.Rustc.V2026_08_01.MirAst.CapturedDynType)
    (src : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) (k : String) :
    Trusted.Rustc.V2026_06_01.MirSemantics.resolveUpcastVTable? (vts.map homVTable) (dts.map homDynType) (homVTable src) k =
      (Trusted.Rustc.V2026_08_01.MirSemantics.resolveUpcastVTable? vts dts src k).map homVTable := by
  simp only [Trusted.Rustc.V2026_06_01.MirSemantics.resolveUpcastVTable?, Trusted.Rustc.V2026_08_01.MirSemantics.resolveUpcastVTable?, homVTable_dynKey,
    dynKeysCompatible_hom, vtableDirectSuperIds_hom, vtableSuperLinkCount_hom,
    vtableReachesSuperKeyAux_hom, homVTable_concreteTy]
  cases Bool.or (Trusted.Rustc.V2026_08_01.MirSemantics.dynKeysCompatible dts src.dynKey k)
      (Trusted.Rustc.V2026_08_01.MirSemantics.vtableReachesSuperKeyAux vts dts k
        (Nat.add (Nat.add (Trusted.Sequence.length (Trusted.Rustc.V2026_08_01.MirSemantics.vtableDirectSuperIds src))
          (Trusted.Rustc.V2026_08_01.MirSemantics.vtableSuperLinkCount vts)) 1) (Trusted.Rustc.V2026_08_01.MirSemantics.vtableDirectSuperIds src) []) with
  | false => rfl
  | true => simp only [lookupVTableFor_hom]

/-! ## Vtable-environment lemmas -/

theorem optNatBEq_hom (a b : Option Nat) : Trusted.Rustc.V2026_06_01.MirSemantics.optNatBEq a b = Trusted.Rustc.V2026_08_01.MirSemantics.optNatBEq a b := by
  cases a <;> cases b <;> rfl

theorem natListBEq_hom : ∀ a b : List Nat, Trusted.Rustc.V2026_06_01.MirSemantics.natListBEq a b = Trusted.Rustc.V2026_08_01.MirSemantics.natListBEq a b
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by simp only [Trusted.Rustc.V2026_06_01.MirSemantics.natListBEq, Trusted.Rustc.V2026_08_01.MirSemantics.natListBEq, natListBEq_hom xs ys]

theorem capturedVTableSlotBEq_hom (a b : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTableSlot) :
    Trusted.Rustc.V2026_06_01.MirSemantics.capturedVTableSlotBEq (homSlot a) (homSlot b) = Trusted.Rustc.V2026_08_01.MirSemantics.capturedVTableSlotBEq a b := by
  rcases a with (_ | x) | _ | _ | _ | ⟨p1, a1⟩ | _ | i1 <;>
    rcases b with (_ | y) | _ | _ | _ | ⟨p2, a2⟩ | _ | i2 <;>
    first
    | rfl
    | simp only [homSlot, Trusted.Rustc.V2026_06_01.MirSemantics.capturedVTableSlotBEq, Trusted.Rustc.V2026_08_01.MirSemantics.capturedVTableSlotBEq, stringEq_hom,
        rigidTyListEq_hom]

theorem capturedVTableSlotListBEq_hom :
    ∀ a b : List Trusted.Rustc.V2026_08_01.MirAst.CapturedVTableSlot,
      Trusted.Rustc.V2026_06_01.MirSemantics.capturedVTableSlotListBEq (a.map homSlot) (b.map homSlot) =
        Trusted.Rustc.V2026_08_01.MirSemantics.capturedVTableSlotListBEq a b
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [List.map_cons, Trusted.Rustc.V2026_06_01.MirSemantics.capturedVTableSlotListBEq, Trusted.Rustc.V2026_08_01.MirSemantics.capturedVTableSlotListBEq,
      capturedVTableSlotBEq_hom, capturedVTableSlotListBEq_hom xs ys]

theorem capturedVTableBEq_hom (a b : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) :
    Trusted.Rustc.V2026_06_01.MirSemantics.capturedVTableBEq (homVTable a) (homVTable b) = Trusted.Rustc.V2026_08_01.MirSemantics.capturedVTableBEq a b := by
  simp only [Trusted.Rustc.V2026_06_01.MirSemantics.capturedVTableBEq, Trusted.Rustc.V2026_08_01.MirSemantics.capturedVTableBEq, homVTable_vtableId, homVTable_vtableAllocId,
    homVTable_concreteTy, homVTable_dynKey, homVTable_sizeBytes, homVTable_alignBytes,
    homVTable_isUninhabited, homVTable_primarySuperVTableId?, homVTable_extraSuperVTableIds,
    homVTable_slots, rigidTyEq_hom, stringEq_hom, optNatBEq_hom, natListBEq_hom,
    capturedVTableSlotListBEq_hom]

theorem vtablesAgreeWith_hom (acc vs : List Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) :
    Trusted.Rustc.V2026_06_01.MirSemantics.vtablesAgreeWith (acc.map homVTable) (vs.map homVTable) = Trusted.Rustc.V2026_08_01.MirSemantics.vtablesAgreeWith acc vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, Trusted.Rustc.V2026_06_01.MirSemantics.vtablesAgreeWith, Trusted.Rustc.V2026_08_01.MirSemantics.vtablesAgreeWith, ih,
      homVTable_vtableAllocId, lookupVTableByAllocId_hom]
    cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupVTableByAllocId acc v.vtableAllocId <;>
      simp only [Option.map_none, Option.map_some, capturedVTableBEq_hom]

theorem dedupVTablesInto_hom (acc vs : List Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) :
    Trusted.Rustc.V2026_06_01.MirSemantics.dedupVTablesInto (acc.map homVTable) (vs.map homVTable) =
      (Trusted.Rustc.V2026_08_01.MirSemantics.dedupVTablesInto acc vs).map homVTable := by
  induction vs generalizing acc with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, Trusted.Rustc.V2026_06_01.MirSemantics.dedupVTablesInto, Trusted.Rustc.V2026_08_01.MirSemantics.dedupVTablesInto, homVTable_vtableAllocId,
      lookupVTableByAllocId_hom]
    cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupVTableByAllocId acc v.vtableAllocId with
    | none =>
      have := ih (acc ++ v :: [])
      simp only [List.map_append, List.map_cons, List.map_nil] at this
      simpa only [Option.map_none] using this
    | some _ => simpa only [Option.map_some] using ih acc

/-- Dyn-relevant relation between two linked-callee tables: the per-body vtable and `dyn`
descriptor tables correspond under the embedding (no other body component is constrained). -/
structure BodiesRel (bs6 : List Trusted.Rustc.V2026_06_01.MirAst.CapturedMir) (bs8 : List Trusted.Rustc.V2026_08_01.MirAst.CapturedMir) : Prop where
  vtables : bs6.map (·.vtables) = bs8.map (fun b => b.vtables.map homVTable)
  dynTypes : bs6.map (·.dynTypes) = bs8.map (fun b => b.dynTypes.map homDynType)

/-- Dyn-relevant relation between two optional current bodies (`.none` for the intrinsic path
or `.some b6 / .some b8` for the virtual-call and safe `size_of_val` paths). -/
inductive OptBodyRel :
    Option Trusted.Rustc.V2026_06_01.MirAst.CapturedMir →
    Option Trusted.Rustc.V2026_08_01.MirAst.CapturedMir → Prop where
  | none : OptBodyRel .none .none
  | some (b6 : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir)
         (b8 : Trusted.Rustc.V2026_08_01.MirAst.CapturedMir)
         (hvt : b6.vtables = b8.vtables.map homVTable)
         (hdt : b6.dynTypes = b8.dynTypes.map homDynType) :
         OptBodyRel (.some b6) (.some b8)

theorem dynSourceBodies_rel
    {cb6 : Option Trusted.Rustc.V2026_06_01.MirAst.CapturedMir}
    {cb8 : Option Trusted.Rustc.V2026_08_01.MirAst.CapturedMir}
    (hcb : OptBodyRel cb6 cb8)
    {bs6 : List Trusted.Rustc.V2026_06_01.MirAst.CapturedMir}
    {bs8 : List Trusted.Rustc.V2026_08_01.MirAst.CapturedMir}
    (hbs : BodiesRel bs6 bs8) :
    BodiesRel
      (Trusted.Rustc.V2026_06_01.MirSemantics.dynSourceBodies cb6 bs6)
      (Trusted.Rustc.V2026_08_01.MirSemantics.dynSourceBodies cb8 bs8) := by
  cases hcb with
  | none => exact hbs
  | some b6 b8 hvt hdt =>
    refine ⟨?_, ?_⟩
    · simp only [Trusted.Rustc.V2026_06_01.MirSemantics.dynSourceBodies,
        Trusted.Rustc.V2026_08_01.MirSemantics.dynSourceBodies, List.map_cons, hvt, hbs.vtables]
    · simp only [Trusted.Rustc.V2026_06_01.MirSemantics.dynSourceBodies,
        Trusted.Rustc.V2026_08_01.MirSemantics.dynSourceBodies, List.map_cons, hdt, hbs.dynTypes]

/-- `collectBodyVTables` as a fold over the projected vtable tables (dialect 06). -/
theorem collectBodyVTables_eq6 (cb : Option Trusted.Rustc.V2026_06_01.MirAst.CapturedMir)
    (bs : List Trusted.Rustc.V2026_06_01.MirAst.CapturedMir) :
    Trusted.Rustc.V2026_06_01.MirSemantics.collectBodyVTables cb bs =
      List.foldl Trusted.Rustc.V2026_06_01.MirSemantics.dedupVTablesInto []
        ((Trusted.Rustc.V2026_06_01.MirSemantics.dynSourceBodies cb bs).map (·.vtables)) := by
  simp only [Trusted.Rustc.V2026_06_01.MirSemantics.collectBodyVTables, List.foldl_map]

/-- `collectBodyVTables` as a fold over the projected vtable tables (dialect 08). -/
theorem collectBodyVTables_eq8 (cb : Option Trusted.Rustc.V2026_08_01.MirAst.CapturedMir)
    (bs : List Trusted.Rustc.V2026_08_01.MirAst.CapturedMir) :
    Trusted.Rustc.V2026_08_01.MirSemantics.collectBodyVTables cb bs =
      List.foldl Trusted.Rustc.V2026_08_01.MirSemantics.dedupVTablesInto []
        ((Trusted.Rustc.V2026_08_01.MirSemantics.dynSourceBodies cb bs).map (·.vtables)) := by
  simp only [Trusted.Rustc.V2026_08_01.MirSemantics.collectBodyVTables, List.foldl_map]

theorem foldl_dedup_hom (L : List (List Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable)) (acc : List Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) :
    List.foldl Trusted.Rustc.V2026_06_01.MirSemantics.dedupVTablesInto (acc.map homVTable) (L.map (fun vs => vs.map homVTable)) =
      (List.foldl Trusted.Rustc.V2026_08_01.MirSemantics.dedupVTablesInto acc L).map homVTable := by
  induction L generalizing acc with
  | nil => rfl
  | cons vs L ih => simp only [List.map_cons, List.foldl_cons, dedupVTablesInto_hom, ih]

theorem collectBodyVTables_opt_hom
    {cb6 : Option Trusted.Rustc.V2026_06_01.MirAst.CapturedMir}
    {cb8 : Option Trusted.Rustc.V2026_08_01.MirAst.CapturedMir}
    (hcb : OptBodyRel cb6 cb8)
    {bs6 : List Trusted.Rustc.V2026_06_01.MirAst.CapturedMir}
    {bs8 : List Trusted.Rustc.V2026_08_01.MirAst.CapturedMir}
    (h : BodiesRel bs6 bs8) :
    Trusted.Rustc.V2026_06_01.MirSemantics.collectBodyVTables cb6 bs6 =
      (Trusted.Rustc.V2026_08_01.MirSemantics.collectBodyVTables cb8 bs8).map homVTable := by
  have hSrc := dynSourceBodies_rel hcb h
  rw [collectBodyVTables_eq6, collectBodyVTables_eq8, hSrc.vtables]
  have := foldl_dedup_hom
    ((Trusted.Rustc.V2026_08_01.MirSemantics.dynSourceBodies cb8 bs8).map (·.vtables)) []
  simpa only [List.map_map, Function.comp_def, List.map_nil] using this

theorem collectBodyVTables_hom {bs6 : List Trusted.Rustc.V2026_06_01.MirAst.CapturedMir} {bs8 : List Trusted.Rustc.V2026_08_01.MirAst.CapturedMir}
    (h : BodiesRel bs6 bs8) :
    Trusted.Rustc.V2026_06_01.MirSemantics.collectBodyVTables .none bs6 = (Trusted.Rustc.V2026_08_01.MirSemantics.collectBodyVTables .none bs8).map homVTable :=
  collectBodyVTables_opt_hom .none h

/-- `List.all` congruence for pointwise-equal predicates. -/
theorem all_congr' {α : Type} (l : List α) (f g : α → Bool) (h : ∀ x, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.all_cons, h x, ih]

/-- One body's `CapturedDynType` table merged into an accumulator (dialect 06). -/
def dtInsert6 (acc ds : List Trusted.Rustc.V2026_06_01.MirAst.CapturedDynType) : List Trusted.Rustc.V2026_06_01.MirAst.CapturedDynType :=
  ds.foldl (fun acc' d =>
    match Trusted.Rustc.V2026_06_01.MirSemantics.lookupDynType acc' d.dynKey with
    | .some _ => acc'
    | .none => acc' ++ d :: .nil) acc

/-- One body's `CapturedDynType` table merged into an accumulator (dialect 08). -/
def dtInsert8 (acc ds : List Trusted.Rustc.V2026_08_01.MirAst.CapturedDynType) : List Trusted.Rustc.V2026_08_01.MirAst.CapturedDynType :=
  ds.foldl (fun acc' d =>
    match Trusted.Rustc.V2026_08_01.MirSemantics.lookupDynType acc' d.dynKey with
    | .some _ => acc'
    | .none => acc' ++ d :: .nil) acc

theorem collectBodyDynTypes_eq6 (cb : Option Trusted.Rustc.V2026_06_01.MirAst.CapturedMir)
    (bs : List Trusted.Rustc.V2026_06_01.MirAst.CapturedMir) :
    Trusted.Rustc.V2026_06_01.MirSemantics.collectBodyDynTypes cb bs =
      List.foldl dtInsert6 []
        ((Trusted.Rustc.V2026_06_01.MirSemantics.dynSourceBodies cb bs).map (·.dynTypes)) := by
  simp only [Trusted.Rustc.V2026_06_01.MirSemantics.collectBodyDynTypes, List.foldl_map]
  rfl

theorem collectBodyDynTypes_eq8 (cb : Option Trusted.Rustc.V2026_08_01.MirAst.CapturedMir)
    (bs : List Trusted.Rustc.V2026_08_01.MirAst.CapturedMir) :
    Trusted.Rustc.V2026_08_01.MirSemantics.collectBodyDynTypes cb bs =
      List.foldl dtInsert8 []
        ((Trusted.Rustc.V2026_08_01.MirSemantics.dynSourceBodies cb bs).map (·.dynTypes)) := by
  simp only [Trusted.Rustc.V2026_08_01.MirSemantics.collectBodyDynTypes, List.foldl_map]
  rfl

theorem dtInsert_hom (acc ds : List Trusted.Rustc.V2026_08_01.MirAst.CapturedDynType) :
    dtInsert6 (acc.map homDynType) (ds.map homDynType) = (dtInsert8 acc ds).map homDynType := by
  induction ds generalizing acc with
  | nil => rfl
  | cons d ds ih =>
    simp only [dtInsert6, dtInsert8, List.map_cons, List.foldl_cons, homDynType_dynKey,
      lookupDynType_hom] at ih ⊢
    cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupDynType acc d.dynKey with
    | none =>
      have := ih (acc ++ d :: [])
      simp only [List.map_append, List.map_cons, List.map_nil] at this
      simpa only [Option.map_none] using this
    | some _ => simpa only [Option.map_some] using ih acc

theorem collectBodyDynTypes_opt_hom
    {cb6 : Option Trusted.Rustc.V2026_06_01.MirAst.CapturedMir}
    {cb8 : Option Trusted.Rustc.V2026_08_01.MirAst.CapturedMir}
    (hcb : OptBodyRel cb6 cb8)
    {bs6 : List Trusted.Rustc.V2026_06_01.MirAst.CapturedMir}
    {bs8 : List Trusted.Rustc.V2026_08_01.MirAst.CapturedMir}
    (h : BodiesRel bs6 bs8) :
    Trusted.Rustc.V2026_06_01.MirSemantics.collectBodyDynTypes cb6 bs6 =
      (Trusted.Rustc.V2026_08_01.MirSemantics.collectBodyDynTypes cb8 bs8).map homDynType := by
  have hSrc := dynSourceBodies_rel hcb h
  rw [collectBodyDynTypes_eq6, collectBodyDynTypes_eq8, hSrc.dynTypes]
  have key : ∀ (L : List (List Trusted.Rustc.V2026_08_01.MirAst.CapturedDynType)) (acc : List Trusted.Rustc.V2026_08_01.MirAst.CapturedDynType),
      List.foldl dtInsert6 (acc.map homDynType) (L.map (fun ds => ds.map homDynType)) =
        (List.foldl dtInsert8 acc L).map homDynType := by
    intro L
    induction L with
    | nil => intro acc; rfl
    | cons ds L ih => intro acc; simp only [List.map_cons, List.foldl_cons, dtInsert_hom, ih]
  have := key ((Trusted.Rustc.V2026_08_01.MirSemantics.dynSourceBodies cb8 bs8).map (·.dynTypes)) []
  simpa only [List.map_map, Function.comp_def, List.map_nil] using this

theorem collectBodyDynTypes_hom {bs6 : List Trusted.Rustc.V2026_06_01.MirAst.CapturedMir} {bs8 : List Trusted.Rustc.V2026_08_01.MirAst.CapturedMir}
    (h : BodiesRel bs6 bs8) :
    Trusted.Rustc.V2026_06_01.MirSemantics.collectBodyDynTypes .none bs6 = (Trusted.Rustc.V2026_08_01.MirSemantics.collectBodyDynTypes .none bs8).map homDynType :=
  collectBodyDynTypes_opt_hom .none h

theorem bodyVTablesConsistent_opt_hom
    {cb6 : Option Trusted.Rustc.V2026_06_01.MirAst.CapturedMir}
    {cb8 : Option Trusted.Rustc.V2026_08_01.MirAst.CapturedMir}
    (hcb : OptBodyRel cb6 cb8)
    {bs6 : List Trusted.Rustc.V2026_06_01.MirAst.CapturedMir}
    {bs8 : List Trusted.Rustc.V2026_08_01.MirAst.CapturedMir}
    (h : BodiesRel bs6 bs8) (vts : List Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) :
    Trusted.Rustc.V2026_06_01.MirSemantics.bodyVTablesConsistent cb6 bs6 (vts.map homVTable) =
      Trusted.Rustc.V2026_08_01.MirSemantics.bodyVTablesConsistent cb8 bs8 vts := by
  have hSrc := dynSourceBodies_rel hcb h
  have e6 : (Trusted.Rustc.V2026_06_01.MirSemantics.dynSourceBodies cb6 bs6).all
      (fun b => Trusted.Rustc.V2026_06_01.MirSemantics.vtablesAgreeWith (vts.map homVTable) b.vtables) =
      ((Trusted.Rustc.V2026_06_01.MirSemantics.dynSourceBodies cb6 bs6).map (·.vtables)).all
        (Trusted.Rustc.V2026_06_01.MirSemantics.vtablesAgreeWith (vts.map homVTable)) := by
    simp only [List.all_map, Function.comp_def]
  have e8 : (Trusted.Rustc.V2026_08_01.MirSemantics.dynSourceBodies cb8 bs8).all
      (fun b => Trusted.Rustc.V2026_08_01.MirSemantics.vtablesAgreeWith vts b.vtables) =
      ((Trusted.Rustc.V2026_08_01.MirSemantics.dynSourceBodies cb8 bs8).map (·.vtables)).all
        (Trusted.Rustc.V2026_08_01.MirSemantics.vtablesAgreeWith vts) := by
    simp only [List.all_map, Function.comp_def]
  simp only [Trusted.Rustc.V2026_06_01.MirSemantics.bodyVTablesConsistent,
    Trusted.Rustc.V2026_08_01.MirSemantics.bodyVTablesConsistent]
  rw [e6, e8, hSrc.vtables, List.all_map, List.all_map]
  apply all_congr'
  intro b
  simp only [Function.comp_apply, vtablesAgreeWith_hom]

theorem bodyVTablesConsistent_hom {bs6 : List Trusted.Rustc.V2026_06_01.MirAst.CapturedMir} {bs8 : List Trusted.Rustc.V2026_08_01.MirAst.CapturedMir}
    (h : BodiesRel bs6 bs8) (vts : List Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) :
    Trusted.Rustc.V2026_06_01.MirSemantics.bodyVTablesConsistent .none bs6 (vts.map homVTable) = Trusted.Rustc.V2026_08_01.MirSemantics.bodyVTablesConsistent .none bs8 vts :=
  bodyVTablesConsistent_opt_hom .none h vts

theorem vtableAllocIdsUnique_hom (vs : List Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) :
    Trusted.Rustc.V2026_06_01.MirSemantics.vtableAllocIdsUnique (vs.map homVTable) = Trusted.Rustc.V2026_08_01.MirSemantics.vtableAllocIdsUnique vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, Trusted.Rustc.V2026_06_01.MirSemantics.vtableAllocIdsUnique, Trusted.Rustc.V2026_08_01.MirSemantics.vtableAllocIdsUnique, ih,
      homVTable_vtableAllocId, lookupVTableByAllocId_hom]
    cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupVTableByAllocId vs v.vtableAllocId <;> rfl

theorem vtableIdsUnique_hom (vs : List Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) :
    Trusted.Rustc.V2026_06_01.MirSemantics.vtableIdsUnique (vs.map homVTable) = Trusted.Rustc.V2026_08_01.MirSemantics.vtableIdsUnique vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, Trusted.Rustc.V2026_06_01.MirSemantics.vtableIdsUnique, Trusted.Rustc.V2026_08_01.MirSemantics.vtableIdsUnique, ih, homVTable_vtableId,
      lookupVTableById_hom]
    cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupVTableById vs v.vtableId <;> rfl

theorem vtableSuperLinkOk_hom (vts : List Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) (v : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) (t : Nat) :
    Trusted.Rustc.V2026_06_01.MirSemantics.vtableSuperLinkOk (vts.map homVTable) (homVTable v) t = Trusted.Rustc.V2026_08_01.MirSemantics.vtableSuperLinkOk vts v t := by
  simp only [Trusted.Rustc.V2026_06_01.MirSemantics.vtableSuperLinkOk, Trusted.Rustc.V2026_08_01.MirSemantics.vtableSuperLinkOk, homVTable_vtableId, lookupVTableById_hom]
  cases Nat.beq t v.vtableId
  · cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupVTableById vts t <;>
      simp only [Option.map_none, Option.map_some, homVTable_concreteTy, homVTable_sizeBytes,
        homVTable_alignBytes, homVTable_isUninhabited, rigidTyEq_hom]
  · rfl

theorem vtableSuperLinksOk_hom (vts : List Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) (v : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) :
    Trusted.Rustc.V2026_06_01.MirSemantics.vtableSuperLinksOk (vts.map homVTable) (homVTable v) = Trusted.Rustc.V2026_08_01.MirSemantics.vtableSuperLinksOk vts v := by
  simp only [Trusted.Rustc.V2026_06_01.MirSemantics.vtableSuperLinksOk, Trusted.Rustc.V2026_08_01.MirSemantics.vtableSuperLinksOk, homVTable_primarySuperVTableId?,
    homVTable_extraSuperVTableIds, homVTable_slots, vtableSuperLinkOk_hom]
  congr 1
  congr 1
  generalize v.slots = l
  induction l with
  | nil => rfl
  | cons s ss ih =>
    cases s <;> simp only [List.map_cons, List.all_cons, homSlot, ih]


theorem vtableEnvOk_hom (ptrBytes : Nat) (vts : List Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable) (n : Nat)
    (g6 : List Trusted.Rustc.V2026_06_01.MirAst.CapturedAllocation) (g8 : List Trusted.Rustc.V2026_08_01.MirAst.CapturedAllocation)
    (f6 : List Trusted.Rustc.V2026_06_01.MirSemantics.FnPtrEntry) (f8 : List Trusted.Rustc.V2026_08_01.MirSemantics.FnPtrEntry)
    (hg : ∀ a, Trusted.Rustc.V2026_06_01.MirSemantics.isGlobalAllocIdIn g6 a = Trusted.Rustc.V2026_08_01.MirSemantics.isGlobalAllocIdIn g8 a)
    (hf : ∀ a, (Trusted.Rustc.V2026_06_01.MirSemantics.lookupFnPtr f6 a).isSome = (Trusted.Rustc.V2026_08_01.MirSemantics.lookupFnPtr f8 a).isSome) :
    Trusted.Rustc.V2026_06_01.MirSemantics.vtableEnvOk ptrBytes (vts.map homVTable) n g6 f6 = Trusted.Rustc.V2026_08_01.MirSemantics.vtableEnvOk ptrBytes vts n g8 f8 := by
  simp only [Trusted.Rustc.V2026_06_01.MirSemantics.vtableEnvOk, Trusted.Rustc.V2026_08_01.MirSemantics.vtableEnvOk, vtableAllocIdsUnique_hom, vtableIdsUnique_hom]
  congr 1
  congr 1
  rw [List.all_map]
  apply all_congr'
  intro v
  simp only [Function.comp_apply, wfVTableEntry_hom, vtableSuperLinksOk_hom, homVTable_vtableAllocId,
    Trusted.Rustc.V2026_06_01.MirSemantics.vtableAllocBase, Trusted.Rustc.V2026_08_01.MirSemantics.vtableAllocBase, Trusted.Rustc.V2026_06_01.MirSemantics.vtableAllocSpan, Trusted.Rustc.V2026_08_01.MirSemantics.vtableAllocSpan, hg]
  have hfa := hf v.vtableAllocId
  cases h6 : Trusted.Rustc.V2026_06_01.MirSemantics.lookupFnPtr f6 v.vtableAllocId <;> cases h8 : Trusted.Rustc.V2026_08_01.MirSemantics.lookupFnPtr f8 v.vtableAllocId <;>
    simp only [h6, h8, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
      Bool.true_eq_false] at hfa ⊢ <;> rfl

/-- Dyn-relevant relation between two `DynMemView`s: corresponding linked-body vtable/`dyn`
tables, equal `nextAllocId`, and agreement of the global / function-pointer / borrow-tag
membership tests that `dynVTableEnv?` and `checkDynVTablePtr` consult. -/
structure DynViewRel (mv6 : Trusted.Rustc.V2026_06_01.MirSemantics.DynMemView) (mv8 : Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView) : Prop where
  bodies : BodiesRel mv6.dynBodies mv8.dynBodies
  nextAllocId : mv6.nextAllocId = mv8.nextAllocId
  globals : ∀ a, Trusted.Rustc.V2026_06_01.MirSemantics.isGlobalAllocIdIn mv6.globals a = Trusted.Rustc.V2026_08_01.MirSemantics.isGlobalAllocIdIn mv8.globals a
  fnPtrs : ∀ a, (Trusted.Rustc.V2026_06_01.MirSemantics.lookupFnPtr mv6.fnPtrs a).isSome = (Trusted.Rustc.V2026_08_01.MirSemantics.lookupFnPtr mv8.fnPtrs a).isSome
  borrows : ∀ t, (Trusted.Rustc.V2026_06_01.MirSemantics.lookupBorrow mv6.borrows t).isSome = (Trusted.Rustc.V2026_08_01.MirSemantics.lookupBorrow mv8.borrows t).isSome

theorem dynVTableEnv?_opt_hom
    {cb6 : Option Trusted.Rustc.V2026_06_01.MirAst.CapturedMir}
    {cb8 : Option Trusted.Rustc.V2026_08_01.MirAst.CapturedMir}
    (hcb : OptBodyRel cb6 cb8)
    {mv6 : Trusted.Rustc.V2026_06_01.MirSemantics.DynMemView}
    {mv8 : Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView}
    (h : DynViewRel mv6 mv8) (ptrBytes : Nat) :
    Trusted.Rustc.V2026_06_01.MirSemantics.dynVTableEnv? cb6 mv6 ptrBytes =
      (Trusted.Rustc.V2026_08_01.MirSemantics.dynVTableEnv? cb8 mv8 ptrBytes).map
        (fun e => (e.1.map homVTable, e.2.map homDynType)) := by
  simp only [Trusted.Rustc.V2026_06_01.MirSemantics.dynVTableEnv?,
    Trusted.Rustc.V2026_08_01.MirSemantics.dynVTableEnv?, collectBodyVTables_opt_hom hcb h.bodies]
  cases hv : Trusted.Rustc.V2026_08_01.MirSemantics.collectBodyVTables cb8 mv8.dynBodies with
  | nil => rfl
  | cons v vs =>
    have hc := bodyVTablesConsistent_opt_hom hcb h.bodies (v :: vs)
    have he := vtableEnvOk_hom ptrBytes (v :: vs) mv8.nextAllocId mv6.globals mv8.globals
      mv6.fnPtrs mv8.fnPtrs h.globals h.fnPtrs
    simp only [List.map_cons] at hc he
    simp only [List.map_cons, h.nextAllocId]
    rw [hc, he]
    cases Bool.and (Trusted.Rustc.V2026_08_01.MirSemantics.bodyVTablesConsistent cb8 mv8.dynBodies (v :: vs))
        (Trusted.Rustc.V2026_08_01.MirSemantics.vtableEnvOk ptrBytes (v :: vs) mv8.nextAllocId mv8.globals mv8.fnPtrs) with
    | false => rfl
    | true => simp only [Option.map_some, List.map_cons, collectBodyDynTypes_opt_hom hcb h.bodies]

theorem dynVTableEnv?_hom {mv6 : Trusted.Rustc.V2026_06_01.MirSemantics.DynMemView} {mv8 : Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView} (h : DynViewRel mv6 mv8)
    (ptrBytes : Nat) :
    Trusted.Rustc.V2026_06_01.MirSemantics.dynVTableEnv? .none mv6 ptrBytes =
      (Trusted.Rustc.V2026_08_01.MirSemantics.dynVTableEnv? .none mv8 ptrBytes).map
        (fun e => (e.1.map homVTable, e.2.map homDynType)) :=
  dynVTableEnv?_opt_hom .none h ptrBytes

theorem homPtr_allocId (p : Trusted.Rustc.V2026_08_01.MirAst.ProvenancePtr) : (homPtr p).allocId = p.allocId := rfl
theorem homPtr_offsetBytes (p : Trusted.Rustc.V2026_08_01.MirAst.ProvenancePtr) : (homPtr p).offsetBytes = p.offsetBytes := rfl
theorem homPtr_tag (p : Trusted.Rustc.V2026_08_01.MirAst.ProvenancePtr) : Trusted.Rustc.V2026_06_01.MirAst.ProvenancePtr.tag (homPtr p) = Trusted.Rustc.V2026_08_01.MirAst.ProvenancePtr.tag p :=
  rfl

/-- `DynCheck` embedding on the witness `(entry, vtables, dynTypes)` of `checkDynVTablePtr`. -/
def homDynCheck :
    Trusted.Rustc.V2026_08_01.MirSemantics.DynCheck (Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable × List Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable × List Trusted.Rustc.V2026_08_01.MirAst.CapturedDynType) →
      Trusted.Rustc.V2026_06_01.MirSemantics.DynCheck (Trusted.Rustc.V2026_06_01.MirAst.CapturedVTable × List Trusted.Rustc.V2026_06_01.MirAst.CapturedVTable × List Trusted.Rustc.V2026_06_01.MirAst.CapturedDynType)
  | .ok (e, vts, dts) => .ok (homVTable e, vts.map homVTable, dts.map homDynType)
  | .ub => .ub
  | .unsupported => .unsupported

/-- `checkDynVTablePtr` commutes with the embedding for ANY optional current body
(`OptBodyRel cb6 cb8`: both `.none` for intrinsics and `.some _` for virtual calls / safe
`size_of_val`), under `DynViewRel`, for every pointer width, metadata value, and expected key. -/
theorem checkDynVTablePtr_opt_hom
    {cb6 : Option Trusted.Rustc.V2026_06_01.MirAst.CapturedMir}
    {cb8 : Option Trusted.Rustc.V2026_08_01.MirAst.CapturedMir}
    (hcb : OptBodyRel cb6 cb8)
    {mv6 : Trusted.Rustc.V2026_06_01.MirSemantics.DynMemView}
    {mv8 : Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView}
    (h : DynViewRel mv6 mv8)
    (ptrBytes : Nat) (v : Trusted.Rustc.V2026_08_01.MirSemantics.Value) (k : String) :
    Trusted.Rustc.V2026_06_01.MirSemantics.checkDynVTablePtr cb6 mv6 ptrBytes (homValue v) k =
      homDynCheck (Trusted.Rustc.V2026_08_01.MirSemantics.checkDynVTablePtr cb8 mv8 ptrBytes v k) := by
  cases v with
  | ptr p n =>
    simp only [homValue, Trusted.Rustc.V2026_06_01.MirSemantics.checkDynVTablePtr,
      Trusted.Rustc.V2026_08_01.MirSemantics.checkDynVTablePtr, dynVTableEnv?_opt_hom hcb h]
    cases Nat.beq n ptrBytes
    · rfl
    · cases Trusted.Rustc.V2026_08_01.MirSemantics.dynVTableEnv? cb8 mv8 ptrBytes with
      | none => rfl
      | some e =>
        obtain ⟨vts, dts⟩ := e
        simp only [Option.map_some, dynTypeModeled_hom]
        cases Trusted.Rustc.V2026_08_01.MirSemantics.dynTypeModeled dts k
        · rfl
        · simp only [homPtr_allocId, lookupVTableByAllocId_hom, homPtr_tag, homPtr_offsetBytes]
          have hb := h.borrows (Trusted.Rustc.V2026_08_01.MirAst.ProvenancePtr.tag p)
          cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupVTableByAllocId vts p.allocId with
          | some entry =>
            simp only [Option.map_some]
            cases hb6 : Trusted.Rustc.V2026_06_01.MirSemantics.lookupBorrow mv6.borrows (Trusted.Rustc.V2026_08_01.MirAst.ProvenancePtr.tag p) <;>
              cases hb8 : Trusted.Rustc.V2026_08_01.MirSemantics.lookupBorrow mv8.borrows (Trusted.Rustc.V2026_08_01.MirAst.ProvenancePtr.tag p) <;>
              simp only [hb6, hb8, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
                Bool.true_eq_false] at hb ⊢
            · cases Nat.beq p.offsetBytes 0
              · rfl
              · simp only [homVTable_dynKey, dynKeysCompatible_hom]
                cases Trusted.Rustc.V2026_08_01.MirSemantics.dynKeysCompatible dts entry.dynKey k
                · cases Trusted.Rustc.V2026_08_01.MirSemantics.dynTypeModeled dts entry.dynKey <;> rfl
                · rfl
            · rfl
          | none =>
            simp only [Option.map_none, h.globals]
            have hf := h.fnPtrs p.allocId
            cases hb6 : Trusted.Rustc.V2026_06_01.MirSemantics.lookupBorrow mv6.borrows (Trusted.Rustc.V2026_08_01.MirAst.ProvenancePtr.tag p) <;>
              cases hb8 : Trusted.Rustc.V2026_08_01.MirSemantics.lookupBorrow mv8.borrows (Trusted.Rustc.V2026_08_01.MirAst.ProvenancePtr.tag p) <;>
              simp only [hb6, hb8, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
                Bool.true_eq_false] at hb ⊢ <;>
              cases hf6 : Trusted.Rustc.V2026_06_01.MirSemantics.lookupFnPtr mv6.fnPtrs p.allocId <;>
              cases hf8 : Trusted.Rustc.V2026_08_01.MirSemantics.lookupFnPtr mv8.fnPtrs p.allocId <;>
              simp only [hf6, hf8, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
                Bool.true_eq_false, Trusted.Rustc.V2026_06_01.MirSemantics.vtableAllocBase, Trusted.Rustc.V2026_08_01.MirSemantics.vtableAllocBase, Trusted.Rustc.V2026_06_01.MirSemantics.vtableAllocSpan,
                Trusted.Rustc.V2026_08_01.MirSemantics.vtableAllocSpan] at hf ⊢ <;>
              first
              | rfl
              | (split <;> rename_i hc <;> simp only [hc, homDynCheck])
  | _ => rfl

/-- `checkDynVTablePtr` (intrinsic path `currentBody = .none`) as a specialization of
`checkDynVTablePtr_opt_hom`. -/
theorem checkDynVTablePtr_hom {mv6 : Trusted.Rustc.V2026_06_01.MirSemantics.DynMemView} {mv8 : Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView} (h : DynViewRel mv6 mv8)
    (ptrBytes : Nat) (v : Trusted.Rustc.V2026_08_01.MirSemantics.Value) (k : String) :
    Trusted.Rustc.V2026_06_01.MirSemantics.checkDynVTablePtr .none mv6 ptrBytes (homValue v) k =
      homDynCheck (Trusted.Rustc.V2026_08_01.MirSemantics.checkDynVTablePtr .none mv8 ptrBytes v k) :=
  checkDynVTablePtr_opt_hom .none h ptrBytes v k

/-- `DynCheck Value` embedding for unsizing results. -/
def homDynCheckVal :
    Trusted.Rustc.V2026_08_01.MirSemantics.DynCheck Trusted.Rustc.V2026_08_01.MirSemantics.Value →
      Trusted.Rustc.V2026_06_01.MirSemantics.DynCheck Trusted.Rustc.V2026_06_01.MirSemantics.Value
  | .ok v => .ok (homValue v)
  | .ub => .ub
  | .unsupported => .unsupported

/-- **C7** Raw `T -> dyn K` unsizing (`evalThinToDynUnsize ... isRef := false`) commutes with the
embedding across ALL pointer widths (32-bit, 64-bit, etc.) under `DynViewRel`. -/
theorem evalThinToDynUnsize_raw_hom
    (l6 : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot)
    (l8 : List Trusted.Rustc.V2026_08_01.MirSemantics.LocalSlot)
    {mv6 : Trusted.Rustc.V2026_06_01.MirSemantics.DynMemView}
    {mv8 : Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView}
    (h : DynViewRel mv6 mv8)
    (ld6 : List Trusted.Rustc.V2026_06_01.MirAst.LocalDecl)
    (ld8 : List Trusted.Rustc.V2026_08_01.MirAst.LocalDecl)
    (La : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (Lb : Trusted.Rustc.V2026_08_01.Layout.LayoutTable)
    (hL : Trusted.Rustc.V2026_06_01.MirSemantics.layoutPointerBytes La =
      Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb)
    (dataVal : Trusted.Rustc.V2026_08_01.MirSemantics.Value)
    (srcPointee : Trusted.Rustc.V2026_08_01.MirAst.RigidTy)
    (dynKey : String) (isMut : Bool) :
    Trusted.Rustc.V2026_06_01.MirSemantics.evalThinToDynUnsize
        l6 mv6 ld6 La (homValue dataVal) (homTy srcPointee) dynKey false isMut =
      homDynCheckVal (Trusted.Rustc.V2026_08_01.MirSemantics.evalThinToDynUnsize
        l8 mv8 ld8 Lb dataVal srcPointee dynKey false isMut) := by
  have hTail : ∀ (v : Trusted.Rustc.V2026_08_01.MirSemantics.Value) (ok : Bool),
      (match ok with
        | false => Trusted.Rustc.V2026_06_01.MirSemantics.DynCheck.ub
        | true =>
          match Trusted.Rustc.V2026_06_01.MirSemantics.dynVTableEnv? .none mv6
              (Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb) with
          | .none => .unsupported
          | .some (vts, dts) =>
            match Trusted.Rustc.V2026_06_01.MirSemantics.dynTypeModeled dts dynKey with
            | false => .unsupported
            | true =>
              match Trusted.Rustc.V2026_06_01.MirSemantics.lookupVTableFor vts (homTy srcPointee) dynKey with
              | .none => .unsupported
              | .some entry =>
                .ok (.aggregate 0 (homValue v ::
                  .ptr { allocId := entry.vtableAllocId, offsetBytes := 0 }
                    (Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb) :: .nil))) =
      homDynCheckVal (match ok with
        | false => Trusted.Rustc.V2026_08_01.MirSemantics.DynCheck.ub
        | true =>
          match Trusted.Rustc.V2026_08_01.MirSemantics.dynVTableEnv? .none mv8
              (Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb) with
          | .none => .unsupported
          | .some (vts, dts) =>
            match Trusted.Rustc.V2026_08_01.MirSemantics.dynTypeModeled dts dynKey with
            | false => .unsupported
            | true =>
              match Trusted.Rustc.V2026_08_01.MirSemantics.lookupVTableFor vts srcPointee dynKey with
              | .none => .unsupported
              | .some entry =>
                .ok (.aggregate 0 (v ::
                  .ptr { allocId := entry.vtableAllocId, offsetBytes := 0 }
                    (Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb) :: .nil))) := by
    intro v ok
    cases ok
    · rfl
    · simp only [dynVTableEnv?_hom h]
      cases Trusted.Rustc.V2026_08_01.MirSemantics.dynVTableEnv? .none mv8
          (Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb) with
      | none => rfl
      | some e =>
        obtain ⟨vts, dts⟩ := e
        simp only [Option.map_some, dynTypeModeled_hom]
        cases Trusted.Rustc.V2026_08_01.MirSemantics.dynTypeModeled dts dynKey
        · rfl
        · simp only [lookupVTableFor_hom]
          cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupVTableFor vts srcPointee dynKey with
          | none => rfl
          | some entry => rfl
  unfold Trusted.Rustc.V2026_06_01.MirSemantics.evalThinToDynUnsize
    Trusted.Rustc.V2026_08_01.MirSemantics.evalThinToDynUnsize
  simp only [hL]
  cases dataVal with
  | unit => rfl
  | aggregate _ _ => rfl
  | ptr p sz => exact hTail (.ptr p sz) (Nat.beq sz (Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb))
  | scalar sc => exact hTail (.scalar sc) (Nat.beq sc.sizeBytes (Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb))

/-- **C7** Auto-trait subset check (`defPathsSubset`) agrees identically across dialects. -/
theorem defPathsSubset_hom (xs ys : List Trusted.Rustc.V2026_08_01.MirAst.DefPath) :
    Trusted.Rustc.V2026_06_01.MirSemantics.defPathsSubset xs ys =
      Trusted.Rustc.V2026_08_01.MirSemantics.defPathsSubset xs ys := by
  unfold Trusted.Rustc.V2026_06_01.MirSemantics.defPathsSubset
    Trusted.Rustc.V2026_08_01.MirSemantics.defPathsSubset
  simp only [stringEq_hom]

/-- **C7** Raw `dyn Src -> dyn Dst` unsizing & trait upcasting (`evalDynToDynUnsize ... isRef :=
false`) commutes with the embedding across ALL pointer widths (32-bit, 64-bit, etc.), ALL vtable
and `dyn`-type graphs (`DynViewRel`), equal-key NOP, primary-prefix and `TraitVPtr` supertrait
upcasting, auto-trait subset checks, and `.ub` / `.unsupported` faults. -/
theorem evalDynToDynUnsize_raw_hom
    (l6 : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot)
    (l8 : List Trusted.Rustc.V2026_08_01.MirSemantics.LocalSlot)
    {mv6 : Trusted.Rustc.V2026_06_01.MirSemantics.DynMemView}
    {mv8 : Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView}
    (h : DynViewRel mv6 mv8)
    (ld6 : List Trusted.Rustc.V2026_06_01.MirAst.LocalDecl)
    (ld8 : List Trusted.Rustc.V2026_08_01.MirAst.LocalDecl)
    (La : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (Lb : Trusted.Rustc.V2026_08_01.Layout.LayoutTable)
    (hL : Trusted.Rustc.V2026_06_01.MirSemantics.layoutPointerBytes La =
      Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb)
    (fatVal : Trusted.Rustc.V2026_08_01.MirSemantics.Value)
    (srcKey dstKey : String) (isMut : Bool) :
    Trusted.Rustc.V2026_06_01.MirSemantics.evalDynToDynUnsize
        l6 mv6 ld6 La (homValue fatVal) srcKey dstKey false isMut =
      homDynCheckVal (Trusted.Rustc.V2026_08_01.MirSemantics.evalDynToDynUnsize
        l8 mv8 ld8 Lb fatVal srcKey dstKey false isMut) := by
  rcases fatVal with _ | _ | _ | ⟨i, fs⟩
  · rfl
  · rfl
  · rfl
  · rcases i with _ | i
    · rcases fs with _ | ⟨dv, _ | ⟨mv, _ | ⟨x, rest⟩⟩⟩
      · rfl
      · rfl
      · rcases dv with _ | sc | ⟨p, sz⟩ | ⟨j, gs⟩
        · rfl
        · simp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalDynToDynUnsize,
            Trusted.Rustc.V2026_08_01.MirSemantics.evalDynToDynUnsize, hL, homValue, homValues,
            homScalar, stringEq_hom, checkDynVTablePtr_hom h]
          generalize Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb = pb
          cases Nat.beq sc.sizeBytes pb
          · rfl
          · cases Trusted.Rustc.V2026_08_01.MirSemantics.stringEq srcKey dstKey
            · cases Trusted.Rustc.V2026_08_01.MirSemantics.checkDynVTablePtr .none mv8 pb mv srcKey with
              | ub => rfl
              | unsupported => rfl
              | ok w =>
                obtain ⟨entry, vts, dts⟩ := w
                simp only [homDynCheck, lookupDynType_hom, dynTypeModeled_hom, resolveUpcastVTable?_hom]
                cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupDynType dts srcKey with
                | none =>
                  cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupDynType dts dstKey with
                  | none =>
                    cases Trusted.Rustc.V2026_08_01.MirSemantics.dynTypeModeled dts dstKey
                    · rfl
                    · cases Trusted.Rustc.V2026_08_01.MirSemantics.resolveUpcastVTable? vts dts entry dstKey <;> rfl
                  | some dd =>
                    simp only [Option.map_none, Option.map_some, homDynType_autoTraits]
                    cases dd.autoTraits with
                    | nil =>
                      cases Trusted.Rustc.V2026_08_01.MirSemantics.dynTypeModeled dts dstKey
                      · rfl
                      · cases Trusted.Rustc.V2026_08_01.MirSemantics.resolveUpcastVTable? vts dts entry dstKey <;> rfl
                    | cons _ _ => rfl
                | some ds =>
                  cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupDynType dts dstKey with
                  | none =>
                    cases Trusted.Rustc.V2026_08_01.MirSemantics.dynTypeModeled dts dstKey
                    · rfl
                    · cases Trusted.Rustc.V2026_08_01.MirSemantics.resolveUpcastVTable? vts dts entry dstKey <;> rfl
                  | some dd =>
                    simp only [Option.map_some, homDynType_autoTraits, defPathsSubset_hom]
                    cases Trusted.Rustc.V2026_08_01.MirSemantics.defPathsSubset dd.autoTraits ds.autoTraits
                    · rfl
                    · cases Trusted.Rustc.V2026_08_01.MirSemantics.dynTypeModeled dts dstKey
                      · rfl
                      · cases Trusted.Rustc.V2026_08_01.MirSemantics.resolveUpcastVTable? vts dts entry dstKey <;> rfl
            · cases Trusted.Rustc.V2026_08_01.MirSemantics.checkDynVTablePtr .none mv8 pb mv srcKey <;> rfl
        · simp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalDynToDynUnsize,
            Trusted.Rustc.V2026_08_01.MirSemantics.evalDynToDynUnsize, hL, homValue, homValues,
            homPtr, stringEq_hom, checkDynVTablePtr_hom h]
          generalize Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb = pb
          cases Nat.beq sz pb
          · rfl
          · cases Trusted.Rustc.V2026_08_01.MirSemantics.stringEq srcKey dstKey
            · cases Trusted.Rustc.V2026_08_01.MirSemantics.checkDynVTablePtr .none mv8 pb mv srcKey with
              | ub => rfl
              | unsupported => rfl
              | ok w =>
                obtain ⟨entry, vts, dts⟩ := w
                simp only [homDynCheck, lookupDynType_hom, dynTypeModeled_hom, resolveUpcastVTable?_hom]
                cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupDynType dts srcKey with
                | none =>
                  cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupDynType dts dstKey with
                  | none =>
                    cases Trusted.Rustc.V2026_08_01.MirSemantics.dynTypeModeled dts dstKey
                    · rfl
                    · cases Trusted.Rustc.V2026_08_01.MirSemantics.resolveUpcastVTable? vts dts entry dstKey <;> rfl
                  | some dd =>
                    simp only [Option.map_none, Option.map_some, homDynType_autoTraits]
                    cases dd.autoTraits with
                    | nil =>
                      cases Trusted.Rustc.V2026_08_01.MirSemantics.dynTypeModeled dts dstKey
                      · rfl
                      · cases Trusted.Rustc.V2026_08_01.MirSemantics.resolveUpcastVTable? vts dts entry dstKey <;> rfl
                    | cons _ _ => rfl
                | some ds =>
                  cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupDynType dts dstKey with
                  | none =>
                    cases Trusted.Rustc.V2026_08_01.MirSemantics.dynTypeModeled dts dstKey
                    · rfl
                    · cases Trusted.Rustc.V2026_08_01.MirSemantics.resolveUpcastVTable? vts dts entry dstKey <;> rfl
                  | some dd =>
                    simp only [Option.map_some, homDynType_autoTraits, defPathsSubset_hom]
                    cases Trusted.Rustc.V2026_08_01.MirSemantics.defPathsSubset dd.autoTraits ds.autoTraits
                    · rfl
                    · cases Trusted.Rustc.V2026_08_01.MirSemantics.dynTypeModeled dts dstKey
                      · rfl
                      · cases Trusted.Rustc.V2026_08_01.MirSemantics.resolveUpcastVTable? vts dts entry dstKey <;> rfl
            · cases Trusted.Rustc.V2026_08_01.MirSemantics.checkDynVTablePtr .none mv8 pb mv srcKey <;> rfl
        · rfl
      · rfl
    · rfl

/-! ## C7 relational commuting theorems: `evalDynSizeAlignOfVal`, `evalAddrEqCall` -/

/-- Dialect-neutral outcome class of a `dyn` intrinsic step: `.ub`, `.unsupported`, or the
intrinsic return of scalar `⟨bits, sizeBytes⟩` through the dialect's own
`writeIntrinsicReturn`. -/
inductive DynStepClass : Type where
  | ub
  | unsupported
  | write (bits sizeBytes : Nat)

/-- Realize a `DynStepClass` as a `V2026_06_01` step node. -/
def DynStepClass.run6 : DynStepClass → Trusted.Rustc.V2026_06_01.MirSemantics.MachineState → List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot → Trusted.Rustc.V2026_06_01.MirAst.Place → Nat →
    Trusted.Rustc.V2026_06_01.MirSemantics.MirStepNode
  | .ub, _, _, _, _ => Trusted.Rustc.V2026_06_01.MirSemantics.MirStepNode.fail .ub
  | .unsupported, _, _, _, _ => Trusted.Rustc.V2026_06_01.MirSemantics.MirStepNode.unsupported
  | .write b sz, s, l, d, t => Trusted.Rustc.V2026_06_01.MirSemantics.writeIntrinsicReturn s l d t (.scalar ⟨b, sz⟩)

/-- Realize a `DynStepClass` as a `V2026_08_01` step node. -/
def DynStepClass.run8 : DynStepClass → Trusted.Rustc.V2026_08_01.MirSemantics.MachineState → List Trusted.Rustc.V2026_08_01.MirSemantics.LocalSlot → Trusted.Rustc.V2026_08_01.MirAst.Place → Nat →
    Trusted.Rustc.V2026_08_01.MirSemantics.MirStepNode
  | .ub, _, _, _, _ => Trusted.Rustc.V2026_08_01.MirSemantics.MirStepNode.fail .ub
  | .unsupported, _, _, _, _ => Trusted.Rustc.V2026_08_01.MirSemantics.MirStepNode.unsupported
  | .write b sz, s, l, d, t => Trusted.Rustc.V2026_08_01.MirSemantics.writeIntrinsicReturn s l d t (.scalar ⟨b, sz⟩)

/-- Dyn-relevant relation between two machine memories (`DynViewRel` of their `DynMemView`s):
linked-body vtable/`dyn` tables, `nextAllocId`, and global / function-pointer / borrow-tag
membership. Frame bookkeeping, locals, bytes, and Tree Borrows permissions are unconstrained. -/
abbrev DynMemRel (m6 : Trusted.Rustc.V2026_06_01.MirSemantics.Memory) (m8 : Trusted.Rustc.V2026_08_01.MirSemantics.Memory) : Prop :=
  DynViewRel (Trusted.Rustc.V2026_06_01.MirSemantics.DynMemView.ofMemory m6) (Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView.ofMemory m8)

/-- **C7 (relational)** `evalDynSizeAlignOfVal` (`size_of_val` / `align_of_val` on `&dyn K`)
commutes with the embedding: for `DynMemRel`-related memories and layout tables of equal pointer
width, both dialects take the SAME outcome class (`.ub`, `.unsupported`, or the intrinsic return
of the same `usize` scalar) on every argument value of the 08 dialect, every key and both
intrinsics. Scope: the destination write itself is each dialect's own `writeIntrinsicReturn`
(not a `dyn` operation); locals and destination places are arbitrary. -/
theorem evalDynSizeAlignOfVal_hom (s6 : Trusted.Rustc.V2026_06_01.MirSemantics.MachineState) (s8 : Trusted.Rustc.V2026_08_01.MirSemantics.MachineState)
    (hmem : DynMemRel s6.memory s8.memory)
    (La : Trusted.Rustc.V2026_06_01.Layout.LayoutTable) (Lb : Trusted.Rustc.V2026_08_01.Layout.LayoutTable)
    (hL : Trusted.Rustc.V2026_06_01.MirSemantics.layoutPointerBytes La = Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb)
    (l6 : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot) (l8 : List Trusted.Rustc.V2026_08_01.MirSemantics.LocalSlot) (d6 : Trusted.Rustc.V2026_06_01.MirAst.Place) (d8 : Trusted.Rustc.V2026_08_01.MirAst.Place) (bb : Nat)
    (v : Trusted.Rustc.V2026_08_01.MirSemantics.Value) (k : String) (isSize : Bool) :
    ∃ c : DynStepClass,
      Trusted.Rustc.V2026_06_01.MirSemantics.evalDynSizeAlignOfVal s6 La l6 d6 bb (homValue v) k isSize = c.run6 s6 l6 d6 bb ∧
      Trusted.Rustc.V2026_08_01.MirSemantics.evalDynSizeAlignOfVal s8 Lb l8 d8 bb v k isSize = c.run8 s8 l8 d8 bb := by
  rcases v with _ | sc | ⟨p, n⟩ | ⟨i, fs⟩
  · exact ⟨.ub, rfl, rfl⟩
  · exact ⟨.ub, rfl, rfl⟩
  · exact ⟨.ub, rfl, rfl⟩
  · rcases i with _ | i
    · rcases fs with _ | ⟨dv, _ | ⟨mv, _ | ⟨x, rest⟩⟩⟩
      · exact ⟨.ub, rfl, rfl⟩
      · exact ⟨.ub, rfl, rfl⟩
      · simp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalDynSizeAlignOfVal, Trusted.Rustc.V2026_08_01.MirSemantics.evalDynSizeAlignOfVal, hL, homValue, homValues,
          checkDynVTablePtr_hom hmem]
        generalize Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb = pb
        have key : ∀ ok : Bool,
            ∃ c : DynStepClass,
              (match ok with
                | false => Trusted.Rustc.V2026_06_01.MirSemantics.MirStepNode.fail .ub
                | true =>
                  match homDynCheck (Trusted.Rustc.V2026_08_01.MirSemantics.checkDynVTablePtr .none (Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView.ofMemory s8.memory)
                      pb mv k) with
                  | .ub => Trusted.Rustc.V2026_06_01.MirSemantics.MirStepNode.fail .ub
                  | .unsupported => Trusted.Rustc.V2026_06_01.MirSemantics.MirStepNode.unsupported
                  | .ok (entry, _, _) =>
                    Trusted.Rustc.V2026_06_01.MirSemantics.writeIntrinsicReturn s6 l6 d6 bb
                      (.scalar ⟨(match isSize with
                        | true => entry.sizeBytes
                        | false => entry.alignBytes), pb⟩)) = c.run6 s6 l6 d6 bb ∧
              (match ok with
                | false => Trusted.Rustc.V2026_08_01.MirSemantics.MirStepNode.fail .ub
                | true =>
                  match Trusted.Rustc.V2026_08_01.MirSemantics.checkDynVTablePtr .none (Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView.ofMemory s8.memory) pb mv k with
                  | .ub => Trusted.Rustc.V2026_08_01.MirSemantics.MirStepNode.fail .ub
                  | .unsupported => Trusted.Rustc.V2026_08_01.MirSemantics.MirStepNode.unsupported
                  | .ok (entry, _, _) =>
                    Trusted.Rustc.V2026_08_01.MirSemantics.writeIntrinsicReturn s8 l8 d8 bb
                      (.scalar ⟨(match isSize with
                        | true => entry.sizeBytes
                        | false => entry.alignBytes), pb⟩)) = c.run8 s8 l8 d8 bb := by
          intro ok
          cases ok
          · exact ⟨.ub, rfl, rfl⟩
          · cases Trusted.Rustc.V2026_08_01.MirSemantics.checkDynVTablePtr .none (Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView.ofMemory s8.memory) pb mv k with
            | ok w =>
              obtain ⟨e, vts, dts⟩ := w
              cases isSize
              · exact ⟨.write e.alignBytes pb, rfl, rfl⟩
              · exact ⟨.write e.sizeBytes pb, rfl, rfl⟩
            | ub => exact ⟨.ub, rfl, rfl⟩
            | unsupported => exact ⟨.unsupported, rfl, rfl⟩
        rcases dv with _ | sc | ⟨p, n⟩ | ⟨j, gs⟩
        · exact ⟨.ub, rfl, rfl⟩
        · exact key (Nat.beq sc.sizeBytes pb)
        · exact key (Nat.beq n pb)
        · exact ⟨.ub, rfl, rfl⟩
      · exact ⟨.ub, rfl, rfl⟩
    · exact ⟨.ub, rfl, rfl⟩

theorem scalarModulus_hom (n : Nat) : Trusted.Rustc.V2026_06_01.MirSemantics.scalarModulus n = Trusted.Rustc.V2026_08_01.MirSemantics.scalarModulus n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Trusted.Rustc.V2026_06_01.MirSemantics.scalarModulus, Trusted.Rustc.V2026_08_01.MirSemantics.scalarModulus, ih]

theorem wrapScalarBits_hom (v m : Nat) : Trusted.Rustc.V2026_06_01.MirSemantics.wrapScalarBits v m = Trusted.Rustc.V2026_08_01.MirSemantics.wrapScalarBits v m := by
  simp only [Trusted.Rustc.V2026_06_01.MirSemantics.wrapScalarBits, Trusted.Rustc.V2026_08_01.MirSemantics.wrapScalarBits]
  cases Nat.ble m v <;> rfl

theorem isPtrSizedWord_hom (pb : Nat) (v : Trusted.Rustc.V2026_08_01.MirSemantics.Value) :
    Trusted.Rustc.V2026_06_01.MirSemantics.isPtrSizedWord pb (homValue v) = Trusted.Rustc.V2026_08_01.MirSemantics.isPtrSizedWord pb v := by
  cases v <;> rfl

theorem ptrArgDataWord?_hom (pb : Nat) (v : Trusted.Rustc.V2026_08_01.MirSemantics.Value) :
    Trusted.Rustc.V2026_06_01.MirSemantics.ptrArgDataWord? pb (homValue v) = (Trusted.Rustc.V2026_08_01.MirSemantics.ptrArgDataWord? pb v).map homValue := by
  rcases v with _ | sc | ⟨p, n⟩ | ⟨i, fs⟩
  · rfl
  · simp only [homValue, Trusted.Rustc.V2026_06_01.MirSemantics.ptrArgDataWord?, Trusted.Rustc.V2026_08_01.MirSemantics.ptrArgDataWord?, homScalar]
    cases Nat.beq sc.sizeBytes pb <;> rfl
  · simp only [homValue, Trusted.Rustc.V2026_06_01.MirSemantics.ptrArgDataWord?, Trusted.Rustc.V2026_08_01.MirSemantics.ptrArgDataWord?]
    cases Nat.beq n pb <;> rfl
  · rcases i with _ | i
    · rcases fs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      · rfl
      · rfl
      · simp only [homValue, homValues, Trusted.Rustc.V2026_06_01.MirSemantics.ptrArgDataWord?, Trusted.Rustc.V2026_08_01.MirSemantics.ptrArgDataWord?, isPtrSizedWord_hom]
        cases Bool.and (Trusted.Rustc.V2026_08_01.MirSemantics.isPtrSizedWord pb a) (Trusted.Rustc.V2026_08_01.MirSemantics.isPtrSizedWord pb b) <;> rfl
      · rfl
    · rfl

/-- Address-resolution agreement on the two dialects' frame/borrow state at pointer width
`pb`: `ptrAddress?` (the non-`dyn` resolver of `addr_eq`'s data words) agrees on every pointer
of the 08 dialect. Realized by `addrRel_of_no_borrows` whenever both borrow tables are empty. -/
def AddrRel (l6 : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot) (m6 : Trusted.Rustc.V2026_06_01.MirSemantics.Memory) (ld6 : List Trusted.Rustc.V2026_06_01.MirAst.LocalDecl) (La : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (l8 : List Trusted.Rustc.V2026_08_01.MirSemantics.LocalSlot) (m8 : Trusted.Rustc.V2026_08_01.MirSemantics.Memory) (ld8 : List Trusted.Rustc.V2026_08_01.MirAst.LocalDecl) (Lb : Trusted.Rustc.V2026_08_01.Layout.LayoutTable)
    (pb : Nat) : Prop :=
  ∀ p : Trusted.Rustc.V2026_08_01.MirAst.ProvenancePtr,
    Trusted.Rustc.V2026_06_01.MirSemantics.ptrAddress? l6 m6.borrows m6.callerLocals ld6 La pb (homPtr p) m6.callStack =
      Trusted.Rustc.V2026_08_01.MirSemantics.ptrAddress? l8 m8.borrows m8.callerLocals ld8 Lb pb p m8.callStack

theorem resolveWideWordScalar?_hom (l6 : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot) (m6 : Trusted.Rustc.V2026_06_01.MirSemantics.Memory) (ld6 : List Trusted.Rustc.V2026_06_01.MirAst.LocalDecl)
    (La : Trusted.Rustc.V2026_06_01.Layout.LayoutTable) (l8 : List Trusted.Rustc.V2026_08_01.MirSemantics.LocalSlot) (m8 : Trusted.Rustc.V2026_08_01.MirSemantics.Memory) (ld8 : List Trusted.Rustc.V2026_08_01.MirAst.LocalDecl)
    (Lb : Trusted.Rustc.V2026_08_01.Layout.LayoutTable) (pb : Nat) (h : AddrRel l6 m6 ld6 La l8 m8 ld8 Lb pb) (w : Trusted.Rustc.V2026_08_01.MirSemantics.Value) :
    Trusted.Rustc.V2026_06_01.MirSemantics.resolveWideWordScalar? (homValue w) l6 m6.borrows m6.callerLocals ld6 La pb m6.callStack =
      (Trusted.Rustc.V2026_08_01.MirSemantics.resolveWideWordScalar? w l8 m8.borrows m8.callerLocals ld8 Lb pb m8.callStack).map
        homScalar := by
  rcases w with _ | sc | ⟨p, n⟩ | ⟨i, fs⟩
  · rfl
  · simp only [homValue, Trusted.Rustc.V2026_06_01.MirSemantics.resolveWideWordScalar?, Trusted.Rustc.V2026_08_01.MirSemantics.resolveWideWordScalar?, homScalar]
    cases Nat.beq sc.sizeBytes pb
    · rfl
    · simp only [wrapScalarBits_hom, scalarModulus_hom, Option.map_some]
      rfl
  · simp only [homValue, Trusted.Rustc.V2026_06_01.MirSemantics.resolveWideWordScalar?, Trusted.Rustc.V2026_08_01.MirSemantics.resolveWideWordScalar?]
    cases Nat.beq n pb
    · rfl
    · simp only [Trusted.Rustc.V2026_06_01.MirSemantics.ptrAddressScalar?, Trusted.Rustc.V2026_08_01.MirSemantics.ptrAddressScalar?, h p]
      cases Trusted.Rustc.V2026_08_01.MirSemantics.ptrAddress? l8 m8.borrows m8.callerLocals ld8 Lb pb p m8.callStack with
      | none => rfl
      | some a => simp only [wrapScalarBits_hom, scalarModulus_hom, Option.map_some, homScalar]
  · rfl

/-- **C7 (relational)** `evalAddrEqCall` (`core::ptr::addr_eq`, thin-address equality of two
possibly-wide pointers) commutes with the embedding: under `AddrRel` (address resolution of
data words agrees) and equal pointer width, both dialects take the SAME outcome class (`.ub`,
`.unsupported`, or the intrinsic return of the same `bool` scalar) for every argument list of
the 08 dialect and every return-target option. The vtable words are never consulted. -/
theorem evalAddrEqCall_hom (s6 : Trusted.Rustc.V2026_06_01.MirSemantics.MachineState) (s8 : Trusted.Rustc.V2026_08_01.MirSemantics.MachineState)
    (ld6 : List Trusted.Rustc.V2026_06_01.MirAst.LocalDecl) (ld8 : List Trusted.Rustc.V2026_08_01.MirAst.LocalDecl) (La : Trusted.Rustc.V2026_06_01.Layout.LayoutTable) (Lb : Trusted.Rustc.V2026_08_01.Layout.LayoutTable)
    (hL : Trusted.Rustc.V2026_06_01.MirSemantics.layoutPointerBytes La = Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb)
    (l6 : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot) (l8 : List Trusted.Rustc.V2026_08_01.MirSemantics.LocalSlot) (d6 : Trusted.Rustc.V2026_06_01.MirAst.Place) (d8 : Trusted.Rustc.V2026_08_01.MirAst.Place)
    (tb : Option Nat)
    (haddr : AddrRel l6 s6.memory ld6 La l8 s8.memory ld8 Lb (Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb))
    (args : List Trusted.Rustc.V2026_08_01.MirSemantics.Value) :
    ∃ c : DynStepClass,
      Trusted.Rustc.V2026_06_01.MirSemantics.evalAddrEqCall s6 ld6 La (homValues args) l6 d6 tb = c.run6 s6 l6 d6 (tb.getD 0) ∧
      Trusted.Rustc.V2026_08_01.MirSemantics.evalAddrEqCall s8 ld8 Lb args l8 d8 tb = c.run8 s8 l8 d8 (tb.getD 0) := by
  rcases args with _ | ⟨pv, _ | ⟨qv, _ | ⟨x, rest⟩⟩⟩
  · exact ⟨.ub, rfl, rfl⟩
  · exact ⟨.ub, rfl, rfl⟩
  · simp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalAddrEqCall, Trusted.Rustc.V2026_08_01.MirSemantics.evalAddrEqCall, hL, homValues, ptrArgDataWord?_hom]
    cases Trusted.Rustc.V2026_08_01.MirSemantics.ptrArgDataWord? (Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb) pv with
    | none => exact ⟨.ub, rfl, rfl⟩
    | some pw =>
      cases Trusted.Rustc.V2026_08_01.MirSemantics.ptrArgDataWord? (Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb) qv with
      | none => exact ⟨.ub, rfl, rfl⟩
      | some qw =>
        cases tb with
        | none => exact ⟨.ub, rfl, rfl⟩
        | some t =>
          simp only [Option.map_some,
            resolveWideWordScalar?_hom l6 s6.memory ld6 La l8 s8.memory ld8 Lb _ haddr]
          cases Trusted.Rustc.V2026_08_01.MirSemantics.resolveWideWordScalar? pw l8 s8.memory.borrows s8.memory.callerLocals ld8 Lb
              (Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb) s8.memory.callStack with
          | none => exact ⟨.unsupported, rfl, rfl⟩
          | some pa =>
            cases Trusted.Rustc.V2026_08_01.MirSemantics.resolveWideWordScalar? qw l8 s8.memory.borrows s8.memory.callerLocals ld8 Lb
                (Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb) s8.memory.callStack with
            | none => exact ⟨.unsupported, rfl, rfl⟩
            | some qa =>
              cases hb : Nat.beq pa.bits qa.bits
              · exact ⟨.write 0 1, by simp only [Option.map_some, homScalar, hb]; rfl,
                  by simp only [hb]; rfl⟩
              · exact ⟨.write 1 1, by simp only [Option.map_some, homScalar, hb]; rfl,
                  by simp only [hb]; rfl⟩
  · exact ⟨.ub, rfl, rfl⟩

/-- **C7** Scalar/dangling-ZST & `kani#5216` uninhabited reference validity
(`dynRefDataValid` on any scalar address) commutes identically across dialects at EVERY
pointer width `ptrBytes` (32-bit, 64-bit, etc.). -/
theorem dynRefDataValid_scalar_hom
    (l6 : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot)
    (mv6 : Trusted.Rustc.V2026_06_01.MirSemantics.DynMemView)
    (ld6 : List Trusted.Rustc.V2026_06_01.MirAst.LocalDecl)
    (La : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (l8 : List Trusted.Rustc.V2026_08_01.MirSemantics.LocalSlot)
    (mv8 : Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView)
    (ld8 : List Trusted.Rustc.V2026_08_01.MirAst.LocalDecl)
    (Lb : Trusted.Rustc.V2026_08_01.Layout.LayoutTable)
    (ptrBytes : Nat) (sc : Trusted.Rustc.V2026_08_01.MirAst.ScalarInt)
    (entry : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable)
    (isMut checkTB : Bool) :
    Trusted.Rustc.V2026_06_01.MirSemantics.dynRefDataValid l6 mv6 ld6 La ptrBytes
        (.scalar (homScalar sc)) (homVTable entry) isMut checkTB =
      Trusted.Rustc.V2026_08_01.MirSemantics.dynRefDataValid l8 mv8 ld8 Lb ptrBytes
        (.scalar sc) entry isMut checkTB := by
  unfold Trusted.Rustc.V2026_06_01.MirSemantics.dynRefDataValid
    Trusted.Rustc.V2026_08_01.MirSemantics.dynRefDataValid
  simp only [homVTable_isUninhabited, homVTable_alignBytes, homVTable_sizeBytes, homScalar,
    scalarModulus_hom, wrapScalarBits_hom]
  rfl

/-- **C7** Safe-reference (`isRef := true`) `T -> dyn K` unsizing on any scalar address
(covering 32-bit wrapped null, ZST alignment, and `kani#5216` uninhabited `!`) commutes across
dialects at EVERY pointer width under `DynViewRel`. -/
theorem evalThinToDynUnsize_scalarRef_hom
    (l6 : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot)
    (l8 : List Trusted.Rustc.V2026_08_01.MirSemantics.LocalSlot)
    {mv6 : Trusted.Rustc.V2026_06_01.MirSemantics.DynMemView}
    {mv8 : Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView}
    (h : DynViewRel mv6 mv8)
    (ld6 : List Trusted.Rustc.V2026_06_01.MirAst.LocalDecl)
    (ld8 : List Trusted.Rustc.V2026_08_01.MirAst.LocalDecl)
    (La : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (Lb : Trusted.Rustc.V2026_08_01.Layout.LayoutTable)
    (hL : Trusted.Rustc.V2026_06_01.MirSemantics.layoutPointerBytes La =
      Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb)
    (sc : Trusted.Rustc.V2026_08_01.MirAst.ScalarInt)
    (srcPointee : Trusted.Rustc.V2026_08_01.MirAst.RigidTy)
    (dynKey : String) (isMut : Bool) :
    Trusted.Rustc.V2026_06_01.MirSemantics.evalThinToDynUnsize
        l6 mv6 ld6 La (.scalar (homScalar sc)) (homTy srcPointee) dynKey true isMut =
      homDynCheckVal (Trusted.Rustc.V2026_08_01.MirSemantics.evalThinToDynUnsize
        l8 mv8 ld8 Lb (.scalar sc) srcPointee dynKey true isMut) := by
  have hSz : (homScalar sc).sizeBytes = sc.sizeBytes := rfl
  simp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalThinToDynUnsize,
    Trusted.Rustc.V2026_08_01.MirSemantics.evalThinToDynUnsize, hL, hSz, dynVTableEnv?_hom h]
  generalize Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb = pb
  cases Nat.beq sc.sizeBytes pb
  · rfl
  · cases Trusted.Rustc.V2026_08_01.MirSemantics.dynVTableEnv? .none mv8 pb with
    | none => rfl
    | some e =>
      obtain ⟨vts, dts⟩ := e
      simp only [Option.map_some, dynTypeModeled_hom]
      cases Trusted.Rustc.V2026_08_01.MirSemantics.dynTypeModeled dts dynKey
      · rfl
      · simp only [lookupVTableFor_hom]
        cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupVTableFor vts srcPointee dynKey with
        | none => rfl
        | some entry =>
          simp only [Option.map_some]
          rw [dynRefDataValid_scalar_hom l6 mv6 ld6 La l8 mv8 ld8 Lb]
          cases Trusted.Rustc.V2026_08_01.MirSemantics.dynRefDataValid l8 mv8 ld8 Lb pb
            (.scalar sc) entry isMut true <;> rfl

/-- **C7** Safe-reference (`isRef := true`) `dyn Src -> dyn Dst` NOP and trait upcasting on any
scalar address commutes across dialects at EVERY pointer width under `DynViewRel`. -/
theorem evalDynToDynUnsize_scalarRef_hom
    (l6 : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot)
    (l8 : List Trusted.Rustc.V2026_08_01.MirSemantics.LocalSlot)
    {mv6 : Trusted.Rustc.V2026_06_01.MirSemantics.DynMemView}
    {mv8 : Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView}
    (h : DynViewRel mv6 mv8)
    (ld6 : List Trusted.Rustc.V2026_06_01.MirAst.LocalDecl)
    (ld8 : List Trusted.Rustc.V2026_08_01.MirAst.LocalDecl)
    (La : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (Lb : Trusted.Rustc.V2026_08_01.Layout.LayoutTable)
    (hL : Trusted.Rustc.V2026_06_01.MirSemantics.layoutPointerBytes La =
      Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb)
    (sc : Trusted.Rustc.V2026_08_01.MirAst.ScalarInt)
    (metaVal : Trusted.Rustc.V2026_08_01.MirSemantics.Value)
    (srcKey dstKey : String) (isMut : Bool) :
    Trusted.Rustc.V2026_06_01.MirSemantics.evalDynToDynUnsize
        l6 mv6 ld6 La (.aggregate 0 [.scalar (homScalar sc), homValue metaVal]) srcKey dstKey true isMut =
      homDynCheckVal (Trusted.Rustc.V2026_08_01.MirSemantics.evalDynToDynUnsize
        l8 mv8 ld8 Lb (.aggregate 0 [.scalar sc, metaVal]) srcKey dstKey true isMut) := by
  have hSz : (homScalar sc).sizeBytes = sc.sizeBytes := rfl
  simp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalDynToDynUnsize,
    Trusted.Rustc.V2026_08_01.MirSemantics.evalDynToDynUnsize, hL, hSz, stringEq_hom,
    checkDynVTablePtr_hom h]
  generalize Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes Lb = pb
  cases Nat.beq sc.sizeBytes pb
  · rfl
  · cases Trusted.Rustc.V2026_08_01.MirSemantics.stringEq srcKey dstKey
    · cases Trusted.Rustc.V2026_08_01.MirSemantics.checkDynVTablePtr .none mv8 pb metaVal srcKey with
      | ub => rfl
      | unsupported => rfl
      | ok w =>
        obtain ⟨entry, vts, dts⟩ := w
        simp only [homDynCheck, lookupDynType_hom, dynTypeModeled_hom, resolveUpcastVTable?_hom]
        cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupDynType dts srcKey with
        | none =>
          cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupDynType dts dstKey with
          | none =>
            cases Trusted.Rustc.V2026_08_01.MirSemantics.dynTypeModeled dts dstKey
            · rfl
            · cases Trusted.Rustc.V2026_08_01.MirSemantics.resolveUpcastVTable? vts dts entry dstKey with
              | none => rfl
              | some dstEntry =>
                simp only [Option.map_some]
                rw [dynRefDataValid_scalar_hom l6 mv6 ld6 La l8 mv8 ld8 Lb]
                cases Trusted.Rustc.V2026_08_01.MirSemantics.dynRefDataValid l8 mv8 ld8 Lb pb
                  (.scalar sc) dstEntry isMut true <;> rfl
          | some dd =>
            simp only [Option.map_none, Option.map_some, homDynType_autoTraits]
            cases dd.autoTraits with
            | nil =>
              cases Trusted.Rustc.V2026_08_01.MirSemantics.dynTypeModeled dts dstKey
              · rfl
              · cases Trusted.Rustc.V2026_08_01.MirSemantics.resolveUpcastVTable? vts dts entry dstKey with
                | none => rfl
                | some dstEntry =>
                  simp only [Option.map_some]
                  rw [dynRefDataValid_scalar_hom l6 mv6 ld6 La l8 mv8 ld8 Lb]
                  cases Trusted.Rustc.V2026_08_01.MirSemantics.dynRefDataValid l8 mv8 ld8 Lb pb
                    (.scalar sc) dstEntry isMut true <;> rfl
            | cons _ _ => rfl
        | some ds =>
          cases Trusted.Rustc.V2026_08_01.MirSemantics.lookupDynType dts dstKey with
          | none =>
            cases Trusted.Rustc.V2026_08_01.MirSemantics.dynTypeModeled dts dstKey
            · rfl
            · cases Trusted.Rustc.V2026_08_01.MirSemantics.resolveUpcastVTable? vts dts entry dstKey with
              | none => rfl
              | some dstEntry =>
                simp only [Option.map_some]
                rw [dynRefDataValid_scalar_hom l6 mv6 ld6 La l8 mv8 ld8 Lb]
                cases Trusted.Rustc.V2026_08_01.MirSemantics.dynRefDataValid l8 mv8 ld8 Lb pb
                  (.scalar sc) dstEntry isMut true <;> rfl
          | some dd =>
            simp only [Option.map_some, homDynType_autoTraits, defPathsSubset_hom]
            cases Trusted.Rustc.V2026_08_01.MirSemantics.defPathsSubset dd.autoTraits ds.autoTraits
            · rfl
            · cases Trusted.Rustc.V2026_08_01.MirSemantics.dynTypeModeled dts dstKey
              · rfl
              · cases Trusted.Rustc.V2026_08_01.MirSemantics.resolveUpcastVTable? vts dts entry dstKey with
                | none => rfl
                | some dstEntry =>
                  simp only [Option.map_some]
                  rw [dynRefDataValid_scalar_hom l6 mv6 ld6 La l8 mv8 ld8 Lb]
                  cases Trusted.Rustc.V2026_08_01.MirSemantics.dynRefDataValid l8 mv8 ld8 Lb pb
                    (.scalar sc) dstEntry isMut true <;> rfl
    · cases Trusted.Rustc.V2026_08_01.MirSemantics.checkDynVTablePtr .none mv8 pb metaVal srcKey with
      | ub => rfl
      | unsupported => rfl
      | ok w =>
        obtain ⟨srcEntry, _, _⟩ := w
        simp only [homDynCheck]
        rw [dynRefDataValid_scalar_hom l6 mv6 ld6 La l8 mv8 ld8 Lb]
        cases Trusted.Rustc.V2026_08_01.MirSemantics.dynRefDataValid l8 mv8 ld8 Lb pb
          (.scalar sc) srcEntry isMut true <;> rfl

theorem stackLocalAddrPageBase_hom (pb : Nat) :
    Trusted.Rustc.V2026_06_01.MirSemantics.stackLocalAddrPageBase pb =
      Trusted.Rustc.V2026_08_01.MirSemantics.stackLocalAddrPageBase pb := by
  unfold Trusted.Rustc.V2026_06_01.MirSemantics.stackLocalAddrPageBase
    Trusted.Rustc.V2026_08_01.MirSemantics.stackLocalAddrPageBase
  cases Nat.ble 8 pb <;> rfl

/-- Correspondence of two non-empty root-local borrow tables (every tracked tag points to the
same `targetLocal` with empty `targetProjection`, matching `&x` / `&mut x` stack borrows). -/
def RootBorrowsRel
    (bs6 : List Trusted.Rustc.V2026_06_01.MirSemantics.BorrowEntry)
    (bs8 : List Trusted.Rustc.V2026_08_01.MirSemantics.BorrowEntry) : Prop :=
  (∀ tag,
    (Trusted.Rustc.V2026_06_01.MirSemantics.lookupBorrow bs6 tag).map (·.targetLocal) =
      (Trusted.Rustc.V2026_08_01.MirSemantics.lookupBorrow bs8 tag).map (·.targetLocal)) ∧
  (∀ tag b6, Trusted.Rustc.V2026_06_01.MirSemantics.lookupBorrow bs6 tag = .some b6 →
    b6.targetProjection = []) ∧
  (∀ tag b8, Trusted.Rustc.V2026_08_01.MirSemantics.lookupBorrow bs8 tag = .some b8 →
    b8.targetProjection = [])

/-- Realizability of `AddrRel` for arbitrary non-empty root-local borrow tables (covering
distinct borrow tags aliasing the same stack local). -/
theorem addrRel_of_root_borrows
    (l6 : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot)
    (m6 : Trusted.Rustc.V2026_06_01.MirSemantics.Memory)
    (ld6 : List Trusted.Rustc.V2026_06_01.MirAst.LocalDecl)
    (La : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (l8 : List Trusted.Rustc.V2026_08_01.MirSemantics.LocalSlot)
    (m8 : Trusted.Rustc.V2026_08_01.MirSemantics.Memory)
    (ld8 : List Trusted.Rustc.V2026_08_01.MirAst.LocalDecl)
    (Lb : Trusted.Rustc.V2026_08_01.Layout.LayoutTable)
    (pb : Nat) (hrb : RootBorrowsRel m6.borrows m8.borrows) :
    AddrRel l6 m6 ld6 La l8 m8 ld8 Lb pb := by
  obtain ⟨hLoc, hProj6, hProj8⟩ := hrb
  intro p
  unfold Trusted.Rustc.V2026_06_01.MirSemantics.ptrAddress?
    Trusted.Rustc.V2026_08_01.MirSemantics.ptrAddress?
  have ht := hLoc (Trusted.Rustc.V2026_08_01.MirAst.ProvenancePtr.tag p)
  simp only [homPtr_tag, homPtr_allocId, homPtr_offsetBytes]
  cases hb6 : Trusted.Rustc.V2026_06_01.MirSemantics.lookupBorrow m6.borrows
      (Trusted.Rustc.V2026_08_01.MirAst.ProvenancePtr.tag p) with
  | none =>
    cases hb8 : Trusted.Rustc.V2026_08_01.MirSemantics.lookupBorrow m8.borrows
        (Trusted.Rustc.V2026_08_01.MirAst.ProvenancePtr.tag p) with
    | none => rfl
    | some b8 => simp [hb6, hb8] at ht
  | some b6 =>
    cases hb8 : Trusted.Rustc.V2026_08_01.MirSemantics.lookupBorrow m8.borrows
        (Trusted.Rustc.V2026_08_01.MirAst.ProvenancePtr.tag p) with
    | none => simp [hb6, hb8] at ht
    | some b8 =>
      simp only [hb6, hb8, Option.map_some, Option.some.injEq] at ht
      have hp6 := hProj6 _ _ hb6
      have hp8 := hProj8 _ _ hb8
      unfold Trusted.Rustc.V2026_06_01.MirSemantics.borrowBaseAddress?
        Trusted.Rustc.V2026_08_01.MirSemantics.borrowBaseAddress?
        Trusted.Rustc.V2026_06_01.MirSemantics.borrowPlaceByteOffset?
        Trusted.Rustc.V2026_08_01.MirSemantics.borrowPlaceByteOffset?
      simp only [hp6, hp8, ht, stackLocalAddrPageBase_hom]
      rfl

/-- Realizability of `AddrRel`: with empty borrow tables both resolvers compute the synthetic
address `allocId * 65536 + offsetBytes` of every pointer. -/
theorem addrRel_of_no_borrows (l6 : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot) (m6 : Trusted.Rustc.V2026_06_01.MirSemantics.Memory) (ld6 : List Trusted.Rustc.V2026_06_01.MirAst.LocalDecl)
    (La : Trusted.Rustc.V2026_06_01.Layout.LayoutTable) (l8 : List Trusted.Rustc.V2026_08_01.MirSemantics.LocalSlot) (m8 : Trusted.Rustc.V2026_08_01.MirSemantics.Memory) (ld8 : List Trusted.Rustc.V2026_08_01.MirAst.LocalDecl)
    (Lb : Trusted.Rustc.V2026_08_01.Layout.LayoutTable) (pb : Nat) (h6 : m6.borrows = []) (h8 : m8.borrows = []) :
    AddrRel l6 m6 ld6 La l8 m8 ld8 Lb pb :=
  addrRel_of_root_borrows l6 m6 ld6 La l8 m8 ld8 Lb pb
    ⟨fun _ => by simp [h6, h8, Trusted.Rustc.V2026_06_01.MirSemantics.lookupBorrow, Trusted.Rustc.V2026_08_01.MirSemantics.lookupBorrow],
     fun _ _ h => by simp [h6, Trusted.Rustc.V2026_06_01.MirSemantics.lookupBorrow] at h,
     fun _ _ h => by simp [h8, Trusted.Rustc.V2026_08_01.MirSemantics.lookupBorrow] at h⟩

/-! ## Realizability witnesses (every relation / hypothesis is inhabited) and non-vacuity of
every outcome class -/

/-- Witness `u32` type layout (dialect 06). -/
def wTyLayout6 : Trusted.Rustc.V2026_06_01.Layout.TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 },
    backendRepr := .scalar (.initialized (.int 32 false) { start := 0, end_ := 4294967295 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- Witness `u32` type layout (dialect 08). -/
def wTyLayout8 : Trusted.Rustc.V2026_08_01.Layout.TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 },
    backendRepr := .scalar (.initialized (.int 32 false) { start := 0, end_ := 4294967295 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- Witness 64-bit layout table (dialect 06). -/
def wLayouts6 : Trusted.Rustc.V2026_06_01.Layout.LayoutTable := { pointerBits := 64, isLittleEndian := true, entries := [wTyLayout6] }

/-- Witness 64-bit layout table (dialect 08). -/
def wLayouts8 : Trusted.Rustc.V2026_08_01.Layout.LayoutTable := { pointerBits := 64, isLittleEndian := true, entries := [wTyLayout8] }

/-- Witness vtable of `(u32, dyn Tr)` (dialect 08). -/
def wVTable8 : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable :=
  { vtableId := 0, vtableAllocId := 16384, concreteTy := .uint .u32, dynKey := "Tr", sizeBytes := 4,
    alignBytes := 4, slots := [.dropInPlace .none, .size, .align, .method "Tr::m" []] }

/-- Witness linked body carrying `wVTable8` (dialect 08). -/
def wBody8 : Trusted.Rustc.V2026_08_01.MirAst.CapturedMir :=
  { defPath := "w", phase := .runtimePostCleanup, role := .subject, argCount := 0, localDecls := [],
    basicBlocks := [],
    fnAbi := { args := [], ret := { layout := wTyLayout8, mode := .direct }, conv := .rust,
               canUnwind := true },
    layouts := wLayouts8, allocations := [], vtables := [wVTable8] }

/-- Witness linked body carrying the embedded vtable `homVTable wVTable8` (dialect 06). -/
def wBody6 : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir :=
  { defPath := "w", phase := .runtimePostCleanup, role := .subject, argCount := 0, localDecls := [],
    basicBlocks := [],
    fnAbi := { args := [], ret := { layout := wTyLayout6, mode := .direct }, conv := .rust,
               canUnwind := true },
    layouts := wLayouts6, allocations := [], vtables := [homVTable wVTable8] }

/-- Witness machine state linking `wBody8` (dialect 08). -/
def wState8 : Trusted.Rustc.V2026_08_01.MirSemantics.MachineState := Trusted.Rustc.V2026_08_01.MirSemantics.initMachineStateWithCallees wBody8 [] [wBody8]

/-- Witness machine state linking `wBody6` (dialect 06). -/
def wState6 : Trusted.Rustc.V2026_06_01.MirSemantics.MachineState := Trusted.Rustc.V2026_06_01.MirSemantics.initMachineStateWithCallees wBody6 [] [wBody6]

/-- Witness states with no linked bodies (no vtable environment). -/
def wBare8 : Trusted.Rustc.V2026_08_01.MirSemantics.MachineState := { wState8 with memory := { wState8.memory with callees := [] } }

/-- Witness states with no linked bodies (no vtable environment). -/
def wBare6 : Trusted.Rustc.V2026_06_01.MirSemantics.MachineState := { wState6 with memory := { wState6.memory with callees := [] } }

/-- Witness destination place `_0` (dialect 06). -/
def wPlace6 : Trusted.Rustc.V2026_06_01.MirAst.Place := { local_ := 0, projection := [] }

/-- Witness destination place `_0` (dialect 08). -/
def wPlace8 : Trusted.Rustc.V2026_08_01.MirAst.Place := { local_ := 0, projection := [] }

/-- Realizability of `DynMemRel` / `DynViewRel` / `BodiesRel` on a non-empty vtable table. -/
theorem wState_dynMemRel : DynMemRel wState6.memory wState8.memory :=
  ⟨⟨rfl, rfl⟩, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Realizability of `DynMemRel` on the empty environment. -/
theorem wBare_dynMemRel : DynMemRel wBare6.memory wBare8.memory :=
  ⟨⟨rfl, rfl⟩, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Realizability of the pointer-width hypothesis. -/
theorem wLayouts_ptrBytes : Trusted.Rustc.V2026_06_01.MirSemantics.layoutPointerBytes wLayouts6 = Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes wLayouts8 := rfl

/-- Realizability of `AddrRel` on the witness states. -/
theorem wState_addrRel :
    AddrRel [] wState6.memory [] wLayouts6 [] wState8.memory [] wLayouts8
      (Trusted.Rustc.V2026_08_01.MirSemantics.layoutPointerBytes wLayouts8) :=
  addrRel_of_no_borrows _ _ _ _ _ _ _ _ _ rfl rfl

/-- A `&dyn Tr` wide pointer to data allocation `1` with vtable pointer `(allocId, offset)`. -/
def wDynRef (vtAlloc vtOff : Nat) : Trusted.Rustc.V2026_08_01.MirSemantics.Value :=
  .aggregate 0 [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := vtAlloc, offsetBytes := vtOff } 8]

/-- Locals of the successor frame of a silent step (`none` for faults / other nodes): pins the
value actually written by `writeIntrinsicReturn` (dialect 06). -/
def stepLocals6 : Trusted.Rustc.V2026_06_01.MirSemantics.MirStepNode → Option (List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot)
  | .tau (.running s) => .some s.frame.locals
  | _ => .none

/-- Locals of the successor frame of a silent step (dialect 08). -/
def stepLocals8 : Trusted.Rustc.V2026_08_01.MirSemantics.MirStepNode → Option (List Trusted.Rustc.V2026_08_01.MirSemantics.LocalSlot)
  | .tau (.running s) => .some s.frame.locals
  | _ => .none

/-- The `.write` witnesses really write: `size_of_val`/`align_of_val` store `4usize` into the
live local `_0` in BOTH dialects, and `addr_eq` stores `true` / `false`. -/
theorem witness_written_values :
    stepLocals6 (Trusted.Rustc.V2026_06_01.MirSemantics.evalDynSizeAlignOfVal wState6 wLayouts6 [.uninit] wPlace6 1
        (homValue (wDynRef 16384 0)) "Tr" true) = .some [.init (.scalar ⟨4, 8⟩)] ∧
      stepLocals8 (Trusted.Rustc.V2026_08_01.MirSemantics.evalDynSizeAlignOfVal wState8 wLayouts8 [.uninit] wPlace8 1
        (wDynRef 16384 0) "Tr" true) = .some [.init (.scalar ⟨4, 8⟩)] ∧
      stepLocals6 (Trusted.Rustc.V2026_06_01.MirSemantics.evalAddrEqCall wState6 [] wLayouts6
        (homValues [wDynRef 16384 0, .ptr { allocId := 1, offsetBytes := 0 } 8]) [.uninit] wPlace6
        (.some 1)) = .some [.init (.scalar ⟨1, 1⟩)] ∧
      stepLocals8 (Trusted.Rustc.V2026_08_01.MirSemantics.evalAddrEqCall wState8 [] wLayouts8
        [wDynRef 16384 0, .ptr { allocId := 1, offsetBytes := 0 } 8] [.uninit] wPlace8 (.some 1)) =
        .some [.init (.scalar ⟨1, 1⟩)] ∧
      stepLocals6 (Trusted.Rustc.V2026_06_01.MirSemantics.evalAddrEqCall wState6 [] wLayouts6
        (homValues [wDynRef 16384 0, .ptr { allocId := 2, offsetBytes := 0 } 8]) [.uninit] wPlace6
        (.some 1)) = .some [.init (.scalar ⟨0, 1⟩)] ∧
      stepLocals8 (Trusted.Rustc.V2026_08_01.MirSemantics.evalAddrEqCall wState8 [] wLayouts8
        [wDynRef 16384 0, .ptr { allocId := 2, offsetBytes := 0 } 8] [.uninit] wPlace8 (.some 1)) =
        .some [.init (.scalar ⟨0, 1⟩)] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Non-vacuity of `evalDynSizeAlignOfVal_hom`, class `.write`: `size_of_val::<dyn Tr>` returns
`4usize` and `align_of_val` returns `4usize` in BOTH dialects. -/
theorem evalDynSizeAlignOfVal_witness_write :
    Trusted.Rustc.V2026_06_01.MirSemantics.evalDynSizeAlignOfVal wState6 wLayouts6 [.uninit] wPlace6 1 (homValue (wDynRef 16384 0)) "Tr" true =
        DynStepClass.run6 (.write 4 8) wState6 [.uninit] wPlace6 1 ∧
      Trusted.Rustc.V2026_08_01.MirSemantics.evalDynSizeAlignOfVal wState8 wLayouts8 [.uninit] wPlace8 1 (wDynRef 16384 0) "Tr" true =
        DynStepClass.run8 (.write 4 8) wState8 [.uninit] wPlace8 1 ∧
      Trusted.Rustc.V2026_06_01.MirSemantics.evalDynSizeAlignOfVal wState6 wLayouts6 [.uninit] wPlace6 1 (homValue (wDynRef 16384 0)) "Tr" false =
        DynStepClass.run6 (.write 4 8) wState6 [.uninit] wPlace6 1 ∧
      Trusted.Rustc.V2026_08_01.MirSemantics.evalDynSizeAlignOfVal wState8 wLayouts8 [.uninit] wPlace8 1 (wDynRef 16384 0) "Tr" false =
        DynStepClass.run8 (.write 4 8) wState8 [.uninit] wPlace8 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Non-vacuity of `evalDynSizeAlignOfVal_hom`, class `.ub`: a vtable pointer at non-zero offset
(`InvalidVTablePointer`) and a vtable of an incompatible modeled trait (`Tr` vs expected `Alt`)
both fault `.ub` in BOTH dialects. -/
theorem evalDynSizeAlignOfVal_witness_ub :
    Trusted.Rustc.V2026_06_01.MirSemantics.evalDynSizeAlignOfVal wState6 wLayouts6 [.uninit] wPlace6 1 (homValue (wDynRef 16384 1)) "Tr" true =
        DynStepClass.run6 .ub wState6 [.uninit] wPlace6 1 ∧
      Trusted.Rustc.V2026_08_01.MirSemantics.evalDynSizeAlignOfVal wState8 wLayouts8 [.uninit] wPlace8 1 (wDynRef 16384 1) "Tr" true =
        DynStepClass.run8 .ub wState8 [.uninit] wPlace8 1 ∧
      Trusted.Rustc.V2026_06_01.MirSemantics.evalDynSizeAlignOfVal wState6 wLayouts6 [.uninit] wPlace6 1 (homValue (wDynRef 16384 0)) "Alt" true =
        DynStepClass.run6 .ub wState6 [.uninit] wPlace6 1 ∧
      Trusted.Rustc.V2026_08_01.MirSemantics.evalDynSizeAlignOfVal wState8 wLayouts8 [.uninit] wPlace8 1 (wDynRef 16384 0) "Alt" true =
        DynStepClass.run8 .ub wState8 [.uninit] wPlace8 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Non-vacuity of `evalDynSizeAlignOfVal_hom`, class `.unsupported`: with no linked vtable
environment both dialects fail closed. -/
theorem evalDynSizeAlignOfVal_witness_unsupported :
    Trusted.Rustc.V2026_06_01.MirSemantics.evalDynSizeAlignOfVal wBare6 wLayouts6 [.uninit] wPlace6 1 (homValue (wDynRef 16384 0)) "Tr" true =
        DynStepClass.run6 .unsupported wBare6 [.uninit] wPlace6 1 ∧
      Trusted.Rustc.V2026_08_01.MirSemantics.evalDynSizeAlignOfVal wBare8 wLayouts8 [.uninit] wPlace8 1 (wDynRef 16384 0) "Tr" true =
        DynStepClass.run8 .unsupported wBare8 [.uninit] wPlace8 1 :=
  ⟨rfl, rfl⟩

/-- Non-vacuity of `evalAddrEqCall_hom`, class `.write`: `addr_eq(p as *const dyn Tr, p)` is
`true` (vtable word ignored) and `addr_eq` of distinct allocations is `false`, in BOTH dialects. -/
theorem evalAddrEqCall_witness_write :
    Trusted.Rustc.V2026_06_01.MirSemantics.evalAddrEqCall wState6 [] wLayouts6
        (homValues [wDynRef 16384 0, .ptr { allocId := 1, offsetBytes := 0 } 8]) [.uninit] wPlace6 (.some 1) =
        DynStepClass.run6 (.write 1 1) wState6 [.uninit] wPlace6 1 ∧
      Trusted.Rustc.V2026_08_01.MirSemantics.evalAddrEqCall wState8 [] wLayouts8
        [wDynRef 16384 0, .ptr { allocId := 1, offsetBytes := 0 } 8] [.uninit] wPlace8 (.some 1) =
        DynStepClass.run8 (.write 1 1) wState8 [.uninit] wPlace8 1 ∧
      Trusted.Rustc.V2026_06_01.MirSemantics.evalAddrEqCall wState6 [] wLayouts6
        (homValues [wDynRef 16384 0, .ptr { allocId := 2, offsetBytes := 0 } 8]) [.uninit] wPlace6 (.some 1) =
        DynStepClass.run6 (.write 0 1) wState6 [.uninit] wPlace6 1 ∧
      Trusted.Rustc.V2026_08_01.MirSemantics.evalAddrEqCall wState8 [] wLayouts8
        [wDynRef 16384 0, .ptr { allocId := 2, offsetBytes := 0 } 8] [.uninit] wPlace8 (.some 1) =
        DynStepClass.run8 (.write 0 1) wState8 [.uninit] wPlace8 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Non-vacuity of `evalAddrEqCall_hom`, class `.ub`: a missing return target and a
non-pointer-sized argument both fault `.ub` in BOTH dialects. -/
theorem evalAddrEqCall_witness_ub :
    Trusted.Rustc.V2026_06_01.MirSemantics.evalAddrEqCall wState6 [] wLayouts6
        (homValues [wDynRef 16384 0, wDynRef 16384 0]) [.uninit] wPlace6 .none =
        DynStepClass.run6 .ub wState6 [.uninit] wPlace6 0 ∧
      Trusted.Rustc.V2026_08_01.MirSemantics.evalAddrEqCall wState8 [] wLayouts8 [wDynRef 16384 0, wDynRef 16384 0] [.uninit] wPlace8 .none =
        DynStepClass.run8 .ub wState8 [.uninit] wPlace8 0 ∧
      Trusted.Rustc.V2026_06_01.MirSemantics.evalAddrEqCall wState6 [] wLayouts6
        (homValues [.ptr { allocId := 1, offsetBytes := 0 } 4, wDynRef 16384 0]) [.uninit] wPlace6 (.some 1) =
        DynStepClass.run6 .ub wState6 [.uninit] wPlace6 1 ∧
      Trusted.Rustc.V2026_08_01.MirSemantics.evalAddrEqCall wState8 [] wLayouts8
        [.ptr { allocId := 1, offsetBytes := 0 } 4, wDynRef 16384 0] [.uninit] wPlace8 (.some 1) =
        DynStepClass.run8 .ub wState8 [.uninit] wPlace8 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Realizability of `OptBodyRel` on `.some` bodies (`wBody6` and `wBody8`). -/
theorem wBody_optBodyRel : OptBodyRel (.some wBody6) (.some wBody8) :=
  .some wBody6 wBody8 rfl rfl

/-- Non-vacuity of `checkDynVTablePtr_opt_hom` on `currentBody = .some _` (virtual-call / safe
`size_of_val` path): `wBare6`/`wBare8` have empty `callees`, so ONLY `currentBody` supplies the
vtable, and both dialects return `.ok` with the same entry. -/
theorem checkDynVTablePtr_opt_witness :
    Trusted.Rustc.V2026_06_01.MirSemantics.checkDynVTablePtr (.some wBody6)
        (Trusted.Rustc.V2026_06_01.MirSemantics.DynMemView.ofMemory wBare6.memory) 8
        (homValue (.ptr { allocId := 16384, offsetBytes := 0 } 8)) "Tr" =
      .ok (homVTable wVTable8, [homVTable wVTable8], []) ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.checkDynVTablePtr (.some wBody8)
        (Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView.ofMemory wBare8.memory) 8
        (.ptr { allocId := 16384, offsetBytes := 0 } 8) "Tr" =
      .ok (wVTable8, [wVTable8], []) :=
  ⟨rfl, rfl⟩

/-- Witness 32-bit layout tables (`pointerBits := 32`) in both dialects. -/
def wLayouts32_6 : Trusted.Rustc.V2026_06_01.Layout.LayoutTable :=
  { pointerBits := 32, isLittleEndian := true, entries := [wTyLayout6] }

def wLayouts32_8 : Trusted.Rustc.V2026_08_01.Layout.LayoutTable :=
  { pointerBits := 32, isLittleEndian := true, entries := [wTyLayout8] }

/-- Witness uninhabited ZST vtable (`! : dyn Tr`, `kani#5216`). -/
def wVTableUninhab8 : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable :=
  { vtableId := 1, vtableAllocId := 16385, concreteTy := .never, dynKey := "Tr",
    sizeBytes := 0, alignBytes := 1, isUninhabited := true,
    slots := [.dropInPlace .none, .size, .align] }

/-- Witness inhabited ZST vtable (`() : dyn Tr`, size 0, align 1). -/
def wVTableZst8 : Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable :=
  { vtableId := 2, vtableAllocId := 16386, concreteTy := .tuple [], dynKey := "Tr",
    sizeBytes := 0, alignBytes := 1, isUninhabited := false,
    slots := [.dropInPlace .none, .size, .align] }

/-- Non-vacuity of `evalThinToDynUnsize_raw_hom` at both 32-bit and 64-bit pointer widths. -/
theorem evalThinToDynUnsize_raw_witness_32bit_64bit :
    Trusted.Rustc.V2026_06_01.MirSemantics.evalThinToDynUnsize []
        (Trusted.Rustc.V2026_06_01.MirSemantics.DynMemView.ofMemory wState6.memory) [] wLayouts32_6
        (homValue (.scalar ⟨0, 4⟩)) (homTy (.uint .u32)) "Tr" false false =
      homDynCheckVal (Trusted.Rustc.V2026_08_01.MirSemantics.evalThinToDynUnsize []
        (Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView.ofMemory wState8.memory) [] wLayouts32_8
        (.scalar ⟨0, 4⟩) (.uint .u32) "Tr" false false) ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalThinToDynUnsize []
        (Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView.ofMemory wState8.memory) [] wLayouts32_8
        (.scalar ⟨0, 4⟩) (.uint .u32) "Tr" false false =
      .ok (.aggregate 0 [.scalar ⟨0, 4⟩, .ptr { allocId := 16384, offsetBytes := 0 } 4]) ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalThinToDynUnsize []
        (Trusted.Rustc.V2026_06_01.MirSemantics.DynMemView.ofMemory wState6.memory) [] wLayouts6
        (homValue (.scalar ⟨0, 8⟩)) (homTy (.uint .u32)) "Tr" false false =
      .ok (.aggregate 0 [.scalar ⟨0, 8⟩, .ptr { allocId := 16384, offsetBytes := 0 } 8]) :=
  ⟨rfl, rfl, rfl⟩

/-- Non-vacuity of `dynRefDataValid_scalar_hom`: 32-bit wrapped `2^32` null fails (`false`),
aligned non-null `4` succeeds (`true`) on ZST, and uninhabited `!` (`kani#5216`) fails (`false`)
in BOTH dialects. -/
theorem dynRefDataValid_scalar_witness_32bit_uninhabited :
    Trusted.Rustc.V2026_06_01.MirSemantics.dynRefDataValid []
        (Trusted.Rustc.V2026_06_01.MirSemantics.DynMemView.ofMemory wState6.memory) [] wLayouts32_6 4
        (.scalar (homScalar ⟨4294967296, 4⟩)) (homVTable wVTableZst8) false true = false ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.dynRefDataValid []
        (Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView.ofMemory wState8.memory) [] wLayouts32_8 4
        (.scalar ⟨4294967296, 4⟩) wVTableZst8 false true = false ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.dynRefDataValid []
        (Trusted.Rustc.V2026_06_01.MirSemantics.DynMemView.ofMemory wState6.memory) [] wLayouts32_6 4
        (.scalar (homScalar ⟨4, 4⟩)) (homVTable wVTableZst8) false true = true ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.dynRefDataValid []
        (Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView.ofMemory wState8.memory) [] wLayouts32_8 4
        (.scalar ⟨4, 4⟩) wVTableZst8 false true = true ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.dynRefDataValid []
        (Trusted.Rustc.V2026_06_01.MirSemantics.DynMemView.ofMemory wState6.memory) [] wLayouts32_6 4
        (.scalar (homScalar ⟨4, 4⟩)) (homVTable wVTableUninhab8) false true = false ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.dynRefDataValid []
        (Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView.ofMemory wState8.memory) [] wLayouts32_8 4
        (.scalar ⟨4, 4⟩) wVTableUninhab8 false true = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Non-empty root-local borrow states in both dialects: TWO distinct borrow tags (`1` and `2`)
both aliasing stack local `_1` (empty `targetProjection`). -/
def wBorrowState6 : Trusted.Rustc.V2026_06_01.MirSemantics.MachineState :=
  { wState6 with
    memory := { wState6.memory with
      borrows :=
        [ { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen },
          { tag := 2, targetLocal := 1, targetProjection := [], perm := .frozen } ] } }

def wBorrowState8 : Trusted.Rustc.V2026_08_01.MirSemantics.MachineState :=
  { wState8 with
    memory := { wState8.memory with
      borrows :=
        [ { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen },
          { tag := 2, targetLocal := 1, targetProjection := [], perm := .frozen } ] } }

/-- Realizability of `addrRel_of_root_borrows` on non-empty multi-tag borrow states. -/
theorem wBorrowState_addrRel :
    AddrRel [] wBorrowState6.memory [] wLayouts6 [] wBorrowState8.memory [] wLayouts8 8 := by
  apply addrRel_of_root_borrows
  refine ⟨?_, ?_, ?_⟩
  · intro tag
    simp only [wBorrowState6, wBorrowState8, Trusted.Rustc.V2026_06_01.MirSemantics.lookupBorrow,
      Trusted.Rustc.V2026_08_01.MirSemantics.lookupBorrow]
    cases Nat.beq 1 tag <;> cases Nat.beq 2 tag <;> rfl
  · intro tag b6 h
    simp only [wBorrowState6, Trusted.Rustc.V2026_06_01.MirSemantics.lookupBorrow] at h
    cases h1 : Nat.beq 1 tag
    · simp only [h1] at h
      cases h2 : Nat.beq 2 tag
      · simp [h2] at h
      · simp only [h2, Option.some.injEq] at h; rw [← h]
    · simp only [h1, Option.some.injEq] at h; rw [← h]
  · intro tag b8 h
    simp only [wBorrowState8, Trusted.Rustc.V2026_08_01.MirSemantics.lookupBorrow] at h
    cases h1 : Nat.beq 1 tag
    · simp only [h1] at h
      cases h2 : Nat.beq 2 tag
      · simp [h2] at h
      · simp only [h2, Option.some.injEq] at h; rw [← h]
    · simp only [h1, Option.some.injEq] at h; rw [← h]

/-- Non-vacuity of `evalAddrEqCall_hom` with NON-EMPTY borrow tables (`rust#166144`): two wide
pointers carrying DIFFERENT borrow tags (`1` vs `2`) to the SAME stack local `_1` AND DIFFERENT
vtable pointers (`16384` vs `16385`) compare equal (`1`) in BOTH dialects. -/
theorem evalAddrEqCall_witness_nonempty_borrows :
    let p1 : Trusted.Rustc.V2026_08_01.MirSemantics.Value :=
      .aggregate 0 [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 16384, offsetBytes := 0 } 8]
    let p2 : Trusted.Rustc.V2026_08_01.MirSemantics.Value :=
      .aggregate 0 [.ptr { allocId := 2, offsetBytes := 0 } 8, .ptr { allocId := 16385, offsetBytes := 0 } 8]
    Trusted.Rustc.V2026_06_01.MirSemantics.evalAddrEqCall wBorrowState6 [] wLayouts6
        (homValues [p1, p2]) [.uninit] wPlace6 (.some 1) =
      DynStepClass.run6 (.write 1 1) wBorrowState6 [.uninit] wPlace6 1 ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalAddrEqCall wBorrowState8 [] wLayouts8
        [p1, p2] [.uninit] wPlace8 (.some 1) =
      DynStepClass.run8 (.write 1 1) wBorrowState8 [.uninit] wPlace8 1 :=
  ⟨rfl, rfl⟩

/-- Non-vacuity of `unpackDynReceiver?_hom` across all 3 receiver kinds (`.ref`, `.raw`,
nested `.pinRef`) plus `.pinRef` non-aggregate `.unsupported` and `.raw` scalar `.ub` in BOTH
dialects. -/
theorem unpackDynReceiver?_witness :
    let d : Trusted.Rustc.V2026_08_01.MirSemantics.Value := .ptr { allocId := 1, offsetBytes := 0 } 8
    let m : Trusted.Rustc.V2026_08_01.MirSemantics.Value := .ptr { allocId := 16384, offsetBytes := 0 } 8
    let fat : Trusted.Rustc.V2026_08_01.MirSemantics.Value := .aggregate 0 [d, m]
    let pinned : Trusted.Rustc.V2026_08_01.MirSemantics.Value := .aggregate 0 [fat]
    Trusted.Rustc.V2026_06_01.MirSemantics.unpackDynReceiver? (homDRK (.ref .not)) (homValue fat) =
      .ok (homValue d, homValue m) ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.unpackDynReceiver? (.ref .not) fat = .ok (d, m) ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.unpackDynReceiver? (homDRK (.raw .mut)) (homValue fat) =
      .ok (homValue d, homValue m) ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.unpackDynReceiver? (.raw .mut) fat = .ok (d, m) ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.unpackDynReceiver? (homDRK (.pinRef .mut)) (homValue pinned) =
      .ok (homValue d, homValue m) ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.unpackDynReceiver? (.pinRef .mut) pinned = .ok (d, m) ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.unpackDynReceiver? (homDRK (.pinRef .mut)) (homValue fat) =
      .unsupported ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.unpackDynReceiver? (.pinRef .mut) fat = .unsupported ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.unpackDynReceiver? (homDRK (.raw .not)) (homValue d) = .ub ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.unpackDynReceiver? (.raw .not) d = .ub :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Witness multi-supertrait + auto-trait environment (`Sub : Sup + Side + Send`, plus `SupSync :
Send + Sync`) for `evalDynToDynUnsize_raw_hom`. -/
def wUpVTables8 : List Trusted.Rustc.V2026_08_01.MirAst.CapturedVTable :=
  [ { vtableId := 10, vtableAllocId := 16390, concreteTy := .uint .u32, dynKey := "Sub",
      sizeBytes := 4, alignBytes := 4, primarySuperVTableId? := .some 11,
      slots := [.dropInPlace .none, .size, .align, .traitVPtr 12] },
    { vtableId := 11, vtableAllocId := 16391, concreteTy := .uint .u32, dynKey := "Sup",
      sizeBytes := 4, alignBytes := 4, slots := [.dropInPlace .none, .size, .align] },
    { vtableId := 12, vtableAllocId := 16392, concreteTy := .uint .u32, dynKey := "Side",
      sizeBytes := 4, alignBytes := 4, slots := [.dropInPlace .none, .size, .align] } ]

def wUpDynTypes8 : List Trusted.Rustc.V2026_08_01.MirAst.CapturedDynType :=
  [ { dynKey := "Sub", predicateKey := "Sub", principalTrait? := .some "Sub",
      typeArgs := [], assocBindings := [], autoTraits := ["Send"],
      hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true },
    { dynKey := "Sup", predicateKey := "Sup", principalTrait? := .some "Sup",
      typeArgs := [], assocBindings := [], autoTraits := ["Send"],
      hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true },
    { dynKey := "Side", predicateKey := "Side", principalTrait? := .some "Side",
      typeArgs := [], assocBindings := [], autoTraits := [],
      hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true },
    { dynKey := "SupSync", predicateKey := "SupSync", principalTrait? := .some "Sup",
      typeArgs := [], assocBindings := [], autoTraits := ["Send", "Sync"],
      hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } ]

def wUpBody8 : Trusted.Rustc.V2026_08_01.MirAst.CapturedMir :=
  { wBody8 with vtables := wUpVTables8, dynTypes := wUpDynTypes8 }

def wUpBody6 : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir :=
  { wBody6 with vtables := wUpVTables8.map homVTable, dynTypes := wUpDynTypes8.map homDynType }

def wUpState8 : Trusted.Rustc.V2026_08_01.MirSemantics.MachineState :=
  Trusted.Rustc.V2026_08_01.MirSemantics.initMachineStateWithCallees wUpBody8 [] [wUpBody8]

def wUpState6 : Trusted.Rustc.V2026_06_01.MirSemantics.MachineState :=
  Trusted.Rustc.V2026_06_01.MirSemantics.initMachineStateWithCallees wUpBody6 [] [wUpBody6]

/-- Realizability of `DynMemRel` on the multi-supertrait + auto-trait environment. -/
theorem wUpState_dynMemRel : DynMemRel wUpState6.memory wUpState8.memory :=
  ⟨⟨rfl, rfl⟩, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Non-vacuity of `evalDynToDynUnsize_raw_hom` across all 5 outcome branches in BOTH dialects:
equal-key NOP (`16390 -> 16390`), primary supertrait upcast (`Sub -> Sup`: `16390 -> 16391`),
secondary `TraitVPtr` upcast (`Sub -> Side`: `16390 -> 16392`), auto-trait violation
(`Sub [Send] -> SupSync [Send, Sync]`: `.unsupported`), and wrong-trait vtable on NOP
(`16391` with expected `"Sub"`: `.ub`). -/
theorem evalDynToDynUnsize_raw_witness :
    let mv6 := Trusted.Rustc.V2026_06_01.MirSemantics.DynMemView.ofMemory wUpState6.memory
    let mv8 := Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView.ofMemory wUpState8.memory
    let subPtr : Trusted.Rustc.V2026_08_01.MirSemantics.Value :=
      .aggregate 0 [.ptr { allocId := 5, offsetBytes := 1 } 8, .ptr { allocId := 16390, offsetBytes := 0 } 8]
    let supPtr : Trusted.Rustc.V2026_08_01.MirSemantics.Value :=
      .aggregate 0 [.ptr { allocId := 5, offsetBytes := 1 } 8, .ptr { allocId := 16391, offsetBytes := 0 } 8]
    let sidePtr : Trusted.Rustc.V2026_08_01.MirSemantics.Value :=
      .aggregate 0 [.ptr { allocId := 5, offsetBytes := 1 } 8, .ptr { allocId := 16392, offsetBytes := 0 } 8]
    Trusted.Rustc.V2026_06_01.MirSemantics.evalDynToDynUnsize [] mv6 [] wLayouts6 (homValue subPtr) "Sub" "Sub" false false =
      .ok (homValue subPtr) ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalDynToDynUnsize [] mv8 [] wLayouts8 subPtr "Sub" "Sub" false false =
      .ok subPtr ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalDynToDynUnsize [] mv6 [] wLayouts6 (homValue subPtr) "Sub" "Sup" false false =
      .ok (homValue supPtr) ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalDynToDynUnsize [] mv8 [] wLayouts8 subPtr "Sub" "Sup" false false =
      .ok supPtr ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalDynToDynUnsize [] mv6 [] wLayouts6 (homValue subPtr) "Sub" "Side" false false =
      .ok (homValue sidePtr) ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalDynToDynUnsize [] mv8 [] wLayouts8 subPtr "Sub" "Side" false false =
      .ok sidePtr ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalDynToDynUnsize [] mv6 [] wLayouts6 (homValue subPtr) "Sub" "SupSync" false false =
      .unsupported ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalDynToDynUnsize [] mv8 [] wLayouts8 subPtr "Sub" "SupSync" false false =
      .unsupported ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalDynToDynUnsize [] mv6 [] wLayouts6 (homValue supPtr) "Sub" "Sub" false false =
      .ub ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalDynToDynUnsize [] mv8 [] wLayouts8 supPtr "Sub" "Sub" false false =
      .ub :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Witness 32-bit ZST + uninhabited (`kani#5216`) environment for safe-ref scalar unsizing &
NOP/upcast in BOTH dialects. -/
def wZstUninhabBody8 : Trusted.Rustc.V2026_08_01.MirAst.CapturedMir :=
  { wBody8 with vtables := [wVTableUninhab8, wVTableZst8] }

def wZstUninhabBody6 : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir :=
  { wBody6 with vtables := [homVTable wVTableUninhab8, homVTable wVTableZst8] }

def wZstUninhabState8 : Trusted.Rustc.V2026_08_01.MirSemantics.MachineState :=
  Trusted.Rustc.V2026_08_01.MirSemantics.initMachineStateWithCallees wZstUninhabBody8 [] [wZstUninhabBody8]

def wZstUninhabState6 : Trusted.Rustc.V2026_06_01.MirSemantics.MachineState :=
  Trusted.Rustc.V2026_06_01.MirSemantics.initMachineStateWithCallees wZstUninhabBody6 [] [wZstUninhabBody6]

/-- Non-vacuity of `evalThinToDynUnsize_scalarRef_hom` & `evalDynToDynUnsize_scalarRef_hom`:
at 32-bit pointer width (`pointerBits = 32`), in BOTH dialects:
1. Valid aligned non-null ZST `&() -> &dyn Tr` returns `.ok` (both thin-to-dyn and dyn-to-dyn NOP);
2. 32-bit wrapped null `2^32` on `&() -> &dyn Tr` faults `.ub`;
3. `kani#5216` uninhabited `&! -> &dyn Tr` faults `.ub` (both thin-to-dyn and dyn-to-dyn NOP). -/
theorem evalScalarRefUnsize_witness_32bit_uninhabited :
    let mv6 := Trusted.Rustc.V2026_06_01.MirSemantics.DynMemView.ofMemory wZstUninhabState6.memory
    let mv8 := Trusted.Rustc.V2026_08_01.MirSemantics.DynMemView.ofMemory wZstUninhabState8.memory
    let zstOk8 : Trusted.Rustc.V2026_08_01.MirSemantics.Value :=
      .aggregate 0 [.scalar ⟨4, 4⟩, .ptr { allocId := 16386, offsetBytes := 0 } 4]
    let zstNull8 : Trusted.Rustc.V2026_08_01.MirSemantics.Value :=
      .aggregate 0 [.scalar ⟨4294967296, 4⟩, .ptr { allocId := 16386, offsetBytes := 0 } 4]
    let unin8 : Trusted.Rustc.V2026_08_01.MirSemantics.Value :=
      .aggregate 0 [.scalar ⟨4, 4⟩, .ptr { allocId := 16385, offsetBytes := 0 } 4]
    Trusted.Rustc.V2026_06_01.MirSemantics.evalThinToDynUnsize [] mv6 [] wLayouts32_6
        (.scalar (homScalar ⟨4, 4⟩)) (homTy (.tuple [])) "Tr" true false = .ok (homValue zstOk8) ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalThinToDynUnsize [] mv8 [] wLayouts32_8
        (.scalar ⟨4, 4⟩) (.tuple []) "Tr" true false = .ok zstOk8 ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalThinToDynUnsize [] mv6 [] wLayouts32_6
        (.scalar (homScalar ⟨4294967296, 4⟩)) (homTy (.tuple [])) "Tr" true false = .ub ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalThinToDynUnsize [] mv8 [] wLayouts32_8
        (.scalar ⟨4294967296, 4⟩) (.tuple []) "Tr" true false = .ub ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalThinToDynUnsize [] mv6 [] wLayouts32_6
        (.scalar (homScalar ⟨4, 4⟩)) (homTy .never) "Tr" true false = .ub ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalThinToDynUnsize [] mv8 [] wLayouts32_8
        (.scalar ⟨4, 4⟩) .never "Tr" true false = .ub ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalDynToDynUnsize [] mv6 [] wLayouts32_6
        (homValue zstOk8) "Tr" "Tr" true false = .ok (homValue zstOk8) ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalDynToDynUnsize [] mv8 [] wLayouts32_8
        zstOk8 "Tr" "Tr" true false = .ok zstOk8 ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalDynToDynUnsize [] mv6 [] wLayouts32_6
        (homValue zstNull8) "Tr" "Tr" true false = .ub ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalDynToDynUnsize [] mv8 [] wLayouts32_8
        zstNull8 "Tr" "Tr" true false = .ub ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalDynToDynUnsize [] mv6 [] wLayouts32_6
        (homValue unin8) "Tr" "Tr" true false = .ub ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalDynToDynUnsize [] mv8 [] wLayouts32_8
        unin8 "Tr" "Tr" true false = .ub :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.Mir.DynTraitVTableTests.Hom

/-! ## §4. Campaign #22 Miri-Differential Agreement (Condition `C8`) -/

namespace Anneal.Mir.DynTraitVTableTests.Campaign22

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-! ### Shared harness and table-forging combinators (negative controls). -/

/-- Link-time run of a Campaign #22 outer function: `evalMirDiffTagBounded 512` from the
empty-memory initial state with the given linked callee table. -/
def runC22 (outer : CapturedMir) (linked : List CapturedMir) : MirDiffTag :=
  evalMirDiffTagBounded 512 outer (initMachineStateWithMemoryAndCallees outer [] emptyMemory linked)

/-- `runC22` together with the active fault/unwind source span (`probeMirDiffExecBounded`). -/
def probeC22 (outer : CapturedMir) (linked : List CapturedMir) : MirDiffTag × String :=
  probeMirDiffExecBounded 512 outer
    (.running (initMachineStateWithMemoryAndCallees outer [] emptyMemory linked))

/-- Replace the captured vtable table of `b` by `f b.vtables` (every other field unchanged). -/
def mapVTables (f : List CapturedVTable → List CapturedVTable) (b : CapturedMir) : CapturedMir :=
  { b with vtables := f b.vtables }

/-- Strip the captured vtable table (`vtables := []`). -/
def stripVTables : CapturedMir → CapturedMir := mapVTables (fun _ => [])

/-- Apply `g` to the vtable record with `vtableId = id`. -/
def forgeVTableId (id : Nat) (g : CapturedVTable → CapturedVTable) :
    List CapturedVTable → List CapturedVTable :=
  List.map (fun v => if v.vtableId = id then g v else v)

/-- Forgery 1: overwrite vtable `1`'s first method slot (index `3`) with the non-method
header slot `.size` (the table stays well formed: header shape, layout, ids unchanged). -/
def forgeNonMethodSlot : List CapturedVTable → List CapturedVTable :=
  forgeVTableId 1 (fun v => { v with slots := v.slots.set 3 .size })

/-- Forgery 2: truncate vtable `1` to its header plus first method (slot index `4` becomes
out of bounds). -/
def forgeTruncatedSlots : List CapturedVTable → List CapturedVTable :=
  forgeVTableId 1 (fun v => { v with slots := v.slots.take 4 })

/-- Forgery 3: give vtable `2` the `dynKey` of vtable `0` (wrong trait: the
`(Receiver, dyn Trait)` vtable disappears and `(Receiver, dyn Alt)` is duplicated). -/
def forgeWrongDynKey : List CapturedVTable → List CapturedVTable
  | v0 :: v1 :: v2 :: rest => v0 :: v1 :: { v2 with dynKey := v0.dynKey } :: rest
  | vts => vts

/-! ### Campaign #22 `finding_0000`: `miri_diff_corpus::pass_option_some_niche_and_single_c_mut__b0_c10` (Miri: `MIRI_PASS:scalar:20:4`).

Verbatim `layouts`/`body` definitions emitted by HEAD `anneal-rustc-capture` (`Runtime(PostCleanup)` MIR,
nightly-2026-06-01, `-Zmir-opt-level=0 -C debug-assertions=off -C overflow-checks=on`). -/

namespace F0000.Outer

/-! Captured `miri_diff_corpus` item `pass_option_some_niche_and_single_c_mut__b0_c10`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 1, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 1, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 1, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.multiple (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) 0 (List.cons (FieldsShape.arbitrary List.nil List.nil) (List.cons (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)) List.nil))), isUninhabited := false, fieldLayouts := (List.cons 3 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 2 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.multiple (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 2 }) 0 (List.cons (FieldsShape.arbitrary List.nil List.nil) (List.cons (FieldsShape.arbitrary List.nil List.nil) (List.cons (FieldsShape.arbitrary List.nil List.nil) List.nil)))), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 255, end_ := 2 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.multiple (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 255, end_ := 2 }) 0 (List.cons (FieldsShape.arbitrary List.nil List.nil) (List.cons (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)) List.nil))), isUninhabited := false, fieldLayouts := (List.cons 5 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 255 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 true) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 0 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.multiple (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 0 }) 0 (List.cons (FieldsShape.arbitrary (List.cons { bytes := 4 } List.nil) (List.cons 0 List.nil)) List.nil)), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 9 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } List.nil))))))))))))) }

-- bb0: StorageLive(_1); _1 = const 7_u32 as core::num::NonZero<u32> (Transmute); StorageLive(_2); StorageLive(_3); StorageLive(_4); _4 = copy _1; _3 = core::option::Option::<core::num::NonZero<u32>>::Some(move _4); StorageDead(_4); _2 = move _3 as u32 (Transmute); StorageDead(_3); StorageLive(_5); StorageLive(_6); _6 = core::option::Option::<core::num::NonZero<u32>>::None; _5 = move _6 as u32 (Transmute); StorageDead(_6); StorageLive(_7); StorageLive(_8); _8 = ColorTag::Green; _7 = core::option::Option::<ColorTag>::Some(move _8); StorageDead(_8); StorageLive(_9); _11 = discriminant(_7); switchInt(move _11) -> [0: bb3, 1: bb2, otherwise: bb1]
-- bb1: unreachable
-- bb2: _10 = discriminant(((_7 as Some).0: ColorTag)); switchInt(move _10) -> [0: bb6, 1: bb5, 2: bb4, otherwise: bb1]
-- bb3: _9 = const 4_u32; goto -> bb7
-- bb4: _9 = const 3_u32; goto -> bb7
-- bb5: _9 = const 2_u32; goto -> bb7
-- bb6: _9 = const 1_u32; goto -> bb7
-- bb7: StorageLive(_12); StorageLive(_13); StorageLive(_14); StorageLive(_15); _15 = copy _2; StorageLive(_16); _16 = copy _5; _14 = BitXor(move _15, move _16); StorageDead(_16); StorageDead(_15); StorageLive(_17); _17 = copy _9; _13 = BitXor(move _14, move _17); StorageDead(_17); StorageDead(_14); _12 = SingleC::Only(move _13); StorageDead(_13); StorageLive(_18); StorageLive(_19); _19 = &mut _12; StorageLive(_20); _20 = &mut (((*_19) as Only).0: u32); (*_20) = BitXor(copy (*_20), const 12_u32); _18 = const (); StorageDead(_20); StorageDead(_19); StorageDead(_18); StorageLive(_21); StorageLive(_22); StorageLive(_23); _23 = copy ((_12 as Only).0: u32); StorageLive(_24); _24 = copy _23; _22 = BitXor(move _24, const 3_u32); StorageDead(_24); StorageDead(_23); _21 = SingleC::Only(move _22); StorageDead(_22); _12 = move _21; StorageDead(_21); StorageLive(_25); StorageLive(_26); _26 = copy ((_12 as Only).0: u32); _25 = copy _26; StorageDead(_26); StorageLive(_27); StorageLive(_28); StorageLive(_29); _29 = copy _2; _28 = BitAnd(move _29, const 65535_u32); StorageDead(_29); _27 = __anneal_vt_driver_43543(move _28, const 24_u32) -> [return: bb8, unwind continue]
-- bb8: StorageDead(_28); StorageLive(_30); _30 = copy _25; StorageLive(_31); _31 = copy _27; _0 = BitXor(move _30, move _31); StorageDead(_31); StorageDead(_30); StorageDead(_27); StorageDead(_25); StorageDead(_12); StorageDead(_9); StorageDead(_7); StorageDead(_5); StorageDead(_2); StorageDead(_1); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::pass_option_some_niche_and_single_c_mut__b0_c10",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", predicateKey := "miri_diff_corpus::__AnnealVtableAlt43543", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt43543"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", predicateKey := "miri_diff_corpus::__AnnealVtableTrait43543", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait43543"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableAlt43543>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver43543 as __AnnealVtableTrait43543>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver43543 as __AnnealVtableTrait43543>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableTrait43543>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableTrait43543>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt43543::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait43543::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait43543::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", slotIdx := 4 } List.nil))),
    argCount := 0,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "core::num::NonZero" (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 3 }, debugName := (Option.some "nz") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "some_bits") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "core::option::Option" (List.cons (RigidTy.adt "core::num::NonZero" (List.cons (RigidTy.uint UintTy.u32) List.nil)) List.nil)), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "core::num::NonZero" (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "none_bits") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "core::option::Option" (List.cons (RigidTy.adt "core::num::NonZero" (List.cons (RigidTy.uint UintTy.u32) List.nil)) List.nil)), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "core::option::Option" (List.cons (RigidTy.adt "miri_diff_corpus::ColorTag" List.nil) List.nil)), layoutIdx := 6 }, debugName := (Option.some "oc") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "miri_diff_corpus::ColorTag" List.nil), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "color_val") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.int IntTy.isize), layoutIdx := 8 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "miri_diff_corpus::SingleC" List.nil), layoutIdx := 9 }, debugName := (Option.some "s") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 10 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.adt "miri_diff_corpus::SingleC" List.nil)), layoutIdx := 11 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.uint UintTy.u32)), layoutIdx := 12 }, debugName := (Option.some "p") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "miri_diff_corpus::SingleC" List.nil), layoutIdx := 9 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "v") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__tail___miri_vt_43543") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "v") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__miri_vt_43543") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))))))))))))))))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 10), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 11), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 1), span := "src/lib.rs:346:9: 346:11" } (List.cons { kind := (StatementKind.assign { local_ := 1, projection := List.nil } (Rvalue.cast CastKind.transmute (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 7, sizeBytes := 4 })) }) { kind := (RigidTy.adt "core::num::NonZero" (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 3 })), span := "src/lib.rs:346:35: 346:69" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:347:9: 347:18" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:347:72: 347:80" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:347:77: 347:79" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:347:77: 347:79" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "core::option::Option" 1 Option.none) (List.cons (Operand.move { local_ := 4, projection := List.nil }) List.nil))), span := "src/lib.rs:347:72: 347:80" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:347:79: 347:80" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast CastKind.transmute (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 })), span := "src/lib.rs:347:35: 347:81" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:347:80: 347:81" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:348:9: 348:18" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:348:72: 348:76" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "core::option::Option" 0 Option.none) List.nil)), span := "src/lib.rs:348:72: 348:76" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.cast CastKind.transmute (Operand.move { local_ := 6, projection := List.nil }) { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 })), span := "src/lib.rs:348:35: 348:77" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:348:76: 348:77" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:349:9: 349:11" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:349:37: 349:52" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::ColorTag" 1 Option.none) List.nil)), span := "src/lib.rs:349:37: 349:52" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "core::option::Option" 1 Option.none) (List.cons (Operand.move { local_ := 8, projection := List.nil }) List.nil))), span := "src/lib.rs:349:32: 349:53" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:349:52: 349:53" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:350:9: 350:18" } (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.discriminant { local_ := 7, projection := List.nil })), span := "src/lib.rs:350:32: 350:34" } List.nil)))))))))))))))))))))))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 11, projection := List.nil }) { branches := (List.cons (0, 3) (List.cons (1, 2) List.nil)), otherwise := 1 }), span := "src/lib.rs:350:26: 350:34" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := TerminatorKind.unreachable, span := "src/lib.rs:350:32: 350:34" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.discriminant { local_ := 7, projection := (List.cons (ProjectionElem.downcast (Option.some "Some") 1) (List.cons (ProjectionElem.field 0 { kind := (RigidTy.adt "miri_diff_corpus::ColorTag" List.nil), layoutIdx := 5 }) List.nil)) })), span := "src/lib.rs:350:32: 350:34" } List.nil), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 10, projection := List.nil }) { branches := (List.cons (0, 6) (List.cons (1, 5) (List.cons (2, 4) List.nil))), otherwise := 1 }), span := "src/lib.rs:350:26: 350:34" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 4, sizeBytes := 4 })) }))), span := "src/lib.rs:354:17: 354:21" } List.nil), terminator := { kind := (TerminatorKind.goto 7), span := "src/lib.rs:354:17: 354:21" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 3, sizeBytes := 4 })) }))), span := "src/lib.rs:353:33: 353:37" } List.nil), terminator := { kind := (TerminatorKind.goto 7), span := "src/lib.rs:353:33: 353:37" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }))), span := "src/lib.rs:352:34: 352:38" } List.nil), terminator := { kind := (TerminatorKind.goto 7), span := "src/lib.rs:352:34: 352:38" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:351:32: 351:36" } List.nil), terminator := { kind := (TerminatorKind.goto 7), span := "src/lib.rs:351:32: 351:36" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:356:9: 356:14" } (List.cons { kind := (StatementKind.storageLive 13), span := "src/lib.rs:356:31: 356:64" } (List.cons { kind := (StatementKind.storageLive 14), span := "src/lib.rs:356:31: 356:52" } (List.cons { kind := (StatementKind.storageLive 15), span := "src/lib.rs:356:31: 356:40" } (List.cons { kind := (StatementKind.assign { local_ := 15, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:356:31: 356:40" } (List.cons { kind := (StatementKind.storageLive 16), span := "src/lib.rs:356:43: 356:52" } (List.cons { kind := (StatementKind.assign { local_ := 16, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 5, projection := List.nil }))), span := "src/lib.rs:356:43: 356:52" } (List.cons { kind := (StatementKind.assign { local_ := 14, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 15, projection := List.nil }) (Operand.move { local_ := 16, projection := List.nil }))), span := "src/lib.rs:356:31: 356:52" } (List.cons { kind := (StatementKind.storageDead 16), span := "src/lib.rs:356:51: 356:52" } (List.cons { kind := (StatementKind.storageDead 15), span := "src/lib.rs:356:51: 356:52" } (List.cons { kind := (StatementKind.storageLive 17), span := "src/lib.rs:356:55: 356:64" } (List.cons { kind := (StatementKind.assign { local_ := 17, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 9, projection := List.nil }))), span := "src/lib.rs:356:55: 356:64" } (List.cons { kind := (StatementKind.assign { local_ := 13, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 14, projection := List.nil }) (Operand.move { local_ := 17, projection := List.nil }))), span := "src/lib.rs:356:31: 356:64" } (List.cons { kind := (StatementKind.storageDead 17), span := "src/lib.rs:356:63: 356:64" } (List.cons { kind := (StatementKind.storageDead 14), span := "src/lib.rs:356:63: 356:64" } (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::SingleC" 0 Option.none) (List.cons (Operand.move { local_ := 13, projection := List.nil }) List.nil))), span := "src/lib.rs:356:17: 356:65" } (List.cons { kind := (StatementKind.storageDead 13), span := "src/lib.rs:356:64: 356:65" } (List.cons { kind := (StatementKind.storageLive 18), span := "src/lib.rs:357:5: 361:6" } (List.cons { kind := (StatementKind.storageLive 19), span := "src/lib.rs:357:11: 357:17" } (List.cons { kind := (StatementKind.assign { local_ := 19, projection := List.nil } (Rvalue.ref (BorrowKind.mut false) { local_ := 12, projection := List.nil })), span := "src/lib.rs:357:11: 357:17" } (List.cons { kind := (StatementKind.storageLive 20), span := "src/lib.rs:358:23: 358:24" } (List.cons { kind := (StatementKind.assign { local_ := 20, projection := List.nil } (Rvalue.ref (BorrowKind.mut false) { local_ := 19, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.downcast (Option.some "Only") 0) (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil))) })), span := "src/lib.rs:358:23: 358:24" } (List.cons { kind := (StatementKind.assign { local_ := 20, projection := (List.cons ProjectionElem.deref List.nil) } (Rvalue.binaryOp BinOp.bitXor (Operand.copy { local_ := 20, projection := (List.cons ProjectionElem.deref List.nil) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 12, sizeBytes := 4 })) }))), span := "src/lib.rs:359:13: 359:24" } (List.cons { kind := (StatementKind.assign { local_ := 18, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 10 }, val := ConstValue.zeroSized }))), span := "src/lib.rs:358:29: 360:10" } (List.cons { kind := (StatementKind.storageDead 20), span := "src/lib.rs:360:9: 360:10" } (List.cons { kind := (StatementKind.storageDead 19), span := "src/lib.rs:361:5: 361:6" } (List.cons { kind := (StatementKind.storageDead 18), span := "src/lib.rs:361:5: 361:6" } (List.cons { kind := (StatementKind.storageLive 21), span := "src/lib.rs:362:9: 366:6" } (List.cons { kind := (StatementKind.storageLive 22), span := "src/lib.rs:363:9: 365:10" } (List.cons { kind := (StatementKind.storageLive 23), span := "src/lib.rs:364:27: 364:28" } (List.cons { kind := (StatementKind.assign { local_ := 23, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 12, projection := (List.cons (ProjectionElem.downcast (Option.some "Only") 0) (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:364:27: 364:28" } (List.cons { kind := (StatementKind.storageLive 24), span := "src/lib.rs:364:33: 364:34" } (List.cons { kind := (StatementKind.assign { local_ := 24, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 23, projection := List.nil }))), span := "src/lib.rs:364:33: 364:34" } (List.cons { kind := (StatementKind.assign { local_ := 22, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 24, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 3, sizeBytes := 4 })) }))), span := "src/lib.rs:364:33: 364:41" } (List.cons { kind := (StatementKind.storageDead 24), span := "src/lib.rs:364:40: 364:41" } (List.cons { kind := (StatementKind.storageDead 23), span := "src/lib.rs:364:40: 364:41" } (List.cons { kind := (StatementKind.assign { local_ := 21, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::SingleC" 0 Option.none) (List.cons (Operand.move { local_ := 22, projection := List.nil }) List.nil))), span := "src/lib.rs:362:9: 366:6" } (List.cons { kind := (StatementKind.storageDead 22), span := "src/lib.rs:366:5: 366:6" } (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.use (Operand.move { local_ := 21, projection := List.nil }))), span := "src/lib.rs:362:5: 366:6" } (List.cons { kind := (StatementKind.storageDead 21), span := "src/lib.rs:366:5: 366:6" } (List.cons { kind := (StatementKind.storageLive 25), span := "src/lib.rs:367:9: 367:31" } (List.cons { kind := (StatementKind.storageLive 26), span := "src/lib.rs:368:23: 368:24" } (List.cons { kind := (StatementKind.assign { local_ := 26, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 12, projection := (List.cons (ProjectionElem.downcast (Option.some "Only") 0) (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:368:23: 368:24" } (List.cons { kind := (StatementKind.assign { local_ := 25, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 26, projection := List.nil }))), span := "src/lib.rs:368:29: 368:30" } (List.cons { kind := (StatementKind.storageDead 26), span := "src/lib.rs:368:29: 368:30" } (List.cons { kind := (StatementKind.storageLive 27), span := "src/lib.rs:370:9: 370:24" } (List.cons { kind := (StatementKind.storageLive 28), span := "src/lib.rs:371:9: 371:39" } (List.cons { kind := (StatementKind.storageLive 29), span := "src/lib.rs:371:9: 371:27" } (List.cons { kind := (StatementKind.assign { local_ := 29, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:371:10: 371:19" } (List.cons { kind := (StatementKind.assign { local_ := 28, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 29, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 65535, sizeBytes := 4 })) }))), span := "src/lib.rs:371:9: 371:39" } (List.cons { kind := (StatementKind.storageDead 29), span := "src/lib.rs:371:38: 371:39" } List.nil))))))))))))))))))))))))))))))))))))))))))))))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__anneal_vt_driver_43543" List.nil), layoutIdx := 10 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 28, projection := List.nil }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 24, sizeBytes := 4 })) }) List.nil)) { local_ := 27, projection := List.nil } (Option.some 8) UnwindAction.continue_), span := "src/lib.rs:370:32: 373:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 28), span := "src/lib.rs:373:5: 373:6" } (List.cons { kind := (StatementKind.storageLive 30), span := "src/lib.rs:374:5: 374:27" } (List.cons { kind := (StatementKind.assign { local_ := 30, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 25, projection := List.nil }))), span := "src/lib.rs:374:5: 374:27" } (List.cons { kind := (StatementKind.storageLive 31), span := "src/lib.rs:374:30: 374:54" } (List.cons { kind := (StatementKind.assign { local_ := 31, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 27, projection := List.nil }))), span := "src/lib.rs:374:31: 374:46" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 30, projection := List.nil }) (Operand.move { local_ := 31, projection := List.nil }))), span := "src/lib.rs:374:5: 374:54" } (List.cons { kind := (StatementKind.storageDead 31), span := "src/lib.rs:374:53: 374:54" } (List.cons { kind := (StatementKind.storageDead 30), span := "src/lib.rs:374:53: 374:54" } (List.cons { kind := (StatementKind.storageDead 27), span := "src/lib.rs:375:1: 375:2" } (List.cons { kind := (StatementKind.storageDead 25), span := "src/lib.rs:375:1: 375:2" } (List.cons { kind := (StatementKind.storageDead 12), span := "src/lib.rs:375:1: 375:2" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:375:1: 375:2" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:375:1: 375:2" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:375:1: 375:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:375:1: 375:2" } (List.cons { kind := (StatementKind.storageDead 1), span := "src/lib.rs:375:1: 375:2" } List.nil)))))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:375:2: 375:2" }, isCleanup := false } List.nil))))))))),
    fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0000.Outer

namespace F0000.Driver

/-! Captured `miri_diff_corpus` item `__anneal_vt_driver_43543`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 0 List.nil)) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))))))) }

-- bb0: StorageLive(_3); StorageLive(_4); StorageLive(_5); _5 = copy _2; _4 = BitXor(move _5, const 3_u32); StorageDead(_5); _3 = __AnnealVtableReceiver43543 { bias: move _4 }; StorageDead(_4); StorageLive(_6); StorageLive(_7); StorageLive(_8); StorageLive(_9); _9 = copy _1; _8 = BitAnd(move _9, const 255_u32); StorageDead(_9); _7 = BitXor(move _8, const 3_u32); StorageDead(_8); StorageLive(_10); StorageLive(_11); StorageLive(_12); _12 = copy _2; _13 = Lt(const 1_u32, const 32_u32); assert(move _13, "attempt to shift right by `{}`, which would overflow", const 1_u32) -> [success: bb1, unwind continue]
-- bb1: _11 = Shr(move _12, const 1_u32); StorageDead(_12); _10 = BitXor(move _11, const 3_u32); StorageDead(_11); _6 = __AnnealVtableAltReceiver43543 { pad: move _7, bias: move _10 }; StorageDead(_10); StorageDead(_7); StorageLive(_14); StorageLive(_15); StorageLive(_16); StorageLive(_17); StorageLive(_18); _18 = &_3; _17 = &(*_18); _16 = move _17 as &dyn __AnnealVtableTrait43543 (PointerCoercion(Unsize, AsCast)); StorageDead(_17); _15 = &(*_16); _14 = move _15 as &dyn __AnnealVtableTrait43543 (PointerCoercion(Unsize, Implicit)); StorageDead(_15); StorageDead(_18); StorageDead(_16); StorageLive(_19); StorageLive(_20); StorageLive(_21); StorageLive(_22); StorageLive(_23); _23 = &_6; _22 = &(*_23); _21 = move _22 as &dyn __AnnealVtableTrait43543 (PointerCoercion(Unsize, AsCast)); StorageDead(_22); _20 = &(*_21); _19 = move _20 as &dyn __AnnealVtableTrait43543 (PointerCoercion(Unsize, Implicit)); StorageDead(_20); StorageDead(_23); StorageDead(_21); StorageLive(_24); StorageLive(_25); StorageLive(_26); StorageLive(_27); StorageLive(_28); StorageLive(_29); _29 = copy _1; _28 = BitAnd(move _29, const 1_u32); StorageDead(_29); _27 = Eq(move _28, const 0_u32); switchInt(move _27) -> [0: bb3, otherwise: bb2]
-- bb2: StorageDead(_28); StorageLive(_30); StorageLive(_31); StorageLive(_32); _32 = &(*_14); _31 = move _32 as &dyn __AnnealVtableTrait43543 (PointerCoercion(Unsize, Implicit)); StorageDead(_32); _30 = &(*_31); _26 = move _30 as &dyn __AnnealVtableTrait43543 (PointerCoercion(Unsize, Implicit)); StorageDead(_31); StorageDead(_30); goto -> bb4
-- bb3: StorageDead(_28); StorageLive(_33); _33 = &(*_19); _26 = move _33 as &dyn __AnnealVtableTrait43543 (PointerCoercion(Unsize, Implicit)); StorageDead(_33); goto -> bb4
-- bb4: _25 = &(*_26); _24 = move _25 as &dyn __AnnealVtableTrait43543 (PointerCoercion(Unsize, Implicit)); StorageDead(_27); StorageDead(_25); StorageDead(_26); StorageLive(_34); StorageLive(_35); StorageLive(_36); StorageLive(_37); StorageLive(_38); _38 = &_3; _37 = &(*_38); _36 = move _37 as &dyn __AnnealVtableAlt43543 (PointerCoercion(Unsize, AsCast)); StorageDead(_37); _35 = &(*_36); _34 = move _35 as &dyn __AnnealVtableAlt43543 (PointerCoercion(Unsize, Implicit)); StorageDead(_35); StorageDead(_38); StorageDead(_36); StorageLive(_39); StorageLive(_40); StorageLive(_41); _41 = &(*_24); StorageLive(_42); _42 = copy _1; _40 = <dyn __AnnealVtableTrait43543 as __AnnealVtableTrait43543>::eval_vt(move _41, move _42) -> [return: bb5, unwind continue]
-- bb5: StorageDead(_42); StorageDead(_41); StorageLive(_43); StorageLive(_44); _44 = &(*_24); _43 = <dyn __AnnealVtableTrait43543 as __AnnealVtableTrait43543>::tag_vt(move _44) -> [return: bb6, unwind continue]
-- bb6: StorageDead(_44); _39 = BitXor(move _40, move _43); StorageDead(_43); StorageDead(_40); StorageLive(_45); StorageLive(_46); _46 = &(*_34); _45 = <dyn __AnnealVtableAlt43543 as __AnnealVtableAlt43543>::eval_alt(move _46) -> [return: bb7, unwind continue]
-- bb7: StorageDead(_46); StorageLive(_47); StorageLive(_48); StorageLive(_49); _49 = &raw const (*_14); StorageLive(_50); _50 = &raw const (*_34); _48 = core::ptr::addr_eq::<dyn __AnnealVtableTrait43543, dyn __AnnealVtableAlt43543>(move _49, move _50) -> [return: bb8, unwind continue]
-- bb8: switchInt(move _48) -> [0: bb10, otherwise: bb9]
-- bb9: StorageDead(_50); StorageDead(_49); _47 = const 1_u32; goto -> bb11
-- bb10: StorageDead(_50); StorageDead(_49); _47 = const 0_u32; goto -> bb11
-- bb11: StorageDead(_48); StorageLive(_51); StorageLive(_52); StorageLive(_53); _53 = &raw const (*_14); StorageLive(_54); _54 = &raw const (*_19); _52 = core::ptr::addr_eq::<dyn __AnnealVtableTrait43543, dyn __AnnealVtableTrait43543>(move _53, move _54) -> [return: bb12, unwind continue]
-- bb12: switchInt(move _52) -> [0: bb14, otherwise: bb13]
-- bb13: StorageDead(_54); StorageDead(_53); _51 = const 0_u32; goto -> bb15
-- bb14: StorageDead(_54); StorageDead(_53); _51 = const 2_u32; goto -> bb15
-- bb15: StorageDead(_52); StorageLive(_55); StorageLive(_56); StorageLive(_57); _57 = copy _39; StorageLive(_58); StorageLive(_59); _59 = copy _45; _60 = Lt(const 2_u32, const 32_u32); assert(move _60, "attempt to shift left by `{}`, which would overflow", const 2_u32) -> [success: bb16, unwind continue]
-- bb16: _58 = Shl(move _59, const 2_u32); StorageDead(_59); _56 = BitXor(move _57, move _58); StorageDead(_58); StorageDead(_57); StorageLive(_61); _61 = copy _47; _55 = BitXor(move _56, move _61); StorageDead(_61); StorageDead(_56); StorageLive(_62); _62 = copy _51; _0 = BitXor(move _55, move _62); StorageDead(_62); StorageDead(_55); StorageDead(_51); StorageDead(_47); StorageDead(_45); StorageDead(_39); StorageDead(_34); StorageDead(_24); StorageDead(_19); StorageDead(_14); StorageDead(_6); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::__anneal_vt_driver_43543",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", predicateKey := "miri_diff_corpus::__AnnealVtableAlt43543", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt43543"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", predicateKey := "miri_diff_corpus::__AnnealVtableTrait43543", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait43543"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableAlt43543>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver43543 as __AnnealVtableTrait43543>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver43543 as __AnnealVtableTrait43543>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableTrait43543>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableTrait43543>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt43543::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait43543::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait43543::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", slotIdx := 4 } List.nil))),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_seed") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_bias") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil), layoutIdx := 1 }, debugName := (Option.some "__vt_rec") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver43543" List.nil), layoutIdx := 2 }, debugName := (Option.some "__vt_other") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 }, debugName := (Option.some "__vt_rec_dyn") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 }, debugName := (Option.some "__vt_other_dyn") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver43543" List.nil)), layoutIdx := 6 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver43543" List.nil)), layoutIdx := 6 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 }, debugName := (Option.some "__vt_dyn") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt43543")), layoutIdx := 4 }, debugName := (Option.some "__vt_dyn_alt") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt43543")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt43543")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_virtual") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_alt_bits") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt43543")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_same_obj") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt43543")), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_diff_obj") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 13), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 60), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:310:9: 310:17" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:311:15: 311:31" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:311:15: 311:24" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:311:15: 311:24" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 5, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 3, sizeBytes := 4 })) }))), span := "src/lib.rs:311:15: 311:31" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:311:30: 311:31" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::__AnnealVtableReceiver43543" 0 Option.none) (List.cons (Operand.move { local_ := 4, projection := List.nil }) List.nil))), span := "src/lib.rs:310:49: 312:6" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:312:5: 312:6" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:313:9: 313:19" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:314:14: 314:42" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:314:14: 314:35" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:314:15: 314:24" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:314:15: 314:24" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 9, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 255, sizeBytes := 4 })) }))), span := "src/lib.rs:314:14: 314:35" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:314:34: 314:35" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 8, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 3, sizeBytes := 4 })) }))), span := "src/lib.rs:314:14: 314:42" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:314:41: 314:42" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:315:15: 315:41" } (List.cons { kind := (StatementKind.storageLive 11), span := "src/lib.rs:315:15: 315:34" } (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:315:16: 315:25" } (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:315:16: 315:25" } (List.cons { kind := (StatementKind.assign { local_ := 13, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:315:15: 315:34" } List.nil)))))))))))))))))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 13, projection := List.nil }) true 1 UnwindAction.continue_), span := "src/lib.rs:315:15: 315:34" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.binaryOp BinOp.shr (Operand.move { local_ := 12, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:315:15: 315:34" } (List.cons { kind := (StatementKind.storageDead 12), span := "src/lib.rs:315:33: 315:34" } (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 11, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 3, sizeBytes := 4 })) }))), span := "src/lib.rs:315:15: 315:41" } (List.cons { kind := (StatementKind.storageDead 11), span := "src/lib.rs:315:40: 315:41" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::__AnnealVtableAltReceiver43543" 0 Option.none) (List.cons (Operand.move { local_ := 7, projection := List.nil }) (List.cons (Operand.move { local_ := 10, projection := List.nil }) List.nil)))), span := "src/lib.rs:313:54: 316:6" } (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:316:5: 316:6" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:316:5: 316:6" } (List.cons { kind := (StatementKind.storageLive 14), span := "src/lib.rs:317:9: 317:21" } (List.cons { kind := (StatementKind.storageLive 15), span := "src/lib.rs:317:55: 318:41" } (List.cons { kind := (StatementKind.storageLive 16), span := "src/lib.rs:317:55: 318:41" } (List.cons { kind := (StatementKind.storageLive 17), span := "src/lib.rs:317:55: 317:64" } (List.cons { kind := (StatementKind.storageLive 18), span := "src/lib.rs:317:55: 317:64" } (List.cons { kind := (StatementKind.assign { local_ := 18, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 3, projection := List.nil })), span := "src/lib.rs:317:55: 317:64" } (List.cons { kind := (StatementKind.assign { local_ := 17, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 18, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:317:55: 317:64" } (List.cons { kind := (StatementKind.assign { local_ := 16, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 17, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 })), span := "src/lib.rs:317:55: 318:41" } (List.cons { kind := (StatementKind.storageDead 17), span := "src/lib.rs:317:63: 317:64" } (List.cons { kind := (StatementKind.assign { local_ := 15, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 16, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:317:55: 318:41" } (List.cons { kind := (StatementKind.assign { local_ := 14, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 15, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 })), span := "src/lib.rs:317:55: 318:41" } (List.cons { kind := (StatementKind.storageDead 15), span := "src/lib.rs:318:40: 318:41" } (List.cons { kind := (StatementKind.storageDead 18), span := "src/lib.rs:318:41: 318:42" } (List.cons { kind := (StatementKind.storageDead 16), span := "src/lib.rs:318:41: 318:42" } (List.cons { kind := (StatementKind.storageLive 19), span := "src/lib.rs:319:9: 319:23" } (List.cons { kind := (StatementKind.storageLive 20), span := "src/lib.rs:319:57: 320:41" } (List.cons { kind := (StatementKind.storageLive 21), span := "src/lib.rs:319:57: 320:41" } (List.cons { kind := (StatementKind.storageLive 22), span := "src/lib.rs:319:57: 319:68" } (List.cons { kind := (StatementKind.storageLive 23), span := "src/lib.rs:319:57: 319:68" } (List.cons { kind := (StatementKind.assign { local_ := 23, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 6, projection := List.nil })), span := "src/lib.rs:319:57: 319:68" } (List.cons { kind := (StatementKind.assign { local_ := 22, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 23, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:319:57: 319:68" } (List.cons { kind := (StatementKind.assign { local_ := 21, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 22, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 })), span := "src/lib.rs:319:57: 320:41" } (List.cons { kind := (StatementKind.storageDead 22), span := "src/lib.rs:319:67: 319:68" } (List.cons { kind := (StatementKind.assign { local_ := 20, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 21, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:319:57: 320:41" } (List.cons { kind := (StatementKind.assign { local_ := 19, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 20, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 })), span := "src/lib.rs:319:57: 320:41" } (List.cons { kind := (StatementKind.storageDead 20), span := "src/lib.rs:320:40: 320:41" } (List.cons { kind := (StatementKind.storageDead 23), span := "src/lib.rs:320:41: 320:42" } (List.cons { kind := (StatementKind.storageDead 21), span := "src/lib.rs:320:41: 320:42" } (List.cons { kind := (StatementKind.storageLive 24), span := "src/lib.rs:321:9: 321:17" } (List.cons { kind := (StatementKind.storageLive 25), span := "src/lib.rs:321:51: 325:6" } (List.cons { kind := (StatementKind.storageLive 26), span := "src/lib.rs:321:51: 325:6" } (List.cons { kind := (StatementKind.storageLive 27), span := "src/lib.rs:321:54: 321:80" } (List.cons { kind := (StatementKind.storageLive 28), span := "src/lib.rs:321:54: 321:72" } (List.cons { kind := (StatementKind.storageLive 29), span := "src/lib.rs:321:55: 321:64" } (List.cons { kind := (StatementKind.assign { local_ := 29, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:321:55: 321:64" } (List.cons { kind := (StatementKind.assign { local_ := 28, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 29, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:321:54: 321:72" } (List.cons { kind := (StatementKind.storageDead 29), span := "src/lib.rs:321:71: 321:72" } (List.cons { kind := (StatementKind.assign { local_ := 27, projection := List.nil } (Rvalue.binaryOp BinOp.eq (Operand.move { local_ := 28, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:321:54: 321:80" } List.nil))))))))))))))))))))))))))))))))))))))))))))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 27, projection := List.nil }) { branches := (List.cons (0, 3) List.nil), otherwise := 2 }), span := "src/lib.rs:321:54: 321:80" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 28), span := "src/lib.rs:321:79: 321:80" } (List.cons { kind := (StatementKind.storageLive 30), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.storageLive 31), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.storageLive 32), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.assign { local_ := 32, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 14, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.assign { local_ := 31, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 32, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 })), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.storageDead 32), span := "src/lib.rs:322:20: 322:21" } (List.cons { kind := (StatementKind.assign { local_ := 30, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 31, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.assign { local_ := 26, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 30, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 })), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.storageDead 31), span := "src/lib.rs:323:5: 323:6" } (List.cons { kind := (StatementKind.storageDead 30), span := "src/lib.rs:323:5: 323:6" } List.nil))))))))))), terminator := { kind := (TerminatorKind.goto 4), span := "src/lib.rs:321:51: 325:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 28), span := "src/lib.rs:321:79: 321:80" } (List.cons { kind := (StatementKind.storageLive 33), span := "src/lib.rs:324:9: 324:23" } (List.cons { kind := (StatementKind.assign { local_ := 33, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 19, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:324:9: 324:23" } (List.cons { kind := (StatementKind.assign { local_ := 26, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 33, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 })), span := "src/lib.rs:324:9: 324:23" } (List.cons { kind := (StatementKind.storageDead 33), span := "src/lib.rs:324:22: 324:23" } List.nil))))), terminator := { kind := (TerminatorKind.goto 4), span := "src/lib.rs:321:51: 325:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 25, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 26, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:321:51: 325:6" } (List.cons { kind := (StatementKind.assign { local_ := 24, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 25, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543")), layoutIdx := 4 })), span := "src/lib.rs:321:51: 325:6" } (List.cons { kind := (StatementKind.storageDead 27), span := "src/lib.rs:325:5: 325:6" } (List.cons { kind := (StatementKind.storageDead 25), span := "src/lib.rs:325:5: 325:6" } (List.cons { kind := (StatementKind.storageDead 26), span := "src/lib.rs:325:6: 325:7" } (List.cons { kind := (StatementKind.storageLive 34), span := "src/lib.rs:326:9: 326:21" } (List.cons { kind := (StatementKind.storageLive 35), span := "src/lib.rs:326:53: 327:39" } (List.cons { kind := (StatementKind.storageLive 36), span := "src/lib.rs:326:53: 327:39" } (List.cons { kind := (StatementKind.storageLive 37), span := "src/lib.rs:326:53: 326:62" } (List.cons { kind := (StatementKind.storageLive 38), span := "src/lib.rs:326:53: 326:62" } (List.cons { kind := (StatementKind.assign { local_ := 38, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 3, projection := List.nil })), span := "src/lib.rs:326:53: 326:62" } (List.cons { kind := (StatementKind.assign { local_ := 37, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 38, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:326:53: 326:62" } (List.cons { kind := (StatementKind.assign { local_ := 36, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 37, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt43543")), layoutIdx := 4 })), span := "src/lib.rs:326:53: 327:39" } (List.cons { kind := (StatementKind.storageDead 37), span := "src/lib.rs:326:61: 326:62" } (List.cons { kind := (StatementKind.assign { local_ := 35, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 36, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:326:53: 327:39" } (List.cons { kind := (StatementKind.assign { local_ := 34, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 35, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt43543")), layoutIdx := 4 })), span := "src/lib.rs:326:53: 327:39" } (List.cons { kind := (StatementKind.storageDead 35), span := "src/lib.rs:327:38: 327:39" } (List.cons { kind := (StatementKind.storageDead 38), span := "src/lib.rs:327:39: 327:40" } (List.cons { kind := (StatementKind.storageDead 36), span := "src/lib.rs:327:39: 327:40" } (List.cons { kind := (StatementKind.storageLive 39), span := "src/lib.rs:328:9: 328:21" } (List.cons { kind := (StatementKind.storageLive 40), span := "src/lib.rs:328:29: 328:56" } (List.cons { kind := (StatementKind.storageLive 41), span := "src/lib.rs:328:29: 328:37" } (List.cons { kind := (StatementKind.assign { local_ := 41, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 24, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:328:29: 328:37" } (List.cons { kind := (StatementKind.storageLive 42), span := "src/lib.rs:328:46: 328:55" } (List.cons { kind := (StatementKind.assign { local_ := 42, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:328:46: 328:55" } List.nil))))))))))))))))))))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__AnnealVtableTrait43543::eval_vt" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543") List.nil)), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 41, projection := List.nil }) (List.cons (Operand.move { local_ := 42, projection := List.nil }) List.nil)) { local_ := 40, projection := List.nil } (Option.some 5) UnwindAction.continue_), span := "src/lib.rs:328:29: 328:56" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 42), span := "src/lib.rs:328:55: 328:56" } (List.cons { kind := (StatementKind.storageDead 41), span := "src/lib.rs:328:55: 328:56" } (List.cons { kind := (StatementKind.storageLive 43), span := "src/lib.rs:328:59: 328:76" } (List.cons { kind := (StatementKind.storageLive 44), span := "src/lib.rs:328:59: 328:67" } (List.cons { kind := (StatementKind.assign { local_ := 44, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 24, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:328:59: 328:67" } List.nil))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__AnnealVtableTrait43543::tag_vt" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543") List.nil)), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 44, projection := List.nil }) List.nil) { local_ := 43, projection := List.nil } (Option.some 6) UnwindAction.continue_), span := "src/lib.rs:328:59: 328:76" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 44), span := "src/lib.rs:328:75: 328:76" } (List.cons { kind := (StatementKind.assign { local_ := 39, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 40, projection := List.nil }) (Operand.move { local_ := 43, projection := List.nil }))), span := "src/lib.rs:328:29: 328:76" } (List.cons { kind := (StatementKind.storageDead 43), span := "src/lib.rs:328:75: 328:76" } (List.cons { kind := (StatementKind.storageDead 40), span := "src/lib.rs:328:75: 328:76" } (List.cons { kind := (StatementKind.storageLive 45), span := "src/lib.rs:329:9: 329:22" } (List.cons { kind := (StatementKind.storageLive 46), span := "src/lib.rs:329:30: 329:42" } (List.cons { kind := (StatementKind.assign { local_ := 46, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 34, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:329:30: 329:42" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__AnnealVtableAlt43543::eval_alt" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt43543") List.nil)), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 46, projection := List.nil }) List.nil) { local_ := 45, projection := List.nil } (Option.some 7) UnwindAction.continue_), span := "src/lib.rs:329:30: 329:53" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 46), span := "src/lib.rs:329:52: 329:53" } (List.cons { kind := (StatementKind.storageLive 47), span := "src/lib.rs:330:9: 330:22" } (List.cons { kind := (StatementKind.storageLive 48), span := "src/lib.rs:330:33: 330:79" } (List.cons { kind := (StatementKind.storageLive 49), span := "src/lib.rs:330:52: 330:64" } (List.cons { kind := (StatementKind.assign { local_ := 49, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 14, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:330:52: 330:64" } (List.cons { kind := (StatementKind.storageLive 50), span := "src/lib.rs:330:66: 330:78" } (List.cons { kind := (StatementKind.assign { local_ := 50, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 34, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:330:66: 330:78" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::ptr::addr_eq" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543") (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt43543") List.nil))), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 49, projection := List.nil }) (List.cons (Operand.move { local_ := 50, projection := List.nil }) List.nil)) { local_ := 48, projection := List.nil } (Option.some 8) UnwindAction.continue_), span := "src/lib.rs:330:33: 330:79" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 48, projection := List.nil }) { branches := (List.cons (0, 10) List.nil), otherwise := 9 }), span := "src/lib.rs:330:33: 330:79" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 50), span := "src/lib.rs:330:78: 330:79" } (List.cons { kind := (StatementKind.storageDead 49), span := "src/lib.rs:330:78: 330:79" } (List.cons { kind := (StatementKind.assign { local_ := 47, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:331:9: 331:13" } List.nil))), terminator := { kind := (TerminatorKind.goto 11), span := "src/lib.rs:330:30: 334:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 50), span := "src/lib.rs:330:78: 330:79" } (List.cons { kind := (StatementKind.storageDead 49), span := "src/lib.rs:330:78: 330:79" } (List.cons { kind := (StatementKind.assign { local_ := 47, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:333:9: 333:13" } List.nil))), terminator := { kind := (TerminatorKind.goto 11), span := "src/lib.rs:330:30: 334:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 48), span := "src/lib.rs:334:5: 334:6" } (List.cons { kind := (StatementKind.storageLive 51), span := "src/lib.rs:335:9: 335:22" } (List.cons { kind := (StatementKind.storageLive 52), span := "src/lib.rs:335:33: 335:81" } (List.cons { kind := (StatementKind.storageLive 53), span := "src/lib.rs:335:52: 335:64" } (List.cons { kind := (StatementKind.assign { local_ := 53, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 14, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:335:52: 335:64" } (List.cons { kind := (StatementKind.storageLive 54), span := "src/lib.rs:335:66: 335:80" } (List.cons { kind := (StatementKind.assign { local_ := 54, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 19, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:335:66: 335:80" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::ptr::addr_eq" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543") (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait43543") List.nil))), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 53, projection := List.nil }) (List.cons (Operand.move { local_ := 54, projection := List.nil }) List.nil)) { local_ := 52, projection := List.nil } (Option.some 12) UnwindAction.continue_), span := "src/lib.rs:335:33: 335:81" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 52, projection := List.nil }) { branches := (List.cons (0, 14) List.nil), otherwise := 13 }), span := "src/lib.rs:335:33: 335:81" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 54), span := "src/lib.rs:335:80: 335:81" } (List.cons { kind := (StatementKind.storageDead 53), span := "src/lib.rs:335:80: 335:81" } (List.cons { kind := (StatementKind.assign { local_ := 51, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:336:9: 336:13" } List.nil))), terminator := { kind := (TerminatorKind.goto 15), span := "src/lib.rs:335:30: 339:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 54), span := "src/lib.rs:335:80: 335:81" } (List.cons { kind := (StatementKind.storageDead 53), span := "src/lib.rs:335:80: 335:81" } (List.cons { kind := (StatementKind.assign { local_ := 51, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }))), span := "src/lib.rs:338:9: 338:13" } List.nil))), terminator := { kind := (TerminatorKind.goto 15), span := "src/lib.rs:335:30: 339:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 52), span := "src/lib.rs:339:5: 339:6" } (List.cons { kind := (StatementKind.storageLive 55), span := "src/lib.rs:340:5: 340:59" } (List.cons { kind := (StatementKind.storageLive 56), span := "src/lib.rs:340:5: 340:43" } (List.cons { kind := (StatementKind.storageLive 57), span := "src/lib.rs:340:5: 340:17" } (List.cons { kind := (StatementKind.assign { local_ := 57, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 39, projection := List.nil }))), span := "src/lib.rs:340:5: 340:17" } (List.cons { kind := (StatementKind.storageLive 58), span := "src/lib.rs:340:20: 340:43" } (List.cons { kind := (StatementKind.storageLive 59), span := "src/lib.rs:340:21: 340:34" } (List.cons { kind := (StatementKind.assign { local_ := 59, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 45, projection := List.nil }))), span := "src/lib.rs:340:21: 340:34" } (List.cons { kind := (StatementKind.assign { local_ := 60, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:340:20: 340:43" } List.nil))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 60, projection := List.nil }) true 16 UnwindAction.continue_), span := "src/lib.rs:340:20: 340:43" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 58, projection := List.nil } (Rvalue.binaryOp BinOp.shl (Operand.move { local_ := 59, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }))), span := "src/lib.rs:340:20: 340:43" } (List.cons { kind := (StatementKind.storageDead 59), span := "src/lib.rs:340:42: 340:43" } (List.cons { kind := (StatementKind.assign { local_ := 56, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 57, projection := List.nil }) (Operand.move { local_ := 58, projection := List.nil }))), span := "src/lib.rs:340:5: 340:43" } (List.cons { kind := (StatementKind.storageDead 58), span := "src/lib.rs:340:42: 340:43" } (List.cons { kind := (StatementKind.storageDead 57), span := "src/lib.rs:340:42: 340:43" } (List.cons { kind := (StatementKind.storageLive 61), span := "src/lib.rs:340:46: 340:59" } (List.cons { kind := (StatementKind.assign { local_ := 61, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 47, projection := List.nil }))), span := "src/lib.rs:340:46: 340:59" } (List.cons { kind := (StatementKind.assign { local_ := 55, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 56, projection := List.nil }) (Operand.move { local_ := 61, projection := List.nil }))), span := "src/lib.rs:340:5: 340:59" } (List.cons { kind := (StatementKind.storageDead 61), span := "src/lib.rs:340:58: 340:59" } (List.cons { kind := (StatementKind.storageDead 56), span := "src/lib.rs:340:58: 340:59" } (List.cons { kind := (StatementKind.storageLive 62), span := "src/lib.rs:340:62: 340:75" } (List.cons { kind := (StatementKind.assign { local_ := 62, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 51, projection := List.nil }))), span := "src/lib.rs:340:62: 340:75" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 55, projection := List.nil }) (Operand.move { local_ := 62, projection := List.nil }))), span := "src/lib.rs:340:5: 340:75" } (List.cons { kind := (StatementKind.storageDead 62), span := "src/lib.rs:340:74: 340:75" } (List.cons { kind := (StatementKind.storageDead 55), span := "src/lib.rs:340:74: 340:75" } (List.cons { kind := (StatementKind.storageDead 51), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 47), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 45), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 39), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 34), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 24), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 19), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 14), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:341:1: 341:2" } List.nil))))))))))))))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:341:2: 341:2" }, isCleanup := false } List.nil))))))))))))))))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0000.Driver

namespace F0000.RecvTraitEvalVt

/-! Captured `miri_diff_corpus` item `__AnnealVtableReceiver43543_as___AnnealVtableTrait43543_eval_vt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_3); StorageLive(_4); _4 = copy _2; StorageLive(_5); _5 = copy ((*_1).0: u32); _3 = BitXor(move _4, move _5); StorageDead(_5); StorageDead(_4); _0 = BitAnd(move _3, const 65535_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableTrait43543>::eval_vt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableTrait43543::eval_vt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableTrait43543>::eval_vt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", predicateKey := "miri_diff_corpus::__AnnealVtableAlt43543", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt43543"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", predicateKey := "miri_diff_corpus::__AnnealVtableTrait43543", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait43543"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableAlt43543>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver43543 as __AnnealVtableTrait43543>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver43543 as __AnnealVtableTrait43543>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableTrait43543>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableTrait43543>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt43543::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait43543::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait43543::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", slotIdx := 4 } List.nil))),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:289:9: 289:24" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:289:10: 289:11" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:289:10: 289:11" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:289:14: 289:23" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:289:14: 289:23" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 4, projection := List.nil }) (Operand.move { local_ := 5, projection := List.nil }))), span := "src/lib.rs:289:9: 289:24" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:289:23: 289:24" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:289:23: 289:24" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 65535, sizeBytes := 4 })) }))), span := "src/lib.rs:289:9: 289:36" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:289:35: 289:36" } List.nil)))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:290:6: 290:6" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0000.RecvTraitEvalVt

namespace F0000.RecvTraitTagVt

/-! Captured `miri_diff_corpus` item `__AnnealVtableReceiver43543_as___AnnealVtableTrait43543_tag_vt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = copy ((*_1).0: u32); _2 = BitAnd(move _3, const 63_u32); StorageDead(_3); _0 = BitXor(move _2, const 21_u32); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableTrait43543>::tag_vt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableTrait43543::tag_vt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableTrait43543>::tag_vt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", predicateKey := "miri_diff_corpus::__AnnealVtableAlt43543", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt43543"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", predicateKey := "miri_diff_corpus::__AnnealVtableTrait43543", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait43543"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableAlt43543>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver43543 as __AnnealVtableTrait43543>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver43543 as __AnnealVtableTrait43543>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableTrait43543>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableTrait43543>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt43543::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait43543::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait43543::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", slotIdx := 4 } List.nil))),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:292:9: 292:30" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:292:10: 292:19" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:292:10: 292:19" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 63, sizeBytes := 4 })) }))), span := "src/lib.rs:292:9: 292:30" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:292:29: 292:30" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 2, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 21, sizeBytes := 4 })) }))), span := "src/lib.rs:292:9: 292:40" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:292:39: 292:40" } List.nil))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:293:6: 293:6" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0000.RecvTraitTagVt

namespace F0000.RecvAltEvalAlt

/-! Captured `miri_diff_corpus` item `__AnnealVtableReceiver43543_as___AnnealVtableAlt43543_eval_alt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))) }

-- bb0: StorageLive(_2); _2 = copy ((*_1).0: u32); _3 = Lt(const 1_u32, const 32_u32); assert(move _3, "attempt to shift right by `{}`, which would overflow", const 1_u32) -> [success: bb1, unwind continue]
-- bb1: _0 = Shr(move _2, const 1_u32); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableAlt43543>::eval_alt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableAlt43543::eval_alt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableAlt43543>::eval_alt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", predicateKey := "miri_diff_corpus::__AnnealVtableAlt43543", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt43543"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", predicateKey := "miri_diff_corpus::__AnnealVtableTrait43543", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait43543"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableAlt43543>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver43543 as __AnnealVtableTrait43543>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver43543 as __AnnealVtableTrait43543>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableTrait43543>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableTrait43543>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt43543::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait43543::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait43543::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", slotIdx := 4 } List.nil))),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:305:9: 305:18" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:305:9: 305:18" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:305:9: 305:26" } List.nil)))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 3, projection := List.nil }) true 1 UnwindAction.continue_), span := "src/lib.rs:305:9: 305:26" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.shr (Operand.move { local_ := 2, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:305:9: 305:26" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:305:25: 305:26" } List.nil)), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:306:6: 306:6" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0000.RecvAltEvalAlt

namespace F0000.AltRecvTraitEvalVt

/-! Captured `miri_diff_corpus` item `__AnnealVtableAltReceiver43543_as___AnnealVtableTrait43543_eval_vt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 0 List.nil)) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))) }

-- bb0: StorageLive(_3); StorageLive(_4); StorageLive(_5); StorageLive(_6); _6 = copy _2; _7 = Lt(const 1_u32, const 32_u32); assert(move _7, "attempt to shift right by `{}`, which would overflow", const 1_u32) -> [success: bb1, unwind continue]
-- bb1: _5 = Shr(move _6, const 1_u32); StorageDead(_6); StorageLive(_8); _8 = copy ((*_1).0: u32); _4 = BitXor(move _5, move _8); StorageDead(_8); StorageDead(_5); StorageLive(_9); _9 = copy ((*_1).1: u32); _3 = BitXor(move _4, move _9); StorageDead(_9); StorageDead(_4); _0 = BitAnd(move _3, const 65535_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableAltReceiver43543 as __AnnealVtableTrait43543>::eval_vt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableTrait43543::eval_vt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver43543" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableAltReceiver43543 as __AnnealVtableTrait43543>::eval_vt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", predicateKey := "miri_diff_corpus::__AnnealVtableAlt43543", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt43543"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", predicateKey := "miri_diff_corpus::__AnnealVtableTrait43543", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait43543"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableAlt43543>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver43543 as __AnnealVtableTrait43543>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver43543 as __AnnealVtableTrait43543>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableTrait43543>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableTrait43543>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt43543::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait43543::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait43543::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", slotIdx := 4 } List.nil))),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver43543" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 7), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:297:9: 297:45" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:297:10: 297:32" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:297:10: 297:21" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:297:11: 297:12" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:297:11: 297:12" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:297:10: 297:21" } List.nil))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 7, projection := List.nil }) true 1 UnwindAction.continue_), span := "src/lib.rs:297:10: 297:21" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.binaryOp BinOp.shr (Operand.move { local_ := 6, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:297:10: 297:21" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:297:20: 297:21" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:297:24: 297:32" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:297:24: 297:32" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 5, projection := List.nil }) (Operand.move { local_ := 8, projection := List.nil }))), span := "src/lib.rs:297:10: 297:32" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:297:31: 297:32" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:297:31: 297:32" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:297:35: 297:44" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 1 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:297:35: 297:44" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 4, projection := List.nil }) (Operand.move { local_ := 9, projection := List.nil }))), span := "src/lib.rs:297:9: 297:45" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:297:44: 297:45" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:297:44: 297:45" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 65535, sizeBytes := 4 })) }))), span := "src/lib.rs:297:9: 297:57" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:297:56: 297:57" } List.nil)))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:298:6: 298:6" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0000.AltRecvTraitEvalVt

namespace F0000.AltRecvTraitTagVt

/-! Captured `miri_diff_corpus` item `__AnnealVtableAltReceiver43543_as___AnnealVtableTrait43543_tag_vt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 0 List.nil)) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_2); StorageLive(_3); StorageLive(_4); _4 = copy ((*_1).0: u32); StorageLive(_5); _5 = copy ((*_1).1: u32); _3 = BitXor(move _4, move _5); StorageDead(_5); StorageDead(_4); _2 = BitAnd(move _3, const 63_u32); StorageDead(_3); _0 = BitXor(move _2, const 42_u32); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableAltReceiver43543 as __AnnealVtableTrait43543>::tag_vt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableTrait43543::tag_vt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver43543" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableAltReceiver43543 as __AnnealVtableTrait43543>::tag_vt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", predicateKey := "miri_diff_corpus::__AnnealVtableAlt43543", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt43543"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", predicateKey := "miri_diff_corpus::__AnnealVtableTrait43543", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait43543"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableAlt43543>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver43543 as __AnnealVtableTrait43543>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver43543 as __AnnealVtableTrait43543>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver43543" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableTrait43543>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver43543 as __AnnealVtableTrait43543>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt43543::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt43543", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait43543::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait43543::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait43543", slotIdx := 4 } List.nil))),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver43543" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:300:9: 300:43" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:300:10: 300:32" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:300:11: 300:19" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:300:11: 300:19" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:300:22: 300:31" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 1 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:300:22: 300:31" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 4, projection := List.nil }) (Operand.move { local_ := 5, projection := List.nil }))), span := "src/lib.rs:300:10: 300:32" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:300:31: 300:32" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:300:31: 300:32" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 63, sizeBytes := 4 })) }))), span := "src/lib.rs:300:9: 300:43" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:300:42: 300:43" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 2, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 42, sizeBytes := 4 })) }))), span := "src/lib.rs:300:9: 300:53" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:300:52: 300:53" } List.nil))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:301:6: 301:6" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0000.AltRecvTraitTagVt

/-- Linked callee table of `finding_0000`: the driver and the 5 trait-method impls. -/
def F0000.linkedCallees : List CapturedMir :=
  [F0000.Driver.body, F0000.RecvTraitEvalVt.body, F0000.RecvTraitTagVt.body, F0000.RecvAltEvalAlt.body, F0000.AltRecvTraitEvalVt.body, F0000.AltRecvTraitTagVt.body]

set_option maxRecDepth 1000000 in
/-- Campaign #22 `finding_0000` end-to-end agreement with Miri (`MIRI_PASS:scalar:20:4`):
`miri_diff_corpus::pass_option_some_niche_and_single_c_mut__b0_c10` returns `20_u32` with the driver and the 5 trait-method
impls linked. -/
theorem F0000.miri_agreement :
    evalMirDiffTagBounded 512 F0000.Outer.body
      (initMachineStateWithMemoryAndCallees F0000.Outer.body [] emptyMemory F0000.linkedCallees) =
      .normalScalar 20 4 := by
  rfl

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0000`, only the driver linked (the 5 trait-method impls are absent)): the first virtual call resolves through the captured vtable to a method `DefPath` with no linked body, so the run stops at that `externalCall` (never a value).
Fault site: `src/lib.rs:328:29: 328:56`. -/
theorem F0000.control_noImpls :
    runC22 F0000.Outer.body [F0000.Driver.body] =
      .externalCall "miri_diff_corpus::<__AnnealVtableAltReceiver43543 as __AnnealVtableTrait43543>::eval_vt" ∧
    probeC22 F0000.Outer.body [F0000.Driver.body] =
      (.externalCall "miri_diff_corpus::<__AnnealVtableAltReceiver43543 as __AnnealVtableTrait43543>::eval_vt", "src/lib.rs:328:29: 328:56") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0000`, nothing linked): the outer function's call to the unlinked driver escapes as `externalCall` (never a value).
Fault site: `src/lib.rs:370:32: 373:6`. -/
theorem F0000.control_noDriver :
    runC22 F0000.Outer.body [] =
      .externalCall "miri_diff_corpus::__anneal_vt_driver_43543" ∧
    probeC22 F0000.Outer.body [] =
      (.externalCall "miri_diff_corpus::__anneal_vt_driver_43543", "src/lib.rs:370:32: 373:6") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0000`, `vtables` stripped from the outer body and from every linked body): the first `&T as &dyn Trait` unsizing finds no usable captured `(T, dyn Trait)` vtable (missing table, missing record, or `bodyVTablesConsistent` failure) and fails closed with `.unsupported` at that statement (never `.ub`, never a value).
Fault site: `src/lib.rs:317:55: 318:41`. -/
theorem F0000.control_stripped :
    runC22 (stripVTables F0000.Outer.body) (F0000.linkedCallees.map stripVTables) =
      .unsupported ∧
    probeC22 (stripVTables F0000.Outer.body) (F0000.linkedCallees.map stripVTables) =
      (.unsupported, "src/lib.rs:317:55: 318:41") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0000`, `vtables` stripped from every linked body (outer body intact)): the first `&T as &dyn Trait` unsizing finds no usable captured `(T, dyn Trait)` vtable (missing table, missing record, or `bodyVTablesConsistent` failure) and fails closed with `.unsupported` at that statement (never `.ub`, never a value).
Fault site: `src/lib.rs:317:55: 318:41`. -/
theorem F0000.control_strippedLinked :
    runC22 F0000.Outer.body (F0000.linkedCallees.map stripVTables) =
      .unsupported ∧
    probeC22 F0000.Outer.body (F0000.linkedCallees.map stripVTables) =
      (.unsupported, "src/lib.rs:317:55: 318:41") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0000`, unit-consistent forgery `forgeNonMethodSlot` applied to every body): the virtual call reads a vtable slot that is not a method (`.size` header slot, or past the end of the table): Miri's `get_vtable_entries`/`VtblEntry` dispatch raises UB (\"`dyn` call trying to call something that is not a method\" / out-of-bounds vtable index), and the TCB faults `.ub` at that call.
Fault site: `src/lib.rs:328:29: 328:56`. -/
theorem F0000.control_nonMethodSlot :
    runC22 (mapVTables forgeNonMethodSlot F0000.Outer.body) (F0000.linkedCallees.map (mapVTables forgeNonMethodSlot)) =
      .ub ∧
    probeC22 (mapVTables forgeNonMethodSlot F0000.Outer.body) (F0000.linkedCallees.map (mapVTables forgeNonMethodSlot)) =
      (.ub, "src/lib.rs:328:29: 328:56") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0000`, unit-consistent forgery `forgeTruncatedSlots` applied to every body): the virtual call reads a vtable slot that is not a method (`.size` header slot, or past the end of the table): Miri's `get_vtable_entries`/`VtblEntry` dispatch raises UB (\"`dyn` call trying to call something that is not a method\" / out-of-bounds vtable index), and the TCB faults `.ub` at that call.
Fault site: `src/lib.rs:328:59: 328:76`. -/
theorem F0000.control_truncatedSlots :
    runC22 (mapVTables forgeTruncatedSlots F0000.Outer.body) (F0000.linkedCallees.map (mapVTables forgeTruncatedSlots)) =
      .ub ∧
    probeC22 (mapVTables forgeTruncatedSlots F0000.Outer.body) (F0000.linkedCallees.map (mapVTables forgeTruncatedSlots)) =
      (.ub, "src/lib.rs:328:59: 328:76") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0000`, unit-consistent forgery `forgeWrongDynKey` applied to every body): the first `&T as &dyn Trait` unsizing finds no usable captured `(T, dyn Trait)` vtable (missing table, missing record, or `bodyVTablesConsistent` failure) and fails closed with `.unsupported` at that statement (never `.ub`, never a value).
Fault site: `src/lib.rs:317:55: 318:41`. -/
theorem F0000.control_wrongDynKey :
    runC22 (mapVTables forgeWrongDynKey F0000.Outer.body) (F0000.linkedCallees.map (mapVTables forgeWrongDynKey)) =
      .unsupported ∧
    probeC22 (mapVTables forgeWrongDynKey F0000.Outer.body) (F0000.linkedCallees.map (mapVTables forgeWrongDynKey)) =
      (.unsupported, "src/lib.rs:317:55: 318:41") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0000`, `forgeNonMethodSlot` applied to the driver's table only (linked bodies disagree)): the first `&T as &dyn Trait` unsizing finds no usable captured `(T, dyn Trait)` vtable (missing table, missing record, or `bodyVTablesConsistent` failure) and fails closed with `.unsupported` at that statement (never `.ub`, never a value).
Fault site: `src/lib.rs:317:55: 318:41`. -/
theorem F0000.control_inconsistent :
    runC22 F0000.Outer.body (mapVTables forgeNonMethodSlot F0000.Driver.body :: F0000.linkedCallees.drop 1) =
      .unsupported ∧
    probeC22 F0000.Outer.body (mapVTables forgeNonMethodSlot F0000.Driver.body :: F0000.linkedCallees.drop 1) =
      (.unsupported, "src/lib.rs:317:55: 318:41") :=
  ⟨by rfl, by rfl⟩

/-! ### Campaign #22 `finding_0001`: `miri_diff_corpus::pass_bitwise_and_or_xor_not__b8_c9` (Miri: `MIRI_PASS:scalar:182:4`).

Verbatim `layouts`/`body` definitions emitted by HEAD `anneal-rustc-capture` (`Runtime(PostCleanup)` MIR,
nightly-2026-06-01, `-Zmir-opt-level=0 -C debug-assertions=off -C overflow-checks=on`). -/

namespace F0001.Outer

/-! Captured `miri_diff_corpus` item `pass_bitwise_and_or_xor_not__b8_c9`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 1 List.nil)) } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_1); _1 = const 252641535_u32; StorageLive(_2); _2 = const 16715535_u32; StorageLive(_3); StorageLive(_4); _4 = copy _1; StorageLive(_5); _5 = copy _2; _3 = BitAnd(move _4, move _5); StorageDead(_5); StorageDead(_4); StorageLive(_6); StorageLive(_7); _7 = copy _1; StorageLive(_8); _8 = copy _2; _6 = BitOr(move _7, move _8); StorageDead(_8); StorageDead(_7); StorageLive(_9); StorageLive(_10); _10 = copy _1; StorageLive(_11); _11 = copy _2; _9 = BitXor(move _10, move _11); StorageDead(_11); StorageDead(_10); StorageLive(_12); StorageLive(_13); StorageLive(_14); StorageLive(_15); _15 = copy _3; StorageLive(_16); _16 = copy _6; _14 = BitXor(move _15, move _16); StorageDead(_16); StorageDead(_15); StorageLive(_17); _17 = copy _9; _18 = SubWithOverflow(copy _14, copy _17); assert(!move (_18.1: bool), "attempt to compute `{} - {}`, which would overflow", move _14, move _17) -> [success: bb1, unwind continue]
-- bb1: _13 = move (_18.0: u32); StorageDead(_17); StorageDead(_14); StorageLive(_19); StorageLive(_20); _20 = Not(const 0_u32); _19 = BitXor(move _20, const u32::MAX); StorageDead(_20); _21 = AddWithOverflow(copy _13, copy _19); assert(!move (_21.1: bool), "attempt to compute `{} + {}`, which would overflow", move _13, move _19) -> [success: bb2, unwind continue]
-- bb2: _12 = move (_21.0: u32); StorageDead(_19); StorageDead(_13); StorageLive(_22); StorageLive(_23); StorageLive(_24); _24 = copy _1; _23 = BitAnd(move _24, const 65535_u32); StorageDead(_24); _22 = __anneal_vt_driver_45921(move _23, const 24_u32) -> [return: bb3, unwind continue]
-- bb3: StorageDead(_23); StorageLive(_25); _25 = copy _12; StorageLive(_26); _26 = copy _22; _0 = BitXor(move _25, move _26); StorageDead(_26); StorageDead(_25); StorageDead(_22); StorageDead(_12); StorageDead(_9); StorageDead(_6); StorageDead(_3); StorageDead(_2); StorageDead(_1); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::pass_bitwise_and_or_xor_not__b8_c9",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", predicateKey := "miri_diff_corpus::__AnnealVtableAlt45921", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt45921"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", predicateKey := "miri_diff_corpus::__AnnealVtableTrait45921", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait45921"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableAlt45921>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver45921 as __AnnealVtableTrait45921>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver45921 as __AnnealVtableTrait45921>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableTrait45921>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableTrait45921>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt45921::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait45921::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait45921::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", slotIdx := 4 } List.nil))),
    argCount := 0,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "y") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "and_v") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "or_v") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "xor_v") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__tail___miri_vt_45921") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) (List.cons RigidTy.bool List.nil))), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) (List.cons RigidTy.bool List.nil))), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__miri_vt_45921") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))))))))))))))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 18), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 21), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 1), span := "src/lib.rs:344:9: 344:10" } (List.cons { kind := (StatementKind.assign { local_ := 1, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 252641535, sizeBytes := 4 })) }))), span := "src/lib.rs:344:18: 344:29" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:345:9: 345:10" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 16715535, sizeBytes := 4 })) }))), span := "src/lib.rs:345:18: 345:29" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:346:9: 346:14" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:346:17: 346:18" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:346:17: 346:18" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:346:21: 346:22" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:346:21: 346:22" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 4, projection := List.nil }) (Operand.move { local_ := 5, projection := List.nil }))), span := "src/lib.rs:346:17: 346:22" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:346:21: 346:22" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:346:21: 346:22" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:347:9: 347:13" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:347:16: 347:17" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:347:16: 347:17" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:347:20: 347:21" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:347:20: 347:21" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.binaryOp BinOp.bitOr (Operand.move { local_ := 7, projection := List.nil }) (Operand.move { local_ := 8, projection := List.nil }))), span := "src/lib.rs:347:16: 347:21" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:347:20: 347:21" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:347:20: 347:21" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:348:9: 348:14" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:348:17: 348:18" } (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:348:17: 348:18" } (List.cons { kind := (StatementKind.storageLive 11), span := "src/lib.rs:348:21: 348:22" } (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:348:21: 348:22" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 10, projection := List.nil }) (Operand.move { local_ := 11, projection := List.nil }))), span := "src/lib.rs:348:17: 348:22" } (List.cons { kind := (StatementKind.storageDead 11), span := "src/lib.rs:348:21: 348:22" } (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:348:21: 348:22" } (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:349:9: 349:31" } (List.cons { kind := (StatementKind.storageLive 13), span := "src/lib.rs:349:39: 349:61" } (List.cons { kind := (StatementKind.storageLive 14), span := "src/lib.rs:349:39: 349:53" } (List.cons { kind := (StatementKind.storageLive 15), span := "src/lib.rs:349:40: 349:45" } (List.cons { kind := (StatementKind.assign { local_ := 15, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:349:40: 349:45" } (List.cons { kind := (StatementKind.storageLive 16), span := "src/lib.rs:349:48: 349:52" } (List.cons { kind := (StatementKind.assign { local_ := 16, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 6, projection := List.nil }))), span := "src/lib.rs:349:48: 349:52" } (List.cons { kind := (StatementKind.assign { local_ := 14, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 15, projection := List.nil }) (Operand.move { local_ := 16, projection := List.nil }))), span := "src/lib.rs:349:39: 349:53" } (List.cons { kind := (StatementKind.storageDead 16), span := "src/lib.rs:349:52: 349:53" } (List.cons { kind := (StatementKind.storageDead 15), span := "src/lib.rs:349:52: 349:53" } (List.cons { kind := (StatementKind.storageLive 17), span := "src/lib.rs:349:56: 349:61" } (List.cons { kind := (StatementKind.assign { local_ := 17, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 9, projection := List.nil }))), span := "src/lib.rs:349:56: 349:61" } (List.cons { kind := (StatementKind.assign { local_ := 18, projection := List.nil } (Rvalue.binaryOp BinOp.subWithOverflow (Operand.copy { local_ := 14, projection := List.nil }) (Operand.copy { local_ := 17, projection := List.nil }))), span := "src/lib.rs:349:39: 349:61" } List.nil))))))))))))))))))))))))))))))))))))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 18, projection := (List.cons (ProjectionElem.field 1 { kind := RigidTy.bool, layoutIdx := 1 }) List.nil) }) false 1 UnwindAction.continue_), span := "src/lib.rs:349:39: 349:61" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 13, projection := List.nil } (Rvalue.use (Operand.move { local_ := 18, projection := (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil) }))), span := "src/lib.rs:349:39: 349:61" } (List.cons { kind := (StatementKind.storageDead 17), span := "src/lib.rs:349:60: 349:61" } (List.cons { kind := (StatementKind.storageDead 14), span := "src/lib.rs:349:60: 349:61" } (List.cons { kind := (StatementKind.storageLive 19), span := "src/lib.rs:349:64: 349:85" } (List.cons { kind := (StatementKind.storageLive 20), span := "src/lib.rs:349:65: 349:70" } (List.cons { kind := (StatementKind.assign { local_ := 20, projection := List.nil } (Rvalue.unaryOp UnOp.not (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:349:65: 349:70" } (List.cons { kind := (StatementKind.assign { local_ := 19, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 20, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 4294967295, sizeBytes := 4 })) }))), span := "src/lib.rs:349:64: 349:85" } (List.cons { kind := (StatementKind.storageDead 20), span := "src/lib.rs:349:84: 349:85" } (List.cons { kind := (StatementKind.assign { local_ := 21, projection := List.nil } (Rvalue.binaryOp BinOp.addWithOverflow (Operand.copy { local_ := 13, projection := List.nil }) (Operand.copy { local_ := 19, projection := List.nil }))), span := "src/lib.rs:349:39: 349:85" } List.nil))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 21, projection := (List.cons (ProjectionElem.field 1 { kind := RigidTy.bool, layoutIdx := 1 }) List.nil) }) false 2 UnwindAction.continue_), span := "src/lib.rs:349:39: 349:85" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.use (Operand.move { local_ := 21, projection := (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil) }))), span := "src/lib.rs:349:39: 349:85" } (List.cons { kind := (StatementKind.storageDead 19), span := "src/lib.rs:349:84: 349:85" } (List.cons { kind := (StatementKind.storageDead 13), span := "src/lib.rs:349:84: 349:85" } (List.cons { kind := (StatementKind.storageLive 22), span := "src/lib.rs:350:9: 350:24" } (List.cons { kind := (StatementKind.storageLive 23), span := "src/lib.rs:350:57: 350:79" } (List.cons { kind := (StatementKind.storageLive 24), span := "src/lib.rs:350:57: 350:67" } (List.cons { kind := (StatementKind.assign { local_ := 24, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:350:58: 350:59" } (List.cons { kind := (StatementKind.assign { local_ := 23, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 24, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 65535, sizeBytes := 4 })) }))), span := "src/lib.rs:350:57: 350:79" } (List.cons { kind := (StatementKind.storageDead 24), span := "src/lib.rs:350:78: 350:79" } List.nil))))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__anneal_vt_driver_45921" List.nil), layoutIdx := 3 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 23, projection := List.nil }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 24, sizeBytes := 4 })) }) List.nil)) { local_ := 22, projection := List.nil } (Option.some 3) UnwindAction.continue_), span := "src/lib.rs:350:32: 350:87" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 23), span := "src/lib.rs:350:86: 350:87" } (List.cons { kind := (StatementKind.storageLive 25), span := "src/lib.rs:351:5: 351:27" } (List.cons { kind := (StatementKind.assign { local_ := 25, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 12, projection := List.nil }))), span := "src/lib.rs:351:5: 351:27" } (List.cons { kind := (StatementKind.storageLive 26), span := "src/lib.rs:351:30: 351:54" } (List.cons { kind := (StatementKind.assign { local_ := 26, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 22, projection := List.nil }))), span := "src/lib.rs:351:31: 351:46" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 25, projection := List.nil }) (Operand.move { local_ := 26, projection := List.nil }))), span := "src/lib.rs:351:5: 351:54" } (List.cons { kind := (StatementKind.storageDead 26), span := "src/lib.rs:351:53: 351:54" } (List.cons { kind := (StatementKind.storageDead 25), span := "src/lib.rs:351:53: 351:54" } (List.cons { kind := (StatementKind.storageDead 22), span := "src/lib.rs:352:1: 352:2" } (List.cons { kind := (StatementKind.storageDead 12), span := "src/lib.rs:352:1: 352:2" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:352:1: 352:2" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:352:1: 352:2" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:352:1: 352:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:352:1: 352:2" } (List.cons { kind := (StatementKind.storageDead 1), span := "src/lib.rs:352:1: 352:2" } List.nil))))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:352:2: 352:2" }, isCleanup := false } List.nil)))),
    fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0001.Outer

namespace F0001.Driver

/-! Captured `miri_diff_corpus` item `__anneal_vt_driver_45921`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 0 List.nil)) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))))))) }

-- bb0: StorageLive(_3); StorageLive(_4); StorageLive(_5); _5 = copy _2; _4 = BitXor(move _5, const 9_u32); StorageDead(_5); _3 = __AnnealVtableReceiver45921 { bias: move _4 }; StorageDead(_4); StorageLive(_6); StorageLive(_7); StorageLive(_8); StorageLive(_9); _9 = copy _1; _8 = BitAnd(move _9, const 255_u32); StorageDead(_9); _7 = BitXor(move _8, const 9_u32); StorageDead(_8); StorageLive(_10); StorageLive(_11); StorageLive(_12); _12 = copy _2; _13 = Lt(const 1_u32, const 32_u32); assert(move _13, "attempt to shift right by `{}`, which would overflow", const 1_u32) -> [success: bb1, unwind continue]
-- bb1: _11 = Shr(move _12, const 1_u32); StorageDead(_12); _10 = BitXor(move _11, const 9_u32); StorageDead(_11); _6 = __AnnealVtableAltReceiver45921 { pad: move _7, bias: move _10 }; StorageDead(_10); StorageDead(_7); StorageLive(_14); StorageLive(_15); StorageLive(_16); StorageLive(_17); StorageLive(_18); _18 = &_3; _17 = &(*_18); _16 = move _17 as &dyn __AnnealVtableTrait45921 (PointerCoercion(Unsize, AsCast)); StorageDead(_17); _15 = &(*_16); _14 = move _15 as &dyn __AnnealVtableTrait45921 (PointerCoercion(Unsize, Implicit)); StorageDead(_15); StorageDead(_18); StorageDead(_16); StorageLive(_19); StorageLive(_20); StorageLive(_21); StorageLive(_22); StorageLive(_23); _23 = &_6; _22 = &(*_23); _21 = move _22 as &dyn __AnnealVtableTrait45921 (PointerCoercion(Unsize, AsCast)); StorageDead(_22); _20 = &(*_21); _19 = move _20 as &dyn __AnnealVtableTrait45921 (PointerCoercion(Unsize, Implicit)); StorageDead(_20); StorageDead(_23); StorageDead(_21); StorageLive(_24); StorageLive(_25); StorageLive(_26); StorageLive(_27); StorageLive(_28); StorageLive(_29); _29 = copy _1; _28 = BitAnd(move _29, const 1_u32); StorageDead(_29); _27 = Eq(move _28, const 0_u32); switchInt(move _27) -> [0: bb3, otherwise: bb2]
-- bb2: StorageDead(_28); StorageLive(_30); StorageLive(_31); StorageLive(_32); _32 = &(*_14); _31 = move _32 as &dyn __AnnealVtableTrait45921 (PointerCoercion(Unsize, Implicit)); StorageDead(_32); _30 = &(*_31); _26 = move _30 as &dyn __AnnealVtableTrait45921 (PointerCoercion(Unsize, Implicit)); StorageDead(_31); StorageDead(_30); goto -> bb4
-- bb3: StorageDead(_28); StorageLive(_33); _33 = &(*_19); _26 = move _33 as &dyn __AnnealVtableTrait45921 (PointerCoercion(Unsize, Implicit)); StorageDead(_33); goto -> bb4
-- bb4: _25 = &(*_26); _24 = move _25 as &dyn __AnnealVtableTrait45921 (PointerCoercion(Unsize, Implicit)); StorageDead(_27); StorageDead(_25); StorageDead(_26); StorageLive(_34); StorageLive(_35); StorageLive(_36); StorageLive(_37); StorageLive(_38); _38 = &_3; _37 = &(*_38); _36 = move _37 as &dyn __AnnealVtableAlt45921 (PointerCoercion(Unsize, AsCast)); StorageDead(_37); _35 = &(*_36); _34 = move _35 as &dyn __AnnealVtableAlt45921 (PointerCoercion(Unsize, Implicit)); StorageDead(_35); StorageDead(_38); StorageDead(_36); StorageLive(_39); StorageLive(_40); StorageLive(_41); _41 = &(*_24); StorageLive(_42); _42 = copy _1; _40 = <dyn __AnnealVtableTrait45921 as __AnnealVtableTrait45921>::eval_vt(move _41, move _42) -> [return: bb5, unwind continue]
-- bb5: StorageDead(_42); StorageDead(_41); StorageLive(_43); StorageLive(_44); _44 = &(*_24); _43 = <dyn __AnnealVtableTrait45921 as __AnnealVtableTrait45921>::tag_vt(move _44) -> [return: bb6, unwind continue]
-- bb6: StorageDead(_44); _39 = BitXor(move _40, move _43); StorageDead(_43); StorageDead(_40); StorageLive(_45); StorageLive(_46); _46 = &(*_34); _45 = <dyn __AnnealVtableAlt45921 as __AnnealVtableAlt45921>::eval_alt(move _46) -> [return: bb7, unwind continue]
-- bb7: StorageDead(_46); StorageLive(_47); StorageLive(_48); StorageLive(_49); _49 = &raw const (*_14); StorageLive(_50); _50 = &raw const (*_34); _48 = core::ptr::addr_eq::<dyn __AnnealVtableTrait45921, dyn __AnnealVtableAlt45921>(move _49, move _50) -> [return: bb8, unwind continue]
-- bb8: switchInt(move _48) -> [0: bb10, otherwise: bb9]
-- bb9: StorageDead(_50); StorageDead(_49); _47 = const 1_u32; goto -> bb11
-- bb10: StorageDead(_50); StorageDead(_49); _47 = const 0_u32; goto -> bb11
-- bb11: StorageDead(_48); StorageLive(_51); StorageLive(_52); StorageLive(_53); _53 = &raw const (*_14); StorageLive(_54); _54 = &raw const (*_19); _52 = core::ptr::addr_eq::<dyn __AnnealVtableTrait45921, dyn __AnnealVtableTrait45921>(move _53, move _54) -> [return: bb12, unwind continue]
-- bb12: switchInt(move _52) -> [0: bb14, otherwise: bb13]
-- bb13: StorageDead(_54); StorageDead(_53); _51 = const 0_u32; goto -> bb15
-- bb14: StorageDead(_54); StorageDead(_53); _51 = const 2_u32; goto -> bb15
-- bb15: StorageDead(_52); StorageLive(_55); StorageLive(_56); StorageLive(_57); _57 = copy _39; StorageLive(_58); StorageLive(_59); _59 = copy _45; _60 = Lt(const 2_u32, const 32_u32); assert(move _60, "attempt to shift left by `{}`, which would overflow", const 2_u32) -> [success: bb16, unwind continue]
-- bb16: _58 = Shl(move _59, const 2_u32); StorageDead(_59); _56 = BitXor(move _57, move _58); StorageDead(_58); StorageDead(_57); StorageLive(_61); _61 = copy _47; _55 = BitXor(move _56, move _61); StorageDead(_61); StorageDead(_56); StorageLive(_62); _62 = copy _51; _0 = BitXor(move _55, move _62); StorageDead(_62); StorageDead(_55); StorageDead(_51); StorageDead(_47); StorageDead(_45); StorageDead(_39); StorageDead(_34); StorageDead(_24); StorageDead(_19); StorageDead(_14); StorageDead(_6); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::__anneal_vt_driver_45921",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", predicateKey := "miri_diff_corpus::__AnnealVtableAlt45921", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt45921"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", predicateKey := "miri_diff_corpus::__AnnealVtableTrait45921", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait45921"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableAlt45921>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver45921 as __AnnealVtableTrait45921>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver45921 as __AnnealVtableTrait45921>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableTrait45921>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableTrait45921>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt45921::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait45921::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait45921::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", slotIdx := 4 } List.nil))),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_seed") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_bias") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil), layoutIdx := 1 }, debugName := (Option.some "__vt_rec") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver45921" List.nil), layoutIdx := 2 }, debugName := (Option.some "__vt_other") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 }, debugName := (Option.some "__vt_rec_dyn") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 }, debugName := (Option.some "__vt_other_dyn") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver45921" List.nil)), layoutIdx := 6 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver45921" List.nil)), layoutIdx := 6 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 }, debugName := (Option.some "__vt_dyn") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt45921")), layoutIdx := 4 }, debugName := (Option.some "__vt_dyn_alt") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt45921")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt45921")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_virtual") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_alt_bits") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt45921")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_same_obj") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt45921")), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_diff_obj") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 13), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 60), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:310:9: 310:17" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:311:15: 311:31" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:311:15: 311:24" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:311:15: 311:24" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 5, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 9, sizeBytes := 4 })) }))), span := "src/lib.rs:311:15: 311:31" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:311:30: 311:31" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::__AnnealVtableReceiver45921" 0 Option.none) (List.cons (Operand.move { local_ := 4, projection := List.nil }) List.nil))), span := "src/lib.rs:310:49: 312:6" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:312:5: 312:6" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:313:9: 313:19" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:314:14: 314:42" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:314:14: 314:35" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:314:15: 314:24" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:314:15: 314:24" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 9, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 255, sizeBytes := 4 })) }))), span := "src/lib.rs:314:14: 314:35" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:314:34: 314:35" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 8, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 9, sizeBytes := 4 })) }))), span := "src/lib.rs:314:14: 314:42" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:314:41: 314:42" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:315:15: 315:41" } (List.cons { kind := (StatementKind.storageLive 11), span := "src/lib.rs:315:15: 315:34" } (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:315:16: 315:25" } (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:315:16: 315:25" } (List.cons { kind := (StatementKind.assign { local_ := 13, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:315:15: 315:34" } List.nil)))))))))))))))))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 13, projection := List.nil }) true 1 UnwindAction.continue_), span := "src/lib.rs:315:15: 315:34" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.binaryOp BinOp.shr (Operand.move { local_ := 12, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:315:15: 315:34" } (List.cons { kind := (StatementKind.storageDead 12), span := "src/lib.rs:315:33: 315:34" } (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 11, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 9, sizeBytes := 4 })) }))), span := "src/lib.rs:315:15: 315:41" } (List.cons { kind := (StatementKind.storageDead 11), span := "src/lib.rs:315:40: 315:41" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::__AnnealVtableAltReceiver45921" 0 Option.none) (List.cons (Operand.move { local_ := 7, projection := List.nil }) (List.cons (Operand.move { local_ := 10, projection := List.nil }) List.nil)))), span := "src/lib.rs:313:54: 316:6" } (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:316:5: 316:6" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:316:5: 316:6" } (List.cons { kind := (StatementKind.storageLive 14), span := "src/lib.rs:317:9: 317:21" } (List.cons { kind := (StatementKind.storageLive 15), span := "src/lib.rs:317:55: 318:41" } (List.cons { kind := (StatementKind.storageLive 16), span := "src/lib.rs:317:55: 318:41" } (List.cons { kind := (StatementKind.storageLive 17), span := "src/lib.rs:317:55: 317:64" } (List.cons { kind := (StatementKind.storageLive 18), span := "src/lib.rs:317:55: 317:64" } (List.cons { kind := (StatementKind.assign { local_ := 18, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 3, projection := List.nil })), span := "src/lib.rs:317:55: 317:64" } (List.cons { kind := (StatementKind.assign { local_ := 17, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 18, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:317:55: 317:64" } (List.cons { kind := (StatementKind.assign { local_ := 16, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 17, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 })), span := "src/lib.rs:317:55: 318:41" } (List.cons { kind := (StatementKind.storageDead 17), span := "src/lib.rs:317:63: 317:64" } (List.cons { kind := (StatementKind.assign { local_ := 15, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 16, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:317:55: 318:41" } (List.cons { kind := (StatementKind.assign { local_ := 14, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 15, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 })), span := "src/lib.rs:317:55: 318:41" } (List.cons { kind := (StatementKind.storageDead 15), span := "src/lib.rs:318:40: 318:41" } (List.cons { kind := (StatementKind.storageDead 18), span := "src/lib.rs:318:41: 318:42" } (List.cons { kind := (StatementKind.storageDead 16), span := "src/lib.rs:318:41: 318:42" } (List.cons { kind := (StatementKind.storageLive 19), span := "src/lib.rs:319:9: 319:23" } (List.cons { kind := (StatementKind.storageLive 20), span := "src/lib.rs:319:57: 320:41" } (List.cons { kind := (StatementKind.storageLive 21), span := "src/lib.rs:319:57: 320:41" } (List.cons { kind := (StatementKind.storageLive 22), span := "src/lib.rs:319:57: 319:68" } (List.cons { kind := (StatementKind.storageLive 23), span := "src/lib.rs:319:57: 319:68" } (List.cons { kind := (StatementKind.assign { local_ := 23, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 6, projection := List.nil })), span := "src/lib.rs:319:57: 319:68" } (List.cons { kind := (StatementKind.assign { local_ := 22, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 23, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:319:57: 319:68" } (List.cons { kind := (StatementKind.assign { local_ := 21, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 22, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 })), span := "src/lib.rs:319:57: 320:41" } (List.cons { kind := (StatementKind.storageDead 22), span := "src/lib.rs:319:67: 319:68" } (List.cons { kind := (StatementKind.assign { local_ := 20, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 21, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:319:57: 320:41" } (List.cons { kind := (StatementKind.assign { local_ := 19, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 20, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 })), span := "src/lib.rs:319:57: 320:41" } (List.cons { kind := (StatementKind.storageDead 20), span := "src/lib.rs:320:40: 320:41" } (List.cons { kind := (StatementKind.storageDead 23), span := "src/lib.rs:320:41: 320:42" } (List.cons { kind := (StatementKind.storageDead 21), span := "src/lib.rs:320:41: 320:42" } (List.cons { kind := (StatementKind.storageLive 24), span := "src/lib.rs:321:9: 321:17" } (List.cons { kind := (StatementKind.storageLive 25), span := "src/lib.rs:321:51: 325:6" } (List.cons { kind := (StatementKind.storageLive 26), span := "src/lib.rs:321:51: 325:6" } (List.cons { kind := (StatementKind.storageLive 27), span := "src/lib.rs:321:54: 321:80" } (List.cons { kind := (StatementKind.storageLive 28), span := "src/lib.rs:321:54: 321:72" } (List.cons { kind := (StatementKind.storageLive 29), span := "src/lib.rs:321:55: 321:64" } (List.cons { kind := (StatementKind.assign { local_ := 29, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:321:55: 321:64" } (List.cons { kind := (StatementKind.assign { local_ := 28, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 29, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:321:54: 321:72" } (List.cons { kind := (StatementKind.storageDead 29), span := "src/lib.rs:321:71: 321:72" } (List.cons { kind := (StatementKind.assign { local_ := 27, projection := List.nil } (Rvalue.binaryOp BinOp.eq (Operand.move { local_ := 28, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:321:54: 321:80" } List.nil))))))))))))))))))))))))))))))))))))))))))))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 27, projection := List.nil }) { branches := (List.cons (0, 3) List.nil), otherwise := 2 }), span := "src/lib.rs:321:54: 321:80" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 28), span := "src/lib.rs:321:79: 321:80" } (List.cons { kind := (StatementKind.storageLive 30), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.storageLive 31), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.storageLive 32), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.assign { local_ := 32, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 14, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.assign { local_ := 31, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 32, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 })), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.storageDead 32), span := "src/lib.rs:322:20: 322:21" } (List.cons { kind := (StatementKind.assign { local_ := 30, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 31, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.assign { local_ := 26, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 30, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 })), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.storageDead 31), span := "src/lib.rs:323:5: 323:6" } (List.cons { kind := (StatementKind.storageDead 30), span := "src/lib.rs:323:5: 323:6" } List.nil))))))))))), terminator := { kind := (TerminatorKind.goto 4), span := "src/lib.rs:321:51: 325:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 28), span := "src/lib.rs:321:79: 321:80" } (List.cons { kind := (StatementKind.storageLive 33), span := "src/lib.rs:324:9: 324:23" } (List.cons { kind := (StatementKind.assign { local_ := 33, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 19, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:324:9: 324:23" } (List.cons { kind := (StatementKind.assign { local_ := 26, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 33, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 })), span := "src/lib.rs:324:9: 324:23" } (List.cons { kind := (StatementKind.storageDead 33), span := "src/lib.rs:324:22: 324:23" } List.nil))))), terminator := { kind := (TerminatorKind.goto 4), span := "src/lib.rs:321:51: 325:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 25, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 26, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:321:51: 325:6" } (List.cons { kind := (StatementKind.assign { local_ := 24, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 25, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921")), layoutIdx := 4 })), span := "src/lib.rs:321:51: 325:6" } (List.cons { kind := (StatementKind.storageDead 27), span := "src/lib.rs:325:5: 325:6" } (List.cons { kind := (StatementKind.storageDead 25), span := "src/lib.rs:325:5: 325:6" } (List.cons { kind := (StatementKind.storageDead 26), span := "src/lib.rs:325:6: 325:7" } (List.cons { kind := (StatementKind.storageLive 34), span := "src/lib.rs:326:9: 326:21" } (List.cons { kind := (StatementKind.storageLive 35), span := "src/lib.rs:326:53: 327:39" } (List.cons { kind := (StatementKind.storageLive 36), span := "src/lib.rs:326:53: 327:39" } (List.cons { kind := (StatementKind.storageLive 37), span := "src/lib.rs:326:53: 326:62" } (List.cons { kind := (StatementKind.storageLive 38), span := "src/lib.rs:326:53: 326:62" } (List.cons { kind := (StatementKind.assign { local_ := 38, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 3, projection := List.nil })), span := "src/lib.rs:326:53: 326:62" } (List.cons { kind := (StatementKind.assign { local_ := 37, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 38, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:326:53: 326:62" } (List.cons { kind := (StatementKind.assign { local_ := 36, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 37, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt45921")), layoutIdx := 4 })), span := "src/lib.rs:326:53: 327:39" } (List.cons { kind := (StatementKind.storageDead 37), span := "src/lib.rs:326:61: 326:62" } (List.cons { kind := (StatementKind.assign { local_ := 35, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 36, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:326:53: 327:39" } (List.cons { kind := (StatementKind.assign { local_ := 34, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 35, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt45921")), layoutIdx := 4 })), span := "src/lib.rs:326:53: 327:39" } (List.cons { kind := (StatementKind.storageDead 35), span := "src/lib.rs:327:38: 327:39" } (List.cons { kind := (StatementKind.storageDead 38), span := "src/lib.rs:327:39: 327:40" } (List.cons { kind := (StatementKind.storageDead 36), span := "src/lib.rs:327:39: 327:40" } (List.cons { kind := (StatementKind.storageLive 39), span := "src/lib.rs:328:9: 328:21" } (List.cons { kind := (StatementKind.storageLive 40), span := "src/lib.rs:328:29: 328:56" } (List.cons { kind := (StatementKind.storageLive 41), span := "src/lib.rs:328:29: 328:37" } (List.cons { kind := (StatementKind.assign { local_ := 41, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 24, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:328:29: 328:37" } (List.cons { kind := (StatementKind.storageLive 42), span := "src/lib.rs:328:46: 328:55" } (List.cons { kind := (StatementKind.assign { local_ := 42, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:328:46: 328:55" } List.nil))))))))))))))))))))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__AnnealVtableTrait45921::eval_vt" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921") List.nil)), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 41, projection := List.nil }) (List.cons (Operand.move { local_ := 42, projection := List.nil }) List.nil)) { local_ := 40, projection := List.nil } (Option.some 5) UnwindAction.continue_), span := "src/lib.rs:328:29: 328:56" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 42), span := "src/lib.rs:328:55: 328:56" } (List.cons { kind := (StatementKind.storageDead 41), span := "src/lib.rs:328:55: 328:56" } (List.cons { kind := (StatementKind.storageLive 43), span := "src/lib.rs:328:59: 328:76" } (List.cons { kind := (StatementKind.storageLive 44), span := "src/lib.rs:328:59: 328:67" } (List.cons { kind := (StatementKind.assign { local_ := 44, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 24, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:328:59: 328:67" } List.nil))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__AnnealVtableTrait45921::tag_vt" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921") List.nil)), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 44, projection := List.nil }) List.nil) { local_ := 43, projection := List.nil } (Option.some 6) UnwindAction.continue_), span := "src/lib.rs:328:59: 328:76" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 44), span := "src/lib.rs:328:75: 328:76" } (List.cons { kind := (StatementKind.assign { local_ := 39, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 40, projection := List.nil }) (Operand.move { local_ := 43, projection := List.nil }))), span := "src/lib.rs:328:29: 328:76" } (List.cons { kind := (StatementKind.storageDead 43), span := "src/lib.rs:328:75: 328:76" } (List.cons { kind := (StatementKind.storageDead 40), span := "src/lib.rs:328:75: 328:76" } (List.cons { kind := (StatementKind.storageLive 45), span := "src/lib.rs:329:9: 329:22" } (List.cons { kind := (StatementKind.storageLive 46), span := "src/lib.rs:329:30: 329:42" } (List.cons { kind := (StatementKind.assign { local_ := 46, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 34, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:329:30: 329:42" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__AnnealVtableAlt45921::eval_alt" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt45921") List.nil)), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 46, projection := List.nil }) List.nil) { local_ := 45, projection := List.nil } (Option.some 7) UnwindAction.continue_), span := "src/lib.rs:329:30: 329:53" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 46), span := "src/lib.rs:329:52: 329:53" } (List.cons { kind := (StatementKind.storageLive 47), span := "src/lib.rs:330:9: 330:22" } (List.cons { kind := (StatementKind.storageLive 48), span := "src/lib.rs:330:33: 330:79" } (List.cons { kind := (StatementKind.storageLive 49), span := "src/lib.rs:330:52: 330:64" } (List.cons { kind := (StatementKind.assign { local_ := 49, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 14, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:330:52: 330:64" } (List.cons { kind := (StatementKind.storageLive 50), span := "src/lib.rs:330:66: 330:78" } (List.cons { kind := (StatementKind.assign { local_ := 50, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 34, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:330:66: 330:78" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::ptr::addr_eq" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921") (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt45921") List.nil))), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 49, projection := List.nil }) (List.cons (Operand.move { local_ := 50, projection := List.nil }) List.nil)) { local_ := 48, projection := List.nil } (Option.some 8) UnwindAction.continue_), span := "src/lib.rs:330:33: 330:79" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 48, projection := List.nil }) { branches := (List.cons (0, 10) List.nil), otherwise := 9 }), span := "src/lib.rs:330:33: 330:79" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 50), span := "src/lib.rs:330:78: 330:79" } (List.cons { kind := (StatementKind.storageDead 49), span := "src/lib.rs:330:78: 330:79" } (List.cons { kind := (StatementKind.assign { local_ := 47, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:331:9: 331:13" } List.nil))), terminator := { kind := (TerminatorKind.goto 11), span := "src/lib.rs:330:30: 334:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 50), span := "src/lib.rs:330:78: 330:79" } (List.cons { kind := (StatementKind.storageDead 49), span := "src/lib.rs:330:78: 330:79" } (List.cons { kind := (StatementKind.assign { local_ := 47, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:333:9: 333:13" } List.nil))), terminator := { kind := (TerminatorKind.goto 11), span := "src/lib.rs:330:30: 334:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 48), span := "src/lib.rs:334:5: 334:6" } (List.cons { kind := (StatementKind.storageLive 51), span := "src/lib.rs:335:9: 335:22" } (List.cons { kind := (StatementKind.storageLive 52), span := "src/lib.rs:335:33: 335:81" } (List.cons { kind := (StatementKind.storageLive 53), span := "src/lib.rs:335:52: 335:64" } (List.cons { kind := (StatementKind.assign { local_ := 53, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 14, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:335:52: 335:64" } (List.cons { kind := (StatementKind.storageLive 54), span := "src/lib.rs:335:66: 335:80" } (List.cons { kind := (StatementKind.assign { local_ := 54, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 19, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:335:66: 335:80" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::ptr::addr_eq" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921") (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait45921") List.nil))), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 53, projection := List.nil }) (List.cons (Operand.move { local_ := 54, projection := List.nil }) List.nil)) { local_ := 52, projection := List.nil } (Option.some 12) UnwindAction.continue_), span := "src/lib.rs:335:33: 335:81" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 52, projection := List.nil }) { branches := (List.cons (0, 14) List.nil), otherwise := 13 }), span := "src/lib.rs:335:33: 335:81" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 54), span := "src/lib.rs:335:80: 335:81" } (List.cons { kind := (StatementKind.storageDead 53), span := "src/lib.rs:335:80: 335:81" } (List.cons { kind := (StatementKind.assign { local_ := 51, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:336:9: 336:13" } List.nil))), terminator := { kind := (TerminatorKind.goto 15), span := "src/lib.rs:335:30: 339:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 54), span := "src/lib.rs:335:80: 335:81" } (List.cons { kind := (StatementKind.storageDead 53), span := "src/lib.rs:335:80: 335:81" } (List.cons { kind := (StatementKind.assign { local_ := 51, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }))), span := "src/lib.rs:338:9: 338:13" } List.nil))), terminator := { kind := (TerminatorKind.goto 15), span := "src/lib.rs:335:30: 339:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 52), span := "src/lib.rs:339:5: 339:6" } (List.cons { kind := (StatementKind.storageLive 55), span := "src/lib.rs:340:5: 340:59" } (List.cons { kind := (StatementKind.storageLive 56), span := "src/lib.rs:340:5: 340:43" } (List.cons { kind := (StatementKind.storageLive 57), span := "src/lib.rs:340:5: 340:17" } (List.cons { kind := (StatementKind.assign { local_ := 57, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 39, projection := List.nil }))), span := "src/lib.rs:340:5: 340:17" } (List.cons { kind := (StatementKind.storageLive 58), span := "src/lib.rs:340:20: 340:43" } (List.cons { kind := (StatementKind.storageLive 59), span := "src/lib.rs:340:21: 340:34" } (List.cons { kind := (StatementKind.assign { local_ := 59, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 45, projection := List.nil }))), span := "src/lib.rs:340:21: 340:34" } (List.cons { kind := (StatementKind.assign { local_ := 60, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:340:20: 340:43" } List.nil))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 60, projection := List.nil }) true 16 UnwindAction.continue_), span := "src/lib.rs:340:20: 340:43" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 58, projection := List.nil } (Rvalue.binaryOp BinOp.shl (Operand.move { local_ := 59, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }))), span := "src/lib.rs:340:20: 340:43" } (List.cons { kind := (StatementKind.storageDead 59), span := "src/lib.rs:340:42: 340:43" } (List.cons { kind := (StatementKind.assign { local_ := 56, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 57, projection := List.nil }) (Operand.move { local_ := 58, projection := List.nil }))), span := "src/lib.rs:340:5: 340:43" } (List.cons { kind := (StatementKind.storageDead 58), span := "src/lib.rs:340:42: 340:43" } (List.cons { kind := (StatementKind.storageDead 57), span := "src/lib.rs:340:42: 340:43" } (List.cons { kind := (StatementKind.storageLive 61), span := "src/lib.rs:340:46: 340:59" } (List.cons { kind := (StatementKind.assign { local_ := 61, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 47, projection := List.nil }))), span := "src/lib.rs:340:46: 340:59" } (List.cons { kind := (StatementKind.assign { local_ := 55, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 56, projection := List.nil }) (Operand.move { local_ := 61, projection := List.nil }))), span := "src/lib.rs:340:5: 340:59" } (List.cons { kind := (StatementKind.storageDead 61), span := "src/lib.rs:340:58: 340:59" } (List.cons { kind := (StatementKind.storageDead 56), span := "src/lib.rs:340:58: 340:59" } (List.cons { kind := (StatementKind.storageLive 62), span := "src/lib.rs:340:62: 340:75" } (List.cons { kind := (StatementKind.assign { local_ := 62, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 51, projection := List.nil }))), span := "src/lib.rs:340:62: 340:75" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 55, projection := List.nil }) (Operand.move { local_ := 62, projection := List.nil }))), span := "src/lib.rs:340:5: 340:75" } (List.cons { kind := (StatementKind.storageDead 62), span := "src/lib.rs:340:74: 340:75" } (List.cons { kind := (StatementKind.storageDead 55), span := "src/lib.rs:340:74: 340:75" } (List.cons { kind := (StatementKind.storageDead 51), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 47), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 45), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 39), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 34), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 24), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 19), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 14), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:341:1: 341:2" } List.nil))))))))))))))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:341:2: 341:2" }, isCleanup := false } List.nil))))))))))))))))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0001.Driver

namespace F0001.RecvTraitEvalVt

/-! Captured `miri_diff_corpus` item `__AnnealVtableReceiver45921_as___AnnealVtableTrait45921_eval_vt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_3); StorageLive(_4); _4 = copy _2; StorageLive(_5); _5 = copy ((*_1).0: u32); _3 = BitXor(move _4, move _5); StorageDead(_5); StorageDead(_4); _0 = BitAnd(move _3, const 65535_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableTrait45921>::eval_vt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableTrait45921::eval_vt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableTrait45921>::eval_vt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", predicateKey := "miri_diff_corpus::__AnnealVtableAlt45921", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt45921"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", predicateKey := "miri_diff_corpus::__AnnealVtableTrait45921", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait45921"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableAlt45921>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver45921 as __AnnealVtableTrait45921>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver45921 as __AnnealVtableTrait45921>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableTrait45921>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableTrait45921>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt45921::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait45921::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait45921::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", slotIdx := 4 } List.nil))),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:289:9: 289:24" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:289:10: 289:11" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:289:10: 289:11" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:289:14: 289:23" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:289:14: 289:23" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 4, projection := List.nil }) (Operand.move { local_ := 5, projection := List.nil }))), span := "src/lib.rs:289:9: 289:24" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:289:23: 289:24" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:289:23: 289:24" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 65535, sizeBytes := 4 })) }))), span := "src/lib.rs:289:9: 289:36" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:289:35: 289:36" } List.nil)))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:290:6: 290:6" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0001.RecvTraitEvalVt

namespace F0001.RecvTraitTagVt

/-! Captured `miri_diff_corpus` item `__AnnealVtableReceiver45921_as___AnnealVtableTrait45921_tag_vt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = copy ((*_1).0: u32); _2 = BitAnd(move _3, const 63_u32); StorageDead(_3); _0 = BitXor(move _2, const 21_u32); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableTrait45921>::tag_vt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableTrait45921::tag_vt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableTrait45921>::tag_vt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", predicateKey := "miri_diff_corpus::__AnnealVtableAlt45921", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt45921"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", predicateKey := "miri_diff_corpus::__AnnealVtableTrait45921", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait45921"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableAlt45921>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver45921 as __AnnealVtableTrait45921>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver45921 as __AnnealVtableTrait45921>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableTrait45921>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableTrait45921>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt45921::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait45921::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait45921::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", slotIdx := 4 } List.nil))),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:292:9: 292:30" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:292:10: 292:19" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:292:10: 292:19" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 63, sizeBytes := 4 })) }))), span := "src/lib.rs:292:9: 292:30" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:292:29: 292:30" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 2, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 21, sizeBytes := 4 })) }))), span := "src/lib.rs:292:9: 292:40" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:292:39: 292:40" } List.nil))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:293:6: 293:6" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0001.RecvTraitTagVt

namespace F0001.RecvAltEvalAlt

/-! Captured `miri_diff_corpus` item `__AnnealVtableReceiver45921_as___AnnealVtableAlt45921_eval_alt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))) }

-- bb0: StorageLive(_2); _2 = copy ((*_1).0: u32); _3 = Lt(const 1_u32, const 32_u32); assert(move _3, "attempt to shift right by `{}`, which would overflow", const 1_u32) -> [success: bb1, unwind continue]
-- bb1: _0 = Shr(move _2, const 1_u32); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableAlt45921>::eval_alt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableAlt45921::eval_alt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableAlt45921>::eval_alt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", predicateKey := "miri_diff_corpus::__AnnealVtableAlt45921", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt45921"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", predicateKey := "miri_diff_corpus::__AnnealVtableTrait45921", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait45921"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableAlt45921>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver45921 as __AnnealVtableTrait45921>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver45921 as __AnnealVtableTrait45921>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableTrait45921>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableTrait45921>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt45921::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait45921::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait45921::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", slotIdx := 4 } List.nil))),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:305:9: 305:18" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:305:9: 305:18" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:305:9: 305:26" } List.nil)))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 3, projection := List.nil }) true 1 UnwindAction.continue_), span := "src/lib.rs:305:9: 305:26" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.shr (Operand.move { local_ := 2, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:305:9: 305:26" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:305:25: 305:26" } List.nil)), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:306:6: 306:6" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0001.RecvAltEvalAlt

namespace F0001.AltRecvTraitEvalVt

/-! Captured `miri_diff_corpus` item `__AnnealVtableAltReceiver45921_as___AnnealVtableTrait45921_eval_vt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 0 List.nil)) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))) }

-- bb0: StorageLive(_3); StorageLive(_4); StorageLive(_5); StorageLive(_6); _6 = copy _2; _7 = Lt(const 1_u32, const 32_u32); assert(move _7, "attempt to shift right by `{}`, which would overflow", const 1_u32) -> [success: bb1, unwind continue]
-- bb1: _5 = Shr(move _6, const 1_u32); StorageDead(_6); StorageLive(_8); _8 = copy ((*_1).0: u32); _4 = BitXor(move _5, move _8); StorageDead(_8); StorageDead(_5); StorageLive(_9); _9 = copy ((*_1).1: u32); _3 = BitXor(move _4, move _9); StorageDead(_9); StorageDead(_4); _0 = BitAnd(move _3, const 65535_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableAltReceiver45921 as __AnnealVtableTrait45921>::eval_vt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableTrait45921::eval_vt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver45921" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableAltReceiver45921 as __AnnealVtableTrait45921>::eval_vt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", predicateKey := "miri_diff_corpus::__AnnealVtableAlt45921", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt45921"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", predicateKey := "miri_diff_corpus::__AnnealVtableTrait45921", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait45921"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableAlt45921>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver45921 as __AnnealVtableTrait45921>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver45921 as __AnnealVtableTrait45921>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableTrait45921>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableTrait45921>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt45921::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait45921::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait45921::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", slotIdx := 4 } List.nil))),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver45921" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 7), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:297:9: 297:45" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:297:10: 297:32" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:297:10: 297:21" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:297:11: 297:12" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:297:11: 297:12" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:297:10: 297:21" } List.nil))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 7, projection := List.nil }) true 1 UnwindAction.continue_), span := "src/lib.rs:297:10: 297:21" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.binaryOp BinOp.shr (Operand.move { local_ := 6, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:297:10: 297:21" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:297:20: 297:21" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:297:24: 297:32" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:297:24: 297:32" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 5, projection := List.nil }) (Operand.move { local_ := 8, projection := List.nil }))), span := "src/lib.rs:297:10: 297:32" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:297:31: 297:32" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:297:31: 297:32" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:297:35: 297:44" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 1 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:297:35: 297:44" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 4, projection := List.nil }) (Operand.move { local_ := 9, projection := List.nil }))), span := "src/lib.rs:297:9: 297:45" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:297:44: 297:45" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:297:44: 297:45" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 65535, sizeBytes := 4 })) }))), span := "src/lib.rs:297:9: 297:57" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:297:56: 297:57" } List.nil)))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:298:6: 298:6" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0001.AltRecvTraitEvalVt

namespace F0001.AltRecvTraitTagVt

/-! Captured `miri_diff_corpus` item `__AnnealVtableAltReceiver45921_as___AnnealVtableTrait45921_tag_vt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 0 List.nil)) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_2); StorageLive(_3); StorageLive(_4); _4 = copy ((*_1).0: u32); StorageLive(_5); _5 = copy ((*_1).1: u32); _3 = BitXor(move _4, move _5); StorageDead(_5); StorageDead(_4); _2 = BitAnd(move _3, const 63_u32); StorageDead(_3); _0 = BitXor(move _2, const 42_u32); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableAltReceiver45921 as __AnnealVtableTrait45921>::tag_vt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableTrait45921::tag_vt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver45921" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableAltReceiver45921 as __AnnealVtableTrait45921>::tag_vt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", predicateKey := "miri_diff_corpus::__AnnealVtableAlt45921", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt45921"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", predicateKey := "miri_diff_corpus::__AnnealVtableTrait45921", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait45921"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableAlt45921>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver45921 as __AnnealVtableTrait45921>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver45921 as __AnnealVtableTrait45921>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver45921" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableTrait45921>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver45921 as __AnnealVtableTrait45921>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt45921::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt45921", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait45921::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait45921::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait45921", slotIdx := 4 } List.nil))),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver45921" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:300:9: 300:43" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:300:10: 300:32" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:300:11: 300:19" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:300:11: 300:19" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:300:22: 300:31" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 1 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:300:22: 300:31" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 4, projection := List.nil }) (Operand.move { local_ := 5, projection := List.nil }))), span := "src/lib.rs:300:10: 300:32" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:300:31: 300:32" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:300:31: 300:32" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 63, sizeBytes := 4 })) }))), span := "src/lib.rs:300:9: 300:43" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:300:42: 300:43" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 2, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 42, sizeBytes := 4 })) }))), span := "src/lib.rs:300:9: 300:53" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:300:52: 300:53" } List.nil))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:301:6: 301:6" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0001.AltRecvTraitTagVt

/-- Linked callee table of `finding_0001`: the driver and the 5 trait-method impls. -/
def F0001.linkedCallees : List CapturedMir :=
  [F0001.Driver.body, F0001.RecvTraitEvalVt.body, F0001.RecvTraitTagVt.body, F0001.RecvAltEvalAlt.body, F0001.AltRecvTraitEvalVt.body, F0001.AltRecvTraitTagVt.body]

set_option maxRecDepth 1000000 in
/-- Campaign #22 `finding_0001` end-to-end agreement with Miri (`MIRI_PASS:scalar:182:4`):
`miri_diff_corpus::pass_bitwise_and_or_xor_not__b8_c9` returns `182_u32` with the driver and the 5 trait-method
impls linked. -/
theorem F0001.miri_agreement :
    evalMirDiffTagBounded 512 F0001.Outer.body
      (initMachineStateWithMemoryAndCallees F0001.Outer.body [] emptyMemory F0001.linkedCallees) =
      .normalScalar 182 4 := by
  rfl

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0001`, only the driver linked (the 5 trait-method impls are absent)): the first virtual call resolves through the captured vtable to a method `DefPath` with no linked body, so the run stops at that `externalCall` (never a value).
Fault site: `src/lib.rs:328:29: 328:56`. -/
theorem F0001.control_noImpls :
    runC22 F0001.Outer.body [F0001.Driver.body] =
      .externalCall "miri_diff_corpus::<__AnnealVtableAltReceiver45921 as __AnnealVtableTrait45921>::eval_vt" ∧
    probeC22 F0001.Outer.body [F0001.Driver.body] =
      (.externalCall "miri_diff_corpus::<__AnnealVtableAltReceiver45921 as __AnnealVtableTrait45921>::eval_vt", "src/lib.rs:328:29: 328:56") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0001`, nothing linked): the outer function's call to the unlinked driver escapes as `externalCall` (never a value).
Fault site: `src/lib.rs:350:32: 350:87`. -/
theorem F0001.control_noDriver :
    runC22 F0001.Outer.body [] =
      .externalCall "miri_diff_corpus::__anneal_vt_driver_45921" ∧
    probeC22 F0001.Outer.body [] =
      (.externalCall "miri_diff_corpus::__anneal_vt_driver_45921", "src/lib.rs:350:32: 350:87") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0001`, `vtables` stripped from the outer body and from every linked body): the first `&T as &dyn Trait` unsizing finds no usable captured `(T, dyn Trait)` vtable (missing table, missing record, or `bodyVTablesConsistent` failure) and fails closed with `.unsupported` at that statement (never `.ub`, never a value).
Fault site: `src/lib.rs:317:55: 318:41`. -/
theorem F0001.control_stripped :
    runC22 (stripVTables F0001.Outer.body) (F0001.linkedCallees.map stripVTables) =
      .unsupported ∧
    probeC22 (stripVTables F0001.Outer.body) (F0001.linkedCallees.map stripVTables) =
      (.unsupported, "src/lib.rs:317:55: 318:41") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0001`, `vtables` stripped from every linked body (outer body intact)): the first `&T as &dyn Trait` unsizing finds no usable captured `(T, dyn Trait)` vtable (missing table, missing record, or `bodyVTablesConsistent` failure) and fails closed with `.unsupported` at that statement (never `.ub`, never a value).
Fault site: `src/lib.rs:317:55: 318:41`. -/
theorem F0001.control_strippedLinked :
    runC22 F0001.Outer.body (F0001.linkedCallees.map stripVTables) =
      .unsupported ∧
    probeC22 F0001.Outer.body (F0001.linkedCallees.map stripVTables) =
      (.unsupported, "src/lib.rs:317:55: 318:41") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0001`, unit-consistent forgery `forgeNonMethodSlot` applied to every body): the virtual call reads a vtable slot that is not a method (`.size` header slot, or past the end of the table): Miri's `get_vtable_entries`/`VtblEntry` dispatch raises UB (\"`dyn` call trying to call something that is not a method\" / out-of-bounds vtable index), and the TCB faults `.ub` at that call.
Fault site: `src/lib.rs:328:29: 328:56`. -/
theorem F0001.control_nonMethodSlot :
    runC22 (mapVTables forgeNonMethodSlot F0001.Outer.body) (F0001.linkedCallees.map (mapVTables forgeNonMethodSlot)) =
      .ub ∧
    probeC22 (mapVTables forgeNonMethodSlot F0001.Outer.body) (F0001.linkedCallees.map (mapVTables forgeNonMethodSlot)) =
      (.ub, "src/lib.rs:328:29: 328:56") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0001`, unit-consistent forgery `forgeTruncatedSlots` applied to every body): the virtual call reads a vtable slot that is not a method (`.size` header slot, or past the end of the table): Miri's `get_vtable_entries`/`VtblEntry` dispatch raises UB (\"`dyn` call trying to call something that is not a method\" / out-of-bounds vtable index), and the TCB faults `.ub` at that call.
Fault site: `src/lib.rs:328:59: 328:76`. -/
theorem F0001.control_truncatedSlots :
    runC22 (mapVTables forgeTruncatedSlots F0001.Outer.body) (F0001.linkedCallees.map (mapVTables forgeTruncatedSlots)) =
      .ub ∧
    probeC22 (mapVTables forgeTruncatedSlots F0001.Outer.body) (F0001.linkedCallees.map (mapVTables forgeTruncatedSlots)) =
      (.ub, "src/lib.rs:328:59: 328:76") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0001`, unit-consistent forgery `forgeWrongDynKey` applied to every body): the first `&T as &dyn Trait` unsizing finds no usable captured `(T, dyn Trait)` vtable (missing table, missing record, or `bodyVTablesConsistent` failure) and fails closed with `.unsupported` at that statement (never `.ub`, never a value).
Fault site: `src/lib.rs:317:55: 318:41`. -/
theorem F0001.control_wrongDynKey :
    runC22 (mapVTables forgeWrongDynKey F0001.Outer.body) (F0001.linkedCallees.map (mapVTables forgeWrongDynKey)) =
      .unsupported ∧
    probeC22 (mapVTables forgeWrongDynKey F0001.Outer.body) (F0001.linkedCallees.map (mapVTables forgeWrongDynKey)) =
      (.unsupported, "src/lib.rs:317:55: 318:41") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0001`, `forgeNonMethodSlot` applied to the driver's table only (linked bodies disagree)): the first `&T as &dyn Trait` unsizing finds no usable captured `(T, dyn Trait)` vtable (missing table, missing record, or `bodyVTablesConsistent` failure) and fails closed with `.unsupported` at that statement (never `.ub`, never a value).
Fault site: `src/lib.rs:317:55: 318:41`. -/
theorem F0001.control_inconsistent :
    runC22 F0001.Outer.body (mapVTables forgeNonMethodSlot F0001.Driver.body :: F0001.linkedCallees.drop 1) =
      .unsupported ∧
    probeC22 F0001.Outer.body (mapVTables forgeNonMethodSlot F0001.Driver.body :: F0001.linkedCallees.drop 1) =
      (.unsupported, "src/lib.rs:317:55: 318:41") :=
  ⟨by rfl, by rfl⟩

/-! ### Campaign #22 `finding_0002`: `miri_diff_corpus::pass_subslice_pattern_extract__b17_c23` (Miri: `MIRI_PASS:scalar:67:4`).

Verbatim `layouts`/`body` definitions emitted by HEAD `anneal-rustc-capture` (`Runtime(PostCleanup)` MIR,
nightly-2026-06-01, `-Zmir-opt-level=0 -C debug-assertions=off -C overflow-checks=on`). -/

namespace F0002.Outer

/-! Captured `miri_diff_corpus` item `pass_subslice_pattern_extract__b17_c23`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 16 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.array { bytes := 4 } 4), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.array { bytes := 4 } 2), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 4 List.nil)) } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))))) }

-- bb0: StorageLive(_1); _1 = [const 3_u32, const 6_u32, const 9_u32, const 12_u32]; StorageLive(_2); _2 = copy _1[0 of 4]; StorageLive(_3); _3 = copy _1[1..3]; StorageLive(_4); _4 = copy _1[3 of 4]; StorageLive(_5); StorageLive(_6); StorageLive(_7); StorageLive(_8); _8 = copy _2; StorageLive(_9); StorageLive(_10); _10 = const 0_usize; _11 = Lt(copy _10, const 2_usize); assert(move _11, "index out of bounds: the length is {} but the index is {}", const 2_usize, copy _10) -> [success: bb1, unwind continue]
-- bb1: _9 = copy _3[_10]; _12 = AddWithOverflow(copy _8, copy _9); assert(!move (_12.1: bool), "attempt to compute `{} + {}`, which would overflow", move _8, move _9) -> [success: bb2, unwind continue]
-- bb2: _7 = move (_12.0: u32); StorageDead(_9); StorageDead(_8); StorageLive(_13); StorageLive(_14); _14 = const 1_usize; _15 = Lt(copy _14, const 2_usize); assert(move _15, "index out of bounds: the length is {} but the index is {}", const 2_usize, copy _14) -> [success: bb3, unwind continue]
-- bb3: _13 = copy _3[_14]; _16 = AddWithOverflow(copy _7, copy _13); assert(!move (_16.1: bool), "attempt to compute `{} + {}`, which would overflow", move _7, move _13) -> [success: bb4, unwind continue]
-- bb4: _6 = move (_16.0: u32); StorageDead(_13); StorageDead(_7); StorageLive(_17); _17 = copy _4; _18 = AddWithOverflow(copy _6, copy _17); assert(!move (_18.1: bool), "attempt to compute `{} + {}`, which would overflow", move _6, move _17) -> [success: bb5, unwind continue]
-- bb5: _5 = move (_18.0: u32); StorageDead(_17); StorageDead(_6); StorageDead(_14); StorageDead(_10); StorageLive(_19); _19 = __anneal_vt_driver_31616(const 9_u32, const 48_u32) -> [return: bb6, unwind continue]
-- bb6: StorageLive(_20); _20 = copy _5; StorageLive(_21); _21 = copy _19; _0 = BitXor(move _20, move _21); StorageDead(_21); StorageDead(_20); StorageDead(_19); StorageDead(_5); StorageDead(_4); StorageDead(_3); StorageDead(_2); StorageDead(_1); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::pass_subslice_pattern_extract__b17_c23",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", predicateKey := "miri_diff_corpus::__AnnealVtableAlt31616", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt31616"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", predicateKey := "miri_diff_corpus::__AnnealVtableTrait31616", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait31616"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableAlt31616>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver31616 as __AnnealVtableTrait31616>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver31616 as __AnnealVtableTrait31616>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableTrait31616>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableTrait31616>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt31616::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait31616::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait31616::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", slotIdx := 4 } List.nil))),
    argCount := 0,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.array (RigidTy.uint UintTy.u32) 4), layoutIdx := 1 }, debugName := (Option.some "arr") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "first") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.array (RigidTy.uint UintTy.u32) 2), layoutIdx := 2 }, debugName := (Option.some "middle") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "last") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__tail___miri_vt_31616") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) (List.cons RigidTy.bool List.nil))), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) (List.cons RigidTy.bool List.nil))), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) (List.cons RigidTy.bool List.nil))), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__miri_vt_31616") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))))))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 11), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 12), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 15), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 16), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 18), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 1), span := "src/lib.rs:344:9: 344:12" } (List.cons { kind := (StatementKind.assign { local_ := 1, projection := List.nil } (Rvalue.aggregate (AggregateKind.array { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 3, sizeBytes := 4 })) }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 6, sizeBytes := 4 })) }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 9, sizeBytes := 4 })) }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 12, sizeBytes := 4 })) }) List.nil)))))), span := "src/lib.rs:344:25: 344:38" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:345:10: 345:15" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons (ProjectionElem.constantIndex 0 4 false) List.nil) }))), span := "src/lib.rs:345:10: 345:15" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:345:17: 345:23" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons (ProjectionElem.subslice 1 3 false) List.nil) }))), span := "src/lib.rs:345:17: 345:23" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:345:30: 345:34" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons (ProjectionElem.constantIndex 3 4 false) List.nil) }))), span := "src/lib.rs:345:30: 345:34" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:346:9: 346:31" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:346:39: 346:68" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:346:39: 346:56" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:346:39: 346:44" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:346:39: 346:44" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:346:47: 346:56" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:346:54: 346:55" } (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 8 })) }))), span := "src/lib.rs:346:54: 346:55" } (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.copy { local_ := 10, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 8 })) }))), span := "src/lib.rs:346:47: 346:56" } List.nil)))))))))))))))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 11, projection := List.nil }) true 1 UnwindAction.continue_), span := "src/lib.rs:346:47: 346:56" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := (List.cons (ProjectionElem.index 10) List.nil) }))), span := "src/lib.rs:346:47: 346:56" } (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.binaryOp BinOp.addWithOverflow (Operand.copy { local_ := 8, projection := List.nil }) (Operand.copy { local_ := 9, projection := List.nil }))), span := "src/lib.rs:346:39: 346:56" } List.nil)), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 12, projection := (List.cons (ProjectionElem.field 1 { kind := RigidTy.bool, layoutIdx := 4 }) List.nil) }) false 2 UnwindAction.continue_), span := "src/lib.rs:346:39: 346:56" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.move { local_ := 12, projection := (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil) }))), span := "src/lib.rs:346:39: 346:56" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:346:55: 346:56" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:346:55: 346:56" } (List.cons { kind := (StatementKind.storageLive 13), span := "src/lib.rs:346:59: 346:68" } (List.cons { kind := (StatementKind.storageLive 14), span := "src/lib.rs:346:66: 346:67" } (List.cons { kind := (StatementKind.assign { local_ := 14, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 8 })) }))), span := "src/lib.rs:346:66: 346:67" } (List.cons { kind := (StatementKind.assign { local_ := 15, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.copy { local_ := 14, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 8 })) }))), span := "src/lib.rs:346:59: 346:68" } List.nil))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 15, projection := List.nil }) true 3 UnwindAction.continue_), span := "src/lib.rs:346:59: 346:68" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 13, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := (List.cons (ProjectionElem.index 14) List.nil) }))), span := "src/lib.rs:346:59: 346:68" } (List.cons { kind := (StatementKind.assign { local_ := 16, projection := List.nil } (Rvalue.binaryOp BinOp.addWithOverflow (Operand.copy { local_ := 7, projection := List.nil }) (Operand.copy { local_ := 13, projection := List.nil }))), span := "src/lib.rs:346:39: 346:68" } List.nil)), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 16, projection := (List.cons (ProjectionElem.field 1 { kind := RigidTy.bool, layoutIdx := 4 }) List.nil) }) false 4 UnwindAction.continue_), span := "src/lib.rs:346:39: 346:68" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.move { local_ := 16, projection := (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil) }))), span := "src/lib.rs:346:39: 346:68" } (List.cons { kind := (StatementKind.storageDead 13), span := "src/lib.rs:346:67: 346:68" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:346:67: 346:68" } (List.cons { kind := (StatementKind.storageLive 17), span := "src/lib.rs:346:71: 346:75" } (List.cons { kind := (StatementKind.assign { local_ := 17, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := List.nil }))), span := "src/lib.rs:346:71: 346:75" } (List.cons { kind := (StatementKind.assign { local_ := 18, projection := List.nil } (Rvalue.binaryOp BinOp.addWithOverflow (Operand.copy { local_ := 6, projection := List.nil }) (Operand.copy { local_ := 17, projection := List.nil }))), span := "src/lib.rs:346:39: 346:75" } List.nil)))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 18, projection := (List.cons (ProjectionElem.field 1 { kind := RigidTy.bool, layoutIdx := 4 }) List.nil) }) false 5 UnwindAction.continue_), span := "src/lib.rs:346:39: 346:75" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.move { local_ := 18, projection := (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil) }))), span := "src/lib.rs:346:39: 346:75" } (List.cons { kind := (StatementKind.storageDead 17), span := "src/lib.rs:346:74: 346:75" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:346:74: 346:75" } (List.cons { kind := (StatementKind.storageDead 14), span := "src/lib.rs:346:75: 346:76" } (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:346:75: 346:76" } (List.cons { kind := (StatementKind.storageLive 19), span := "src/lib.rs:347:9: 347:24" } List.nil)))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__anneal_vt_driver_31616" List.nil), layoutIdx := 6 }, val := ConstValue.zeroSized }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 9, sizeBytes := 4 })) }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 48, sizeBytes := 4 })) }) List.nil)) { local_ := 19, projection := List.nil } (Option.some 6) UnwindAction.continue_), span := "src/lib.rs:347:32: 347:69" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 20), span := "src/lib.rs:348:5: 348:27" } (List.cons { kind := (StatementKind.assign { local_ := 20, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 5, projection := List.nil }))), span := "src/lib.rs:348:5: 348:27" } (List.cons { kind := (StatementKind.storageLive 21), span := "src/lib.rs:348:30: 348:54" } (List.cons { kind := (StatementKind.assign { local_ := 21, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 19, projection := List.nil }))), span := "src/lib.rs:348:31: 348:46" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 20, projection := List.nil }) (Operand.move { local_ := 21, projection := List.nil }))), span := "src/lib.rs:348:5: 348:54" } (List.cons { kind := (StatementKind.storageDead 21), span := "src/lib.rs:348:53: 348:54" } (List.cons { kind := (StatementKind.storageDead 20), span := "src/lib.rs:348:53: 348:54" } (List.cons { kind := (StatementKind.storageDead 19), span := "src/lib.rs:349:1: 349:2" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:349:1: 349:2" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:349:1: 349:2" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:349:1: 349:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:349:1: 349:2" } (List.cons { kind := (StatementKind.storageDead 1), span := "src/lib.rs:349:1: 349:2" } List.nil))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:349:2: 349:2" }, isCleanup := false } List.nil))))))),
    fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0002.Outer

namespace F0002.Driver

/-! Captured `miri_diff_corpus` item `__anneal_vt_driver_31616`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 0 List.nil)) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))))))) }

-- bb0: StorageLive(_3); StorageLive(_4); StorageLive(_5); _5 = copy _2; _4 = BitXor(move _5, const 9_u32); StorageDead(_5); _3 = __AnnealVtableReceiver31616 { bias: move _4 }; StorageDead(_4); StorageLive(_6); StorageLive(_7); StorageLive(_8); StorageLive(_9); _9 = copy _1; _8 = BitAnd(move _9, const 255_u32); StorageDead(_9); _7 = BitXor(move _8, const 9_u32); StorageDead(_8); StorageLive(_10); StorageLive(_11); StorageLive(_12); _12 = copy _2; _13 = Lt(const 1_u32, const 32_u32); assert(move _13, "attempt to shift right by `{}`, which would overflow", const 1_u32) -> [success: bb1, unwind continue]
-- bb1: _11 = Shr(move _12, const 1_u32); StorageDead(_12); _10 = BitXor(move _11, const 9_u32); StorageDead(_11); _6 = __AnnealVtableAltReceiver31616 { pad: move _7, bias: move _10 }; StorageDead(_10); StorageDead(_7); StorageLive(_14); StorageLive(_15); StorageLive(_16); StorageLive(_17); StorageLive(_18); _18 = &_3; _17 = &(*_18); _16 = move _17 as &dyn __AnnealVtableTrait31616 (PointerCoercion(Unsize, AsCast)); StorageDead(_17); _15 = &(*_16); _14 = move _15 as &dyn __AnnealVtableTrait31616 (PointerCoercion(Unsize, Implicit)); StorageDead(_15); StorageDead(_18); StorageDead(_16); StorageLive(_19); StorageLive(_20); StorageLive(_21); StorageLive(_22); StorageLive(_23); _23 = &_6; _22 = &(*_23); _21 = move _22 as &dyn __AnnealVtableTrait31616 (PointerCoercion(Unsize, AsCast)); StorageDead(_22); _20 = &(*_21); _19 = move _20 as &dyn __AnnealVtableTrait31616 (PointerCoercion(Unsize, Implicit)); StorageDead(_20); StorageDead(_23); StorageDead(_21); StorageLive(_24); StorageLive(_25); StorageLive(_26); StorageLive(_27); StorageLive(_28); StorageLive(_29); _29 = copy _1; _28 = BitAnd(move _29, const 1_u32); StorageDead(_29); _27 = Eq(move _28, const 0_u32); switchInt(move _27) -> [0: bb3, otherwise: bb2]
-- bb2: StorageDead(_28); StorageLive(_30); StorageLive(_31); StorageLive(_32); _32 = &(*_14); _31 = move _32 as &dyn __AnnealVtableTrait31616 (PointerCoercion(Unsize, Implicit)); StorageDead(_32); _30 = &(*_31); _26 = move _30 as &dyn __AnnealVtableTrait31616 (PointerCoercion(Unsize, Implicit)); StorageDead(_31); StorageDead(_30); goto -> bb4
-- bb3: StorageDead(_28); StorageLive(_33); _33 = &(*_19); _26 = move _33 as &dyn __AnnealVtableTrait31616 (PointerCoercion(Unsize, Implicit)); StorageDead(_33); goto -> bb4
-- bb4: _25 = &(*_26); _24 = move _25 as &dyn __AnnealVtableTrait31616 (PointerCoercion(Unsize, Implicit)); StorageDead(_27); StorageDead(_25); StorageDead(_26); StorageLive(_34); StorageLive(_35); StorageLive(_36); StorageLive(_37); StorageLive(_38); _38 = &_3; _37 = &(*_38); _36 = move _37 as &dyn __AnnealVtableAlt31616 (PointerCoercion(Unsize, AsCast)); StorageDead(_37); _35 = &(*_36); _34 = move _35 as &dyn __AnnealVtableAlt31616 (PointerCoercion(Unsize, Implicit)); StorageDead(_35); StorageDead(_38); StorageDead(_36); StorageLive(_39); StorageLive(_40); StorageLive(_41); _41 = &(*_24); StorageLive(_42); _42 = copy _1; _40 = <dyn __AnnealVtableTrait31616 as __AnnealVtableTrait31616>::eval_vt(move _41, move _42) -> [return: bb5, unwind continue]
-- bb5: StorageDead(_42); StorageDead(_41); StorageLive(_43); StorageLive(_44); _44 = &(*_24); _43 = <dyn __AnnealVtableTrait31616 as __AnnealVtableTrait31616>::tag_vt(move _44) -> [return: bb6, unwind continue]
-- bb6: StorageDead(_44); _39 = BitXor(move _40, move _43); StorageDead(_43); StorageDead(_40); StorageLive(_45); StorageLive(_46); _46 = &(*_34); _45 = <dyn __AnnealVtableAlt31616 as __AnnealVtableAlt31616>::eval_alt(move _46) -> [return: bb7, unwind continue]
-- bb7: StorageDead(_46); StorageLive(_47); StorageLive(_48); StorageLive(_49); _49 = &raw const (*_14); StorageLive(_50); _50 = &raw const (*_34); _48 = core::ptr::addr_eq::<dyn __AnnealVtableTrait31616, dyn __AnnealVtableAlt31616>(move _49, move _50) -> [return: bb8, unwind continue]
-- bb8: switchInt(move _48) -> [0: bb10, otherwise: bb9]
-- bb9: StorageDead(_50); StorageDead(_49); _47 = const 1_u32; goto -> bb11
-- bb10: StorageDead(_50); StorageDead(_49); _47 = const 0_u32; goto -> bb11
-- bb11: StorageDead(_48); StorageLive(_51); StorageLive(_52); StorageLive(_53); _53 = &raw const (*_14); StorageLive(_54); _54 = &raw const (*_19); _52 = core::ptr::addr_eq::<dyn __AnnealVtableTrait31616, dyn __AnnealVtableTrait31616>(move _53, move _54) -> [return: bb12, unwind continue]
-- bb12: switchInt(move _52) -> [0: bb14, otherwise: bb13]
-- bb13: StorageDead(_54); StorageDead(_53); _51 = const 0_u32; goto -> bb15
-- bb14: StorageDead(_54); StorageDead(_53); _51 = const 2_u32; goto -> bb15
-- bb15: StorageDead(_52); StorageLive(_55); StorageLive(_56); StorageLive(_57); _57 = copy _39; StorageLive(_58); StorageLive(_59); _59 = copy _45; _60 = Lt(const 2_u32, const 32_u32); assert(move _60, "attempt to shift left by `{}`, which would overflow", const 2_u32) -> [success: bb16, unwind continue]
-- bb16: _58 = Shl(move _59, const 2_u32); StorageDead(_59); _56 = BitXor(move _57, move _58); StorageDead(_58); StorageDead(_57); StorageLive(_61); _61 = copy _47; _55 = BitXor(move _56, move _61); StorageDead(_61); StorageDead(_56); StorageLive(_62); _62 = copy _51; _0 = BitXor(move _55, move _62); StorageDead(_62); StorageDead(_55); StorageDead(_51); StorageDead(_47); StorageDead(_45); StorageDead(_39); StorageDead(_34); StorageDead(_24); StorageDead(_19); StorageDead(_14); StorageDead(_6); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::__anneal_vt_driver_31616",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", predicateKey := "miri_diff_corpus::__AnnealVtableAlt31616", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt31616"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", predicateKey := "miri_diff_corpus::__AnnealVtableTrait31616", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait31616"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableAlt31616>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver31616 as __AnnealVtableTrait31616>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver31616 as __AnnealVtableTrait31616>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableTrait31616>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableTrait31616>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt31616::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait31616::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait31616::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", slotIdx := 4 } List.nil))),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_seed") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_bias") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil), layoutIdx := 1 }, debugName := (Option.some "__vt_rec") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver31616" List.nil), layoutIdx := 2 }, debugName := (Option.some "__vt_other") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 }, debugName := (Option.some "__vt_rec_dyn") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 }, debugName := (Option.some "__vt_other_dyn") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver31616" List.nil)), layoutIdx := 6 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver31616" List.nil)), layoutIdx := 6 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 }, debugName := (Option.some "__vt_dyn") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt31616")), layoutIdx := 4 }, debugName := (Option.some "__vt_dyn_alt") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt31616")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt31616")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_virtual") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_alt_bits") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt31616")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_same_obj") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt31616")), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_diff_obj") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 13), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 60), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:310:9: 310:17" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:311:15: 311:31" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:311:15: 311:24" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:311:15: 311:24" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 5, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 9, sizeBytes := 4 })) }))), span := "src/lib.rs:311:15: 311:31" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:311:30: 311:31" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::__AnnealVtableReceiver31616" 0 Option.none) (List.cons (Operand.move { local_ := 4, projection := List.nil }) List.nil))), span := "src/lib.rs:310:49: 312:6" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:312:5: 312:6" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:313:9: 313:19" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:314:14: 314:42" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:314:14: 314:35" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:314:15: 314:24" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:314:15: 314:24" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 9, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 255, sizeBytes := 4 })) }))), span := "src/lib.rs:314:14: 314:35" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:314:34: 314:35" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 8, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 9, sizeBytes := 4 })) }))), span := "src/lib.rs:314:14: 314:42" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:314:41: 314:42" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:315:15: 315:41" } (List.cons { kind := (StatementKind.storageLive 11), span := "src/lib.rs:315:15: 315:34" } (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:315:16: 315:25" } (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:315:16: 315:25" } (List.cons { kind := (StatementKind.assign { local_ := 13, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:315:15: 315:34" } List.nil)))))))))))))))))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 13, projection := List.nil }) true 1 UnwindAction.continue_), span := "src/lib.rs:315:15: 315:34" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.binaryOp BinOp.shr (Operand.move { local_ := 12, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:315:15: 315:34" } (List.cons { kind := (StatementKind.storageDead 12), span := "src/lib.rs:315:33: 315:34" } (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 11, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 9, sizeBytes := 4 })) }))), span := "src/lib.rs:315:15: 315:41" } (List.cons { kind := (StatementKind.storageDead 11), span := "src/lib.rs:315:40: 315:41" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::__AnnealVtableAltReceiver31616" 0 Option.none) (List.cons (Operand.move { local_ := 7, projection := List.nil }) (List.cons (Operand.move { local_ := 10, projection := List.nil }) List.nil)))), span := "src/lib.rs:313:54: 316:6" } (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:316:5: 316:6" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:316:5: 316:6" } (List.cons { kind := (StatementKind.storageLive 14), span := "src/lib.rs:317:9: 317:21" } (List.cons { kind := (StatementKind.storageLive 15), span := "src/lib.rs:317:55: 318:41" } (List.cons { kind := (StatementKind.storageLive 16), span := "src/lib.rs:317:55: 318:41" } (List.cons { kind := (StatementKind.storageLive 17), span := "src/lib.rs:317:55: 317:64" } (List.cons { kind := (StatementKind.storageLive 18), span := "src/lib.rs:317:55: 317:64" } (List.cons { kind := (StatementKind.assign { local_ := 18, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 3, projection := List.nil })), span := "src/lib.rs:317:55: 317:64" } (List.cons { kind := (StatementKind.assign { local_ := 17, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 18, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:317:55: 317:64" } (List.cons { kind := (StatementKind.assign { local_ := 16, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 17, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 })), span := "src/lib.rs:317:55: 318:41" } (List.cons { kind := (StatementKind.storageDead 17), span := "src/lib.rs:317:63: 317:64" } (List.cons { kind := (StatementKind.assign { local_ := 15, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 16, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:317:55: 318:41" } (List.cons { kind := (StatementKind.assign { local_ := 14, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 15, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 })), span := "src/lib.rs:317:55: 318:41" } (List.cons { kind := (StatementKind.storageDead 15), span := "src/lib.rs:318:40: 318:41" } (List.cons { kind := (StatementKind.storageDead 18), span := "src/lib.rs:318:41: 318:42" } (List.cons { kind := (StatementKind.storageDead 16), span := "src/lib.rs:318:41: 318:42" } (List.cons { kind := (StatementKind.storageLive 19), span := "src/lib.rs:319:9: 319:23" } (List.cons { kind := (StatementKind.storageLive 20), span := "src/lib.rs:319:57: 320:41" } (List.cons { kind := (StatementKind.storageLive 21), span := "src/lib.rs:319:57: 320:41" } (List.cons { kind := (StatementKind.storageLive 22), span := "src/lib.rs:319:57: 319:68" } (List.cons { kind := (StatementKind.storageLive 23), span := "src/lib.rs:319:57: 319:68" } (List.cons { kind := (StatementKind.assign { local_ := 23, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 6, projection := List.nil })), span := "src/lib.rs:319:57: 319:68" } (List.cons { kind := (StatementKind.assign { local_ := 22, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 23, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:319:57: 319:68" } (List.cons { kind := (StatementKind.assign { local_ := 21, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 22, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 })), span := "src/lib.rs:319:57: 320:41" } (List.cons { kind := (StatementKind.storageDead 22), span := "src/lib.rs:319:67: 319:68" } (List.cons { kind := (StatementKind.assign { local_ := 20, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 21, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:319:57: 320:41" } (List.cons { kind := (StatementKind.assign { local_ := 19, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 20, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 })), span := "src/lib.rs:319:57: 320:41" } (List.cons { kind := (StatementKind.storageDead 20), span := "src/lib.rs:320:40: 320:41" } (List.cons { kind := (StatementKind.storageDead 23), span := "src/lib.rs:320:41: 320:42" } (List.cons { kind := (StatementKind.storageDead 21), span := "src/lib.rs:320:41: 320:42" } (List.cons { kind := (StatementKind.storageLive 24), span := "src/lib.rs:321:9: 321:17" } (List.cons { kind := (StatementKind.storageLive 25), span := "src/lib.rs:321:51: 325:6" } (List.cons { kind := (StatementKind.storageLive 26), span := "src/lib.rs:321:51: 325:6" } (List.cons { kind := (StatementKind.storageLive 27), span := "src/lib.rs:321:54: 321:80" } (List.cons { kind := (StatementKind.storageLive 28), span := "src/lib.rs:321:54: 321:72" } (List.cons { kind := (StatementKind.storageLive 29), span := "src/lib.rs:321:55: 321:64" } (List.cons { kind := (StatementKind.assign { local_ := 29, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:321:55: 321:64" } (List.cons { kind := (StatementKind.assign { local_ := 28, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 29, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:321:54: 321:72" } (List.cons { kind := (StatementKind.storageDead 29), span := "src/lib.rs:321:71: 321:72" } (List.cons { kind := (StatementKind.assign { local_ := 27, projection := List.nil } (Rvalue.binaryOp BinOp.eq (Operand.move { local_ := 28, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:321:54: 321:80" } List.nil))))))))))))))))))))))))))))))))))))))))))))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 27, projection := List.nil }) { branches := (List.cons (0, 3) List.nil), otherwise := 2 }), span := "src/lib.rs:321:54: 321:80" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 28), span := "src/lib.rs:321:79: 321:80" } (List.cons { kind := (StatementKind.storageLive 30), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.storageLive 31), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.storageLive 32), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.assign { local_ := 32, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 14, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.assign { local_ := 31, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 32, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 })), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.storageDead 32), span := "src/lib.rs:322:20: 322:21" } (List.cons { kind := (StatementKind.assign { local_ := 30, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 31, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.assign { local_ := 26, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 30, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 })), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.storageDead 31), span := "src/lib.rs:323:5: 323:6" } (List.cons { kind := (StatementKind.storageDead 30), span := "src/lib.rs:323:5: 323:6" } List.nil))))))))))), terminator := { kind := (TerminatorKind.goto 4), span := "src/lib.rs:321:51: 325:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 28), span := "src/lib.rs:321:79: 321:80" } (List.cons { kind := (StatementKind.storageLive 33), span := "src/lib.rs:324:9: 324:23" } (List.cons { kind := (StatementKind.assign { local_ := 33, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 19, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:324:9: 324:23" } (List.cons { kind := (StatementKind.assign { local_ := 26, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 33, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 })), span := "src/lib.rs:324:9: 324:23" } (List.cons { kind := (StatementKind.storageDead 33), span := "src/lib.rs:324:22: 324:23" } List.nil))))), terminator := { kind := (TerminatorKind.goto 4), span := "src/lib.rs:321:51: 325:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 25, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 26, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:321:51: 325:6" } (List.cons { kind := (StatementKind.assign { local_ := 24, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 25, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616")), layoutIdx := 4 })), span := "src/lib.rs:321:51: 325:6" } (List.cons { kind := (StatementKind.storageDead 27), span := "src/lib.rs:325:5: 325:6" } (List.cons { kind := (StatementKind.storageDead 25), span := "src/lib.rs:325:5: 325:6" } (List.cons { kind := (StatementKind.storageDead 26), span := "src/lib.rs:325:6: 325:7" } (List.cons { kind := (StatementKind.storageLive 34), span := "src/lib.rs:326:9: 326:21" } (List.cons { kind := (StatementKind.storageLive 35), span := "src/lib.rs:326:53: 327:39" } (List.cons { kind := (StatementKind.storageLive 36), span := "src/lib.rs:326:53: 327:39" } (List.cons { kind := (StatementKind.storageLive 37), span := "src/lib.rs:326:53: 326:62" } (List.cons { kind := (StatementKind.storageLive 38), span := "src/lib.rs:326:53: 326:62" } (List.cons { kind := (StatementKind.assign { local_ := 38, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 3, projection := List.nil })), span := "src/lib.rs:326:53: 326:62" } (List.cons { kind := (StatementKind.assign { local_ := 37, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 38, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:326:53: 326:62" } (List.cons { kind := (StatementKind.assign { local_ := 36, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 37, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt31616")), layoutIdx := 4 })), span := "src/lib.rs:326:53: 327:39" } (List.cons { kind := (StatementKind.storageDead 37), span := "src/lib.rs:326:61: 326:62" } (List.cons { kind := (StatementKind.assign { local_ := 35, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 36, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:326:53: 327:39" } (List.cons { kind := (StatementKind.assign { local_ := 34, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 35, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt31616")), layoutIdx := 4 })), span := "src/lib.rs:326:53: 327:39" } (List.cons { kind := (StatementKind.storageDead 35), span := "src/lib.rs:327:38: 327:39" } (List.cons { kind := (StatementKind.storageDead 38), span := "src/lib.rs:327:39: 327:40" } (List.cons { kind := (StatementKind.storageDead 36), span := "src/lib.rs:327:39: 327:40" } (List.cons { kind := (StatementKind.storageLive 39), span := "src/lib.rs:328:9: 328:21" } (List.cons { kind := (StatementKind.storageLive 40), span := "src/lib.rs:328:29: 328:56" } (List.cons { kind := (StatementKind.storageLive 41), span := "src/lib.rs:328:29: 328:37" } (List.cons { kind := (StatementKind.assign { local_ := 41, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 24, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:328:29: 328:37" } (List.cons { kind := (StatementKind.storageLive 42), span := "src/lib.rs:328:46: 328:55" } (List.cons { kind := (StatementKind.assign { local_ := 42, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:328:46: 328:55" } List.nil))))))))))))))))))))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__AnnealVtableTrait31616::eval_vt" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616") List.nil)), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 41, projection := List.nil }) (List.cons (Operand.move { local_ := 42, projection := List.nil }) List.nil)) { local_ := 40, projection := List.nil } (Option.some 5) UnwindAction.continue_), span := "src/lib.rs:328:29: 328:56" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 42), span := "src/lib.rs:328:55: 328:56" } (List.cons { kind := (StatementKind.storageDead 41), span := "src/lib.rs:328:55: 328:56" } (List.cons { kind := (StatementKind.storageLive 43), span := "src/lib.rs:328:59: 328:76" } (List.cons { kind := (StatementKind.storageLive 44), span := "src/lib.rs:328:59: 328:67" } (List.cons { kind := (StatementKind.assign { local_ := 44, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 24, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:328:59: 328:67" } List.nil))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__AnnealVtableTrait31616::tag_vt" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616") List.nil)), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 44, projection := List.nil }) List.nil) { local_ := 43, projection := List.nil } (Option.some 6) UnwindAction.continue_), span := "src/lib.rs:328:59: 328:76" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 44), span := "src/lib.rs:328:75: 328:76" } (List.cons { kind := (StatementKind.assign { local_ := 39, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 40, projection := List.nil }) (Operand.move { local_ := 43, projection := List.nil }))), span := "src/lib.rs:328:29: 328:76" } (List.cons { kind := (StatementKind.storageDead 43), span := "src/lib.rs:328:75: 328:76" } (List.cons { kind := (StatementKind.storageDead 40), span := "src/lib.rs:328:75: 328:76" } (List.cons { kind := (StatementKind.storageLive 45), span := "src/lib.rs:329:9: 329:22" } (List.cons { kind := (StatementKind.storageLive 46), span := "src/lib.rs:329:30: 329:42" } (List.cons { kind := (StatementKind.assign { local_ := 46, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 34, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:329:30: 329:42" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__AnnealVtableAlt31616::eval_alt" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt31616") List.nil)), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 46, projection := List.nil }) List.nil) { local_ := 45, projection := List.nil } (Option.some 7) UnwindAction.continue_), span := "src/lib.rs:329:30: 329:53" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 46), span := "src/lib.rs:329:52: 329:53" } (List.cons { kind := (StatementKind.storageLive 47), span := "src/lib.rs:330:9: 330:22" } (List.cons { kind := (StatementKind.storageLive 48), span := "src/lib.rs:330:33: 330:79" } (List.cons { kind := (StatementKind.storageLive 49), span := "src/lib.rs:330:52: 330:64" } (List.cons { kind := (StatementKind.assign { local_ := 49, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 14, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:330:52: 330:64" } (List.cons { kind := (StatementKind.storageLive 50), span := "src/lib.rs:330:66: 330:78" } (List.cons { kind := (StatementKind.assign { local_ := 50, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 34, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:330:66: 330:78" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::ptr::addr_eq" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616") (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt31616") List.nil))), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 49, projection := List.nil }) (List.cons (Operand.move { local_ := 50, projection := List.nil }) List.nil)) { local_ := 48, projection := List.nil } (Option.some 8) UnwindAction.continue_), span := "src/lib.rs:330:33: 330:79" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 48, projection := List.nil }) { branches := (List.cons (0, 10) List.nil), otherwise := 9 }), span := "src/lib.rs:330:33: 330:79" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 50), span := "src/lib.rs:330:78: 330:79" } (List.cons { kind := (StatementKind.storageDead 49), span := "src/lib.rs:330:78: 330:79" } (List.cons { kind := (StatementKind.assign { local_ := 47, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:331:9: 331:13" } List.nil))), terminator := { kind := (TerminatorKind.goto 11), span := "src/lib.rs:330:30: 334:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 50), span := "src/lib.rs:330:78: 330:79" } (List.cons { kind := (StatementKind.storageDead 49), span := "src/lib.rs:330:78: 330:79" } (List.cons { kind := (StatementKind.assign { local_ := 47, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:333:9: 333:13" } List.nil))), terminator := { kind := (TerminatorKind.goto 11), span := "src/lib.rs:330:30: 334:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 48), span := "src/lib.rs:334:5: 334:6" } (List.cons { kind := (StatementKind.storageLive 51), span := "src/lib.rs:335:9: 335:22" } (List.cons { kind := (StatementKind.storageLive 52), span := "src/lib.rs:335:33: 335:81" } (List.cons { kind := (StatementKind.storageLive 53), span := "src/lib.rs:335:52: 335:64" } (List.cons { kind := (StatementKind.assign { local_ := 53, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 14, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:335:52: 335:64" } (List.cons { kind := (StatementKind.storageLive 54), span := "src/lib.rs:335:66: 335:80" } (List.cons { kind := (StatementKind.assign { local_ := 54, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 19, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:335:66: 335:80" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::ptr::addr_eq" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616") (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait31616") List.nil))), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 53, projection := List.nil }) (List.cons (Operand.move { local_ := 54, projection := List.nil }) List.nil)) { local_ := 52, projection := List.nil } (Option.some 12) UnwindAction.continue_), span := "src/lib.rs:335:33: 335:81" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 52, projection := List.nil }) { branches := (List.cons (0, 14) List.nil), otherwise := 13 }), span := "src/lib.rs:335:33: 335:81" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 54), span := "src/lib.rs:335:80: 335:81" } (List.cons { kind := (StatementKind.storageDead 53), span := "src/lib.rs:335:80: 335:81" } (List.cons { kind := (StatementKind.assign { local_ := 51, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:336:9: 336:13" } List.nil))), terminator := { kind := (TerminatorKind.goto 15), span := "src/lib.rs:335:30: 339:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 54), span := "src/lib.rs:335:80: 335:81" } (List.cons { kind := (StatementKind.storageDead 53), span := "src/lib.rs:335:80: 335:81" } (List.cons { kind := (StatementKind.assign { local_ := 51, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }))), span := "src/lib.rs:338:9: 338:13" } List.nil))), terminator := { kind := (TerminatorKind.goto 15), span := "src/lib.rs:335:30: 339:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 52), span := "src/lib.rs:339:5: 339:6" } (List.cons { kind := (StatementKind.storageLive 55), span := "src/lib.rs:340:5: 340:59" } (List.cons { kind := (StatementKind.storageLive 56), span := "src/lib.rs:340:5: 340:43" } (List.cons { kind := (StatementKind.storageLive 57), span := "src/lib.rs:340:5: 340:17" } (List.cons { kind := (StatementKind.assign { local_ := 57, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 39, projection := List.nil }))), span := "src/lib.rs:340:5: 340:17" } (List.cons { kind := (StatementKind.storageLive 58), span := "src/lib.rs:340:20: 340:43" } (List.cons { kind := (StatementKind.storageLive 59), span := "src/lib.rs:340:21: 340:34" } (List.cons { kind := (StatementKind.assign { local_ := 59, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 45, projection := List.nil }))), span := "src/lib.rs:340:21: 340:34" } (List.cons { kind := (StatementKind.assign { local_ := 60, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:340:20: 340:43" } List.nil))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 60, projection := List.nil }) true 16 UnwindAction.continue_), span := "src/lib.rs:340:20: 340:43" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 58, projection := List.nil } (Rvalue.binaryOp BinOp.shl (Operand.move { local_ := 59, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }))), span := "src/lib.rs:340:20: 340:43" } (List.cons { kind := (StatementKind.storageDead 59), span := "src/lib.rs:340:42: 340:43" } (List.cons { kind := (StatementKind.assign { local_ := 56, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 57, projection := List.nil }) (Operand.move { local_ := 58, projection := List.nil }))), span := "src/lib.rs:340:5: 340:43" } (List.cons { kind := (StatementKind.storageDead 58), span := "src/lib.rs:340:42: 340:43" } (List.cons { kind := (StatementKind.storageDead 57), span := "src/lib.rs:340:42: 340:43" } (List.cons { kind := (StatementKind.storageLive 61), span := "src/lib.rs:340:46: 340:59" } (List.cons { kind := (StatementKind.assign { local_ := 61, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 47, projection := List.nil }))), span := "src/lib.rs:340:46: 340:59" } (List.cons { kind := (StatementKind.assign { local_ := 55, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 56, projection := List.nil }) (Operand.move { local_ := 61, projection := List.nil }))), span := "src/lib.rs:340:5: 340:59" } (List.cons { kind := (StatementKind.storageDead 61), span := "src/lib.rs:340:58: 340:59" } (List.cons { kind := (StatementKind.storageDead 56), span := "src/lib.rs:340:58: 340:59" } (List.cons { kind := (StatementKind.storageLive 62), span := "src/lib.rs:340:62: 340:75" } (List.cons { kind := (StatementKind.assign { local_ := 62, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 51, projection := List.nil }))), span := "src/lib.rs:340:62: 340:75" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 55, projection := List.nil }) (Operand.move { local_ := 62, projection := List.nil }))), span := "src/lib.rs:340:5: 340:75" } (List.cons { kind := (StatementKind.storageDead 62), span := "src/lib.rs:340:74: 340:75" } (List.cons { kind := (StatementKind.storageDead 55), span := "src/lib.rs:340:74: 340:75" } (List.cons { kind := (StatementKind.storageDead 51), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 47), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 45), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 39), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 34), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 24), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 19), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 14), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:341:1: 341:2" } List.nil))))))))))))))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:341:2: 341:2" }, isCleanup := false } List.nil))))))))))))))))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0002.Driver

namespace F0002.RecvTraitEvalVt

/-! Captured `miri_diff_corpus` item `__AnnealVtableReceiver31616_as___AnnealVtableTrait31616_eval_vt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_3); StorageLive(_4); _4 = copy _2; StorageLive(_5); _5 = copy ((*_1).0: u32); _3 = BitXor(move _4, move _5); StorageDead(_5); StorageDead(_4); _0 = BitAnd(move _3, const 65535_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableTrait31616>::eval_vt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableTrait31616::eval_vt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableTrait31616>::eval_vt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", predicateKey := "miri_diff_corpus::__AnnealVtableAlt31616", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt31616"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", predicateKey := "miri_diff_corpus::__AnnealVtableTrait31616", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait31616"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableAlt31616>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver31616 as __AnnealVtableTrait31616>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver31616 as __AnnealVtableTrait31616>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableTrait31616>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableTrait31616>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt31616::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait31616::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait31616::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", slotIdx := 4 } List.nil))),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:289:9: 289:24" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:289:10: 289:11" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:289:10: 289:11" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:289:14: 289:23" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:289:14: 289:23" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 4, projection := List.nil }) (Operand.move { local_ := 5, projection := List.nil }))), span := "src/lib.rs:289:9: 289:24" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:289:23: 289:24" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:289:23: 289:24" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 65535, sizeBytes := 4 })) }))), span := "src/lib.rs:289:9: 289:36" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:289:35: 289:36" } List.nil)))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:290:6: 290:6" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0002.RecvTraitEvalVt

namespace F0002.RecvTraitTagVt

/-! Captured `miri_diff_corpus` item `__AnnealVtableReceiver31616_as___AnnealVtableTrait31616_tag_vt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = copy ((*_1).0: u32); _2 = BitAnd(move _3, const 63_u32); StorageDead(_3); _0 = BitXor(move _2, const 21_u32); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableTrait31616>::tag_vt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableTrait31616::tag_vt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableTrait31616>::tag_vt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", predicateKey := "miri_diff_corpus::__AnnealVtableAlt31616", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt31616"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", predicateKey := "miri_diff_corpus::__AnnealVtableTrait31616", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait31616"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableAlt31616>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver31616 as __AnnealVtableTrait31616>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver31616 as __AnnealVtableTrait31616>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableTrait31616>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableTrait31616>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt31616::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait31616::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait31616::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", slotIdx := 4 } List.nil))),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:292:9: 292:30" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:292:10: 292:19" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:292:10: 292:19" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 63, sizeBytes := 4 })) }))), span := "src/lib.rs:292:9: 292:30" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:292:29: 292:30" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 2, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 21, sizeBytes := 4 })) }))), span := "src/lib.rs:292:9: 292:40" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:292:39: 292:40" } List.nil))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:293:6: 293:6" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0002.RecvTraitTagVt

namespace F0002.RecvAltEvalAlt

/-! Captured `miri_diff_corpus` item `__AnnealVtableReceiver31616_as___AnnealVtableAlt31616_eval_alt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))) }

-- bb0: StorageLive(_2); _2 = copy ((*_1).0: u32); _3 = Lt(const 1_u32, const 32_u32); assert(move _3, "attempt to shift right by `{}`, which would overflow", const 1_u32) -> [success: bb1, unwind continue]
-- bb1: _0 = Shr(move _2, const 1_u32); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableAlt31616>::eval_alt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableAlt31616::eval_alt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableAlt31616>::eval_alt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", predicateKey := "miri_diff_corpus::__AnnealVtableAlt31616", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt31616"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", predicateKey := "miri_diff_corpus::__AnnealVtableTrait31616", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait31616"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableAlt31616>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver31616 as __AnnealVtableTrait31616>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver31616 as __AnnealVtableTrait31616>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableTrait31616>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableTrait31616>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt31616::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait31616::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait31616::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", slotIdx := 4 } List.nil))),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:305:9: 305:18" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:305:9: 305:18" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:305:9: 305:26" } List.nil)))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 3, projection := List.nil }) true 1 UnwindAction.continue_), span := "src/lib.rs:305:9: 305:26" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.shr (Operand.move { local_ := 2, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:305:9: 305:26" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:305:25: 305:26" } List.nil)), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:306:6: 306:6" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0002.RecvAltEvalAlt

namespace F0002.AltRecvTraitEvalVt

/-! Captured `miri_diff_corpus` item `__AnnealVtableAltReceiver31616_as___AnnealVtableTrait31616_eval_vt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 0 List.nil)) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))) }

-- bb0: StorageLive(_3); StorageLive(_4); StorageLive(_5); StorageLive(_6); _6 = copy _2; _7 = Lt(const 1_u32, const 32_u32); assert(move _7, "attempt to shift right by `{}`, which would overflow", const 1_u32) -> [success: bb1, unwind continue]
-- bb1: _5 = Shr(move _6, const 1_u32); StorageDead(_6); StorageLive(_8); _8 = copy ((*_1).0: u32); _4 = BitXor(move _5, move _8); StorageDead(_8); StorageDead(_5); StorageLive(_9); _9 = copy ((*_1).1: u32); _3 = BitXor(move _4, move _9); StorageDead(_9); StorageDead(_4); _0 = BitAnd(move _3, const 65535_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableAltReceiver31616 as __AnnealVtableTrait31616>::eval_vt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableTrait31616::eval_vt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver31616" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableAltReceiver31616 as __AnnealVtableTrait31616>::eval_vt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", predicateKey := "miri_diff_corpus::__AnnealVtableAlt31616", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt31616"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", predicateKey := "miri_diff_corpus::__AnnealVtableTrait31616", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait31616"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableAlt31616>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver31616 as __AnnealVtableTrait31616>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver31616 as __AnnealVtableTrait31616>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableTrait31616>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableTrait31616>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt31616::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait31616::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait31616::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", slotIdx := 4 } List.nil))),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver31616" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 7), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:297:9: 297:45" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:297:10: 297:32" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:297:10: 297:21" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:297:11: 297:12" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:297:11: 297:12" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:297:10: 297:21" } List.nil))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 7, projection := List.nil }) true 1 UnwindAction.continue_), span := "src/lib.rs:297:10: 297:21" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.binaryOp BinOp.shr (Operand.move { local_ := 6, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:297:10: 297:21" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:297:20: 297:21" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:297:24: 297:32" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:297:24: 297:32" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 5, projection := List.nil }) (Operand.move { local_ := 8, projection := List.nil }))), span := "src/lib.rs:297:10: 297:32" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:297:31: 297:32" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:297:31: 297:32" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:297:35: 297:44" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 1 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:297:35: 297:44" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 4, projection := List.nil }) (Operand.move { local_ := 9, projection := List.nil }))), span := "src/lib.rs:297:9: 297:45" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:297:44: 297:45" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:297:44: 297:45" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 65535, sizeBytes := 4 })) }))), span := "src/lib.rs:297:9: 297:57" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:297:56: 297:57" } List.nil)))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:298:6: 298:6" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0002.AltRecvTraitEvalVt

namespace F0002.AltRecvTraitTagVt

/-! Captured `miri_diff_corpus` item `__AnnealVtableAltReceiver31616_as___AnnealVtableTrait31616_tag_vt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 0 List.nil)) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_2); StorageLive(_3); StorageLive(_4); _4 = copy ((*_1).0: u32); StorageLive(_5); _5 = copy ((*_1).1: u32); _3 = BitXor(move _4, move _5); StorageDead(_5); StorageDead(_4); _2 = BitAnd(move _3, const 63_u32); StorageDead(_3); _0 = BitXor(move _2, const 42_u32); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableAltReceiver31616 as __AnnealVtableTrait31616>::tag_vt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableTrait31616::tag_vt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver31616" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableAltReceiver31616 as __AnnealVtableTrait31616>::tag_vt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", predicateKey := "miri_diff_corpus::__AnnealVtableAlt31616", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt31616"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", predicateKey := "miri_diff_corpus::__AnnealVtableTrait31616", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait31616"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableAlt31616>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver31616 as __AnnealVtableTrait31616>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver31616 as __AnnealVtableTrait31616>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver31616" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableTrait31616>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver31616 as __AnnealVtableTrait31616>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt31616::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt31616", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait31616::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait31616::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait31616", slotIdx := 4 } List.nil))),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver31616" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:300:9: 300:43" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:300:10: 300:32" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:300:11: 300:19" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:300:11: 300:19" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:300:22: 300:31" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 1 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:300:22: 300:31" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 4, projection := List.nil }) (Operand.move { local_ := 5, projection := List.nil }))), span := "src/lib.rs:300:10: 300:32" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:300:31: 300:32" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:300:31: 300:32" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 63, sizeBytes := 4 })) }))), span := "src/lib.rs:300:9: 300:43" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:300:42: 300:43" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 2, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 42, sizeBytes := 4 })) }))), span := "src/lib.rs:300:9: 300:53" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:300:52: 300:53" } List.nil))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:301:6: 301:6" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0002.AltRecvTraitTagVt

/-- Linked callee table of `finding_0002`: the driver and the 5 trait-method impls. -/
def F0002.linkedCallees : List CapturedMir :=
  [F0002.Driver.body, F0002.RecvTraitEvalVt.body, F0002.RecvTraitTagVt.body, F0002.RecvAltEvalAlt.body, F0002.AltRecvTraitEvalVt.body, F0002.AltRecvTraitTagVt.body]

set_option maxRecDepth 1000000 in
/-- Campaign #22 `finding_0002` end-to-end agreement with Miri (`MIRI_PASS:scalar:67:4`):
`miri_diff_corpus::pass_subslice_pattern_extract__b17_c23` returns `67_u32` with the driver and the 5 trait-method
impls linked. -/
theorem F0002.miri_agreement :
    evalMirDiffTagBounded 512 F0002.Outer.body
      (initMachineStateWithMemoryAndCallees F0002.Outer.body [] emptyMemory F0002.linkedCallees) =
      .normalScalar 67 4 := by
  rfl

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0002`, only the driver linked (the 5 trait-method impls are absent)): the first virtual call resolves through the captured vtable to a method `DefPath` with no linked body, so the run stops at that `externalCall` (never a value).
Fault site: `src/lib.rs:328:29: 328:56`. -/
theorem F0002.control_noImpls :
    runC22 F0002.Outer.body [F0002.Driver.body] =
      .externalCall "miri_diff_corpus::<__AnnealVtableAltReceiver31616 as __AnnealVtableTrait31616>::eval_vt" ∧
    probeC22 F0002.Outer.body [F0002.Driver.body] =
      (.externalCall "miri_diff_corpus::<__AnnealVtableAltReceiver31616 as __AnnealVtableTrait31616>::eval_vt", "src/lib.rs:328:29: 328:56") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0002`, nothing linked): the outer function's call to the unlinked driver escapes as `externalCall` (never a value).
Fault site: `src/lib.rs:347:32: 347:69`. -/
theorem F0002.control_noDriver :
    runC22 F0002.Outer.body [] =
      .externalCall "miri_diff_corpus::__anneal_vt_driver_31616" ∧
    probeC22 F0002.Outer.body [] =
      (.externalCall "miri_diff_corpus::__anneal_vt_driver_31616", "src/lib.rs:347:32: 347:69") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0002`, `vtables` stripped from the outer body and from every linked body): the first `&T as &dyn Trait` unsizing finds no usable captured `(T, dyn Trait)` vtable (missing table, missing record, or `bodyVTablesConsistent` failure) and fails closed with `.unsupported` at that statement (never `.ub`, never a value).
Fault site: `src/lib.rs:317:55: 318:41`. -/
theorem F0002.control_stripped :
    runC22 (stripVTables F0002.Outer.body) (F0002.linkedCallees.map stripVTables) =
      .unsupported ∧
    probeC22 (stripVTables F0002.Outer.body) (F0002.linkedCallees.map stripVTables) =
      (.unsupported, "src/lib.rs:317:55: 318:41") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0002`, `vtables` stripped from every linked body (outer body intact)): the first `&T as &dyn Trait` unsizing finds no usable captured `(T, dyn Trait)` vtable (missing table, missing record, or `bodyVTablesConsistent` failure) and fails closed with `.unsupported` at that statement (never `.ub`, never a value).
Fault site: `src/lib.rs:317:55: 318:41`. -/
theorem F0002.control_strippedLinked :
    runC22 F0002.Outer.body (F0002.linkedCallees.map stripVTables) =
      .unsupported ∧
    probeC22 F0002.Outer.body (F0002.linkedCallees.map stripVTables) =
      (.unsupported, "src/lib.rs:317:55: 318:41") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0002`, unit-consistent forgery `forgeNonMethodSlot` applied to every body): the virtual call reads a vtable slot that is not a method (`.size` header slot, or past the end of the table): Miri's `get_vtable_entries`/`VtblEntry` dispatch raises UB (\"`dyn` call trying to call something that is not a method\" / out-of-bounds vtable index), and the TCB faults `.ub` at that call.
Fault site: `src/lib.rs:328:29: 328:56`. -/
theorem F0002.control_nonMethodSlot :
    runC22 (mapVTables forgeNonMethodSlot F0002.Outer.body) (F0002.linkedCallees.map (mapVTables forgeNonMethodSlot)) =
      .ub ∧
    probeC22 (mapVTables forgeNonMethodSlot F0002.Outer.body) (F0002.linkedCallees.map (mapVTables forgeNonMethodSlot)) =
      (.ub, "src/lib.rs:328:29: 328:56") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0002`, unit-consistent forgery `forgeTruncatedSlots` applied to every body): the virtual call reads a vtable slot that is not a method (`.size` header slot, or past the end of the table): Miri's `get_vtable_entries`/`VtblEntry` dispatch raises UB (\"`dyn` call trying to call something that is not a method\" / out-of-bounds vtable index), and the TCB faults `.ub` at that call.
Fault site: `src/lib.rs:328:59: 328:76`. -/
theorem F0002.control_truncatedSlots :
    runC22 (mapVTables forgeTruncatedSlots F0002.Outer.body) (F0002.linkedCallees.map (mapVTables forgeTruncatedSlots)) =
      .ub ∧
    probeC22 (mapVTables forgeTruncatedSlots F0002.Outer.body) (F0002.linkedCallees.map (mapVTables forgeTruncatedSlots)) =
      (.ub, "src/lib.rs:328:59: 328:76") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0002`, unit-consistent forgery `forgeWrongDynKey` applied to every body): the first `&T as &dyn Trait` unsizing finds no usable captured `(T, dyn Trait)` vtable (missing table, missing record, or `bodyVTablesConsistent` failure) and fails closed with `.unsupported` at that statement (never `.ub`, never a value).
Fault site: `src/lib.rs:317:55: 318:41`. -/
theorem F0002.control_wrongDynKey :
    runC22 (mapVTables forgeWrongDynKey F0002.Outer.body) (F0002.linkedCallees.map (mapVTables forgeWrongDynKey)) =
      .unsupported ∧
    probeC22 (mapVTables forgeWrongDynKey F0002.Outer.body) (F0002.linkedCallees.map (mapVTables forgeWrongDynKey)) =
      (.unsupported, "src/lib.rs:317:55: 318:41") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0002`, `forgeNonMethodSlot` applied to the driver's table only (linked bodies disagree)): the first `&T as &dyn Trait` unsizing finds no usable captured `(T, dyn Trait)` vtable (missing table, missing record, or `bodyVTablesConsistent` failure) and fails closed with `.unsupported` at that statement (never `.ub`, never a value).
Fault site: `src/lib.rs:317:55: 318:41`. -/
theorem F0002.control_inconsistent :
    runC22 F0002.Outer.body (mapVTables forgeNonMethodSlot F0002.Driver.body :: F0002.linkedCallees.drop 1) =
      .unsupported ∧
    probeC22 F0002.Outer.body (mapVTables forgeNonMethodSlot F0002.Driver.body :: F0002.linkedCallees.drop 1) =
      (.unsupported, "src/lib.rs:317:55: 318:41") :=
  ⟨by rfl, by rfl⟩

/-! ### Campaign #22 `finding_0003`: `miri_diff_corpus::pass_exact_div_valid__b17_c25` (Miri: `MIRI_PASS:scalar:57:4`).

Verbatim `layouts`/`body` definitions emitted by HEAD `anneal-rustc-capture` (`Runtime(PostCleanup)` MIR,
nightly-2026-06-01, `-Zmir-opt-level=0 -C debug-assertions=off -C overflow-checks=on`). -/

namespace F0003.Outer

/-! Captured `miri_diff_corpus` item `pass_exact_div_valid__b17_c25`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)) }

-- bb0: StorageLive(_1); _1 = core::intrinsics::exact_div::<u32>(const 84_u32, const 7_u32) -> [return: bb1, unwind unreachable]
-- bb1: StorageLive(_2); _2 = __anneal_vt_driver_49793(const 9_u32, const 5_u32) -> [return: bb2, unwind continue]
-- bb2: StorageLive(_3); _3 = copy _1; StorageLive(_4); _4 = copy _2; _0 = BitXor(move _3, move _4); StorageDead(_4); StorageDead(_3); StorageDead(_2); StorageDead(_1); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::pass_exact_div_valid__b17_c25",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", predicateKey := "miri_diff_corpus::__AnnealVtableAlt49793", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt49793"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", predicateKey := "miri_diff_corpus::__AnnealVtableTrait49793", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait49793"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableAlt49793>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver49793 as __AnnealVtableTrait49793>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver49793 as __AnnealVtableTrait49793>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableTrait49793>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableTrait49793>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt49793::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait49793::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait49793::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", slotIdx := 4 } List.nil))),
    argCount := 0,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__tail___miri_vt_49793") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__miri_vt_49793") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 1), span := "src/lib.rs:344:9: 344:31" } List.nil), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::intrinsics::exact_div" (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 84, sizeBytes := 4 })) }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 7, sizeBytes := 4 })) }) List.nil)) { local_ := 1, projection := List.nil } (Option.some 1) UnwindAction.unreachable), span := "src/lib.rs:344:48: 344:70" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:345:9: 345:24" } List.nil), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__anneal_vt_driver_49793" List.nil), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 9, sizeBytes := 4 })) }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 5, sizeBytes := 4 })) }) List.nil)) { local_ := 2, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:345:32: 345:68" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:346:5: 346:27" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:346:5: 346:27" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:346:30: 346:54" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:346:31: 346:46" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 3, projection := List.nil }) (Operand.move { local_ := 4, projection := List.nil }))), span := "src/lib.rs:346:5: 346:54" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:346:53: 346:54" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:346:53: 346:54" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:347:1: 347:2" } (List.cons { kind := (StatementKind.storageDead 1), span := "src/lib.rs:347:1: 347:2" } List.nil))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:347:2: 347:2" }, isCleanup := false } List.nil))),
    fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0003.Outer

namespace F0003.Driver

/-! Captured `miri_diff_corpus` item `__anneal_vt_driver_49793`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 0 List.nil)) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))))))) }

-- bb0: StorageLive(_3); StorageLive(_4); StorageLive(_5); _5 = copy _2; _4 = BitXor(move _5, const 9_u32); StorageDead(_5); _3 = __AnnealVtableReceiver49793 { bias: move _4 }; StorageDead(_4); StorageLive(_6); StorageLive(_7); StorageLive(_8); StorageLive(_9); _9 = copy _1; _8 = BitAnd(move _9, const 255_u32); StorageDead(_9); _7 = BitXor(move _8, const 9_u32); StorageDead(_8); StorageLive(_10); StorageLive(_11); StorageLive(_12); _12 = copy _2; _13 = Lt(const 1_u32, const 32_u32); assert(move _13, "attempt to shift right by `{}`, which would overflow", const 1_u32) -> [success: bb1, unwind continue]
-- bb1: _11 = Shr(move _12, const 1_u32); StorageDead(_12); _10 = BitXor(move _11, const 9_u32); StorageDead(_11); _6 = __AnnealVtableAltReceiver49793 { pad: move _7, bias: move _10 }; StorageDead(_10); StorageDead(_7); StorageLive(_14); StorageLive(_15); StorageLive(_16); StorageLive(_17); StorageLive(_18); _18 = &_3; _17 = &(*_18); _16 = move _17 as &dyn __AnnealVtableTrait49793 (PointerCoercion(Unsize, AsCast)); StorageDead(_17); _15 = &(*_16); _14 = move _15 as &dyn __AnnealVtableTrait49793 (PointerCoercion(Unsize, Implicit)); StorageDead(_15); StorageDead(_18); StorageDead(_16); StorageLive(_19); StorageLive(_20); StorageLive(_21); StorageLive(_22); StorageLive(_23); _23 = &_6; _22 = &(*_23); _21 = move _22 as &dyn __AnnealVtableTrait49793 (PointerCoercion(Unsize, AsCast)); StorageDead(_22); _20 = &(*_21); _19 = move _20 as &dyn __AnnealVtableTrait49793 (PointerCoercion(Unsize, Implicit)); StorageDead(_20); StorageDead(_23); StorageDead(_21); StorageLive(_24); StorageLive(_25); StorageLive(_26); StorageLive(_27); StorageLive(_28); StorageLive(_29); _29 = copy _1; _28 = BitAnd(move _29, const 1_u32); StorageDead(_29); _27 = Eq(move _28, const 0_u32); switchInt(move _27) -> [0: bb3, otherwise: bb2]
-- bb2: StorageDead(_28); StorageLive(_30); StorageLive(_31); StorageLive(_32); _32 = &(*_14); _31 = move _32 as &dyn __AnnealVtableTrait49793 (PointerCoercion(Unsize, Implicit)); StorageDead(_32); _30 = &(*_31); _26 = move _30 as &dyn __AnnealVtableTrait49793 (PointerCoercion(Unsize, Implicit)); StorageDead(_31); StorageDead(_30); goto -> bb4
-- bb3: StorageDead(_28); StorageLive(_33); _33 = &(*_19); _26 = move _33 as &dyn __AnnealVtableTrait49793 (PointerCoercion(Unsize, Implicit)); StorageDead(_33); goto -> bb4
-- bb4: _25 = &(*_26); _24 = move _25 as &dyn __AnnealVtableTrait49793 (PointerCoercion(Unsize, Implicit)); StorageDead(_27); StorageDead(_25); StorageDead(_26); StorageLive(_34); StorageLive(_35); StorageLive(_36); StorageLive(_37); StorageLive(_38); _38 = &_3; _37 = &(*_38); _36 = move _37 as &dyn __AnnealVtableAlt49793 (PointerCoercion(Unsize, AsCast)); StorageDead(_37); _35 = &(*_36); _34 = move _35 as &dyn __AnnealVtableAlt49793 (PointerCoercion(Unsize, Implicit)); StorageDead(_35); StorageDead(_38); StorageDead(_36); StorageLive(_39); StorageLive(_40); StorageLive(_41); _41 = &(*_24); StorageLive(_42); _42 = copy _1; _40 = <dyn __AnnealVtableTrait49793 as __AnnealVtableTrait49793>::eval_vt(move _41, move _42) -> [return: bb5, unwind continue]
-- bb5: StorageDead(_42); StorageDead(_41); StorageLive(_43); StorageLive(_44); _44 = &(*_24); _43 = <dyn __AnnealVtableTrait49793 as __AnnealVtableTrait49793>::tag_vt(move _44) -> [return: bb6, unwind continue]
-- bb6: StorageDead(_44); _39 = BitXor(move _40, move _43); StorageDead(_43); StorageDead(_40); StorageLive(_45); StorageLive(_46); _46 = &(*_34); _45 = <dyn __AnnealVtableAlt49793 as __AnnealVtableAlt49793>::eval_alt(move _46) -> [return: bb7, unwind continue]
-- bb7: StorageDead(_46); StorageLive(_47); StorageLive(_48); StorageLive(_49); _49 = &raw const (*_14); StorageLive(_50); _50 = &raw const (*_34); _48 = core::ptr::addr_eq::<dyn __AnnealVtableTrait49793, dyn __AnnealVtableAlt49793>(move _49, move _50) -> [return: bb8, unwind continue]
-- bb8: switchInt(move _48) -> [0: bb10, otherwise: bb9]
-- bb9: StorageDead(_50); StorageDead(_49); _47 = const 1_u32; goto -> bb11
-- bb10: StorageDead(_50); StorageDead(_49); _47 = const 0_u32; goto -> bb11
-- bb11: StorageDead(_48); StorageLive(_51); StorageLive(_52); StorageLive(_53); _53 = &raw const (*_14); StorageLive(_54); _54 = &raw const (*_19); _52 = core::ptr::addr_eq::<dyn __AnnealVtableTrait49793, dyn __AnnealVtableTrait49793>(move _53, move _54) -> [return: bb12, unwind continue]
-- bb12: switchInt(move _52) -> [0: bb14, otherwise: bb13]
-- bb13: StorageDead(_54); StorageDead(_53); _51 = const 0_u32; goto -> bb15
-- bb14: StorageDead(_54); StorageDead(_53); _51 = const 2_u32; goto -> bb15
-- bb15: StorageDead(_52); StorageLive(_55); StorageLive(_56); StorageLive(_57); _57 = copy _39; StorageLive(_58); StorageLive(_59); _59 = copy _45; _60 = Lt(const 2_u32, const 32_u32); assert(move _60, "attempt to shift left by `{}`, which would overflow", const 2_u32) -> [success: bb16, unwind continue]
-- bb16: _58 = Shl(move _59, const 2_u32); StorageDead(_59); _56 = BitXor(move _57, move _58); StorageDead(_58); StorageDead(_57); StorageLive(_61); _61 = copy _47; _55 = BitXor(move _56, move _61); StorageDead(_61); StorageDead(_56); StorageLive(_62); _62 = copy _51; _0 = BitXor(move _55, move _62); StorageDead(_62); StorageDead(_55); StorageDead(_51); StorageDead(_47); StorageDead(_45); StorageDead(_39); StorageDead(_34); StorageDead(_24); StorageDead(_19); StorageDead(_14); StorageDead(_6); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::__anneal_vt_driver_49793",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", predicateKey := "miri_diff_corpus::__AnnealVtableAlt49793", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt49793"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", predicateKey := "miri_diff_corpus::__AnnealVtableTrait49793", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait49793"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableAlt49793>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver49793 as __AnnealVtableTrait49793>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver49793 as __AnnealVtableTrait49793>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableTrait49793>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableTrait49793>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt49793::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait49793::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait49793::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", slotIdx := 4 } List.nil))),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_seed") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_bias") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil), layoutIdx := 1 }, debugName := (Option.some "__vt_rec") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver49793" List.nil), layoutIdx := 2 }, debugName := (Option.some "__vt_other") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 }, debugName := (Option.some "__vt_rec_dyn") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 }, debugName := (Option.some "__vt_other_dyn") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver49793" List.nil)), layoutIdx := 6 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver49793" List.nil)), layoutIdx := 6 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 }, debugName := (Option.some "__vt_dyn") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt49793")), layoutIdx := 4 }, debugName := (Option.some "__vt_dyn_alt") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt49793")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt49793")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_virtual") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_alt_bits") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt49793")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_same_obj") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt49793")), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_diff_obj") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 13), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 60), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:310:9: 310:17" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:311:15: 311:31" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:311:15: 311:24" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:311:15: 311:24" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 5, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 9, sizeBytes := 4 })) }))), span := "src/lib.rs:311:15: 311:31" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:311:30: 311:31" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::__AnnealVtableReceiver49793" 0 Option.none) (List.cons (Operand.move { local_ := 4, projection := List.nil }) List.nil))), span := "src/lib.rs:310:49: 312:6" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:312:5: 312:6" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:313:9: 313:19" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:314:14: 314:42" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:314:14: 314:35" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:314:15: 314:24" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:314:15: 314:24" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 9, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 255, sizeBytes := 4 })) }))), span := "src/lib.rs:314:14: 314:35" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:314:34: 314:35" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 8, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 9, sizeBytes := 4 })) }))), span := "src/lib.rs:314:14: 314:42" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:314:41: 314:42" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:315:15: 315:41" } (List.cons { kind := (StatementKind.storageLive 11), span := "src/lib.rs:315:15: 315:34" } (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:315:16: 315:25" } (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:315:16: 315:25" } (List.cons { kind := (StatementKind.assign { local_ := 13, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:315:15: 315:34" } List.nil)))))))))))))))))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 13, projection := List.nil }) true 1 UnwindAction.continue_), span := "src/lib.rs:315:15: 315:34" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.binaryOp BinOp.shr (Operand.move { local_ := 12, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:315:15: 315:34" } (List.cons { kind := (StatementKind.storageDead 12), span := "src/lib.rs:315:33: 315:34" } (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 11, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 9, sizeBytes := 4 })) }))), span := "src/lib.rs:315:15: 315:41" } (List.cons { kind := (StatementKind.storageDead 11), span := "src/lib.rs:315:40: 315:41" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::__AnnealVtableAltReceiver49793" 0 Option.none) (List.cons (Operand.move { local_ := 7, projection := List.nil }) (List.cons (Operand.move { local_ := 10, projection := List.nil }) List.nil)))), span := "src/lib.rs:313:54: 316:6" } (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:316:5: 316:6" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:316:5: 316:6" } (List.cons { kind := (StatementKind.storageLive 14), span := "src/lib.rs:317:9: 317:21" } (List.cons { kind := (StatementKind.storageLive 15), span := "src/lib.rs:317:55: 318:41" } (List.cons { kind := (StatementKind.storageLive 16), span := "src/lib.rs:317:55: 318:41" } (List.cons { kind := (StatementKind.storageLive 17), span := "src/lib.rs:317:55: 317:64" } (List.cons { kind := (StatementKind.storageLive 18), span := "src/lib.rs:317:55: 317:64" } (List.cons { kind := (StatementKind.assign { local_ := 18, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 3, projection := List.nil })), span := "src/lib.rs:317:55: 317:64" } (List.cons { kind := (StatementKind.assign { local_ := 17, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 18, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:317:55: 317:64" } (List.cons { kind := (StatementKind.assign { local_ := 16, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 17, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 })), span := "src/lib.rs:317:55: 318:41" } (List.cons { kind := (StatementKind.storageDead 17), span := "src/lib.rs:317:63: 317:64" } (List.cons { kind := (StatementKind.assign { local_ := 15, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 16, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:317:55: 318:41" } (List.cons { kind := (StatementKind.assign { local_ := 14, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 15, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 })), span := "src/lib.rs:317:55: 318:41" } (List.cons { kind := (StatementKind.storageDead 15), span := "src/lib.rs:318:40: 318:41" } (List.cons { kind := (StatementKind.storageDead 18), span := "src/lib.rs:318:41: 318:42" } (List.cons { kind := (StatementKind.storageDead 16), span := "src/lib.rs:318:41: 318:42" } (List.cons { kind := (StatementKind.storageLive 19), span := "src/lib.rs:319:9: 319:23" } (List.cons { kind := (StatementKind.storageLive 20), span := "src/lib.rs:319:57: 320:41" } (List.cons { kind := (StatementKind.storageLive 21), span := "src/lib.rs:319:57: 320:41" } (List.cons { kind := (StatementKind.storageLive 22), span := "src/lib.rs:319:57: 319:68" } (List.cons { kind := (StatementKind.storageLive 23), span := "src/lib.rs:319:57: 319:68" } (List.cons { kind := (StatementKind.assign { local_ := 23, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 6, projection := List.nil })), span := "src/lib.rs:319:57: 319:68" } (List.cons { kind := (StatementKind.assign { local_ := 22, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 23, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:319:57: 319:68" } (List.cons { kind := (StatementKind.assign { local_ := 21, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 22, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 })), span := "src/lib.rs:319:57: 320:41" } (List.cons { kind := (StatementKind.storageDead 22), span := "src/lib.rs:319:67: 319:68" } (List.cons { kind := (StatementKind.assign { local_ := 20, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 21, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:319:57: 320:41" } (List.cons { kind := (StatementKind.assign { local_ := 19, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 20, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 })), span := "src/lib.rs:319:57: 320:41" } (List.cons { kind := (StatementKind.storageDead 20), span := "src/lib.rs:320:40: 320:41" } (List.cons { kind := (StatementKind.storageDead 23), span := "src/lib.rs:320:41: 320:42" } (List.cons { kind := (StatementKind.storageDead 21), span := "src/lib.rs:320:41: 320:42" } (List.cons { kind := (StatementKind.storageLive 24), span := "src/lib.rs:321:9: 321:17" } (List.cons { kind := (StatementKind.storageLive 25), span := "src/lib.rs:321:51: 325:6" } (List.cons { kind := (StatementKind.storageLive 26), span := "src/lib.rs:321:51: 325:6" } (List.cons { kind := (StatementKind.storageLive 27), span := "src/lib.rs:321:54: 321:80" } (List.cons { kind := (StatementKind.storageLive 28), span := "src/lib.rs:321:54: 321:72" } (List.cons { kind := (StatementKind.storageLive 29), span := "src/lib.rs:321:55: 321:64" } (List.cons { kind := (StatementKind.assign { local_ := 29, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:321:55: 321:64" } (List.cons { kind := (StatementKind.assign { local_ := 28, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 29, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:321:54: 321:72" } (List.cons { kind := (StatementKind.storageDead 29), span := "src/lib.rs:321:71: 321:72" } (List.cons { kind := (StatementKind.assign { local_ := 27, projection := List.nil } (Rvalue.binaryOp BinOp.eq (Operand.move { local_ := 28, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:321:54: 321:80" } List.nil))))))))))))))))))))))))))))))))))))))))))))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 27, projection := List.nil }) { branches := (List.cons (0, 3) List.nil), otherwise := 2 }), span := "src/lib.rs:321:54: 321:80" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 28), span := "src/lib.rs:321:79: 321:80" } (List.cons { kind := (StatementKind.storageLive 30), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.storageLive 31), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.storageLive 32), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.assign { local_ := 32, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 14, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.assign { local_ := 31, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 32, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 })), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.storageDead 32), span := "src/lib.rs:322:20: 322:21" } (List.cons { kind := (StatementKind.assign { local_ := 30, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 31, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.assign { local_ := 26, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 30, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 })), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.storageDead 31), span := "src/lib.rs:323:5: 323:6" } (List.cons { kind := (StatementKind.storageDead 30), span := "src/lib.rs:323:5: 323:6" } List.nil))))))))))), terminator := { kind := (TerminatorKind.goto 4), span := "src/lib.rs:321:51: 325:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 28), span := "src/lib.rs:321:79: 321:80" } (List.cons { kind := (StatementKind.storageLive 33), span := "src/lib.rs:324:9: 324:23" } (List.cons { kind := (StatementKind.assign { local_ := 33, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 19, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:324:9: 324:23" } (List.cons { kind := (StatementKind.assign { local_ := 26, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 33, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 })), span := "src/lib.rs:324:9: 324:23" } (List.cons { kind := (StatementKind.storageDead 33), span := "src/lib.rs:324:22: 324:23" } List.nil))))), terminator := { kind := (TerminatorKind.goto 4), span := "src/lib.rs:321:51: 325:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 25, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 26, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:321:51: 325:6" } (List.cons { kind := (StatementKind.assign { local_ := 24, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 25, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793")), layoutIdx := 4 })), span := "src/lib.rs:321:51: 325:6" } (List.cons { kind := (StatementKind.storageDead 27), span := "src/lib.rs:325:5: 325:6" } (List.cons { kind := (StatementKind.storageDead 25), span := "src/lib.rs:325:5: 325:6" } (List.cons { kind := (StatementKind.storageDead 26), span := "src/lib.rs:325:6: 325:7" } (List.cons { kind := (StatementKind.storageLive 34), span := "src/lib.rs:326:9: 326:21" } (List.cons { kind := (StatementKind.storageLive 35), span := "src/lib.rs:326:53: 327:39" } (List.cons { kind := (StatementKind.storageLive 36), span := "src/lib.rs:326:53: 327:39" } (List.cons { kind := (StatementKind.storageLive 37), span := "src/lib.rs:326:53: 326:62" } (List.cons { kind := (StatementKind.storageLive 38), span := "src/lib.rs:326:53: 326:62" } (List.cons { kind := (StatementKind.assign { local_ := 38, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 3, projection := List.nil })), span := "src/lib.rs:326:53: 326:62" } (List.cons { kind := (StatementKind.assign { local_ := 37, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 38, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:326:53: 326:62" } (List.cons { kind := (StatementKind.assign { local_ := 36, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 37, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt49793")), layoutIdx := 4 })), span := "src/lib.rs:326:53: 327:39" } (List.cons { kind := (StatementKind.storageDead 37), span := "src/lib.rs:326:61: 326:62" } (List.cons { kind := (StatementKind.assign { local_ := 35, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 36, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:326:53: 327:39" } (List.cons { kind := (StatementKind.assign { local_ := 34, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 35, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt49793")), layoutIdx := 4 })), span := "src/lib.rs:326:53: 327:39" } (List.cons { kind := (StatementKind.storageDead 35), span := "src/lib.rs:327:38: 327:39" } (List.cons { kind := (StatementKind.storageDead 38), span := "src/lib.rs:327:39: 327:40" } (List.cons { kind := (StatementKind.storageDead 36), span := "src/lib.rs:327:39: 327:40" } (List.cons { kind := (StatementKind.storageLive 39), span := "src/lib.rs:328:9: 328:21" } (List.cons { kind := (StatementKind.storageLive 40), span := "src/lib.rs:328:29: 328:56" } (List.cons { kind := (StatementKind.storageLive 41), span := "src/lib.rs:328:29: 328:37" } (List.cons { kind := (StatementKind.assign { local_ := 41, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 24, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:328:29: 328:37" } (List.cons { kind := (StatementKind.storageLive 42), span := "src/lib.rs:328:46: 328:55" } (List.cons { kind := (StatementKind.assign { local_ := 42, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:328:46: 328:55" } List.nil))))))))))))))))))))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__AnnealVtableTrait49793::eval_vt" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793") List.nil)), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 41, projection := List.nil }) (List.cons (Operand.move { local_ := 42, projection := List.nil }) List.nil)) { local_ := 40, projection := List.nil } (Option.some 5) UnwindAction.continue_), span := "src/lib.rs:328:29: 328:56" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 42), span := "src/lib.rs:328:55: 328:56" } (List.cons { kind := (StatementKind.storageDead 41), span := "src/lib.rs:328:55: 328:56" } (List.cons { kind := (StatementKind.storageLive 43), span := "src/lib.rs:328:59: 328:76" } (List.cons { kind := (StatementKind.storageLive 44), span := "src/lib.rs:328:59: 328:67" } (List.cons { kind := (StatementKind.assign { local_ := 44, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 24, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:328:59: 328:67" } List.nil))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__AnnealVtableTrait49793::tag_vt" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793") List.nil)), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 44, projection := List.nil }) List.nil) { local_ := 43, projection := List.nil } (Option.some 6) UnwindAction.continue_), span := "src/lib.rs:328:59: 328:76" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 44), span := "src/lib.rs:328:75: 328:76" } (List.cons { kind := (StatementKind.assign { local_ := 39, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 40, projection := List.nil }) (Operand.move { local_ := 43, projection := List.nil }))), span := "src/lib.rs:328:29: 328:76" } (List.cons { kind := (StatementKind.storageDead 43), span := "src/lib.rs:328:75: 328:76" } (List.cons { kind := (StatementKind.storageDead 40), span := "src/lib.rs:328:75: 328:76" } (List.cons { kind := (StatementKind.storageLive 45), span := "src/lib.rs:329:9: 329:22" } (List.cons { kind := (StatementKind.storageLive 46), span := "src/lib.rs:329:30: 329:42" } (List.cons { kind := (StatementKind.assign { local_ := 46, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 34, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:329:30: 329:42" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__AnnealVtableAlt49793::eval_alt" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt49793") List.nil)), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 46, projection := List.nil }) List.nil) { local_ := 45, projection := List.nil } (Option.some 7) UnwindAction.continue_), span := "src/lib.rs:329:30: 329:53" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 46), span := "src/lib.rs:329:52: 329:53" } (List.cons { kind := (StatementKind.storageLive 47), span := "src/lib.rs:330:9: 330:22" } (List.cons { kind := (StatementKind.storageLive 48), span := "src/lib.rs:330:33: 330:79" } (List.cons { kind := (StatementKind.storageLive 49), span := "src/lib.rs:330:52: 330:64" } (List.cons { kind := (StatementKind.assign { local_ := 49, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 14, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:330:52: 330:64" } (List.cons { kind := (StatementKind.storageLive 50), span := "src/lib.rs:330:66: 330:78" } (List.cons { kind := (StatementKind.assign { local_ := 50, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 34, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:330:66: 330:78" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::ptr::addr_eq" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793") (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt49793") List.nil))), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 49, projection := List.nil }) (List.cons (Operand.move { local_ := 50, projection := List.nil }) List.nil)) { local_ := 48, projection := List.nil } (Option.some 8) UnwindAction.continue_), span := "src/lib.rs:330:33: 330:79" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 48, projection := List.nil }) { branches := (List.cons (0, 10) List.nil), otherwise := 9 }), span := "src/lib.rs:330:33: 330:79" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 50), span := "src/lib.rs:330:78: 330:79" } (List.cons { kind := (StatementKind.storageDead 49), span := "src/lib.rs:330:78: 330:79" } (List.cons { kind := (StatementKind.assign { local_ := 47, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:331:9: 331:13" } List.nil))), terminator := { kind := (TerminatorKind.goto 11), span := "src/lib.rs:330:30: 334:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 50), span := "src/lib.rs:330:78: 330:79" } (List.cons { kind := (StatementKind.storageDead 49), span := "src/lib.rs:330:78: 330:79" } (List.cons { kind := (StatementKind.assign { local_ := 47, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:333:9: 333:13" } List.nil))), terminator := { kind := (TerminatorKind.goto 11), span := "src/lib.rs:330:30: 334:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 48), span := "src/lib.rs:334:5: 334:6" } (List.cons { kind := (StatementKind.storageLive 51), span := "src/lib.rs:335:9: 335:22" } (List.cons { kind := (StatementKind.storageLive 52), span := "src/lib.rs:335:33: 335:81" } (List.cons { kind := (StatementKind.storageLive 53), span := "src/lib.rs:335:52: 335:64" } (List.cons { kind := (StatementKind.assign { local_ := 53, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 14, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:335:52: 335:64" } (List.cons { kind := (StatementKind.storageLive 54), span := "src/lib.rs:335:66: 335:80" } (List.cons { kind := (StatementKind.assign { local_ := 54, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 19, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:335:66: 335:80" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::ptr::addr_eq" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793") (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait49793") List.nil))), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 53, projection := List.nil }) (List.cons (Operand.move { local_ := 54, projection := List.nil }) List.nil)) { local_ := 52, projection := List.nil } (Option.some 12) UnwindAction.continue_), span := "src/lib.rs:335:33: 335:81" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 52, projection := List.nil }) { branches := (List.cons (0, 14) List.nil), otherwise := 13 }), span := "src/lib.rs:335:33: 335:81" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 54), span := "src/lib.rs:335:80: 335:81" } (List.cons { kind := (StatementKind.storageDead 53), span := "src/lib.rs:335:80: 335:81" } (List.cons { kind := (StatementKind.assign { local_ := 51, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:336:9: 336:13" } List.nil))), terminator := { kind := (TerminatorKind.goto 15), span := "src/lib.rs:335:30: 339:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 54), span := "src/lib.rs:335:80: 335:81" } (List.cons { kind := (StatementKind.storageDead 53), span := "src/lib.rs:335:80: 335:81" } (List.cons { kind := (StatementKind.assign { local_ := 51, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }))), span := "src/lib.rs:338:9: 338:13" } List.nil))), terminator := { kind := (TerminatorKind.goto 15), span := "src/lib.rs:335:30: 339:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 52), span := "src/lib.rs:339:5: 339:6" } (List.cons { kind := (StatementKind.storageLive 55), span := "src/lib.rs:340:5: 340:59" } (List.cons { kind := (StatementKind.storageLive 56), span := "src/lib.rs:340:5: 340:43" } (List.cons { kind := (StatementKind.storageLive 57), span := "src/lib.rs:340:5: 340:17" } (List.cons { kind := (StatementKind.assign { local_ := 57, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 39, projection := List.nil }))), span := "src/lib.rs:340:5: 340:17" } (List.cons { kind := (StatementKind.storageLive 58), span := "src/lib.rs:340:20: 340:43" } (List.cons { kind := (StatementKind.storageLive 59), span := "src/lib.rs:340:21: 340:34" } (List.cons { kind := (StatementKind.assign { local_ := 59, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 45, projection := List.nil }))), span := "src/lib.rs:340:21: 340:34" } (List.cons { kind := (StatementKind.assign { local_ := 60, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:340:20: 340:43" } List.nil))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 60, projection := List.nil }) true 16 UnwindAction.continue_), span := "src/lib.rs:340:20: 340:43" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 58, projection := List.nil } (Rvalue.binaryOp BinOp.shl (Operand.move { local_ := 59, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }))), span := "src/lib.rs:340:20: 340:43" } (List.cons { kind := (StatementKind.storageDead 59), span := "src/lib.rs:340:42: 340:43" } (List.cons { kind := (StatementKind.assign { local_ := 56, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 57, projection := List.nil }) (Operand.move { local_ := 58, projection := List.nil }))), span := "src/lib.rs:340:5: 340:43" } (List.cons { kind := (StatementKind.storageDead 58), span := "src/lib.rs:340:42: 340:43" } (List.cons { kind := (StatementKind.storageDead 57), span := "src/lib.rs:340:42: 340:43" } (List.cons { kind := (StatementKind.storageLive 61), span := "src/lib.rs:340:46: 340:59" } (List.cons { kind := (StatementKind.assign { local_ := 61, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 47, projection := List.nil }))), span := "src/lib.rs:340:46: 340:59" } (List.cons { kind := (StatementKind.assign { local_ := 55, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 56, projection := List.nil }) (Operand.move { local_ := 61, projection := List.nil }))), span := "src/lib.rs:340:5: 340:59" } (List.cons { kind := (StatementKind.storageDead 61), span := "src/lib.rs:340:58: 340:59" } (List.cons { kind := (StatementKind.storageDead 56), span := "src/lib.rs:340:58: 340:59" } (List.cons { kind := (StatementKind.storageLive 62), span := "src/lib.rs:340:62: 340:75" } (List.cons { kind := (StatementKind.assign { local_ := 62, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 51, projection := List.nil }))), span := "src/lib.rs:340:62: 340:75" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 55, projection := List.nil }) (Operand.move { local_ := 62, projection := List.nil }))), span := "src/lib.rs:340:5: 340:75" } (List.cons { kind := (StatementKind.storageDead 62), span := "src/lib.rs:340:74: 340:75" } (List.cons { kind := (StatementKind.storageDead 55), span := "src/lib.rs:340:74: 340:75" } (List.cons { kind := (StatementKind.storageDead 51), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 47), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 45), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 39), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 34), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 24), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 19), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 14), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:341:1: 341:2" } List.nil))))))))))))))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:341:2: 341:2" }, isCleanup := false } List.nil))))))))))))))))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0003.Driver

namespace F0003.RecvTraitEvalVt

/-! Captured `miri_diff_corpus` item `__AnnealVtableReceiver49793_as___AnnealVtableTrait49793_eval_vt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_3); StorageLive(_4); _4 = copy _2; StorageLive(_5); _5 = copy ((*_1).0: u32); _3 = BitXor(move _4, move _5); StorageDead(_5); StorageDead(_4); _0 = BitAnd(move _3, const 65535_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableTrait49793>::eval_vt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableTrait49793::eval_vt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableTrait49793>::eval_vt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", predicateKey := "miri_diff_corpus::__AnnealVtableAlt49793", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt49793"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", predicateKey := "miri_diff_corpus::__AnnealVtableTrait49793", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait49793"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableAlt49793>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver49793 as __AnnealVtableTrait49793>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver49793 as __AnnealVtableTrait49793>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableTrait49793>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableTrait49793>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt49793::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait49793::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait49793::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", slotIdx := 4 } List.nil))),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:289:9: 289:24" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:289:10: 289:11" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:289:10: 289:11" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:289:14: 289:23" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:289:14: 289:23" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 4, projection := List.nil }) (Operand.move { local_ := 5, projection := List.nil }))), span := "src/lib.rs:289:9: 289:24" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:289:23: 289:24" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:289:23: 289:24" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 65535, sizeBytes := 4 })) }))), span := "src/lib.rs:289:9: 289:36" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:289:35: 289:36" } List.nil)))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:290:6: 290:6" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0003.RecvTraitEvalVt

namespace F0003.RecvTraitTagVt

/-! Captured `miri_diff_corpus` item `__AnnealVtableReceiver49793_as___AnnealVtableTrait49793_tag_vt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = copy ((*_1).0: u32); _2 = BitAnd(move _3, const 63_u32); StorageDead(_3); _0 = BitXor(move _2, const 21_u32); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableTrait49793>::tag_vt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableTrait49793::tag_vt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableTrait49793>::tag_vt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", predicateKey := "miri_diff_corpus::__AnnealVtableAlt49793", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt49793"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", predicateKey := "miri_diff_corpus::__AnnealVtableTrait49793", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait49793"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableAlt49793>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver49793 as __AnnealVtableTrait49793>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver49793 as __AnnealVtableTrait49793>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableTrait49793>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableTrait49793>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt49793::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait49793::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait49793::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", slotIdx := 4 } List.nil))),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:292:9: 292:30" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:292:10: 292:19" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:292:10: 292:19" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 63, sizeBytes := 4 })) }))), span := "src/lib.rs:292:9: 292:30" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:292:29: 292:30" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 2, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 21, sizeBytes := 4 })) }))), span := "src/lib.rs:292:9: 292:40" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:292:39: 292:40" } List.nil))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:293:6: 293:6" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0003.RecvTraitTagVt

namespace F0003.RecvAltEvalAlt

/-! Captured `miri_diff_corpus` item `__AnnealVtableReceiver49793_as___AnnealVtableAlt49793_eval_alt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))) }

-- bb0: StorageLive(_2); _2 = copy ((*_1).0: u32); _3 = Lt(const 1_u32, const 32_u32); assert(move _3, "attempt to shift right by `{}`, which would overflow", const 1_u32) -> [success: bb1, unwind continue]
-- bb1: _0 = Shr(move _2, const 1_u32); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableAlt49793>::eval_alt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableAlt49793::eval_alt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableAlt49793>::eval_alt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", predicateKey := "miri_diff_corpus::__AnnealVtableAlt49793", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt49793"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", predicateKey := "miri_diff_corpus::__AnnealVtableTrait49793", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait49793"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableAlt49793>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver49793 as __AnnealVtableTrait49793>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver49793 as __AnnealVtableTrait49793>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableTrait49793>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableTrait49793>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt49793::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait49793::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait49793::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", slotIdx := 4 } List.nil))),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:305:9: 305:18" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:305:9: 305:18" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:305:9: 305:26" } List.nil)))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 3, projection := List.nil }) true 1 UnwindAction.continue_), span := "src/lib.rs:305:9: 305:26" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.shr (Operand.move { local_ := 2, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:305:9: 305:26" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:305:25: 305:26" } List.nil)), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:306:6: 306:6" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0003.RecvAltEvalAlt

namespace F0003.AltRecvTraitEvalVt

/-! Captured `miri_diff_corpus` item `__AnnealVtableAltReceiver49793_as___AnnealVtableTrait49793_eval_vt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 0 List.nil)) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))) }

-- bb0: StorageLive(_3); StorageLive(_4); StorageLive(_5); StorageLive(_6); _6 = copy _2; _7 = Lt(const 1_u32, const 32_u32); assert(move _7, "attempt to shift right by `{}`, which would overflow", const 1_u32) -> [success: bb1, unwind continue]
-- bb1: _5 = Shr(move _6, const 1_u32); StorageDead(_6); StorageLive(_8); _8 = copy ((*_1).0: u32); _4 = BitXor(move _5, move _8); StorageDead(_8); StorageDead(_5); StorageLive(_9); _9 = copy ((*_1).1: u32); _3 = BitXor(move _4, move _9); StorageDead(_9); StorageDead(_4); _0 = BitAnd(move _3, const 65535_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableAltReceiver49793 as __AnnealVtableTrait49793>::eval_vt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableTrait49793::eval_vt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver49793" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableAltReceiver49793 as __AnnealVtableTrait49793>::eval_vt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", predicateKey := "miri_diff_corpus::__AnnealVtableAlt49793", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt49793"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", predicateKey := "miri_diff_corpus::__AnnealVtableTrait49793", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait49793"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableAlt49793>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver49793 as __AnnealVtableTrait49793>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver49793 as __AnnealVtableTrait49793>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableTrait49793>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableTrait49793>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt49793::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait49793::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait49793::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", slotIdx := 4 } List.nil))),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver49793" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 7), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:297:9: 297:45" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:297:10: 297:32" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:297:10: 297:21" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:297:11: 297:12" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:297:11: 297:12" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:297:10: 297:21" } List.nil))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 7, projection := List.nil }) true 1 UnwindAction.continue_), span := "src/lib.rs:297:10: 297:21" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.binaryOp BinOp.shr (Operand.move { local_ := 6, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:297:10: 297:21" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:297:20: 297:21" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:297:24: 297:32" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:297:24: 297:32" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 5, projection := List.nil }) (Operand.move { local_ := 8, projection := List.nil }))), span := "src/lib.rs:297:10: 297:32" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:297:31: 297:32" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:297:31: 297:32" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:297:35: 297:44" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 1 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:297:35: 297:44" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 4, projection := List.nil }) (Operand.move { local_ := 9, projection := List.nil }))), span := "src/lib.rs:297:9: 297:45" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:297:44: 297:45" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:297:44: 297:45" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 65535, sizeBytes := 4 })) }))), span := "src/lib.rs:297:9: 297:57" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:297:56: 297:57" } List.nil)))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:298:6: 298:6" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0003.AltRecvTraitEvalVt

namespace F0003.AltRecvTraitTagVt

/-! Captured `miri_diff_corpus` item `__AnnealVtableAltReceiver49793_as___AnnealVtableTrait49793_tag_vt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 0 List.nil)) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_2); StorageLive(_3); StorageLive(_4); _4 = copy ((*_1).0: u32); StorageLive(_5); _5 = copy ((*_1).1: u32); _3 = BitXor(move _4, move _5); StorageDead(_5); StorageDead(_4); _2 = BitAnd(move _3, const 63_u32); StorageDead(_3); _0 = BitXor(move _2, const 42_u32); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableAltReceiver49793 as __AnnealVtableTrait49793>::tag_vt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableTrait49793::tag_vt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver49793" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableAltReceiver49793 as __AnnealVtableTrait49793>::tag_vt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", predicateKey := "miri_diff_corpus::__AnnealVtableAlt49793", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt49793"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", predicateKey := "miri_diff_corpus::__AnnealVtableTrait49793", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait49793"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableAlt49793>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver49793 as __AnnealVtableTrait49793>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver49793 as __AnnealVtableTrait49793>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver49793" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableTrait49793>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver49793 as __AnnealVtableTrait49793>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt49793::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt49793", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait49793::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait49793::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait49793", slotIdx := 4 } List.nil))),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver49793" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:300:9: 300:43" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:300:10: 300:32" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:300:11: 300:19" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:300:11: 300:19" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:300:22: 300:31" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 1 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:300:22: 300:31" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 4, projection := List.nil }) (Operand.move { local_ := 5, projection := List.nil }))), span := "src/lib.rs:300:10: 300:32" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:300:31: 300:32" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:300:31: 300:32" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 63, sizeBytes := 4 })) }))), span := "src/lib.rs:300:9: 300:43" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:300:42: 300:43" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 2, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 42, sizeBytes := 4 })) }))), span := "src/lib.rs:300:9: 300:53" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:300:52: 300:53" } List.nil))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:301:6: 301:6" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0003.AltRecvTraitTagVt

/-- Linked callee table of `finding_0003`: the driver and the 5 trait-method impls. -/
def F0003.linkedCallees : List CapturedMir :=
  [F0003.Driver.body, F0003.RecvTraitEvalVt.body, F0003.RecvTraitTagVt.body, F0003.RecvAltEvalAlt.body, F0003.AltRecvTraitEvalVt.body, F0003.AltRecvTraitTagVt.body]

set_option maxRecDepth 1000000 in
/-- Campaign #22 `finding_0003` end-to-end agreement with Miri (`MIRI_PASS:scalar:57:4`):
`miri_diff_corpus::pass_exact_div_valid__b17_c25` returns `57_u32` with the driver and the 5 trait-method
impls linked. -/
theorem F0003.miri_agreement :
    evalMirDiffTagBounded 512 F0003.Outer.body
      (initMachineStateWithMemoryAndCallees F0003.Outer.body [] emptyMemory F0003.linkedCallees) =
      .normalScalar 57 4 := by
  rfl

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0003`, only the driver linked (the 5 trait-method impls are absent)): the first virtual call resolves through the captured vtable to a method `DefPath` with no linked body, so the run stops at that `externalCall` (never a value).
Fault site: `src/lib.rs:328:29: 328:56`. -/
theorem F0003.control_noImpls :
    runC22 F0003.Outer.body [F0003.Driver.body] =
      .externalCall "miri_diff_corpus::<__AnnealVtableAltReceiver49793 as __AnnealVtableTrait49793>::eval_vt" ∧
    probeC22 F0003.Outer.body [F0003.Driver.body] =
      (.externalCall "miri_diff_corpus::<__AnnealVtableAltReceiver49793 as __AnnealVtableTrait49793>::eval_vt", "src/lib.rs:328:29: 328:56") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0003`, nothing linked): the outer function's call to the unlinked driver escapes as `externalCall` (never a value).
Fault site: `src/lib.rs:345:32: 345:68`. -/
theorem F0003.control_noDriver :
    runC22 F0003.Outer.body [] =
      .externalCall "miri_diff_corpus::__anneal_vt_driver_49793" ∧
    probeC22 F0003.Outer.body [] =
      (.externalCall "miri_diff_corpus::__anneal_vt_driver_49793", "src/lib.rs:345:32: 345:68") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0003`, `vtables` stripped from the outer body and from every linked body): the first `&T as &dyn Trait` unsizing finds no usable captured `(T, dyn Trait)` vtable (missing table, missing record, or `bodyVTablesConsistent` failure) and fails closed with `.unsupported` at that statement (never `.ub`, never a value).
Fault site: `src/lib.rs:317:55: 318:41`. -/
theorem F0003.control_stripped :
    runC22 (stripVTables F0003.Outer.body) (F0003.linkedCallees.map stripVTables) =
      .unsupported ∧
    probeC22 (stripVTables F0003.Outer.body) (F0003.linkedCallees.map stripVTables) =
      (.unsupported, "src/lib.rs:317:55: 318:41") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0003`, `vtables` stripped from every linked body (outer body intact)): the first `&T as &dyn Trait` unsizing finds no usable captured `(T, dyn Trait)` vtable (missing table, missing record, or `bodyVTablesConsistent` failure) and fails closed with `.unsupported` at that statement (never `.ub`, never a value).
Fault site: `src/lib.rs:317:55: 318:41`. -/
theorem F0003.control_strippedLinked :
    runC22 F0003.Outer.body (F0003.linkedCallees.map stripVTables) =
      .unsupported ∧
    probeC22 F0003.Outer.body (F0003.linkedCallees.map stripVTables) =
      (.unsupported, "src/lib.rs:317:55: 318:41") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0003`, unit-consistent forgery `forgeNonMethodSlot` applied to every body): the virtual call reads a vtable slot that is not a method (`.size` header slot, or past the end of the table): Miri's `get_vtable_entries`/`VtblEntry` dispatch raises UB (\"`dyn` call trying to call something that is not a method\" / out-of-bounds vtable index), and the TCB faults `.ub` at that call.
Fault site: `src/lib.rs:328:29: 328:56`. -/
theorem F0003.control_nonMethodSlot :
    runC22 (mapVTables forgeNonMethodSlot F0003.Outer.body) (F0003.linkedCallees.map (mapVTables forgeNonMethodSlot)) =
      .ub ∧
    probeC22 (mapVTables forgeNonMethodSlot F0003.Outer.body) (F0003.linkedCallees.map (mapVTables forgeNonMethodSlot)) =
      (.ub, "src/lib.rs:328:29: 328:56") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0003`, unit-consistent forgery `forgeTruncatedSlots` applied to every body): the virtual call reads a vtable slot that is not a method (`.size` header slot, or past the end of the table): Miri's `get_vtable_entries`/`VtblEntry` dispatch raises UB (\"`dyn` call trying to call something that is not a method\" / out-of-bounds vtable index), and the TCB faults `.ub` at that call.
Fault site: `src/lib.rs:328:59: 328:76`. -/
theorem F0003.control_truncatedSlots :
    runC22 (mapVTables forgeTruncatedSlots F0003.Outer.body) (F0003.linkedCallees.map (mapVTables forgeTruncatedSlots)) =
      .ub ∧
    probeC22 (mapVTables forgeTruncatedSlots F0003.Outer.body) (F0003.linkedCallees.map (mapVTables forgeTruncatedSlots)) =
      (.ub, "src/lib.rs:328:59: 328:76") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0003`, unit-consistent forgery `forgeWrongDynKey` applied to every body): the first `&T as &dyn Trait` unsizing finds no usable captured `(T, dyn Trait)` vtable (missing table, missing record, or `bodyVTablesConsistent` failure) and fails closed with `.unsupported` at that statement (never `.ub`, never a value).
Fault site: `src/lib.rs:317:55: 318:41`. -/
theorem F0003.control_wrongDynKey :
    runC22 (mapVTables forgeWrongDynKey F0003.Outer.body) (F0003.linkedCallees.map (mapVTables forgeWrongDynKey)) =
      .unsupported ∧
    probeC22 (mapVTables forgeWrongDynKey F0003.Outer.body) (F0003.linkedCallees.map (mapVTables forgeWrongDynKey)) =
      (.unsupported, "src/lib.rs:317:55: 318:41") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0003`, `forgeNonMethodSlot` applied to the driver's table only (linked bodies disagree)): the first `&T as &dyn Trait` unsizing finds no usable captured `(T, dyn Trait)` vtable (missing table, missing record, or `bodyVTablesConsistent` failure) and fails closed with `.unsupported` at that statement (never `.ub`, never a value).
Fault site: `src/lib.rs:317:55: 318:41`. -/
theorem F0003.control_inconsistent :
    runC22 F0003.Outer.body (mapVTables forgeNonMethodSlot F0003.Driver.body :: F0003.linkedCallees.drop 1) =
      .unsupported ∧
    probeC22 F0003.Outer.body (mapVTables forgeNonMethodSlot F0003.Driver.body :: F0003.linkedCallees.drop 1) =
      (.unsupported, "src/lib.rs:317:55: 318:41") :=
  ⟨by rfl, by rfl⟩

/-! ### Campaign #22 `finding_0004`: `miri_diff_corpus::safe_reborrow_then_parent_write__b20_c28` (Miri: `MIRI_PASS:scalar:5:4`).

Verbatim `layouts`/`body` definitions emitted by HEAD `anneal-rustc-capture` (`Runtime(PostCleanup)` MIR,
nightly-2026-06-01, `-Zmir-opt-level=0 -C debug-assertions=off -C overflow-checks=on`). -/

namespace F0004.Outer

/-! Captured `miri_diff_corpus` item `safe_reborrow_then_parent_write__b20_c28`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: StorageLive(_1); _1 = const 5_u32; StorageLive(_2); StorageLive(_3); _3 = &mut _1; _2 = &mut (*_3); StorageDead(_3); StorageLive(_4); StorageLive(_5); StorageLive(_6); _6 = &mut (*_2); _5 = &mut (*_6); StorageDead(_6); (*_5) = const 6_u32; _4 = const (); StorageDead(_5); StorageDead(_4); (*_2) = const 7_u32; StorageLive(_7); _7 = copy (*_2); StorageLive(_8); StorageLive(_9); StorageLive(_10); _10 = copy _1; _9 = BitAnd(move _10, const 65535_u32); StorageDead(_10); _8 = __anneal_vt_driver_5011(move _9, const 5_u32) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_9); StorageLive(_11); _11 = copy _7; StorageLive(_12); _12 = copy _8; _0 = BitXor(move _11, move _12); StorageDead(_12); StorageDead(_11); StorageDead(_8); StorageDead(_7); StorageDead(_2); StorageDead(_1); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::safe_reborrow_then_parent_write__b20_c28",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", predicateKey := "miri_diff_corpus::__AnnealVtableAlt5011", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt5011"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", predicateKey := "miri_diff_corpus::__AnnealVtableTrait5011", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait5011"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableAlt5011>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver5011 as __AnnealVtableTrait5011>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver5011 as __AnnealVtableTrait5011>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableTrait5011>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableTrait5011>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt5011::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait5011::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait5011::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", slotIdx := 4 } List.nil))),
    argCount := 0,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.uint UintTy.u32)), layoutIdx := 1 }, debugName := (Option.some "p") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.uint UintTy.u32)), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.uint UintTy.u32)), layoutIdx := 1 }, debugName := (Option.some "q") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.uint UintTy.u32)), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__tail___miri_vt_5011") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__miri_vt_5011") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 1), span := "src/lib.rs:344:9: 344:14" } (List.cons { kind := (StatementKind.assign { local_ := 1, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 5, sizeBytes := 4 })) }))), span := "src/lib.rs:344:22: 344:23" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:345:9: 345:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:345:23: 345:29" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.ref (BorrowKind.mut false) { local_ := 1, projection := List.nil })), span := "src/lib.rs:345:23: 345:29" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.ref (BorrowKind.mut false) { local_ := 3, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:345:23: 345:29" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:345:29: 345:30" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:346:5: 349:6" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:347:13: 347:14" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:347:27: 347:34" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.ref (BorrowKind.mut false) { local_ := 2, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:347:27: 347:34" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.ref (BorrowKind.mut false) { local_ := 6, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:347:27: 347:34" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:347:34: 347:35" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := (List.cons ProjectionElem.deref List.nil) } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 6, sizeBytes := 4 })) }))), span := "src/lib.rs:348:9: 348:15" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 2 }, val := ConstValue.zeroSized }))), span := "src/lib.rs:346:5: 349:6" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:349:5: 349:6" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:349:5: 349:6" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := (List.cons ProjectionElem.deref List.nil) } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 7, sizeBytes := 4 })) }))), span := "src/lib.rs:350:5: 350:11" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:351:9: 351:30" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := (List.cons ProjectionElem.deref List.nil) }))), span := "src/lib.rs:351:38: 351:40" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:352:9: 352:23" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:352:55: 352:77" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:352:55: 352:65" } (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:352:56: 352:57" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 10, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 65535, sizeBytes := 4 })) }))), span := "src/lib.rs:352:55: 352:77" } (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:352:76: 352:77" } List.nil)))))))))))))))))))))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__anneal_vt_driver_5011" List.nil), layoutIdx := 2 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 9, projection := List.nil }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 5, sizeBytes := 4 })) }) List.nil)) { local_ := 8, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:352:31: 352:84" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:352:83: 352:84" } (List.cons { kind := (StatementKind.storageLive 11), span := "src/lib.rs:353:5: 353:26" } (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 7, projection := List.nil }))), span := "src/lib.rs:353:5: 353:26" } (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:353:29: 353:52" } (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 8, projection := List.nil }))), span := "src/lib.rs:353:30: 353:44" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 11, projection := List.nil }) (Operand.move { local_ := 12, projection := List.nil }))), span := "src/lib.rs:353:5: 353:52" } (List.cons { kind := (StatementKind.storageDead 12), span := "src/lib.rs:353:51: 353:52" } (List.cons { kind := (StatementKind.storageDead 11), span := "src/lib.rs:353:51: 353:52" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:354:1: 354:2" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:354:1: 354:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:354:1: 354:2" } (List.cons { kind := (StatementKind.storageDead 1), span := "src/lib.rs:354:1: 354:2" } List.nil)))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:354:2: 354:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0004.Outer

namespace F0004.Driver

/-! Captured `miri_diff_corpus` item `__anneal_vt_driver_5011`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 0 List.nil)) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))))))) }

-- bb0: StorageLive(_3); StorageLive(_4); StorageLive(_5); _5 = copy _2; _4 = BitXor(move _5, const 17_u32); StorageDead(_5); _3 = __AnnealVtableReceiver5011 { bias: move _4 }; StorageDead(_4); StorageLive(_6); StorageLive(_7); StorageLive(_8); StorageLive(_9); _9 = copy _1; _8 = BitAnd(move _9, const 255_u32); StorageDead(_9); _7 = BitXor(move _8, const 17_u32); StorageDead(_8); StorageLive(_10); StorageLive(_11); StorageLive(_12); _12 = copy _2; _13 = Lt(const 1_u32, const 32_u32); assert(move _13, "attempt to shift right by `{}`, which would overflow", const 1_u32) -> [success: bb1, unwind continue]
-- bb1: _11 = Shr(move _12, const 1_u32); StorageDead(_12); _10 = BitXor(move _11, const 17_u32); StorageDead(_11); _6 = __AnnealVtableAltReceiver5011 { pad: move _7, bias: move _10 }; StorageDead(_10); StorageDead(_7); StorageLive(_14); StorageLive(_15); StorageLive(_16); StorageLive(_17); StorageLive(_18); _18 = &_3; _17 = &(*_18); _16 = move _17 as &dyn __AnnealVtableTrait5011 (PointerCoercion(Unsize, AsCast)); StorageDead(_17); _15 = &(*_16); _14 = move _15 as &dyn __AnnealVtableTrait5011 (PointerCoercion(Unsize, Implicit)); StorageDead(_15); StorageDead(_18); StorageDead(_16); StorageLive(_19); StorageLive(_20); StorageLive(_21); StorageLive(_22); StorageLive(_23); _23 = &_6; _22 = &(*_23); _21 = move _22 as &dyn __AnnealVtableTrait5011 (PointerCoercion(Unsize, AsCast)); StorageDead(_22); _20 = &(*_21); _19 = move _20 as &dyn __AnnealVtableTrait5011 (PointerCoercion(Unsize, Implicit)); StorageDead(_20); StorageDead(_23); StorageDead(_21); StorageLive(_24); StorageLive(_25); StorageLive(_26); StorageLive(_27); StorageLive(_28); StorageLive(_29); _29 = copy _1; _28 = BitAnd(move _29, const 1_u32); StorageDead(_29); _27 = Eq(move _28, const 0_u32); switchInt(move _27) -> [0: bb3, otherwise: bb2]
-- bb2: StorageDead(_28); StorageLive(_30); StorageLive(_31); StorageLive(_32); _32 = &(*_14); _31 = move _32 as &dyn __AnnealVtableTrait5011 (PointerCoercion(Unsize, Implicit)); StorageDead(_32); _30 = &(*_31); _26 = move _30 as &dyn __AnnealVtableTrait5011 (PointerCoercion(Unsize, Implicit)); StorageDead(_31); StorageDead(_30); goto -> bb4
-- bb3: StorageDead(_28); StorageLive(_33); _33 = &(*_19); _26 = move _33 as &dyn __AnnealVtableTrait5011 (PointerCoercion(Unsize, Implicit)); StorageDead(_33); goto -> bb4
-- bb4: _25 = &(*_26); _24 = move _25 as &dyn __AnnealVtableTrait5011 (PointerCoercion(Unsize, Implicit)); StorageDead(_27); StorageDead(_25); StorageDead(_26); StorageLive(_34); StorageLive(_35); StorageLive(_36); StorageLive(_37); StorageLive(_38); _38 = &_3; _37 = &(*_38); _36 = move _37 as &dyn __AnnealVtableAlt5011 (PointerCoercion(Unsize, AsCast)); StorageDead(_37); _35 = &(*_36); _34 = move _35 as &dyn __AnnealVtableAlt5011 (PointerCoercion(Unsize, Implicit)); StorageDead(_35); StorageDead(_38); StorageDead(_36); StorageLive(_39); StorageLive(_40); StorageLive(_41); _41 = &(*_24); StorageLive(_42); _42 = copy _1; _40 = <dyn __AnnealVtableTrait5011 as __AnnealVtableTrait5011>::eval_vt(move _41, move _42) -> [return: bb5, unwind continue]
-- bb5: StorageDead(_42); StorageDead(_41); StorageLive(_43); StorageLive(_44); _44 = &(*_24); _43 = <dyn __AnnealVtableTrait5011 as __AnnealVtableTrait5011>::tag_vt(move _44) -> [return: bb6, unwind continue]
-- bb6: StorageDead(_44); _39 = BitXor(move _40, move _43); StorageDead(_43); StorageDead(_40); StorageLive(_45); StorageLive(_46); _46 = &(*_34); _45 = <dyn __AnnealVtableAlt5011 as __AnnealVtableAlt5011>::eval_alt(move _46) -> [return: bb7, unwind continue]
-- bb7: StorageDead(_46); StorageLive(_47); StorageLive(_48); StorageLive(_49); _49 = &raw const (*_14); StorageLive(_50); _50 = &raw const (*_34); _48 = core::ptr::addr_eq::<dyn __AnnealVtableTrait5011, dyn __AnnealVtableAlt5011>(move _49, move _50) -> [return: bb8, unwind continue]
-- bb8: switchInt(move _48) -> [0: bb10, otherwise: bb9]
-- bb9: StorageDead(_50); StorageDead(_49); _47 = const 1_u32; goto -> bb11
-- bb10: StorageDead(_50); StorageDead(_49); _47 = const 0_u32; goto -> bb11
-- bb11: StorageDead(_48); StorageLive(_51); StorageLive(_52); StorageLive(_53); _53 = &raw const (*_14); StorageLive(_54); _54 = &raw const (*_19); _52 = core::ptr::addr_eq::<dyn __AnnealVtableTrait5011, dyn __AnnealVtableTrait5011>(move _53, move _54) -> [return: bb12, unwind continue]
-- bb12: switchInt(move _52) -> [0: bb14, otherwise: bb13]
-- bb13: StorageDead(_54); StorageDead(_53); _51 = const 0_u32; goto -> bb15
-- bb14: StorageDead(_54); StorageDead(_53); _51 = const 2_u32; goto -> bb15
-- bb15: StorageDead(_52); StorageLive(_55); StorageLive(_56); StorageLive(_57); _57 = copy _39; StorageLive(_58); StorageLive(_59); _59 = copy _45; _60 = Lt(const 2_u32, const 32_u32); assert(move _60, "attempt to shift left by `{}`, which would overflow", const 2_u32) -> [success: bb16, unwind continue]
-- bb16: _58 = Shl(move _59, const 2_u32); StorageDead(_59); _56 = BitXor(move _57, move _58); StorageDead(_58); StorageDead(_57); StorageLive(_61); _61 = copy _47; _55 = BitXor(move _56, move _61); StorageDead(_61); StorageDead(_56); StorageLive(_62); _62 = copy _51; _0 = BitXor(move _55, move _62); StorageDead(_62); StorageDead(_55); StorageDead(_51); StorageDead(_47); StorageDead(_45); StorageDead(_39); StorageDead(_34); StorageDead(_24); StorageDead(_19); StorageDead(_14); StorageDead(_6); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::__anneal_vt_driver_5011",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", predicateKey := "miri_diff_corpus::__AnnealVtableAlt5011", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt5011"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", predicateKey := "miri_diff_corpus::__AnnealVtableTrait5011", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait5011"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableAlt5011>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver5011 as __AnnealVtableTrait5011>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver5011 as __AnnealVtableTrait5011>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableTrait5011>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableTrait5011>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt5011::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait5011::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait5011::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", slotIdx := 4 } List.nil))),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_seed") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_bias") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil), layoutIdx := 1 }, debugName := (Option.some "__vt_rec") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver5011" List.nil), layoutIdx := 2 }, debugName := (Option.some "__vt_other") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 }, debugName := (Option.some "__vt_rec_dyn") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 }, debugName := (Option.some "__vt_other_dyn") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver5011" List.nil)), layoutIdx := 6 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver5011" List.nil)), layoutIdx := 6 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 }, debugName := (Option.some "__vt_dyn") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt5011")), layoutIdx := 4 }, debugName := (Option.some "__vt_dyn_alt") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt5011")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt5011")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_virtual") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_alt_bits") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt5011")), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_same_obj") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt5011")), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_diff_obj") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 13), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 60), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:310:9: 310:17" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:311:15: 311:32" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:311:15: 311:24" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:311:15: 311:24" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 5, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 17, sizeBytes := 4 })) }))), span := "src/lib.rs:311:15: 311:32" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:311:31: 311:32" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::__AnnealVtableReceiver5011" 0 Option.none) (List.cons (Operand.move { local_ := 4, projection := List.nil }) List.nil))), span := "src/lib.rs:310:48: 312:6" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:312:5: 312:6" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:313:9: 313:19" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:314:14: 314:43" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:314:14: 314:35" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:314:15: 314:24" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:314:15: 314:24" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 9, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 255, sizeBytes := 4 })) }))), span := "src/lib.rs:314:14: 314:35" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:314:34: 314:35" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 8, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 17, sizeBytes := 4 })) }))), span := "src/lib.rs:314:14: 314:43" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:314:42: 314:43" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:315:15: 315:42" } (List.cons { kind := (StatementKind.storageLive 11), span := "src/lib.rs:315:15: 315:34" } (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:315:16: 315:25" } (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:315:16: 315:25" } (List.cons { kind := (StatementKind.assign { local_ := 13, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:315:15: 315:34" } List.nil)))))))))))))))))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 13, projection := List.nil }) true 1 UnwindAction.continue_), span := "src/lib.rs:315:15: 315:34" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.binaryOp BinOp.shr (Operand.move { local_ := 12, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:315:15: 315:34" } (List.cons { kind := (StatementKind.storageDead 12), span := "src/lib.rs:315:33: 315:34" } (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 11, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 17, sizeBytes := 4 })) }))), span := "src/lib.rs:315:15: 315:42" } (List.cons { kind := (StatementKind.storageDead 11), span := "src/lib.rs:315:41: 315:42" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::__AnnealVtableAltReceiver5011" 0 Option.none) (List.cons (Operand.move { local_ := 7, projection := List.nil }) (List.cons (Operand.move { local_ := 10, projection := List.nil }) List.nil)))), span := "src/lib.rs:313:53: 316:6" } (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:316:5: 316:6" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:316:5: 316:6" } (List.cons { kind := (StatementKind.storageLive 14), span := "src/lib.rs:317:9: 317:21" } (List.cons { kind := (StatementKind.storageLive 15), span := "src/lib.rs:317:54: 318:40" } (List.cons { kind := (StatementKind.storageLive 16), span := "src/lib.rs:317:54: 318:40" } (List.cons { kind := (StatementKind.storageLive 17), span := "src/lib.rs:317:54: 317:63" } (List.cons { kind := (StatementKind.storageLive 18), span := "src/lib.rs:317:54: 317:63" } (List.cons { kind := (StatementKind.assign { local_ := 18, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 3, projection := List.nil })), span := "src/lib.rs:317:54: 317:63" } (List.cons { kind := (StatementKind.assign { local_ := 17, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 18, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:317:54: 317:63" } (List.cons { kind := (StatementKind.assign { local_ := 16, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 17, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 })), span := "src/lib.rs:317:54: 318:40" } (List.cons { kind := (StatementKind.storageDead 17), span := "src/lib.rs:317:62: 317:63" } (List.cons { kind := (StatementKind.assign { local_ := 15, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 16, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:317:54: 318:40" } (List.cons { kind := (StatementKind.assign { local_ := 14, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 15, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 })), span := "src/lib.rs:317:54: 318:40" } (List.cons { kind := (StatementKind.storageDead 15), span := "src/lib.rs:318:39: 318:40" } (List.cons { kind := (StatementKind.storageDead 18), span := "src/lib.rs:318:40: 318:41" } (List.cons { kind := (StatementKind.storageDead 16), span := "src/lib.rs:318:40: 318:41" } (List.cons { kind := (StatementKind.storageLive 19), span := "src/lib.rs:319:9: 319:23" } (List.cons { kind := (StatementKind.storageLive 20), span := "src/lib.rs:319:56: 320:40" } (List.cons { kind := (StatementKind.storageLive 21), span := "src/lib.rs:319:56: 320:40" } (List.cons { kind := (StatementKind.storageLive 22), span := "src/lib.rs:319:56: 319:67" } (List.cons { kind := (StatementKind.storageLive 23), span := "src/lib.rs:319:56: 319:67" } (List.cons { kind := (StatementKind.assign { local_ := 23, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 6, projection := List.nil })), span := "src/lib.rs:319:56: 319:67" } (List.cons { kind := (StatementKind.assign { local_ := 22, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 23, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:319:56: 319:67" } (List.cons { kind := (StatementKind.assign { local_ := 21, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 22, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 })), span := "src/lib.rs:319:56: 320:40" } (List.cons { kind := (StatementKind.storageDead 22), span := "src/lib.rs:319:66: 319:67" } (List.cons { kind := (StatementKind.assign { local_ := 20, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 21, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:319:56: 320:40" } (List.cons { kind := (StatementKind.assign { local_ := 19, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 20, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 })), span := "src/lib.rs:319:56: 320:40" } (List.cons { kind := (StatementKind.storageDead 20), span := "src/lib.rs:320:39: 320:40" } (List.cons { kind := (StatementKind.storageDead 23), span := "src/lib.rs:320:40: 320:41" } (List.cons { kind := (StatementKind.storageDead 21), span := "src/lib.rs:320:40: 320:41" } (List.cons { kind := (StatementKind.storageLive 24), span := "src/lib.rs:321:9: 321:17" } (List.cons { kind := (StatementKind.storageLive 25), span := "src/lib.rs:321:50: 325:6" } (List.cons { kind := (StatementKind.storageLive 26), span := "src/lib.rs:321:50: 325:6" } (List.cons { kind := (StatementKind.storageLive 27), span := "src/lib.rs:321:53: 321:79" } (List.cons { kind := (StatementKind.storageLive 28), span := "src/lib.rs:321:53: 321:71" } (List.cons { kind := (StatementKind.storageLive 29), span := "src/lib.rs:321:54: 321:63" } (List.cons { kind := (StatementKind.assign { local_ := 29, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:321:54: 321:63" } (List.cons { kind := (StatementKind.assign { local_ := 28, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 29, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:321:53: 321:71" } (List.cons { kind := (StatementKind.storageDead 29), span := "src/lib.rs:321:70: 321:71" } (List.cons { kind := (StatementKind.assign { local_ := 27, projection := List.nil } (Rvalue.binaryOp BinOp.eq (Operand.move { local_ := 28, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:321:53: 321:79" } List.nil))))))))))))))))))))))))))))))))))))))))))))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 27, projection := List.nil }) { branches := (List.cons (0, 3) List.nil), otherwise := 2 }), span := "src/lib.rs:321:53: 321:79" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 28), span := "src/lib.rs:321:78: 321:79" } (List.cons { kind := (StatementKind.storageLive 30), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.storageLive 31), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.storageLive 32), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.assign { local_ := 32, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 14, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.assign { local_ := 31, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 32, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 })), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.storageDead 32), span := "src/lib.rs:322:20: 322:21" } (List.cons { kind := (StatementKind.assign { local_ := 30, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 31, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.assign { local_ := 26, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 30, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 })), span := "src/lib.rs:322:9: 322:21" } (List.cons { kind := (StatementKind.storageDead 31), span := "src/lib.rs:323:5: 323:6" } (List.cons { kind := (StatementKind.storageDead 30), span := "src/lib.rs:323:5: 323:6" } List.nil))))))))))), terminator := { kind := (TerminatorKind.goto 4), span := "src/lib.rs:321:50: 325:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 28), span := "src/lib.rs:321:78: 321:79" } (List.cons { kind := (StatementKind.storageLive 33), span := "src/lib.rs:324:9: 324:23" } (List.cons { kind := (StatementKind.assign { local_ := 33, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 19, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:324:9: 324:23" } (List.cons { kind := (StatementKind.assign { local_ := 26, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 33, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 })), span := "src/lib.rs:324:9: 324:23" } (List.cons { kind := (StatementKind.storageDead 33), span := "src/lib.rs:324:22: 324:23" } List.nil))))), terminator := { kind := (TerminatorKind.goto 4), span := "src/lib.rs:321:50: 325:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 25, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 26, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:321:50: 325:6" } (List.cons { kind := (StatementKind.assign { local_ := 24, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 25, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011")), layoutIdx := 4 })), span := "src/lib.rs:321:50: 325:6" } (List.cons { kind := (StatementKind.storageDead 27), span := "src/lib.rs:325:5: 325:6" } (List.cons { kind := (StatementKind.storageDead 25), span := "src/lib.rs:325:5: 325:6" } (List.cons { kind := (StatementKind.storageDead 26), span := "src/lib.rs:325:6: 325:7" } (List.cons { kind := (StatementKind.storageLive 34), span := "src/lib.rs:326:9: 326:21" } (List.cons { kind := (StatementKind.storageLive 35), span := "src/lib.rs:326:52: 327:38" } (List.cons { kind := (StatementKind.storageLive 36), span := "src/lib.rs:326:52: 327:38" } (List.cons { kind := (StatementKind.storageLive 37), span := "src/lib.rs:326:52: 326:61" } (List.cons { kind := (StatementKind.storageLive 38), span := "src/lib.rs:326:52: 326:61" } (List.cons { kind := (StatementKind.assign { local_ := 38, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 3, projection := List.nil })), span := "src/lib.rs:326:52: 326:61" } (List.cons { kind := (StatementKind.assign { local_ := 37, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 38, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:326:52: 326:61" } (List.cons { kind := (StatementKind.assign { local_ := 36, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 37, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt5011")), layoutIdx := 4 })), span := "src/lib.rs:326:52: 327:38" } (List.cons { kind := (StatementKind.storageDead 37), span := "src/lib.rs:326:60: 326:61" } (List.cons { kind := (StatementKind.assign { local_ := 35, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 36, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:326:52: 327:38" } (List.cons { kind := (StatementKind.assign { local_ := 34, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "Unsize") (Operand.move { local_ := 35, projection := List.nil }) { kind := (RigidTy.ref Mutability.not (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt5011")), layoutIdx := 4 })), span := "src/lib.rs:326:52: 327:38" } (List.cons { kind := (StatementKind.storageDead 35), span := "src/lib.rs:327:37: 327:38" } (List.cons { kind := (StatementKind.storageDead 38), span := "src/lib.rs:327:38: 327:39" } (List.cons { kind := (StatementKind.storageDead 36), span := "src/lib.rs:327:38: 327:39" } (List.cons { kind := (StatementKind.storageLive 39), span := "src/lib.rs:328:9: 328:21" } (List.cons { kind := (StatementKind.storageLive 40), span := "src/lib.rs:328:29: 328:56" } (List.cons { kind := (StatementKind.storageLive 41), span := "src/lib.rs:328:29: 328:37" } (List.cons { kind := (StatementKind.assign { local_ := 41, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 24, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:328:29: 328:37" } (List.cons { kind := (StatementKind.storageLive 42), span := "src/lib.rs:328:46: 328:55" } (List.cons { kind := (StatementKind.assign { local_ := 42, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:328:46: 328:55" } List.nil))))))))))))))))))))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__AnnealVtableTrait5011::eval_vt" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011") List.nil)), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 41, projection := List.nil }) (List.cons (Operand.move { local_ := 42, projection := List.nil }) List.nil)) { local_ := 40, projection := List.nil } (Option.some 5) UnwindAction.continue_), span := "src/lib.rs:328:29: 328:56" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 42), span := "src/lib.rs:328:55: 328:56" } (List.cons { kind := (StatementKind.storageDead 41), span := "src/lib.rs:328:55: 328:56" } (List.cons { kind := (StatementKind.storageLive 43), span := "src/lib.rs:328:59: 328:76" } (List.cons { kind := (StatementKind.storageLive 44), span := "src/lib.rs:328:59: 328:67" } (List.cons { kind := (StatementKind.assign { local_ := 44, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 24, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:328:59: 328:67" } List.nil))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__AnnealVtableTrait5011::tag_vt" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011") List.nil)), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 44, projection := List.nil }) List.nil) { local_ := 43, projection := List.nil } (Option.some 6) UnwindAction.continue_), span := "src/lib.rs:328:59: 328:76" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 44), span := "src/lib.rs:328:75: 328:76" } (List.cons { kind := (StatementKind.assign { local_ := 39, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 40, projection := List.nil }) (Operand.move { local_ := 43, projection := List.nil }))), span := "src/lib.rs:328:29: 328:76" } (List.cons { kind := (StatementKind.storageDead 43), span := "src/lib.rs:328:75: 328:76" } (List.cons { kind := (StatementKind.storageDead 40), span := "src/lib.rs:328:75: 328:76" } (List.cons { kind := (StatementKind.storageLive 45), span := "src/lib.rs:329:9: 329:22" } (List.cons { kind := (StatementKind.storageLive 46), span := "src/lib.rs:329:30: 329:42" } (List.cons { kind := (StatementKind.assign { local_ := 46, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 34, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:329:30: 329:42" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__AnnealVtableAlt5011::eval_alt" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt5011") List.nil)), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 46, projection := List.nil }) List.nil) { local_ := 45, projection := List.nil } (Option.some 7) UnwindAction.continue_), span := "src/lib.rs:329:30: 329:53" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 46), span := "src/lib.rs:329:52: 329:53" } (List.cons { kind := (StatementKind.storageLive 47), span := "src/lib.rs:330:9: 330:22" } (List.cons { kind := (StatementKind.storageLive 48), span := "src/lib.rs:330:33: 330:79" } (List.cons { kind := (StatementKind.storageLive 49), span := "src/lib.rs:330:52: 330:64" } (List.cons { kind := (StatementKind.assign { local_ := 49, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 14, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:330:52: 330:64" } (List.cons { kind := (StatementKind.storageLive 50), span := "src/lib.rs:330:66: 330:78" } (List.cons { kind := (StatementKind.assign { local_ := 50, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 34, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:330:66: 330:78" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::ptr::addr_eq" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011") (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableAlt5011") List.nil))), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 49, projection := List.nil }) (List.cons (Operand.move { local_ := 50, projection := List.nil }) List.nil)) { local_ := 48, projection := List.nil } (Option.some 8) UnwindAction.continue_), span := "src/lib.rs:330:33: 330:79" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 48, projection := List.nil }) { branches := (List.cons (0, 10) List.nil), otherwise := 9 }), span := "src/lib.rs:330:33: 330:79" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 50), span := "src/lib.rs:330:78: 330:79" } (List.cons { kind := (StatementKind.storageDead 49), span := "src/lib.rs:330:78: 330:79" } (List.cons { kind := (StatementKind.assign { local_ := 47, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:331:9: 331:13" } List.nil))), terminator := { kind := (TerminatorKind.goto 11), span := "src/lib.rs:330:30: 334:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 50), span := "src/lib.rs:330:78: 330:79" } (List.cons { kind := (StatementKind.storageDead 49), span := "src/lib.rs:330:78: 330:79" } (List.cons { kind := (StatementKind.assign { local_ := 47, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:333:9: 333:13" } List.nil))), terminator := { kind := (TerminatorKind.goto 11), span := "src/lib.rs:330:30: 334:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 48), span := "src/lib.rs:334:5: 334:6" } (List.cons { kind := (StatementKind.storageLive 51), span := "src/lib.rs:335:9: 335:22" } (List.cons { kind := (StatementKind.storageLive 52), span := "src/lib.rs:335:33: 335:81" } (List.cons { kind := (StatementKind.storageLive 53), span := "src/lib.rs:335:52: 335:64" } (List.cons { kind := (StatementKind.assign { local_ := 53, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 14, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:335:52: 335:64" } (List.cons { kind := (StatementKind.storageLive 54), span := "src/lib.rs:335:66: 335:80" } (List.cons { kind := (StatementKind.assign { local_ := 54, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 19, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:335:66: 335:80" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::ptr::addr_eq" (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011") (List.cons (RigidTy.dynamic "miri_diff_corpus::__AnnealVtableTrait5011") List.nil))), layoutIdx := 8 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 53, projection := List.nil }) (List.cons (Operand.move { local_ := 54, projection := List.nil }) List.nil)) { local_ := 52, projection := List.nil } (Option.some 12) UnwindAction.continue_), span := "src/lib.rs:335:33: 335:81" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 52, projection := List.nil }) { branches := (List.cons (0, 14) List.nil), otherwise := 13 }), span := "src/lib.rs:335:33: 335:81" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 54), span := "src/lib.rs:335:80: 335:81" } (List.cons { kind := (StatementKind.storageDead 53), span := "src/lib.rs:335:80: 335:81" } (List.cons { kind := (StatementKind.assign { local_ := 51, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:336:9: 336:13" } List.nil))), terminator := { kind := (TerminatorKind.goto 15), span := "src/lib.rs:335:30: 339:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 54), span := "src/lib.rs:335:80: 335:81" } (List.cons { kind := (StatementKind.storageDead 53), span := "src/lib.rs:335:80: 335:81" } (List.cons { kind := (StatementKind.assign { local_ := 51, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }))), span := "src/lib.rs:338:9: 338:13" } List.nil))), terminator := { kind := (TerminatorKind.goto 15), span := "src/lib.rs:335:30: 339:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 52), span := "src/lib.rs:339:5: 339:6" } (List.cons { kind := (StatementKind.storageLive 55), span := "src/lib.rs:340:5: 340:59" } (List.cons { kind := (StatementKind.storageLive 56), span := "src/lib.rs:340:5: 340:43" } (List.cons { kind := (StatementKind.storageLive 57), span := "src/lib.rs:340:5: 340:17" } (List.cons { kind := (StatementKind.assign { local_ := 57, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 39, projection := List.nil }))), span := "src/lib.rs:340:5: 340:17" } (List.cons { kind := (StatementKind.storageLive 58), span := "src/lib.rs:340:20: 340:43" } (List.cons { kind := (StatementKind.storageLive 59), span := "src/lib.rs:340:21: 340:34" } (List.cons { kind := (StatementKind.assign { local_ := 59, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 45, projection := List.nil }))), span := "src/lib.rs:340:21: 340:34" } (List.cons { kind := (StatementKind.assign { local_ := 60, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:340:20: 340:43" } List.nil))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 60, projection := List.nil }) true 16 UnwindAction.continue_), span := "src/lib.rs:340:20: 340:43" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 58, projection := List.nil } (Rvalue.binaryOp BinOp.shl (Operand.move { local_ := 59, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }))), span := "src/lib.rs:340:20: 340:43" } (List.cons { kind := (StatementKind.storageDead 59), span := "src/lib.rs:340:42: 340:43" } (List.cons { kind := (StatementKind.assign { local_ := 56, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 57, projection := List.nil }) (Operand.move { local_ := 58, projection := List.nil }))), span := "src/lib.rs:340:5: 340:43" } (List.cons { kind := (StatementKind.storageDead 58), span := "src/lib.rs:340:42: 340:43" } (List.cons { kind := (StatementKind.storageDead 57), span := "src/lib.rs:340:42: 340:43" } (List.cons { kind := (StatementKind.storageLive 61), span := "src/lib.rs:340:46: 340:59" } (List.cons { kind := (StatementKind.assign { local_ := 61, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 47, projection := List.nil }))), span := "src/lib.rs:340:46: 340:59" } (List.cons { kind := (StatementKind.assign { local_ := 55, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 56, projection := List.nil }) (Operand.move { local_ := 61, projection := List.nil }))), span := "src/lib.rs:340:5: 340:59" } (List.cons { kind := (StatementKind.storageDead 61), span := "src/lib.rs:340:58: 340:59" } (List.cons { kind := (StatementKind.storageDead 56), span := "src/lib.rs:340:58: 340:59" } (List.cons { kind := (StatementKind.storageLive 62), span := "src/lib.rs:340:62: 340:75" } (List.cons { kind := (StatementKind.assign { local_ := 62, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 51, projection := List.nil }))), span := "src/lib.rs:340:62: 340:75" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 55, projection := List.nil }) (Operand.move { local_ := 62, projection := List.nil }))), span := "src/lib.rs:340:5: 340:75" } (List.cons { kind := (StatementKind.storageDead 62), span := "src/lib.rs:340:74: 340:75" } (List.cons { kind := (StatementKind.storageDead 55), span := "src/lib.rs:340:74: 340:75" } (List.cons { kind := (StatementKind.storageDead 51), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 47), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 45), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 39), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 34), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 24), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 19), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 14), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:341:1: 341:2" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:341:1: 341:2" } List.nil))))))))))))))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:341:2: 341:2" }, isCleanup := false } List.nil))))))))))))))))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0004.Driver

namespace F0004.RecvTraitEvalVt

/-! Captured `miri_diff_corpus` item `__AnnealVtableReceiver5011_as___AnnealVtableTrait5011_eval_vt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_3); StorageLive(_4); _4 = copy _2; StorageLive(_5); _5 = copy ((*_1).0: u32); _3 = BitXor(move _4, move _5); StorageDead(_5); StorageDead(_4); _0 = BitAnd(move _3, const 65535_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableTrait5011>::eval_vt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableTrait5011::eval_vt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableTrait5011>::eval_vt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", predicateKey := "miri_diff_corpus::__AnnealVtableAlt5011", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt5011"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", predicateKey := "miri_diff_corpus::__AnnealVtableTrait5011", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait5011"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableAlt5011>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver5011 as __AnnealVtableTrait5011>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver5011 as __AnnealVtableTrait5011>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableTrait5011>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableTrait5011>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt5011::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait5011::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait5011::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", slotIdx := 4 } List.nil))),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:289:9: 289:24" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:289:10: 289:11" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:289:10: 289:11" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:289:14: 289:23" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:289:14: 289:23" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 4, projection := List.nil }) (Operand.move { local_ := 5, projection := List.nil }))), span := "src/lib.rs:289:9: 289:24" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:289:23: 289:24" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:289:23: 289:24" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 65535, sizeBytes := 4 })) }))), span := "src/lib.rs:289:9: 289:36" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:289:35: 289:36" } List.nil)))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:290:6: 290:6" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0004.RecvTraitEvalVt

namespace F0004.RecvTraitTagVt

/-! Captured `miri_diff_corpus` item `__AnnealVtableReceiver5011_as___AnnealVtableTrait5011_tag_vt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = copy ((*_1).0: u32); _2 = BitAnd(move _3, const 63_u32); StorageDead(_3); _0 = BitXor(move _2, const 21_u32); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableTrait5011>::tag_vt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableTrait5011::tag_vt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableTrait5011>::tag_vt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", predicateKey := "miri_diff_corpus::__AnnealVtableAlt5011", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt5011"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", predicateKey := "miri_diff_corpus::__AnnealVtableTrait5011", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait5011"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableAlt5011>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver5011 as __AnnealVtableTrait5011>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver5011 as __AnnealVtableTrait5011>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableTrait5011>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableTrait5011>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt5011::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait5011::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait5011::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", slotIdx := 4 } List.nil))),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:292:9: 292:30" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:292:10: 292:19" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:292:10: 292:19" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 63, sizeBytes := 4 })) }))), span := "src/lib.rs:292:9: 292:30" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:292:29: 292:30" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 2, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 21, sizeBytes := 4 })) }))), span := "src/lib.rs:292:9: 292:40" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:292:39: 292:40" } List.nil))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:293:6: 293:6" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0004.RecvTraitTagVt

namespace F0004.RecvAltEvalAlt

/-! Captured `miri_diff_corpus` item `__AnnealVtableReceiver5011_as___AnnealVtableAlt5011_eval_alt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))) }

-- bb0: StorageLive(_2); _2 = copy ((*_1).0: u32); _3 = Lt(const 1_u32, const 32_u32); assert(move _3, "attempt to shift right by `{}`, which would overflow", const 1_u32) -> [success: bb1, unwind continue]
-- bb1: _0 = Shr(move _2, const 1_u32); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableAlt5011>::eval_alt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableAlt5011::eval_alt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableAlt5011>::eval_alt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", predicateKey := "miri_diff_corpus::__AnnealVtableAlt5011", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt5011"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", predicateKey := "miri_diff_corpus::__AnnealVtableTrait5011", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait5011"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableAlt5011>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver5011 as __AnnealVtableTrait5011>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver5011 as __AnnealVtableTrait5011>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableTrait5011>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableTrait5011>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt5011::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait5011::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait5011::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", slotIdx := 4 } List.nil))),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:305:9: 305:18" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:305:9: 305:18" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:305:9: 305:26" } List.nil)))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 3, projection := List.nil }) true 1 UnwindAction.continue_), span := "src/lib.rs:305:9: 305:26" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.shr (Operand.move { local_ := 2, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:305:9: 305:26" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:305:25: 305:26" } List.nil)), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:306:6: 306:6" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0004.RecvAltEvalAlt

namespace F0004.AltRecvTraitEvalVt

/-! Captured `miri_diff_corpus` item `__AnnealVtableAltReceiver5011_as___AnnealVtableTrait5011_eval_vt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 0 List.nil)) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))) }

-- bb0: StorageLive(_3); StorageLive(_4); StorageLive(_5); StorageLive(_6); _6 = copy _2; _7 = Lt(const 1_u32, const 32_u32); assert(move _7, "attempt to shift right by `{}`, which would overflow", const 1_u32) -> [success: bb1, unwind continue]
-- bb1: _5 = Shr(move _6, const 1_u32); StorageDead(_6); StorageLive(_8); _8 = copy ((*_1).0: u32); _4 = BitXor(move _5, move _8); StorageDead(_8); StorageDead(_5); StorageLive(_9); _9 = copy ((*_1).1: u32); _3 = BitXor(move _4, move _9); StorageDead(_9); StorageDead(_4); _0 = BitAnd(move _3, const 65535_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableAltReceiver5011 as __AnnealVtableTrait5011>::eval_vt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableTrait5011::eval_vt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver5011" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableAltReceiver5011 as __AnnealVtableTrait5011>::eval_vt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", predicateKey := "miri_diff_corpus::__AnnealVtableAlt5011", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt5011"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", predicateKey := "miri_diff_corpus::__AnnealVtableTrait5011", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait5011"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableAlt5011>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver5011 as __AnnealVtableTrait5011>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver5011 as __AnnealVtableTrait5011>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableTrait5011>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableTrait5011>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt5011::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait5011::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait5011::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", slotIdx := 4 } List.nil))),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver5011" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 7), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:297:9: 297:45" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:297:10: 297:32" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:297:10: 297:21" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:297:11: 297:12" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:297:11: 297:12" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:297:10: 297:21" } List.nil))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 7, projection := List.nil }) true 1 UnwindAction.continue_), span := "src/lib.rs:297:10: 297:21" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.binaryOp BinOp.shr (Operand.move { local_ := 6, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:297:10: 297:21" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:297:20: 297:21" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:297:24: 297:32" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:297:24: 297:32" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 5, projection := List.nil }) (Operand.move { local_ := 8, projection := List.nil }))), span := "src/lib.rs:297:10: 297:32" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:297:31: 297:32" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:297:31: 297:32" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:297:35: 297:44" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 1 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:297:35: 297:44" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 4, projection := List.nil }) (Operand.move { local_ := 9, projection := List.nil }))), span := "src/lib.rs:297:9: 297:45" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:297:44: 297:45" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:297:44: 297:45" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 65535, sizeBytes := 4 })) }))), span := "src/lib.rs:297:9: 297:57" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:297:56: 297:57" } List.nil)))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:298:6: 298:6" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0004.AltRecvTraitEvalVt

namespace F0004.AltRecvTraitTagVt

/-! Captured `miri_diff_corpus` item `__AnnealVtableAltReceiver5011_as___AnnealVtableTrait5011_tag_vt`. -/

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 0 List.nil)) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_2); StorageLive(_3); StorageLive(_4); _4 = copy ((*_1).0: u32); StorageLive(_5); _5 = copy ((*_1).1: u32); _3 = BitXor(move _4, move _5); StorageDead(_5); StorageDead(_4); _2 = BitAnd(move _3, const 63_u32); StorageDead(_3); _0 = BitXor(move _2, const 42_u32); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::<__AnnealVtableAltReceiver5011 as __AnnealVtableTrait5011>::tag_vt",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "miri_diff_corpus::__AnnealVtableTrait5011::tag_vt", args := (List.cons (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver5011" List.nil) List.nil) }, implPath := "miri_diff_corpus::<__AnnealVtableAltReceiver5011 as __AnnealVtableTrait5011>::tag_vt" } List.nil),
    dynTypes := (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", predicateKey := "miri_diff_corpus::__AnnealVtableAlt5011", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableAlt5011"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } (List.cons { dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", predicateKey := "miri_diff_corpus::__AnnealVtableTrait5011", principalTrait? := (Option.some "miri_diff_corpus::__AnnealVtableTrait5011"), typeArgs := List.nil, assocBindings := List.nil, autoTraits := List.nil, hasUnresolvedExistentialBinder := false, supertraitOutlivesOk := true } List.nil)),
    vtables := (List.cons { vtableId := 0, vtableAllocId := 16384, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableAlt5011>::eval_alt" List.nil) List.nil)))) } (List.cons { vtableId := 1, vtableAllocId := 16385, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", sizeBytes := 8, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver5011 as __AnnealVtableTrait5011>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableAltReceiver5011 as __AnnealVtableTrait5011>::tag_vt" List.nil) List.nil))))) } (List.cons { vtableId := 2, vtableAllocId := 16386, concreteTy := (RigidTy.adt "miri_diff_corpus::__AnnealVtableReceiver5011" List.nil), dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", sizeBytes := 4, alignBytes := 4, isUninhabited := false, primarySuperVTableId? := Option.none, slots := (List.cons (CapturedVTableSlot.dropInPlace Option.none) (List.cons CapturedVTableSlot.size (List.cons CapturedVTableSlot.align (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableTrait5011>::eval_vt" List.nil) (List.cons (CapturedVTableSlot.method "miri_diff_corpus::<__AnnealVtableReceiver5011 as __AnnealVtableTrait5011>::tag_vt" List.nil) List.nil))))) } List.nil))),
    virtualMethods := (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableAlt5011::eval_alt", dynKey := "miri_diff_corpus::__AnnealVtableAlt5011", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait5011::eval_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", slotIdx := 3 } (List.cons { methodDefPath := "miri_diff_corpus::__AnnealVtableTrait5011::tag_vt", dynKey := "miri_diff_corpus::__AnnealVtableTrait5011", slotIdx := 4 } List.nil))),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::__AnnealVtableAltReceiver5011" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:300:9: 300:43" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:300:10: 300:32" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:300:11: 300:19" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:300:11: 300:19" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:300:22: 300:31" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 1 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:300:22: 300:31" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 4, projection := List.nil }) (Operand.move { local_ := 5, projection := List.nil }))), span := "src/lib.rs:300:10: 300:32" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:300:31: 300:32" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:300:31: 300:32" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 63, sizeBytes := 4 })) }))), span := "src/lib.rs:300:9: 300:43" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:300:42: 300:43" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 2, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 42, sizeBytes := 4 })) }))), span := "src/lib.rs:300:9: 300:53" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:300:52: 300:53" } List.nil))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:301:6: 301:6" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end F0004.AltRecvTraitTagVt

/-- Linked callee table of `finding_0004`: the driver and the 5 trait-method impls. -/
def F0004.linkedCallees : List CapturedMir :=
  [F0004.Driver.body, F0004.RecvTraitEvalVt.body, F0004.RecvTraitTagVt.body, F0004.RecvAltEvalAlt.body, F0004.AltRecvTraitEvalVt.body, F0004.AltRecvTraitTagVt.body]

set_option maxRecDepth 1000000 in
/-- Campaign #22 `finding_0004` end-to-end agreement with Miri (`MIRI_PASS:scalar:5:4`):
`miri_diff_corpus::safe_reborrow_then_parent_write__b20_c28` returns `5_u32` with the driver and the 5 trait-method
impls linked. -/
theorem F0004.miri_agreement :
    evalMirDiffTagBounded 512 F0004.Outer.body
      (initMachineStateWithMemoryAndCallees F0004.Outer.body [] emptyMemory F0004.linkedCallees) =
      .normalScalar 5 4 := by
  rfl

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0004`, only the driver linked (the 5 trait-method impls are absent)): the first virtual call resolves through the captured vtable to a method `DefPath` with no linked body, so the run stops at that `externalCall` (never a value).
Fault site: `src/lib.rs:328:29: 328:56`. -/
theorem F0004.control_noImpls :
    runC22 F0004.Outer.body [F0004.Driver.body] =
      .externalCall "miri_diff_corpus::<__AnnealVtableAltReceiver5011 as __AnnealVtableTrait5011>::eval_vt" ∧
    probeC22 F0004.Outer.body [F0004.Driver.body] =
      (.externalCall "miri_diff_corpus::<__AnnealVtableAltReceiver5011 as __AnnealVtableTrait5011>::eval_vt", "src/lib.rs:328:29: 328:56") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0004`, nothing linked): the outer function's call to the unlinked driver escapes as `externalCall` (never a value).
Fault site: `src/lib.rs:352:31: 352:84`. -/
theorem F0004.control_noDriver :
    runC22 F0004.Outer.body [] =
      .externalCall "miri_diff_corpus::__anneal_vt_driver_5011" ∧
    probeC22 F0004.Outer.body [] =
      (.externalCall "miri_diff_corpus::__anneal_vt_driver_5011", "src/lib.rs:352:31: 352:84") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0004`, `vtables` stripped from the outer body and from every linked body): the first `&T as &dyn Trait` unsizing finds no usable captured `(T, dyn Trait)` vtable (missing table, missing record, or `bodyVTablesConsistent` failure) and fails closed with `.unsupported` at that statement (never `.ub`, never a value).
Fault site: `src/lib.rs:317:54: 318:40`. -/
theorem F0004.control_stripped :
    runC22 (stripVTables F0004.Outer.body) (F0004.linkedCallees.map stripVTables) =
      .unsupported ∧
    probeC22 (stripVTables F0004.Outer.body) (F0004.linkedCallees.map stripVTables) =
      (.unsupported, "src/lib.rs:317:54: 318:40") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0004`, `vtables` stripped from every linked body (outer body intact)): the first `&T as &dyn Trait` unsizing finds no usable captured `(T, dyn Trait)` vtable (missing table, missing record, or `bodyVTablesConsistent` failure) and fails closed with `.unsupported` at that statement (never `.ub`, never a value).
Fault site: `src/lib.rs:317:54: 318:40`. -/
theorem F0004.control_strippedLinked :
    runC22 F0004.Outer.body (F0004.linkedCallees.map stripVTables) =
      .unsupported ∧
    probeC22 F0004.Outer.body (F0004.linkedCallees.map stripVTables) =
      (.unsupported, "src/lib.rs:317:54: 318:40") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0004`, unit-consistent forgery `forgeNonMethodSlot` applied to every body): the virtual call reads a vtable slot that is not a method (`.size` header slot, or past the end of the table): Miri's `get_vtable_entries`/`VtblEntry` dispatch raises UB (\"`dyn` call trying to call something that is not a method\" / out-of-bounds vtable index), and the TCB faults `.ub` at that call.
Fault site: `src/lib.rs:328:29: 328:56`. -/
theorem F0004.control_nonMethodSlot :
    runC22 (mapVTables forgeNonMethodSlot F0004.Outer.body) (F0004.linkedCallees.map (mapVTables forgeNonMethodSlot)) =
      .ub ∧
    probeC22 (mapVTables forgeNonMethodSlot F0004.Outer.body) (F0004.linkedCallees.map (mapVTables forgeNonMethodSlot)) =
      (.ub, "src/lib.rs:328:29: 328:56") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0004`, unit-consistent forgery `forgeTruncatedSlots` applied to every body): the virtual call reads a vtable slot that is not a method (`.size` header slot, or past the end of the table): Miri's `get_vtable_entries`/`VtblEntry` dispatch raises UB (\"`dyn` call trying to call something that is not a method\" / out-of-bounds vtable index), and the TCB faults `.ub` at that call.
Fault site: `src/lib.rs:328:59: 328:76`. -/
theorem F0004.control_truncatedSlots :
    runC22 (mapVTables forgeTruncatedSlots F0004.Outer.body) (F0004.linkedCallees.map (mapVTables forgeTruncatedSlots)) =
      .ub ∧
    probeC22 (mapVTables forgeTruncatedSlots F0004.Outer.body) (F0004.linkedCallees.map (mapVTables forgeTruncatedSlots)) =
      (.ub, "src/lib.rs:328:59: 328:76") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0004`, unit-consistent forgery `forgeWrongDynKey` applied to every body): the first `&T as &dyn Trait` unsizing finds no usable captured `(T, dyn Trait)` vtable (missing table, missing record, or `bodyVTablesConsistent` failure) and fails closed with `.unsupported` at that statement (never `.ub`, never a value).
Fault site: `src/lib.rs:317:54: 318:40`. -/
theorem F0004.control_wrongDynKey :
    runC22 (mapVTables forgeWrongDynKey F0004.Outer.body) (F0004.linkedCallees.map (mapVTables forgeWrongDynKey)) =
      .unsupported ∧
    probeC22 (mapVTables forgeWrongDynKey F0004.Outer.body) (F0004.linkedCallees.map (mapVTables forgeWrongDynKey)) =
      (.unsupported, "src/lib.rs:317:54: 318:40") :=
  ⟨by rfl, by rfl⟩

set_option maxRecDepth 1000000 in
/-- Negative control (`finding_0004`, `forgeNonMethodSlot` applied to the driver's table only (linked bodies disagree)): the first `&T as &dyn Trait` unsizing finds no usable captured `(T, dyn Trait)` vtable (missing table, missing record, or `bodyVTablesConsistent` failure) and fails closed with `.unsupported` at that statement (never `.ub`, never a value).
Fault site: `src/lib.rs:317:54: 318:40`. -/
theorem F0004.control_inconsistent :
    runC22 F0004.Outer.body (mapVTables forgeNonMethodSlot F0004.Driver.body :: F0004.linkedCallees.drop 1) =
      .unsupported ∧
    probeC22 F0004.Outer.body (mapVTables forgeNonMethodSlot F0004.Driver.body :: F0004.linkedCallees.drop 1) =
      (.unsupported, "src/lib.rs:317:54: 318:40") :=
  ⟨by rfl, by rfl⟩


end Anneal.Mir.DynTraitVTableTests.Campaign22

/-! ## §5. Constructive Axiom Audit of `Anneal.Mir.DynTraitVTableBundle` & Test Module -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let constructiveDecls : List Name :=
    [ ``Anneal.Mir.DynTraitVTableBundle.dvCodec,
      ``Anneal.Mir.DynTraitVTableBundle.dvCodec_tight,
      ``Anneal.Mir.DynTraitVTableBundle.allDvModes_complete,
      ``Anneal.Mir.DynTraitVTableBundle.allDvMrModes_complete,
      ``Anneal.Mir.DynTraitVTableBundle.allDvLmModes_complete,
      ``Anneal.Mir.DynTraitVTableBundle.allDvVariants_complete,
      ``Anneal.Mir.DynTraitVTableBundle.allDvCases_complete,
      ``Anneal.Mir.DynTraitVTableBundle.dvAnnealEval,
      ``Anneal.Mir.DynTraitVTableBundle.dvAnnealEval_eq,
      ``Anneal.Mir.DynTraitVTableBundle.dvAnnealEval_funext,
      ``Anneal.Mir.DynTraitVTableBundle.mrAuthority,
      ``Anneal.Mir.DynTraitVTableBundle.mrAuthority_denoteConsistent,
      ``Anneal.Mir.DynTraitVTableBundle.mrAuthority_verdict_eq,
      ``Anneal.Mir.DynTraitVTableBundle.mrVerdictFn_funext,
      ``Anneal.Mir.DynTraitVTableBundle.mrSide_check,
      ``Anneal.Mir.DynTraitVTableBundle.mrVariantSide_check,
      ``Anneal.Mir.DynTraitVTableBundle.lmCheckOf_congr,
      ``Anneal.Mir.DynTraitVTableBundle.lmVariantCheckOf_congr,
      ``Anneal.Mir.DynTraitVTableBundle.bundleOf,
      ``Anneal.Mir.DynTraitVTableBundle.variantBundleOf,
      ``Anneal.Mir.DynTraitVTableBundle.threeWayNormalAgreement,
      ``Anneal.Mir.DynTraitVTableBundle.crossAuthorityFaultEquiv,
      ``Anneal.Mir.DynTraitVTableBundle.exactBehaviorEq_both,
      ``Anneal.Mir.DynTraitVTableBundle.mr_modeSensitivity_present,
      ``Anneal.Mir.DynTraitVTableBundle.lm_modeSensitivity_present,
      ``Anneal.Mir.DynTraitVTableBundle.variant_bundle_claims,
      ``Anneal.Mir.DynTraitVTableBundle.dv_variant_outcomes_distinct,
      ``Anneal.Mir.DynTraitVTableBundle.ep2_dyn_trait_vtable_capstone ]
  for d in constructiveDecls do
    let axs ← liftCoreM <| Lean.collectAxioms d
    for a in axs do
      unless a == ``propext || a == ``Quot.sound do
        throwError "constructive audit failure: {d} uses non-constructive axiom {a}"
  -- The `C7` dialect-homomorphism and `C8` Campaign #22 theorems must be present, and no
  -- `C8` theorem may use `Classical.choice`.
  let c8 := `Anneal.Mir.DynTraitVTableTests.Campaign22
  let c7 := `Anneal.Mir.DynTraitVTableTests.Hom
  let mut c8Count : Nat := 0
  for f in [`F0000, `F0001, `F0002, `F0003, `F0004] do
    for t in [`miri_agreement, `control_noImpls, `control_noDriver, `control_stripped,
              `control_strippedLinked, `control_nonMethodSlot, `control_truncatedSlots,
              `control_wrongDynKey, `control_inconsistent] do
      let n := c8 ++ f ++ t
      let some (.thmInfo _) := env.find? n | throwError "C8 audit: {n} missing"
      for a in ← liftCoreM <| Lean.collectAxioms n do
        unless a == ``propext || a == ``Quot.sound do
          throwError "C8 audit failure: {n} uses axiom {a}"
      c8Count := c8Count + 1
  let c7Required : List Name :=
    [ `homUint_injective, `homInt_injective, `homFloat_injective, `homMut_injective,
      `homSafety_injective, `homCallConv_injective, `homTy_injective, `homTys_injective,
      `homSlot_injective, `homVTable_injective, `homScalar_injective, `homPtr_injective,
      `homValue_injective, `homValues_injective,
      `wfVTableEntry_hom, `resolveUpcastVTable?_hom, `dynUnsizeTarget?_hom,
      `classifyDynReceiver?_hom, `narrowDynReceiver_hom, `unpackDynReceiver?_hom,
      `dynVTableEnv?_opt_hom, `dynVTableEnv?_hom,
      `checkDynVTablePtr_opt_hom, `checkDynVTablePtr_hom,
      `evalThinToDynUnsize_raw_hom, `defPathsSubset_hom, `evalDynToDynUnsize_raw_hom,
      `dynRefDataValid_scalar_hom,
      `evalThinToDynUnsize_scalarRef_hom, `evalDynToDynUnsize_scalarRef_hom,
      `evalDynSizeAlignOfVal_hom, `evalAddrEqCall_hom,
      `addrRel_of_root_borrows, `addrRel_of_no_borrows,
      `wState_dynMemRel, `wBare_dynMemRel, `wBody_optBodyRel, `wState_addrRel,
      `wBorrowState_addrRel, `wUpState_dynMemRel,
      `witness_written_values, `checkDynVTablePtr_opt_witness,
      `unpackDynReceiver?_witness, `evalDynToDynUnsize_raw_witness,
      `evalScalarRefUnsize_witness_32bit_uninhabited,
      `evalThinToDynUnsize_raw_witness_32bit_64bit,
      `dynRefDataValid_scalar_witness_32bit_uninhabited,
      `evalDynSizeAlignOfVal_witness_write, `evalDynSizeAlignOfVal_witness_ub,
      `evalDynSizeAlignOfVal_witness_unsupported, `evalAddrEqCall_witness_write,
      `evalAddrEqCall_witness_ub, `evalAddrEqCall_witness_nonempty_borrows ]
  for t in c7Required do
    let some (.thmInfo _) := env.find? (c7 ++ t) | throwError "C7 audit: {c7 ++ t} missing"
    for a in ← liftCoreM <| Lean.collectAxioms (c7 ++ t) do
      unless a == ``propext || a == ``Quot.sound do
        throwError "C7 audit failure: {c7 ++ t} uses axiom {a}"
  let rec isTrivialProp : Expr → Bool
    | .forallE _ _ body _ => isTrivialProp body
    | .letE _ _ _ body _ => isTrivialProp body
    | e =>
      if e.isConstOf ``True then true
      else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
      else if e.isAppOfArity ``Iff 2 then e.appFn!.appArg! == e.appArg!
      else false
  let mut moduleCount : Nat := 0
  for (c, ci) in env.constants.map₂.toList do
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "test audit failure: {c} uses sorryAx"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "test audit failure: {c} uses non-standard axiom {a}"
    if !c.isInternal then
      if let .thmInfo v := ci then
        if isTrivialProp v.type then
          throwError "test audit failure: {c} is a trivial theorem"
    moduleCount := moduleCount + 1
  logInfo m!"dv constructive audit: verified {constructiveDecls.length} bundle declarations in [propext, Quot.sound] (0 Classical.choice, 0 sorryAx, 0 ofReduceBool), {c8Count} C8 theorems and {c7Required.length} C7 theorems in [propext, Quot.sound], {moduleCount} module declarations in standard axioms (0 trivial)"
