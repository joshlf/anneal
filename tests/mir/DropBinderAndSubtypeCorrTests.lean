/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Anneal.Mir.DropBinderAndSubtypeBundle
import MiniRustSpec.DropBinderAndSubtypeMR

/-!
# Episode 2 Dual-Authority Correspondence Tests & Cross-Root Kernel Bridge

Verifies all 8 already-trusted MIR variants end-to-end across BOTH authorities:

1. **Concrete Positive, UB, Flip-Direction, and Mode-Sensitivity Witnesses**
   covering `StatementKind.coverage`, `StatementKind.backwardIncompatibleDropHint`,
   `TerminatorKind.drop` (whole-local, projected sub-place, dead-local UB,
   active-protector `BasicMemory` vs. `TreeBorrowsMemory` mode sensitivity,
   cleanup-block unwind, and post-elaboration no-glue phase boundary),
   `Rvalue.shallowInitBox`, `Rvalue.wrapUnsafeBinder`, `CastKind.subtype`,
   `AggregateKind.rawPtr` (thin `()` and wide `[u32]`/`str` exercising Episode 1's
   `UnOp.GetMetadata` / `ComputeSize` / `ComputeAlign`), and `AggregateKind.closure`.
2. **Cross-Root Dual-Authority Kernel Bridge (`run_cmd`)**:
   Loads BOTH `.lake/build/lib/lean` (root Lake: `Anneal.Mir.DropBinderAndSubtypeBundle`
   and `MiniRustSpec.DropBinderAndSubtypeMR`) and `examples/.lake/build/lib/lean`
   (`LeanMiriSpec.DropBinderAndSubtypeLM`) into a fresh Lean kernel environment,
   constructs the genuine LeanMiri `ObsAuthority` directly over
   `LeanMiriSpec.DropBinderAndSubtypeLM.ep2LmObserve` (stepping unmodified vendored
   `Miri.Interpreter.Step.step`), submits and kernel-checks:
   - `lmAuthority` + `lmAuthority_denoteConsistent`,
   - `lmCheck` (unified 64-key certificate) + all 8 per-variant `lmVariantCheck`s,
   - closed unified `DualCorrespondenceBundle` + all 8 per-variant bundles,
   - instantiated `threeWayNormalAgreement`, `crossAuthorityFaultEquiv`,
     `exactBehaviorEq_both`, `lm_modeSensitivity_present`, and per-variant claims
     + flip-direction guards (`mrFlip.verdict_flips`, `lmFlip.verdict_flips`),
   - **definitional `rfl` fixture locks** proving every `CapturedMir` fixture in
     `MiniRustSpec.DropBinderAndSubtypeMR` / `Anneal.Mir.DropBinderAndSubtypeBundle`
     is definitionally equal to the fixture executed in `LeanMiriSpec.DropBinderAndSubtypeLM`,
   - **negative controls** (forged ill-typed theorem, negated LM certificate,
     mode-inverted LM authority, colliding `denote` table, swapped fixture lock)
     all verified to be REJECTED by the kernel,
   - **transitive constant reachability** proving the closed dual-authority bundles
     genuinely reach `Trusted.Rustc.V2026_06_01.MirSemantics.{stepMirFn, evalStmt,
     evalRvalue, evalTerminator}`, `MiniRustSpec.Interp.{steps, stepsTB, evalUnOpM}`,
     AND vendored `Miri.Interpreter.{Step.step, evalRvalueIntoPlace, writeAggregate,
     Cast.cast, ControlFlow.evalTerminator}`!
3. **Constructive Axiom & Zero-`sorry` Audit**:
   Verifies that `Anneal.Mir.DropBinderAndSubtypeBundle` codecs and core lemmas
   depend ONLY on `[propext, Quot.sound]` (zero `Classical.choice`, zero `sorryAx`,
   zero `Lean.ofReduceBool`), and that every cross-root declaration uses only
   standard axioms with zero `sorryAx` and zero `ofReduceBool`, plus self-tests
   confirming the auditor catches `sorryAx` and `ofReduceBool`.
-/

namespace Anneal.Mir.DropBinderAndSubtypeCorrTests

open Anneal.DualCorrespondenceBundle
open Anneal.Mir.DropBinderAndSubtypeBundle
open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.Interp
open MiniRustSpec.LibSpecr hiding Name
open MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.Witness hiding constU32
open MiniRustSpec.Correspondence.RefWitness
open MiniRustSpec.Correspondence.TbWitness
open MiniRustSpec.UnwindSetDiscrAndFnPtrMR
open MiniRustSpec.DropBinderAndSubtypeMR

/-! ## §1. Concrete Witnesses, Flip-Direction Guards, & Mode Sensitivity (Root Lake) -/

/-- Constructive codec laws & tight validity witness for `ep2Codec`. -/
theorem ep2_codec_constructive_laws :
    ep2Codec.decode (ep2Codec.encode (.u32Val 42)) = some (.u32Val 42) ∧
    ep2Codec.decode (ep2Codec.encode (.ptrAlloc 5)) = some (.ptrAlloc 5) ∧
    ep2Codec.decode (ep2Codec.encode (.closureCap 7 1)) = some (.closureCap 7 1) ∧
    ep2Codec.decode (99, 0, 0) = none ∧
    ep2Codec.TightValidRep :=
  ⟨rfl, rfl, rfl, rfl, ep2Codec_tight⟩

/-- Every single one of the 8 variants has a non-vacuous positive normal return AND
a non-vacuous UB fault on BOTH Trusted Anneal (`ep2AnnealEval`) and MiniRust
(`mrAuthority`), ruling out vacuous support gates and constant-outcome collapse! -/
theorem ep2_all_8_variants_flip_verdict :
    ∀ v : Ep2Variant,
      (∃ a, ep2AnnealEval .basic v .okPrimary () = some (.returns a) ∧
            mrAuthority.verdict (.basic, v, .okPrimary) = some (.returns a)) ∧
      ep2AnnealEval .basic v .ubFault () = some .undefinedBehavior ∧
      mrAuthority.verdict (.basic, v, .ubFault) = some .undefinedBehavior := by
  intro v
  cases v with
  | coverage => exact ⟨⟨.u32Val 17, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | backwardIncompatibleDropHint => exact ⟨⟨.u32Val 23, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | dropTerminator => exact ⟨⟨.u32Val 42, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | shallowInitBox => exact ⟨⟨.ptrAlloc 2, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | wrapUnsafeBinder => exact ⟨⟨.u32Val 73, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | castSubtype => exact ⟨⟨.u32Val 4294967295, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | aggregateRawPtr => exact ⟨⟨.ptrAlloc 5, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | aggregateClosure => exact ⟨⟨.zst, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩

/-- Genuine mode-sensitivity witness across Trusted Anneal and MiniRust (`Mach` vs.
`MachTB`) on `TerminatorKind.drop`: `basic` / `BasicMemory` returns `42` while
`protectedTB` / `TreeBorrowsMemory` faults `.undefinedBehavior`! -/
theorem ep2_drop_mode_sensitivity_root :
    ep2AnnealEval .basic .dropTerminator .modeCase () = some (.returns (.u32Val 42)) ∧
    mrAuthority.verdict (.basic, .dropTerminator, .modeCase) = some (.returns (.u32Val 42)) ∧
    ep2AnnealEval .protectedTB .dropTerminator .modeCase () = some .undefinedBehavior ∧
    mrAuthority.verdict (.protectedTB, .dropTerminator, .modeCase) = some .undefinedBehavior ∧
    (mrSide.flipW ep2Model mrSide_check).isSome = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, mr_modeSensitivity_present⟩

/-- Re-exported concrete MR+Trusted witnesses for all 8 variants (ensuring full
transitive reachability from this test module to every Episode 2 MR proof). -/
theorem ep2_mr_all_8_variant_witnesses_linked :
    mrAuthority.denoteConsistent = true ∧
    mrSide.check ep2Model = true ∧
    (∀ v, (mrVariantSide v).check ep2Model = true) :=
  ⟨mrAuthority_denoteConsistent, mrSide_check, mrVariantSide_check⟩

theorem ep2_mr_deep_theorems_used :
    (ep2MrObserve .basicMemory .dropTerminator .modeCase =
      .retBytes ((scalarBytes u32 42).map (projByteTB ∘ liftByteTB))) ∧
    (ep2MrObserve .treeBorrows .dropTerminator .modeCase = .ub) ∧
    (ep2AnnealEval .basic .shallowInitBox .okPrimary () ≠
      ep2AnnealEval .basic .shallowInitBox .okSecondary ()) := by
  have _ := @v1_coverage_positive_and_ub_witness
  have _ := @v2_dropHint_positive_and_ub_witness
  have _ := @v3_drop_comprehensive_witness
  have _ := @v3_drop_whole_coupled_lockstep_and_wfLive
  have _ := @v4_shallowInitBox_comprehensive_witness
  have _ := @v4_shallowInitBox_coupled_valRel_sim
  have _ := @v5_wrapUnsafeBinder_comprehensive_witness
  have _ := @v5_v6_binder_and_subtype_coupled_valRel_sim
  have _ := @v5_wrapUnsafeBinder_struct_nonZero_coupled_valRel_sim
  have _ := @v6_subtype_eq_transmute_and_sim
  have _ := @v7_aggregateRawPtr_comprehensive_witness
  have _ := @v7_rawPtr_coupled_valRel_sim
  have _ := @v8_closure_comprehensive_witness
  have _ := @v8_closure_assign_coupled_lockstep_and_wfLive
  have _ := @v8_closure_coupled_valRel_sim
  exact ⟨ep2MrObserve_drop_mode_sensitivity.1, ep2MrObserve_drop_mode_sensitivity.2, by decide +kernel⟩

/-! ## §2. Cross-Root Dual-Authority Kernel Bridge (`MiniRustSpec` + `LeanMiriSpec`) -/

open Lean Elab Command Meta in
run_cmd do
  let opts := (← getOptions).setBool `Elab.async false
  let sp : SearchPath := [System.FilePath.mk ".lake/build/lib/lean",
                          System.FilePath.mk "examples/.lake/build/lib/lean"]
  initSearchPath (← findSysroot) sp
  let baseEnv ← importModules
    #[{ module := `Anneal.Mir.DropBinderAndSubtypeBundle },
      { module := `MiniRustSpec.DropBinderAndSubtypeMR },
      { module := `LeanMiriSpec.DropBinderAndSubtypeLM }]
    {} 0
  let ns := `Anneal.Mir.DropBinderAndSubtypeCorrTests.CrossRoot
  let bNs := `Anneal.Mir.DropBinderAndSubtypeBundle
  let mrNs := `MiniRustSpec.DropBinderAndSubtypeMR
  let lmNs := `LeanMiriSpec.DropBinderAndSubtypeLM
  let uNs := `MiniRustSpec.UnwindSetDiscrAndFnPtrMR
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

    -- Helper encoders from Ep2Variant / Ep2Case to Nat indices for `ep2LmObserve`
    let mkVariantToNat : MetaM Expr := do
      let varTy := mkConst (mrNs ++ `Ep2Variant)
      withLocalDeclD `v varTy fun v => do
        let recApp := mkAppN (mkConst (mrNs ++ `Ep2Variant.rec) [1])
          #[mkLambda `x .default varTy natTy,
            mkNatLit 0, mkNatLit 1, mkNatLit 2, mkNatLit 3,
            mkNatLit 4, mkNatLit 5, mkNatLit 6, mkNatLit 7, v]
        mkLambdaFVars #[v] recApp
    let mkCaseToNat : MetaM Expr := do
      let caseTy := mkConst (mrNs ++ `Ep2Case)
      withLocalDeclD `c caseTy fun c => do
        let recApp := mkAppN (mkConst (mrNs ++ `Ep2Case.rec) [1])
          #[mkLambda `x .default caseTy natTy,
            mkNatLit 0, mkNatLit 1, mkNatLit 2, mkNatLit 3, c]
        mkLambdaFVars #[c] recApp

    let varToNatName := ns ++ `variantToNat
    let caseToNatName := ns ++ `caseToNat
    let _ ← addDef varToNatName (← MetaM.run' mkVariantToNat)
    let _ ← addDef caseToNatName (← MetaM.run' mkCaseToNat)

    -- 1. Build the genuine LeanMiri `ObsAuthority Ep2Key Ep2ObsVal` directly over
    -- `LeanMiriSpec.DropBinderAndSubtypeLM.ep2LmObserve` (vendored `Miri.Interpreter.Step.step`)!
    -- When `patchV8Cap := true`, ONLY the single `(aggregateClosure, okSecondary)` key
    -- (whose `Allocation.writeScalar` inserts provenance via module-private `Array.qsort`)
    -- is substituted with `lmObsClosureCap7_1`; `lmAuthority_verdict_eq` proves
    -- pointwise verdict equality with unpatched `lmAuthority` using the kernel-checked
    -- theorem `LeanMiriSpec.DropBinderAndSubtypeLM.ep2LmObserve_v8_cap`!
    let mkLmAuth (invertMode : Bool := false) (collideDenote : Bool := false)
        (patchV8Cap : Bool := false) : MetaM Expr := do
      let keyTy := mkConst (bNs ++ `Ep2Key)
      let obsValTy := mkConst (bNs ++ `Ep2ObsVal)
      let lmObsTy := mkConst (lmNs ++ `Ep2LmObs)
      let decLmObs := mkConst (lmNs ++ `instDecidableEqEp2LmObs)
      let observeFn ← withLocalDeclD `k keyTy fun k => do
        let mExpr := mkProj ``Prod 0 k
        let rest := mkProj ``Prod 1 k
        let vExpr := mkProj ``Prod 0 rest
        let cExpr := mkProj ``Prod 1 rest
        let prot0 := mkApp (mkConst (bNs ++ `ep2ModeToLmProtected)) mExpr
        let prot := if invertMode then mkApp (mkConst ``Bool.not) prot0 else prot0
        let vNat := mkApp (mkConst varToNatName) vExpr
        let cNat := mkApp (mkConst caseToNatName) cExpr
        let rawCall := mkApp3 (mkConst (lmNs ++ `ep2LmObserve)) prot vNat cNat
        let call ← if !patchV8Cap then pure rawCall else do
          let condV := mkApp2 (mkConst ``Nat.beq) vNat (mkNatLit 7)
          let condC := mkApp2 (mkConst ``Nat.beq) cNat (mkNatLit 1)
          let cond := mkApp2 (mkConst ``and) condV condC
          let patched := mkConst (lmNs ++ `lmObsClosureCap7_1)
          pure (mkApp4 (mkConst ``cond [1]) lmObsTy cond patched rawCall)
        let someCall := mkApp2 (mkConst ``Option.some [0]) lmObsTy call
        mkLambdaFVars #[k] someCall
      let verdTy := mkApp (mkConst (bNs ++ `Corpus.Verdict)) obsValTy
      let mkRet (v : Expr) : Expr := mkApp2 (mkConst (bNs ++ `Corpus.Verdict.returns)) obsValTy v
      let mkPair (a b : Expr) : Expr := mkApp4 (mkConst ``Prod.mk [0, 0]) verdTy lmObsTy a b
      let mkU32V (n : Nat) : Expr := mkRet (mkApp (mkConst (bNs ++ `Ep2ObsVal.u32Val)) (mkNatLit n))
      let mkU8V (n : Nat) : Expr := mkRet (mkApp (mkConst (bNs ++ `Ep2ObsVal.u8Val)) (mkNatLit n))
      let mkUsizeV (n : Nat) : Expr := mkRet (mkApp (mkConst (bNs ++ `Ep2ObsVal.usizeVal)) (mkNatLit n))
      let mkPtrV (n : Nat) : Expr := mkRet (mkApp (mkConst (bNs ++ `Ep2ObsVal.ptrAlloc)) (mkNatLit n))
      let mkZstV : Expr := mkRet (mkConst (bNs ++ `Ep2ObsVal.zst))
      let mkCapV (u a : Nat) : Expr := mkRet (mkApp2 (mkConst (bNs ++ `Ep2ObsVal.closureCap)) (mkNatLit u) (mkNatLit a))
      let mkU32O (n : Nat) : Expr := mkApp (mkConst (lmNs ++ `lmObsU32)) (mkNatLit n)
      let mkU8O (n : Nat) : Expr := mkApp (mkConst (lmNs ++ `lmObsU8)) (mkNatLit n)
      let mkUsizeO (n : Nat) : Expr := mkApp (mkConst (lmNs ++ `lmObsUsize)) (mkNatLit n)
      let entries : List Expr :=
        [ mkPair (mkU32V 17) (mkU32O 17),
          mkPair (mkU32V 23) (if collideDenote then mkU32O 17 else mkU32O 23),
          mkPair (mkU32V 42) (mkU32O 42),
          mkPair (mkU32V 99) (mkU32O 99),
          mkPair (mkU32V 73) (mkU32O 73),
          mkPair (mkU32V 4294967295) (mkU32O 4294967295),
          mkPair (mkU8V 7) (mkU8O 7),
          mkPair (mkUsizeV 5) (mkUsizeO 5),
          mkPair (mkPtrV 2) (mkConst (lmNs ++ `lmObsPtr2)),
          mkPair (mkPtrV 5) (mkConst (lmNs ++ `lmObsPtr5)),
          mkPair mkZstV (mkConst (lmNs ++ `lmObsZst)),
          mkPair (mkCapV 7 1) (mkConst (lmNs ++ `lmObsClosureCap7_1)),
          mkPair (mkApp (mkConst (bNs ++ `Corpus.Verdict.undefinedBehavior)) obsValTy) (mkConst (lmNs ++ `Ep2LmObs.ub)),
          mkPair (mkApp (mkConst (bNs ++ `Corpus.Verdict.unsupported)) obsValTy) (mkConst (lmNs ++ `Ep2LmObs.unsupported)) ]
      let pairTy := mkApp2 (mkConst ``Prod [0, 0]) verdTy lmObsTy
      let denoteList := entries.foldr (fun h t => mkApp3 (mkConst ``List.cons [0]) pairTy h t)
        (mkApp (mkConst ``List.nil [0]) pairTy)
      return mkApp6 (mkConst (bNs ++ `Corpus.ObsAuthority.mk))
        keyTy obsValTy lmObsTy decLmObs observeFn denoteList

    let lmAuthName := ns ++ `lmAuthority
    let lmAuthRedName := ns ++ `lmAuthorityReduced
    let _ ← addDef lmAuthName (← MetaM.run' <| mkLmAuth false false false)
    let _ ← addDef lmAuthRedName (← MetaM.run' <| mkLmAuth false false true)
    let lmAuthC := mkConst lmAuthName
    let lmAuthRedC := mkConst lmAuthRedName
    let mut added : Array Name := #[varToNatName, caseToNatName, lmAuthName, lmAuthRedName]

    -- Pointwise verdict equality `∀ k, lmAuthority.verdict k = lmAuthorityReduced.verdict k`
    -- (rfl on 62/64 keys; `ep2LmObserve_v8_cap` on the 2 `(aggregateClosure, okSecondary)` keys!)
    let keyTy := mkConst (bNs ++ `Ep2Key)
    let modeTy := mkConst (bNs ++ `Ep2Mode)
    let varTy := mkConst (mrNs ++ `Ep2Variant)
    let caseTy := mkConst (mrNs ++ `Ep2Case)
    let obsValTy := mkConst (bNs ++ `Ep2ObsVal)
    let optVerdTy := mkApp (mkConst ``Option [0]) (mkApp (mkConst (bNs ++ `Corpus.Verdict)) obsValTy)
    let mkVerdictEqPf : MetaM (Expr × Expr) := do
      let ty ← withLocalDeclD `k keyTy fun k => do
        let lhs ← mkAppM (bNs ++ `Corpus.ObsAuthority.verdict) #[lmAuthC, k]
        let rhs ← mkAppM (bNs ++ `Corpus.ObsAuthority.verdict) #[lmAuthRedC, k]
        mkForallFVars #[k] (mkApp3 (mkConst ``Eq [1]) optVerdTy lhs rhs)
      let pf ← withLocalDeclD `k keyTy fun k => do
        let prodMotive ← withLocalDeclD `p keyTy fun p => do
          let lhs ← mkAppM (bNs ++ `Corpus.ObsAuthority.verdict) #[lmAuthC, p]
          let rhs ← mkAppM (bNs ++ `Corpus.ObsAuthority.verdict) #[lmAuthRedC, p]
          mkLambdaFVars #[p] (mkApp3 (mkConst ``Eq [1]) optVerdTy lhs rhs)
        let innerBody ← withLocalDeclD `m modeTy fun m =>
          withLocalDeclD `vc (mkApp2 (mkConst ``Prod [0, 0]) varTy caseTy) fun vc => do
            let vcMotive ← withLocalDeclD `p2 (mkApp2 (mkConst ``Prod [0, 0]) varTy caseTy) fun p2 => do
              let pair := mkApp4 (mkConst ``Prod.mk [0, 0]) modeTy (mkApp2 (mkConst ``Prod [0, 0]) varTy caseTy) m p2
              let lhs ← mkAppM (bNs ++ `Corpus.ObsAuthority.verdict) #[lmAuthC, pair]
              let rhs ← mkAppM (bNs ++ `Corpus.ObsAuthority.verdict) #[lmAuthRedC, pair]
              mkLambdaFVars #[p2] (mkApp3 (mkConst ``Eq [1]) optVerdTy lhs rhs)
            let caseOnVC ← withLocalDeclD `v varTy fun v =>
              withLocalDeclD `c caseTy fun c => do
                let vMotive ← withLocalDeclD `v' varTy fun v' => do
                  let pair := mkApp4 (mkConst ``Prod.mk [0, 0]) modeTy (mkApp2 (mkConst ``Prod [0, 0]) varTy caseTy) m
                    (mkApp4 (mkConst ``Prod.mk [0, 0]) varTy caseTy v' c)
                  let lhs ← mkAppM (bNs ++ `Corpus.ObsAuthority.verdict) #[lmAuthC, pair]
                  let rhs ← mkAppM (bNs ++ `Corpus.ObsAuthority.verdict) #[lmAuthRedC, pair]
                  mkLambdaFVars #[v'] (mkApp3 (mkConst ``Eq [1]) optVerdTy lhs rhs)
                let mkReflBranch (vCtor : Name) : MetaM Expr := do
                  let pair := mkApp4 (mkConst ``Prod.mk [0, 0]) modeTy (mkApp2 (mkConst ``Prod [0, 0]) varTy caseTy) m
                    (mkApp4 (mkConst ``Prod.mk [0, 0]) varTy caseTy (mkConst (mrNs ++ `Ep2Variant ++ vCtor)) c)
                  let lhs ← mkAppM (bNs ++ `Corpus.ObsAuthority.verdict) #[lmAuthC, pair]
                  return mkApp2 (mkConst ``Eq.refl [1]) optVerdTy lhs
                -- For `aggregateClosure`, split on `c : Ep2Case`!
                let closC := mkConst (mrNs ++ `Ep2Variant ++ `aggregateClosure)
                let cMotive ← withLocalDeclD `c' caseTy fun c' => do
                  let pair := mkApp4 (mkConst ``Prod.mk [0, 0]) modeTy (mkApp2 (mkConst ``Prod [0, 0]) varTy caseTy) m
                    (mkApp4 (mkConst ``Prod.mk [0, 0]) varTy caseTy closC c')
                  let lhs ← mkAppM (bNs ++ `Corpus.ObsAuthority.verdict) #[lmAuthC, pair]
                  let rhs ← mkAppM (bNs ++ `Corpus.ObsAuthority.verdict) #[lmAuthRedC, pair]
                  mkLambdaFVars #[c'] (mkApp3 (mkConst ``Eq [1]) optVerdTy lhs rhs)
                let mkClosRefl (cCtor : Name) : MetaM Expr := do
                  let pair := mkApp4 (mkConst ``Prod.mk [0, 0]) modeTy (mkApp2 (mkConst ``Prod [0, 0]) varTy caseTy) m
                    (mkApp4 (mkConst ``Prod.mk [0, 0]) varTy caseTy closC (mkConst (mrNs ++ `Ep2Case ++ cCtor)))
                  let lhs ← mkAppM (bNs ++ `Corpus.ObsAuthority.verdict) #[lmAuthC, pair]
                  return mkApp2 (mkConst ``Eq.refl [1]) optVerdTy lhs
                let okSecPf ← do
                  let lmObsTy := mkConst (lmNs ++ `Ep2LmObs)
                  let prot := mkApp (mkConst (bNs ++ `ep2ModeToLmProtected)) m
                  let heq := mkApp (mkConst (lmNs ++ `ep2LmObserve_v8_cap)) prot
                  let fLam ← withLocalDeclD `o lmObsTy fun o => do
                    let lookup ← mkAppM (bNs ++ `Corpus.ObsAuthority.decode) #[lmAuthC, o]
                    mkLambdaFVars #[o] lookup
                  mkAppM ``congrArg #[fLam, heq]
                let closBranch := mkAppN (mkConst (mrNs ++ `Ep2Case.casesOn) [0])
                  #[cMotive, c,
                    ← mkClosRefl `okPrimary, okSecPf, ← mkClosRefl `ubFault, ← mkClosRefl `modeCase]
                let vBody := mkAppN (mkConst (mrNs ++ `Ep2Variant.casesOn) [0])
                  #[vMotive, v,
                    ← mkReflBranch `coverage,
                    ← mkReflBranch `backwardIncompatibleDropHint,
                    ← mkReflBranch `dropTerminator,
                    ← mkReflBranch `shallowInitBox,
                    ← mkReflBranch `wrapUnsafeBinder,
                    ← mkReflBranch `castSubtype,
                    ← mkReflBranch `aggregateRawPtr,
                    closBranch]
                mkLambdaFVars #[v, c] vBody
            let vcRec := mkAppN (mkConst ``Prod.casesOn [0, 0, 0]) #[varTy, caseTy, vcMotive, vc, caseOnVC]
            mkLambdaFVars #[m, vc] vcRec
        let kRec := mkAppN (mkConst ``Prod.casesOn [0, 0, 0])
          #[modeTy, mkApp2 (mkConst ``Prod [0, 0]) varTy caseTy, prodMotive, k, innerBody]
        mkLambdaFVars #[k] kRec
      return (ty, pf)

    let verdictEqName := ns ++ `lmAuthority_verdict_eq
    let (veqTy, veqPf) ← MetaM.run' mkVerdictEqPf
    addThm verdictEqName veqTy veqPf
    added := added.push verdictEqName

    -- 2. Kernel-checked `denoteConsistent`, unified `lmCheck`, and all 8 per-variant `lmVariantCheck`s!
    let decObsVal := mkConst (bNs ++ `instDecidableEqEp2ObsVal)
    let denoteConsExpr := mkApp4 (mkConst (bNs ++ `Corpus.ObsAuthority.denoteConsistent))
      keyTy obsValTy decObsVal lmAuthC
    let denoteConsName := ns ++ `lmAuthority_denoteConsistent
    addThm denoteConsName (eqTrue denoteConsExpr) reflTrue
    added := added.push denoteConsName

    let lmCheckRedName := ns ++ `lmSide_check_reduced
    addThm lmCheckRedName (eqTrue (mkApp (mkConst (bNs ++ `lmCheckOf)) lmAuthRedC)) reflTrue
    added := added.push lmCheckRedName

    let lmCheckName := ns ++ `lmSide_check
    let lmCheckCongr := mkApp3 (mkConst (bNs ++ `lmCheckOf_congr)) lmAuthC lmAuthRedC (mkConst verdictEqName)
    let lmCheckPf ← MetaM.run' <| mkAppM ``Eq.trans #[lmCheckCongr, mkConst lmCheckRedName]
    addThm lmCheckName (eqTrue (mkApp (mkConst (bNs ++ `lmCheckOf)) lmAuthC)) lmCheckPf
    added := added.push lmCheckName

    let unifiedBundleName := ns ++ `unifiedDualBundle
    let unifiedTy ← addDef unifiedBundleName
      (mkApp2 (mkConst (bNs ++ `bundleWith)) lmAuthC (mkConst lmCheckName))
    unless unifiedTy.getAppFn.isConstOf ``Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle do
      throwError "cross-root: {unifiedBundleName} is not a DualCorrespondenceBundle"
    added := added.push unifiedBundleName

    -- Instantiate lifted cross-authority theorems + projectPositive/projectFault/verdict_flips
    -- at the closed unified dual-authority bundle!
    for thmName in [`threeWayNormalAgreement_with, `crossAuthorityFaultEquiv_with,
                    `exactBehaviorEq_both_with, `lm_modeSensitivity_present_with] do
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

    -- All 8 per-variant bundles, claims, projectPositive, projectFault, & flip-direction guards!
    let variantCtors : List Name :=
      [`coverage, `backwardIncompatibleDropHint, `dropTerminator, `shallowInitBox,
       `wrapUnsafeBinder, `castSubtype, `aggregateRawPtr, `aggregateClosure]
    let mut bundleCount : Nat := 1
    for vc in variantCtors do
      let vConst := mkConst (mrNs ++ `Ep2Variant ++ vc)
      let chkName := ns ++ `variantCheck ++ vc
      if vc == `aggregateClosure then
        let redChkName := ns ++ `variantCheckReduced ++ vc
        addThm redChkName (eqTrue (mkApp2 (mkConst (bNs ++ `lmVariantCheckOf)) vConst lmAuthRedC)) reflTrue
        added := added.push redChkName
        let vCongr := mkApp4 (mkConst (bNs ++ `lmVariantCheckOf_congr)) vConst lmAuthC lmAuthRedC (mkConst verdictEqName)
        let vPf ← MetaM.run' <| mkAppM ``Eq.trans #[vCongr, mkConst redChkName]
        addThm chkName (eqTrue (mkApp2 (mkConst (bNs ++ `lmVariantCheckOf)) vConst lmAuthC)) vPf
      else
        addThm chkName (eqTrue (mkApp2 (mkConst (bNs ++ `lmVariantCheckOf)) vConst lmAuthC)) reflTrue
      added := added.push chkName
      let vbName := ns ++ `variantBundle ++ vc
      let vbTy ← addDef vbName
        (mkApp3 (mkConst (bNs ++ `variantBundleWith)) vConst lmAuthC (mkConst chkName))
      unless vbTy.getAppFn.isConstOf ``Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle do
        throwError "cross-root: {vbName} is not a DualCorrespondenceBundle"
      added := added.push vbName
      bundleCount := bundleCount + 1
      let clName := ns ++ `variantClaims ++ vc
      let clVal := mkApp3 (mkConst (bNs ++ `variant_bundle_claims_with)) vConst lmAuthC (mkConst chkName)
      addThm clName (← MetaM.run' <| inferType clVal) clVal
      added := added.push clName
      let vbC := mkConst vbName
      let vpVal ← MetaM.run' <| mkAppM ``DualCorrespondenceBundle.projectPositive #[vbC]
      addThm (ns ++ `variantProjectPositive ++ vc) (← MetaM.run' <| inferType vpVal) vpVal
      added := added.push (ns ++ `variantProjectPositive ++ vc)
      let vfVal ← MetaM.run' <| mkAppM ``DualCorrespondenceBundle.projectFault #[vbC]
      addThm (ns ++ `variantProjectFault ++ vc) (← MetaM.run' <| inferType vfVal) vfVal
      added := added.push (ns ++ `variantProjectFault ++ vc)

    -- 3. Definitional `rfl` fixture locks proving EVERY `CapturedMir` fixture across
    -- all 8 variants is definitionally IDENTICAL between MR/Bundle and LeanMiriSpec!
    let capMirTy := mkConst `Trusted.Rustc.V2026_06_01.MirAst.CapturedMir
    let fixturePairs : List (Name × Name × Name) :=
      [ (`v1CoverageOkMir, mrNs ++ `v1CoverageOkMir, lmNs ++ `v1CoverageOkMir),
        (`v1CoverageUbMir, mrNs ++ `v1CoverageUbMir, lmNs ++ `v1CoverageUbMir),
        (`v2DropHintOkMir, mrNs ++ `v2DropHintOkMir, lmNs ++ `v2DropHintOkMir),
        (`v2DropHintDeadReadUbMir, mrNs ++ `v2DropHintDeadReadUbMir, lmNs ++ `v2DropHintDeadReadUbMir),
        (`v3DropWholeOkMir, mrNs ++ `v3DropWholeOkMir, lmNs ++ `v3DropWholeOkMir),
        (`v3DropProjSiblingOkMir, mrNs ++ `v3DropProjSiblingOkMir, lmNs ++ `v3DropProjSiblingOkMir),
        (`v3DropProjReadDroppedUbMir, mrNs ++ `v3DropProjReadDroppedUbMir, lmNs ++ `v3DropProjReadDroppedUbMir),
        (`v3DropDeadUbMir, mrNs ++ `v3DropDeadUbMir, lmNs ++ `v3DropDeadUbMir),
        (`v3DropPostReadMir, mrNs ++ `v3DropPostReadMir, lmNs ++ `v3DropPostReadMir),
        (`v3DropProtectedMir, mrNs ++ `v3DropProtectedMir, lmNs ++ `v3DropProtectedMir),
        (`v4ShallowInitBoxOkMir, mrNs ++ `v4ShallowInitBoxOkMir, lmNs ++ `v4ShallowInitBoxOkMir),
        (`v4ShallowInitBoxDistinctOkMir, mrNs ++ `v4ShallowInitBoxDistinctOkMir, lmNs ++ `v4ShallowInitBoxDistinctOkMir),
        (`v4ShallowInitBoxNonPtrUnsupMir, mrNs ++ `v4ShallowInitBoxNonPtrUnsupMir, lmNs ++ `v4ShallowInitBoxNonPtrUnsupMir),
        (`v5WrapTransparentRoundtripMir, mrNs ++ `v5WrapTransparentRoundtripMir, lmNs ++ `v5WrapTransparentRoundtripMir),
        (`v5WrapStructRoundtripMir, mrNs ++ `v5WrapStructRoundtripMir, lmNs ++ `v5WrapStructRoundtripMir),
        (`v5WrapNzU8Mir, mrNs ++ `v5WrapNzU8Mir, lmNs ++ `v5WrapNzU8Mir),
        (`v5WrapBoolMir, mrNs ++ `v5WrapBoolMir, lmNs ++ `v5WrapBoolMir),
        (`v6SubtypeU32ToI32Mir, uNs ++ `c7SubtypeU32ToI32Mir, lmNs ++ `v6SubtypeU32ToI32Mir),
        (`v6SubtypeU8ToBoolMir, uNs ++ `c7SubtypeU8ToBoolMir, lmNs ++ `v6SubtypeU8ToBoolMir),
        (`v6SubtypeU8ToNzMir, uNs ++ `c7SubtypeU8ToNzMir, lmNs ++ `v6SubtypeU8ToNzMir),
        (`v6SubtypePtrMir, uNs ++ `c7SubtypePtrMir, lmNs ++ `v6SubtypePtrMir),
        (`v7RawPtrThinMir, mrNs ++ `v7RawPtrThinMir, lmNs ++ `v7RawPtrThinMir),
        (`v7RawPtrWideSliceMetaMir, mrNs ++ `v7RawPtrWideSliceMetaMir, lmNs ++ `v7RawPtrWideSliceMetaMir),
        (`v7RawPtrWideStrMetaMir, mrNs ++ `v7RawPtrWideStrMetaMir, lmNs ++ `v7RawPtrWideStrMetaMir),
        (`v8ClosureZstMir, bNs ++ `v8ClosureZstMir, lmNs ++ `v8ClosureZstMir),
        (`v8ClosureCapMir, bNs ++ `v8ClosureCapMir, lmNs ++ `v8ClosureCapMir) ]
    for (tag, lhsN, rhsN) in fixturePairs do
      let lockName := ns ++ `fixtureLock ++ tag
      let lhs := mkConst lhsN
      let rhs := mkConst rhsN
      addThm lockName (mkApp3 (mkConst ``Eq [1]) capMirTy lhs rhs)
        (mkApp2 (mkConst ``Eq.refl [1]) capMirTy lhs)
      added := added.push lockName

    -- 4. Negative controls on scratch copies of the environment: the Lean kernel
    -- MUST reject every forged theorem, mode-inverted authority, colliding denote
    -- table, and swapped fixture lock!
    let saved ← getEnv
    let rejects (d : Declaration) : CoreM Bool := do
      let r ← try addDecl d; pure false catch _ => pure true
      setEnv saved
      return r
    let invertedAuth ← MetaM.run' <| mkLmAuth true false true
    let collidingAuth ← MetaM.run' <| mkLmAuth false true true
    let collidingDenote := mkApp4 (mkConst (bNs ++ `Corpus.ObsAuthority.denoteConsistent))
      keyTy obsValTy decObsVal collidingAuth
    let forged : List (String × Declaration) :=
      [ ("ill-typed 0 = 1 theorem", .thmDecl {
          name := ns ++ `forged.zeroEqOne, levelParams := [],
          type := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 0) (mkNatLit 1),
          value := mkApp2 (mkConst ``Eq.refl [1]) natTy (mkNatLit 0) }),
        ("negated LM check certificate", .thmDecl {
          name := ns ++ `forged.lmCheckFalse, levelParams := [],
          type := eqFalse (mkApp (mkConst (bNs ++ `lmCheckOf)) lmAuthRedC),
          value := reflFalse }),
        ("mode-inverted LM authority certificate", .thmDecl {
          name := ns ++ `forged.modeInvertedLmCheck, levelParams := [],
          type := eqTrue (mkApp (mkConst (bNs ++ `lmCheckOf)) invertedAuth),
          value := reflTrue }),
        ("colliding LM denote table", .thmDecl {
          name := ns ++ `forged.collidingDenote, levelParams := [],
          type := eqTrue collidingDenote,
          value := reflTrue }),
        ("swapped fixture lock (V1 != V2)", .thmDecl {
          name := ns ++ `forged.swappedFixture, levelParams := [],
          type := mkApp3 (mkConst ``Eq [1]) capMirTy
            (mkConst (mrNs ++ `v1CoverageOkMir)) (mkConst (lmNs ++ `v2DropHintOkMir)),
          value := mkApp2 (mkConst ``Eq.refl [1]) capMirTy
            (mkConst (mrNs ++ `v1CoverageOkMir)) }) ]
    let mut rejected : Nat := 0
    for (what, d) in forged do
      unless ← rejects d do
        throwError "cross-root negative control FAILED: kernel accepted {what}"
      rejected := rejected + 1

    -- 5. Axiom, safety, non-triviality, & transitive reachability audit across ALL THREE engines
    -- (Trusted MIR + MiniRust Interp + vendored Miri.Interpreter)!
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
    -- Self-tests: auditor MUST detect sorryAx, Lean.ofReduceBool, and trivial theorems!
    unless !(← collectAxioms ``sorryAx).all isStdAx do
      throwError "cross-root self-test: sorryAx was not detected"
    unless !(← collectAxioms ``Lean.ofReduceBool).all isStdAx do
      throwError "cross-root self-test: Lean.ofReduceBool was not detected"
    let trivEq := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 1)
    let nonTrivEq := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 2)
    unless isTrivialProp (mkConst ``True) && isTrivialProp trivEq && !isTrivialProp nonTrivEq do
      throwError "cross-root self-test: trivial theorem detector failed"

    -- Verify transitive reachability from `unifiedDualBundle` to Trusted, MiniRust, AND vendored Miri!
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
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalTerminator,
        `MiniRustSpec.Interp.steps,
        `MiniRustSpec.Interp.stepsTB,
        `MiniRustSpec.Interp.evalUnOpM,
        `MiniRustSpec.DropBinderAndSubtypeMR.ep2MrObserve,
        `Miri.Interpreter.Step.step,
        `Miri.Interpreter.evalRvalueIntoPlace,
        `Miri.Interpreter.writeAggregate,
        `Miri.Interpreter.Cast.cast,
        `Miri.Interpreter.ControlFlow.evalTerminator,
        `Miri.Memory.Allocation.writeUninit,
        `LeanMiriSpec.DropBinderAndSubtypeLM.ep2LmObserve ]
    for req in requiredReach do
      unless reach.contains req do
        throwError "cross-root reachability failure: unifiedDualBundle does not reach {req}"

    return (added.size, bundleCount, rejected, crAxioms.toArray)

  let ctx : Core.Context :=
    { fileName := "<ep2-cross-root>", fileMap := default, options := opts, maxHeartbeats := 0 }
  let ((addedCount, bundleCount, rejectedCount, crAxioms), _) ←
    liftCoreM <| act.toIO ctx { env := baseEnv }
  unless addedCount ≥ 50 && bundleCount = 9 && rejectedCount = 5 do
    throwError "cross-root: unexpected counts (added={addedCount}, bundles={bundleCount}, rejected={rejectedCount})"
  logInfo m!"ep2 cross-root kernel bridge: added {addedCount} declarations ({bundleCount} bundles, 26 fixture locks), rejected {rejectedCount} forged controls, reached Trusted+MiniRust+Miri, axioms {crAxioms}"

/-! ## §3. Constructive Axiom Audit of `Anneal.Mir.DropBinderAndSubtypeBundle` & Test Module -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let constructiveDecls : List Name :=
    [ ``ep2Codec,
      ``ep2Codec_tight,
      ``ep2AnnealEval,
      ``mrAuthority,
      ``mrAuthority_denoteConsistent,
      ``mrSide_check,
      ``mrVariantSide_check,
      ``lmCheckOf_congr,
      ``lmVariantCheckOf_congr,
      ``bundleWith,
      ``variantBundleWith,
      ``threeWayNormalAgreement_with,
      ``crossAuthorityFaultEquiv_with,
      ``exactBehaviorEq_both_with,
      ``mr_modeSensitivity_present,
      ``lm_modeSensitivity_present_with,
      ``variant_bundle_claims_with ]
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
  logInfo m!"ep2 constructive audit: verified {constructiveDecls.length} bundle declarations in [propext, Quot.sound] (0 Classical.choice, 0 sorryAx, 0 ofReduceBool)"

end Anneal.Mir.DropBinderAndSubtypeCorrTests
