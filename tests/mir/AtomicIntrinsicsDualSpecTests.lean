/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Anneal.Mir.AtomicIntrinsicsDualSpec
import MiniRustSpec.AtomicIntrinsicsMR

/-!
# Episode 2 Dual-Authority Atomic Intrinsics Tests & Cross-Root Kernel Bridge

Verifies Rust atomic intrinsic semantics end-to-end across BOTH independent
authorities:

1. **§1. Root-Package Witnesses & Constructive Codec Laws**
   Kernel-checked (`decide +kernel` / `rfl`, zero `native_decide`) witnesses
   exercising `u8`/`u16`/`u32`/`u64`/`usize` store & load round-trips, CAS
   match/mismatch, `fetch_add`/`fetch_sub`/`fetch_and`/`fetch_or`/`fetch_xor`,
   misaligned UB, oversized `u128` UB, OOB UB, Tree Borrows `Frozen` mode
   sensitivity, RMW wrapping-overflow boundary (`Stop.specPanic` in MiniRust
   `d821c6e3`), universal Episode 1 MiniRust laws, and constructive
   `atomicOutcomeCodec`.
2. **§2. Cross-Root Dual-Authority Kernel Bridge (`run_cmd`)**
   Loads BOTH `.lake/build/lib/lean` (`Anneal.Mir.AtomicIntrinsicsDualSpec` and
   `MiniRustSpec.AtomicIntrinsicsMR`) and `examples/.lake/build/lib/lean`
   (`LeanMiriSpec.AtomicIntrinsicsLM`) into a fresh Lean kernel environment:
   - translates `LeanMiriSpec.AtomicIntrinsicsLM.LmAtomicObs → AtomicAccessOutcome`
     via `LmAtomicObs.rec` (zero mocks),
   - defines `crossRootLmObs` calling `LeanMiriSpec.AtomicIntrinsicsLM.lmAtomicObserve`,
   - proves `lmAuthorityCheck crossRootLmObs = true` in the Lean kernel via
     `Eq.refl Bool.true`,
   - instantiates `closedAtomicDualContract : AtomicDualContract` and all 5
     closed projections (`agreement_zone_exact`, `overflow_divergence_explicit`,
     `readonly_alloc_divergence_explicit`, `mode_sensitivity_joint`,
     `mr_universal_laws`),
   - runs **6 negative controls** on scratch copies of `Environment` confirming
     the Lean kernel rejects every forged theorem, inverted mode, shifted case
     index, inverted CAS flag, and UB-to-store forgery,
   - audits every cross-root declaration and key `LeanMiriSpec.AtomicIntrinsicsLM`
     theorems for `.safe`, non-triviality, standard-3-axiom purity (zero
     `sorryAx`, zero `Lean.ofReduceBool`, zero `Lean.trustCompiler`), self-tests
     the auditor, and verifies **transitive constant reachability** from
     `closedAtomicDualContract` to BOTH `MiniRustSpec.Interp.{evalIntrinsic,
     evalIntrinsicM}` AND vendored `Miri.Interpreter.{IntrinsicAtomic.eval,
     AtomicMachine.bind, PlaceMachine.memoryAccess}` +
     `Miri.TreeBorrows.BorrowTree.performBorrowAccessRange`.
3. **§3. Root-Package Constructive Codec & Test Module Axiom Audit (`run_cmd`)**
   Verifies choice-free `[propext, Quot.sound]` purity of the constructive codec
   and soundness theorems, and standard-3-axiom purity of all test declarations.
-/

namespace Anneal.Mir.AtomicIntrinsicsDualSpecTests

set_option Elab.async false

open Anneal.Mir.AtomicIntrinsicsDualSpec
open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.Interp
open MiniRustSpec.LibSpecr hiding Name
open MiniRustSpec.AtomicIntrinsicsMR

/-! ## §1. Root-Package Positive, Negative, Mode-Sensitivity & Constructive Codec Witnesses -/

/-- Constructive round-trip, rejection of malformed wire encodings, and
tightness of `atomicOutcomeCodec` (zero `Classical.choice`). -/
theorem atomic_codec_constructive_laws :
    atomicOutcomeCodec.decode (atomicOutcomeCodec.encode (.okStore 9)) = some (.okStore 9) ∧
    atomicOutcomeCodec.decode (atomicOutcomeCodec.encode (.okScalar 5 8)) = some (.okScalar 5 8) ∧
    atomicOutcomeCodec.decode (atomicOutcomeCodec.encode (.okCas 5 true 9)) =
      some (.okCas 5 true 9) ∧
    atomicOutcomeCodec.decode (atomicOutcomeCodec.encode .ub) = some .ub ∧
    atomicOutcomeCodec.decode (atomicOutcomeCodec.encode .specPanic) = some .specPanic ∧
    atomicOutcomeCodec.decode (atomicOutcomeCodec.encode .invalidOrUnsupported) =
      some .invalidOrUnsupported ∧
    atomicOutcomeCodec.decode (6, 0, false, 0) = none ∧
    atomicOutcomeCodec.decode (0, 1, false, 0) = none ∧
    atomicOutcomeCodec.TightValidRep :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, atomicOutcomeCodec_tight⟩

/-- Store and load witnesses across `u8`, `u16`, `u32`, `u64`, and `usize` on
both `Mach` (`BasicMemory`) and `MachTB` (`TreeBorrowsMemory`). -/
theorem atomic_mr_store_load_widths_witness :
    (∀ m : AtomicMemoryMode,
      mrAtomicObserve m 0 = .okScalar 200 200 ∧
      mrAtomicObserve m 1 = .okStore 200 ∧
      mrAtomicObserve m 2 = .okScalar 48879 48879 ∧
      mrAtomicObserve m 3 = .okStore 48879 ∧
      mrAtomicObserve m 4 = .okScalar 3735928559 3735928559 ∧
      mrAtomicObserve m 5 = .okStore 3735928559 ∧
      mrAtomicObserve m 6 = .okScalar 81985529216486895 81985529216486895 ∧
      mrAtomicObserve m 7 = .okStore 81985529216486895) ∧
    bmObs (bmStoreLoad (.Int 18446744073709551615) (.Int IntType.usize_ty)
        (.Int IntType.usize_ty)) =
      bmRoundTrip (.Int 18446744073709551615)
        (initBytes [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]) ∧
    tbObs (tbStoreLoad (.Int 18446744073709551615) (.Int IntType.usize_ty)
        (.Int IntType.usize_ty)) =
      tbRoundTrip (.Int 18446744073709551615)
        (initBytes [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]) := by
  refine ⟨fun m => ?_, by decide +kernel, by decide +kernel⟩
  exact ⟨mrAtomicObserve_table m 0 (by decide), mrAtomicObserve_table m 1 (by decide),
         mrAtomicObserve_table m 2 (by decide), mrAtomicObserve_table m 3 (by decide),
         mrAtomicObserve_table m 4 (by decide), mrAtomicObserve_table m 5 (by decide),
         mrAtomicObserve_table m 6 (by decide), mrAtomicObserve_table m 7 (by decide)⟩

/-- CAS match/mismatch (`8, 9`) and `fetchAdd`/`fetchSub`/`fetchBitAnd`/
`fetchBitOr`/`fetchBitXor` (`10..14`) across both memory models. -/
theorem atomic_mr_cas_and_rmw_witness (m : AtomicMemoryMode) :
    mrAtomicObserve m 8 = .okCas 5 true 9 ∧
    mrAtomicObserve m 9 = .okCas 5 false 5 ∧
    mrAtomicObserve m 10 = .okScalar 5 8 ∧
    mrAtomicObserve m 11 = .okScalar 5 3 ∧
    mrAtomicObserve m 12 = .okScalar 5 4 ∧
    mrAtomicObserve m 13 = .okScalar 5 7 ∧
    mrAtomicObserve m 14 = .okScalar 5 4 :=
  ⟨mrAtomicObserve_table m 8 (by decide), mrAtomicObserve_table m 9 (by decide),
   mrAtomicObserve_table m 10 (by decide), mrAtomicObserve_table m 11 (by decide),
   mrAtomicObserve_table m 12 (by decide), mrAtomicObserve_table m 13 (by decide),
   mrAtomicObserve_table m 14 (by decide)⟩

/-- Negative & boundary witnesses across both memory models: misaligned UB
(`17`), oversized `u128` UB (`18`), OOB UB (`19`), and MiniRust `d821c6e3`
wrapping-overflow `Stop.specPanic` (`15, 16`). -/
theorem atomic_mr_faults_and_overflow_witness (m : AtomicMemoryMode) :
    mrAtomicObserve m 17 = .ub ∧
    mrAtomicObserve m 18 = .ub ∧
    mrAtomicObserve m 19 = .ub ∧
    mrAtomicObserve m 15 = .specPanic ∧
    mrAtomicObserve m 16 = .specPanic :=
  ⟨mrAtomicObserve_table m 17 (by decide), mrAtomicObserve_table m 18 (by decide),
   mrAtomicObserve_table m 19 (by decide),
   (mr_wrapping_overflow_specPanic m).1, (mr_wrapping_overflow_specPanic m).2⟩

/-- Genuine Tree Borrows `Frozen` mode sensitivity on the root package:
reads (`23`) and failing CAS (`24`) succeed in both modes, while writes (`25`,
`26`, `27`) succeed on `.basic` and fault `.ub` on `.treeBorrows`. -/
theorem atomic_mr_tb_frozen_mode_sensitivity_witness :
    mrAtomicObserve .basic 23 = .okScalar 5 5 ∧
    mrAtomicObserve .treeBorrows 23 = .okScalar 5 5 ∧
    mrAtomicObserve .basic 24 = .okCas 5 false 5 ∧
    mrAtomicObserve .treeBorrows 24 = .okCas 5 false 5 ∧
    mrAtomicObserve .basic 25 = .okStore 9 ∧
    mrAtomicObserve .treeBorrows 25 = .ub ∧
    mrAtomicObserve .basic 26 = .okScalar 5 6 ∧
    mrAtomicObserve .treeBorrows 26 = .ub ∧
    mrAtomicObserve .basic 27 = .okCas 5 true 9 ∧
    mrAtomicObserve .treeBorrows 27 = .ub :=
  mr_tb_frozen_mode_sensitivity

/-- Root-package linkage to Episode 1's universal polymorphic MiniRust laws. -/
theorem atomic_mr_universal_laws_linked :
    (∀ (m : Mach) (op : IntrinsicOp) (args : List (Val × «Type»)) (retTy : «Type»),
      isAtomicOp op = true →
      evalIntrinsicM (M := BM) m op args retTy = evalIntrinsic m op args retTy) ∧
    (∀ (m m' : MachTB) (op : IntrinsicOp) (args : List (Value TBM × «Type»))
      (retTy : «Type») (val : Value TBM),
      isAtomicOp op = true →
      MiniRustSpec.Correspondence.MachTB.wfLive m →
      evalIntrinsicM m op args retTy = .ok (val, m') →
      MiniRustSpec.Correspondence.MachTB.wfLive m') ∧
    (MiniRustSpec.Correspondence.MachTB.wfLive (tbWith []) ∧
      scalarAgrees BM evalIntrinsic bmFive bmPtr = true ∧
      scalarAgrees TBM evalIntrinsicM tbFive tbPtr = true) :=
  ⟨mr_universal_bm_eq_atomic,
   fun _ _ _ _ _ _ hop hwf h => mr_universal_tb_wfLive hop hwf h,
   mr_universal_ep1_capstone_bridge⟩

/-! ## §2. Cross-Root Dual-Authority Kernel Bridge (`MiniRustSpec` + `LeanMiriSpec`) -/

open Lean Elab Command Meta in
run_cmd do
  let opts := (← getOptions).setBool `Elab.async false
  let sp : SearchPath := [System.FilePath.mk ".lake/build/lib/lean",
                          System.FilePath.mk "examples/.lake/build/lib/lean"]
  initSearchPath (← findSysroot) sp
  let baseEnv ← importModules
    #[{ module := `Anneal.Mir.AtomicIntrinsicsDualSpec },
      { module := `MiniRustSpec.AtomicIntrinsicsMR },
      { module := `LeanMiriSpec.AtomicIntrinsicsLM }]
    {} 0
  let ns := `Anneal.Mir.AtomicIntrinsicsDualSpecTests.CrossRoot
  let dsNs := `Anneal.Mir.AtomicIntrinsicsDualSpec
  let lmNs := `LeanMiriSpec.AtomicIntrinsicsLM
  let act : CoreM (Nat × Nat × Array Lean.Name) := do
    let addDef (name : Lean.Name) (val : Expr) : CoreM Expr := do
      let ty ← MetaM.run' <| inferType val
      addDecl <| .defnDecl {
        name, levelParams := [], type := ty, value := val,
        hints := .regular 0, safety := .safe }
      return ty
    let addThm (name : Lean.Name) (ty pf : Expr) : CoreM Unit := do
      addDecl <| .thmDecl { name, levelParams := [], type := ty, value := pf }
    let boolTy := mkConst ``Bool
    let boolTrue := mkConst ``Bool.true
    let boolFalse := mkConst ``Bool.false
    let natTy := mkConst ``Nat
    let eqTrue (e : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) boolTy e boolTrue
    let reflTrue : Expr := mkApp2 (mkConst ``Eq.refl [1]) boolTy boolTrue
    let eqFalse (e : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) boolTy e boolFalse
    let reflFalse : Expr := mkApp2 (mkConst ``Eq.refl [1]) boolTy boolFalse

    let lmObsTy := mkConst (lmNs ++ `LmAtomicObs)
    let outcomeTy := mkConst (dsNs ++ `AtomicAccessOutcome)

    -- Translator `LmAtomicObs → AtomicAccessOutcome` via `LmAtomicObs.rec.{1}` (zero mocks).
    -- Supports optional corruption flags for negative controls.
    let mkTranslateLmObs (invertCas : Bool := false) (forgeUbToStore : Bool := false) :
        MetaM Expr := do
      let motive := mkLambda `x .default lmObsTy outcomeTy
      let brOkStore ← withLocalDeclD `post natTy fun post =>
        mkLambdaFVars #[post] (mkApp (mkConst (dsNs ++ `AtomicAccessOutcome.okStore)) post)
      let brOkScalar ← withLocalDeclD `ret natTy fun ret =>
        withLocalDeclD `post natTy fun post =>
          mkLambdaFVars #[ret, post]
            (mkApp2 (mkConst (dsNs ++ `AtomicAccessOutcome.okScalar)) ret post)
      let brOkCas ← withLocalDeclD `ret natTy fun ret =>
        withLocalDeclD `succ boolTy fun succ =>
          withLocalDeclD `post natTy fun post =>
            let succ' := if invertCas then mkApp (mkConst ``Bool.not) succ else succ
            mkLambdaFVars #[ret, succ, post]
              (mkApp3 (mkConst (dsNs ++ `AtomicAccessOutcome.okCas)) ret succ' post)
      let brUb :=
        if forgeUbToStore then
          mkApp (mkConst (dsNs ++ `AtomicAccessOutcome.okStore)) (mkNatLit 0)
        else
          mkConst (dsNs ++ `AtomicAccessOutcome.ub)
      let brInvalid := mkConst (dsNs ++ `AtomicAccessOutcome.invalidOrUnsupported)
      withLocalDeclD `o lmObsTy fun o => do
        let recApp := mkAppN (mkConst (lmNs ++ `LmAtomicObs.rec) [1])
          #[motive, brOkStore, brOkScalar, brOkCas, brUb, brInvalid, o]
        mkLambdaFVars #[o] recApp

    let mkCrossRootObs (translator : Expr) (invertMode : Bool := false)
        (shiftCase : Bool := false) : MetaM Expr := do
      withLocalDeclD `tb boolTy fun tb =>
        withLocalDeclD `idx natTy fun idx => do
          let tb' := if invertMode then mkApp (mkConst ``Bool.not) tb else tb
          let idx' := if shiftCase then mkApp2 (mkConst ``Nat.add) idx (mkNatLit 1) else idx
          let raw := mkApp2 (mkConst (lmNs ++ `lmAtomicObserve)) tb' idx'
          mkLambdaFVars #[tb, idx] (mkApp translator raw)

    -- 1. Add genuine translator and `crossRootLmObs` directly over `lmAtomicObserve`.
    let translateName := ns ++ `translateLmObs
    let _ ← addDef translateName (← MetaM.run' <| mkTranslateLmObs false false)
    let crossObsName := ns ++ `crossRootLmObs
    let _ ← addDef crossObsName (← MetaM.run' <| mkCrossRootObs (mkConst translateName) false false)
    let crossObsC := mkConst crossObsName

    -- 2. Kernel-check `lmAuthorityCheck crossRootLmObs = true` via `Eq.refl Bool.true`.
    let checkName := ns ++ `crossRootLmCheck
    let checkExpr := mkApp (mkConst (dsNs ++ `lmAuthorityCheck)) crossObsC
    addThm checkName (eqTrue checkExpr) reflTrue

    -- 3. Instantiate closed `AtomicDualContract` and all 5 named projections.
    let contractName := ns ++ `closedAtomicDualContract
    let contractTy ← addDef contractName
      (mkApp2 (mkConst (dsNs ++ `atomicDualContractOfCheck)) crossObsC (mkConst checkName))
    unless contractTy.isConstOf (dsNs ++ `AtomicDualContract) do
      throwError "cross-root: {contractName} is not an AtomicDualContract"
    let contractC := mkConst contractName

    let mut added : Array Lean.Name := #[translateName, crossObsName, checkName, contractName]
    for projName in [`contract_agreement_zone_exact,
                     `contract_overflow_divergence,
                     `contract_readonly_alloc_divergence,
                     `contract_mode_sensitivity_joint,
                     `contract_mr_universal_laws] do
      let val := mkApp (mkConst (dsNs ++ projName)) contractC
      let ty ← MetaM.run' <| inferType val
      let outName := ns ++ projName
      addThm outName ty val
      added := added.push outName

    -- 4. Six negative controls on scratch copies of the environment: the Lean kernel
    -- MUST reject every forged theorem, inverted mode, shifted case, inverted CAS flag,
    -- and UB-to-okStore forgery.
    let saved ← getEnv
    let rejects (d : Declaration) : CoreM Bool := do
      let r ← try addDecl d; pure false catch _ => pure true
      setEnv saved
      return r
    let modeInvertedObs ← MetaM.run' <| mkCrossRootObs (mkConst translateName) true false
    let caseShiftedObs ← MetaM.run' <| mkCrossRootObs (mkConst translateName) false true
    let casInvertedTr ← MetaM.run' <| mkTranslateLmObs true false
    let casInvertedObs ← MetaM.run' <| mkCrossRootObs casInvertedTr false false
    let ubForgedTr ← MetaM.run' <| mkTranslateLmObs false true
    let ubForgedObs ← MetaM.run' <| mkCrossRootObs ubForgedTr false false
    let forged : List (String × Declaration) :=
      [ ("ill-typed 0 = 1 theorem", .thmDecl {
          name := ns ++ `forged.zeroEqOne, levelParams := [],
          type := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 0) (mkNatLit 1),
          value := mkApp2 (mkConst ``Eq.refl [1]) natTy (mkNatLit 0) }),
        ("negated lmAuthorityCheck certificate (= false)", .thmDecl {
          name := ns ++ `forged.lmCheckFalse, levelParams := [],
          type := eqFalse checkExpr,
          value := reflFalse }),
        ("mode-inverted crossRootLmObs (Bool.not tb)", .thmDecl {
          name := ns ++ `forged.modeInverted, levelParams := [],
          type := eqTrue (mkApp (mkConst (dsNs ++ `lmAuthorityCheck)) modeInvertedObs),
          value := reflTrue }),
        ("case-shifted crossRootLmObs (idx + 1)", .thmDecl {
          name := ns ++ `forged.caseShifted, levelParams := [],
          type := eqTrue (mkApp (mkConst (dsNs ++ `lmAuthorityCheck)) caseShiftedObs),
          value := reflTrue }),
        ("CAS-succeeded-inverted translator", .thmDecl {
          name := ns ++ `forged.casInverted, levelParams := [],
          type := eqTrue (mkApp (mkConst (dsNs ++ `lmAuthorityCheck)) casInvertedObs),
          value := reflTrue }),
        ("UB-to-okStore forged translator", .thmDecl {
          name := ns ++ `forged.ubForged, levelParams := [],
          type := eqTrue (mkApp (mkConst (dsNs ++ `lmAuthorityCheck)) ubForgedObs),
          value := reflTrue }) ]
    let mut rejected : Nat := 0
    for (what, d) in forged do
      unless ← rejects d do
        throwError "cross-root negative control FAILED: kernel accepted {what}"
      rejected := rejected + 1

    -- 5. Safety, non-triviality, standard-3-axiom purity, key LM theorem verification,
    -- self-tests, and transitive reachability audit across BOTH engines.
    let env ← getEnv
    let isStdAx (a : Lean.Name) : Bool :=
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
        if a == ``sorryAx || a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
          throwError "cross-root: {n} depends on forbidden axiom {a}"
        unless isStdAx a do
          throwError "cross-root: {n} depends on non-standard axiom {a}"
        crAxioms := crAxioms.insert a

    -- Verify key LeanMiriSpec.AtomicIntrinsicsLM theorems are present, non-trivial, and pure.
    let lmKeyThms : List Lean.Name :=
      [ lmNs ++ `lmAtomicHooks_bind_eq_exec,
        lmNs ++ `atomic_tb_check_bridges_vendored_performBorrowAccessRange,
        lmNs ++ `allowDataRaces_none,
        lmNs ++ `allowDataRaces_rejects_nested,
        lmNs ++ `allowDataRaces_ok_restores,
        lmNs ++ `allowDataRaces_error_restores,
        lmNs ++ `atomicReadOrd_ofOrdering_laws,
        lmNs ++ `atomicWriteOrd_ofOrdering_laws,
        lmNs ++ `prepareAtomicFence_laws,
        lmNs ++ `load_rejects_invalid_ordering,
        lmNs ++ `store_rejects_invalid_ordering,
        lmNs ++ `compareExchange_rejects_invalid_failure_ordering,
        lmNs ++ `fence_rejects_relaxed_and_singlethread_noop,
        lmNs ++ `compareExchange_strong_matches_all_policies,
        lmNs ++ `compareExchange_mismatch_skips_write,
        lmNs ++ `compareExchange_weak_neverFail_succeeds,
        lmNs ++ `compareExchange_weak_alwaysFail_spurious,
        lmNs ++ `compareExchange_weak_mayFail_follows_choice,
        lmNs ++ `eval_store_load_roundtrip_all_widths,
        lmNs ++ `eval_all_rmw_intrinsics,
        lmNs ++ `eval_rmw_wrapping_overflow,
        lmNs ++ `eval_cxchg_and_cxchgweak,
        lmNs ++ `eval_fences_and_unknown_name,
        lmNs ++ `eval_single_thread_global_fast_path,
        lmNs ++ `eval_fault_witnesses,
        lmNs ++ `eval_tb_frozen_mode_sensitivity,
        lmNs ++ `lmAtomicObserve_table ]
    for n in lmKeyThms do
      let some (.thmInfo v) := env.find? n
        | throwError "cross-root: required LM theorem {n} missing"
      if isTrivialProp v.type then
        throwError "cross-root: LM theorem {n} is trivial"
      for a in ← collectAxioms n do
        if a == ``sorryAx || a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
          throwError "cross-root: LM theorem {n} depends on forbidden axiom {a}"
        unless isStdAx a do
          throwError "cross-root: LM theorem {n} depends on non-standard axiom {a}"
        crAxioms := crAxioms.insert a

    -- Self-tests: auditor MUST detect sorryAx, Lean.ofReduceBool, Lean.trustCompiler,
    -- and trivial theorems.
    unless !(← collectAxioms ``sorryAx).all isStdAx do
      throwError "cross-root self-test: sorryAx was not detected"
    unless !(← collectAxioms ``Lean.ofReduceBool).all isStdAx do
      throwError "cross-root self-test: Lean.ofReduceBool was not detected"
    unless !(← collectAxioms ``Lean.trustCompiler).all isStdAx do
      throwError "cross-root self-test: Lean.trustCompiler was not detected"
    let trivEq := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 1)
    let nonTrivEq := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 2)
    unless isTrivialProp (mkConst ``True) && isTrivialProp trivEq && !isTrivialProp nonTrivEq do
      throwError "cross-root self-test: trivial theorem detector failed"

    -- Transitive constant reachability BFS from `closedAtomicDualContract` to BOTH
    -- MiniRust (`evalIntrinsic` / `evalIntrinsicM`) AND vendored Miri (`IntrinsicAtomic.eval` /
    -- `AtomicMachine.bind` / `PlaceMachine.memoryAccess` / `BorrowTree.performBorrowAccessRange`).
    let mut reach : NameSet := {}
    let mut todo : Array Lean.Name := #[contractName]
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if reach.contains n then continue
      reach := reach.insert n
      if let some ci := env.find? n then
        for d in ci.getUsedConstantsAsSet do
          if !reach.contains d then todo := todo.push d
    let requiredReach : List Lean.Name :=
      [ `MiniRustSpec.Interp.evalIntrinsic,
        `MiniRustSpec.Interp.evalIntrinsicM,
        `MiniRustSpec.AtomicIntrinsicsMR.ep1_minirust_atomic_intrinsics_capstone,
        dsNs ++ `mrAtomicObserve,
        dsNs ++ `mrAtomicObserve_table,
        lmNs ++ `lmAtomicObserve,
        `Miri.Interpreter.IntrinsicAtomic.eval,
        `Miri.Interpreter.AtomicMachine.bind,
        `Miri.Interpreter.PlaceMachine.memoryAccess,
        `Miri.TreeBorrows.BorrowTree.performBorrowAccessRange ]
    for req in requiredReach do
      unless reach.contains req do
        throwError "cross-root reachability failure: closedAtomicDualContract does not reach {req}"

    return (added.size, rejected, crAxioms.toArray)

  let ctx : Core.Context :=
    { fileName := "<atomics-cross-root>", fileMap := default, options := opts, maxHeartbeats := 0 }
  let ((addedCount, rejectedCount, crAxioms), _) ←
    liftCoreM <| act.toIO ctx { env := baseEnv }
  unless addedCount = 9 && rejectedCount = 6 do
    throwError "cross-root: unexpected counts (added={addedCount}, rejected={rejectedCount})"
  logInfo m!"atomics cross-root kernel bridge: added {addedCount} declarations, rejected {rejectedCount} forged controls, reached MiniRust+Miri, axioms {crAxioms}"

/-! ## §3. Root-Package Constructive Codec & Test Module Axiom Audit -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let constructiveDecls : List Lean.Name :=
    [ ``Anneal.Mir.AtomicIntrinsicsDualSpec.atomicOutcomeCodec,
      ``Anneal.Mir.AtomicIntrinsicsDualSpec.atomicOutcomeCodec_tight,
      ``Anneal.Mir.AtomicIntrinsicsDualSpec.atomicOutcomeCodec_encode_injective,
      ``Anneal.Mir.AtomicIntrinsicsDualSpec.atomicOutcomeCodec_decode_injective_on_valid,
      ``Anneal.Mir.AtomicIntrinsicsDualSpec.AtomicMemoryMode.of_toLmTreeBorrows,
      ``Anneal.Mir.AtomicIntrinsicsDualSpec.AtomicMemoryMode.to_ofLmTreeBorrows,
      ``Anneal.Mir.AtomicIntrinsicsDualSpec.lmAuthorityCheck_sound ]
  for d in constructiveDecls do
    let axs ← liftCoreM <| Lean.collectAxioms d
    for a in axs do
      unless a == ``propext || a == ``Quot.sound do
        throwError "constructive audit failure: {d} uses non-constructive axiom {a}"
  for (c, _) in env.constants.map₂.toList do
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "test audit failure: {c} uses sorryAx"
      if a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
        throwError "test audit failure: {c} uses {a}"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "test audit failure: {c} uses non-standard axiom {a}"
  logInfo m!"atomics constructive audit: verified {constructiveDecls.length} declarations in [propext, Quot.sound] (0 Classical.choice, 0 sorryAx, 0 ofReduceBool)"

end Anneal.Mir.AtomicIntrinsicsDualSpecTests
