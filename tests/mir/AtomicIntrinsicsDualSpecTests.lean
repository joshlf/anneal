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
   - instantiates `closedAtomicDualContract : AtomicDualContract` and all 10 closed
     projections (incl. `ep2_atomic_intrinsics_dual_authority_capstone`,
     `cas_return_shape`, `divergence_set_exact`, `tcb_codec_bridge`,
     `tcb_codec_divergence_exact`),
   - runs **12 negative controls** on scratch `Environment` copies (forged theorem,
     inverted mode, shifted case, inverted CAS, UB forgery, negated trace, inverted
     Frozen trace, inverted signed CAS, Frozen/Reserved trace swaps, and a forged
     wire-tuple agreement on diverging cell `(basic, 15)`),
   - audits every cross-root declaration and key `LeanMiriSpec.AtomicIntrinsicsLM`
     theorems for `.safe`, non-triviality, standard-3-axiom purity (zero
     `sorryAx`, zero `Lean.ofReduceBool`, zero `Lean.trustCompiler`), self-tests
     the auditor, and verifies **transitive constant reachability** from closed
     `ep2_atomic_intrinsics_dual_authority_capstone` (via `closedAtomicDualContract`)
     to BOTH `MiniRustSpec.Interp.{evalIntrinsic, evalIntrinsicM}` AND vendored
     `Miri.Interpreter.{IntrinsicAtomic.eval, AtomicMachine.bind,
     PlaceMachine.memoryAccess}` + `Miri.TreeBorrows.BorrowTree.performBorrowAccessRange`.
3. **§3. Root-Package Constructive Codec & Test Module Axiom Audit (`run_cmd`)**
   Verifies choice-free `[propext, Quot.sound]` purity of the constructive codec
   and soundness theorems, standard-3-axiom purity, and theorem-count floor (`>= 6`).
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

    -- 2b. Fast-path (`dataRace = some _`) certificate: same check over `lmAtomicObserveWith true`.
    let fastObs ← MetaM.run' <| withLocalDeclD `tb boolTy fun tb =>
      withLocalDeclD `idx natTy fun idx =>
        mkLambdaFVars #[tb, idx] (mkApp (mkConst translateName)
          (mkApp3 (mkConst (lmNs ++ `lmAtomicObserveWith)) boolTrue tb idx))
    let fastObsName := ns ++ `crossRootLmObsFastPath
    let _ ← addDef fastObsName fastObs
    let fastCheckName := ns ++ `crossRootLmCheckFastPath
    addThm fastCheckName
      (eqTrue (mkApp (mkConst (dsNs ++ `lmAuthorityCheck)) (mkConst fastObsName))) reflTrue

    -- 2c. Threaded 5-step trace + closed soundness theorem across BOTH engines per mode.
    let traceObs ← MetaM.run' <| withLocalDeclD `tb boolTy fun tb =>
      mkLambdaFVars #[tb] (mkApp4 (mkConst ``List.map [.zero, .zero]) lmObsTy outcomeTy
        (mkConst translateName) (mkApp (mkConst (lmNs ++ `lmAtomicTrace)) tb))
    let traceObsName := ns ++ `crossRootLmTrace
    let _ ← addDef traceObsName traceObs
    let traceCheckName := ns ++ `crossRootLmTraceCheck
    addThm traceCheckName
      (eqTrue (mkApp (mkConst (dsNs ++ `lmTraceAuthorityCheck)) (mkConst traceObsName))) reflTrue
    let traceEqVal := mkApp2 (mkConst (dsNs ++ `lmTraceAuthorityCheck_sound)) (mkConst traceObsName) (mkConst traceCheckName)
    let traceEqName := ns ++ `crossRootLmTraceEq
    addThm traceEqName (← MetaM.run' <| inferType traceEqVal) traceEqVal
    -- 2d. Mode-sensitive `Frozen`-tag trace (`.basic`: 4 steps; `.treeBorrows`: 3 steps halting `.ub`).
    let frozenTraceObs ← MetaM.run' <| withLocalDeclD `tb boolTy fun tb =>
      mkLambdaFVars #[tb] (mkApp4 (mkConst ``List.map [.zero, .zero]) lmObsTy outcomeTy
        (mkConst translateName) (mkApp2 (mkConst (lmNs ++ `lmTagTrace)) (mkConst (lmNs ++ `CellTagMode.frozenChild)) tb))
    let frozenTraceObsName := ns ++ `crossRootLmFrozenTrace
    let _ ← addDef frozenTraceObsName frozenTraceObs
    let frozenTraceCheckName := ns ++ `crossRootLmFrozenTraceCheck
    addThm frozenTraceCheckName
      (eqTrue (mkApp (mkConst (dsNs ++ `lmFrozenTraceAuthorityCheck)) (mkConst frozenTraceObsName))) reflTrue
    let frozenTraceEqVal := mkApp2 (mkConst (dsNs ++ `lmFrozenTraceAuthorityCheck_sound))
      (mkConst frozenTraceObsName) (mkConst frozenTraceCheckName)
    let frozenTraceEqName := ns ++ `crossRootLmFrozenTraceEq
    addThm frozenTraceEqName (← MetaM.run' <| inferType frozenTraceEqVal) frozenTraceEqVal
    -- 2e. Signed two's-complement boundary cells: 7 in-range agreements + 4 wrap-vs-`specPanic` forced divergences per mode.
    let signedObs ← MetaM.run' <| withLocalDeclD `tb boolTy fun tb =>
      mkLambdaFVars #[tb] (mkApp4 (mkConst ``List.map [.zero, .zero]) lmObsTy outcomeTy
        (mkConst translateName) (mkApp (mkConst (lmNs ++ `lmSignedBoundaryObs)) tb))
    let signedObsName := ns ++ `crossRootLmSignedBoundary
    let _ ← addDef signedObsName signedObs
    let signedCheckName := ns ++ `crossRootLmSignedBoundaryCheck
    addThm signedCheckName (eqTrue (mkApp (mkConst (dsNs ++ `lmSignedBoundaryAuthorityCheck)) (mkConst signedObsName))) reflTrue
    let signedEqVal := mkApp2 (mkConst (dsNs ++ `lmSignedBoundaryAuthorityCheck_sound)) (mkConst signedObsName) (mkConst signedCheckName)
    let signedEqName := ns ++ `crossRootLmSignedBoundaryEq
    addThm signedEqName (← MetaM.run' <| inferType signedEqVal) signedEqVal
    -- 2f. Cross-root `Reserved`-tag 4-step prefix (`lmTagTrace .reservedChild` vs `mrReservedActivationTrace.take 4`).
    let resTraceObs ← MetaM.run' <| withLocalDeclD `tb boolTy fun tb => mkLambdaFVars #[tb] (mkApp4 (mkConst ``List.map [.zero, .zero]) lmObsTy outcomeTy (mkConst translateName) (mkApp2 (mkConst (lmNs ++ `lmTagTrace)) (mkConst (lmNs ++ `CellTagMode.reservedChild)) tb))
    let resTraceObsName := ns ++ `crossRootLmReservedTrace; let _ ← addDef resTraceObsName resTraceObs
    let resTraceCheckName := ns ++ `crossRootLmReservedTraceCheck
    addThm resTraceCheckName (eqTrue (mkApp (mkConst (dsNs ++ `lmReservedTraceAuthorityCheck)) (mkConst resTraceObsName))) reflTrue
    let resTraceEqVal := mkApp2 (mkConst (dsNs ++ `lmReservedTraceAuthorityCheck_sound)) (mkConst resTraceObsName) (mkConst resTraceCheckName)
    let resTraceEqName := ns ++ `crossRootLmReservedTraceEq; addThm resTraceEqName (← MetaM.run' <| inferType resTraceEqVal) resTraceEqVal

    -- 2g. Wire-level single-cell agreement: agreeing cell `(basic, 0)` is kernel-accepted (well-typed positive twin of step 4's `(basic, 15)` forgery).
    let wireAt (idx : Nat) : Expr := eqTrue (mkApp3 (mkConst (dsNs ++ `wireAgreesAt)) crossObsC (mkConst (dsNs ++ `AtomicMemoryMode.basic)) (mkNatLit idx))
    let wireOkName := ns ++ `crossRootWireAgreesCell0; addThm wireOkName (wireAt 0) reflTrue

    -- 3. Instantiate closed `AtomicDualContract`, all 9 named projections, and closed Episode 2 capstone.
    let contractName := ns ++ `closedAtomicDualContract
    let contractTy ← addDef contractName
      (mkApp2 (mkConst (dsNs ++ `atomicDualContractOfCheck)) crossObsC (mkConst checkName))
    unless contractTy.isConstOf (dsNs ++ `AtomicDualContract) do
      throwError "cross-root: {contractName} is not an AtomicDualContract"
    let contractC := mkConst contractName

    let mut added : Array Lean.Name :=
      #[translateName, crossObsName, checkName, fastObsName, fastCheckName, contractName,
        traceObsName, traceCheckName, traceEqName, frozenTraceObsName, frozenTraceCheckName, frozenTraceEqName,
        signedObsName, signedCheckName, signedEqName, resTraceObsName, resTraceCheckName, resTraceEqName, wireOkName]
    for projName in [`contract_agreement_zone_exact,
                     `contract_overflow_divergence,
                     `contract_readonly_alloc_divergence,
                     `contract_mode_sensitivity_joint,
                     `contract_mr_universal_laws,
                     `contract_cas_return_shape,
                     `contract_divergence_set_exact,
                     `contract_tcb_codec_bridge,
                     `contract_tcb_codec_divergence_exact,
                     `ep2_atomic_intrinsics_dual_authority_capstone] do
      let val := mkApp (mkConst (dsNs ++ projName)) contractC
      let ty ← MetaM.run' <| inferType val
      let outName := ns ++ projName
      addThm outName ty val
      added := added.push outName

    -- 4. Twelve negative controls (incl. signed CAS inversion, Frozen/Reserved swap & wire-tuple forgery) on scratch copies of the environment: the Lean kernel
    -- MUST reject every forged theorem, inverted mode, shifted case, inverted CAS flag,
    -- UB-to-okStore forgery, negated trace certificate, and mode-inverted Frozen trace.
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
    let frozenModeInv ← MetaM.run' <| withLocalDeclD `tb boolTy fun tb =>
      mkLambdaFVars #[tb] (mkApp (mkConst frozenTraceObsName) (mkApp (mkConst ``Bool.not) tb))
    let signedCasInv ← MetaM.run' <| withLocalDeclD `tb boolTy fun tb =>
      mkLambdaFVars #[tb] (mkApp4 (mkConst ``List.map [.zero, .zero]) lmObsTy outcomeTy casInvertedTr
        (mkApp (mkConst (lmNs ++ `lmSignedBoundaryObs)) tb))
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
          value := reflTrue }),
        ("negated lmTraceAuthorityCheck certificate (= false)", .thmDecl {
          name := ns ++ `forged.traceCheckFalse, levelParams := [],
          type := eqFalse (mkApp (mkConst (dsNs ++ `lmTraceAuthorityCheck)) (mkConst traceObsName)),
          value := reflFalse }),
        ("mode-inverted Frozen trace (Bool.not tb)", .thmDecl {
          name := ns ++ `forged.frozenTraceModeInverted, levelParams := [],
          type := eqTrue (mkApp (mkConst (dsNs ++ `lmFrozenTraceAuthorityCheck)) frozenModeInv),
          value := reflTrue }),
        ("CAS-succeeded-inverted signed-boundary cells (negative cxchg)", .thmDecl {
          name := ns ++ `forged.signedCasInverted, levelParams := [],
          type := eqTrue (mkApp (mkConst (dsNs ++ `lmSignedBoundaryAuthorityCheck)) signedCasInv),
          value := reflTrue }),
        ("Frozen trace passed to lmReservedTraceAuthorityCheck", .thmDecl { name := ns ++ `forged.frozenAsReservedTrace, levelParams := [], type := eqTrue (mkApp (mkConst (dsNs ++ `lmReservedTraceAuthorityCheck)) (mkConst frozenTraceObsName)), value := reflTrue }),
        ("Reserved trace passed to lmFrozenTraceAuthorityCheck", .thmDecl { name := ns ++ `forged.reservedAsFrozenTrace, levelParams := [], type := eqTrue (mkApp (mkConst (dsNs ++ `lmFrozenTraceAuthorityCheck)) (mkConst resTraceObsName)), value := reflTrue }),
        ("Wire tuples forged equal on diverging cell (basic, 15)", .thmDecl { name := ns ++ `forged.wireAgreesOnDivergence, levelParams := [], type := wireAt 15, value := reflTrue }) ]
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

    -- Verify key LeanMiriSpec.AtomicIntrinsicsLM and AtomicIntrinsicsDualSpec theorems are pure.
    let keyThms : List Lean.Name :=
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
        lmNs ++ `lmAtomicObserve_table,
        lmNs ++ `rmwValue_universal_laws, lmNs ++ `fence_without_global_noop,
        lmNs ++ `eval_u128_in_bounds_mutable_load_not_ub,
        lmNs ++ `lmAtomicObserve_fastPath_invariant,
        lmNs ++ `pointerBinary_laws, lmNs ++ `eval_signed_unsigned_polarity_and_usize,
        dsNs ++ `casOldProjection_casFlagSynth, dsNs ++ `casOldProjection_obsMrCas,
        dsNs ++ `contract_cas_return_shape, dsNs ++ `contract_divergence_set_exact,
        dsNs ++ `mr_universal_cas_failure_returns_before,
        dsNs ++ `mr_universal_rmw_out_of_range_specPanic,
        dsNs ++ `mr_universal_atomicLoad_size_too_big_ub,
        dsNs ++ `mr_signed_unsigned_polarity_and_usize_parity,
        lmNs ++ `lmAtomicTrace_table, dsNs ++ `mrAtomicTrace_table, dsNs ++ `lmTraceAuthorityCheck_sound,
        lmNs ++ `lmAtomicHooks_bind_eq_make, lmNs ++ `lmTagTrace_reserved_vs_frozen,
        dsNs ++ `mrFrozenAndReservedTrace_table, dsNs ++ `lmFrozenTraceAuthorityCheck_sound,
        lmNs ++ `lmSignedBoundaryObs_table, dsNs ++ `mrSignedBoundary_table, dsNs ++ `lmSignedBoundaryAuthorityCheck_sound,
        lmNs ++ `compareExchange_nonwrite_and_choice_invariants, dsNs ++ `contract_tcb_codec_bridge, dsNs ++ `lmReservedTraceAuthorityCheck_sound,
        dsNs ++ `contract_tcb_codec_divergence_exact, dsNs ++ `ep2_atomic_intrinsics_dual_authority_capstone ]
    for n in keyThms do
      let some (.thmInfo v) := env.find? n
        | throwError "cross-root: required theorem {n} missing"
      if isTrivialProp v.type then
        throwError "cross-root: theorem {n} is trivial"
      for a in ← collectAxioms n do
        if a == ``sorryAx || a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
          throwError "cross-root: theorem {n} depends on forbidden axiom {a}"
        unless isStdAx a do
          throwError "cross-root: theorem {n} depends on non-standard axiom {a}"
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

    -- Transitive constant reachability BFS from closed `ep2_atomic_intrinsics_dual_authority_capstone`
    -- (via `closedAtomicDualContract`) to BOTH MiniRust (`evalIntrinsic` / `evalIntrinsicM`) AND all
    -- 11 public defs of vendored `Miri.Interpreter.IntrinsicAtomic` + `AtomicMachine.bind` + `PlaceMachine.memoryAccess`.
    let mut reach : NameSet := {}
    let mut todo : Array Lean.Name := #[ns ++ `ep2_atomic_intrinsics_dual_authority_capstone]
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if reach.contains n then continue
      reach := reach.insert n
      if let some ci := env.find? n then
        for d in ci.getUsedConstantsAsSet do
          if !reach.contains d then todo := todo.push d
    let requiredReach : List Lean.Name :=
      [ contractName,
        dsNs ++ `ep2_atomic_intrinsics_dual_authority_capstone,
        `MiniRustSpec.Interp.evalIntrinsic,
        `MiniRustSpec.Interp.evalIntrinsicM,
        `MiniRustSpec.AtomicIntrinsicsMR.ep1_minirust_atomic_intrinsics_capstone,
        dsNs ++ `mrAtomicObserve,
        dsNs ++ `mrAtomicObserve_table,
        lmNs ++ `lmAtomicObserve,
        lmNs ++ `lmAtomicObserveWith, lmNs ++ `lmTreeBorrowsDiagnostic,
        `Miri.Interpreter.IntrinsicAtomic.allowDataRaces,
        `Miri.Interpreter.IntrinsicAtomic.access,
        `Miri.Interpreter.IntrinsicAtomic.dispatch,
        `Miri.Interpreter.IntrinsicAtomic.load,
        `Miri.Interpreter.IntrinsicAtomic.store,
        `Miri.Interpreter.IntrinsicAtomic.rmwValue,
        `Miri.Interpreter.IntrinsicAtomic.rmw,
        `Miri.Interpreter.IntrinsicAtomic.compareExchange,
        `Miri.Interpreter.IntrinsicAtomic.fence,
        `Miri.Interpreter.IntrinsicAtomic.eval,
        `Miri.Interpreter.AtomicMachine.bind,
        `Miri.Interpreter.PlaceMachine.memoryAccess,
        `Miri.TreeBorrows.BorrowTree.performBorrowAccessRange ]
    for req in requiredReach do
      unless reach.contains req do
        throwError "cross-root reachability failure: closed ep2_atomic_intrinsics_dual_authority_capstone does not reach {req}"
    -- Verify 11th `IntrinsicAtomic` public def (`pointerBinary`) is reached from `pointerBinary_laws`.
    let mut pbReach : NameSet := {}
    let mut pbTodo : Array Lean.Name := #[lmNs ++ `pointerBinary_laws]
    while !pbTodo.isEmpty do
      let n := pbTodo.back!
      pbTodo := pbTodo.pop
      if pbReach.contains n then continue
      pbReach := pbReach.insert n
      if let some ci := env.find? n then
        for d in ci.getUsedConstantsAsSet do
          if !pbReach.contains d then pbTodo := pbTodo.push d
    unless pbReach.contains `Miri.Interpreter.IntrinsicAtomic.pointerBinary do
      throwError "cross-root reachability failure: pointerBinary_laws does not reach IntrinsicAtomic.pointerBinary"
    -- `borrowTracker = none` at runtime (contract reaches `performBorrowAccessRange` only via a
    -- dead branch), so the bridge theorem's *statement* must tie it to the executed diagnostic.
    let tbBridge := lmNs ++ `atomic_tb_check_bridges_vendored_performBorrowAccessRange
    let some tbCi := env.find? tbBridge | throwError "cross-root: {tbBridge} missing"
    for req in [`Miri.TreeBorrows.BorrowTree.performBorrowAccessRange,
                lmNs ++ `lmTreeBorrowsDiagnostic] do
      unless tbCi.type.getUsedConstants.contains req do
        throwError "cross-root: {tbBridge} statement does not mention {req}"

    return (added.size, rejected, crAxioms.toArray)

  let ctx : Core.Context :=
    { fileName := "<atomics-cross-root>", fileMap := default, options := opts, maxHeartbeats := 0 }
  let ((addedCount, rejectedCount, crAxioms), _) ←
    liftCoreM <| act.toIO ctx { env := baseEnv }
  unless addedCount = 29 && rejectedCount = 12 do
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
      ``Anneal.Mir.AtomicIntrinsicsDualSpec.lmAuthorityCheck_sound,
      ``Anneal.Mir.AtomicIntrinsicsDualSpec.casOldProjection_casFlagSynth ]
  for d in constructiveDecls do
    let axs ← liftCoreM <| Lean.collectAxioms d
    for a in axs do
      unless a == ``propext || a == ``Quot.sound do
        throwError "constructive audit failure: {d} uses non-constructive axiom {a}"
  let mut theorems : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "test audit failure: {c} uses sorryAx"
      if a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
        throwError "test audit failure: {c} uses {a}"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "test audit failure: {c} uses non-standard axiom {a}"
    if (`Anneal.Mir.AtomicIntrinsicsDualSpecTests).isPrefixOf c then
      if let .thmInfo _ := info then theorems := theorems + 1
  if theorems < 6 then
    throwError "test audit is vacuous: only {theorems} test theorems seen"
  logInfo m!"atomics constructive audit: verified {constructiveDecls.length} declarations in [propext, Quot.sound] and {theorems} test theorems (0 Classical.choice, 0 sorryAx, 0 ofReduceBool)"

end Anneal.Mir.AtomicIntrinsicsDualSpecTests
