/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import LeanMiriSpec.HeapAllocAndWidePtrLM

/-!
# Episode 2 Heap Allocation & Wide-Pointer Tests and Cross-Root 3-Way Kernel Bridge

Elaborated with `lake --dir examples env lean`, whose `LEAN_PATH` holds
`examples/.lake/build/lib/lean` only, so the top level imports ONLY `Lean` and
`LeanMiriSpec.HeapAllocAndWidePtrLM`; the root-package modules
(`Anneal.Mir.HeapAllocAndWidePtrDualSpec`, `MiniRustSpec.HeapAllocAndWidePtrMR`,
`Trusted.*`) are loaded from `.lake/build/lib/lean` into a fresh kernel environment
in §2.

1. **§1. LeanMiri positive witnesses & fail-closed boundaries** (top-level theorems on
   `LeanMiriSpec.HeapAllocAndWidePtrLM`, reusing its kernel-evaluated tables): heap
   allocation / round-trip, double-free and use-after-free UB, deallocation guards,
   `StaticAllocator` (`rust#166221`) `.machine .global` dealloc UB and `LeakCheck.take`
   exemption vs. `.machine .rust` leak detection, `WeakProtector` / released / `Cell`
   success vs. `StrongProtector` UB and wrong-tag `Frozen` UB (`rust#165833`), slice /
   vtable / heterogeneous `addr_eq = true` vs `== = false` (`rust#166144`), and the
   `Align::MAX` boundary.
2. **§2. Cross-root 3-way kernel bridge (`run_cmd`)**: `LmHeapWideObs.rec` translation,
   `Eq.refl Bool.true` certificates for `lmAuthorityCheck`,
   `lmLifecycleTraceAuthorityCheck`, and the mode-sensitive
   `lmProtectorTraceAuthorityCheck` (on the kernel-evaluable `…U` twins, transported to
   the source observers along their kernel-checked `eq_src` equations), the closed
   `HeapWideDualContract` and capstone, root-package witnesses re-instantiated,
   ≥ 12 kernel-rejected forgeries, axiom / self-test audits, and 3-way transitive
   reachability to `MiniRustSpec.Interp`, vendored `Miri.*`, and
   `Trusted.Rustc.V2026_06_01.MirSemantics`.
3. **§3. Test-module axiom audit (`run_cmd`)**.
-/

namespace Anneal.Mir.HeapAllocAndWidePtrDualSpecTests

set_option Elab.async false

open LeanMiriSpec.HeapAllocAndWidePtrLM
open Miri.ABI (Align)

/-! ## §1. LeanMiri Positive Witnesses & Fail-Closed Boundary Tests -/

/-- Read one cell out of a `List.range 30` table equation. -/
theorem lm_cell {α : Type} {f : Nat → α} {l : List α}
    (h : (List.range 30).map f = l) (i : Nat) (hi : i < 30) : some (f i) = l[i]? := by
  subst h
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- Cell of the `treeBorrows = false` table. -/
theorem lm_basic (i : Nat) (hi : i < 30) :
    some (lmHeapWideObserve false i) =
      ([.okAlloc 0 1, .okAlloc 0 32, .okRoundTrip 3735928559, .okRoundTrip 81985529216486895,
        .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub,
        .memoryLeak, .okDealloc, .okDealloc,
        .okDealloc, .okDealloc, .okDealloc, .okDealloc, .okDealloc,
        .okBool true, .okBool false, .okBool true, .okBool false, .okBool true,
        .invalidOrUnsupported, .ub] : List LmHeapWideObs)[i]? :=
  lm_cell lmHeapWideObserve_table.1 i hi

/-- Cell of the `treeBorrows = true` table. -/
theorem lm_tb (i : Nat) (hi : i < 30) :
    some (lmHeapWideObserve true i) =
      ([.okAlloc 0 1, .okAlloc 0 32, .okRoundTrip 3735928559, .okRoundTrip 81985529216486895,
        .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub,
        .memoryLeak, .okDealloc, .okDealloc,
        .okDealloc, .ub, .okDealloc, .ub, .okDealloc,
        .okBool true, .okBool false, .okBool true, .okBool false, .okBool true,
        .invalidOrUnsupported, .ub] : List LmHeapWideObs)[i]? :=
  lm_cell lmHeapWideObserve_table.2 i hi

/-- Positive: zero-sized / over-aligned heap allocation and `u32` / over-aligned `u64`
round trips through real `Miri.Memory.MemoryLifecycle`, in both modes. -/
theorem lm_alloc_roundtrip_positive (tb : Bool) :
    lmHeapWideObserve tb 0 = .okAlloc 0 1 ∧ lmHeapWideObserve tb 1 = .okAlloc 0 32 ∧
    lmHeapWideObserve tb 2 = .okRoundTrip 3735928559 ∧
    lmHeapWideObserve tb 3 = .okRoundTrip 81985529216486895 := by
  cases tb
  · exact ⟨Option.some.inj (lm_basic 0 (by decide)), Option.some.inj (lm_basic 1 (by decide)),
      Option.some.inj (lm_basic 2 (by decide)), Option.some.inj (lm_basic 3 (by decide))⟩
  · exact ⟨Option.some.inj (lm_tb 0 (by decide)), Option.some.inj (lm_tb 1 (by decide)),
      Option.some.inj (lm_tb 2 (by decide)), Option.some.inj (lm_tb 3 (by decide))⟩

/-- Fail-closed: uninitialized load, non-power-of-two alignment, oversized allocation,
double-free and use-after-free are UB in both modes, with the exact vendored failures. -/
theorem lm_double_free_uaf_guards_ub (tb : Bool) :
    lmHeapWideObserve tb 4 = .ub ∧ lmHeapWideObserve tb 5 = .ub ∧ lmHeapWideObserve tb 6 = .ub ∧
    lmHeapWideObserve tb 7 = .ub ∧ lmHeapWideObserve tb 8 = .ub ∧
    lmCaseFailure false 7 = some (.dealloc (.useAfterFree lmFirstId)) ∧
    lmCaseFailure false 8 = some (.access (.allocationLookup (.deadAllocation lmFirstId))) := by
  have h7 := lm_cell lmCaseFailure_table_basic 7 (by decide)
  have h8 := lm_cell lmCaseFailure_table_basic 8 (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, Option.some.inj (h7.trans rfl), Option.some.inj (h8.trans rfl)⟩ <;>
    cases tb <;> first
      | exact Option.some.inj (lm_basic _ (by decide))
      | exact Option.some.inj (lm_tb _ (by decide))

/-- Fail-closed deallocation guards: interior offset, size / alignment mismatch, and a
provenance-free pointer are UB in both modes. -/
theorem lm_dealloc_guards_ub (tb : Bool) :
    lmHeapWideObserve tb 9 = .ub ∧ lmHeapWideObserve tb 10 = .ub ∧
    lmHeapWideObserve tb 11 = .ub ∧ lmHeapWideObserve tb 12 = .ub := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> cases tb <;> first
    | exact Option.some.inj (lm_basic _ (by decide))
    | exact Option.some.inj (lm_tb _ (by decide))

/-- `rust#166221` (`StaticAllocator`): heap `deallocate` of `.machine .global` / stack
memory is UB (`memoryKindMismatch`), while an unfreed `.machine .global` allocation is
exempt from the leak check that reports `.machine .rust` memory. -/
theorem lm_static_allocator_rust166221 (tb : Bool) :
    lmHeapWideObserve tb 13 = .ub ∧ lmHeapWideObserve tb 14 = .ub ∧
    lmHeapWideObserve tb 15 = .memoryLeak ∧ lmHeapWideObserve tb 16 = .okDealloc ∧
    lmHeapWideObserve tb 17 = .okDealloc ∧
    lmCaseFailure false 13 = some (.dealloc (.memoryKindMismatch lmFirstId)) ∧
    Miri.Interpreter.LeakCheck.mayLeak (.machine .rust) = false ∧
    Miri.Interpreter.LeakCheck.mayLeak (.machine .global) = true := by
  have h13 := lm_cell lmCaseFailure_table_basic 13 (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, Option.some.inj (h13.trans rfl), leakCheck_mayLeak_rust_global.1,
    leakCheck_mayLeak_rust_global.2.1⟩ <;> cases tb <;> first
    | exact Option.some.inj (lm_basic _ (by decide))
    | exact Option.some.inj (lm_tb _ (by decide))

/-- `LeakCheck.take` never reports `.machine .global` memory (universal). -/
theorem lm_leakCheck_take_exempts_global :
    type_of% @leakCheck_take_never_reports_global := @leakCheck_take_never_reports_global

/-- `rust#165833`: the strongly protected, accessed `Frozen` child makes parent
deallocation UB (`ProtectedDisabled`) under Tree Borrows only (case `19`). -/
theorem lm_strong_protector_ub :
    lmHeapWideObserve false 19 = .okDealloc ∧ lmHeapWideObserve true 19 = .ub ∧
    lmCaseFailure true 19 = some (.treeDealloc (.AccessFailure (.AccessFailure ⟨0, 4⟩
      (.TransitionError 1 (.ProtectedDisabled .Frozen))))) := by
  have h := lm_cell lmCaseFailure_table_tb 19 (by decide)
  exact ⟨Option.some.inj (lm_basic 19 (by decide)), Option.some.inj (lm_tb 19 (by decide)),
    Option.some.inj (h.trans rfl)⟩

/-- `rust#165833`: `WeakProtector` `Box` (`18`), released protector (`20`) and protected
`Cell` (`22`) deallocations succeed even with Tree Borrows; the `BorrowTree` statuses. -/
theorem lm_weak_released_cell_ok :
    lmHeapWideObserve true 18 = .okDealloc ∧ lmHeapWideObserve true 20 = .okDealloc ∧
    lmHeapWideObserve true 22 = .okDealloc ∧
    lmScenarioDeallocStatus .globalBox lmFrozenFacts .Box .FnEntry true false false true =
      some .Deallocated ∧
    lmScenarioDeallocStatus .reference lmFrozenFacts .Shared .FnEntry true true true false =
      some .Deallocated ∧
    lmScenarioDeallocStatus .reference lmCellFacts .Shared .FnEntry false false false false =
      some .Deallocated :=
  ⟨Option.some.inj (lm_tb 18 (by decide)), Option.some.inj (lm_tb 20 (by decide)),
    Option.some.inj (lm_tb 22 (by decide)), deallocateBorrowRange_protector_laws.1,
    deallocateBorrowRange_protector_laws.2.2.2.1, deallocateBorrowRange_protector_laws.2.2.2.2.2⟩

/-- `rust#165833`: deallocating through an unprotected `Frozen` child tag is UB under
Tree Borrows (`ChildAccessForbidden`, case `21`), and fine without a borrow tracker. -/
theorem lm_wrong_tag_frozen_ub :
    lmHeapWideObserve false 21 = .okDealloc ∧ lmHeapWideObserve true 21 = .ub ∧
    lmCaseFailure true 21 = some (.treeDealloc (.AccessFailure (.AccessFailure ⟨0, 32⟩
      (.TransitionError 1 (.ChildAccessForbidden .Frozen))))) := by
  have h := lm_cell lmCaseFailure_table_tb 21 (by decide)
  exact ⟨Option.some.inj (lm_basic 21 (by decide)), Option.some.inj (lm_tb 21 (by decide)),
    Option.some.inj (h.trans rfl)⟩

/-- `rust#166144`: `addr_eq` erases slice lengths, vtables, and heterogeneous metadata
(`true`), while full wide `==` compares metadata (`false`), in both modes. -/
theorem lm_addr_eq_vs_eq_rust166144 (tb : Bool) :
    lmHeapWideObserve tb 23 = .okBool true ∧ lmHeapWideObserve tb 24 = .okBool false ∧
    lmHeapWideObserve tb 25 = .okBool true ∧ lmHeapWideObserve tb 26 = .okBool false ∧
    lmHeapWideObserve tb 27 = .okBool true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> cases tb <;> first
    | exact Option.some.inj (lm_basic _ (by decide))
    | exact Option.some.inj (lm_tb _ (by decide))

/-- Universal LeanMiri `addr_eq` laws: metadata and provenance erasure. -/
theorem lm_addr_eq_universal :
    (type_of% @addrEq_metadata_erased) ∧ (type_of% @thinEq_provenance_erased) ∧
    (type_of% @wideEq_hetero_invalidProgram) :=
  ⟨@addrEq_metadata_erased, @thinEq_provenance_erased, @wideEq_hetero_invalidProgram⟩

/-- Boundary: heterogeneous un-erased `==` is an invalid program (`28`), and
`Align::MAX = 2^29` rejects `2^30` on vendored `Miri.ABI.Align.fromBytes` (`29`). -/
theorem lm_divergence_boundaries (tb : Bool) :
    lmHeapWideObserve tb 28 = .invalidOrUnsupported ∧ lmHeapWideObserve tb 29 = .ub ∧
    Align.fromBytes 1073741824 = .error (.tooLarge 1073741824) ∧
    Align.fromBytes 536870912 = .ok Align.MAX ∧
    lmCaseFailure false 29 = some (.allocAlign (.tooLarge 1073741824)) := by
  have h29 := lm_cell lmCaseFailure_table_basic 29 (by decide)
  refine ⟨?_, ?_, align_fromBytes_boundary.2.1, align_fromBytes_boundary.1,
    Option.some.inj (h29.trans rfl)⟩ <;> cases tb <;> first
    | exact Option.some.inj (lm_basic _ (by decide))
    | exact Option.some.inj (lm_tb _ (by decide))

/-- Mode sensitivity is exactly `{19, 21}`; out of range is `.invalidOrUnsupported`. -/
theorem lm_mode_sensitive_exact :
    (List.range 30).filter (fun i => lmHeapWideObserve false i != lmHeapWideObserve true i) =
      [19, 21] ∧
    (∀ tb idx, 30 ≤ idx → lmHeapWideObserve tb idx = .invalidOrUnsupported) :=
  ⟨lmHeapWideObserve_mode_sensitive, lmHeapWideObserve_out_of_range⟩

/-- Both threaded traces on ONE evolving LeanMiri state. -/
theorem lm_threaded_traces :
    lmHeapLifecycleTrace false = lmHeapLifecycleTrace true ∧
    lmHeapLifecycleTrace true =
      [.okAlloc 32 32, .okRoundTrip 14627333968688404088, .memoryLeak, .okBool true,
        .okDealloc, .ub] ∧
    lmProtectorDeallocTrace false = [.okRoundTrip 42, .okBool true, .okDealloc, .okDealloc] ∧
    lmProtectorDeallocTrace true = [.okRoundTrip 42, .okBool true, .ub] ∧
    lmProtectorDeallocTrace false ≠ lmProtectorDeallocTrace true := by
  refine ⟨?_, lmHeapLifecycleTrace_table.2, lmProtectorDeallocTrace_table.1,
    lmProtectorDeallocTrace_table.2, ?_⟩
  · rw [lmHeapLifecycleTrace_table.1, lmHeapLifecycleTrace_table.2]
  · rw [lmProtectorDeallocTrace_table.1, lmProtectorDeallocTrace_table.2]; decide

/-- Linkage to Episode 1's universal LeanMiri capstone. -/
theorem lm_ep1_capstone_linked :
    type_of% @ep1_lean_miri_heap_wide_capstone := @ep1_lean_miri_heap_wide_capstone

/-! ## §2. Cross-Root 3-Way Kernel Bridge (`MiniRustSpec` + `LeanMiriSpec` + `Trusted`) -/

open Lean Elab Command Meta in
run_cmd do
  let opts := (← getOptions).setBool `Elab.async false
  let sp : SearchPath := [System.FilePath.mk ".lake/build/lib/lean",
                          System.FilePath.mk "examples/.lake/build/lib/lean"]
  initSearchPath (← findSysroot) sp
  let baseEnv ← importModules
    #[{ module := `Anneal.Mir.HeapAllocAndWidePtrDualSpec },
      { module := `MiniRustSpec.HeapAllocAndWidePtrMR },
      { module := `LeanMiriSpec.HeapAllocAndWidePtrLM }]
    {} 0
  let ns := `Anneal.Mir.HeapAllocAndWidePtrDualSpecTests.CrossRoot
  let dsNs := `Anneal.Mir.HeapAllocAndWidePtrDualSpec
  let lmNs := `LeanMiriSpec.HeapAllocAndWidePtrLM
  let act : CoreM (Nat × Nat × Array Lean.Name) := do
    let addDef (name : Lean.Name) (val : Expr) : CoreM Unit := do
      let ty ← MetaM.run' <| inferType val
      addDecl <| .defnDecl {
        name, levelParams := [], type := ty, value := val,
        hints := .regular 0, safety := .safe }
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
    let lmObsTy := mkConst (lmNs ++ `LmHeapWideObs)
    let obsTy := mkConst (dsNs ++ `HeapWideObs)
    let obsC (c : String) : Expr := mkConst (dsNs ++ `HeapWideObs ++ Lean.Name.mkSimple c)
    let listMap (f l : Expr) : Expr := mkApp4 (mkConst ``List.map [.zero, .zero]) lmObsTy obsTy f l
    let modeBasic := mkConst (dsNs ++ `HeapWideMemoryMode.basic)
    let modeTb := mkConst (dsNs ++ `HeapWideMemoryMode.treeBorrows)

    -- Translator `LmHeapWideObs → HeapWideObs` via `LmHeapWideObs.rec.{1}` (zero mocks),
    -- with corruption flags for the negative controls.
    let mkTranslate (invertBool forgeUb forgeLeak forgeInvalid : Bool := false) : MetaM Expr := do
      let motive := mkLambda `x .default lmObsTy obsTy
      let brAlloc ← withLocalDeclD `sz natTy fun sz => withLocalDeclD `al natTy fun al =>
        mkLambdaFVars #[sz, al] (mkApp2 (obsC "okAlloc") sz al)
      let brRt ← withLocalDeclD `bits natTy fun b =>
        mkLambdaFVars #[b] (mkApp (obsC "okRoundTrip") b)
      let brBool ← withLocalDeclD `v boolTy fun v =>
        mkLambdaFVars #[v] (mkApp (obsC "okBool") (if invertBool then mkApp (mkConst ``Bool.not) v else v))
      let brLeak := if forgeLeak then obsC "okDealloc" else obsC "memoryLeak"
      let brUb := if forgeUb then obsC "okDealloc" else obsC "ub"
      let brInvalid := if forgeInvalid then obsC "specPanic" else obsC "invalidOrUnsupported"
      withLocalDeclD `o lmObsTy fun o => do
        let recApp := mkAppN (mkConst (lmNs ++ `LmHeapWideObs.rec) [1])
          #[motive, brAlloc, brRt, obsC "okDealloc", brBool, brLeak, brUb, obsC "specPanic",
            brInvalid, o]
        mkLambdaFVars #[o] recApp
    -- Observation function over a 2-argument LeanMiri observer `f`.
    let mkObs (tr f : Expr) (invertMode shiftCase : Bool := false) : MetaM Expr :=
      withLocalDeclD `tb boolTy fun tb => withLocalDeclD `idx natTy fun idx => do
        let tb' := if invertMode then mkApp (mkConst ``Bool.not) tb else tb
        let idx' := if shiftCase then mkApp2 (mkConst ``Nat.add) idx (mkNatLit 1) else idx
        mkLambdaFVars #[tb, idx] (mkApp tr (mkApp2 f tb' idx'))
    -- Trace observation over a 1-argument LeanMiri trace `f`.
    let mkTrace (tr f : Expr) (invertMode : Bool := false) : MetaM Expr :=
      withLocalDeclD `tb boolTy fun tb => do
        let tb' := if invertMode then mkApp (mkConst ``Bool.not) tb else tb
        mkLambdaFVars #[tb] (listMap tr (mkApp f tb'))

    -- 1. Genuine translator.
    let translateName := ns ++ `translateLmObs
    addDef translateName (← MetaM.run' <| mkTranslate)
    let trC := mkConst translateName

    -- 2. Certify a check on the kernel-evaluable `…U` twin by `Eq.refl Bool.true`, then
    -- transport it to the source observer along `eq_src : @src = @srcU`.
    let certify (checkFn : Lean.Name) (mk : Expr → MetaM Expr) (src : Lean.Name) (base : Lean.Name) :
        CoreM (Lean.Name × Lean.Name × Lean.Name × Lean.Name) := do
      let uConst := lmNs ++ Lean.Name.mkSimple ((src.componentsRev.head!.toString) ++ "U")
      let eqSrc := uConst ++ `eq_src
      let obsU := ns ++ (base.appendAfter "U")
      addDef obsU (← MetaM.run' <| mk (mkConst uConst))
      let obs := ns ++ base
      addDef obs (← MetaM.run' <| mk (mkConst src))
      let checkU := ns ++ (base.appendAfter "CheckU")
      addThm checkU (eqTrue (mkApp (mkConst checkFn) (mkConst obsU))) reflTrue
      let srcTy ← MetaM.run' <| inferType (mkConst src)
      let F ← MetaM.run' <| withLocalDeclD `g srcTy fun g => do
        mkLambdaFVars #[g] (mkApp (mkConst checkFn) (← mk g))
      let congr := mkApp6 (mkConst ``congrArg [1, 1]) srcTy boolTy (mkConst src) (mkConst uConst) F
        (mkConst eqSrc)
      let pf := mkApp6 (mkConst ``Eq.trans [1]) boolTy (mkApp (mkConst checkFn) (mkConst obs))
        (mkApp (mkConst checkFn) (mkConst obsU)) boolTrue congr (mkConst checkU)
      let check := ns ++ (base.appendAfter "Check")
      addThm check (eqTrue (mkApp (mkConst checkFn) (mkConst obs))) pf
      return (obs, obsU, check, checkU)

    let (crossObs, crossObsU, crossCheck, crossCheckU) ←
      certify (dsNs ++ `lmAuthorityCheck) (fun f => mkObs trC f) (lmNs ++ `lmHeapWideObserve)
        `crossRootLmObs
    let (lcObs, lcObsU, lcCheck, lcCheckU) ←
      certify (dsNs ++ `lmLifecycleTraceAuthorityCheck) (fun f => mkTrace trC f)
        (lmNs ++ `lmHeapLifecycleTrace) `crossRootLmLifecycle
    let (ptObs, ptObsU, ptCheck, ptCheckU) ←
      certify (dsNs ++ `lmProtectorTraceAuthorityCheck) (fun f => mkTrace trC f)
        (lmNs ++ `lmProtectorDeallocTrace) `crossRootLmProtector

    -- 3. Closed trace soundness theorems.
    let lcEqVal := mkApp2 (mkConst (dsNs ++ `lmLifecycleTraceAuthorityCheck_sound)) (mkConst lcObs)
      (mkConst lcCheck)
    let lcEqName := ns ++ `crossRootLmLifecycleEq
    addThm lcEqName (← MetaM.run' <| inferType lcEqVal) lcEqVal
    let ptEqVal := mkApp2 (mkConst (dsNs ++ `lmProtectorTraceAuthorityCheck_sound)) (mkConst ptObs)
      (mkConst ptCheck)
    let ptEqName := ns ++ `crossRootLmProtectorEq
    addThm ptEqName (← MetaM.run' <| inferType ptEqVal) ptEqVal

    -- 4. Wire-level positive controls on agreeing cells (incl. mode-sensitive `(treeBorrows, 19)`).
    let wireAt (obs : Lean.Name) (m : Expr) (idx : Nat) : Expr :=
      eqTrue (mkApp3 (mkConst (dsNs ++ `wireAgreesAt)) (mkConst obs) m (mkNatLit idx))
    let wire0 := ns ++ `crossRootWireAgreesBasic0
    addThm wire0 (wireAt crossObsU modeBasic 0) reflTrue
    let wire19 := ns ++ `crossRootWireAgreesTb19
    addThm wire19 (wireAt crossObsU modeTb 19) reflTrue
    let wire27 := ns ++ `crossRootWireAgreesTb27
    addThm wire27 (wireAt crossObsU modeTb 27) reflTrue

    -- 5. Closed `HeapWideDualContract`, every named projection, and the closed capstone.
    let contractName := ns ++ `closedHeapWideDualContract
    addDef contractName (mkAppN (mkConst (dsNs ++ `heapWideDualContractOfChecks))
      #[mkConst crossObs, mkConst lcObs, mkConst ptObs, mkConst crossCheck, mkConst lcCheck,
        mkConst ptCheck])
    let some (.defnInfo cInfo) := (← getEnv).find? contractName
      | throwError "cross-root: contract missing"
    unless cInfo.type.isConstOf (dsNs ++ `HeapWideDualContract) do
      throwError "cross-root: {contractName} is not a HeapWideDualContract"
    let contractC := mkConst contractName
    let mut added : Array Lean.Name :=
      #[translateName, crossObs, crossObsU, crossCheck, crossCheckU, lcObs, lcObsU, lcCheck, lcCheckU,
        ptObs, ptObsU, ptCheck, ptCheckU, lcEqName, ptEqName, wire0, wire19, wire27, contractName]
    for projName in [`contract_agreement_zone_exact, `contract_divergence_explicit,
                     `contract_mode_sensitivity_joint, `contract_traces,
                     `contract_divergence_set_exact, `contract_wire_divergence_exact,
                     `contract_static_leak_wide_agreement,
                     `ep2_heap_alloc_and_wide_ptr_dual_authority_capstone] do
      let val := mkApp (mkConst (dsNs ++ projName)) contractC
      let ty ← MetaM.run' <| inferType val
      let outName := ns ++ projName
      addThm outName ty val
      added := added.push outName
    -- Root-package witnesses (MiniRust + Trusted bridge) re-instantiated in this environment.
    for w in [`mrObserve_table, `mr_mode_sensitivity, `mrLifecycleTrace_table,
              `mrProtectorTrace_table, `heapWideOutcomeCodec_rejects_malformed,
              `preventsDeallocation_eq_mr, `mr_prevents_deallocation_iff_trusted,
              `hasFrameDeallocProtectorConflict_iff, `hasProtectedLocalBorrow_iff,
              `evalTerminator_return_protector_ub, `evalTailCallTerminator_protector_ub,
              `trustedTeardown_table, `trusted_protector_cases_match_mr,
              `evalCastPtrToPtr_slice_to_thin, `evalCastPtrToPtr_dyn_to_thin,
              `evalCastPtrToPtr_scalarPair_to_thin, `evalRvalue_thinPtr_eq,
              `trustedCmp_table, `trustedRvalue_witnesses, `trusted_wide_cases_match_mr] do
      let src := dsNs ++ w
      let some (.thmInfo v) := (← getEnv).find? src
        | throwError "cross-root: root witness {src} missing"
      let outName := ns ++ `root ++ w
      addThm outName v.type (mkConst src)
      added := added.push outName

    -- 6. Negative controls on scratch copies: the kernel MUST reject every forgery. Every
    -- forgery is built over the kernel-evaluable `…U` twins (whose genuine versions were
    -- accepted above), so each rejection is a real value mismatch, not a stuck reduction.
    let saved ← getEnv
    let rejects (d : Declaration) : CoreM Bool := do
      let r ← try addDecl d; pure false catch _ => pure true
      setEnv saved
      return r
    let lmObsU := mkConst (lmNs ++ `lmHeapWideObserveU)
    let lmLcU := mkConst (lmNs ++ `lmHeapLifecycleTraceU)
    let lmPtU := mkConst (lmNs ++ `lmProtectorDeallocTraceU)
    let authCheck (o : Expr) : Expr := eqTrue (mkApp (mkConst (dsNs ++ `lmAuthorityCheck)) o)
    let modeInv ← MetaM.run' <| mkObs trC lmObsU true false
    let caseShift ← MetaM.run' <| mkObs trC lmObsU false true
    let boolInv ← MetaM.run' <| mkObs (← MetaM.run' <| mkTranslate true false false false) lmObsU
    let ubForged ← MetaM.run' <| mkObs (← MetaM.run' <| mkTranslate false true false false) lmObsU
    let leakForged ← MetaM.run' <| mkObs (← MetaM.run' <| mkTranslate false false true false) lmObsU
    let invForged ← MetaM.run' <| mkObs (← MetaM.run' <| mkTranslate false false false true) lmObsU
    let ptModeInv ← MetaM.run' <| mkTrace trC lmPtU true
    let lcU ← MetaM.run' <| mkTrace trC lmLcU
    -- MiniRust passed off as LeanMiri: must fail exactly on the divergence set.
    let mrAsLm ← MetaM.run' <| withLocalDeclD `tb boolTy fun tb => withLocalDeclD `idx natTy fun idx =>
      mkLambdaFVars #[tb, idx] (mkApp2 (mkConst (dsNs ++ `mrObserve))
        (mkApp (mkConst (dsNs ++ `HeapWideMemoryMode.ofLmTreeBorrows)) tb) idx)
    let thm (n : String) (ty pf : Expr) : Declaration :=
      .thmDecl { name := ns ++ `forged ++ Lean.Name.mkSimple n, levelParams := [], type := ty, value := pf }
    let forged : List (String × Declaration) :=
      [ ("ill-typed 0 = 1 theorem",
          thm "zeroEqOne" (mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 0) (mkNatLit 1))
            (mkApp2 (mkConst ``Eq.refl [1]) natTy (mkNatLit 0))),
        ("negated lmAuthorityCheck certificate (= false)",
          thm "lmCheckFalse" (eqFalse (mkApp (mkConst (dsNs ++ `lmAuthorityCheck)) (mkConst crossObsU)))
            reflFalse),
        ("mode-inverted observer (Bool.not tb) catching cases 19/21", thm "modeInverted" (authCheck modeInv) reflTrue),
        ("case-shifted observer (idx + 1)", thm "caseShifted" (authCheck caseShift) reflTrue),
        ("okBool-inverted translator", thm "boolInverted" (authCheck boolInv) reflTrue),
        ("ub-to-okDealloc forged translator", thm "ubForged" (authCheck ubForged) reflTrue),
        ("memoryLeak-to-okDealloc forged translator", thm "leakForged" (authCheck leakForged) reflTrue),
        ("invalidOrUnsupported-to-specPanic forged translator masking case 28",
          thm "invalidForged" (authCheck invForged) reflTrue),
        ("wire tuples forged equal on diverging cell (basic, 28)",
          thm "wire28" (wireAt crossObsU modeBasic 28) reflTrue),
        ("wire tuples forged equal on diverging cell (treeBorrows, 29)",
          thm "wire29" (wireAt crossObsU modeTb 29) reflTrue),
        ("negated lifecycle trace certificate (= false)",
          thm "lifecycleFalse"
            (eqFalse (mkApp (mkConst (dsNs ++ `lmLifecycleTraceAuthorityCheck)) (mkConst lcObsU))) reflFalse),
        ("mode-inverted protector trace (Bool.not tb)",
          thm "protectorModeInverted"
            (eqTrue (mkApp (mkConst (dsNs ++ `lmProtectorTraceAuthorityCheck)) ptModeInv)) reflTrue),
        ("protector trace passed to the lifecycle check",
          thm "protectorAsLifecycle"
            (eqTrue (mkApp (mkConst (dsNs ++ `lmLifecycleTraceAuthorityCheck)) (mkConst ptObsU))) reflTrue),
        ("lifecycle trace passed to the protector check",
          thm "lifecycleAsProtector"
            (eqTrue (mkApp (mkConst (dsNs ++ `lmProtectorTraceAuthorityCheck)) lcU)) reflTrue),
        ("MiniRust observer passed off as LeanMiri (diverges on 28, 29)",
          thm "mrAsLm" (authCheck mrAsLm) reflTrue) ]
    let mut rejected : Nat := 0
    for (what, d) in forged do
      unless ← rejects d do
        throwError "cross-root negative control FAILED: kernel accepted {what}"
      rejected := rejected + 1

    -- 7. Safety, non-triviality, standard-3-axiom purity, self-tests, reachability.
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
      | .defnInfo v => if v.safety != .safe then throwError "cross-root: {n} is not safe"
      | .thmInfo v => if isTrivialProp v.type then throwError "cross-root: {n} is a trivial theorem"
      | _ => throwError "cross-root: {n} is not a defn or thm"
      for a in ← collectAxioms n do
        if a == ``sorryAx || a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
          throwError "cross-root: {n} depends on forbidden axiom {a}"
        unless isStdAx a do throwError "cross-root: {n} depends on non-standard axiom {a}"
        crAxioms := crAxioms.insert a
    let keyThms : List Lean.Name :=
      [ lmNs ++ `lmHeapWideObserve_table, lmNs ++ `lmCaseFailure_table_basic,
        lmNs ++ `lmCaseFailure_table_tb, lmNs ++ `lmHeapLifecycleTrace_table,
        lmNs ++ `lmProtectorDeallocTrace_table, lmNs ++ `deallocateBorrowRange_protector_laws,
        lmNs ++ `leakCheck_take_never_reports_global, lmNs ++ `align_fromBytes_boundary,
        lmNs ++ `addrEq_metadata_erased, lmNs ++ `ep1_lean_miri_heap_wide_capstone,
        `MiniRustSpec.HeapAllocAndWidePtrMR.ep1_minirust_heap_wide_capstone,
        `MiniRustSpec.HeapAllocAndWidePtrMR.mrHeapWideObserve_table,
        dsNs ++ `ep2_heap_alloc_and_wide_ptr_dual_authority_capstone,
        dsNs ++ `contract_divergence_set_exact, dsNs ++ `contract_wire_divergence_exact,
        dsNs ++ `trustedTeardown_table, dsNs ++ `trustedCmp_table ]
    for n in keyThms do
      let some (.thmInfo v) := env.find? n | throwError "cross-root: required theorem {n} missing"
      if isTrivialProp v.type then throwError "cross-root: theorem {n} is trivial"
      for a in ← collectAxioms n do
        unless isStdAx a do throwError "cross-root: theorem {n} depends on non-standard axiom {a}"
        crAxioms := crAxioms.insert a
    -- Self-tests: the auditor MUST detect sorryAx / ofReduceBool / trustCompiler and trivia.
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
    -- 3-way transitive constant reachability from the CLOSED capstone.
    let mut reach : NameSet := {}
    let mut todo : Array Lean.Name := #[ns ++ `ep2_heap_alloc_and_wide_ptr_dual_authority_capstone]
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if reach.contains n then continue
      reach := reach.insert n
      if let some ci := env.find? n then
        for d in ci.getUsedConstantsAsSet do
          if !reach.contains d then todo := todo.push d
    let requiredReach : List Lean.Name :=
      [ contractName, crossObs, crossCheck, lcCheck, ptCheck,
        dsNs ++ `ep2_heap_alloc_and_wide_ptr_dual_authority_capstone,
        lmNs ++ `lmHeapWideObserve, lmNs ++ `lmHeapWideObserveU,
        `MiniRustSpec.HeapAllocAndWidePtrMR.mrHeapWideObserve,
        `MiniRustSpec.HeapAllocAndWidePtrMR.ep1_minirust_heap_wide_capstone,
        `MiniRustSpec.Interp.evalIntrinsic, `MiniRustSpec.Interp.evalIntrinsicM,
        `MiniRustSpec.Interp.BasicMemory.leak_check, `MiniRustSpec.Interp.TreeBorrowsMemory.deallocate,
        `MiniRustSpec.Interp.comparePtr,
        `Miri.Memory.MemoryLifecycle.allocatePtr, `Miri.Memory.MemoryLifecycle.deallocatePtrWith,
        `Miri.TreeBorrows.BorrowTree.deallocateBorrowRange, `Miri.Interpreter.LeakCheck.take,
        `Miri.Interpreter.Cast.ptrToPtr, `Miri.Interpreter.ExecutionScalar.pointerBinary,
        `Trusted.Rustc.V2026_06_01.MirSemantics.hasFrameDeallocProtectorConflict,
        `Trusted.Rustc.V2026_06_01.MirSemantics.preventsDeallocation,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalCastPtrToPtr,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalTerminator,
        `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue ]
    for req in requiredReach do
      unless reach.contains req do
        throwError "cross-root reachability failure: closed capstone does not reach {req}"
    return (added.size, rejected, crAxioms.toArray)

  let ctx : Core.Context :=
    { fileName := "<heap-wide-cross-root>", fileMap := default, options := opts, maxHeartbeats := 0 }
  let ((addedCount, rejectedCount, crAxioms), _) ← liftCoreM <| act.toIO ctx { env := baseEnv }
  unless addedCount = 47 && rejectedCount = 15 do
    throwError "cross-root: unexpected counts (added={addedCount}, rejected={rejectedCount})"
  logInfo m!"heap/wide cross-root kernel bridge: added {addedCount} declarations, rejected {rejectedCount} forged controls, reached MiniRust+Miri+Trusted, axioms {crAxioms}"

/-! ## §3. Test Module Axiom Audit -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut theorems : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    for a in ← liftCoreM <| Lean.collectAxioms c do
      if a == ``sorryAx then throwError "test audit failure: {c} uses sorryAx"
      if a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
        throwError "test audit failure: {c} uses {a}"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "test audit failure: {c} uses non-standard axiom {a}"
    if (`Anneal.Mir.HeapAllocAndWidePtrDualSpecTests).isPrefixOf c then
      if let .thmInfo _ := info then theorems := theorems + 1
  if theorems < 12 then
    throwError "test audit is vacuous: only {theorems} test theorems seen"
  logInfo m!"heap/wide test audit: {theorems} §1 theorems (0 sorryAx, 0 ofReduceBool, 0 trustCompiler)"

end Anneal.Mir.HeapAllocAndWidePtrDualSpecTests
