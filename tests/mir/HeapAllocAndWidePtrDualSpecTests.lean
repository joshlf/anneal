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
open Miri.ABI (Align Size)

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

/-- Opposite-polarity LeanMiri `addr_eq` twins (vendored `Cast.ptrToPtr` +
`ExecutionScalar.pointerBinary`): heterogeneous slice / `dyn` pointers at DISTINCT thin
addresses give `false`, at the same address `true` (so case `27`'s `true` is not a
constant), and full slice `==` with equal length gives `true` (so case `24`'s `false` is
not a constant either). -/
theorem lm_addr_eq_polarity_twins :
    lmCompare lmAddrEq (lmSlice ⟨Size.ofBytes 8192, none⟩ 5)
        (lmDyn ⟨Size.ofBytes 12288, none⟩ (lmAddr 36864)) = .ok (.okBool false) ∧
    lmCompare lmAddrEq (lmSlice ⟨Size.ofBytes 8192, none⟩ 5)
        (lmDyn ⟨Size.ofBytes 8192, none⟩ (lmAddr 36864)) = .ok (.okBool true) ∧
    lmCompare lmEq (lmSlice ⟨Size.ofBytes 8192, none⟩ 3)
        (lmSlice ⟨Size.ofBytes 8192, none⟩ 3) = .ok (.okBool true) ∧
    lmCompare lmEq (lmSlice ⟨Size.ofBytes 8192, none⟩ 3)
        (lmSlice ⟨Size.ofBytes 8192, none⟩ 7) = .ok (.okBool false) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

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

    -- 4. Wire-level positive controls on agreeing cells (incl. BOTH mode-sensitive cells
    -- `(treeBorrows, 19)` and `(treeBorrows, 21)`) and wire-disagreement controls on ALL
    -- 4 diverging cells `(basic/treeBorrows, 28/29)`, transported from `crossObsU` to the
    -- source `crossObs` via `lmHeapWideObserveU.eq_src`.
    let wireExpr (obs : Expr) (m : Expr) (idx : Nat) : Expr :=
      mkApp3 (mkConst (dsNs ++ `wireAgreesAt)) obs m (mkNatLit idx)
    let certifyWire (base : Lean.Name) (m : Expr) (idx : Nat) (expected : Bool) :
        CoreM (Lean.Name × Lean.Name) := do
      let uName := ns ++ (base.appendAfter "U")
      let sName := ns ++ base
      let rhs := if expected then boolTrue else boolFalse
      let refl := if expected then reflTrue else reflFalse
      let eqRhs (e : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) boolTy e rhs
      addThm uName (eqRhs (wireExpr (mkConst crossObsU) m idx)) refl
      let srcTy ← MetaM.run' <| inferType (mkConst (lmNs ++ `lmHeapWideObserve))
      let F ← MetaM.run' <| withLocalDeclD `g srcTy fun g => do
        mkLambdaFVars #[g] (wireExpr (← mkObs trC g) m idx)
      let congr := mkApp6 (mkConst ``congrArg [1, 1]) srcTy boolTy
        (mkConst (lmNs ++ `lmHeapWideObserve)) (mkConst (lmNs ++ `lmHeapWideObserveU)) F
        (mkConst (lmNs ++ `lmHeapWideObserveU.eq_src))
      let pf := mkApp6 (mkConst ``Eq.trans [1]) boolTy
        (wireExpr (mkConst crossObs) m idx) (wireExpr (mkConst crossObsU) m idx) rhs
        congr (mkConst uName)
      addThm sName (eqRhs (wireExpr (mkConst crossObs) m idx)) pf
      return (uName, sName)
    let (wire0U, wire0) ← certifyWire `crossRootWireAgreesBasic0 modeBasic 0 true
    let (wire19U, wire19) ← certifyWire `crossRootWireAgreesTb19 modeTb 19 true
    let (wire21U, wire21) ← certifyWire `crossRootWireAgreesTb21 modeTb 21 true
    let (wire27U, wire27) ← certifyWire `crossRootWireAgreesTb27 modeTb 27 true
    let (wire28BU, wire28B) ← certifyWire `crossRootWireDivergesBasic28 modeBasic 28 false
    let (wire28TU, wire28T) ← certifyWire `crossRootWireDivergesTb28 modeTb 28 false
    let (wire29BU, wire29B) ← certifyWire `crossRootWireDivergesBasic29 modeBasic 29 false
    let (wire29TU, wire29T) ← certifyWire `crossRootWireDivergesTb29 modeTb 29 false

    -- 4b. Out-of-range fail-closedness of the SOURCE observer (all `idx ≥ 30`), transported
    -- through the genuine translator from `lmHeapWideObserve_out_of_range`: this makes the
    -- contract's classification total over `Nat` (`contract_total_divergence_exact`).
    let outName := ns ++ `crossRootLmOutOfRange
    let (outTy, outPf) ← MetaM.run' <| withLocalDeclD `tb boolTy fun tb =>
      withLocalDeclD `idx natTy fun idx => do
        let hTy := mkApp4 (mkConst ``LE.le [0]) natTy (mkConst ``instLENat)
          (mkConst (dsNs ++ `canonicalCaseCount)) idx
        withLocalDeclD `h hTy fun h => do
          let lmOut := mkApp3 (mkConst (lmNs ++ `lmHeapWideObserve_out_of_range)) tb idx h
          let pf := mkApp6 (mkConst ``congrArg [1, 1]) lmObsTy obsTy
            (mkApp2 (mkConst (lmNs ++ `lmHeapWideObserve)) tb idx)
            (mkConst (lmNs ++ `LmHeapWideObs.invalidOrUnsupported)) trC lmOut
          let body := mkApp3 (mkConst ``Eq [1]) obsTy (mkApp2 (mkConst crossObs) tb idx)
            (obsC "invalidOrUnsupported")
          return (← mkForallFVars #[tb, idx, h] body, ← mkLambdaFVars #[tb, idx, h] pf)
    addThm outName outTy outPf

    -- 5. Closed `HeapWideDualContract`, every named projection, and the closed capstone.
    let contractName := ns ++ `closedHeapWideDualContract
    addDef contractName (mkAppN (mkConst (dsNs ++ `heapWideDualContractOfChecks))
      #[mkConst crossObs, mkConst lcObs, mkConst ptObs, mkConst crossCheck, mkConst lcCheck,
        mkConst ptCheck, mkConst outName])
    let some (.defnInfo cInfo) := (← getEnv).find? contractName
      | throwError "cross-root: contract missing"
    unless cInfo.type.isConstOf (dsNs ++ `HeapWideDualContract) do
      throwError "cross-root: {contractName} is not a HeapWideDualContract"
    let contractC := mkConst contractName
    let mut added : Array Lean.Name :=
      #[translateName, crossObs, crossObsU, crossCheck, crossCheckU, lcObs, lcObsU, lcCheck, lcCheckU,
        ptObs, ptObsU, ptCheck, ptCheckU, lcEqName, ptEqName,
        wire0U, wire0, wire19U, wire19, wire21U, wire21, wire27U, wire27,
        wire28BU, wire28B, wire28TU, wire28T, wire29BU, wire29B, wire29TU, wire29T, outName,
        contractName]
    for projName in [`contract_agreement_zone_exact, `contract_divergence_explicit,
                     `contract_mode_sensitivity_joint, `contract_traces,
                     `contract_divergence_set_exact, `contract_wire_divergence_exact,
                     `contract_static_leak_wide_agreement,
                     `contract_total_divergence_exact, `contract_total_wire_divergence_exact,
                     `contract_out_of_range_agreement, `contract_trusted_lm_agreement,
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
              `hasFrameDeallocProtectorConflict_eq_mr_node, `hasProtectedLocalBorrow_eq_mr_node,
              `hasFrameDeallocProtectorConflict_iff, `hasProtectedLocalBorrow_iff,
              `evalTerminator_return_protector_ub, `evalTerminator_callee_return_releases_protector,
              `evalTailCallTerminator_protector_ub, `evalTailCallTerminator_no_conflict_steps,
              `evalStmt_storageDead_protector_ub, `evalStmt_storageDead_no_conflict_steps,
              `evalStmt_storageLive_protector_ub,
              `trustedTeardown_table, `trusted_protector_cases_match_mr,
              `trustedStorageDead_and_release_table, `trusted_protector_twins_table,
              `trustedTailCallRun_table,
              `evalCastPtrToPtr_slice_to_thin, `evalCastPtrToPtr_dyn_to_thin,
              `evalCastPtrToPtr_scalarPair_to_thin, `evalCastPtrToPtr_scalarDyn_to_thin,
              `evalRvalue_thinPtr_eq, `evalRvalue_thinScalar_eq,
              `evalRvalue_wideSlice_eq, `evalRvalue_wideDyn_eq,
              `evalRvalue_wideSlice_eq_matches_mr, `evalRvalue_wideDyn_eq_matches_mr,
              `evalCast_then_thinEq_erases_meta_and_prov,
              `trustedCmp_table, `trustedCmp_nonvacuity_twins_table,
              `trustedRvalue_witnesses, `trusted_wide_cases_match_mr,
              `trusted_protector_is_treeBorrows_mode] do
      let src := dsNs ++ w
      let some (.thmInfo v) := (← getEnv).find? src
        | throwError "cross-root: root witness {src} missing"
      let outName := ns ++ `root ++ w
      addThm outName v.type (mkConst src)
      added := added.push outName

    -- 6. Negative controls on scratch copies: every boolean forgery is FIRST verified to
    -- kernel-reduce to `Bool.false` (`addDecl` ACCEPTS `= false` via `Eq.refl false`), and
    -- THEN verified to be REJECTED when claiming `= true` — proving each rejection is a
    -- genuine value mismatch (`false ≠ true`), never a type error or stuck reduction.
    let saved ← getEnv
    let accepts (d : Declaration) : CoreM Bool := do
      let r ← try addDecl d; pure true catch _ => pure false
      setEnv saved
      return r
    let rejects (d : Declaration) : CoreM Bool := do
      let r ← try addDecl d; pure false catch _ => pure true
      setEnv saved
      return r
    let lmObsU := mkConst (lmNs ++ `lmHeapWideObserveU)
    let lmLcU := mkConst (lmNs ++ `lmHeapLifecycleTraceU)
    let lmPtU := mkConst (lmNs ++ `lmProtectorDeallocTraceU)
    let authCheckExpr (o : Expr) : Expr := mkApp (mkConst (dsNs ++ `lmAuthorityCheck)) o
    let modeInv ← MetaM.run' <| mkObs trC lmObsU true false
    let caseShift ← MetaM.run' <| mkObs trC lmObsU false true
    let boolInv ← MetaM.run' <| mkObs (← MetaM.run' <| mkTranslate true false false false) lmObsU
    let ubForged ← MetaM.run' <| mkObs (← MetaM.run' <| mkTranslate false true false false) lmObsU
    let leakForged ← MetaM.run' <| mkObs (← MetaM.run' <| mkTranslate false false true false) lmObsU
    let invForged ← MetaM.run' <| mkObs (← MetaM.run' <| mkTranslate false false false true) lmObsU
    let ptModeInv ← MetaM.run' <| mkTrace trC lmPtU true
    let lcU ← MetaM.run' <| mkTrace trC lmLcU
    -- MiniRust passed off as LeanMiri: must reduce to `false` on the divergence set `{28, 29}`.
    let mrAsLm ← MetaM.run' <| withLocalDeclD `tb boolTy fun tb => withLocalDeclD `idx natTy fun idx =>
      mkLambdaFVars #[tb, idx] (mkApp2 (mkConst (dsNs ++ `mrObserve))
        (mkApp (mkConst (dsNs ++ `HeapWideMemoryMode.ofLmTreeBorrows)) tb) idx)
    let thm (n : String) (ty pf : Expr) : Declaration :=
      .thmDecl { name := ns ++ `forged ++ Lean.Name.mkSimple n, levelParams := [], type := ty, value := pf }
    -- 6a. Two-sided boolean negative controls (kernel MUST accept `= false` AND reject `= true`).
    let boolForgeries : List (String × String × Expr) :=
      [ ("mode-inverted observer (Bool.not tb) catching cases 19/21", "modeInverted", authCheckExpr modeInv),
        ("case-shifted observer (idx + 1)", "caseShifted", authCheckExpr caseShift),
        ("okBool-inverted translator", "boolInverted", authCheckExpr boolInv),
        ("ub-to-okDealloc forged translator", "ubForged", authCheckExpr ubForged),
        ("memoryLeak-to-okDealloc forged translator", "leakForged", authCheckExpr leakForged),
        ("invalidOrUnsupported-to-specPanic forged translator masking case 28",
          "invalidForged", authCheckExpr invForged),
        ("wire tuples forged equal on diverging cell (basic, 28)",
          "wire28Basic", wireExpr (mkConst crossObsU) modeBasic 28),
        ("wire tuples forged equal on diverging cell (treeBorrows, 28)",
          "wire28Tb", wireExpr (mkConst crossObsU) modeTb 28),
        ("wire tuples forged equal on diverging cell (basic, 29)",
          "wire29Basic", wireExpr (mkConst crossObsU) modeBasic 29),
        ("wire tuples forged equal on diverging cell (treeBorrows, 29)",
          "wire29Tb", wireExpr (mkConst crossObsU) modeTb 29),
        ("mode-inverted protector trace (Bool.not tb)",
          "protectorModeInverted", mkApp (mkConst (dsNs ++ `lmProtectorTraceAuthorityCheck)) ptModeInv),
        ("protector trace passed to the lifecycle check",
          "protectorAsLifecycle", mkApp (mkConst (dsNs ++ `lmLifecycleTraceAuthorityCheck)) (mkConst ptObsU)),
        ("lifecycle trace passed to the protector check",
          "lifecycleAsProtector", mkApp (mkConst (dsNs ++ `lmProtectorTraceAuthorityCheck)) lcU),
        ("MiniRust observer passed off as LeanMiri (diverges on 28, 29)",
          "mrAsLm", authCheckExpr mrAsLm) ]
    let mut rejected : Nat := 0
    for (what, tag, expr) in boolForgeries do
      unless ← accepts (thm (tag ++ "IsFalse") (eqFalse expr) reflFalse) do
        throwError "cross-root negative control VACUOUS: {what} did not kernel-reduce to Bool.false"
      unless ← rejects (thm tag (eqTrue expr) reflTrue) do
        throwError "cross-root negative control FAILED: kernel accepted {what}"
      rejected := rejected + 1
    -- 6b. Non-boolean / flipped-polarity / Trusted / codec forgeries (each paired with a true baseline).
    let tdFrozenTrue := mkApp2 (mkConst (dsNs ++ `trustedTeardownObs))
      (mkConst `Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowPerm.frozen) boolTrue
    let sliceCmpFalse := mkAppN (mkConst (dsNs ++ `trustedCmpObs))
      #[mkConst (dsNs ++ `hwSliceTy), mkConst (dsNs ++ `hwSliceTy), boolFalse,
        mkApp2 (mkConst (dsNs ++ `hwSlice)) (mkConst (dsNs ++ `hwPtrA)) (mkNatLit 3),
        mkApp2 (mkConst (dsNs ++ `hwSlice)) (mkConst (dsNs ++ `hwPtrA)) (mkNatLit 7)]
    let badTuple := mkApp4 (mkConst ``Prod.mk [0, 0]) natTy
      (mkApp2 (mkConst ``Prod [0, 0]) natTy (mkApp2 (mkConst ``Prod [0, 0]) natTy boolTy))
      (mkNatLit 8)
      (mkApp4 (mkConst ``Prod.mk [0, 0]) natTy (mkApp2 (mkConst ``Prod [0, 0]) natTy boolTy)
        (mkNatLit 0) (mkApp4 (mkConst ``Prod.mk [0, 0]) natTy boolTy (mkNatLit 0) boolFalse))
    let badDecode := mkApp (mkConst (dsNs ++ `heapWideDecode)) badTuple
    let optObsTy := mkApp (mkConst ``Option [0]) obsTy
    let extraForged : List (String × Option Declaration × Declaration) :=
      [ ("ill-typed 0 = 1 theorem", none,
          thm "zeroEqOne" (mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 0) (mkNatLit 1))
            (mkApp2 (mkConst ``Eq.refl [1]) natTy (mkNatLit 0))),
        ("negated lmAuthorityCheck certificate (= false)", none,
          thm "lmCheckFalse" (eqFalse (authCheckExpr (mkConst crossObsU))) reflFalse),
        ("negated lifecycle trace certificate (= false)", none,
          thm "lifecycleFalse"
            (eqFalse (mkApp (mkConst (dsNs ++ `lmLifecycleTraceAuthorityCheck)) (mkConst lcObsU))) reflFalse),
        ("forged Trusted active strong-protector teardown = okDealloc",
          some (thm "tdFrozenIsUb" (mkApp3 (mkConst ``Eq [1]) obsTy tdFrozenTrue (obsC "ub"))
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy (obsC "ub"))),
          thm "tdFrozenForgedOk" (mkApp3 (mkConst ``Eq [1]) obsTy tdFrozenTrue (obsC "okDealloc"))
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy (obsC "okDealloc"))),
        ("forged Trusted full wide slice == ignores length (okBool true)",
          some (thm "sliceCmpIsFalse" (mkApp3 (mkConst ``Eq [1]) obsTy sliceCmpFalse (mkApp (obsC "okBool") boolFalse))
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy (mkApp (obsC "okBool") boolFalse))),
          thm "sliceCmpForgedTrue" (mkApp3 (mkConst ``Eq [1]) obsTy sliceCmpFalse (mkApp (obsC "okBool") boolTrue))
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy (mkApp (obsC "okBool") boolTrue))),
        ("forged 3-way: Trusted active-protector verdict equals LeanMiri BASIC-mode case 19",
          some (thm "trustedEqLmTb19"
            (mkApp3 (mkConst ``Eq [1]) obsTy tdFrozenTrue (mkApp2 (mkConst crossObsU) boolTrue (mkNatLit 19)))
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy tdFrozenTrue)),
          thm "trustedEqLmBasic19"
            (mkApp3 (mkConst ``Eq [1]) obsTy tdFrozenTrue (mkApp2 (mkConst crossObsU) boolFalse (mkNatLit 19)))
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy tdFrozenTrue)),
        ("forged out-of-range LeanMiri cell (false, 30) = ub",
          some (thm "outOfRangeIsInvalid"
            (mkApp3 (mkConst ``Eq [1]) obsTy (mkApp2 (mkConst crossObsU) boolFalse (mkNatLit 30))
              (obsC "invalidOrUnsupported"))
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy (obsC "invalidOrUnsupported"))),
          thm "outOfRangeForgedUb"
            (mkApp3 (mkConst ``Eq [1]) obsTy (mkApp2 (mkConst crossObsU) boolFalse (mkNatLit 30))
              (obsC "ub"))
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy (obsC "ub"))),
        ("forged callee-return that keeps protector 1 still deallocates (okDealloc)",
          some (thm "calleeKeepIsUb"
            (mkApp3 (mkConst ``Eq [1]) obsTy (mkConst (dsNs ++ `trustedCalleeKeepThenDeallocObs)) (obsC "ub"))
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy (obsC "ub"))),
          thm "calleeKeepForgedOk"
            (mkApp3 (mkConst ``Eq [1]) obsTy (mkConst (dsNs ++ `trustedCalleeKeepThenDeallocObs))
              (obsC "okDealloc"))
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy (obsC "okDealloc"))),
        ("forged malformed codec tuple decodes to some .ub",
          some (thm "badDecodeIsNone" (mkApp3 (mkConst ``Eq [1]) optObsTy badDecode (mkApp (mkConst ``Option.none [0]) obsTy))
            (mkApp2 (mkConst ``Eq.refl [1]) optObsTy (mkApp (mkConst ``Option.none [0]) obsTy))),
          thm "badDecodeForgedUb" (mkApp3 (mkConst ``Eq [1]) optObsTy badDecode (mkApp2 (mkConst ``Option.some [0]) obsTy (obsC "ub")))
            (mkApp2 (mkConst ``Eq.refl [1]) optObsTy (mkApp2 (mkConst ``Option.some [0]) obsTy (obsC "ub")))),
        ("forged released tail-call run still faults (.ub instead of .okDealloc)",
          some (thm "tailCallRunRelIsOk"
            (mkApp3 (mkConst ``Eq [1]) obsTy
              (mkApp2 (mkConst (dsNs ++ `trustedTailCallRunObs))
                (mkConst `Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowPerm.frozen) boolFalse)
              (obsC "okDealloc"))
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy (obsC "okDealloc"))),
          thm "tailCallRunRelForgedUb"
            (mkApp3 (mkConst ``Eq [1]) obsTy
              (mkApp2 (mkConst (dsNs ++ `trustedTailCallRunObs))
                (mkConst `Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowPerm.frozen) boolFalse)
              (obsC "ub"))
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy (obsC "ub"))),
        ("forged Trusted addr_eq ignores distinct addresses (hwPtrA vs hwPtrC = true)",
          some (thm "addrEqDiffIsFalse"
            (mkApp3 (mkConst ``Eq [1]) obsTy
              (mkAppN (mkConst (dsNs ++ `trustedCmpObs))
                #[mkConst (dsNs ++ `hwSliceTy), mkConst (dsNs ++ `hwSliceTy), boolTrue,
                  mkApp2 (mkConst (dsNs ++ `hwSlice)) (mkConst (dsNs ++ `hwPtrA)) (mkNatLit 3),
                  mkApp2 (mkConst (dsNs ++ `hwSlice)) (mkConst (dsNs ++ `hwPtrC)) (mkNatLit 3)])
              (mkApp (obsC "okBool") boolFalse))
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy (mkApp (obsC "okBool") boolFalse))),
          thm "addrEqDiffForgedTrue"
            (mkApp3 (mkConst ``Eq [1]) obsTy
              (mkAppN (mkConst (dsNs ++ `trustedCmpObs))
                #[mkConst (dsNs ++ `hwSliceTy), mkConst (dsNs ++ `hwSliceTy), boolTrue,
                  mkApp2 (mkConst (dsNs ++ `hwSlice)) (mkConst (dsNs ++ `hwPtrA)) (mkNatLit 3),
                  mkApp2 (mkConst (dsNs ++ `hwSlice)) (mkConst (dsNs ++ `hwPtrC)) (mkNatLit 3)])
              (mkApp (obsC "okBool") boolTrue))
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy (mkApp (obsC "okBool") boolTrue))),
        ("forged Trusted full wide slice == on identical ptr+len returns false",
          some (thm "wideEqSameIsTrue"
            (mkApp3 (mkConst ``Eq [1]) obsTy
              (mkAppN (mkConst (dsNs ++ `trustedCmpObs))
                #[mkConst (dsNs ++ `hwSliceTy), mkConst (dsNs ++ `hwSliceTy), boolFalse,
                  mkApp2 (mkConst (dsNs ++ `hwSlice)) (mkConst (dsNs ++ `hwPtrA)) (mkNatLit 3),
                  mkApp2 (mkConst (dsNs ++ `hwSlice)) (mkConst (dsNs ++ `hwPtrA)) (mkNatLit 3)])
              (mkApp (obsC "okBool") boolTrue))
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy (mkApp (obsC "okBool") boolTrue))),
          thm "wideEqSameForgedFalse"
            (mkApp3 (mkConst ``Eq [1]) obsTy
              (mkAppN (mkConst (dsNs ++ `trustedCmpObs))
                #[mkConst (dsNs ++ `hwSliceTy), mkConst (dsNs ++ `hwSliceTy), boolFalse,
                  mkApp2 (mkConst (dsNs ++ `hwSlice)) (mkConst (dsNs ++ `hwPtrA)) (mkNatLit 3),
                  mkApp2 (mkConst (dsNs ++ `hwSlice)) (mkConst (dsNs ++ `hwPtrA)) (mkNatLit 3)])
              (mkApp (obsC "okBool") boolFalse))
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy (mkApp (obsC "okBool") boolFalse))) ]
    for (what, baseOpt, d) in extraForged do
      if let some baseDecl := baseOpt then
        unless ← accepts baseDecl do
          throwError "cross-root negative control VACUOUS: baseline for {what} failed to kernel-reduce"
      unless ← rejects d do
        throwError "cross-root negative control FAILED: kernel accepted {what}"
      rejected := rejected + 1

    -- 7. Safety, non-triviality, choice-free codec check, standard-3-axiom purity, self-tests, reachability.
    let env ← getEnv
    let isStdAx (a : Lean.Name) : Bool :=
      a == ``propext || a == ``Classical.choice || a == ``Quot.sound
    -- Constructive codec layer in DualSpec must be strictly choice-free (`[propext, Quot.sound]`).
    for c in [dsNs ++ `heapWideOutcomeCodec, dsNs ++ `heapWideOutcomeCodec_tight,
              dsNs ++ `heapWideOutcomeCodec_encode_injective,
              dsNs ++ `heapWideOutcomeCodec_decode_injective_on_valid,
              dsNs ++ `heapWideDecode_canonical, dsNs ++ `lmAuthorityCheck_sound] do
      for a in ← collectAxioms c do
        unless a == ``propext || a == ``Quot.sound do
          throwError "cross-root constructive audit: {c} must not depend on {a}"
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
        dsNs ++ `hasFrameDeallocProtectorConflict_eq_mr_node,
        dsNs ++ `hasProtectedLocalBorrow_eq_mr_node,
        dsNs ++ `evalRvalue_wideSlice_eq, dsNs ++ `evalRvalue_wideDyn_eq,
        dsNs ++ `evalCast_then_thinEq_erases_meta_and_prov,
        dsNs ++ `trustedTeardown_table, dsNs ++ `trustedStorageDead_and_release_table,
        dsNs ++ `trustedCmp_table ]
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
      [ outName, lmNs ++ `lmHeapWideObserve_out_of_range,
        contractName, crossObs, crossCheck, lcCheck, ptCheck,
        dsNs ++ `ep2_heap_alloc_and_wide_ptr_dual_authority_capstone,
        lmNs ++ `lmHeapWideObserve, lmNs ++ `lmHeapWideObserveU,
        lmNs ++ `lmHeapLifecycleTrace, lmNs ++ `lmProtectorDeallocTrace,
        `MiniRustSpec.HeapAllocAndWidePtrMR.mrHeapWideObserve,
        `MiniRustSpec.HeapAllocAndWidePtrMR.ep1_minirust_heap_wide_capstone,
        `MiniRustSpec.Interp.evalIntrinsic, `MiniRustSpec.Interp.evalIntrinsicM,
        `MiniRustSpec.Interp.BasicMemory.leak_check, `MiniRustSpec.Interp.TreeBorrowsMemory.deallocate,
        `MiniRustSpec.Interp.Node.contains_strong_protector_preventing_deallocation,
        `MiniRustSpec.Interp.comparePtr,
        `Miri.ABI.Align.fromBytes,
        `Miri.Memory.MemoryLifecycle.allocatePtr, `Miri.Memory.MemoryLifecycle.deallocatePtrWith,
        `Miri.TreeBorrows.BorrowTree.deallocateBorrowRange, `Miri.Interpreter.LeakCheck.take,
        `Miri.Interpreter.Cast.ptrToPtr, `Miri.Interpreter.ExecutionScalar.pointerBinary,
        `Trusted.Rustc.V2026_06_01.MirSemantics.hasFrameDeallocProtectorConflict,
        `Trusted.Rustc.V2026_06_01.MirSemantics.hasProtectedLocalBorrow,
        `Trusted.Rustc.V2026_06_01.MirSemantics.preventsDeallocation,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalTerminator,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalTailCallTerminator,
        `Trusted.Rustc.V2026_06_01.MirSemantics.enterTailCalleeFrame,
        `Trusted.Rustc.V2026_06_01.MirSemantics.restoreCallerProtectors,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalCastPtrToPtr,
        `Trusted.Rustc.V2026_06_01.MirSemantics.ptrToAddrScalar,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalWidePtrAggregateRelBinOp,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalWidePtrRelBinOp,
        `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn ]
    for req in requiredReach do
      unless reach.contains req do
        throwError "cross-root reachability failure: closed capstone does not reach {req}"
    return (added.size, rejected, crAxioms.toArray)

  let ctx : Core.Context :=
    { fileName := "<heap-wide-cross-root>", fileMap := default, options := opts, maxHeartbeats := 0 }
  let ((addedCount, rejectedCount, crAxioms), _) ← liftCoreM <| act.toIO ctx { env := baseEnv }
  unless addedCount = 84 && rejectedCount = 26 do
    throwError "cross-root: unexpected counts (added={addedCount}, rejected={rejectedCount})"
  logInfo m!"heap/wide cross-root kernel bridge: added {addedCount} declarations, rejected {rejectedCount} forged controls (all boolean/value forgeries verified two-sided), reached MiniRust+Miri+Trusted, axioms {crAxioms}"

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
