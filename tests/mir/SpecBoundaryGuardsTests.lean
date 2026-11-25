-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.SpecBoundaryGuards

/-!
# Tests for `Anneal.SpecBoundaryGuards`

1. **Wire-ID parity** (§1): the 12 `PropertyClassTag` identifiers, variant names,
   ranks, and waivability flags, and the 3 `SpecBoundaryGuardClass` identifiers,
   diagnostic names, and vacuity classes, pinned as literal tables. The same tables
   are asserted by `cargo_anneal::property_registry` and `anneal_spec::spec_check`.
2. **Guard 1** (§2): entry-point classification vectors, the `verus#3606` collapse on
   `main` / `_start` / `__start`, a second concrete `MirSemantics` fixture built
   only from the module's public step lemmas, and fail-closed negatives.
3. **Guard 2** (§3): the `2 ^ 64` wraparound, both `False` derivations at concrete
   widths, the type-name verdict table, and the unbounded models.
4. **Guard 3** (§4): concrete surviving and killed mutants, the `Except` variant,
   and `MirSemantics` counterexamples.
5. **Kernel audit** (§5): a compile-time `run_cmd` over every constant of
   `Anneal.SpecBoundaryGuards` and of this file.
-/

namespace Anneal.SpecBoundaryGuardsTests

open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.SpecRealizability
open Anneal.SpecBoundaryGuards

/-! ## 1. Cross-Language Wire-ID Parity -/

/-- The 12 wire identifiers in rank order (`PropertyClass::as_str`). -/
theorem propertyClass_wire_ids :
    PropertyClassTag.all.map PropertyClassTag.asStr =
      ["arithmetic_overflow", "shift_bounds", "div_rem_ub", "pointer_deref",
        "slice_array_bounds", "discriminant_validity", "call_contract", "loop_termination",
        "switch_exhaustiveness", "memory_copy_overlap", "uninit_read",
        "unsupported_fallback"] :=
  rfl

/-- The 12 Rust variant names in rank order. -/
theorem propertyClass_variant_names :
    PropertyClassTag.all.map PropertyClassTag.variantName =
      ["ArithmeticOverflow", "ShiftBounds", "DivRemUb", "PointerDereference",
        "SliceArrayBounds", "DiscriminantValidity", "CallContract", "LoopTermination",
        "SwitchExhaustiveness", "MemoryCopyOverlap", "UninitRead", "UnsupportedFallback"] :=
  rfl

/-- Ranks are `0..11` in order. -/
theorem propertyClass_ranks :
    PropertyClassTag.all.map PropertyClassTag.rank = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] :=
  rfl

/-- Classes `0..10` are waivable and class `11` is not. -/
theorem propertyClass_waivability :
    PropertyClassTag.all.map PropertyClassTag.isWaivable =
      [true, true, true, true, true, true, true, true, true, true, true, false] :=
  rfl

/-- Every wire identifier and every rank round-trips. -/
theorem propertyClass_roundtrips :
    PropertyClassTag.all.all (fun c =>
      PropertyClassTag.ofStr? c.asStr == some c &&
        PropertyClassTag.ofRank? c.rank == some c &&
        PropertyClassTag.ofVariantName? c.variantName == some c) = true := by
  decide

/-- Parsing is exact: near-miss identifiers are rejected (fail-closed). -/
theorem propertyClass_rejects_near_misses :
    ["", "Arithmetic_Overflow", "arithmetic_overflow ", " arithmetic_overflow",
      "arithmetic-overflow", "ArithmeticOverflow", "pointer_dereference", "div_rem",
      "unsupported", "entry_point_requires"].all
        (fun s => (PropertyClassTag.ofStr? s).isNone) = true := by
  decide

/-- Out-of-range ranks are rejected. -/
theorem propertyClass_rejects_out_of_range_ranks :
    [12, 13, 255, 4294967296].all (fun n => (PropertyClassTag.ofRank? n).isNone) = true := by
  decide

/-- The frozen `(guard_id, canonical_name, vacuity_class)` table. -/
theorem guard_wire_table :
    SpecBoundaryGuardClass.all.map
        (fun g => (g.rank, g.guardId, g.canonicalName, g.toVacuityClass.canonicalName)) =
      [(0, "entry_point_requires", "EntryPointPrecondition", "DeadPrecondition"),
        (1, "fixed_width_ghost_length", "FixedWidthGhostLength", "SpecViolation"),
        (2, "error_branch_wildcard", "ErrorBranchWildcard", "SurvivedAllMutants")] :=
  rfl

/-- Every guard identifier, diagnostic name, and rank round-trips. -/
theorem guard_roundtrips :
    SpecBoundaryGuardClass.all.all (fun g =>
      SpecBoundaryGuardClass.ofGuardId? g.guardId == some g &&
        SpecBoundaryGuardClass.ofCanonicalName? g.canonicalName == some g &&
        SpecBoundaryGuardClass.ofRank? g.rank == some g) = true := by
  decide

/-- Guard parsing is exact and does not confuse the two wire namespaces. -/
theorem guard_rejects_near_misses :
    ["", "EntryPointPrecondition", "entry_point_precondition", "entry_point_requires ",
      "Entry_Point_Requires", "fixed_width_ghost_len", "error_branch_wildcards",
      "arithmetic_overflow"].all
        (fun s => (SpecBoundaryGuardClass.ofGuardId? s).isNone) = true ∧
    ["", "entry_point_requires", "entryPointPrecondition", "EntryPointRequires",
      "DeadPrecondition", "FixedWidthGhostLength ", "ErrorBranchWildCard"].all
        (fun s => (SpecBoundaryGuardClass.ofCanonicalName? s).isNone) = true := by
  decide

/-- The guard vacuity classes are members of the frozen 5-class taxonomy and the
    3 guards map onto 3 distinct classes. -/
theorem guard_vacuity_classes :
    SpecBoundaryGuardClass.all.map SpecBoundaryGuardClass.toVacuityClass =
      [VacuityClass.deadPrecondition, VacuityClass.specViolation,
        VacuityClass.survivedAllMutants] :=
  rfl

/-- The two taxonomies are disjoint on the wire: no guard identifier is a property
    class identifier. -/
theorem guard_ids_disjoint_from_property_classes :
    SpecBoundaryGuardClass.all.all
        (fun g => (PropertyClassTag.ofStr? g.guardId).isNone) = true ∧
    PropertyClassTag.all.all
        (fun c => (SpecBoundaryGuardClass.ofGuardId? c.asStr).isNone) = true := by
  decide

/-- `EntryPointKind` wire identifiers (`EntryPointKind::as_str`). -/
theorem entryPointKind_wire_ids :
    [EntryPointKind.rustMain, .noMainStart, .customEntryAttr].map EntryPointKind.asStr =
      ["main", "no_main_start", "entry_attribute"] :=
  rfl

/-! ## 2. Guard 1 — Entry-Point `requires` Ban -/

/-! ### 2.1 Classification Vectors -/

/-- Path segmentation splits exactly at `::`. -/
theorem pathSegments_vectors :
    pathSegments "main" = ["main"] ∧
    pathSegments "my_crate::main" = ["my_crate", "main"] ∧
    pathSegments "a::b::c" = ["a", "b", "c"] ∧
    pathSegments "" = [""] ∧
    pathSegments "::main" = ["", "main"] ∧
    pathSegments "a:b" = ["a:b"] ∧
    pathSegments "a:::b" = ["a", ":b"] := by
  decide

/-- Binary entry symbols accepted by the name-only test. -/
theorem entrySymbol_accepts :
    ["main", "::main", "my_crate::main", "::my_crate::main", "_start", "::_start",
      "my_crate::_start", "::my_crate::_start", "__start", "::__start",
      "my_crate::__start", "::my_crate::__start", "crate::main"].all
        isBinaryEntrySymbol = true := by
  decide

/-- Substring, impl/trait, malformed-crate, and nesting false positives rejected
    by the name-only test. -/
theorem entrySymbol_rejects :
    ["", "domain", "maintain", "main_loop", "mainx", "xmain", "Main", "MAIN", "start",
      "_start_", "___start", "my_crate::domain", "my_crate::maintain", "my_crate::main_loop",
      "my_crate::Type::main", "my_crate::module::_start", "my_crate::main::helper", "main::",
      "my_crate::main ", "my_crate:main", "<MyType as Trait>::main", "<impl Foo>::main",
      "{{impl}}::main", ":::main", "::::main", "my_crate::::main", "123::main",
      "my crate::main", " ::main"].all (fun s => !isBinaryEntrySymbol s) = true := by
  decide

/-- Cross-language entry-point classification vectors
    (`anneal_spec::spec_check::classify_entry_point` asserts the same table). -/
def entryClassificationVectors : List (EntryPointDescriptor × Option EntryPointKind) :=
  [ ({ defPath := "main" }, some .rustMain),
    ({ defPath := "::main" }, some .rustMain),
    ({ defPath := "my_crate::main" }, some .rustMain),
    ({ defPath := "::my_crate::main" }, some .rustMain),
    ({ defPath := "my_crate::main", crateNoMain := true }, some .noMainStart),
    ({ defPath := "_start", crateNoMain := true }, some .noMainStart),
    ({ defPath := "::_start", crateNoMain := true }, some .noMainStart),
    ({ defPath := "my_crate::_start", crateNoMain := true }, some .noMainStart),
    ({ defPath := "::my_crate::_start", crateNoMain := true }, some .noMainStart),
    ({ defPath := "my_crate::__start", crateNoMain := true }, some .noMainStart),
    ({ defPath := "my_crate::_start" }, none),
    ({ defPath := "my_crate::__start" }, none),
    ({ defPath := "my_crate::boot", linkSymbol := some "_start" }, some .noMainStart),
    ({ defPath := "my_crate::arch::boot", linkSymbol := some "__start" }, some .noMainStart),
    ({ defPath := "my_crate::arch::c_main", linkSymbol := some "main" }, some .noMainStart),
    ({ defPath := "my_crate::helper", linkSymbol := some "helper" }, none),
    ({ defPath := "my_crate::helper", linkSymbol := some "main_loop" }, none),
    ({ defPath := "my_crate::reset", hasEntryAttr := true }, some .customEntryAttr),
    ({ defPath := "my_crate::main", hasEntryAttr := true }, some .customEntryAttr),
    ({ defPath := "my_crate::Type::main", isAssocFn := true }, none),
    ({ defPath := "Type::main", isAssocFn := true }, none),
    ({ defPath := "my_crate::Type::run", isAssocFn := true, hasEntryAttr := true }, none),
    ({ defPath := "my_crate::Boot::_start", isAssocFn := true, linkSymbol := some "_start" },
      some .noMainStart),
    ({ defPath := "my_crate::Server::main", isAssocFn := true, hasEntryAttr := true,
       linkSymbol := some "main" }, some .noMainStart),
    ({ defPath := "my_crate::Boot::run", isAssocFn := true, linkSymbol := some "run" }, none),
    ({ defPath := "my_crate::Boot::main", isAssocFn := true, linkSymbol := some "boot_main" },
      none),
    ({ defPath := "my_crate::Type::main" }, none),
    ({ defPath := "<MyType as Trait>::main" }, none),
    ({ defPath := "<impl Foo>::main" }, none),
    ({ defPath := "{{impl}}::main" }, none),
    ({ defPath := ":::main" }, none),
    ({ defPath := "::::main" }, none),
    ({ defPath := "123::main" }, none),
    ({ defPath := "my_crate::module::main" }, none),
    ({ defPath := "my_crate::domain" }, none),
    ({ defPath := "my_crate::maintain" }, none),
    ({ defPath := "my_crate::main_loop" }, none),
    ({ defPath := "my_crate::main_loop", crateNoMain := true }, none) ]

theorem entryClassificationVectors_hold :
    entryClassificationVectors.all (fun v => classifyEntryPoint v.1 == v.2) = true := by
  decide

/-- `classifyEntryPath` never accepts a path the name-only test rejects. -/
theorem classifyEntryPath_sound_on_vectors :
    entryClassificationVectors.all (fun v =>
      (classifyEntryPath v.1.defPath v.1.crateNoMain).isNone ||
        isBinaryEntrySymbol v.1.defPath) = true := by
  decide

/-- The linker does not see Rust namespaces: an associated function exported as
    `_start` is the entry symbol of the binary, whatever its path. -/
theorem exported_assocFn_start_is_entry :
    classifyEntryPoint
        { defPath := "fw::Boot::reset", isAssocFn := true, linkSymbol := some "_start" } =
      some .noMainStart :=
  classifyEntryPoint_assocFn_exported rfl rfl (by decide)

/-- Every descriptor exported under `main` is an entry point: no combination of
    the other facts hides it. -/
theorem exported_main_is_always_entry (defPath : String) (noMain attr assoc : Bool) :
    (classifyEntryPoint
        { defPath := defPath, crateNoMain := noMain, hasEntryAttr := attr,
          linkSymbol := some "main", isAssocFn := assoc }).isSome = true :=
  classifyEntryPoint_isSome_of_exported_entry_symbol rfl (by decide)

/-- Fail-closed negative: an unexported method named `main` is not an entry point,
    and neither is one exported under an ordinary symbol. -/
theorem unexported_method_main_is_not_entry :
    classifyEntryPoint { defPath := "app::Server::main", isAssocFn := true } = none ∧
      classifyEntryPoint
          { defPath := "app::Server::main", isAssocFn := true, hasEntryAttr := true,
            linkSymbol := some "server_main" } = none :=
  ⟨classifyEntryPoint_assocFn rfl rfl,
    classifyEntryPoint_assocFn_of_non_entry_symbol rfl rfl (by decide)⟩

/-- Enabling `#![no_main]` preserves every existing entry point on the classification
    vectors. -/
theorem entry_classification_monotone_in_no_main (d : EntryPointDescriptor)
    (h : (classifyEntryPoint { d with crateNoMain := false }).isSome = true) :
    (classifyEntryPoint { d with crateNoMain := true }).isSome = true :=
  classifyEntryPoint_mono_crateNoMain h

/-! ### 2.2 The Collapse on `main`, `_start`, and `__start` -/

open EntryDemo in
/-- The collapse holds for every accepted entry symbol spelling. -/
theorem collapse_on_every_entry_spelling :
    EntryRequiresSoundnessCollapse u8EntryAbi (divEntryClaim "main") ∧
    EntryRequiresSoundnessCollapse u8EntryAbi (divEntryClaim "my_crate::main") ∧
    EntryRequiresSoundnessCollapse u8EntryAbi (divEntryClaim "_start") ∧
    EntryRequiresSoundnessCollapse u8EntryAbi (divEntryClaim "my_crate::__start") :=
  ⟨divEntryClaim_collapse _ (by decide), divEntryClaim_collapse _ (by decide),
    divEntryClaim_collapse _ (by decide), divEntryClaim_collapse _ (by decide)⟩

open EntryDemo in
/-- The collapse really is a counterexample to closed-program safety and to the
    guard, on `main` and on `_start`. -/
theorem collapse_refutes_safety_and_guard :
    ¬ ClaimClosedProgramSafe u8EntryAbi (divEntryClaim "entry_demo::main") ∧
    ¬ ClaimEntryRequiresGuard u8EntryAbi (divEntryClaim "entry_demo::main") ∧
    ¬ ClaimClosedProgramSafe u8EntryAbi (divEntryClaim "_start") ∧
    ¬ ClaimEntryRequiresGuard u8EntryAbi (divEntryClaim "_start") :=
  ⟨main_requires_collapse.not_closedProgramSafe, main_requires_collapse.not_guard,
    start_requires_collapse.not_closedProgramSafe, start_requires_collapse.not_guard⟩

open EntryDemo in
/-- All three specification gates pass on the collapsing claim: the collapse is
    invisible to `DeadPrecondition`, `PostconditionDichotomy`, and the kernel. -/
theorem collapse_passes_every_spec_gate :
    NonVacuousPre (divEntryClaim "entry_demo::main").pre ∧
    ClaimDichotomy (divEntryClaim "entry_demo::main") ∧
    VerificationResult (divEntryClaim "entry_demo::main") ∧
    PreconditionSatisfiable (divEntryClaim "entry_demo::main").pre :=
  ⟨main_requires_collapse.nonVacuous, main_requires_collapse.dichotomy,
    main_requires_collapse.verified, main_requires_collapse.nonVacuous⟩

open EntryDemo in
/-- The stateful collapse on `_start`. -/
theorem stateful_collapse_refutes_safety :
    ¬ StatefulClaimClosedProgramSafe u8StatefulEntryAbi (divEntryStatefulClaim "_start") ∧
    ¬ StatefulClaimEntryRequiresGuard u8StatefulEntryAbi (divEntryStatefulClaim "_start") :=
  ⟨start_requires_stateful_collapse.not_closedProgramSafe,
    start_requires_stateful_collapse.not_guard⟩

open EntryDemo in
/-- Even a kernel-verified `TotalVerificationResult` on `main` or `_start` collapses
    when its `requires` is non-universal. -/
theorem total_collapse_refutes_total_and_guard :
    ¬ TotalClaimClosedProgramTotal u8StatefulEntryAbi (divEntryTotalClaim "entry_demo::main") ∧
    ¬ TotalClaimEntryRequiresGuard u8StatefulEntryAbi (divEntryTotalClaim "entry_demo::main") ∧
    ¬ TotalClaimClosedProgramTotal u8StatefulEntryAbi (divEntryTotalClaim "_start") ∧
    ¬ TotalClaimEntryRequiresGuard u8StatefulEntryAbi (divEntryTotalClaim "_start") :=
  ⟨main_requires_total_collapse.not_closedProgramTotal, main_requires_total_collapse.not_guard,
    start_requires_total_collapse.not_closedProgramTotal, start_requires_total_collapse.not_guard⟩

open EntryDemo in
/-- The collapsing `TotalClaim` passes every standard realizability and verification gate. -/
theorem total_collapse_passes_every_spec_gate :
    NonVacuousStatefulPre (divEntryTotalClaim "entry_demo::main").pre ∧
    TotalClaimDichotomy (divEntryTotalClaim "entry_demo::main") ∧
    TotalVerificationResult (divEntryTotalClaim "entry_demo::main") :=
  ⟨main_requires_total_collapse.nonVacuous, main_requires_total_collapse.dichotomy,
    main_requires_total_collapse.verified⟩

open EntryDemo in
/-- **Positive.** The guarded echo entry point is safe on `argc == 0`, the very
    input on which the division entry point has undefined behavior. -/
theorem echoEntry_safe_on_zero :
    TreeSafe (mirCallTreeWithCallees (echoEntryBody "entry_demo::main") (u8Arg 0) []) ∧
    ¬ TreeSafe (mirCallTreeWithCallees (divEntryBody "entry_demo::main") (u8Arg 0) []) :=
  ⟨echoEntry_closedProgramSafe "entry_demo::main" (u8Arg 0) ⟨0, by decide, rfl⟩,
    divEntry_not_treeSafe_on_zero "entry_demo::main"⟩

open EntryDemo in
/-- **Positive.** The guarded echo entry point returns its argument on every
    ABI-admissible start. -/
theorem echoEntry_closedProgramCorrect :
    ClaimClosedProgramCorrect u8EntryAbi (echoEntryClaim "entry_demo::main") :=
  claimClosedProgramCorrect_of_guard (echoEntry_guard _) (echoEntryClaim_verified _)

/-- **Fail-closed.** An explicit `requires` is accepted exactly when the ABI implies
    it: `argc < 256` is trivial on the `u8` ABI, `argc == 1` is not. -/
theorem explicit_requires_guard_examples :
    EntryPointRequiresGuard EntryDemo.u8EntryAbi
        (effectiveEntryPre true EntryDemo.u8EntryAbi
          (fun args => ∃ n, n < 256 ∧ args = EntryDemo.u8Arg n)) ∧
    ¬ EntryPointRequiresGuard EntryDemo.u8EntryAbi
        (effectiveEntryPre true EntryDemo.u8EntryAbi (fun args => args = EntryDemo.u8Arg 1)) := by
  refine ⟨(entryPointRequiresGuard_explicit_iff _ _).mpr fun _ h => h, ?_⟩
  intro hGuard
  have hAll := (entryPointRequiresGuard_explicit_iff _ _).mp hGuard
  have hZero : EntryDemo.u8Arg 0 = EntryDemo.u8Arg 1 :=
    hAll (EntryDemo.u8Arg 0) ⟨0, by decide, rfl⟩
  cases hZero

/-! ### 2.3 A Second `MirSemantics` Fixture: `7 % argc` -/

/-- `fn <entry>(argc: u8) -> u8 { 7 % argc }` in runtime MIR:
    `bb0: _0 = Rem(const 7_u8, copy _1); return`. -/
def remEntryBody (defPath : DefPath) : CapturedMir :=
  EntryDemo.singleAssignBody defPath
    (.binaryOp .rem (EntryDemo.u8Const 7) (.copy (EntryDemo.localPlace 1)))

/-- The claim `{argc == 2} <entry> {ret == 1}`. -/
def remEntryClaim (defPath : DefPath) : Claim where
  body := remEntryBody defPath
  pre := fun args => args = EntryDemo.u8Arg 2
  post := fun _ ret => ret = .scalar { bits := 1, sizeBytes := 1 }

theorem remEntry_step_zero (defPath : DefPath) :
    stepMirState (remEntryBody defPath)
        (.running (initMachineStateWithCallees (remEntryBody defPath) (EntryDemo.u8Arg 0) [])) =
      MirStepNode.fail .ub :=
  rfl

theorem remEntry_step_two (defPath : DefPath) :
    stepMirState (remEntryBody defPath)
        (.running (initMachineStateWithCallees (remEntryBody defPath) (EntryDemo.u8Arg 2) [])) =
      .tau (.running (EntryDemo.afterAssign 1 2)) :=
  rfl

theorem remEntry_step_return (defPath : DefPath) :
    stepMirState (remEntryBody defPath) (.running (EntryDemo.afterAssign 1 2)) =
      .ret (.normal (.scalar { bits := 1, sizeBytes := 1 }, {})) :=
  rfl

theorem remEntryClaim_verified (defPath : DefPath) :
    VerificationResult (remEntryClaim defPath) := by
  refine ⟨fun args hPre => ?_⟩
  have hArgs : args = EntryDemo.u8Arg 2 := hPre
  subst hArgs
  obtain ⟨hSafe, hRet⟩ :=
    mirTree_safe_of_step_tau_ret (remEntry_step_two defPath) (remEntry_step_return defPath)
  refine ⟨hSafe, ?_⟩
  intro out hReach _ retVal mem' hOut
  have hEq := hRet out.1 out.2 hReach
  rw [hEq] at hOut
  cases hOut
  rfl

/-- The collapse reproduces on an independent fixture using only the public API. -/
theorem remEntryClaim_collapse :
    EntryRequiresSoundnessCollapse EntryDemo.u8EntryAbi (remEntryClaim "fw::__start") where
  entrySymbol := by decide
  nonVacuous := ⟨EntryDemo.u8Arg 2, rfl⟩
  dichotomy :=
    ⟨EntryDemo.u8Arg 2, rfl, ⟨.scalar { bits := 1, sizeBytes := 1 }, rfl⟩,
      ⟨.unit, fun h => Value.noConfusion h⟩⟩
  verified := remEntryClaim_verified _
  escapes := by
    refine ⟨EntryDemo.u8Arg 0, ⟨0, by decide, rfl⟩, ?_,
      faultsWith_of_step_fail (remEntry_step_zero _)⟩
    intro hPre
    have hArgs : EntryDemo.u8Arg 0 = EntryDemo.u8Arg 2 := hPre
    cases hArgs

/-- **Fail-closed.** A non-entry symbol cannot be packaged as a collapse witness:
    the witness demands `isBinaryEntrySymbol`. -/
theorem no_collapse_witness_for_non_entry_symbol (admissible : List Value → Prop) :
    ¬ EntryRequiresSoundnessCollapse admissible (remEntryClaim "fw::helper") :=
  fun h => absurd h.entrySymbol (by decide)

/-- A faulting first step is observed as `FaultNow`, and never as `TreeSafe`. -/
theorem remEntry_faultNow_on_zero :
    FaultNow (mirCallTreeWithCallees (remEntryBody "fw::__start") (EntryDemo.u8Arg 0) []) :=
  (faultsWith_of_step_fail (remEntry_step_zero _)).faultNow

/-! ## 3. Guard 2 — Fixed-Width Ghost Length -/

/-- The guard verdict on widths. -/
theorem ghostLengthTypeGuard_verdicts :
    GhostLengthTypeGuard .unboundedNat ∧ GhostLengthTypeGuard .unboundedInt ∧
    ¬ GhostLengthTypeGuard (.fixedUnsigned 64) ∧ ¬ GhostLengthTypeGuard (.fixedSigned 64) ∧
    ¬ GhostLengthTypeGuard (.fixedUnsigned 8) ∧ ¬ GhostLengthTypeGuard (.fixedUnsigned 128) ∧
    ¬ GhostLengthTypeGuard (.fixedUnsigned 0) := by
  decide

/-- The type-name verdict table (`scan_ghost_length_width_diagnostics` flags exactly
    the `some false` names). -/
theorem ghostLengthTypeName_verdicts :
    ["Nat", "Int", "u64", "usize", "UInt64", "USize", "u8", "i64", "ISize", "u128",
      "String", "nat", "U64", "Usize", "BitVec", ""].map ghostLengthTypeNameVerdict? =
      [some true, some true, some false, some false, some false, some false, some false,
        some false, some false, some false, none, none, none, none, none, none] := by
  decide

/-- The flagged-name table has exactly the 22 spellings shared with the Rust scanner. -/
theorem fixedWidthGhostTypeNames_table :
    fixedWidthGhostTypeNames =
      ["UInt8", "UInt16", "UInt32", "UInt64", "USize", "Int8", "Int16", "Int32", "Int64",
        "ISize", "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128",
        "isize"] ∧
    fixedWidthGhostTypeNames.length = 22 ∧ unboundedGhostTypeNames = ["Nat", "Int"] :=
  ⟨rfl, rfl, rfl⟩

/-- The `u64` wraparound at and around `2 ^ 64`. -/
theorem u64GhostLen_wraparound_vectors :
    u64GhostLen 0 = 0 ∧ u64GhostLen (2 ^ 64) = 0 ∧ u64GhostLen (2 ^ 64 + 5) = 5 ∧
    u64GhostLen (2 ^ 64 - 1) = 18446744073709551615 ∧ u64GhostLen (2 * 2 ^ 64) = 0 ∧
    (2 : Nat) ^ 64 ≠ 0 := by
  decide

/-- `2 ^ 64` distinct appends are indistinguishable from none at `u64`, yet the list
    is non-empty and its `Nat` and `Int` lengths are exact. -/
theorem replicate_two_pow_64_lengths :
    u64ListGhostLen (List.replicate (2 ^ 64) 'x') = 0 ∧
    List.replicate (2 ^ 64) 'x' ≠ [] ∧
    natGhostLen (List.replicate (2 ^ 64) 'x') = 2 ^ 64 ∧
    intGhostLen (List.replicate (2 ^ 64) 'x') = 2 ^ 64 :=
  ⟨u64ListGhostLen_replicate_two_pow_64 'x', replicate_two_pow_64_ne_nil 'x',
    natGhostLen_replicate_two_pow_64 'x', intGhostLen_replicate_two_pow_64 'x'⟩

/-- **The `Slate` exploit.** From the fixed-width axioms plus either inductive axiom,
    any proposition follows — here `0 = 1`. -/
theorem slate_exploit_proves_anything {Coll : Type} (A : FixedWidthGhostCollectionAxioms Coll 64) :
    (A.ZeroLenIsEmpty → (0 : Nat) = 1) ∧ (A.LenStrictMono → (0 : Nat) = 1) :=
  ⟨fun h => (false_of_u64_ghost_length_zero_empty A h).elim,
    fun h => (false_of_u64_ghost_length_strict_mono A h).elim⟩

/-- Both `False` derivations at the narrow widths `u8`, `u16`, and `u32`, and at the
    degenerate width `0`. -/
theorem false_at_narrow_widths :
    ¬ (modCounterAxioms 8).ZeroLenIsEmpty ∧ ¬ (modCounterAxioms 8).LenStrictMono ∧
    ¬ (modCounterAxioms 16).ZeroLenIsEmpty ∧ ¬ (modCounterAxioms 32).LenStrictMono ∧
    ¬ (modCounterAxioms 0).ZeroLenIsEmpty ∧ ¬ (modCounterAxioms 0).LenStrictMono :=
  ⟨modCounterAxioms_not_zeroLenIsEmpty 8, modCounterAxioms_not_lenStrictMono 8,
    modCounterAxioms_not_zeroLenIsEmpty 16, modCounterAxioms_not_lenStrictMono 32,
    modCounterAxioms_not_zeroLenIsEmpty 0, modCounterAxioms_not_lenStrictMono 0⟩

/-- The `u8` counter model wraps at `256`: its length at `256` is `0` and at `255`
    is `255`. -/
theorem modCounter_u8_wraps :
    ((modCounterAxioms 8).len 256).val = 0 ∧ ((modCounterAxioms 8).len 255).val = 255 ∧
    ((modCounterAxioms 8).len 257).val = 1 := by
  decide

/-- The concrete witness of the `u8` "zero length means empty" failure: the
    collection `snoc 255` holds `256` elements, has length `0`, and is not empty. -/
theorem modCounter_u8_zero_len_nonempty :
    ∃ c, ((modCounterAxioms 8).len ((modCounterAxioms 8).snoc c)).val = 0 ∧
      ¬ (modCounterAxioms 8).IsEmpty ((modCounterAxioms 8).snoc c) :=
  ⟨255, by decide, fun h => Nat.succ_ne_zero 255 h⟩

/-- **Positive.** The list model satisfies every unbounded axiom, and its length
    after `n` appends is `n` at every `n`, `2 ^ 64` included. -/
theorem listGhostLength_never_wraps (n : Nat) :
    (listGhostLengthAxioms 'x').len
        (iterSnoc (listGhostLengthAxioms 'x').snoc n (listGhostLengthAxioms 'x').empty) = n :=
  (listGhostLengthAxioms 'x').len_iterSnoc n

/-- **Positive.** `Nat` and `Int` list lengths satisfy the inductive laws on a
    concrete list. -/
theorem nat_int_ghostLen_laws :
    natGhostLen ([] : List Nat) = 0 ∧ natGhostLen [3, 1, 4] = natGhostLen [1, 4] + 1 ∧
    natGhostLen [1, 4] < natGhostLen [3, 1, 4] ∧
    (natGhostLen ([] : List Nat) = 0 ↔ ([] : List Nat) = []) ∧
    intGhostLen [3, 1, 4] = 3 ∧ 0 ≤ intGhostLen [3, 1, 4] ∧
    intGhostLen [1, 4] < intGhostLen [3, 1, 4] :=
  ⟨natGhostLen_nil, natGhostLen_cons 3 [1, 4], natGhostLen_lt_cons 3 [1, 4],
    natGhostLen_eq_zero_iff [], rfl, intGhostLen_nonneg _, intGhostLen_lt_cons 3 [1, 4]⟩

/-- The guard coincides with model existence at concrete widths. -/
theorem guard_iff_model_examples :
    Nonempty (InductiveGhostLengthModel .unboundedNat) ∧
    Nonempty (InductiveGhostLengthModel .unboundedInt) ∧
    ¬ Nonempty (InductiveGhostLengthModel (.fixedUnsigned 64)) ∧
    ¬ Nonempty (InductiveGhostLengthModel (.fixedSigned 64)) :=
  ⟨(ghostLengthTypeGuard_iff_nonempty_model _).mp ghostLengthTypeGuard_unboundedNat,
    (ghostLengthTypeGuard_iff_nonempty_model _).mp ghostLengthTypeGuard_unboundedInt,
    isEmpty_model_of_fixedUnsigned 64,
    isEmpty_model_of_fixedSigned 64⟩

/-- Target-width-independent `USize` and arbitrary-width `BitVec` ghost lengths
    also wrap to zero and derive `False` from the zero-length-is-empty axiom. -/
theorem usize_and_bitvec_wraparound_false :
    usizeGhostLen USize.size = 0 ∧
    bitVecGhostLen 64 (2 ^ 64) = 0 ∧
    bitVecGhostLen 32 (2 ^ 32) = 0 ∧
    (¬ ∀ xs : List Unit, usizeListGhostLen xs = 0 → xs = []) ∧
    (¬ ∀ xs : List Unit, bitVecListGhostLen 64 xs = 0 → xs = []) :=
  ⟨usizeGhostLen_wraps, bitVec64GhostLen_two_pow_64, bitVecGhostLen_two_pow 32,
    false_of_usize_list_len_zero_imp_nil (),
    false_of_bitVec_list_len_zero_imp_nil 64 ()⟩

/-- Signed 64-bit `Int64` ghost lengths fail non-negativity at `2 ^ 63` and wrap to
    zero at `2 ^ 64`, refuting both non-negativity and emptiness axioms. -/
theorem i64_signed_overflow_and_wraparound_false :
    (i64GhostLen (2 ^ 63 - 1)).toInt = 2 ^ 63 - 1 ∧
    (i64GhostLen (2 ^ 63)).toInt < 0 ∧
    i64GhostLen (2 ^ 64) = 0 ∧
    (¬ ∀ xs : List Unit, 0 ≤ (i64ListGhostLen xs).toInt) ∧
    (¬ ∀ xs : List Unit, i64ListGhostLen xs = 0 → xs = []) :=
  ⟨i64GhostLen_max_pos, i64GhostLen_two_pow_63_neg, i64GhostLen_two_pow_64_zero,
    false_of_i64_list_len_nonneg (), false_of_i64_list_len_zero_imp_nil ()⟩

/-- The capacity of a fixed-width model is the exact length at which the machine
    type wraps to zero (unsigned) or turns negative (signed). -/
theorem fixed_width_capacity_matches_machine_overflow :
    (GhostIntWidth.fixedUnsigned 64).capacity? = some (2 ^ 64) ∧
      u64GhostLen (2 ^ 64) = 0 ∧
      (GhostIntWidth.fixedSigned 64).capacity? = some (2 ^ 63) ∧
      (i64GhostLen (2 ^ 63)).toInt < 0 :=
  ⟨fixedUnsigned64_capacity_is_u64_wraparound.1,
    fixedUnsigned64_capacity_is_u64_wraparound.2.2.2,
    fixedSigned64_capacity_is_i64_sign_flip.1,
    fixedSigned64_capacity_is_i64_sign_flip.2.2.2.2⟩

/-- Universal faithfulness across `UInt64`, `BitVec w`, and `Int64`: machine storage
    is faithful on `n` if and only if the corresponding `GhostIntWidth` represents `n`. -/
theorem machine_ghost_lengths_faithful_iff_represents (w n : Nat) :
    ((u64GhostLen n).toNat = n ↔ (GhostIntWidth.fixedUnsigned 64).Represents n) ∧
      ((bitVecGhostLen w n).toNat = n ↔ (GhostIntWidth.fixedUnsigned w).Represents n) ∧
      ((i64GhostLen n).toInt = Int.ofNat n ↔ (GhostIntWidth.fixedSigned 64).Represents n) :=
  ⟨u64GhostLen_faithful_iff n, bitVecGhostLen_faithful_iff w n, i64GhostLen_faithful_iff n⟩

/-- **Positive.** The unbounded `Int` list model is consistent and never wraps. -/
theorem unboundedInt_list_model_never_wraps (n : Nat) :
    Nonempty (UnboundedIntGhostCollectionAxioms (List Unit)) ∧
    (listIntGhostLengthAxioms 'x').len
        (iterSnoc (listIntGhostLengthAxioms 'x').snoc n (listIntGhostLengthAxioms 'x').empty) =
      Int.ofNat n :=
  ⟨unboundedIntGhostCollectionAxioms_nonempty, (listIntGhostLengthAxioms 'x').len_iterSnoc n⟩

/-! ## 4. Guard 3 — Error-Branch `True` Wildcard -/

/-- A checked increment over `u8`-like inputs: `Ok(x + 1)` below `255`, else
    `Err "overflow"`. -/
def checkedIncr (x : Nat) : FallibleOutcome Nat String :=
  if x < 255 then .ok (x + 1) else .err "overflow"

/-- Inputs on which `checkedIncr` must succeed. -/
abbrev incrExpectsOk (x : Nat) : Prop := x < 255

/-- Precondition of the increment contract: `x` is a `u8`. -/
abbrev incrPre (x : Nat) : Prop := x < 256

/-- The wildcard contract `| Ok v => v = x + 1 | Err _ => True`. -/
def incrWildcardPost : Nat → FallibleOutcome Nat String → Prop :=
  errorWildcardPost (fun x => x + 1)

/-- The guarded contract. -/
def incrGuardedPost : Nat → FallibleOutcome Nat String → Prop :=
  errorGuardedPost incrExpectsOk (fun x => x + 1) (fun _ => "overflow")

/-- The wildcard contract passes `PostconditionDichotomy`. -/
theorem incrWildcardPost_dichotomy : PostconditionDichotomy incrPre incrWildcardPost :=
  errorWildcardPost_postconditionDichotomy _ ⟨0, 1, by decide⟩ ⟨0, by decide⟩

/-- The correct implementation satisfies both contracts. -/
theorem checkedIncr_accepted :
    MutantSurvives incrPre incrWildcardPost checkedIncr ∧
    MutantSurvives incrPre incrGuardedPost checkedIncr := by
  refine ⟨fun x _ => ?_, fun x _ => ?_⟩
  · unfold checkedIncr
    split
    · exact rfl
    · exact True.intro
  · unfold checkedIncr
    split
    · rename_i h
      exact ⟨h, rfl⟩
    · rename_i h
      exact ⟨h, rfl⟩

/-- **Negative.** Four wrong implementations survive the wildcard contract. -/
theorem wrong_impls_survive_wildcard :
    MutantSurvives incrPre incrWildcardPost (fun _ => .err "overflow") ∧
    MutantSurvives incrPre incrWildcardPost (fun _ => .err "disk on fire") ∧
    MutantSurvives incrPre incrWildcardPost (fun _ => .ub) ∧
    MutantSurvives incrPre incrWildcardPost (fun _ => .unsupported) :=
  ⟨errorWildcardPost_constErr_survives _ _, errorWildcardPost_constErr_survives _ _,
    errorWildcardPost_constUb_survives _, errorWildcardPost_constUnsupported_survives _⟩

theorem incrGuardedPost_guarded :
    ErrorBranchGuardedPost incrPre incrExpectsOk incrGuardedPost :=
  errorGuardedPost_guarded _ _ _ _

/-- **Positive.** The same four wrong implementations are killed by the guarded
    contract. -/
theorem wrong_impls_killed_by_guard :
    ¬ MutantSurvives incrPre incrGuardedPost (fun _ => .err "overflow") ∧
    ¬ MutantSurvives incrPre incrGuardedPost (fun _ => .err "disk on fire") ∧
    ¬ MutantSurvives incrPre incrGuardedPost (fun _ => .ub) ∧
    ¬ MutantSurvives incrPre incrGuardedPost (fun _ => .unsupported) :=
  ⟨incrGuardedPost_guarded.kills_constErr ⟨0, by decide, by decide⟩ _,
    incrGuardedPost_guarded.kills_constErr ⟨0, by decide, by decide⟩ _,
    incrGuardedPost_guarded.kills_constUb ⟨0, by decide⟩,
    incrGuardedPost_guarded.kills_constUnsupported ⟨0, by decide⟩⟩

/-- **Positive.** On the overflow input the guarded contract accepts
    `Err "overflow"` and rejects the wrong payload `Err "disk on fire"`. -/
theorem wrong_err_payload_killed :
    incrGuardedPost 255 (.err "overflow") ∧ ¬ incrGuardedPost 255 (.err "disk on fire") := by
  have hErr : ¬ incrExpectsOk 255 := by decide
  have hAccept : incrGuardedPost 255 (.err "overflow") := ⟨hErr, rfl⟩
  exact ⟨hAccept,
    incrGuardedPost_guarded.kills_wrong_err_payload (by decide) hErr hAccept (by decide)⟩

/-- The wrong-payload mutant survives the wildcard on that same input. -/
theorem wrong_err_payload_survives_wildcard :
    incrWildcardPost 255 (.err "disk on fire") ∧ incrWildcardPost 255 (.err "overflow") :=
  ⟨True.intro, True.intro⟩

/-- The guarded contract has error-fibre dichotomy; the wildcard contract does not. -/
theorem errorFibreDichotomy_separates :
    ErrorFibreDichotomy incrPre incrGuardedPost ∧ ¬ ErrorFibreDichotomy incrPre incrWildcardPost :=
  ⟨incrGuardedPost_guarded.errorFibreDichotomy ⟨255, by decide, by decide⟩
      ⟨"a", "b", by decide⟩,
    errorWildcardPost_not_errorFibreDichotomy _⟩

/-- Spelling the tautology differently does not change the defect: a reflexive error
    arm, a double negation, and an implication into `True` all denote the wildcard
    postcondition, so they inherit its mutant survival. -/
theorem tautological_error_arms_are_the_wildcard :
    (fun (x : Nat) (out : FallibleOutcome Nat String) =>
        match out with
        | .ok v => v = x + 1
        | .err e => e = e
        | .ub => 0 = 0
        | .unsupported => ¬¬True) = errorWildcardPost (fun x => x + 1) ∧
      (fun (x : Nat) (out : FallibleOutcome Nat String) =>
        match out with
        | .ok v => v = x + 1
        | .err e => e = "overflow" → True
        | .ub => True
        | .unsupported => True) = errorWildcardPost (fun x => x + 1) ∧
      (fun (x : Nat) (out : Except String Nat) =>
        match out with
        | .ok v => v = x + 1
        | .error e => e = e) = exceptErrorWildcardPost (fun x => x + 1) :=
  ⟨eq_errorWildcardPost_of_tautological_fault_arms _ _ (fun _ _ => Iff.rfl) (fun _ _ => rfl)
      (fun _ => rfl) (fun _ h => h True.intro),
    eq_errorWildcardPost_of_tautological_fault_arms _ _ (fun _ _ => Iff.rfl)
      (fun _ _ _ => True.intro) (fun _ => True.intro) (fun _ => True.intro),
    eq_exceptErrorWildcardPost_of_tautological_error_arm _ _ (fun _ _ => Iff.rfl)
      (fun _ _ => rfl)⟩

/-- The guarded contract is dichotomous and forces fault-freedom of `checkedIncr`. -/
theorem guarded_dichotomy_and_fault_free :
    PostconditionDichotomy incrPre incrGuardedPost ∧
    ∀ x, incrPre x → (checkedIncr x).isFault = false :=
  ⟨incrGuardedPost_guarded.postconditionDichotomy ⟨0, by decide⟩,
    fun _ hx => incrGuardedPost_guarded.fault_free checkedIncr_accepted.2 hx⟩

/-- **Fail-closed.** The wildcard contract is not a guarded postcondition, for any
    choice of `expectsOk`. -/
theorem incrWildcardPost_not_guarded (expectsOk : Nat → Prop) :
    ¬ ErrorBranchGuardedPost incrPre expectsOk incrWildcardPost :=
  not_errorBranchGuardedPost_errorWildcardPost _ ⟨0, by decide⟩

/-- The pure `Except` wildcard: dichotomous, yet the constant-`error` mutant
    survives and no `error` payload is ever rejected. -/
theorem except_wildcard_vacuity :
    PostconditionDichotomy incrPre
        (exceptErrorWildcardPost (ε := String) (fun x : Nat => x + 1)) ∧
    MutantSurvives incrPre (exceptErrorWildcardPost (fun x : Nat => x + 1))
        (fun _ => Except.error "boom") ∧
    exceptErrorWildcardPost (fun x : Nat => x + 1) 3 (Except.error "boom" : Except String Nat) ∧
    exceptErrorWildcardPost (fun x : Nat => x + 1) 3 (Except.ok 4 : Except String Nat) ∧
    ¬ exceptErrorWildcardPost (fun x : Nat => x + 1) 3 (Except.ok 5 : Except String Nat) :=
  ⟨exceptErrorWildcardPost_postconditionDichotomy _ ⟨0, 1, by decide⟩ ⟨0, by decide⟩,
    exceptErrorWildcardPost_constError_survives _ _, True.intro, rfl,
    fun h : (5 : Nat) = 3 + 1 => absurd h (by decide)⟩

/-- **Positive (`Except`).** `exceptGuardedPost` satisfies
    `ErrorBranchGuardedExceptPost`, kills constant-`error` and wrong-payload
    mutants, and achieves error-fibre dichotomy; `exceptErrorWildcardPost` fails it. -/
theorem except_guarded_kills_mutants_and_dichotomy :
    let post := exceptGuardedPost incrExpectsOk (fun x => x + 1) (fun _ => "overflow")
    ¬ MutantSurvives incrPre post (fun _ => Except.error "overflow") ∧
    ¬ post 255 (Except.error "disk on fire") ∧
    (∃ x, incrPre x ∧ ∃ eOk eBad : String,
      post x (.error eOk) ∧ ¬ post x (.error eBad)) ∧
    ¬ ErrorBranchGuardedExceptPost incrPre incrExpectsOk
        (exceptErrorWildcardPost (ε := String) (fun x : Nat => x + 1)) := by
  have hG := exceptGuardedPost_guarded incrPre incrExpectsOk (fun x => x + 1) (fun _ => "overflow")
  have hErr : ¬ incrExpectsOk 255 := by decide
  have hAccept : exceptGuardedPost incrExpectsOk (fun x => x + 1) (fun _ => "overflow")
      255 (.error "overflow") := ⟨hErr, rfl⟩
  exact ⟨hG.kills_constError ⟨0, by decide, by decide⟩ "overflow",
    hG.kills_wrong_error_payload (by decide) hErr hAccept (by decide),
    hG.errorDichotomy ⟨255, by decide, by decide⟩ ⟨"a", "b", by decide⟩,
    not_errorBranchGuardedExceptPost_exceptErrorWildcardPost _
      ⟨0, by decide, by decide⟩ "overflow"⟩

/-- `MirSemantics` counterexamples: `Div` and `Rem` by zero are `.ub`, the wildcard
    correspondence accepts both, and the guarded correspondence rejects both. -/
theorem scalar_corr_mir_counterexamples (expected : Value) :
    evalScalarBinOp .rem { bits := 7, sizeBytes := 1 } { bits := 0, sizeBytes := 1 } [] = .ub ∧
    scalarWildcardCorr expected
      (evalScalarBinOp .div { bits := 1, sizeBytes := 1 } { bits := 0, sizeBytes := 1 } []) ∧
    scalarWildcardCorr expected
      (evalScalarBinOp .rem { bits := 7, sizeBytes := 1 } { bits := 0, sizeBytes := 1 } []) ∧
    ¬ scalarGuardedCorr expected
      (evalScalarBinOp .div { bits := 1, sizeBytes := 1 } { bits := 0, sizeBytes := 1 } []) ∧
    ¬ scalarGuardedCorr expected
      (evalScalarBinOp .rem { bits := 7, sizeBytes := 1 } { bits := 0, sizeBytes := 1 } []) :=
  ⟨rfl, scalarWildcardCorr_accepts_div_by_zero expected, True.intro,
    scalarGuardedCorr_rejects_div_by_zero expected, fun h => h⟩

/-- The wildcard correspondence still rejects a wrong *successful* value: its
    dichotomy comes from the `ok` arm alone. -/
theorem scalarWildcardCorr_rejects_wrong_ok :
    ¬ scalarWildcardCorr (.scalar { bits := 2, sizeBytes := 1 })
      (evalScalarBinOp .div { bits := 1, sizeBytes := 1 } { bits := 1, sizeBytes := 1 } []) := by
  rw [evalScalarBinOp_div_one_ok]
  intro h
  cases h

/-- `MirStepNode` classification of returns, halts, and faults. -/
theorem classifyMirStepNode_vectors :
    classifyMirStepNode (MirStepNode.fail .ub) = some .ub ∧
    classifyMirStepNode (MirStepNode.fail .unsupported) = some .unsupported ∧
    classifyMirStepNode (MirStepNode.fail .outOfFuel) = some .unsupported ∧
    classifyMirStepNode (.ret .panic) = some (.err .panic) ∧
    classifyMirStepNode (.ret .abort) = some (.err .abort) ∧
    classifyMirStepNode (.ret (.normal (.unit, {}))) = some (.ok (.unit, {})) ∧
    classifyMirStepNode (.tau (.halted .panic)) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The `Rem` fixture's faulting step is classified `ub` and accepted by the
    wildcard postcondition, while the echo entry point's steps never fault. -/
theorem mirStepNode_wildcard_counterexample (expected : MirReturn) :
    classifyMirStepNode
        (stepMirState (remEntryBody "fw::__start")
          (.running (initMachineStateWithCallees (remEntryBody "fw::__start")
            (EntryDemo.u8Arg 0) []))) = some .ub ∧
    errorWildcardPost (fun _ : Unit => expected) ()
      (.ub : FallibleOutcome MirReturn HaltError) ∧
    (∃ out, classifyMirStepNode
        (stepMirState (EntryDemo.divEntryBody "_start")
          (.running (initMachineStateWithCallees (EntryDemo.divEntryBody "_start")
            (EntryDemo.u8Arg 0) []))) = some out ∧ out = .ub) := by
  refine ⟨?_, True.intro, ?_⟩
  · rw [remEntry_step_zero]
    rfl
  · obtain ⟨out, hOut, hUb, -⟩ := errorWildcardPost_accepts_divEntry_ub "_start" expected
    exact ⟨out, hOut, hUb⟩

/-! ## 5. Kernel Environment Audit

Every constant of `Anneal.SpecBoundaryGuards` and every constant added by this file
must be a safe kernel declaration (no `unsafe`, no `partial`, no `axiom`, no
`opaque`) whose transitive axiom closure lies inside
`{propext, Classical.choice, Quot.sound}`. Every other axiom fails the audit: a
proof gap, and the compiler-trust axioms behind native evaluation, are rejected
exactly like a user-declared one. The audit also enforces theorem-count floors and
stays silent on success. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let moduleName := `Anneal.SpecBoundaryGuards
  let some modIdx := env.getModuleIdx? moduleName
    | throwError "module {moduleName} is not imported"
  -- Audit one constant; returns `true` when it is a kernel theorem.
  let audit (n : Name) (ci : ConstantInfo) : CommandElabM Bool := do
    if ci.isUnsafe then throwError "unsafe declaration: {n}"
    if ci.isPartial then throwError "partial declaration: {n}"
    match ci with
    | .axiomInfo _ => throwError "axiom declaration: {n}"
    | .opaqueInfo _ => throwError "opaque declaration: {n}"
    | .defnInfo v =>
      unless v.safety == .safe do throwError "non-safe definition: {n}"
    | _ => pure ()
    for a in ← liftCoreM <| Lean.collectAxioms n do
      unless allowed.contains a do
        throwError "{n} depends on disallowed axiom {a}"
    return ci matches .thmInfo _
  let mut moduleDecls : Nat := 0
  let mut moduleThms : Nat := 0
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some modIdx then
      moduleDecls := moduleDecls + 1
      if ← audit n ci then
        moduleThms := moduleThms + 1
  let mut testDecls : Nat := 0
  let mut testThms : Nat := 0
  for (n, ci) in env.constants.map₂.toList do
    testDecls := testDecls + 1
    if ← audit n ci then
      testThms := testThms + 1
  -- Flagship results must exist as theorems of the audited module.
  for flagship in
      [``Anneal.SpecBoundaryGuards.PropertyClassTag.asStr_injective,
        ``Anneal.SpecBoundaryGuards.SpecBoundaryGuardClass.guardId_injective,
        ``Anneal.SpecBoundaryGuards.classifyEntryPoint_isSome_of_exported_entry_symbol,
        ``Anneal.SpecBoundaryGuards.classifyEntryPoint_mono_crateNoMain,
        ``Anneal.SpecBoundaryGuards.claimClosedProgramSafe_of_guard,
        ``Anneal.SpecBoundaryGuards.statefulClaimClosedProgramSafe_of_guard,
        ``Anneal.SpecBoundaryGuards.totalClaimClosedProgramTotal_of_guard,
        ``Anneal.SpecBoundaryGuards.EntryDemo.main_requires_collapse,
        ``Anneal.SpecBoundaryGuards.EntryDemo.start_requires_collapse,
        ``Anneal.SpecBoundaryGuards.EntryDemo.divEntryTotalClaim_collapse,
        ``Anneal.SpecBoundaryGuards.EntryDemo.main_requires_total_collapse,
        ``Anneal.SpecBoundaryGuards.u64GhostLen_two_pow_64,
        ``Anneal.SpecBoundaryGuards.usizeGhostLen_wraps,
        ``Anneal.SpecBoundaryGuards.bitVec64GhostLen_two_pow_64,
        ``Anneal.SpecBoundaryGuards.i64GhostLen_two_pow_63_neg,
        ``Anneal.SpecBoundaryGuards.fixedUnsigned64_capacity_is_u64_wraparound,
        ``Anneal.SpecBoundaryGuards.fixedSigned64_capacity_is_i64_sign_flip,
        ``Anneal.SpecBoundaryGuards.u64GhostLen_faithful_iff,
        ``Anneal.SpecBoundaryGuards.bitVecGhostLen_faithful_iff,
        ``Anneal.SpecBoundaryGuards.i64GhostLen_faithful_iff,
        ``Anneal.SpecBoundaryGuards.false_of_i64_list_len_nonneg,
        ``Anneal.SpecBoundaryGuards.false_of_fixedWidth_ghost_length_strict_mono,
        ``Anneal.SpecBoundaryGuards.false_of_fixedWidth_ghost_length_zero_empty,
        ``Anneal.SpecBoundaryGuards.isEmpty_model_of_fixedSigned,
        ``Anneal.SpecBoundaryGuards.unboundedIntGhostCollectionAxioms_nonempty,
        ``Anneal.SpecBoundaryGuards.ghostLengthTypeGuard_iff_nonempty_model,
        ``Anneal.SpecBoundaryGuards.eq_errorWildcardPost_of_tautological_fault_arms,
        ``Anneal.SpecBoundaryGuards.eq_exceptErrorWildcardPost_of_tautological_error_arm,
        ``Anneal.SpecBoundaryGuards.errorWildcardPost_postconditionDichotomy,
        ``Anneal.SpecBoundaryGuards.errorWildcardPost_not_errorFibreDichotomy,
        ``Anneal.SpecBoundaryGuards.scalarWildcardCorr_accepts_div_by_zero,
        ``Anneal.SpecBoundaryGuards.ErrorBranchGuardedPost.kills_constErr,
        ``Anneal.SpecBoundaryGuards.exceptGuardedPost_guarded] do
    match env.find? flagship with
    | some (.thmInfo _) =>
      unless env.getModuleIdxFor? flagship == some modIdx do
        throwError "flagship theorem {flagship} is not defined in {moduleName}"
    | _ => throwError "flagship theorem {flagship} is missing"
  unless moduleThms ≥ 120 do
    throwError "{moduleName}: only {moduleThms} kernel theorems (expected ≥ 120)"
  unless moduleDecls ≥ moduleThms do
    throwError "{moduleName}: inconsistent declaration count {moduleDecls}"
  unless testThms ≥ 50 do
    throwError "SpecBoundaryGuardsTests: only {testThms} kernel theorems (expected ≥ 50)"
  unless testDecls ≥ testThms do
    throwError "SpecBoundaryGuardsTests: inconsistent declaration count {testDecls}"

end Anneal.SpecBoundaryGuardsTests
