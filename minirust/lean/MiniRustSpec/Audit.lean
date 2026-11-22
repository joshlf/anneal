/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import MiniRustSpec.Anchors
import MiniRustSpec.Correspondence.Witness
import MiniRustSpec.Correspondence.PointerWitness
import MiniRustSpec.Correspondence.RefWitness
import MiniRustSpec.Correspondence.TbWitness
import MiniRustSpec.Correspondence.Provenance
import MiniRustSpec.Correspondence.ProvenanceWitness
import MiniRustSpec.Correspondence.WideSliceDst
import MiniRustSpec.Correspondence.IntrinsicBoundary

/-!
# Axiom audit

`#assert_standard_axioms` fails the build unless each listed declaration
depends only on Lean's standard axioms (`propext`, `Quot.sound`,
`Classical.choice`); in particular on no `sorryAx` and no
`Lean.ofReduceBool` (which `native_decide` would introduce). It also logs the
axioms of each declaration, so `lake build MiniRustSpec.Audit` doubles as the
`#print axioms` receipt.

`#check_theorem_deps` (`checkTheoremDeps`) performs the same check on a group
of declarations and logs one summary line per group, tagged `[ANCHOR-AUDIT]`
(the anchors of the interpretation), `[SIMULATION-AUDIT]` (the
correspondence theorems and the lemmas they rest on), `[WITNESS-AUDIT]`
(the concrete witnesses; a second and a third `[WITNESS-AUDIT]` line cover
`Correspondence.IntrinsicFallback` and `Correspondence.IntrinsicBoundary`),
`[POINTER-AUDIT]` (the MR-3.1 raw pointer lemmas of `Correspondence.Pointers`
and `Correspondence.PointerStep` and the witnesses of
`Correspondence.PointerWitness`), `[REF-AUDIT]` (the MR-3.2 reference,
reborrowing, safe-pointer validity, and Tree Borrows `ReborrowSettings`
theorems and witnesses), `[TB-AUDIT]` (the MR-3.2 Tree Borrows `wf` /
`wfLive` / `no_specPanic` invariants, dereference-`move` and pointer-to-pointer
dereference-copy correspondence lemmas, and `Correspondence.TbWitness` 3-way
witnesses), `[PROV-AUDIT]` (the MR-3.3 provenance-cast theorems and
witnesses), `[WIDE-SLICE-DST-AUDIT]` (the wide-slice and unsized DST
pointer-metadata, layout, indexing, reborrowing, and divergence theorems and
witnesses of `Correspondence.WideSliceDst`), or `[DEINIT-AUDIT]` (the projected-`Deinit` fragment `inFragmentD`
of `Correspondence.DeinitWindow`, the `Rvalue::Discriminant` lowering, the
sub-place audit hook `subplace_audit_closure` of `Correspondence.DeinitBridge`
— the one `MiniRustSpec` module that imports `Anneal.Mir.AdtAndControl` — and
their witnesses), ending in `sorry_free=true`. A group that depends on `sorryAx` or
on any other non-standard axiom fails the build instead.

`#assert_minirustspec_import_isolation` (`[IMPORT-ISOLATION]`) fails the build unless the
module import graph satisfies the `MiniRustSpec` import-isolation invariant of
`Correspondence.DeinitBridge` across **every** `Anneal.*` module in the graph (`[adv ep2-A3]`):
`DeinitBridge` is the only `MiniRustSpec` module that directly imports an `Anneal.*` module, every
import path from another `MiniRustSpec` module to *any* `Anneal.*` module passes through
`DeinitBridge`, its only client is `Correspondence.IntrinsicBoundary`, and the core modules
(`Interp`, `Generated`, `Correspondence.Translate`, `Correspondence.Simulation`,
`Correspondence.IntrinsicFallback`) reach neither `DeinitBridge` nor any `Anneal.*` module. The
checker validates itself on five synthetic negative-control graphs (including transitive reachability
to non-`AdtAndControl` `Anneal.*` modules and bypasses from an allowed bridge client) and one
conforming multi-`Anneal` positive-control graph.

`#assert_adt_control_audit_coverage` (`[ADT-AUDIT-COVERAGE]`, `[ANNEAL-AXIOMS]`, `[adv ep2-B4]` /
`[adv ep2-A4]`) fails the build unless:
1. every public, user-declared theorem of `Anneal.Mir.AdtAndControl` lies in the dependency closure
   of the three `[DEINIT-AUDIT]` closures (`subplace_audit_closure`, `call_intrinsic_audit_closure`,
   `adt_control_residual_audit_closure`) together with the `MiniRustSpec` declarations audited by
   `#assert_all_minirustspec_standard_axioms` — and in particular **every** Episode 2 Section 5
   public theorem of `Anneal.Mir.AdtAndControl` is reachable from `call_intrinsic_audit_closure`
   alone;
2. both `adt_control_residual_audit_closure` and `call_intrinsic_audit_closure` are non-vacuously
   required (negative controls); and
3. every declaration across **every** imported `Anneal.*` module (`Anneal.Mir.AdtAndControl` and
   `Anneal.Mir.PlaceAndRvalue`, including private and compiler-generated ones) is `unsafe`-free and
   depends only on the standard axioms (`propext`, `Quot.sound`, `Classical.choice`) via both
   `Lean.collectAxioms` and `dependencyClosureWithAxioms`.
-/

namespace MiniRustSpec.Audit

open Lean Elab Command

/-- Fail unless every listed declaration is distinct and depends only on the
standard axioms. -/
elab "#assert_standard_axioms " ids:ident* : command => do
  let mut seen : Lean.NameSet := {}
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    if seen.contains n then
      throwError "duplicate declaration {n} in #assert_standard_axioms"
    seen := seen.insert n
    let axs ← liftCoreM <| Lean.collectAxioms n
    for a in axs do
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{n} depends on the non-standard axiom {a}"
    logInfo m!"{n} depends on axioms: {axs.toList}"

/-- `checkTheoremDeps`: fail unless every listed declaration is a distinct
`theorem` (`ConstantInfo.thmInfo`) that depends only on the standard axioms,
then log one line `<tag> decls=<n> axioms=<union> sorry_free=true`. -/
elab "#check_theorem_deps " tag:str ids:ident* : command => do
  let env ← getEnv
  let mut seen : Lean.NameSet := {}
  let mut union : Array Name := #[]
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    if seen.contains n then
      throwError "{tag.getString} duplicate declaration {n}"
    seen := seen.insert n
    unless (env.find? n matches some (.thmInfo _)) do
      throwError "{tag.getString} {n} is not a theorem"
    let axs ← liftCoreM <| Lean.collectAxioms n
    for a in axs do
      if a == ``sorryAx then
        throwError "{tag.getString} {n} depends on sorryAx"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{tag.getString} {n} depends on the non-standard axiom {a}"
      unless union.contains a do
        union := union.push a
  logInfo m!"{tag.getString} decls={ids.size} axioms={union.toList} sorry_free=true"

/-- Reachability in a module import graph given by its direct-import adjacency `direct`: whether
`target` is reachable from `start` along import edges without passing through module `avoid`
(pass `.anonymous` to avoid nothing). -/
def importGraphReaches (direct : Std.HashMap Lean.Name (Array Lean.Name))
    (start target avoid : Lean.Name) : Bool := Id.run do
  let mut visited : Lean.NameSet := {}
  let mut stack : Array Lean.Name := #[start]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if n == target then
      return true
    if n == avoid || visited.contains n then
      continue
    visited := visited.insert n
    for imp in direct.getD n #[] do
      stack := stack.push imp
  return false

/-- Violations of the `MiniRustSpec` import-isolation invariant in the module import graph
`graph` (every module paired with its direct imports, hardened in `[adv ep2-A3]` across **all**
`Anneal.*` modules in `graph` and without `else if` suppression):
1. no `MiniRustSpec` module other than `bridge` directly imports any `Anneal.*` module;
2. no `MiniRustSpec` module other than `bridge` reaches *any* `Anneal.*` module (including `adt`
   and upstream dependencies such as `Anneal.Mir.PlaceAndRvalue`) along an import path that avoids
   `bridge`;
3. no `MiniRustSpec` module other than `bridge` and its `allowed` clients reaches `bridge` or any
   `Anneal.*` module;
4. every `core` module is present in `graph` and reaches neither `bridge` nor any `Anneal.*` module. -/
def importIsolationViolations (graph : Array (Lean.Name × Array Lean.Name))
    (bridge adt : Lean.Name) (allowed core : List Lean.Name) : Array String := Id.run do
  let direct : Std.HashMap Lean.Name (Array Lean.Name) :=
    graph.foldl (fun m p => m.insert p.1 p.2) {}
  let mut annealTargets : Array Lean.Name := #[adt]
  for (mName, imps) in graph do
    if (`Anneal).isPrefixOf mName && !annealTargets.contains mName then
      annealTargets := annealTargets.push mName
    for imp in imps do
      if (`Anneal).isPrefixOf imp && !annealTargets.contains imp then
        annealTargets := annealTargets.push imp
  let mut out : Array String := #[]
  for (mod, imps) in graph do
    if (`MiniRustSpec).isPrefixOf mod && mod != bridge then
      for imp in imps do
        if (`Anneal).isPrefixOf imp then
          out := out.push s!"{mod} directly imports {imp}"
      for ann in annealTargets do
        if importGraphReaches direct mod ann bridge then
          out := out.push s!"{mod} reaches {ann} along a path avoiding {bridge}"
      let reachesBridgeOrAnneal :=
        importGraphReaches direct mod bridge .anonymous ||
        annealTargets.any (fun ann => importGraphReaches direct mod ann .anonymous)
      if reachesBridgeOrAnneal && !allowed.contains mod then
        out := out.push s!"{mod} reaches {bridge}/Anneal.* but is not an allowed client of {bridge}"
  for c in core do
    if !direct.contains c then
      out := out.push s!"core module {c} is missing from the import graph"
    else
      if importGraphReaches direct c bridge .anonymous then
        out := out.push s!"core module {c} reaches {bridge}"
      for ann in annealTargets do
        if importGraphReaches direct c ann .anonymous then
          out := out.push s!"core module {c} reaches {ann}"
  return out

/-- `[IMPORT-ISOLATION]`: fail unless the module import graph of this environment satisfies the
`MiniRustSpec` import-isolation invariant (`importIsolationViolations`), after first checking
that the checker rejects five synthetic violating graphs (negative controls: direct `Anneal.*`
import, bypass from an unlisted module, bypass from an *allowed* bridge client, transitive
reachability to a non-`AdtAndControl` `Anneal.*` module via a non-`MiniRustSpec` shim, and an
unlisted client of `DeinitBridge`) and accepts a synthetic multi-`Anneal` conforming graph
(positive control). -/
elab "#assert_minirustspec_import_isolation" : command => do
  let env ← getEnv
  let graph : Array (Lean.Name × Array Lean.Name) :=
    (env.header.moduleNames.zip env.header.moduleData).map fun (n, d) =>
      (n, d.imports.map (·.module))
  let bridge := `MiniRustSpec.Correspondence.DeinitBridge
  let adt := `Anneal.Mir.AdtAndControl
  let par := `Anneal.Mir.PlaceAndRvalue
  let ib := `MiniRustSpec.Correspondence.IntrinsicBoundary
  let allowed := [ib]
  let core := [`MiniRustSpec.Correspondence.Translate, `MiniRustSpec.Correspondence.Simulation,
    `MiniRustSpec.Correspondence.IntrinsicFallback, `MiniRustSpec.Interp, `MiniRustSpec.Generated]
  let translate := `MiniRustSpec.Correspondence.Translate
  let negDirect : Array (Lean.Name × Array Lean.Name) :=
    #[(translate, #[`Anneal.Scalars]), (`Anneal.Scalars, #[])]
  let negBypass : Array (Lean.Name × Array Lean.Name) :=
    #[(`MiniRustSpec.Leaky, #[bridge, `Trusted.Shim]), (bridge, #[adt]), (`Trusted.Shim, #[adt]),
      (adt, #[])]
  let negAllowedBypass : Array (Lean.Name × Array Lean.Name) :=
    #[(ib, #[bridge, `Trusted.Shim]), (bridge, #[adt]), (`Trusted.Shim, #[adt]), (adt, #[])]
  let negOtherAnneal : Array (Lean.Name × Array Lean.Name) :=
    #[(translate, #[`Trusted.Shim]), (`Trusted.Shim, #[par]), (par, #[])]
  let negClient : Array (Lean.Name × Array Lean.Name) :=
    #[(translate, #[bridge]), (bridge, #[adt]), (adt, #[])]
  let pos : Array (Lean.Name × Array Lean.Name) :=
    #[(ib, #[bridge]), (bridge, #[adt]), (adt, #[par]), (par, #[]), (translate, #[])]
  for (label, g) in [("direct", negDirect), ("bypass", negBypass),
      ("allowed-bypass", negAllowedBypass), ("other-anneal", negOtherAnneal),
      ("client", negClient)] do
    if (importIsolationViolations g bridge adt allowed []).isEmpty then
      throwError "[IMPORT-ISOLATION] negative control `{label}` was not rejected"
  unless (importIsolationViolations pos bridge adt allowed [translate]).isEmpty do
    throwError "[IMPORT-ISOLATION] positive control was rejected"
  let violations := importIsolationViolations graph bridge adt allowed core
  unless violations.isEmpty do
    throwError "[IMPORT-ISOLATION] violations: {violations.toList}"
  let direct : Std.HashMap Lean.Name (Array Lean.Name) :=
    graph.foldl (fun m p => m.insert p.1 p.2) {}
  let mrs := graph.filter fun p => (`MiniRustSpec).isPrefixOf p.1
  let clients := mrs.filterMap fun p =>
    if p.1 != bridge && importGraphReaches direct p.1 adt .anonymous then some p.1 else none
  unless importGraphReaches direct bridge adt .anonymous do
    throwError "[IMPORT-ISOLATION] {bridge} does not import {adt}"
  logInfo m!"[IMPORT-ISOLATION] minirustspec_modules={mrs.size} anneal_importer={bridge} bridge_clients={clients.toList} core_checked={core.length} controls=6/6 ok=true"

/-- Dependency closure of `seeds` in the environment `env` (through the types and the values of
definitions **and** theorems), together with every axiom it reaches. -/
def dependencyClosureWithAxioms (env : Lean.Environment) (seeds : Array Lean.Name) :
    Lean.NameSet × Array Lean.Name := Id.run do
  let mut visited : Lean.NameSet := {}
  let mut axs : Array Lean.Name := #[]
  let mut stack := seeds
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then
      continue
    visited := visited.insert n
    if let some ci := env.find? n then
      if ci matches .axiomInfo _ then
        axs := axs.push n
      for c in ci.type.getUsedConstants do
        unless visited.contains c do
          stack := stack.push c
      if let some v := ci.value? (allowOpaque := true) then
        for c in v.getUsedConstants do
          unless visited.contains c do
            stack := stack.push c
  return (visited, axs)

/-- `[ADT-AUDIT-COVERAGE]` and `[ANNEAL-AXIOMS]` (`[adv ep2-B4]` / `[adv ep2-A4]`): fail unless
1. every public, user-declared theorem of `Anneal.Mir.AdtAndControl` lies in the dependency closure
   of the three `[DEINIT-AUDIT]` closures (`subplace_audit_closure`, `call_intrinsic_audit_closure`,
   `adt_control_residual_audit_closure`) together with the `MiniRustSpec` declarations whose axioms
   `#assert_all_minirustspec_standard_axioms` checks — AND every Episode 2 Section 5 public theorem
   of `Anneal.Mir.AdtAndControl` (starting at `LIntrinsicOp.fromRustIntrinsicKind_toRustIntrinsicKind`)
   is reachable from `call_intrinsic_audit_closure` **alone**;
2. (negative controls) dropping `adt_control_residual_audit_closure` leaves residual theorems
   uncovered, and dropping `call_intrinsic_audit_closure` leaves Section 5 theorems uncovered; and
3. every declaration across **every** imported `Anneal.*` module (`Anneal.Mir.AdtAndControl` and
   `Anneal.Mir.PlaceAndRvalue`, including private and compiler-generated ones) is `!ci.isUnsafe` and
   depends only on `propext`, `Quot.sound`, and `Classical.choice` under both `Lean.collectAxioms`
   and `dependencyClosureWithAxioms`. -/
elab "#assert_adt_control_audit_coverage" : command => do
  let env ← getEnv
  let adt := `Anneal.Mir.AdtAndControl
  let par := `Anneal.Mir.PlaceAndRvalue
  let subplaceClosure := `MiniRustSpec.Correspondence.DeinitBridge.subplace_audit_closure
  let callClosure := `MiniRustSpec.Correspondence.DeinitBridge.call_intrinsic_audit_closure
  let residual := `MiniRustSpec.Correspondence.DeinitBridge.adt_control_residual_audit_closure
  let sec5Anchor := `Anneal.Mir.AdtAndControl.LIntrinsicOp.fromRustIntrinsicKind_toRustIntrinsicKind
  let some idx := env.getModuleIdx? adt
    | throwError "[ADT-AUDIT-COVERAGE] {adt} is not imported"
  unless (env.getModuleIdx? par).isSome do
    throwError "[ADT-AUDIT-COVERAGE] {par} is not imported"
  let some sec5Dr := Lean.declRangeExt.find? env sec5Anchor
    | throwError "[ADT-AUDIT-COVERAGE] missing declaration range for Section 5 anchor {sec5Anchor}"
  let sec5StartLine := sec5Dr.range.pos.line
  let consts := env.header.moduleData[idx.toNat]!.constNames
  let targets := consts.filter fun c =>
    (env.find? c matches some (.thmInfo _)) && !Lean.isPrivateName c && !c.isInternalDetail &&
      !env.isProjectionFn c && (Lean.declRangeExt.find? env c).isSome
  let sec5Targets := targets.filter fun c =>
    match Lean.declRangeExt.find? env c with
    | some dr => dr.range.pos.line >= sec5StartLine
    | none => false
  if sec5Targets.isEmpty then
    throwError "[ADT-AUDIT-COVERAGE] Section 5 theorem list is unexpectedly empty"
  let mut seeds : Array Lean.Name := #[]
  for i in [:env.header.moduleNames.size] do
    if (`MiniRustSpec).isPrefixOf env.header.moduleNames[i]! then
      seeds := seeds ++ env.header.moduleData[i]!.constNames
  for req in [subplaceClosure, callClosure, residual] do
    unless seeds.contains req do
      throwError "[ADT-AUDIT-COVERAGE] {req} is not an imported MiniRustSpec declaration"
  let (coveredByCall, _) := dependencyClosureWithAxioms env #[callClosure]
  let missingSec5 := sec5Targets.filter fun n => !coveredByCall.contains n
  unless missingSec5.isEmpty do
    throwError "[ADT-AUDIT-COVERAGE] {missingSec5.size} Section 5 theorems of {adt} missing from {callClosure}: {missingSec5.toList.take 25}"
  let (covered, _) := dependencyClosureWithAxioms env seeds
  let missing := targets.filter fun n => !covered.contains n
  unless missing.isEmpty do
    throwError "[ADT-AUDIT-COVERAGE] {missing.size} public theorems of {adt} escape the axiom audit: {missing.toList.take 25}"
  let (coveredWithoutResidual, _) := dependencyClosureWithAxioms env (seeds.filter (· != residual))
  let needed := (targets.filter fun n => !coveredWithoutResidual.contains n).size
  if needed == 0 then
    throwError "[ADT-AUDIT-COVERAGE] negative control failed: {residual} covers nothing new"
  let (coveredWithoutCall, _) := dependencyClosureWithAxioms env (seeds.filter (· != callClosure))
  let neededCall := (sec5Targets.filter fun n => !coveredWithoutCall.contains n).size
  if neededCall == 0 then
    throwError "[ADT-AUDIT-COVERAGE] negative control failed: {callClosure} covers nothing new in Section 5"
  let mut annealMods : Array Lean.Name := #[]
  let mut annealConsts : Array Lean.Name := #[]
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if (`Anneal).isPrefixOf modName then
      annealMods := annealMods.push modName
      for c in env.header.moduleData[i]!.constNames do
        annealConsts := annealConsts.push c
        if let some ci := env.find? c then
          if ci.isUnsafe then
            throwError "[ANNEAL-AXIOMS] unsafe declaration {c} in {modName}"
        let cAxs ← liftCoreM <| Lean.collectAxioms c
        for a in cAxs do
          unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
            throwError "[ANNEAL-AXIOMS] {c} (in {modName}) depends on the non-standard axiom {a}"
  let (_, axs) := dependencyClosureWithAxioms env annealConsts
  for a in axs do
    unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
      throwError "[ANNEAL-AXIOMS] transitive closure of Anneal.* depends on the non-standard axiom {a}"
  logInfo m!"[ADT-AUDIT-COVERAGE] adt_public_theorems={targets.size} audited={targets.size} sec5_theorems={sec5Targets.size} sec5_via_call_closure={sec5Targets.size} only_via_call_closure={neededCall} only_via_residual_closure={needed} ok=true"
  logInfo m!"[ANNEAL-AXIOMS] modules={annealMods.toList} decls={annealConsts.size} axioms={axs.toList} unsafe_free=true sorry_free=true"

open MiniRustSpec.LibSpecr in
#assert_standard_axioms
  Nondet
  NdResult

#assert_standard_axioms MiniRustSpec.Gen.NdResult

open MiniRustSpec.Correspondence in
#assert_standard_axioms
  unitPlace_eq_buildUnitPlace
  abortTerminator_eq_buildAbort
  unitType_eq_unitTy
  mapGet_eq_of_mem_nodup
  isAssume_iff
  translateStmtResult_some
  splitStmts_names
  translateTerminatorInProg_names
  nodup_map_bbName
  bbName_range'_nodup
  range'_append_of_le
  mem_bbName_range'
  translateBlocksInProg_names
  splitStmts_segChain
  translateBlocksInProg_segChain
  progStatementOk_notAssume
  progStatementOk_assume
  SegChain.pcZero
  SegPc.atStmt_notAssume
  SegPc.atStmt_assume
  SegPc.atEnd
  evalPlace_unitPlace
  placeStore_unitValue
  evalTerminator_assume_spec
  evalStmt_assume_anneal
  statementOk_isAssume
  splitStmts_statements
  mapM_translateStmtResult_of_noAssume
  evalPlace_derefFree_mach
  evalPlace_rethread_derefFree
  translatePlace_derefFree
  translateFnInProg_spec
  translateProgFns_get
  findCallee_idx
  lookupFnName_of_lookupFnTarget
  lookupFnTarget_zipIdx_aux
  lookupFnName_zipIdx_aux
  translateProg_spec
  translateCallConv_eq_some_iff
  translateUnwindAction_spec
  mkStartFn_spec
  translateTerminatorInProg_eq_of_not_call
  translateBlocksInProg_eq_of_no_calls
  translateFnInProg_eq_translateFn_of_no_calls
  multi_step_correspondence
  multi_step_start
  multi_step_start_with_no_returnRel
  multi_step_start_no_returnRel
  initMachineStateWithCallees_startRel
  bodyInProgFragment_allScalar
  itOf_scalar_layouts
  tyOf_scalar_layouts
  declSlotData_scalar_layouts
  scalarTypeOf_tyOf_of_isSome
  localAllocsFrom_scalar_layouts
  MultiStartRel.localsOk
  steps_add_no_returnRel
  multi_reaches_rel
  multi_run_ret
  multi_run_ret_from_start
  multi_run_ub
  multi_run_ub_from_start
  CallStackRel.frames_ne_nil
  MultiStateRel.not_returnRel
  multi_run_ub_rel
  multi_run_ub_rel_from_start
  multi_steps_error
  multi_steps_error_from_start
  multi_mirNoUB_safe
  multi_mirNoUB_safe_from_start
  multi_steps_outcome
  multi_steps_outcome_from_start
  multi_steps_outcome_any_from_start
  multi_mirNoUB_progress
  multi_mirNoUB_progress_from_start
  multi_mirNoUB_progress_any_from_start
  multi_mirNoUB_diverges_steps_ok
  multi_mirNoUB_diverges_from_start
  multi_mirNoUB_diverges_rel_from_start
  mirCallWithCallees_ret
  mirCallWithCallees_ub
  mirCallWithCallees_ub_rel
  mirCallWithCallees_noUB
  mirCallWithCallees_steps_error
  mirCallWithCallees_progress
  mirCallWithCallees_progress_any
  mirCallWithCallees_outcome
  mirCallWithCallees_outcome_any
  mirCallWithCallees_diverges_steps_ok
  mirCallWithCallees_diverges_rel
  Shape.not_returnRel_of_ne_nil
  StateRel.not_returnRel
  step_correspondence
  step_start
  step_start_with_no_returnRel
  step_start_no_returnRel
  initMachineState_startRel
  steps_ok_mono
  reaches_rel
  reaches_rel_no_returnRel_N
  reaches_rel_no_returnRel
  run_ret
  run_ret_from_start
  run_ub
  run_ub_from_start
  run_ub_rel_N
  run_ub_rel
  run_ub_rel_from_start_N
  run_ub_rel_from_start
  steps_error
  steps_error_from_start
  steps_outcome
  steps_outcome_from_start
  mirNoUB_safe
  mirNoUB_safe_from_start
  mirNoUB_progress
  mirNoUB_progress_from_start
  mirNoUB_diverges_steps_ok
  mirNoUB_diverges_from_start
  mirNoUB_diverges_rel_from_start
  mirCall_ret
  mirCall_ub
  mirCall_ub_rel
  mirCall_noUB
  mirCall_progress
  mirCall_diverges_steps_ok
  mirCall_diverges_rel
  mirCall_steps_error
  mirCall_outcome
  stmtMustLive_mono
  iterLiveEntries_stabilizes
  livenessOk_eq_true
  liveAtEntry_greatest
  liveAtEntry_zero_mem
  dropMovedFrom_mono
  stmtTupleInit_mono
  termTupleInit_mono
  iterTupleInitEntries_stabilizes
  tupleInitOk_eq_true
  tupleInitAtEntry_greatest
  runA_sound
  runA_noUB
  faultsA_sound
  treeSafe_of_step_inv
  noRet_of_step_inv
  treeSafe_of_tau_inv
  noRet_of_tau_inv
  evalReturn_frame
  evalStatement_assign
  evalStatement_placeMention_place
  evalValue_operand
  evalValue_rvalue
  evalIntBinOp_spec
  evalIntBinOp_divExact
  evalUnOp_countOnes
  intBitAnd_one
  countOnesLoop_bounds
  evalStmt_assign
  evalStmt_placeMention
  evalStmt_placeMention_place
  evalOperand_frag
  tyProjTouchesUnion_false_of_all_nonUnion
  placeTouchesUnion_false_of_all_nonUnion
  placeTouchesUnion_false_of_tupleTypeOf
  placeTouchesUnion_false_of_tuplePlaceSpec
  placeTouchesUnion_false_of_placeOk
  placeTouchesUnion_false_of_inFragment
  evalRvalue_frag
  evalScalarBinOp_frag
  signedOverflowAdd_eq
  signedOverflowSub_eq
  signedOverflowMul_eq
  evalSignedDiv_spec
  evalSignedRem_spec
  shift_offset_eq
  unchecked_shift_oob_iff
  shiftLeftBits_intFromBits
  shiftRightUnsigned_intFromBits
  arithmeticShrBits_intFromBits
  bitwiseAndBits_intFromBits
  bitwiseOrBits_intFromBits
  bitwiseXorBits_intFromBits
  rvalueOk_binaryOp
  castBits_eq_toNat
  switch_lookup
  translateFn_spec
  translateFn_start
  evalValue_operandT
  evalValue_rvalueB
  evalStatement_assign_of
  evalStatement_assignB
  evalOperand_fragT
  evalRvalue_fragB
  evalStmt_assign_of
  evalStmt_assignB
  evalScalarBinOp_rel_int
  evalScalarBinOp_rel_bool
  signedLt_eq
  signedLe_eq
  evalUnaryNot_bool
  evalBinOp_rel_frag
  evalValue_boolNot
  evalValue_boolToU8
  evalValue_boolBitOp
  translateRvalue_cast_bool
  translateRvalue_boolBit
  evalScalarBinOp_boolBit
  switch_spec
  typedLoad_local_bool
  typedLoad_local_bool_uninit
  typedStore_local_bool
  typedStore_base_frag
  opBits_valid
  operandIsSigned_of_OperandOkT
  typedLoad_local_byte
  typedLoad_local_byte_uninit
  typedStore_local_byte
  typedStore_base_byte
  validBits_ordering
  decode_ordering
  checkValue_ordering
  encode_ordering
  evalUnOp_transmute_ordering
  evalBinOp_cmp_frag
  evalValue_translateCmp
  translateRvalue_cmp
  operandType_of_operandIsOrdering
  operandOkO_T
  evalValue_rvalueO
  evalStatement_assignO
  evalScalarBinOp_cmp_int
  evalScalarBinOp_cmp_bool
  evalRvalue_fragO
  evalStmt_assignO
  translateOperand_ordering_const
  scalarTypeOf_cases
  head_size_and_align_tuple
  layout_tuple
  withOverflow_eq
  checkValue_tuple
  encode_tuple
  decode_tuple
  decode_tuple_uninit
  typedLoad_local_tuple
  typedLoad_local_tuple_uninit
  typedStore_local_tuple
  typedLoad_local_localTy
  typedLoad_local_localTy_uninit
  evalPlace_field0L
  evalPlace_field1L
  typedLoad_local_tuple_field0
  typedLoad_local_tuple_field0_uninit
  typedLoad_local_tuple_field1
  typedLoad_local_tuple_field1_uninit
  evalBinOp_intWithOverflow
  translateRvalue_checked
  translateRvalue_tuple_agg
  evalValue_operandTuple
  evalValue_rvalueTuple
  evalStatement_assignTuple
  typedStore_base_tuple
  typedStore_base_localTy
  evalOperand_fragTuple
  evalScalarBinOp_checked
  evalRvalue_fragTuple
  evalStmt_assignTuple
  inFragment_spec
  storageDeadOk_spec
  mentionsOk_stmt
  mentionsOk_term
  foldl_moveOut_mem
  movedBefore_zero
  movedBefore_succ
  lookupSwitchTarget_mem
  unionLocals_mem
  stepMovedEntries_spec
  iterMovedEntries_fixed
  iterMovedEntries_mono
  iterMovedEntries_eq_of_fixed
  terminatorOk_targets_lt
  movesOk_of_fixed
  unionLocals_eq_or_mem_new
  stepMovedEntries_eq_or_strict
  iterMovedEntries_stabilizes
  statementOk_stmtMoved_lt
  terminatorOk_termMoved_lt
  movesOk_iff_blockMovesOk
  stmtMoved_mono
  termMoved_mono
  stepMovedEntries_least
  iterMovedEntries_least
  movedAtEntry_least
  blockMovesOk_spec
  movesOk_spec
  readsOk_mono
  stmtReadsOk_antitone
  termReadsOk_antitone
  blockMovesOk_antitone
  movesOk_of_preFixedPoint
  movesOk_iff_exists_preFixedPoint
  opsPost_get
  StaleOk.agree
  StaleOk.dead_iff
  StaleOk.slots
  StaleOk.readsAgree
  StaleOk.toBlock
  StaleOk.toBlockMove
  StaleOk.assign
  StaleOk.setBoth
  StaleOk.keep
  StateRelAt.advanceN
  StateRelAt.jumpN
  StartRel.localsOk
  initLocalsAux_spec
  steps_add
  moveKind_of_rvalueOk
  moveKind_of_rvalueOkB
  moveKind_of_rvalueOkO
  moveKind_of_rvalueOkTuple
  evalOperand_move
  evalOperand_copy_frame
  evalOperands_move
  evalRvalue_move
  evalRvalue_copy_locals
  evalStmt_assign_move
  evalScalarBinOp_locals
  evalUnaryNot_locals
  readsOk_spec
  opBits_frame
  rvBits_frame
  rvBitsB_frame
  rvBitsO_frame
  rvTupleBits_frame
  evalStmt_storageLive_disable
  evalStmt_storageLive_protected
  evalStmt_storageLive
  evalStmt_storageDead_disable
  evalStmt_storageDead_protected
  evalStmt_storageDead
  evalStmt_deinit
  evalStmt_placeMention_dead
  evalStatement_storageLive
  evalStatement_storageLive_init
  evalStatement_storageDead
  evalStatement_deinit
  evalStatement_assign_dead
  storageDead_some
  storageDead_none
  storageDead_none'
  BM_allocate_local
  BM_allocate_local_cand
  BM_allocate_local_cand_ns
  LocalsOkA.free_candidate_cand_ns
  localDeclOk_of_scalar
  NonScalarLive.of_scalar
  evalStatement_storageLive_cand
  evalStatement_storageLive_cand_ns
  evalStatement_storageLive_init_cand
  evalStatement_storageLive_init_cand_ns
  firstFitAddr_spec
  allocAddrOk_cand
  overlaps_low
  overlaps_cand
  LocalsOkA.free_candidate
  LocalsOkA.alloc'
  LocalsOkA.alloc
  LocalsOk.killLocal
  LocalsOk.forget
  LocalsOkA.teardown
  deallocAll_gen
  killAt_append_dead
  step_initBlock
  evalReturn_callee
  evalStatement_assign_array
  evalStatement_assign_index
  evalStatement_assign_tuple
  evalStatement_assign_field_scalar
  evalValue_specOperand
  evalValue_arrayRvalue
  evalValue_tupleRvalue
  evalPlace_proj
  evalPlace_fieldPath
  evalPlace_tuplePlace
  typedLoad_array_local
  typedLoad_array_elem
  typedLoad_tuple_slice
  typedStore_array_local
  typedStore_array_elem
  typedStore_tuple_slice
  decode_tupleSpec
  encode_tupleSpec
  checkValue_tupleSpec
  evalStmt_assign_array
  evalStmt_assign_index
  evalStmt_assign_tuple
  evalStmt_assign_field_scalar
  evalRvalue_array_frag
  evalRvalue_tuple_frag
  readProjectedValue_proj
  writeProjectedValue_proj
  resolveFieldPath_read
  resolveFieldPath_write
  step_correspondence_N
  step_start_N
  initMachineState_nonScalar
  reaches_rel_N
  run_ret_N
  run_ub_N
  steps_error_N
  steps_outcome_N
  steps_outcome_N_from_start
  mirNoUB_safe_N
  mirNoUB_progress_N
  mirNoUB_progress_N_from_start
  mirNoUB_diverges_steps_ok_N
  mirNoUB_diverges_rel_N_from_start
  mirCall_progress_N
  mirCall_outcome_N
  mirCall_diverges_rel_N
  nodup_map_localName
  nodup_map_fnName
  translateLocals_names
  SegChain.head_regular
  stmtCfgWf_of_translateStatement
  splitStmts_cfgWf
  termCfgWf_of_translateTerminator
  translateBlocksInProg_cfgWf
  translateFnInProg_funcCfgWf_core
  translateFnInProg_funcCfgWf
  translateFn_funcCfgWf
  mkStartFn_funcCfgWf
  translateProgFns_names_and_mem
  translateProg_progWf
  translateTy_eq_none_of_not_isMonoRigidTy
  derefPointeeTy_eq_none_of_not_isMonoRigidTy
  translateTy_container_param
  translateTy_container_alias
  isBorrowDescendantOrSelfAux_mono
  isBorrowDescendantOrSelfAux_of_lookup_sub
  isBorrowDescendantOrSelf_of_lookup_sub
  isBorrowDescendantOrSelf_map_eq
  isBorrowDescendantOrSelf_cons_child

open MiniRustSpec.Correspondence.Witness in
#assert_standard_axioms
  callerCallee_inFragment
  calleePair_initLen
  callerCallee_translate
  callerMain_translateInProg
  ctxCallerMain_ok
  callerCallee20_anneal_ret
  callerCallee20_noUB
  callerCallee20_progress
  callerCallee20_progress_any
  callerCallee20_outcome_any
  callerCallee20_minirust_ret
  callerCallee20_midCall_step5
  callerCallee20_minirust_direct
  callerCalleeOv_anneal_ret
  callerCalleeOv_noUB
  callerCalleeOv_minirust_ret
  callerCalleeOv_minirust_direct
  projDestCaller_inFragment
  ctxProjDest_ok
  projDest_translate
  projDestCaller_translateInProg
  projDest127_anneal_ret
  projDest127_noUB
  projDest127_minirust_ret
  projDest127_minirust_direct
  chain3_inFragment
  chain3_maxStackLocals
  ctxChainEntry_ok
  chain3_translate
  chainEntry_translateInProg
  chainNeg5_anneal_ret
  chainNeg5_noUB
  chainNeg5_minirust_ret
  chainNeg5_depth4_step7
  chainNeg5_minirust_direct
  callArgUb_inFragment
  ctxCallArgUb_ok
  callArgUb_translate
  callArgUbCaller_translateInProg
  callArgUb_anneal_ub
  callArgUb_minirust_ub
  callArgUb_minirust_direct
  callArgUb_converse_error
  callArgUb_outcome
  calleeDivZero_inFragment
  ctxCalleeDivZero_ok
  calleeDivZero_translate
  calleeDivZeroCaller_translateInProg
  calleeDivZero_anneal_ub
  calleeDivZero_minirust_ub
  calleeDivZero_minirust_direct
  calleeDivZero_converse_error
  callSpin_inFragment
  ctxCallSpin_ok
  callSpin_translate
  callSpinCaller_translateInProg
  callSpin_noUB
  callSpin_noRet
  callSpin_minirust_diverges
  callSpin_minirust_diverges_rel
  callDestArgAlias_movesOk
  callDestArgAlias_rejected
  callDestArgAlias_translate
  callDestArgAlias_anneal_ret
  callDestArgAlias_minirust_ub
  callProjMoveReuse_rejected
  callProjMoveReuse_translate
  callProjMoveReuse_anneal_ret
  callProjMoveReuse_minirust_ub
  callMoveReuse_inFragment
  callMoveReuse_anneal_ub
  callMoveReuse_translate
  callMoveReuse_translateInProg
  ctxCallMoveReuse_ok
  callMoveReuse_minirust_ub
  callMoveReuse_minirust_direct
  callMoveReuse_converse_error
  moveReinitByCall_inFragment
  moveReinitByCall_translate
  moveReinitByCall_translateInProg
  ctxMoveReinitByCall_ok
  moveReinitByCall_anneal_ret
  moveReinitByCall_minirust_ret
  moveReinitByCall_minirust_direct
  condCallMoveJoin_inFragment
  condCallMoveJoin_translate
  condCallMoveJoin_translateInProg
  ctxCondCallMoveJoin_ok
  condCallMoveJoin1_anneal_ret
  condCallMoveJoin1_minirust_ret
  condCallMoveJoin0_anneal_ret
  condCallMoveJoin0_minirust_ret
  condCallMoveJoin_minirust_direct
  stmtMoveThenCallArg_movesOk
  stmtMoveThenCallArg_rejected
  recCycle_maxStackLocals
  recCycle_rejected
  layout_ptr_and_array_mr41
  evalConstant_and_fnFromPtr_mr41
  checkAbiCompatibility_all_variants_mr41
  createFrame_ub_mr41
  evalReturn_missingNextBlock_and_bottomOfStack_ub
  cAbiCallee_conv
  cAbi_inFragment
  cAbi_translate
  cAbiCaller_translateInProg
  ctxCAbiCaller_ok
  cAbi32_anneal_ret
  cAbi32_noUB
  cAbi32_minirust_ret
  cAbi32_minirust_direct
  badCallConv_rejected
  deadCallDest_rejected
  deadCallDest_translate
  deadCallDest_anneal_ub
  deadCallDest_minirust_ub_before_callee
  uninitProjCallDest_rejected
  uninitProjCallDest_translate
  uninitProjCallDest_anneal_ret
  uninitProjCallDest_minirust_ret
  diamondCall_inFragment
  diamondCall_maxStackLocals
  ctxDiamondCall_ok
  diamondCall_translate
  diamondCallEntry_translateInProg
  diamondCall5_anneal_ret
  diamondCall5_noUB
  diamondCall5_minirust_ret
  diamondCall5_minirust_direct
  no_returnRel_before
  never_ub_of_nonUb_stop
  callDestArgAlias_noUB
  callDestArgAlias_noUB_transfer_fails
  callProjMoveReuse_noUB
  callProjMoveReuse_noUB_transfer_fails
  uninitProjCallDest_agreement
  liveCallDestSpin_inFragment
  liveCallDestSpin_translate
  liveCallDestSpin_translateInProg
  ctxLiveCallDestSpin_ok
  liveCallDestSpin_noUB
  liveCallDestSpin_noRet
  liveCallDestSpin_minirust_diverges
  liveCallDestSpin_minirust_diverges_rel
  liveCallDestSpin_depth3_step20
  deadCallDestSpin_rejected
  ctxDeadCallDestSpin_ok
  deadCallDestSpin_hyps
  deadCallDestSpin_noUB
  deadCallDestSpin_noRet
  deadCallDestSpin_minirust_ub
  deadCallDestSpin_noUB_transfer_fails
  abiArgMismatch_rejected
  abiArgMismatch_translate
  abiArgMismatch_anneal_ret
  abiArgMismatch_noUB
  abiArgMismatch_minirust_ub
  abiArgMismatch_noUB_transfer_fails
  abiRetMismatch_rejected
  abiRetMismatch_translate
  abiRetMismatch_anneal_ret
  abiRetMismatch_noUB
  abiRetMismatch_minirust_ub
  abiRetMismatch_noUB_transfer_fails
  argCountMismatch_rejected
  argCountMismatch_translate
  argCountMismatch_anneal_ret
  argCountMismatch_noUB
  argCountMismatch_minirust_ub
  argCountMismatch_noUB_transfer_fails
  stmtMoveThenCallArg_translate
  stmtMoveThenCallArg_anneal_ub
  stmtMoveThenCallArg_minirust_ret
  stmtMoveThenCallArg_ub_transfer_fails
  calleeRetUninit_inFragment
  calleeRetUninit_translate
  calleeRetUninit_translateInProg
  ctxCalleeRetUninit_ok
  calleeRetUninit_anneal_ub
  calleeRetUninit_minirust_ub
  calleeRetUninit_minirust_ub_rel
  calleeRetUninit_minirust_direct
  calleeRetUninit_converse_error
  retUninit_minirust_ub_rel_from_start
  negMention0_minirust_ub_rel_from_start
  calleeDivZero_minirust_ub_rel
  callArgUb_minirust_ub_rel
  callMoveReuse_minirust_ub_rel
  projDestCaller_liveness_stabilizes
  projDestCaller_tupleInit_stabilizes
  projDestCaller_liveAtEntry_greatest
  projDestCaller_tupleInitAtEntry_greatest
  progStart_outside_fragment
  ctx0_ok1
  ctx0_ok2
  ctxI8_ok2
  ctx0_ok_u32_i8
  ctxI8_ok3
  ctxI8_ok_hetero
  spinLoop_step_self
  branchSpinLoop1_step_self
  sumTo_inFragment
  sumTo_translate
  sumTo_init_step
  sumTo_rel
  sumTo_anneal_ret
  sumTo_noUB
  sumTo_minirust_ret
  sumTo_minirust_direct
  sumTo_minirust_ret_from_start
  sumTo_minirust_direct_from_start
  retUninit_inFragment
  retUninit_translate
  retUninit_rel
  retUninit_anneal_ub
  retUninit_minirust_ub
  retUninit_minirust_direct
  retUninit_minirust_ub_from_start
  negMention_inFragment
  negMention_translate
  negMention5_startRel
  negMention5_anneal_ret
  negMention5_minirust_ret_from_start
  negMention5_minirust_direct
  negMention0_startRel
  negMention0_anneal_ub
  negMention0_minirust_ub_from_start
  negMention0_minirust_direct
  signedEdge_inFragment
  signedEdge_translate
  signedEdgeMin_anneal_ret
  signedEdgeMin_noUB
  signedEdgeMin_minirust_ret_from_start
  signedEdgeMin_minirust_noUB
  signedEdgeMin_minirust_direct
  signedEdgeOne_anneal_ret
  signedEdgeOne_minirust_ret_from_start
  signedEdgeOne_minirust_direct
  castBitNot_inFragment
  castBitNot_translate
  castBitNot4_anneal_ret
  castBitNot4_noUB
  castBitNot4_minirust_ret_from_start
  castBitNot4_minirust_direct
  spinLoop_inFragment
  spinLoop_translate
  spinLoop_noUB
  spinLoop_diverges
  spinLoop_minirust_steps_ok
  spinLoop_minirust_diverges_rel
  divRemI8_inFragment
  divRemI8_translate
  divRemNeg7_anneal_ret
  divRemNeg7_noUB
  divRemNeg7_minirust_ret_from_start
  divRemNeg7_minirust_direct
  divRemMinOne_anneal_ret
  divRemMinOne_minirust_ret_from_start
  divRemMinOne_minirust_direct
  divByZero_anneal_ub
  divByZero_minirust_ub_from_start
  divByZero_minirust_direct
  divByZero_converse_error
  divMinNeg1_anneal_ub
  divMinNeg1_minirust_ub_from_start
  divMinNeg1_minirust_direct
  remOnlyI8_inFragment
  remOnlyI8_translate
  remByZero_anneal_ub
  remByZero_minirust_ub_from_start
  remByZero_minirust_direct
  remMinNeg1_anneal_ub
  remMinNeg1_minirust_ub_from_start
  remMinNeg1_minirust_direct
  uncheckedArithI8_inFragment
  uncheckedArithI8_translate
  uncheckedOk_anneal_ret
  uncheckedOk_noUB
  uncheckedOk_minirust_ret_from_start
  uncheckedOk_minirust_direct
  uncheckedMulUb_anneal_ub
  uncheckedMulUb_minirust_ub_from_start
  uncheckedMulUb_minirust_direct
  uncheckedSubUb_anneal_ub
  uncheckedSubUb_minirust_ub_from_start
  uncheckedSubUb_minirust_direct
  uncheckedAddUb_anneal_ub
  uncheckedAddUb_minirust_ub_from_start
  uncheckedAddUb_minirust_direct
  uncheckedAddUb_outcome
  branchSpinLoop_inFragment
  branchSpinLoop_translate
  branchSpinLoop1_noUB
  branchSpinLoop1_diverges
  branchSpinLoop1_minirust_diverges_rel
  shiftI8_inFragment
  shiftI8_translate
  shiftOk_anneal_ret
  shiftOk_noUB
  shiftOk_minirust_ret_from_start
  shiftOk_minirust_direct
  shrUncheckedGe8Ub_anneal_ub
  shrUncheckedGe8Ub_minirust_ub_from_start
  shrUncheckedGe8Ub_minirust_direct
  shrUncheckedNegUb_anneal_ub
  shrUncheckedNegUb_minirust_ub_from_start
  shrUncheckedNegUb_minirust_direct
  shlUncheckedI8_inFragment
  shlUncheckedI8_translate
  shlUncheckedGe8Ub_anneal_ub
  shlUncheckedGe8Ub_minirust_ub_from_start
  shlUncheckedGe8Ub_minirust_direct
  shlUncheckedNegUb_anneal_ub
  shlUncheckedNegUb_minirust_ub_from_start
  shlUncheckedNegUb_minirust_direct
  bitwiseI8_inFragment
  bitwiseI8_translate
  bitwiseNeg_anneal_ret
  bitwiseNeg_noUB
  bitwiseNeg_minirust_ret_from_start
  bitwiseNeg_minirust_direct
  countOnes_neg86_i8
  countOnes_neg1_i8
  heteroShiftSwitch_inFragment
  heteroShiftSwitch_translate
  heteroShiftOk_anneal_ret
  heteroShiftOk_noUB
  heteroShiftOk_minirust_ret_from_start
  heteroShiftOk_minirust_direct
  heteroShrGe8Ub_anneal_ub
  heteroShrGe8Ub_minirust_ub_from_start
  heteroShrGe8Ub_minirust_direct
  heteroShrNegUb_anneal_ub
  heteroShrNegUb_minirust_ub_from_start
  heteroShrNegUb_minirust_direct
  divExact_ok_i8
  divExact_rem_ub_i8
  divExact_zero_ub_i8
  divExact_min_neg1_ub_i8
  uninitOperandUb_inFragment
  uninitOperandUb_translate
  uninitBinOpUb_anneal_ub
  uninitBinOpUb_minirust_ub_from_start
  uninitBinOpUb_minirust_direct
  uninitUnOpUb_anneal_ub
  uninitUnOpUb_minirust_ub_from_start
  uninitUnOpUb_minirust_direct
  uninitSwitchUb_anneal_ub
  uninitSwitchUb_minirust_ub_from_start
  uninitSwitchUb_minirust_direct
  uninitSwitchUb_converse_error
  ctxI8_ok_cmpNot
  cmpNotSwitch_inFragment
  cmpNotSwitch_translate
  cmpNotNeg1_anneal_ret
  cmpNotNeg1_noUB
  cmpNotNeg1_minirust_ret_from_start
  cmpNotNeg1_minirust_direct
  cmpNot3_anneal_ret
  cmpNot3_noUB
  cmpNot3_minirust_ret_from_start
  cmpNot3_minirust_direct
  ctxBool_ok
  ctxBool_ok1
  leNeGe_inFragment
  leNeGe_translate
  leNeGe250_anneal_ret
  leNeGe250_noUB
  leNeGe250_minirust_ret_from_start
  leNeGe250_minirust_direct
  leNeGe5_anneal_ret
  leNeGe5_noUB
  leNeGe5_minirust_ret_from_start
  leNeGe5_minirust_direct
  ctxI8_ok_boolCast
  boolCastI8_inFragment
  boolCastI8_translate
  boolCastInvalidArg_rejected
  boolCastTrue_anneal_ret
  boolCastTrue_noUB
  boolCastTrue_minirust_ret_from_start
  boolCastTrue_minirust_direct
  boolCastFalse_anneal_ret
  boolCastFalse_noUB
  boolCastFalse_minirust_ret_from_start
  boolCastFalse_minirust_direct
  uninitBool_inFragment
  uninitBool_translate
  uninitBool_anneal_ub
  uninitBool_minirust_ub_from_start
  uninitBool_minirust_direct
  uninitBoolNot_inFragment
  uninitBoolNot_translate
  uninitBoolNot_anneal_ub
  uninitBoolNot_minirust_ub_from_start
  uninitBoolNot_minirust_direct
  uninitBoolRel_inFragment
  uninitBoolRel_translate
  uninitBoolRel_anneal_ub
  uninitBoolRel_minirust_ub_from_start
  uninitBoolRel_minirust_direct
  ctxI8_ok_cmpSel
  cmpSel_inFragment
  cmpSel_translate
  cmpSelLess_anneal_ret
  cmpSelLess_noUB
  cmpSelLess_minirust_ret_from_start
  cmpSelLess_minirust_direct
  cmpSelEqual_anneal_ret
  cmpSelEqual_noUB
  cmpSelEqual_minirust_ret_from_start
  cmpSelEqual_minirust_direct
  cmpSelGreater_anneal_ret
  cmpSelGreater_noUB
  cmpSelGreater_minirust_ret_from_start
  cmpSelGreater_minirust_direct
  ctxBool_ok_ordering
  uninitOrdering_inFragment
  uninitOrdering_translate
  uninitOrdering_anneal_ub
  uninitOrdering_minirust_ub_from_start
  uninitOrdering_minirust_direct
  ctxI8_ok_boolBitOrdUse
  boolBitOrdUse_inFragment
  boolBitOrdUse_translate
  boolBitOrdInvalidTag_rejected
  boolBitOrdUseCmp_anneal_ret
  boolBitOrdUseCmp_noUB
  boolBitOrdUseCmp_minirust_ret_from_start
  boolBitOrdUseCmp_minirust_direct
  boolBitOrdUseCopy_anneal_ret
  boolBitOrdUseCopy_noUB
  boolBitOrdUseCopy_minirust_ret_from_start
  boolBitOrdUseCopy_minirust_direct
  uninitBoolBitAnd_inFragment
  uninitBoolBitAnd_translate
  uninitBoolBitAnd_anneal_ub
  uninitBoolBitAnd_minirust_ub_from_start
  uninitBoolBitAnd_minirust_direct
  uninitBoolBitOrRhs_inFragment
  uninitBoolBitOrRhs_translate
  uninitBoolBitOrRhs_anneal_ub
  uninitBoolBitOrRhs_minirust_ub_from_start
  uninitBoolBitOrRhs_minirust_direct
  relLt_signed
  relGt_unsigned
  relCmp_signed
  relCmp_unsigned
  relCmp_bool
  relLt_bool
  relGt_bool
  relLe_bool
  relGe_bool
  relEq_bool
  relNe_bool
  relGe_eq
  relNe_eq
  rel_mismatch
  transmute_bool_u8
  transmute_u8_bool
  transmute_u8_bool_invalid
  transmute_size_mismatch
  decode_bool_invalid
  bitNot_bool_panics
  ordering_validTags
  decode_ordering_less
  decode_ordering_invalid
  encode_ordering_greater
  checkValue_variant_invalid
  transmute_i8_ordering
  transmute_i8_ordering_invalid
  layout_paddedPair
  encode_paddedPair
  decode_paddedPair
  checkValue_tuple_arity
  decodeDiscriminant_short_circuits
  layout_slice
  layout_traitObject
  layout_unsizedTuple
  expectSize_unsized_panics
  expectAlign_traitObject_panics
  transmute_unsized_panics
  decode_unsized_panics
  encode_unsized_panics
  checkValue_unsized_panics
  layout_union
  decode_union
  encode_union
  checkValue_union_chunk_size
  checkValue_union_chunk_data
  transmute_union_paddedPair
  transmute_paddedPair_union
  transmute_union_paddedPair_uninit_ub
  ctxI8_ok_checkedArith
  checkedArithI8_inFragment
  checkedArithI8_translate
  checkedArithInvalidTupleArg_rejected
  checkedArithOk_anneal_ret
  checkedArithOk_noUB
  checkedArithOk_minirust_ret_from_start
  checkedArithOk_minirust_direct
  checkedArithAddOv_anneal_ret
  checkedArithAddOv_noUB
  checkedArithAddOv_minirust_ret_from_start
  checkedArithAddOv_minirust_direct
  checkedArithSubOv_anneal_ret
  checkedArithSubOv_noUB
  checkedArithSubOv_minirust_ret_from_start
  checkedArithSubOv_minirust_direct
  checkedArithMulOv_anneal_ret
  checkedArithMulOv_noUB
  checkedArithMulOv_minirust_ret_from_start
  checkedArithMulOv_minirust_direct
  ctxTupleU32_ok
  checkedTupleU32_inFragment
  checkedTupleU32_translate
  checkedTupleUnderAddOv_anneal_ret
  checkedTupleUnderAddOv_noUB
  checkedTupleUnderAddOv_minirust_ret_from_start
  checkedTupleUnderAddOv_minirust_direct
  checkedTupleMulOv_anneal_ret
  checkedTupleMulOv_noUB
  checkedTupleMulOv_minirust_ret_from_start
  checkedTupleMulOv_minirust_direct
  checkedTupleOk_anneal_ret
  checkedTupleOk_noUB
  checkedTupleOk_minirust_ret_from_start
  checkedTupleOk_minirust_direct
  ctxTupleU32_ok1
  uninitTupleField0_inFragment
  uninitTupleField0_translate
  uninitTupleField0_anneal_ub
  uninitTupleField0_minirust_ub_from_start
  uninitTupleField0_minirust_direct
  uninitTupleField0_converse_error
  uninitTupleField1_inFragment
  uninitTupleField1_translate
  uninitTupleField1_anneal_ub
  uninitTupleField1_minirust_ub_from_start
  uninitTupleField1_minirust_direct
  uninitTupleField1_outcome
  withOverflow_i8_layout
  withOverflow_u32_layout
  tupleHeadLayout_full_sized_and_slice
  cappedTailAlign_and_computeSizeAndAlign_all_branches
  evalBinOp_addWithOverflow_i8_max
  evalBinOp_subWithOverflow_i8_min
  evalBinOp_addWithOverflow_u32_max
  evalBinOp_subWithOverflow_u32_zero
  evalBinOp_mulWithOverflow_i8_min
  evalBinOp_mulWithOverflow_u32
  ptrOffsetInbounds_ok_and_oob
  evalValue_tuple_and_evalPlace_field
  evalBinOp_intWithOverflow_nonInt_panics
  evalPlace_field_panics
  evalBinOp_withOverflow_all_widths
  evalPlace_field_union_and_offset_panic
  tempMove_inFragment
  tempMove_alwaysLive
  tempMove_translate
  ctx0_ok_tempMove
  tempMove_initLen
  tempMove3_anneal_ret
  tempMove3_noUB
  tempMove3_progress
  tempMove3_minirust_ret_from_start
  tempMove3_minirust_direct
  tempMove2_anneal_ret
  tempMove2_noUB
  tempMove2_minirust_ret_from_start
  tempMove2_minirust_direct
  deadRead_inFragment
  deadRead_translate
  deadRead_anneal_ub
  deadRead_minirust_ub_from_start
  deadRead_minirust_direct
  deadRead_steps5_ub
  deadRead_converse_error
  deadRead_outcome
  moveReuse_movesOk
  moveReuse_not_inFragment
  moveReuse_translate
  moveReuse7_anneal_ub
  moveReuse7_minirust_direct
  crossBlockMove_inFragment
  crossBlockMove_movedAtEntry
  crossBlockMove_translate
  ctx0_ok_crossBlockMove
  crossBlockMove20_anneal_ret
  crossBlockMove20_noUB
  crossBlockMove20_progress
  crossBlockMove20_minirust_ret_from_start
  crossBlockMove20_minirust_direct
  crossBlockMoveOv_anneal_ret
  crossBlockMoveOv_noUB
  crossBlockMoveOv_progress
  crossBlockMoveOv_minirust_ret_from_start
  crossBlockMoveOv_minirust_direct
  crossBlockMoveReuse_movesOk
  unmarkedTempAssign_rejected
  unmarkedTempAssign_translate
  unmarkedTempAssign_anneal_ub
  unmarkedTempAssign_minirust_direct
  bm_allocate_and_deallocate_ub_cases
  evalStatement_deinit_ok_dead_and_misaligned
  loopTempMove_inFragment
  loopTempMove_alwaysLive
  loopTempMove_initLen
  loopTempMove_movedAtEntry_multiPass
  loopTempMove_translate
  ctx0_ok_loopTempMove
  loopTempMove3_anneal_ret
  loopTempMove3_noUB
  loopTempMove3_progress
  loopTempMove3_minirust_ret_from_start
  loopTempMove3_minirust_direct
  loopTempMove0_anneal_ret
  loopTempMove0_noUB
  loopTempMove0_progress
  loopTempMove0_minirust_ret_from_start
  loopTempMove0_minirust_direct
  loopBackEdgeReuse_movesOk
  loopBackEdgeReuse_translate
  loopBackEdgeReuse1_anneal_ub
  loopBackEdgeReuse1_minirust_direct
  deadAssign_inFragment
  deadAssign_translate
  deadAssign_anneal_ub
  deadAssign_minirust_ub_from_start
  deadAssign_minirust_direct
  deadAssign_steps4_ub
  deadAssign_converse_error
  deadAssign_outcome
  deadDeinit_inFragment
  deadDeinit_translate
  deadDeinit_anneal_ub
  deadDeinit_minirust_ub_from_start
  deadDeinit_minirust_direct
  deadDeinit_steps5_ub
  deadDeinit_converse_error
  deadDeinit_outcome
  ctx0_ok_u32_tuple
  deadPlaceMention_inFragment
  deadPlaceMention_translate
  deadPlaceMention_anneal_ub
  deadPlaceMention_minirust_ub_from_start
  deadPlaceMention_minirust_direct
  deadPlaceMention_steps4_ub
  deadPlaceMention_converse_error
  deadPlaceMention_outcome
  storageDeadRet_rejected
  storageDeadRet_translate
  storageDeadRet_anneal_ub
  storageDeadRet_minirust_panics
  projectedDeinit_rejected
  projectedDeinit_translate
  projectedDeinit_anneal_ub
  projectedDeinit_minirust_ub
  projAssignMoveReuse_movesOk
  sameRvalueMoveReuse_movesOk
  sameRvalueMoveReuse_translate
  sameRvalueMoveReuse5_anneal_ub
  sameRvalueMoveReuse5_minirust_direct
  moveRetPlace_movesOk
  moveRetPlace_translate
  moveRetPlace_anneal_ub
  moveRetPlace_minirust_direct
  storageLiveArgRet_inFragment
  storageLiveArgRet_translate
  ctx0_ok_u32_3
  storageLiveArgRet5_anneal_ret
  storageLiveArgRet5_noUB
  storageLiveArgRet5_progress
  storageLiveArgRet5_minirust_ret_from_start
  storageLiveArgRet5_minirust_direct
  storageDeadArg_rejected
  storageDeadArg_translate
  storageDeadArg5_anneal_ret
  storageDeadArg5_minirust_direct
  storageDeadArgReadAfter_rejected
  storageDeadArgReadAfter_translate
  storageDeadArgReadAfter5_anneal_ub
  storageDeadArgReadAfter5_minirust_ub
  ctx0_2_ok_bool_u32
  diamondMoveJoin_inFragment
  diamondMoveJoin_movedAtEntry
  diamondMoveJoin_translate
  diamondMoveJoinTrue_anneal_ret
  diamondMoveJoinTrue_noUB
  diamondMoveJoinTrue_progress
  diamondMoveJoinTrue_minirust_ret_from_start
  diamondMoveJoinTrue_minirust_direct
  diamondMoveJoinFalse_anneal_ret
  diamondMoveJoinFalse_noUB
  diamondMoveJoinFalse_progress
  diamondMoveJoinFalse_minirust_ret_from_start
  diamondMoveJoinFalse_minirust_direct
  diamondHalfMoveReuse_movesOk
  diamondHalfMoveReuse_translate
  diamondHalfMoveReuseFalse_anneal_ub
  diamondHalfMoveReuseFalse_minirust_direct
  ctx0_ok_tupleAggCastMove
  tupleAggCastMove_inFragment
  tupleAggCastMove_translate
  tupleAggCastMoveNeg5_anneal_ret
  tupleAggCastMoveNeg5_noUB
  tupleAggCastMoveNeg5_progress
  tupleAggCastMoveNeg5_minirust_ret_from_start
  tupleAggCastMoveNeg5_minirust_direct
  projFieldMoveReuse_movesOk
  projFieldMoveReuse_translate
  projFieldMoveReuse_anneal_ub
  projFieldMoveReuse_minirust_direct
  ctx0_ok_trailing_temp_addrs
  ctxI8_ok_ordBoolCastTempMove
  ordBoolCastTempMove_inFragment
  ordBoolCastTempMove_movedAtEntry
  ordBoolCastTempMove_movesOk_by_preFixedPoint
  ordBoolCastTempMove_translate
  ordBoolCastTempMoveTrue_anneal_ret
  ordBoolCastTempMoveTrue_noUB
  ordBoolCastTempMoveTrue_progress
  ordBoolCastTempMoveTrue_minirust_ret_from_start
  ordBoolCastTempMoveTrue_minirust_direct
  ordBoolCastTempMoveFalse_anneal_ret
  ordBoolCastTempMoveFalse_noUB
  ordBoolCastTempMoveFalse_progress
  ordBoolCastTempMoveFalse_minirust_ret_from_start
  ordBoolCastTempMoveFalse_minirust_direct
  ctxI8_ok_arrayOps
  ctxI8_ok_arraySignedIdx
  ctxI8_ok_zeroArray
  arrayOpsI8_inFragment
  arrayOpsI8_translate
  arrayOpsOk_anneal_ret
  arrayOpsOk_noUB
  arrayOpsOk_minirust_ret_from_start
  arrayOpsOk_minirust_direct
  arrayOpsOob_anneal_ub
  arrayOpsOob_minirust_ub_from_start
  arrayOpsOob_minirust_direct
  arrayOpsOob_converse_error
  arraySignedIdxI8_inFragment
  arraySignedIdxI8_translate
  arraySignedIdxOk_anneal_ret
  arraySignedIdxOk_minirust_ret_from_start
  arraySignedIdxOk_minirust_direct
  arraySignedNegUb_anneal_ub
  arraySignedNegUb_minirust_ub_from_start
  arraySignedNegUb_minirust_direct
  arraySignedOobUb_anneal_ub
  arraySignedOobUb_minirust_ub_from_start
  arraySignedOobUb_minirust_direct
  zeroArrayI8_inFragment
  zeroArrayI8_translate
  zeroArrayOk_anneal_ret
  zeroArrayOk_noUB
  zeroArrayOk_minirust_ret_from_start
  zeroArrayOk_minirust_direct
  zeroArrayIdxUb_anneal_ub
  zeroArrayIdxUb_minirust_ub_from_start
  zeroArrayIdxUb_minirust_direct
  arrayOpsOk_minirust_inplace_bytes
  arrayOpsOk_minirust_ret_dealloc
  ctxI8_ok_arrayUninitIdx
  arrayUninitIdxI8_inFragment
  arrayUninitIdxI8_translate
  arrayUninitIdx_anneal_ub
  arrayUninitIdx_minirust_ub_from_start
  arrayUninitIdx_minirust_direct
  ctxU32_ok_arrayU32Idx
  arrayU32Idx_inFragment
  arrayU32Idx_translate
  arrayU32IdxOk_anneal_ret
  arrayU32IdxOk_noUB
  arrayU32IdxOk_minirust_ret_from_start
  arrayU32IdxOk_minirust_direct
  arrayU32IdxOk_minirust_inplace_bytes
  arrayU32IdxOob_anneal_ub
  arrayU32IdxOob_minirust_ub_from_start
  arrayU32IdxOob_minirust_direct
  arrayConstIdxOobI8_inFragment
  arrayConstIdxOobI8_translate
  arrayConstIdxOob_anneal_ub
  arrayConstIdxOob_minirust_ub_from_start
  arrayConstIdxOob_minirust_direct
  sizeMulInt_zero_neg
  array_encode_decode_edge_cases
  ctxI8_ok_arrayCompose
  arrayComposeI8_inFragment
  arrayComposeI8_translate
  arrayComposeOk_anneal_ret
  arrayComposeOk_noUB
  arrayComposeOk_minirust_ret_from_start
  arrayComposeOk_minirust_direct
  arrayComposeAggUb_anneal_ub
  arrayComposeAggUb_minirust_ub_from_start
  arrayComposeAggUb_minirust_direct
  arrayComposeRepeatUb_anneal_ub
  arrayComposeRepeatUb_minirust_ub_from_start
  arrayComposeRepeatUb_minirust_direct
  arrayComposeRhsUb_anneal_ub
  arrayComposeRhsUb_minirust_ub_from_start
  arrayComposeRhsUb_minirust_direct
  arrayComposeBothUb_anneal_ub
  arrayComposeBothUb_minirust_ub_from_start
  arrayComposeBothUb_minirust_direct
  arrayComposeSwitchOobUb_anneal_ub
  arrayComposeSwitchOobUb_minirust_ub_from_start
  arrayComposeSwitchOobUb_minirust_direct
  ctxPadded3_ok
  paddedStructOps_inFragment
  paddedStructOps_translate
  paddedStructOk_anneal_ret
  paddedStructOk_noUB
  paddedStructOk_minirust_ret_from_start
  paddedStructOk_minirust_direct
  paddedStructOk_minirust_padding_bytes
  paddedStructOk_minirust_ret_dealloc
  paddedStructOk_minirust_noUB
  paddedStructOk_minirust_progress
  ctxNested5_ok
  nestedTupleOps_inFragment
  nestedTupleOps_translate
  nestedTupleOk_anneal_ret
  nestedTupleOk_noUB
  nestedTupleOk_minirust_ret_from_start
  nestedTupleOk_minirust_direct
  nestedTupleOk_minirust_padding_bytes
  nestedTupleOk_minirust_ret_dealloc
  nestedTupleOk_minirust_noUB
  nestedTupleOk_minirust_progress
  nestedTupleAggUb_anneal_ub
  nestedTupleAggUb_minirust_ub_from_start
  nestedTupleAggUb_minirust_direct
  nestedTupleAggUb_converse_error
  nestedTupleFieldRhsUb_anneal_ub
  nestedTupleFieldRhsUb_minirust_ub_from_start
  nestedTupleFieldRhsUb_minirust_direct
  nestedTupleFieldRhsUb_converse_error
  nestedTupleCopyUninitUb_anneal_ub
  nestedTupleCopyUninitUb_minirust_ub_from_start
  nestedTupleCopyUninitUb_minirust_direct
  nestedTupleCopyUninitUb_converse_error
  tuple_encode_decode_place_edge_cases
  evalIntrinsic_abort_exit
  evalIntrinsic_assume
  evalIntrinsic_print
  evalIntrinsic_rawEq_withExposed
  evalIntrinsic_rawEq
  evalIntrinsic_allocate_deallocate_leak
  evalIntrinsic_exposeProvenance
  evalIntrinsic_getUnwindPayload_empty
  evalTerminator_abortTerminator
  translateRsIntrinsic_witness
  assumeSub_translate
  assumeSub_translateInProg
  assumeSub_inFragment
  ctxAssumeSub_ok
  runsToScalar_sound
  assumeSub20_anneal_ret
  assumeSub20_minirust_ret
  assumeSub20_minirust_direct
  assumeSub20_split_point
  assumeSubFalse_anneal_ub
  assumeSubFalse_minirust_ub_rel
  assumeSubFalse_ub
  assumeTupleCall_inFragment
  assumeTupleCall_translate
  assumeTupleCall_translateInProg
  ctxAssumeTupleCall_ok
  assumeTupleCall10_anneal_ret
  assumeTupleCall10_minirust_ret
  assumeTupleCallOv_anneal_ub
  assumeTupleCallOv_minirust_ub_rel
  assumeDeadLocal_inFragment
  assumeDeadLocal_translate
  assumeDeadLocal_translateInProg
  ctxAssumeDeadLocal_ok
  assumeDeadLocal_anneal_ub
  assumeDeadLocal_minirust_ub_rel
  assumeMultiFrame_inFragment
  assumeMultiFrame_translate
  assumeMultiFrame_translateInProg
  assumeChainCallee_translateInProg
  assumeMultiFrame_prog_wf
  assumeMultiFrame_func_wf_caller
  assumeMultiFrame_func_wf_callee
  ctxAssumeMultiFrame_ok
  assumeMultiFrame5_anneal_ret
  assumeMultiFrame5_minirust_ret
  assumeMultiFramePreUb_anneal_ub
  assumeMultiFramePreUb_minirust_ub_rel
  assumeMultiFrameCalleeSeg2Ub_anneal_ub
  assumeMultiFrameCalleeSeg2Ub_minirust_ub_rel
  assumeMultiFramePostUb_anneal_ub
  assumeMultiFramePostUb_minirust_ub_rel
  assumeMoveReuse_rejected
  assumeMoveReuse_diverges
  assumeAfterMove_rejected
  assumeAfterMove_diverges
  itOf_uint
  tyOf_uint

#assert_standard_axioms
  MiniRustSpec.Anchors.anchors_ok
  MiniRustSpec.Anchors.anchors_nodup

#check_theorem_deps "[ANCHOR-AUDIT]"
  MiniRustSpec.Anchors.anchors_ok
  MiniRustSpec.Anchors.anchors_nodup

open MiniRustSpec.Correspondence in
#check_theorem_deps "[SIMULATION-AUDIT]"
  unitPlace_eq_buildUnitPlace
  tyProjTouchesUnion_false_of_all_nonUnion
  placeTouchesUnion_false_of_all_nonUnion
  placeTouchesUnion_false_of_tupleTypeOf
  placeTouchesUnion_false_of_tuplePlaceSpec
  placeTouchesUnion_false_of_placeOk
  placeTouchesUnion_false_of_inFragment
  abortTerminator_eq_buildAbort
  unitType_eq_unitTy
  mapGet_eq_of_mem_nodup
  isAssume_iff
  translateStmtResult_some
  splitStmts_names
  translateTerminatorInProg_names
  nodup_map_bbName
  bbName_range'_nodup
  range'_append_of_le
  mem_bbName_range'
  translateBlocksInProg_names
  splitStmts_segChain
  translateBlocksInProg_segChain
  progStatementOk_notAssume
  progStatementOk_assume
  SegChain.pcZero
  SegPc.atStmt_notAssume
  SegPc.atStmt_assume
  SegPc.atEnd
  evalPlace_unitPlace
  placeStore_unitValue
  evalTerminator_assume_spec
  evalStmt_assume_anneal
  statementOk_isAssume
  splitStmts_statements
  mapM_translateStmtResult_of_noAssume
  evalPlace_derefFree_mach
  evalPlace_rethread_derefFree
  translatePlace_derefFree
  translateFnInProg_spec
  translateProgFns_get
  findCallee_idx
  lookupFnName_of_lookupFnTarget
  lookupFnTarget_zipIdx_aux
  lookupFnName_zipIdx_aux
  translateProg_spec
  translateCallConv_eq_some_iff
  translateUnwindAction_spec
  mkStartFn_spec
  translateTerminatorInProg_eq_of_not_call
  translateBlocksInProg_eq_of_no_calls
  translateFnInProg_eq_translateFn_of_no_calls
  multi_step_correspondence
  multi_step_start
  multi_step_start_with_no_returnRel
  multi_step_start_no_returnRel
  initMachineStateWithCallees_startRel
  bodyInProgFragment_allScalar
  itOf_scalar_layouts
  tyOf_scalar_layouts
  declSlotData_scalar_layouts
  scalarTypeOf_tyOf_of_isSome
  localAllocsFrom_scalar_layouts
  MultiStartRel.localsOk
  steps_add_no_returnRel
  multi_reaches_rel
  multi_run_ret
  multi_run_ret_from_start
  multi_run_ub
  multi_run_ub_from_start
  CallStackRel.frames_ne_nil
  MultiStateRel.not_returnRel
  multi_run_ub_rel
  multi_run_ub_rel_from_start
  multi_steps_error
  multi_steps_error_from_start
  multi_mirNoUB_safe
  multi_mirNoUB_safe_from_start
  multi_steps_outcome
  multi_steps_outcome_from_start
  multi_steps_outcome_any_from_start
  multi_mirNoUB_progress
  multi_mirNoUB_progress_from_start
  multi_mirNoUB_progress_any_from_start
  multi_mirNoUB_diverges_steps_ok
  multi_mirNoUB_diverges_from_start
  multi_mirNoUB_diverges_rel_from_start
  mirCallWithCallees_ret
  mirCallWithCallees_ub
  mirCallWithCallees_ub_rel
  mirCallWithCallees_noUB
  mirCallWithCallees_steps_error
  mirCallWithCallees_progress
  mirCallWithCallees_progress_any
  mirCallWithCallees_outcome
  mirCallWithCallees_outcome_any
  mirCallWithCallees_diverges_steps_ok
  mirCallWithCallees_diverges_rel
  Shape.not_returnRel_of_ne_nil
  StateRel.not_returnRel
  step_correspondence
  evalReturn_frame
  step_start
  step_start_with_no_returnRel
  step_start_no_returnRel
  initMachineState_startRel
  reaches_rel_no_returnRel_N
  reaches_rel_no_returnRel
  run_ret
  run_ret_from_start
  run_ub
  run_ub_from_start
  run_ub_rel_N
  run_ub_rel
  run_ub_rel_from_start_N
  run_ub_rel_from_start
  steps_error
  steps_error_from_start
  steps_outcome
  steps_outcome_from_start
  mirNoUB_safe
  mirNoUB_safe_from_start
  mirCall_ret
  mirCall_ub
  mirCall_ub_rel
  mirCall_noUB
  mirCall_progress
  mirCall_steps_error
  mirCall_outcome
  mirCall_diverges_steps_ok
  mirCall_diverges_rel
  stmtMustLive_mono
  iterLiveEntries_stabilizes
  livenessOk_eq_true
  liveAtEntry_greatest
  liveAtEntry_zero_mem
  dropMovedFrom_mono
  stmtTupleInit_mono
  termTupleInit_mono
  iterTupleInitEntries_stabilizes
  tupleInitOk_eq_true
  tupleInitAtEntry_greatest
  evalValue_operandT
  evalValue_rvalueB
  evalStatement_assignB
  evalOperand_fragT
  evalRvalue_fragB
  evalStmt_assignB
  evalScalarBinOp_rel_int
  evalScalarBinOp_rel_bool
  evalScalarBinOp_boolBit
  evalUnaryNot_bool
  evalBinOp_rel_frag
  evalValue_boolNot
  evalValue_boolToU8
  evalValue_boolBitOp
  translateRvalue_cast_bool
  translateRvalue_boolBit
  switch_spec
  typedStore_base_frag
  operandType_of_operandIsOrdering
  operandOkO_T
  evalValue_rvalueO
  evalStatement_assignO
  evalRvalue_fragO
  evalStmt_assignO
  evalScalarBinOp_cmp_int
  evalScalarBinOp_cmp_bool
  evalValue_translateCmp
  validBits_ordering
  typedStore_base_byte
  head_size_and_align_tuple
  layout_tuple
  withOverflow_eq
  checkValue_tuple
  encode_tuple
  decode_tuple
  decode_tuple_uninit
  typedLoad_local_tuple
  typedLoad_local_tuple_uninit
  typedStore_local_tuple
  typedLoad_local_localTy
  typedLoad_local_localTy_uninit
  evalPlace_field0L
  evalPlace_field1L
  typedLoad_local_tuple_field0
  typedLoad_local_tuple_field0_uninit
  typedLoad_local_tuple_field1
  typedLoad_local_tuple_field1_uninit
  evalBinOp_intWithOverflow
  translateRvalue_checked
  translateRvalue_tuple_agg
  evalValue_operandTuple
  evalValue_rvalueTuple
  evalStatement_assignTuple
  typedStore_base_tuple
  typedStore_base_localTy
  evalOperand_fragTuple
  evalScalarBinOp_checked
  evalRvalue_fragTuple
  evalStmt_assignTuple
  evalStatement_placeMention_place
  evalStmt_placeMention_place
  inFragment_spec
  storageDeadOk_spec
  mentionsOk_stmt
  mentionsOk_term
  foldl_moveOut_mem
  movedBefore_zero
  movedBefore_succ
  lookupSwitchTarget_mem
  unionLocals_mem
  stepMovedEntries_spec
  iterMovedEntries_fixed
  iterMovedEntries_mono
  iterMovedEntries_eq_of_fixed
  terminatorOk_targets_lt
  movesOk_of_fixed
  unionLocals_eq_or_mem_new
  stepMovedEntries_eq_or_strict
  iterMovedEntries_stabilizes
  statementOk_stmtMoved_lt
  terminatorOk_termMoved_lt
  movesOk_iff_blockMovesOk
  stmtMoved_mono
  termMoved_mono
  stepMovedEntries_least
  iterMovedEntries_least
  movedAtEntry_least
  blockMovesOk_spec
  movesOk_spec
  readsOk_mono
  stmtReadsOk_antitone
  termReadsOk_antitone
  blockMovesOk_antitone
  movesOk_of_preFixedPoint
  movesOk_iff_exists_preFixedPoint
  opsPost_get
  StaleOk.agree
  StaleOk.dead_iff
  StaleOk.slots
  StaleOk.readsAgree
  StaleOk.toBlock
  StaleOk.toBlockMove
  StaleOk.assign
  StaleOk.setBoth
  StaleOk.keep
  StateRelAt.advanceN
  StateRelAt.jumpN
  StartRel.localsOk
  initLocalsAux_spec
  steps_add
  moveKind_of_rvalueOk
  moveKind_of_rvalueOkB
  moveKind_of_rvalueOkO
  moveKind_of_rvalueOkTuple
  evalOperand_move
  evalOperand_copy_frame
  evalOperands_move
  evalRvalue_move
  evalRvalue_copy_locals
  evalStmt_assign_move
  evalScalarBinOp_locals
  evalUnaryNot_locals
  readsOk_spec
  opBits_frame
  rvBits_frame
  rvBitsB_frame
  rvBitsO_frame
  rvTupleBits_frame
  evalStmt_storageLive_disable
  evalStmt_storageLive_protected
  evalStmt_storageLive
  evalStmt_storageDead_disable
  evalStmt_storageDead_protected
  evalStmt_storageDead
  evalStmt_deinit
  evalStmt_placeMention_dead
  evalStatement_storageLive
  evalStatement_storageLive_init
  evalStatement_storageDead
  evalStatement_deinit
  evalStatement_assign_dead
  storageDead_some
  storageDead_none
  storageDead_none'
  BM_allocate_local
  BM_allocate_local_cand
  BM_allocate_local_cand_ns
  LocalsOkA.free_candidate_cand_ns
  localDeclOk_of_scalar
  NonScalarLive.of_scalar
  evalStatement_storageLive_cand
  evalStatement_storageLive_cand_ns
  evalStatement_storageLive_init_cand
  evalStatement_storageLive_init_cand_ns
  firstFitAddr_spec
  allocAddrOk_cand
  overlaps_low
  overlaps_cand
  LocalsOkA.free_candidate
  LocalsOkA.alloc'
  LocalsOkA.alloc
  LocalsOk.killLocal
  LocalsOk.forget
  LocalsOkA.teardown
  deallocAll_gen
  killAt_append_dead
  evalPlace_proj
  evalStatement_assign_array
  evalStatement_assign_index
  evalValue_arrayRvalue
  typedLoad_array_local
  typedLoad_array_elem
  typedStore_array_local
  typedStore_array_elem
  evalStmt_assign_array
  evalStmt_assign_index
  evalRvalue_array_frag
  readProjectedValue_proj
  writeProjectedValue_proj
  evalPlace_fieldPath
  evalPlace_tuplePlace
  typedLoad_tuple_slice
  typedStore_tuple_slice
  decode_tupleSpec
  encode_tupleSpec
  checkValue_tupleSpec
  evalValue_specOperand
  evalValue_tupleRvalue
  evalStatement_assign_tuple
  evalStatement_assign_field_scalar
  evalStmt_assign_tuple
  evalStmt_assign_field_scalar
  evalRvalue_tuple_frag
  resolveFieldPath_read
  resolveFieldPath_write
  step_correspondence_N
  step_start_N
  initMachineState_nonScalar
  reaches_rel_N
  run_ret_N
  run_ub_N
  steps_error_N
  steps_outcome_N
  steps_outcome_N_from_start
  mirNoUB_safe_N
  mirNoUB_progress_N
  mirNoUB_progress_N_from_start
  mirNoUB_diverges_steps_ok_N
  mirNoUB_diverges_rel_N_from_start
  mirCall_progress_N
  mirCall_outcome_N
  mirCall_diverges_rel_N
  nodup_map_localName
  nodup_map_fnName
  translateLocals_names
  SegChain.head_regular
  stmtCfgWf_of_translateStatement
  splitStmts_cfgWf
  termCfgWf_of_translateTerminator
  translateBlocksInProg_cfgWf
  translateFnInProg_funcCfgWf_core
  translateFnInProg_funcCfgWf
  translateFn_funcCfgWf
  mkStartFn_funcCfgWf
  translateProgFns_names_and_mem
  translateProg_progWf
  translateTy_eq_none_of_not_isMonoRigidTy
  derefPointeeTy_eq_none_of_not_isMonoRigidTy
  translateTy_container_param
  translateTy_container_alias
  isBorrowDescendantOrSelfAux_mono
  isBorrowDescendantOrSelfAux_of_lookup_sub
  isBorrowDescendantOrSelf_of_lookup_sub
  isBorrowDescendantOrSelf_map_eq
  isBorrowDescendantOrSelf_cons_child

open MiniRustSpec.Correspondence.Witness in
#check_theorem_deps "[WITNESS-AUDIT]"
  callerCallee_inFragment
  calleePair_initLen
  callerCallee_translate
  callerMain_translateInProg
  ctxCallerMain_ok
  callerCallee20_anneal_ret
  callerCallee20_noUB
  callerCallee20_progress
  callerCallee20_progress_any
  callerCallee20_outcome_any
  callerCallee20_minirust_ret
  callerCallee20_midCall_step5
  callerCallee20_minirust_direct
  callerCalleeOv_anneal_ret
  callerCalleeOv_noUB
  callerCalleeOv_minirust_ret
  callerCalleeOv_minirust_direct
  projDestCaller_inFragment
  ctxProjDest_ok
  projDest_translate
  projDestCaller_translateInProg
  projDest127_anneal_ret
  projDest127_noUB
  projDest127_minirust_ret
  projDest127_minirust_direct
  chain3_inFragment
  chain3_maxStackLocals
  ctxChainEntry_ok
  chain3_translate
  chainEntry_translateInProg
  chainNeg5_anneal_ret
  chainNeg5_noUB
  chainNeg5_minirust_ret
  chainNeg5_depth4_step7
  chainNeg5_minirust_direct
  callArgUb_inFragment
  ctxCallArgUb_ok
  callArgUb_translate
  callArgUbCaller_translateInProg
  callArgUb_anneal_ub
  callArgUb_minirust_ub
  callArgUb_minirust_direct
  callArgUb_converse_error
  callArgUb_outcome
  calleeDivZero_inFragment
  ctxCalleeDivZero_ok
  calleeDivZero_translate
  calleeDivZeroCaller_translateInProg
  calleeDivZero_anneal_ub
  calleeDivZero_minirust_ub
  calleeDivZero_minirust_direct
  calleeDivZero_converse_error
  callSpin_inFragment
  ctxCallSpin_ok
  callSpin_translate
  callSpinCaller_translateInProg
  callSpin_noUB
  callSpin_noRet
  callSpin_minirust_diverges
  callSpin_minirust_diverges_rel
  callDestArgAlias_movesOk
  callDestArgAlias_rejected
  callDestArgAlias_translate
  callDestArgAlias_anneal_ret
  callDestArgAlias_minirust_ub
  callProjMoveReuse_rejected
  callProjMoveReuse_translate
  callProjMoveReuse_anneal_ret
  callProjMoveReuse_minirust_ub
  callMoveReuse_inFragment
  callMoveReuse_anneal_ub
  callMoveReuse_translate
  callMoveReuse_translateInProg
  ctxCallMoveReuse_ok
  callMoveReuse_minirust_ub
  callMoveReuse_minirust_direct
  callMoveReuse_converse_error
  moveReinitByCall_inFragment
  moveReinitByCall_translate
  moveReinitByCall_translateInProg
  ctxMoveReinitByCall_ok
  moveReinitByCall_anneal_ret
  moveReinitByCall_minirust_ret
  moveReinitByCall_minirust_direct
  condCallMoveJoin_inFragment
  condCallMoveJoin_translate
  condCallMoveJoin_translateInProg
  ctxCondCallMoveJoin_ok
  condCallMoveJoin1_anneal_ret
  condCallMoveJoin1_minirust_ret
  condCallMoveJoin0_anneal_ret
  condCallMoveJoin0_minirust_ret
  condCallMoveJoin_minirust_direct
  stmtMoveThenCallArg_movesOk
  stmtMoveThenCallArg_rejected
  recCycle_maxStackLocals
  recCycle_rejected
  layout_ptr_and_array_mr41
  evalConstant_and_fnFromPtr_mr41
  checkAbiCompatibility_all_variants_mr41
  createFrame_ub_mr41
  evalReturn_missingNextBlock_and_bottomOfStack_ub
  cAbiCallee_conv
  cAbi_inFragment
  cAbi_translate
  cAbiCaller_translateInProg
  ctxCAbiCaller_ok
  cAbi32_anneal_ret
  cAbi32_noUB
  cAbi32_minirust_ret
  cAbi32_minirust_direct
  badCallConv_rejected
  deadCallDest_rejected
  deadCallDest_translate
  deadCallDest_anneal_ub
  deadCallDest_minirust_ub_before_callee
  uninitProjCallDest_rejected
  uninitProjCallDest_translate
  uninitProjCallDest_anneal_ret
  uninitProjCallDest_minirust_ret
  diamondCall_inFragment
  diamondCall_maxStackLocals
  ctxDiamondCall_ok
  diamondCall_translate
  diamondCallEntry_translateInProg
  diamondCall5_anneal_ret
  diamondCall5_noUB
  diamondCall5_minirust_ret
  diamondCall5_minirust_direct
  no_returnRel_before
  never_ub_of_nonUb_stop
  callDestArgAlias_noUB
  callDestArgAlias_noUB_transfer_fails
  callProjMoveReuse_noUB
  callProjMoveReuse_noUB_transfer_fails
  uninitProjCallDest_agreement
  liveCallDestSpin_inFragment
  liveCallDestSpin_translate
  liveCallDestSpin_translateInProg
  ctxLiveCallDestSpin_ok
  liveCallDestSpin_noUB
  liveCallDestSpin_noRet
  liveCallDestSpin_minirust_diverges
  liveCallDestSpin_minirust_diverges_rel
  liveCallDestSpin_depth3_step20
  deadCallDestSpin_rejected
  ctxDeadCallDestSpin_ok
  deadCallDestSpin_hyps
  deadCallDestSpin_noUB
  deadCallDestSpin_noRet
  deadCallDestSpin_minirust_ub
  deadCallDestSpin_noUB_transfer_fails
  abiArgMismatch_rejected
  abiArgMismatch_translate
  abiArgMismatch_anneal_ret
  abiArgMismatch_noUB
  abiArgMismatch_minirust_ub
  abiArgMismatch_noUB_transfer_fails
  abiRetMismatch_rejected
  abiRetMismatch_translate
  abiRetMismatch_anneal_ret
  abiRetMismatch_noUB
  abiRetMismatch_minirust_ub
  abiRetMismatch_noUB_transfer_fails
  argCountMismatch_rejected
  argCountMismatch_translate
  argCountMismatch_anneal_ret
  argCountMismatch_noUB
  argCountMismatch_minirust_ub
  argCountMismatch_noUB_transfer_fails
  stmtMoveThenCallArg_translate
  stmtMoveThenCallArg_anneal_ub
  stmtMoveThenCallArg_minirust_ret
  stmtMoveThenCallArg_ub_transfer_fails
  calleeRetUninit_inFragment
  calleeRetUninit_translate
  calleeRetUninit_translateInProg
  ctxCalleeRetUninit_ok
  calleeRetUninit_anneal_ub
  calleeRetUninit_minirust_ub
  calleeRetUninit_minirust_ub_rel
  calleeRetUninit_minirust_direct
  calleeRetUninit_converse_error
  retUninit_minirust_ub_rel_from_start
  negMention0_minirust_ub_rel_from_start
  calleeDivZero_minirust_ub_rel
  callArgUb_minirust_ub_rel
  callMoveReuse_minirust_ub_rel
  projDestCaller_liveness_stabilizes
  projDestCaller_tupleInit_stabilizes
  projDestCaller_liveAtEntry_greatest
  projDestCaller_tupleInitAtEntry_greatest
  progStart_outside_fragment
  cmpNotSwitch_inFragment
  cmpNotSwitch_translate
  cmpNotNeg1_anneal_ret
  cmpNotNeg1_noUB
  cmpNotNeg1_minirust_ret_from_start
  cmpNotNeg1_minirust_direct
  cmpNot3_anneal_ret
  cmpNot3_noUB
  cmpNot3_minirust_ret_from_start
  cmpNot3_minirust_direct
  leNeGe_inFragment
  leNeGe_translate
  leNeGe250_anneal_ret
  leNeGe250_noUB
  leNeGe250_minirust_ret_from_start
  leNeGe250_minirust_direct
  leNeGe5_anneal_ret
  leNeGe5_noUB
  leNeGe5_minirust_ret_from_start
  leNeGe5_minirust_direct
  boolCastI8_inFragment
  boolCastI8_translate
  boolCastInvalidArg_rejected
  boolCastTrue_anneal_ret
  boolCastTrue_noUB
  boolCastTrue_minirust_ret_from_start
  boolCastTrue_minirust_direct
  boolCastFalse_anneal_ret
  boolCastFalse_noUB
  boolCastFalse_minirust_ret_from_start
  boolCastFalse_minirust_direct
  uninitBool_inFragment
  uninitBool_translate
  uninitBool_anneal_ub
  uninitBool_minirust_ub_from_start
  uninitBool_minirust_direct
  uninitBoolNot_inFragment
  uninitBoolNot_translate
  uninitBoolNot_anneal_ub
  uninitBoolNot_minirust_ub_from_start
  uninitBoolNot_minirust_direct
  uninitBoolRel_inFragment
  uninitBoolRel_translate
  uninitBoolRel_anneal_ub
  uninitBoolRel_minirust_ub_from_start
  uninitBoolRel_minirust_direct
  ctxI8_ok_cmpSel
  cmpSel_inFragment
  cmpSel_translate
  cmpSelLess_anneal_ret
  cmpSelLess_noUB
  cmpSelLess_minirust_ret_from_start
  cmpSelLess_minirust_direct
  cmpSelEqual_anneal_ret
  cmpSelEqual_noUB
  cmpSelEqual_minirust_ret_from_start
  cmpSelEqual_minirust_direct
  cmpSelGreater_anneal_ret
  cmpSelGreater_noUB
  cmpSelGreater_minirust_ret_from_start
  cmpSelGreater_minirust_direct
  ctxBool_ok_ordering
  uninitOrdering_inFragment
  uninitOrdering_translate
  uninitOrdering_anneal_ub
  uninitOrdering_minirust_ub_from_start
  uninitOrdering_minirust_direct
  ctxI8_ok_boolBitOrdUse
  boolBitOrdUse_inFragment
  boolBitOrdUse_translate
  boolBitOrdInvalidTag_rejected
  boolBitOrdUseCmp_anneal_ret
  boolBitOrdUseCmp_noUB
  boolBitOrdUseCmp_minirust_ret_from_start
  boolBitOrdUseCmp_minirust_direct
  boolBitOrdUseCopy_anneal_ret
  boolBitOrdUseCopy_noUB
  boolBitOrdUseCopy_minirust_ret_from_start
  boolBitOrdUseCopy_minirust_direct
  uninitBoolBitAnd_inFragment
  uninitBoolBitAnd_translate
  uninitBoolBitAnd_anneal_ub
  uninitBoolBitAnd_minirust_ub_from_start
  uninitBoolBitAnd_minirust_direct
  uninitBoolBitOrRhs_inFragment
  uninitBoolBitOrRhs_translate
  uninitBoolBitOrRhs_anneal_ub
  uninitBoolBitOrRhs_minirust_ub_from_start
  uninitBoolBitOrRhs_minirust_direct
  relLt_signed
  relGt_unsigned
  relCmp_signed
  relCmp_unsigned
  relCmp_bool
  relLt_bool
  relGt_bool
  relLe_bool
  relGe_bool
  relEq_bool
  relNe_bool
  relGe_eq
  relNe_eq
  rel_mismatch
  transmute_bool_u8
  transmute_u8_bool
  transmute_u8_bool_invalid
  transmute_size_mismatch
  decode_bool_invalid
  bitNot_bool_panics
  ordering_validTags
  decode_ordering_less
  decode_ordering_invalid
  encode_ordering_greater
  checkValue_variant_invalid
  transmute_i8_ordering
  transmute_i8_ordering_invalid
  layout_paddedPair
  encode_paddedPair
  decode_paddedPair
  checkValue_tuple_arity
  decodeDiscriminant_short_circuits
  layout_slice
  layout_traitObject
  layout_unsizedTuple
  expectSize_unsized_panics
  expectAlign_traitObject_panics
  transmute_unsized_panics
  decode_unsized_panics
  encode_unsized_panics
  checkValue_unsized_panics
  layout_union
  decode_union
  encode_union
  checkValue_union_chunk_size
  checkValue_union_chunk_data
  transmute_union_paddedPair
  transmute_paddedPair_union
  transmute_union_paddedPair_uninit_ub
  ctxI8_ok_checkedArith
  checkedArithI8_inFragment
  checkedArithI8_translate
  checkedArithInvalidTupleArg_rejected
  checkedArithOk_anneal_ret
  checkedArithOk_noUB
  checkedArithOk_minirust_ret_from_start
  checkedArithOk_minirust_direct
  checkedArithAddOv_anneal_ret
  checkedArithAddOv_noUB
  checkedArithAddOv_minirust_ret_from_start
  checkedArithAddOv_minirust_direct
  checkedArithSubOv_anneal_ret
  checkedArithSubOv_noUB
  checkedArithSubOv_minirust_ret_from_start
  checkedArithSubOv_minirust_direct
  checkedArithMulOv_anneal_ret
  checkedArithMulOv_noUB
  checkedArithMulOv_minirust_ret_from_start
  checkedArithMulOv_minirust_direct
  ctxTupleU32_ok
  checkedTupleU32_inFragment
  checkedTupleU32_translate
  checkedTupleUnderAddOv_anneal_ret
  checkedTupleUnderAddOv_noUB
  checkedTupleUnderAddOv_minirust_ret_from_start
  checkedTupleUnderAddOv_minirust_direct
  checkedTupleMulOv_anneal_ret
  checkedTupleMulOv_noUB
  checkedTupleMulOv_minirust_ret_from_start
  checkedTupleMulOv_minirust_direct
  checkedTupleOk_anneal_ret
  checkedTupleOk_noUB
  checkedTupleOk_minirust_ret_from_start
  checkedTupleOk_minirust_direct
  ctxTupleU32_ok1
  uninitTupleField0_inFragment
  uninitTupleField0_translate
  uninitTupleField0_anneal_ub
  uninitTupleField0_minirust_ub_from_start
  uninitTupleField0_minirust_direct
  uninitTupleField0_converse_error
  uninitTupleField1_inFragment
  uninitTupleField1_translate
  uninitTupleField1_anneal_ub
  uninitTupleField1_minirust_ub_from_start
  uninitTupleField1_minirust_direct
  uninitTupleField1_outcome
  withOverflow_i8_layout
  withOverflow_u32_layout
  tupleHeadLayout_full_sized_and_slice
  cappedTailAlign_and_computeSizeAndAlign_all_branches
  evalBinOp_addWithOverflow_i8_max
  evalBinOp_subWithOverflow_i8_min
  evalBinOp_addWithOverflow_u32_max
  evalBinOp_subWithOverflow_u32_zero
  evalBinOp_mulWithOverflow_i8_min
  evalBinOp_mulWithOverflow_u32
  ptrOffsetInbounds_ok_and_oob
  evalValue_tuple_and_evalPlace_field
  evalBinOp_intWithOverflow_nonInt_panics
  evalPlace_field_panics
  evalBinOp_withOverflow_all_widths
  evalPlace_field_union_and_offset_panic
  sumTo_minirust_ret_from_start
  castBitNot4_minirust_ret_from_start
  uninitSwitchUb_minirust_ub_from_start
  tempMove_inFragment
  tempMove_alwaysLive
  tempMove_translate
  ctx0_ok_tempMove
  tempMove_initLen
  tempMove3_anneal_ret
  tempMove3_noUB
  tempMove3_progress
  tempMove3_minirust_ret_from_start
  tempMove3_minirust_direct
  tempMove2_anneal_ret
  tempMove2_noUB
  tempMove2_minirust_ret_from_start
  tempMove2_minirust_direct
  deadRead_inFragment
  deadRead_translate
  deadRead_anneal_ub
  deadRead_minirust_ub_from_start
  deadRead_minirust_direct
  deadRead_steps5_ub
  deadRead_converse_error
  deadRead_outcome
  moveReuse_movesOk
  moveReuse_not_inFragment
  moveReuse_translate
  moveReuse7_anneal_ub
  moveReuse7_minirust_direct
  crossBlockMove_inFragment
  crossBlockMove_movedAtEntry
  crossBlockMove_translate
  ctx0_ok_crossBlockMove
  crossBlockMove20_anneal_ret
  crossBlockMove20_noUB
  crossBlockMove20_progress
  crossBlockMove20_minirust_ret_from_start
  crossBlockMove20_minirust_direct
  crossBlockMoveOv_anneal_ret
  crossBlockMoveOv_noUB
  crossBlockMoveOv_progress
  crossBlockMoveOv_minirust_ret_from_start
  crossBlockMoveOv_minirust_direct
  crossBlockMoveReuse_movesOk
  unmarkedTempAssign_rejected
  unmarkedTempAssign_translate
  unmarkedTempAssign_anneal_ub
  unmarkedTempAssign_minirust_direct
  bm_allocate_and_deallocate_ub_cases
  evalStatement_deinit_ok_dead_and_misaligned
  loopTempMove_inFragment
  loopTempMove_alwaysLive
  loopTempMove_initLen
  loopTempMove_movedAtEntry_multiPass
  loopTempMove_translate
  ctx0_ok_loopTempMove
  loopTempMove3_anneal_ret
  loopTempMove3_noUB
  loopTempMove3_progress
  loopTempMove3_minirust_ret_from_start
  loopTempMove3_minirust_direct
  loopTempMove0_anneal_ret
  loopTempMove0_noUB
  loopTempMove0_progress
  loopTempMove0_minirust_ret_from_start
  loopTempMove0_minirust_direct
  loopBackEdgeReuse_movesOk
  loopBackEdgeReuse_translate
  loopBackEdgeReuse1_anneal_ub
  loopBackEdgeReuse1_minirust_direct
  deadAssign_inFragment
  deadAssign_translate
  deadAssign_anneal_ub
  deadAssign_minirust_ub_from_start
  deadAssign_minirust_direct
  deadAssign_steps4_ub
  deadAssign_converse_error
  deadAssign_outcome
  deadDeinit_inFragment
  deadDeinit_translate
  deadDeinit_anneal_ub
  deadDeinit_minirust_ub_from_start
  deadDeinit_minirust_direct
  deadDeinit_steps5_ub
  deadDeinit_converse_error
  deadDeinit_outcome
  ctx0_ok_u32_tuple
  deadPlaceMention_inFragment
  deadPlaceMention_translate
  deadPlaceMention_anneal_ub
  deadPlaceMention_minirust_ub_from_start
  deadPlaceMention_minirust_direct
  deadPlaceMention_steps4_ub
  deadPlaceMention_converse_error
  deadPlaceMention_outcome
  storageDeadRet_rejected
  storageDeadRet_translate
  storageDeadRet_anneal_ub
  storageDeadRet_minirust_panics
  projectedDeinit_rejected
  projectedDeinit_translate
  projectedDeinit_anneal_ub
  projectedDeinit_minirust_ub
  projAssignMoveReuse_movesOk
  sameRvalueMoveReuse_movesOk
  sameRvalueMoveReuse_translate
  sameRvalueMoveReuse5_anneal_ub
  sameRvalueMoveReuse5_minirust_direct
  moveRetPlace_movesOk
  moveRetPlace_translate
  moveRetPlace_anneal_ub
  moveRetPlace_minirust_direct
  storageLiveArgRet_inFragment
  storageLiveArgRet_translate
  ctx0_ok_u32_3
  storageLiveArgRet5_anneal_ret
  storageLiveArgRet5_noUB
  storageLiveArgRet5_progress
  storageLiveArgRet5_minirust_ret_from_start
  storageLiveArgRet5_minirust_direct
  storageDeadArg_rejected
  storageDeadArg_translate
  storageDeadArg5_anneal_ret
  storageDeadArg5_minirust_direct
  storageDeadArgReadAfter_rejected
  storageDeadArgReadAfter_translate
  storageDeadArgReadAfter5_anneal_ub
  storageDeadArgReadAfter5_minirust_ub
  ctx0_2_ok_bool_u32
  diamondMoveJoin_inFragment
  diamondMoveJoin_movedAtEntry
  diamondMoveJoin_translate
  diamondMoveJoinTrue_anneal_ret
  diamondMoveJoinTrue_noUB
  diamondMoveJoinTrue_progress
  diamondMoveJoinTrue_minirust_ret_from_start
  diamondMoveJoinTrue_minirust_direct
  diamondMoveJoinFalse_anneal_ret
  diamondMoveJoinFalse_noUB
  diamondMoveJoinFalse_progress
  diamondMoveJoinFalse_minirust_ret_from_start
  diamondMoveJoinFalse_minirust_direct
  diamondHalfMoveReuse_movesOk
  diamondHalfMoveReuse_translate
  diamondHalfMoveReuseFalse_anneal_ub
  diamondHalfMoveReuseFalse_minirust_direct
  ctx0_ok_tupleAggCastMove
  tupleAggCastMove_inFragment
  tupleAggCastMove_translate
  tupleAggCastMoveNeg5_anneal_ret
  tupleAggCastMoveNeg5_noUB
  tupleAggCastMoveNeg5_progress
  tupleAggCastMoveNeg5_minirust_ret_from_start
  tupleAggCastMoveNeg5_minirust_direct
  projFieldMoveReuse_movesOk
  projFieldMoveReuse_translate
  projFieldMoveReuse_anneal_ub
  projFieldMoveReuse_minirust_direct
  ctx0_ok_trailing_temp_addrs
  ctxI8_ok_ordBoolCastTempMove
  ordBoolCastTempMove_inFragment
  ordBoolCastTempMove_movedAtEntry
  ordBoolCastTempMove_movesOk_by_preFixedPoint
  ordBoolCastTempMove_translate
  ordBoolCastTempMoveTrue_anneal_ret
  ordBoolCastTempMoveTrue_noUB
  ordBoolCastTempMoveTrue_progress
  ordBoolCastTempMoveTrue_minirust_ret_from_start
  ordBoolCastTempMoveTrue_minirust_direct
  ordBoolCastTempMoveFalse_anneal_ret
  ordBoolCastTempMoveFalse_noUB
  ordBoolCastTempMoveFalse_progress
  ordBoolCastTempMoveFalse_minirust_ret_from_start
  ordBoolCastTempMoveFalse_minirust_direct
  arrayOpsI8_inFragment
  arrayOpsI8_translate
  arrayOpsOk_anneal_ret
  arrayOpsOk_noUB
  arrayOpsOk_minirust_ret_from_start
  arrayOpsOk_minirust_direct
  arrayOpsOk_minirust_inplace_bytes
  arrayOpsOk_minirust_ret_dealloc
  arrayOpsOob_anneal_ub
  arrayOpsOob_minirust_ub_from_start
  arrayOpsOob_minirust_direct
  arrayOpsOob_converse_error
  arraySignedIdxI8_inFragment
  arraySignedIdxI8_translate
  arraySignedIdxOk_anneal_ret
  arraySignedIdxOk_minirust_ret_from_start
  arraySignedIdxOk_minirust_direct
  arraySignedNegUb_anneal_ub
  arraySignedNegUb_minirust_ub_from_start
  arraySignedNegUb_minirust_direct
  arraySignedOobUb_anneal_ub
  arraySignedOobUb_minirust_ub_from_start
  arraySignedOobUb_minirust_direct
  arrayUninitIdxI8_inFragment
  arrayUninitIdxI8_translate
  arrayUninitIdx_anneal_ub
  arrayUninitIdx_minirust_ub_from_start
  arrayUninitIdx_minirust_direct
  arrayU32Idx_inFragment
  arrayU32Idx_translate
  arrayU32IdxOk_anneal_ret
  arrayU32IdxOk_noUB
  arrayU32IdxOk_minirust_ret_from_start
  arrayU32IdxOk_minirust_direct
  arrayU32IdxOk_minirust_inplace_bytes
  arrayU32IdxOob_anneal_ub
  arrayU32IdxOob_minirust_ub_from_start
  arrayU32IdxOob_minirust_direct
  arrayConstIdxOobI8_inFragment
  arrayConstIdxOobI8_translate
  arrayConstIdxOob_anneal_ub
  arrayConstIdxOob_minirust_ub_from_start
  arrayConstIdxOob_minirust_direct
  sizeMulInt_zero_neg
  array_encode_decode_edge_cases
  zeroArrayI8_inFragment
  zeroArrayI8_translate
  zeroArrayOk_anneal_ret
  zeroArrayOk_noUB
  zeroArrayOk_minirust_ret_from_start
  zeroArrayOk_minirust_direct
  zeroArrayIdxUb_anneal_ub
  zeroArrayIdxUb_minirust_ub_from_start
  zeroArrayIdxUb_minirust_direct
  arrayComposeI8_inFragment
  arrayComposeI8_translate
  arrayComposeOk_anneal_ret
  arrayComposeOk_noUB
  arrayComposeOk_minirust_ret_from_start
  arrayComposeOk_minirust_direct
  arrayComposeAggUb_anneal_ub
  arrayComposeAggUb_minirust_ub_from_start
  arrayComposeAggUb_minirust_direct
  arrayComposeRepeatUb_anneal_ub
  arrayComposeRepeatUb_minirust_ub_from_start
  arrayComposeRepeatUb_minirust_direct
  arrayComposeRhsUb_anneal_ub
  arrayComposeRhsUb_minirust_ub_from_start
  arrayComposeRhsUb_minirust_direct
  arrayComposeBothUb_anneal_ub
  arrayComposeBothUb_minirust_ub_from_start
  arrayComposeBothUb_minirust_direct
  arrayComposeSwitchOobUb_anneal_ub
  arrayComposeSwitchOobUb_minirust_ub_from_start
  arrayComposeSwitchOobUb_minirust_direct
  paddedStructOps_inFragment
  paddedStructOps_translate
  paddedStructOk_anneal_ret
  paddedStructOk_noUB
  paddedStructOk_minirust_ret_from_start
  paddedStructOk_minirust_direct
  paddedStructOk_minirust_padding_bytes
  paddedStructOk_minirust_ret_dealloc
  paddedStructOk_minirust_noUB
  paddedStructOk_minirust_progress
  nestedTupleOps_inFragment
  nestedTupleOps_translate
  nestedTupleOk_anneal_ret
  nestedTupleOk_noUB
  nestedTupleOk_minirust_ret_from_start
  nestedTupleOk_minirust_direct
  nestedTupleOk_minirust_padding_bytes
  nestedTupleOk_minirust_ret_dealloc
  nestedTupleOk_minirust_noUB
  nestedTupleOk_minirust_progress
  nestedTupleAggUb_anneal_ub
  nestedTupleAggUb_minirust_ub_from_start
  nestedTupleAggUb_minirust_direct
  nestedTupleAggUb_converse_error
  nestedTupleFieldRhsUb_anneal_ub
  nestedTupleFieldRhsUb_minirust_ub_from_start
  nestedTupleFieldRhsUb_minirust_direct
  nestedTupleFieldRhsUb_converse_error
  nestedTupleCopyUninitUb_anneal_ub
  nestedTupleCopyUninitUb_minirust_ub_from_start
  nestedTupleCopyUninitUb_minirust_direct
  nestedTupleCopyUninitUb_converse_error
  tuple_encode_decode_place_edge_cases
  evalIntrinsic_abort_exit
  evalIntrinsic_assume
  evalIntrinsic_print
  evalIntrinsic_rawEq_withExposed
  evalIntrinsic_rawEq
  evalIntrinsic_allocate_deallocate_leak
  evalIntrinsic_exposeProvenance
  evalIntrinsic_getUnwindPayload_empty
  evalTerminator_abortTerminator
  translateRsIntrinsic_witness
  assumeSub_translate
  assumeSub_translateInProg
  assumeSub_inFragment
  ctxAssumeSub_ok
  runsToScalar_sound
  assumeSub20_anneal_ret
  assumeSub20_minirust_ret
  assumeSub20_minirust_direct
  assumeSub20_split_point
  assumeSubFalse_anneal_ub
  assumeSubFalse_minirust_ub_rel
  assumeSubFalse_ub
  assumeTupleCall_inFragment
  assumeTupleCall_translate
  assumeTupleCall_translateInProg
  ctxAssumeTupleCall_ok
  assumeTupleCall10_anneal_ret
  assumeTupleCall10_minirust_ret
  assumeTupleCallOv_anneal_ub
  assumeTupleCallOv_minirust_ub_rel
  assumeDeadLocal_inFragment
  assumeDeadLocal_translate
  assumeDeadLocal_translateInProg
  ctxAssumeDeadLocal_ok
  assumeDeadLocal_anneal_ub
  assumeDeadLocal_minirust_ub_rel
  assumeMultiFrame_inFragment
  assumeMultiFrame_translate
  assumeMultiFrame_translateInProg
  assumeChainCallee_translateInProg
  assumeMultiFrame_prog_wf
  assumeMultiFrame_func_wf_caller
  assumeMultiFrame_func_wf_callee
  ctxAssumeMultiFrame_ok
  assumeMultiFrame5_anneal_ret
  assumeMultiFrame5_minirust_ret
  assumeMultiFramePreUb_anneal_ub
  assumeMultiFramePreUb_minirust_ub_rel
  assumeMultiFrameCalleeSeg2Ub_anneal_ub
  assumeMultiFrameCalleeSeg2Ub_minirust_ub_rel
  assumeMultiFramePostUb_anneal_ub
  assumeMultiFramePostUb_minirust_ub_rel
  assumeMoveReuse_rejected
  assumeMoveReuse_diverges
  assumeAfterMove_rejected
  assumeAfterMove_diverges
  itOf_uint
  tyOf_uint

open MiniRustSpec.Correspondence MiniRustSpec.Correspondence.PointerWitness in
#assert_standard_axioms
  encodePtrBytes_length
  ptrBytes_length
  encodePtrBytes_data
  decodePtrProvenance_encode
  decodePtrProvenance_none
  two_pow_ptrBits
  inBounds_usize
  lt_two_pow_64_int
  encode_usize
  encodePtr_of_encode
  encodePtr_eq
  firstProvenance_encodePtrBytes
  decodePtr_ptrBytes
  decodePtrProvenance_mixed
  layout_thinRawPtr
  decode_thinRawPtr
  encode_thinRawPtr
  checkValue_thinRawPtr
  checkValue_thinRawPtr_oob
  resolveBorrowProjectionElems_noIndex
  evalRvalue_rawPtr_local
  evalOperand_copy_deref
  evalOperand_copy_deref_disabled
  writePlaceValue_deref_frozen
  writePlaceValue_deref_root
  evalRvalue_offset
  evalRvalue_ptrToPtr
  evalRvalue_expose
  evalRvalue_withExposed
  ptrAliasingOk_spec
  StaleOk.addrTaken_eq
  evalTargetPlace
  evalPtrLoad
  BorrowsOk.start
  BorrowsOk.advance_keep
  BorrowsOk.advance_set_nonptr
  BorrowsOk.ptrCopy
  BorrowsOk.advance_storage
  BorrowsOk.jump
  BorrowsOk.rawPtr
  BorrowsOk.derefWrite
  BorrowsOk.derefRead
  LocalsOk.rawPtr_extend
  evalStmt_assign_rawPtr
  BorrowsOk.freezeRead
  evalStmt_assign_derefWrite
  evalStmt_assign_derefWrite_move
  evalOperand_deref_eq_target
  evalRvalue_ptrRvalue
  evalRvalue_derefRead_eq
  evalPlace_deref
  evalValue_addrOf
  evalStatement_assign_rawPtr_mr
  evalStatement_assign_ptrRvalue_mr
  evalValue_ptrOffset_zero
  derefWrite_target
  statementOk_rawPtr_spec
  statementOk_derefRead
  ptrTargetSpec_cases
  ptrRoundTrip_inFragment
  ptrRoundTrip_translate
  ptrRoundTrip_anneal_ret
  ptrRoundTrip_noUB
  ptrRoundTrip_minirust_direct
  ptrRoundTrip_ctxOk
  ptrRoundTrip_minirust_ret_from_start
  ptrRoundTrip_minirust_noUB
  ptrRoundTrip_progress
  arrayParamPtr_inFragment
  arrayParamPtr_translate
  arrayParamPtr_anneal_ret
  arrayParamPtr_noUB
  arrayParamPtr_ctxOk
  arrayParamPtr_minirust_ret_from_start
  arrayParamPtr_minirust_noUB
  arrayParamPtr_progress
  arrayParamPtr_minirust_direct
  arrayElemPtr_notInFragment
  arrayElemPtr_anneal_ret
  arrayElemPtr_minirust_direct
  fieldPtr_inFragment
  fieldPtr_translate
  fieldPtr_anneal_ret
  fieldPtr_noUB
  fieldPtr_ctxOk
  fieldPtr_minirust_ret_from_start
  fieldPtr_minirust_noUB
  fieldPtr_progress
  fieldPtr_minirust_direct
  nestedFieldPtr_inFragment
  nestedFieldPtr_translate
  nestedFieldPtr_anneal_ret
  nestedFieldPtr_noUB
  nestedFieldPtr_ctxOk
  nestedFieldPtr_minirust_ret_from_start
  nestedFieldPtr_minirust_noUB
  nestedFieldPtr_progress
  nestedFieldPtr_minirust_direct
  nestedFieldPtr_minirust_padding_bytes
  ptrCountdown_inFragment
  ptrCountdown_translate
  ptrCountdown_anneal_ret
  ptrCountdown_noUB
  ptrCountdown_ctxOk
  ptrCountdown_minirust_ret_from_start
  ptrCountdown_minirust_noUB
  ptrCountdown_progress
  ptrCountdown_minirust_direct
  constBorrowLoop_inFragment
  constBorrowLoop_translate
  constBorrowLoop_anneal_ret
  constBorrowLoop_noUB
  constBorrowLoop_ctxOk
  constBorrowLoop_minirust_ret_from_start
  constBorrowLoop_minirust_noUB
  constBorrowLoop_progress
  constBorrowLoop_minirust_direct
  repointPtr_inFragment
  repointPtr_translate
  repointPtr_anneal_ret
  repointPtr_noUB
  repointPtr_ctxOk
  repointPtr_minirust_ret_from_start
  repointPtr_minirust_noUB
  repointPtr_progress
  repointPtr_minirust_direct
  ptrSpinLoop_inFragment
  ptrSpinLoop_translate
  ptrSpinLoop_step_inv
  ptrSpinLoop_noUB
  ptrSpinLoop_diverges
  ptrSpinLoop_ctxOk
  ptrSpinLoop_minirust_steps_ok
  ptrSpinLoop_minirust_diverges_rel
  ptrSpinLoop_minirust_direct
  uninitPtrReadUb_inFragment
  uninitPtrReadUb_translate
  uninitPtrReadUb_anneal_ub
  uninitPtrReadUb_ctxOk
  uninitPtrReadUb_minirust_ub_from_start
  uninitPtrReadUb_converse_error
  uninitPtrReadUb_outcome
  uninitPtrReadUb_minirust_direct
  uninitPtrWriteUb_inFragment
  uninitPtrWriteUb_translate
  uninitPtrWriteUb_anneal_ub
  uninitPtrWriteUb_ctxOk
  uninitPtrWriteUb_minirust_ub_from_start
  uninitPtrWriteUb_converse_error
  uninitPtrWriteUb_outcome
  uninitPtrWriteUb_minirust_direct
  deadPtrReadUb_inFragment
  deadPtrReadUb_translate
  deadPtrReadUb_anneal_ub
  deadPtrReadUb_ctxOk
  deadPtrReadUb_minirust_ub_from_start
  deadPtrReadUb_converse_error
  deadPtrReadUb_outcome
  deadPtrReadUb_minirust_direct
  uninitPtrOffsetUb_inFragment
  uninitPtrOffsetUb_translate
  uninitPtrOffsetUb_anneal_ub
  uninitPtrOffsetUb_ctxOk
  uninitPtrOffsetUb_minirust_ub_from_start
  uninitPtrOffsetUb_converse_error
  uninitPtrOffsetUb_outcome
  uninitPtrOffsetUb_minirust_direct
  derefWriteRhsUb_inFragment
  derefWriteRhsUb_translate
  derefWriteRhsUb_anneal_ub
  derefWriteRhsUb_ctxOk
  derefWriteRhsUb_minirust_ub_from_start
  derefWriteRhsUb_converse_error
  derefWriteRhsUb_outcome
  derefWriteRhsUb_minirust_direct
  derefIdxWriteRhsUb_inFragment
  derefIdxWriteRhsUb_translate
  derefIdxWriteRhsUb_anneal_ub
  derefIdxWriteRhsUb_ctxOk
  derefIdxWriteRhsUb_minirust_ub_from_start
  derefIdxWriteRhsUb_converse_error
  derefIdxWriteRhsUb_outcome
  derefIdxWriteRhsUb_minirust_direct
  derefFieldWriteRhsUb_inFragment
  derefFieldWriteRhsUb_translate
  derefFieldWriteRhsUb_anneal_ub
  derefFieldWriteRhsUb_ctxOk
  derefFieldWriteRhsUb_minirust_ub_from_start
  derefFieldWriteRhsUb_converse_error
  derefFieldWriteRhsUb_outcome
  derefFieldWriteRhsUb_minirust_direct
  dangling_notInFragment
  dangling_anneal_ub
  dangling_minirust_direct
  offsetDeref_notInFragment
  offsetDeref1_translate
  offsetDeref2_translate
  offsetDeref3_translate
  offsetDerefMax_translate
  offsetDeref_anneal_ret
  offsetDeref_anneal_ub
  offsetDeref1_minirust_direct
  offsetDeref2_minirust_direct
  offsetDeref3_minirust_direct
  offsetDerefMax_minirust_direct
  misaligned_notInFragment
  misaligned_anneal_ub
  misaligned_minirust_direct
  exposeTwice_translate
  exposeTwice_notInFragment
  exposeTwice_anneal_ret
  exposeTwice_minirust_direct
  directWrite_notInFragment
  directWrite_anneal_ub
  directWrite_minirust_direct
  frozenWrite_notInFragment
  frozenWrite_anneal_ub
  frozenWrite_minirust_direct
  checkPtr_null
  ptrOffsetWrapping_wraps
  checkValue_thinRawPtr_bounds

open MiniRustSpec.Correspondence MiniRustSpec.Correspondence.PointerWitness in
#check_theorem_deps "[POINTER-AUDIT]"
  encodePtrBytes_length
  ptrBytes_length
  encodePtrBytes_data
  decodePtrProvenance_encode
  decodePtrProvenance_none
  two_pow_ptrBits
  inBounds_usize
  lt_two_pow_64_int
  encode_usize
  encodePtr_of_encode
  encodePtr_eq
  firstProvenance_encodePtrBytes
  decodePtr_ptrBytes
  decodePtrProvenance_mixed
  layout_thinRawPtr
  decode_thinRawPtr
  encode_thinRawPtr
  checkValue_thinRawPtr
  checkValue_thinRawPtr_oob
  resolveBorrowProjectionElems_noIndex
  evalRvalue_rawPtr_local
  evalOperand_copy_deref
  evalOperand_copy_deref_disabled
  writePlaceValue_deref_frozen
  writePlaceValue_deref_root
  evalRvalue_offset
  evalRvalue_ptrToPtr
  evalRvalue_expose
  evalRvalue_withExposed
  ptrAliasingOk_spec
  StaleOk.addrTaken_eq
  evalTargetPlace
  evalPtrLoad
  BorrowsOk.start
  BorrowsOk.advance_keep
  BorrowsOk.advance_set_nonptr
  BorrowsOk.ptrCopy
  BorrowsOk.advance_storage
  BorrowsOk.jump
  BorrowsOk.rawPtr
  BorrowsOk.derefWrite
  BorrowsOk.derefRead
  LocalsOk.rawPtr_extend
  evalStmt_assign_rawPtr
  BorrowsOk.freezeRead
  evalStmt_assign_derefWrite
  evalStmt_assign_derefWrite_move
  evalOperand_deref_eq_target
  evalRvalue_ptrRvalue
  evalRvalue_derefRead_eq
  evalPlace_deref
  evalValue_addrOf
  evalStatement_assign_rawPtr_mr
  evalStatement_assign_ptrRvalue_mr
  evalValue_ptrOffset_zero
  derefWrite_target
  statementOk_rawPtr_spec
  statementOk_derefRead
  ptrTargetSpec_cases
  ptrRoundTrip_inFragment
  ptrRoundTrip_translate
  ptrRoundTrip_anneal_ret
  ptrRoundTrip_noUB
  ptrRoundTrip_minirust_direct
  ptrRoundTrip_ctxOk
  ptrRoundTrip_minirust_ret_from_start
  ptrRoundTrip_minirust_noUB
  ptrRoundTrip_progress
  arrayParamPtr_inFragment
  arrayParamPtr_translate
  arrayParamPtr_anneal_ret
  arrayParamPtr_noUB
  arrayParamPtr_ctxOk
  arrayParamPtr_minirust_ret_from_start
  arrayParamPtr_minirust_noUB
  arrayParamPtr_progress
  arrayParamPtr_minirust_direct
  arrayElemPtr_notInFragment
  arrayElemPtr_anneal_ret
  arrayElemPtr_minirust_direct
  fieldPtr_inFragment
  fieldPtr_translate
  fieldPtr_anneal_ret
  fieldPtr_noUB
  fieldPtr_ctxOk
  fieldPtr_minirust_ret_from_start
  fieldPtr_minirust_noUB
  fieldPtr_progress
  fieldPtr_minirust_direct
  nestedFieldPtr_inFragment
  nestedFieldPtr_translate
  nestedFieldPtr_anneal_ret
  nestedFieldPtr_noUB
  nestedFieldPtr_ctxOk
  nestedFieldPtr_minirust_ret_from_start
  nestedFieldPtr_minirust_noUB
  nestedFieldPtr_progress
  nestedFieldPtr_minirust_direct
  nestedFieldPtr_minirust_padding_bytes
  ptrCountdown_inFragment
  ptrCountdown_translate
  ptrCountdown_anneal_ret
  ptrCountdown_noUB
  ptrCountdown_ctxOk
  ptrCountdown_minirust_ret_from_start
  ptrCountdown_minirust_noUB
  ptrCountdown_progress
  ptrCountdown_minirust_direct
  constBorrowLoop_inFragment
  constBorrowLoop_translate
  constBorrowLoop_anneal_ret
  constBorrowLoop_noUB
  constBorrowLoop_ctxOk
  constBorrowLoop_minirust_ret_from_start
  constBorrowLoop_minirust_noUB
  constBorrowLoop_progress
  constBorrowLoop_minirust_direct
  repointPtr_inFragment
  repointPtr_translate
  repointPtr_anneal_ret
  repointPtr_noUB
  repointPtr_ctxOk
  repointPtr_minirust_ret_from_start
  repointPtr_minirust_noUB
  repointPtr_progress
  repointPtr_minirust_direct
  ptrSpinLoop_inFragment
  ptrSpinLoop_translate
  ptrSpinLoop_step_inv
  ptrSpinLoop_noUB
  ptrSpinLoop_diverges
  ptrSpinLoop_ctxOk
  ptrSpinLoop_minirust_steps_ok
  ptrSpinLoop_minirust_diverges_rel
  ptrSpinLoop_minirust_direct
  uninitPtrReadUb_inFragment
  uninitPtrReadUb_translate
  uninitPtrReadUb_anneal_ub
  uninitPtrReadUb_ctxOk
  uninitPtrReadUb_minirust_ub_from_start
  uninitPtrReadUb_converse_error
  uninitPtrReadUb_outcome
  uninitPtrReadUb_minirust_direct
  uninitPtrWriteUb_inFragment
  uninitPtrWriteUb_translate
  uninitPtrWriteUb_anneal_ub
  uninitPtrWriteUb_ctxOk
  uninitPtrWriteUb_minirust_ub_from_start
  uninitPtrWriteUb_converse_error
  uninitPtrWriteUb_outcome
  uninitPtrWriteUb_minirust_direct
  deadPtrReadUb_inFragment
  deadPtrReadUb_translate
  deadPtrReadUb_anneal_ub
  deadPtrReadUb_ctxOk
  deadPtrReadUb_minirust_ub_from_start
  deadPtrReadUb_converse_error
  deadPtrReadUb_outcome
  deadPtrReadUb_minirust_direct
  uninitPtrOffsetUb_inFragment
  uninitPtrOffsetUb_translate
  uninitPtrOffsetUb_anneal_ub
  uninitPtrOffsetUb_ctxOk
  uninitPtrOffsetUb_minirust_ub_from_start
  uninitPtrOffsetUb_converse_error
  uninitPtrOffsetUb_outcome
  uninitPtrOffsetUb_minirust_direct
  derefWriteRhsUb_inFragment
  derefWriteRhsUb_translate
  derefWriteRhsUb_anneal_ub
  derefWriteRhsUb_ctxOk
  derefWriteRhsUb_minirust_ub_from_start
  derefWriteRhsUb_converse_error
  derefWriteRhsUb_outcome
  derefWriteRhsUb_minirust_direct
  derefIdxWriteRhsUb_inFragment
  derefIdxWriteRhsUb_translate
  derefIdxWriteRhsUb_anneal_ub
  derefIdxWriteRhsUb_ctxOk
  derefIdxWriteRhsUb_minirust_ub_from_start
  derefIdxWriteRhsUb_converse_error
  derefIdxWriteRhsUb_outcome
  derefIdxWriteRhsUb_minirust_direct
  derefFieldWriteRhsUb_inFragment
  derefFieldWriteRhsUb_translate
  derefFieldWriteRhsUb_anneal_ub
  derefFieldWriteRhsUb_ctxOk
  derefFieldWriteRhsUb_minirust_ub_from_start
  derefFieldWriteRhsUb_converse_error
  derefFieldWriteRhsUb_outcome
  derefFieldWriteRhsUb_minirust_direct
  dangling_notInFragment
  dangling_anneal_ub
  dangling_minirust_direct
  offsetDeref_notInFragment
  offsetDeref1_translate
  offsetDeref2_translate
  offsetDeref3_translate
  offsetDerefMax_translate
  offsetDeref_anneal_ret
  offsetDeref_anneal_ub
  offsetDeref1_minirust_direct
  offsetDeref2_minirust_direct
  offsetDeref3_minirust_direct
  offsetDerefMax_minirust_direct
  misaligned_notInFragment
  misaligned_anneal_ub
  misaligned_minirust_direct
  exposeTwice_translate
  exposeTwice_notInFragment
  exposeTwice_anneal_ret
  exposeTwice_minirust_direct
  directWrite_notInFragment
  directWrite_anneal_ub
  directWrite_minirust_direct
  frozenWrite_notInFragment
  frozenWrite_anneal_ub
  frozenWrite_minirust_direct
  checkPtr_null
  ptrOffsetWrapping_wraps
  checkValue_thinRawPtr_bounds

open MiniRustSpec.Correspondence MiniRustSpec.Correspondence.PointerWitness MiniRustSpec.Correspondence.RefWitness in
#assert_standard_axioms
  ptrPointeeOf_of_rawPtrPointeeOf
  ptrPointeeOf_of_refPointeeOf
  declPtrTy_of_rawPtrPointeeOf
  declPtrTy_of_refPointeeOf
  declPtrTy_of_isRefTy_false
  declPtrTy_of_isRefTy_true
  declPtrTy_cases
  refPointeeOf_good
  AddrOk.nonneg
  layout_refTy
  decode_refTy
  decode_refTy_uninit
  encode_refTy
  inBounds_goodSize
  checkValue_refTy
  checkValue_refTy_null_ub
  checkValue_refTy_unaligned_ub
  checkValue_refTy_dangling_ub
  layout_declPtrTy
  decode_declPtrTy
  decode_declPtrTy_uninit
  encode_declPtrTy
  checkValue_declPtrTy
  tyIsFreeze_of_intTypeOf
  appendProjections_nil_right
  sharedBorrowPerm_of_ptrTargetSpec
  sharedBorrowPerm_of_deref_ptrPointeeOf
  evalRvalue_ref_local
  evalRvalue_rawPtr_reborrow
  evalRvalue_ref_reborrow
  evalRvalue_ref_reborrow_frozen_mut_ub
  evalRvalue_ref_reborrow_disabled_ub
  evalRvalue_rawPtr_reborrow_frozen_mut_ub
  evalRvalue_rawPtr_reborrow_disabled_ub
  evalRvalue_reborrow_ub_of_not_init
  cellsToFreezeMask_nil
  cellsToFreezeMask_single_full
  mapM_replicate_ok
  reborrowSettings_shared_freeze
  reborrowSettings_mut_freeze_default
  reborrowSettings_mut_freeze_fnEntry_noImplicit
  reborrowSettings_mut_freeze_fnEntry_implicitWrite
  reborrowSettings_shared_cell
  reborrowSettings_raw_none
  cm_dereferenceable_offsetPtr
  cm_dereferenceable_of_shape_eq
  typedLoad_local_declPtrTy
  typedLoad_local_declPtrTy_uninit
  typedStore_local_declPtrTy
  typedLoad_ptr_declPtrTy
  typedLoad_ptr_declPtrTy_uninit
  typedStore_ptr_declPtrTy
  directBorrowOf_rawPtr_of_nonDeref
  directBorrowOf_ref_of_nonDeref
  mem_bodyAddrTakenLocals_of_directBorrow
  transmute_refTy_ok
  transmute_refTy_dangling_ub
  evalCastOp_transmute_refTy_ok
  evalCastOp_transmute_refTy_dangling_ub
  retagPtrBM_shape
  retagVal_ptr_shape
  evalStatement_validate_declPtrTy
  borrowProjSteps_stripTransparent
  borrowProjOverlap_borrowProjSteps
  updateBorrowPermAtProj_fields
  updateBorrowPermAtProj_cases_of_ne_reserved
  updateBorrowPermAtProj_nil_eq
  updateBorrowPermAtProj_self_or_disjoint
  invalidateConflictingBorrows_eq_map
  invalidateConflictingBorrowsAtProj_eq_map
  invalidateDerefWriteBorrows_eq_map
  lookupBorrow_map_eq
  PtrLocalOk.of_empty
  PtrLocalOk.of_subsumes
  PtrEnvOk.of_subsumes
  getD_map_range
  PtrEnvOk.of_map_range
  ptrEnvBefore_zero
  ptrEnvBefore_succ
  ptrEnvBefore_of_length_le
  blockPtrAliasOk_getElem?
  ptrStmtOk_of_ptrAliasingOk
  ptrEnvBefore_jump_subsumes
  borrowTargets_map_eq
  ctxWithBorrows_invalidateDerefWriteBorrows
  BorrowsOk.usable_of_not_disabled
  PtrEnvOk.foreignRead
  PtrEnvOk.derefRead
  PtrEnvOk.set_nonptr
  PtrEnvOk.setPtrLocal
  directBorrowOf_eq_none_of_reborrowParentOf
  ptrCopySrcOf_of_ptrRvalueOk
  PtrEnvOk.stepPtrCopy
  statementOk_ref_false_of_scalar
  ptrTargetSpec_bound
  evalTargetPlace_deref
  BorrowsOk.freezeRead
  BorrowsOk.directBorrow
  BorrowsOk.reborrow
  BorrowsOk.derefRead
  evalStmt_assign_pushBorrow
  evalStmt_assign_ref
  evalStmt_assign_rawPtr_reborrow
  evalStmt_assign_ref_reborrow
  evalStmt_assign_ub
  ptrPointeeOf_bind_of_rawPtrPointeeOf
  ptrPointeeOf_bind_of_refPointeeOf
  evalValue_addrOf_of
  evalValue_addrOf_place_ub
  ptrPointeeOf_good
  evalValue_addrOf_ref
  borrowPlaceIntType_of_ptrTargetSpec
  evalStatement_assign_ref_mr
  evalStatement_assign_ub_of
  evalStatement_assign_reborrow_mr
  rawPtrMetaOf_of_rawPtrPointeeOf
  statementOk_ptrRvalueOk_of_rawPtr
  statementOk_ptrRvalueOk_of_ref
  statementOk_ref_spec
  statementOk_rawPtr_reborrow_spec
  statementOk_ref_reborrow_spec
  stmtReadsOk_rawPtr_reborrow
  stmtReadsOk_ref_reborrow
  refSharedRead_inFragment
  refSharedRead_translate
  refSharedRead_anneal_ret
  refSharedRead_noUB
  refSharedRead_minirust_direct
  refSharedRead_ctxOk
  refSharedRead_minirust_ret_from_start
  refSharedRead_minirust_noUB
  refSharedRead_progress
  refMutRoundTrip_inFragment
  refMutRoundTrip_translate
  refMutRoundTrip_anneal_ret
  refMutRoundTrip_noUB
  refMutRoundTrip_minirust_direct
  refMutRoundTrip_ctxOk
  refMutRoundTrip_minirust_ret_from_start
  refMutRoundTrip_minirust_noUB
  refMutRoundTrip_progress
  refArrayReborrowChain_inFragment
  refArrayReborrowChain_translate
  refArrayReborrowChain_anneal_ret
  refArrayReborrowChain_noUB
  refArrayReborrowChain_minirust_direct
  refArrayReborrowChain_ctxOk
  refArrayReborrowChain_minirust_ret_from_start
  refArrayReborrowChain_minirust_noUB
  refArrayReborrowChain_progress
  refPaddedStructReborrow_inFragment
  refPaddedStructReborrow_translate
  refPaddedStructReborrow_anneal_ret
  refPaddedStructReborrow_noUB
  refPaddedStructReborrow_minirust_direct
  refPaddedStructReborrow_ctxOk
  refPaddedStructReborrow_minirust_ret_from_start
  refPaddedStructReborrow_minirust_noUB
  refPaddedStructReborrow_progress
  uninitRefReadUb_inFragment
  uninitRefReadUb_translate
  uninitRefReadUb_anneal_ub
  uninitRefReadUb_ctxOk
  uninitRefReadUb_minirust_ub_from_start
  uninitRefReadUb_converse_error
  uninitRefReadUb_outcome
  uninitRefReadUb_minirust_direct
  uninitRefReborrowUb_inFragment
  uninitRefReborrowUb_translate
  uninitRefReborrowUb_anneal_ub
  uninitRefReborrowUb_ctxOk
  uninitRefReborrowUb_minirust_ub_from_start
  uninitRefReborrowUb_converse_error
  uninitRefReborrowUb_outcome
  uninitRefReborrowUb_minirust_direct
  misalignedRef_notInFragment
  misalignedRef_anneal_ub
  misalignedRef_minirust_direct
  danglingRef_notInFragment
  danglingRef_anneal_ret
  danglingRef_minirust_direct
  checkValue_refTy_safe_ptr_ub
  refTwoPhaseBorrowRoundTrip_inFragment
  refTwoPhaseBorrowRoundTrip_translate
  refTwoPhaseBorrowRoundTrip_anneal_ret
  refTwoPhaseBorrowRoundTrip_noUB
  refTwoPhaseBorrowRoundTrip_minirust_direct
  refTwoPhaseBorrowRoundTrip_ctxOk
  refTwoPhaseBorrowRoundTrip_minirust_ret_from_start
  refTwoPhaseBorrowRoundTrip_minirust_noUB
  refTwoPhaseBorrowRoundTrip_progress
  twoPhaseForeignWriteDiscrepancy_translate
  twoPhaseForeignWriteDiscrepancy_notInFragment
  twoPhaseForeignWriteDiscrepancy_anneal_ub
  twoPhaseForeignWriteDiscrepancy_minirust_direct
  twoPhaseDirectWriteTreeBorrows_translate
  twoPhaseDirectWriteTreeBorrows_notInFragment
  twoPhaseDirectWriteTreeBorrows_anneal_ub
  twoPhaseDirectWriteTreeBorrows_minirust_direct
  frozenRefMutReborrow_notInFragment
  frozenRefMutReborrow_anneal_ub
  frozenRefMutReborrow_minirust_direct
  disabledRefReborrow_notInFragment
  disabledRefReborrow_anneal_ub
  disabledRefReborrow_minirust_direct
  childReborrowWriteDisablesParent_inFragment
  childReborrowWriteDisablesParent_anneal_ret
  childReborrowWriteDisablesParent_minirust_direct
  childReborrowWriteDisablesParent_translate
  childReborrowWriteDisablesParent_noUB
  childReborrowWriteDisablesParent_ctxOk
  childReborrowWriteDisablesParent_minirust_ret_from_start
  childReborrowWriteDisablesParent_minirust_noUB
  childReborrowWriteDisablesParent_progress
  reborrowSettings_u32_examples
  refMutReborrowWrite_inFragment
  refMutReborrowWrite_translate
  refMutReborrowWrite_anneal_ret
  refMutReborrowWrite_noUB
  refMutReborrowWrite_minirust_direct
  refMutReborrowWrite_ctxOk
  refMutReborrowWrite_minirust_ret_from_start
  refMutReborrowWrite_minirust_noUB
  refMutReborrowWrite_progress
  refDisjointReborrowWrite_inFragment
  refDisjointReborrowWrite_translate
  refDisjointReborrowWrite_anneal_ret
  refDisjointReborrowWrite_noUB
  refDisjointReborrowWrite_minirust_direct
  refDisjointReborrowWrite_ctxOk
  refDisjointReborrowWrite_minirust_ret_from_start
  refDisjointReborrowWrite_minirust_noUB
  refDisjointReborrowWrite_progress
  refLoopCountdown_inFragment
  refLoopCountdown_ptrEnvAtEntry_bb3
  refLoopCountdown_translate
  refLoopCountdown_anneal_ret
  refLoopCountdown_noUB
  refLoopCountdown_minirust_direct
  refLoopCountdown_ctxOk
  refLoopCountdown_minirust_ret_from_start
  refLoopCountdown_minirust_noUB
  refLoopCountdown_progress
  refMutDivZeroUb_inFragment
  refMutDivZeroUb_translate
  refMutDivZeroUb_anneal_ub
  refMutDivZeroUb_ctxOk
  refMutDivZeroUb_minirust_ub_from_start
  refMutDivZeroUb_converse_error
  refMutDivZeroUb_outcome
  refMutDivZeroUb_minirust_direct
  transmute_refTy_machine_checks
  validate_refTy_machine_checks
  retagTupleFields_machine_checks
  subsumesPtrLocalState_refl
  subsumesPtrLocalState_disabled_right
  subsumesPtrLocalState_trans
  joinPtrLocalState_subsumes_left
  joinPtrLocalState_subsumes_right
  joinPtrLocalState_least
  subsumesPtrEnv_refl
  subsumesPtrEnv_trans
  subsumesPtrEnv_initPtrEnv
  joinPtrEnv_subsumes_left
  joinPtrEnv_subsumes_right
  joinPtrEnv_least
  subsumesPtrLocalState_getD_of_length
  removePeerFromState_mono
  addPeerToState_mono
  ptrStmtStep_length
  ptrStmtStep_mono
  joinPtrLocalState_wf
  joinPtrLocalState_eq_or_rank_lt
  ptrStmtStep_wf
  iterPtrAliasEntries_stabilizes
  ptrEnvAtEntry_fixed
  terminatorOk_termTargets_lt
  ptrAliasingOk_iff_blockPtrAliasOk
  ptrEnvAtEntry_least
  statementOk_retag_spec
  evalStmt_retag_rawPtr_local
  evalStmt_retag_ref_local
  evalStatement_validate_local_mr
  retagRefReborrowChain_inFragment
  retagRefReborrowChain_translate
  retagRefReborrowChain_anneal_ret
  retagRefReborrowChain_noUB
  retagRefReborrowChain_minirust_direct
  retagRefReborrowChain_ctxOk
  retagRefReborrowChain_minirust_ret_from_start
  retagRefReborrowChain_minirust_noUB
  retagRefReborrowChain_progress
  retagUninitRefUb_inFragment
  retagUninitRefUb_translate
  retagUninitRefUb_anneal_ub
  retagUninitRefUb_ctxOk
  retagUninitRefUb_minirust_ub_from_start
  retagUninitRefUb_converse_error
  retagUninitRefUb_outcome
  retagUninitRefUb_minirust_direct
  retagFnEntryProtectorWrite_translate
  retagFnEntryProtectorWrite_notInFragment
  retagFnEntryProtectorWrite_anneal_ub
  retagFnEntryProtectorWrite_minirust_direct
  retagDisabledRefDiscrepancy_translate
  retagDisabledRefDiscrepancy_inFragment
  retagDisabledRefDiscrepancy_anneal_ret
  retagDisabledRefDiscrepancy_minirust_direct
  retagDisabledRefDiscrepancy_translate_eq
  retagDisabledRefDiscrepancy_noUB
  retagDisabledRefDiscrepancy_ctxOk
  retagDisabledRefDiscrepancy_minirust_ret_from_start
  retagDisabledRefDiscrepancy_minirust_noUB
  retagDisabledRefDiscrepancy_progress
  retagScalarDiscrepancy_translate
  retagScalarDiscrepancy_notInFragment
  retagScalarDiscrepancy_anneal_ret
  retagScalarDiscrepancy_minirust_direct
  transmute_declPtrTy_ok
  evalCastOp_transmute_declPtrTy_ok
  translateTy_of_ptrPointeeOf
  rigidTyByteSize_of_ptrPointeeOf
  encodeValueToBytes_of_ptrPointeeOf
  decodeValueFromBytes_of_ptrPointeeOf
  evalRvalue_transmute_ptr
  refBorrowEntry_cases
  updateBorrowPermAtProj_cases
  BorrowsOk.perm_eq
  ctxWithBorrows_refBorrowEntry_eq
  PermissionUnprot.reserved_foreign_read_eq
  Permission.local_write_activates_unprot_reserved
  Permission.foreign_write_unprot_reserved_iff
  PermissionProt.reserved_foreign_read_blocks_local_write
  PermissionUnprot.prevents_deallocation_false
  PermissionProt.prevents_deallocation_iff
  refRawTransmuteChain_inFragment
  refRawTransmuteChain_translate
  refRawTransmuteChain_anneal_ret
  refRawTransmuteChain_noUB
  refRawTransmuteChain_minirust_direct
  refRawTransmuteChain_ctxOk
  refRawTransmuteChain_minirust_ret_from_start
  refRawTransmuteChain_minirust_noUB
  refRawTransmuteChain_progress
  transmuteUninitRefUb_inFragment
  transmuteUninitRefUb_translate
  transmuteUninitRefUb_anneal_ub
  transmuteUninitRefUb_ctxOk
  transmuteUninitRefUb_minirust_ub_from_start
  transmuteUninitRefUb_converse_error
  transmuteUninitRefUb_outcome
  transmuteUninitRefUb_minirust_direct
  transmuteSharedRefToMutWriteDiscrepancy_translate
  transmuteSharedRefToMutWriteDiscrepancy_notInFragment
  transmuteSharedRefToMutWriteDiscrepancy_anneal_ub
  transmuteSharedRefToMutWriteDiscrepancy_minirust_direct
  transmuteDanglingIntToRefDiscrepancy_translate
  transmuteDanglingIntToRefDiscrepancy_notInFragment
  transmuteDanglingIntToRefDiscrepancy_anneal_ub
  transmuteDanglingIntToRefDiscrepancy_minirust_ub
  treeBorrowsChildWritePreservesParent
  treeBorrowsFrozenAndDisabledUb
  treeBorrowsDirectWriteDisablesUnprotReserved
  treeBorrowsProtectorEndAndDeallocChecks
  PermissionUnprot.foreign_write_ok
  PermissionProt.prevents_deallocation_iff_foreign_write_err
  Permission.prevents_deallocation_iff_foreign_write_err
  Permission.transition_preserves_matches_protector
  ReborrowSettings.perm_matches_protector
  ReborrowSettings.new_matches_protector
  Permission.unprotect_matches_no
  Type.decodeM_bm_eq
  Type.decodeFieldsM_bm_eq
  Type.decodeVariantM_bm_eq
  Type.encodeM_bm_eq
  Type.encodeFieldsM_bm_eq
  Type.encodeVariantM_bm_eq
  checkValueM_bm_eq
  checkFieldsM_bm_eq
  checkVariantM_bm_eq
  mutateCurFrameOutM_retag_bm_eq
  evalPlaceM_bm_eq
  evalValueM_bm_eq
  evalValuesM_bm_eq
  retagValM_bm_eq
  retagTupleFieldsM_bm_eq
  retagArrayElemsM_bm_eq
  evalStatementM_bm_eq
  evalTerminatorM_bm_eq
  stepM_bm_eq
  stepsM_bm_eq
  refSharedRead_tb_direct
  refMutRoundTrip_tb_direct
  refArrayReborrowChain_tb_direct
  refPaddedStructReborrow_tb_direct
  refMutReborrowWrite_tb_direct
  refDisjointReborrowWrite_tb_direct
  refLoopCountdown_tb_direct
  refTwoPhaseBorrowRoundTrip_tb_direct
  retagRefReborrowChain_tb_direct
  refRawTransmuteChain_tb_direct
  uninitRefReadUb_tb_direct
  uninitRefReborrowUb_tb_direct
  refMutDivZeroUb_tb_direct
  retagUninitRefUb_tb_direct
  transmuteUninitRefUb_tb_direct
  directWrite_tb_direct
  frozenWrite_tb_direct
  misalignedRef_tb_direct
  danglingRef_tb_direct
  twoPhaseForeignWriteDiscrepancy_tb_direct
  twoPhaseDirectWriteTreeBorrows_tb_direct
  twoPhaseDirectWriteTreeBorrows_simulation
  frozenRefMutReborrow_tb_direct
  frozenRefMutReborrowWrite_translate
  frozenRefMutReborrowWrite_notInFragment
  frozenRefMutReborrowWrite_anneal_ub
  frozenRefMutReborrowWrite_minirust_direct
  frozenRefMutReborrowWrite_tb_direct
  disabledRefReborrow_tb_direct
  childReborrowWriteDisablesParent_tb_direct
  retagFnEntryProtectorWrite_tb_direct
  retagDisabledRefDiscrepancy_tb_direct
  retagTrulyDisabledRefUb_translate
  retagTrulyDisabledRefUb_notInFragment
  retagTrulyDisabledRefUb_anneal_ub
  retagTrulyDisabledRefUb_minirust_direct
  retagTrulyDisabledRefUb_tb_direct
  retagFnEntryLocalDealloc_translate
  retagFnEntryLocalDealloc_notInFragment
  retagFnEntryLocalDealloc_anneal_ub
  retagFnEntryLocalDealloc_minirust_direct
  retagFnEntryLocalDealloc_tb_direct
  retagFnEntryLocalDealloc_simulation
  retagScalarDiscrepancy_tb_direct
  transmuteSharedRefToMutWriteDiscrepancy_tb_direct
  transmuteDanglingIntToRefDiscrepancy_tb_direct
  misaligned_three_way_ub_agreement
  misalignedRef_three_way_ub_agreement
  transmuteDanglingIntToRefDiscrepancy_three_way_ub_agreement
  misalignedRaw_translate
  misalignedRaw_notInFragment
  misalignedRaw_anneal_ret
  misalignedRaw_three_way_agreement
  rawAddrOfUninit_translate
  rawAddrOfUninit_notInFragment
  rawAddrOfUninit_anneal_ret
  rawAddrOfUninit_three_way_agreement
  transmuteDanglingIntToRawPtrNoDerefOk_translate
  transmuteDanglingIntToRawPtrNoDerefOk_notInFragment
  transmuteDanglingIntToRawPtrNoDerefOk_anneal_ret
  transmuteDanglingIntToRawPtrNoDerefOk_three_way_agreement
  retagRawOnRefLocal_inFragment
  retagRawOnRefLocal_translate
  retagRawOnRefLocal_anneal_ret
  retagRawOnRefLocal_noUB
  retagRawOnRefLocal_minirust_direct
  retagRawOnRefLocal_tb_direct
  retagRawOnRefLocal_ctxOk
  retagRawOnRefLocal_minirust_ret_from_start
  retagRawOnRefLocal_minirust_noUB
  retagRawOnRefLocal_progress
  mutableBorrowPerm_of_sharedBorrowPerm_frozen
  placeIsZeroSized_of_deref_ptrPointeeOf
  IsBorrowAncestorOrSelf.refl
  IsBorrowAncestorOrSelf.of_eq
  IsBorrowAncestorOrSelf.of_descendant
  IsBorrowAncestorOrSelf.step
  isBorrowDescendantOrSelfAux_trans
  IsBorrowAncestorOrSelf.trans
  IsBorrowAncestorOrSelf.of_lookup_sub
  IsBorrowAncestorOrSelf.map_iff
  IsBorrowAncestorOrSelf.cases_of_lookup
  BorrowDagOrdered.map
  BorrowDagOrdered.parent_lt_of_lookup
  isBorrowDescendantOrSelfAux_cons_of_lt
  IsBorrowAncestorOrSelf.cons_of_lt_iff
  BorrowDagOrdered.descendant_of_ancestor
  treeBorrowChainChildAccessUBAux_write_false
  derefWriteTreeUB_false_of_ancestors_writable
  subsumesPtrLocalState_freeze_right
  freezePtrState_mono
  BorrowsOk.entry_perm_cases
  BorrowsOk.ancestors_not_disabled
  BorrowsOk.ancestors_writable
  BorrowsOk.perm_std
  FreezeOrSelf.perm_std
  updateBorrowPermTreeAtProj_perm_std
  BorrowDagOrdered.ancestor_le
  BorrowDagOrdered.anc_sub_cons
  BorrowsOk.freezeRead_dag
  BorrowsOk.reborrow_core
  BorrowsOk.retagRef
  invalidateDerefWriteBorrowsWithLayouts_eq_of_not_union
  hasTreeReadUB_false_of_ancestors_not_disabled
  derefReadTreeUB_false_of_ancestors_not_disabled

open MiniRustSpec.Correspondence MiniRustSpec.Correspondence.PointerWitness MiniRustSpec.Correspondence.RefWitness in
#check_theorem_deps "[REF-AUDIT]"
  ptrPointeeOf_of_rawPtrPointeeOf
  ptrPointeeOf_of_refPointeeOf
  declPtrTy_of_rawPtrPointeeOf
  declPtrTy_of_refPointeeOf
  declPtrTy_of_isRefTy_false
  declPtrTy_of_isRefTy_true
  declPtrTy_cases
  refPointeeOf_good
  AddrOk.nonneg
  layout_refTy
  decode_refTy
  decode_refTy_uninit
  encode_refTy
  inBounds_goodSize
  checkValue_refTy
  checkValue_refTy_null_ub
  checkValue_refTy_unaligned_ub
  checkValue_refTy_dangling_ub
  layout_declPtrTy
  decode_declPtrTy
  decode_declPtrTy_uninit
  encode_declPtrTy
  checkValue_declPtrTy
  tyIsFreeze_of_intTypeOf
  appendProjections_nil_right
  sharedBorrowPerm_of_ptrTargetSpec
  sharedBorrowPerm_of_deref_ptrPointeeOf
  evalRvalue_ref_local
  evalRvalue_rawPtr_reborrow
  evalRvalue_ref_reborrow
  evalRvalue_ref_reborrow_frozen_mut_ub
  evalRvalue_ref_reborrow_disabled_ub
  evalRvalue_rawPtr_reborrow_frozen_mut_ub
  evalRvalue_rawPtr_reborrow_disabled_ub
  evalRvalue_reborrow_ub_of_not_init
  cellsToFreezeMask_nil
  cellsToFreezeMask_single_full
  mapM_replicate_ok
  reborrowSettings_shared_freeze
  reborrowSettings_mut_freeze_default
  reborrowSettings_mut_freeze_fnEntry_noImplicit
  reborrowSettings_mut_freeze_fnEntry_implicitWrite
  reborrowSettings_shared_cell
  reborrowSettings_raw_none
  cm_dereferenceable_offsetPtr
  cm_dereferenceable_of_shape_eq
  typedLoad_local_declPtrTy
  typedLoad_local_declPtrTy_uninit
  typedStore_local_declPtrTy
  typedLoad_ptr_declPtrTy
  typedLoad_ptr_declPtrTy_uninit
  typedStore_ptr_declPtrTy
  directBorrowOf_rawPtr_of_nonDeref
  directBorrowOf_ref_of_nonDeref
  mem_bodyAddrTakenLocals_of_directBorrow
  transmute_refTy_ok
  transmute_refTy_dangling_ub
  evalCastOp_transmute_refTy_ok
  evalCastOp_transmute_refTy_dangling_ub
  retagPtrBM_shape
  retagVal_ptr_shape
  evalStatement_validate_declPtrTy
  borrowProjSteps_stripTransparent
  borrowProjOverlap_borrowProjSteps
  updateBorrowPermAtProj_fields
  updateBorrowPermAtProj_cases_of_ne_reserved
  updateBorrowPermAtProj_nil_eq
  updateBorrowPermAtProj_self_or_disjoint
  invalidateConflictingBorrows_eq_map
  invalidateConflictingBorrowsAtProj_eq_map
  invalidateDerefWriteBorrows_eq_map
  lookupBorrow_map_eq
  PtrLocalOk.of_empty
  PtrLocalOk.of_subsumes
  PtrEnvOk.of_subsumes
  getD_map_range
  PtrEnvOk.of_map_range
  ptrEnvBefore_zero
  ptrEnvBefore_succ
  ptrEnvBefore_of_length_le
  blockPtrAliasOk_getElem?
  ptrStmtOk_of_ptrAliasingOk
  ptrEnvBefore_jump_subsumes
  borrowTargets_map_eq
  ctxWithBorrows_invalidateDerefWriteBorrows
  BorrowsOk.usable_of_not_disabled
  PtrEnvOk.foreignRead
  PtrEnvOk.derefRead
  PtrEnvOk.set_nonptr
  PtrEnvOk.setPtrLocal
  directBorrowOf_eq_none_of_reborrowParentOf
  ptrCopySrcOf_of_ptrRvalueOk
  PtrEnvOk.stepPtrCopy
  statementOk_ref_false_of_scalar
  ptrTargetSpec_bound
  evalTargetPlace_deref
  BorrowsOk.freezeRead
  BorrowsOk.directBorrow
  BorrowsOk.reborrow
  BorrowsOk.derefRead
  evalStmt_assign_pushBorrow
  evalStmt_assign_ref
  evalStmt_assign_rawPtr_reborrow
  evalStmt_assign_ref_reborrow
  evalStmt_assign_ub
  ptrPointeeOf_bind_of_rawPtrPointeeOf
  ptrPointeeOf_bind_of_refPointeeOf
  evalValue_addrOf_of
  evalValue_addrOf_place_ub
  ptrPointeeOf_good
  evalValue_addrOf_ref
  borrowPlaceIntType_of_ptrTargetSpec
  evalStatement_assign_ref_mr
  evalStatement_assign_ub_of
  evalStatement_assign_reborrow_mr
  rawPtrMetaOf_of_rawPtrPointeeOf
  statementOk_ptrRvalueOk_of_rawPtr
  statementOk_ptrRvalueOk_of_ref
  statementOk_ref_spec
  statementOk_rawPtr_reborrow_spec
  statementOk_ref_reborrow_spec
  stmtReadsOk_rawPtr_reborrow
  stmtReadsOk_ref_reborrow
  refSharedRead_inFragment
  refSharedRead_translate
  refSharedRead_anneal_ret
  refSharedRead_noUB
  refSharedRead_minirust_direct
  refSharedRead_ctxOk
  refSharedRead_minirust_ret_from_start
  refSharedRead_minirust_noUB
  refSharedRead_progress
  refMutRoundTrip_inFragment
  refMutRoundTrip_translate
  refMutRoundTrip_anneal_ret
  refMutRoundTrip_noUB
  refMutRoundTrip_minirust_direct
  refMutRoundTrip_ctxOk
  refMutRoundTrip_minirust_ret_from_start
  refMutRoundTrip_minirust_noUB
  refMutRoundTrip_progress
  refArrayReborrowChain_inFragment
  refArrayReborrowChain_translate
  refArrayReborrowChain_anneal_ret
  refArrayReborrowChain_noUB
  refArrayReborrowChain_minirust_direct
  refArrayReborrowChain_ctxOk
  refArrayReborrowChain_minirust_ret_from_start
  refArrayReborrowChain_minirust_noUB
  refArrayReborrowChain_progress
  refPaddedStructReborrow_inFragment
  refPaddedStructReborrow_translate
  refPaddedStructReborrow_anneal_ret
  refPaddedStructReborrow_noUB
  refPaddedStructReborrow_minirust_direct
  refPaddedStructReborrow_ctxOk
  refPaddedStructReborrow_minirust_ret_from_start
  refPaddedStructReborrow_minirust_noUB
  refPaddedStructReborrow_progress
  uninitRefReadUb_inFragment
  uninitRefReadUb_translate
  uninitRefReadUb_anneal_ub
  uninitRefReadUb_ctxOk
  uninitRefReadUb_minirust_ub_from_start
  uninitRefReadUb_converse_error
  uninitRefReadUb_outcome
  uninitRefReadUb_minirust_direct
  uninitRefReborrowUb_inFragment
  uninitRefReborrowUb_translate
  uninitRefReborrowUb_anneal_ub
  uninitRefReborrowUb_ctxOk
  uninitRefReborrowUb_minirust_ub_from_start
  uninitRefReborrowUb_converse_error
  uninitRefReborrowUb_outcome
  uninitRefReborrowUb_minirust_direct
  misalignedRef_notInFragment
  misalignedRef_anneal_ub
  misalignedRef_minirust_direct
  danglingRef_notInFragment
  danglingRef_anneal_ret
  danglingRef_minirust_direct
  checkValue_refTy_safe_ptr_ub
  refTwoPhaseBorrowRoundTrip_inFragment
  refTwoPhaseBorrowRoundTrip_translate
  refTwoPhaseBorrowRoundTrip_anneal_ret
  refTwoPhaseBorrowRoundTrip_noUB
  refTwoPhaseBorrowRoundTrip_minirust_direct
  refTwoPhaseBorrowRoundTrip_ctxOk
  refTwoPhaseBorrowRoundTrip_minirust_ret_from_start
  refTwoPhaseBorrowRoundTrip_minirust_noUB
  refTwoPhaseBorrowRoundTrip_progress
  twoPhaseForeignWriteDiscrepancy_translate
  twoPhaseForeignWriteDiscrepancy_notInFragment
  twoPhaseForeignWriteDiscrepancy_anneal_ub
  twoPhaseForeignWriteDiscrepancy_minirust_direct
  twoPhaseDirectWriteTreeBorrows_translate
  twoPhaseDirectWriteTreeBorrows_notInFragment
  twoPhaseDirectWriteTreeBorrows_anneal_ub
  twoPhaseDirectWriteTreeBorrows_minirust_direct
  frozenRefMutReborrow_notInFragment
  frozenRefMutReborrow_anneal_ub
  frozenRefMutReborrow_minirust_direct
  disabledRefReborrow_notInFragment
  disabledRefReborrow_anneal_ub
  disabledRefReborrow_minirust_direct
  childReborrowWriteDisablesParent_inFragment
  childReborrowWriteDisablesParent_anneal_ret
  childReborrowWriteDisablesParent_minirust_direct
  childReborrowWriteDisablesParent_translate
  childReborrowWriteDisablesParent_noUB
  childReborrowWriteDisablesParent_ctxOk
  childReborrowWriteDisablesParent_minirust_ret_from_start
  childReborrowWriteDisablesParent_minirust_noUB
  childReborrowWriteDisablesParent_progress
  reborrowSettings_u32_examples
  refMutReborrowWrite_inFragment
  refMutReborrowWrite_translate
  refMutReborrowWrite_anneal_ret
  refMutReborrowWrite_noUB
  refMutReborrowWrite_minirust_direct
  refMutReborrowWrite_ctxOk
  refMutReborrowWrite_minirust_ret_from_start
  refMutReborrowWrite_minirust_noUB
  refMutReborrowWrite_progress
  refDisjointReborrowWrite_inFragment
  refDisjointReborrowWrite_translate
  refDisjointReborrowWrite_anneal_ret
  refDisjointReborrowWrite_noUB
  refDisjointReborrowWrite_minirust_direct
  refDisjointReborrowWrite_ctxOk
  refDisjointReborrowWrite_minirust_ret_from_start
  refDisjointReborrowWrite_minirust_noUB
  refDisjointReborrowWrite_progress
  refLoopCountdown_inFragment
  refLoopCountdown_ptrEnvAtEntry_bb3
  refLoopCountdown_translate
  refLoopCountdown_anneal_ret
  refLoopCountdown_noUB
  refLoopCountdown_minirust_direct
  refLoopCountdown_ctxOk
  refLoopCountdown_minirust_ret_from_start
  refLoopCountdown_minirust_noUB
  refLoopCountdown_progress
  refMutDivZeroUb_inFragment
  refMutDivZeroUb_translate
  refMutDivZeroUb_anneal_ub
  refMutDivZeroUb_ctxOk
  refMutDivZeroUb_minirust_ub_from_start
  refMutDivZeroUb_converse_error
  refMutDivZeroUb_outcome
  refMutDivZeroUb_minirust_direct
  transmute_refTy_machine_checks
  validate_refTy_machine_checks
  retagTupleFields_machine_checks
  subsumesPtrLocalState_refl
  subsumesPtrLocalState_disabled_right
  subsumesPtrLocalState_trans
  joinPtrLocalState_subsumes_left
  joinPtrLocalState_subsumes_right
  joinPtrLocalState_least
  subsumesPtrEnv_refl
  subsumesPtrEnv_trans
  subsumesPtrEnv_initPtrEnv
  joinPtrEnv_subsumes_left
  joinPtrEnv_subsumes_right
  joinPtrEnv_least
  subsumesPtrLocalState_getD_of_length
  removePeerFromState_mono
  addPeerToState_mono
  ptrStmtStep_length
  ptrStmtStep_mono
  joinPtrLocalState_wf
  joinPtrLocalState_eq_or_rank_lt
  ptrStmtStep_wf
  iterPtrAliasEntries_stabilizes
  ptrEnvAtEntry_fixed
  terminatorOk_termTargets_lt
  ptrAliasingOk_iff_blockPtrAliasOk
  ptrEnvAtEntry_least
  statementOk_retag_spec
  evalStmt_retag_rawPtr_local
  evalStmt_retag_ref_local
  evalStatement_validate_local_mr
  retagRefReborrowChain_inFragment
  retagRefReborrowChain_translate
  retagRefReborrowChain_anneal_ret
  retagRefReborrowChain_noUB
  retagRefReborrowChain_minirust_direct
  retagRefReborrowChain_ctxOk
  retagRefReborrowChain_minirust_ret_from_start
  retagRefReborrowChain_minirust_noUB
  retagRefReborrowChain_progress
  retagUninitRefUb_inFragment
  retagUninitRefUb_translate
  retagUninitRefUb_anneal_ub
  retagUninitRefUb_ctxOk
  retagUninitRefUb_minirust_ub_from_start
  retagUninitRefUb_converse_error
  retagUninitRefUb_outcome
  retagUninitRefUb_minirust_direct
  retagFnEntryProtectorWrite_translate
  retagFnEntryProtectorWrite_notInFragment
  retagFnEntryProtectorWrite_anneal_ub
  retagFnEntryProtectorWrite_minirust_direct
  retagDisabledRefDiscrepancy_translate
  retagDisabledRefDiscrepancy_inFragment
  retagDisabledRefDiscrepancy_anneal_ret
  retagDisabledRefDiscrepancy_minirust_direct
  retagDisabledRefDiscrepancy_translate_eq
  retagDisabledRefDiscrepancy_noUB
  retagDisabledRefDiscrepancy_ctxOk
  retagDisabledRefDiscrepancy_minirust_ret_from_start
  retagDisabledRefDiscrepancy_minirust_noUB
  retagDisabledRefDiscrepancy_progress
  retagScalarDiscrepancy_translate
  retagScalarDiscrepancy_notInFragment
  retagScalarDiscrepancy_anneal_ret
  retagScalarDiscrepancy_minirust_direct
  transmute_declPtrTy_ok
  evalCastOp_transmute_declPtrTy_ok
  translateTy_of_ptrPointeeOf
  rigidTyByteSize_of_ptrPointeeOf
  encodeValueToBytes_of_ptrPointeeOf
  decodeValueFromBytes_of_ptrPointeeOf
  evalRvalue_transmute_ptr
  refBorrowEntry_cases
  updateBorrowPermAtProj_cases
  BorrowsOk.perm_eq
  ctxWithBorrows_refBorrowEntry_eq
  PermissionUnprot.reserved_foreign_read_eq
  Permission.local_write_activates_unprot_reserved
  Permission.foreign_write_unprot_reserved_iff
  PermissionProt.reserved_foreign_read_blocks_local_write
  PermissionUnprot.prevents_deallocation_false
  PermissionProt.prevents_deallocation_iff
  refRawTransmuteChain_inFragment
  refRawTransmuteChain_translate
  refRawTransmuteChain_anneal_ret
  refRawTransmuteChain_noUB
  refRawTransmuteChain_minirust_direct
  refRawTransmuteChain_ctxOk
  refRawTransmuteChain_minirust_ret_from_start
  refRawTransmuteChain_minirust_noUB
  refRawTransmuteChain_progress
  transmuteUninitRefUb_inFragment
  transmuteUninitRefUb_translate
  transmuteUninitRefUb_anneal_ub
  transmuteUninitRefUb_ctxOk
  transmuteUninitRefUb_minirust_ub_from_start
  transmuteUninitRefUb_converse_error
  transmuteUninitRefUb_outcome
  transmuteUninitRefUb_minirust_direct
  transmuteSharedRefToMutWriteDiscrepancy_translate
  transmuteSharedRefToMutWriteDiscrepancy_notInFragment
  transmuteSharedRefToMutWriteDiscrepancy_anneal_ub
  transmuteSharedRefToMutWriteDiscrepancy_minirust_direct
  transmuteDanglingIntToRefDiscrepancy_translate
  transmuteDanglingIntToRefDiscrepancy_notInFragment
  transmuteDanglingIntToRefDiscrepancy_anneal_ub
  transmuteDanglingIntToRefDiscrepancy_minirust_ub
  treeBorrowsChildWritePreservesParent
  treeBorrowsFrozenAndDisabledUb
  treeBorrowsDirectWriteDisablesUnprotReserved
  treeBorrowsProtectorEndAndDeallocChecks
  PermissionUnprot.foreign_write_ok
  PermissionProt.prevents_deallocation_iff_foreign_write_err
  Permission.prevents_deallocation_iff_foreign_write_err
  Permission.transition_preserves_matches_protector
  ReborrowSettings.perm_matches_protector
  ReborrowSettings.new_matches_protector
  Permission.unprotect_matches_no
  Type.decodeM_bm_eq
  Type.decodeFieldsM_bm_eq
  Type.decodeVariantM_bm_eq
  Type.encodeM_bm_eq
  Type.encodeFieldsM_bm_eq
  Type.encodeVariantM_bm_eq
  checkValueM_bm_eq
  checkFieldsM_bm_eq
  checkVariantM_bm_eq
  mutateCurFrameOutM_retag_bm_eq
  evalPlaceM_bm_eq
  evalValueM_bm_eq
  evalValuesM_bm_eq
  retagValM_bm_eq
  retagTupleFieldsM_bm_eq
  retagArrayElemsM_bm_eq
  evalStatementM_bm_eq
  evalTerminatorM_bm_eq
  stepM_bm_eq
  stepsM_bm_eq
  refSharedRead_tb_direct
  refMutRoundTrip_tb_direct
  refArrayReborrowChain_tb_direct
  refPaddedStructReborrow_tb_direct
  refMutReborrowWrite_tb_direct
  refDisjointReborrowWrite_tb_direct
  refLoopCountdown_tb_direct
  refTwoPhaseBorrowRoundTrip_tb_direct
  retagRefReborrowChain_tb_direct
  refRawTransmuteChain_tb_direct
  uninitRefReadUb_tb_direct
  uninitRefReborrowUb_tb_direct
  refMutDivZeroUb_tb_direct
  retagUninitRefUb_tb_direct
  transmuteUninitRefUb_tb_direct
  directWrite_tb_direct
  frozenWrite_tb_direct
  misalignedRef_tb_direct
  danglingRef_tb_direct
  twoPhaseForeignWriteDiscrepancy_tb_direct
  twoPhaseDirectWriteTreeBorrows_tb_direct
  twoPhaseDirectWriteTreeBorrows_simulation
  frozenRefMutReborrow_tb_direct
  frozenRefMutReborrowWrite_translate
  frozenRefMutReborrowWrite_notInFragment
  frozenRefMutReborrowWrite_anneal_ub
  frozenRefMutReborrowWrite_minirust_direct
  frozenRefMutReborrowWrite_tb_direct
  disabledRefReborrow_tb_direct
  childReborrowWriteDisablesParent_tb_direct
  retagFnEntryProtectorWrite_tb_direct
  retagDisabledRefDiscrepancy_tb_direct
  retagTrulyDisabledRefUb_translate
  retagTrulyDisabledRefUb_notInFragment
  retagTrulyDisabledRefUb_anneal_ub
  retagTrulyDisabledRefUb_minirust_direct
  retagTrulyDisabledRefUb_tb_direct
  retagFnEntryLocalDealloc_translate
  retagFnEntryLocalDealloc_notInFragment
  retagFnEntryLocalDealloc_anneal_ub
  retagFnEntryLocalDealloc_minirust_direct
  retagFnEntryLocalDealloc_tb_direct
  retagFnEntryLocalDealloc_simulation
  retagScalarDiscrepancy_tb_direct
  transmuteSharedRefToMutWriteDiscrepancy_tb_direct
  transmuteDanglingIntToRefDiscrepancy_tb_direct
  misaligned_three_way_ub_agreement
  misalignedRef_three_way_ub_agreement
  transmuteDanglingIntToRefDiscrepancy_three_way_ub_agreement
  misalignedRaw_translate
  misalignedRaw_notInFragment
  misalignedRaw_anneal_ret
  misalignedRaw_three_way_agreement
  rawAddrOfUninit_translate
  rawAddrOfUninit_notInFragment
  rawAddrOfUninit_anneal_ret
  rawAddrOfUninit_three_way_agreement
  transmuteDanglingIntToRawPtrNoDerefOk_translate
  transmuteDanglingIntToRawPtrNoDerefOk_notInFragment
  transmuteDanglingIntToRawPtrNoDerefOk_anneal_ret
  transmuteDanglingIntToRawPtrNoDerefOk_three_way_agreement
  retagRawOnRefLocal_inFragment
  retagRawOnRefLocal_translate
  retagRawOnRefLocal_anneal_ret
  retagRawOnRefLocal_noUB
  retagRawOnRefLocal_minirust_direct
  retagRawOnRefLocal_tb_direct
  retagRawOnRefLocal_ctxOk
  retagRawOnRefLocal_minirust_ret_from_start
  retagRawOnRefLocal_minirust_noUB
  retagRawOnRefLocal_progress
  mutableBorrowPerm_of_sharedBorrowPerm_frozen
  placeIsZeroSized_of_deref_ptrPointeeOf
  IsBorrowAncestorOrSelf.refl
  IsBorrowAncestorOrSelf.of_eq
  IsBorrowAncestorOrSelf.of_descendant
  IsBorrowAncestorOrSelf.step
  isBorrowDescendantOrSelfAux_trans
  IsBorrowAncestorOrSelf.trans
  IsBorrowAncestorOrSelf.of_lookup_sub
  IsBorrowAncestorOrSelf.map_iff
  IsBorrowAncestorOrSelf.cases_of_lookup
  BorrowDagOrdered.map
  BorrowDagOrdered.parent_lt_of_lookup
  isBorrowDescendantOrSelfAux_cons_of_lt
  IsBorrowAncestorOrSelf.cons_of_lt_iff
  BorrowDagOrdered.descendant_of_ancestor
  treeBorrowChainChildAccessUBAux_write_false
  derefWriteTreeUB_false_of_ancestors_writable
  subsumesPtrLocalState_freeze_right
  freezePtrState_mono
  BorrowsOk.entry_perm_cases
  BorrowsOk.ancestors_not_disabled
  BorrowsOk.ancestors_writable
  BorrowsOk.perm_std
  FreezeOrSelf.perm_std
  updateBorrowPermTreeAtProj_perm_std
  BorrowDagOrdered.ancestor_le
  BorrowDagOrdered.anc_sub_cons
  BorrowsOk.freezeRead_dag
  BorrowsOk.reborrow_core
  BorrowsOk.retagRef
  invalidateDerefWriteBorrowsWithLayouts_eq_of_not_union
  hasTreeReadUB_false_of_ancestors_not_disabled
  derefReadTreeUB_false_of_ancestors_not_disabled

open MiniRustSpec.Correspondence MiniRustSpec.Correspondence.TbWitness in
#assert_standard_axioms
  Permission.transition_no_specPanic
  Node.transitionRange_wf
  Node.transitionRange_no_specPanic
  Node.transition_wf
  Node.access_wf
  Node.accessChildren_wf
  Node.access_no_specPanic
  Node.accessChildren_no_specPanic
  reborrow_childPermissions_matches_protector
  Node.access_node_wf
  Node.add_node_wf
  TreeBorrowsMemory.reborrowInitAccess_wf
  TreeBorrowsMemory.new_wf
  TreeBorrowsMemory.allocate_wf
  TreeBorrowsMemory.load_wf
  TreeBorrowsMemory.store_wf
  TreeBorrowsMemory.deallocate_wf
  TreeBorrowsMemory.reborrow_wf
  TreeBorrowsMemory.retag_ptr_wf
  TreeBorrowsMemory.reborrow_nonzst_no_offset_panic
  Node.releaseProtectorPermissions_wf
  Node.release_protector_none_wf
  Node.releaseProtectorChildren_none_wf
  Node.release_protector_some_wf
  Node.releaseProtectorChildren_some_wf
  TreeBorrowsMemory.release_protector_wfLive
  TreeBorrowsMemory.end_call_wfLive
  evalStmt_assign_derefWrite_move
  invalidateDerefWriteBorrows_congr_local
  ptrDerefReadSrc_eq_some
  ptrDerefReadOk_false_of_src_none
  statementOk_derefWrite_derefRead
  stmtReadsOk_derefWrite_derefRead
  stmtReadsOk_derefWrite_of_not_derefRead
  evalStatement_assign_deref_load_eq
  evalStatement_assign_deref_load_ub
  StaleOk.assignDeref
  swapRefs_inFragment
  swapRefs_translate
  swapRefs_anneal_ret
  swapRefs_noUB
  swapRefs_ctxOk
  swapRefs_minirust_ret_from_start
  swapRefs_minirust_noUB
  swapRefs_progress
  swapRefs_minirust_direct
  swapRefs_tb_direct
  derefCopyUninitSrcUb_inFragment
  derefCopyUninitSrcUb_translate
  derefCopyUninitSrcUb_anneal_ub
  derefCopyUninitSrcUb_ctxOk
  derefCopyUninitSrcUb_minirust_ub_from_start
  derefCopyUninitSrcUb_converse_error
  derefCopyUninitSrcUb_outcome_N
  derefCopyUninitSrcUb_minirust_direct
  derefCopyUninitSrcUb_tb_direct
  derefWriteMoveUninitUb_inFragment
  derefWriteMoveUninitUb_translate
  derefWriteMoveUninitUb_anneal_ub
  derefWriteMoveUninitUb_ctxOk
  derefWriteMoveUninitUb_minirust_ub_from_start
  derefWriteMoveUninitUb_converse_error
  derefWriteMoveUninitUb_outcome_N
  derefWriteMoveUninitUb_minirust_direct
  derefWriteMoveUninitUb_tb_direct
  pairSplitReborrowOk_translate
  pairSplitReborrowOk_anneal_ret
  pairSplitReborrowOk_minirust_direct
  pairSplitReborrowOk_tb_direct
  pairParentWriteDisablesChild_translate
  pairParentWriteDisablesChild_anneal_ub
  pairParentWriteDisablesChild_minirust_direct
  pairParentWriteDisablesChild_tb_direct
  unsafeCellUnprotInteriorMut_translate
  unsafeCellUnprotInteriorMut_anneal_ret
  unsafeCellUnprotInteriorMut_minirust_direct
  unsafeCellUnprotInteriorMut_tb_direct
  unsafeCellProtectedInteriorMut_translate
  unsafeCellProtectedInteriorMut_anneal_ret
  unsafeCellProtectedInteriorMut_anneal_noUB
  unsafeCellProtectedInteriorMut_minirust_direct
  unsafeCellProtectedInteriorMut_tb_direct
  unsafeCellProtectedInteriorMut_simulation
  unsafeCellProtectedStorageDead_simulation
  exposeSingleRefMutRoundTrip_translateIntr
  exposeSingleRefMutRoundTrip_anneal_ret
  exposeSingleRefMutRoundTrip_minirust_direct
  exposeSingleRefMutRoundTrip_tb_direct
  exposeSharedRefWriteUb_translateIntr
  exposeSharedRefWriteUb_anneal_ub
  exposeSharedRefWriteUb_minirust_direct
  exposeSharedRefWriteUb_tb_direct
  exposeTwoRefMutAngelicUnsupported_translateIntr
  exposeTwoRefMutAngelicUnsupported_anneal_ret
  exposeTwoRefMutAngelicUnsupported_minirust_direct
  exposeTwoRefMutAngelicUnsupported_tb_direct
  treeBorrowsWeakBoxDeallocAndDeadRelease
  boolMutRefToggle_translate
  boolMutRefToggle_true_three_way
  boolMutRefToggle_false_three_way
  boolInvalidByteRefUb_translate
  boolInvalidByteRefUb_anneal_ub
  boolInvalidByteRefUb_minirust_direct
  boolInvalidByteRefUb_tb_direct
  zstWrappingSubReborrow_bm_ret
  zstWrappingSubReborrow_tb_specPanic
  nonZstWrappingSubReborrow_bm_and_tb_ub
  TreeBorrowsMemory.allocate_no_specPanic
  TreeBorrowsMemory.load_no_specPanic
  TreeBorrowsMemory.store_no_specPanic
  TreeBorrowsMemory.deallocate_no_specPanic
  TreeBorrowsMemory.new_wfLive
  TreeBorrowsMemory.allocate_wfLive
  TreeBorrowsMemory.load_wfLive
  TreeBorrowsMemory.store_wfLive
  TreeBorrowsMemory.deallocate_wfLive
  TreeBorrowsMemory.reborrow_wfLive
  TreeBorrowsMemory.retag_ptr_wfLive
  typedLoadM_tb_wfLive
  typedStoreM_tb_wfLive
  placeLoadM_tb_wfLive
  placeStoreM_tb_wfLive
  evalPlaceM_tb_wfLive
  evalValueM_tb_wfLive
  evalValuesM_tb_wfLive
  storageDeadM_tb_wfLive
  storageLiveM_tb_wfLive
  retagValM_tb_wfLive
  retagTupleFieldsM_tb_wfLive
  retagArrayElemsM_tb_wfLive
  evalStatementM_tb_wfLive
  evalIntrinsicM_tb_wfLive
  evalArgsM_tb_wfLive
  deallocAllM_tb_wfLive
  evalReturnM_tb_wfLive
  evalTerminatorM_tb_wfLive
  stepTB_wfLive
  stepsTB_wfLive
  liftAllocTB_wf
  liftMachToTB_wf
  liftMachToTB_wfLive
  liftMachToTB_stepsTB_wfLive
  startMachineTB_stepsTB_wfLive
  selfDerefCopyOk_inFragment
  selfDerefCopyOk_translate
  selfDerefCopyOk_anneal_ret
  selfDerefCopyOk_noUB
  selfDerefCopyOk_ctxOk
  selfDerefCopyOk_minirust_ret_from_start
  selfDerefCopyOk_minirust_noUB
  selfDerefCopyOk_progress
  selfDerefCopyOk_minirust_direct
  selfDerefCopyOk_tb_direct
  parentDerefCopyDisablesChild_notInFragment
  parentDerefCopyDisablesChild_translate
  parentDerefCopyDisablesChild_anneal_ub
  parentDerefCopyDisablesChild_minirust_direct
  parentDerefCopyDisablesChild_tb_direct
  loopDerefCopyCountdown_inFragment
  loopDerefCopyCountdown_translate
  loopDerefCopyCountdown_anneal_ret
  loopDerefCopyCountdown_noUB
  loopDerefCopyCountdown_ctxOk
  loopDerefCopyCountdown_minirust_ret_from_start
  loopDerefCopyCountdown_minirust_noUB
  loopDerefCopyCountdown_progress
  loopDerefCopyCountdown_minirust_direct
  loopDerefCopyCountdown_tb_direct
  stdOrderingMutRefCmp_translate
  stdOrderingMutRefCmp_five_three_way
  stdOrderingMutRefCmp_twenty_three_way
  unitTupleMutRefRoundTrip_translate
  unitTupleMutRefRoundTrip_three_way
  boolInvalidLoadDirectUb_translate
  boolInvalidLoadDirectUb_three_way_ub
  boolInvalidLoadDirectUb_notInFragment
  boolInvalidLoadDirectUb_valid_three_way_ret
  storageCycleDisablesBorrowUb_notInFragment
  storageCycleDisablesBorrowUb_translate
  storageCycleDisablesBorrowUb_three_way_ub
  derefReadFreezesActiveMutUb_notInFragment
  derefReadFreezesActiveMutUb_translate
  derefReadFreezesActiveMutUb_three_way
  mutReborrowForeignReadRoundTrip_inFragment
  mutReborrowForeignReadRoundTrip_translate
  mutReborrowForeignReadRoundTrip_ctxOk
  mutReborrowForeignReadRoundTrip_anneal_ret
  mutReborrowForeignReadRoundTrip_noUB
  mutReborrowForeignReadRoundTrip_minirust_ret_from_start
  mutReborrowForeignReadRoundTrip_minirust_noUB
  mutReborrowForeignReadRoundTrip_progress
  mutReborrowForeignReadRoundTrip_three_way
  storageLiveReallocDisablesBorrowUb_notInFragment
  storageLiveReallocDisablesBorrowUb_translate
  storageLiveReallocDisablesBorrowUb_three_way_ub

open MiniRustSpec.Correspondence MiniRustSpec.Correspondence.TbWitness in
#check_theorem_deps "[TB-AUDIT]"
  Permission.transition_no_specPanic
  Node.transitionRange_wf
  Node.transitionRange_no_specPanic
  Node.transition_wf
  Node.access_wf
  Node.accessChildren_wf
  Node.access_no_specPanic
  Node.accessChildren_no_specPanic
  reborrow_childPermissions_matches_protector
  Node.access_node_wf
  Node.add_node_wf
  TreeBorrowsMemory.reborrowInitAccess_wf
  TreeBorrowsMemory.new_wf
  TreeBorrowsMemory.allocate_wf
  TreeBorrowsMemory.load_wf
  TreeBorrowsMemory.store_wf
  TreeBorrowsMemory.deallocate_wf
  TreeBorrowsMemory.reborrow_wf
  TreeBorrowsMemory.retag_ptr_wf
  TreeBorrowsMemory.reborrow_nonzst_no_offset_panic
  Node.releaseProtectorPermissions_wf
  Node.release_protector_none_wf
  Node.releaseProtectorChildren_none_wf
  Node.release_protector_some_wf
  Node.releaseProtectorChildren_some_wf
  TreeBorrowsMemory.release_protector_wfLive
  TreeBorrowsMemory.end_call_wfLive
  evalStmt_assign_derefWrite_move
  invalidateDerefWriteBorrows_congr_local
  ptrDerefReadSrc_eq_some
  ptrDerefReadOk_false_of_src_none
  statementOk_derefWrite_derefRead
  stmtReadsOk_derefWrite_derefRead
  stmtReadsOk_derefWrite_of_not_derefRead
  evalStatement_assign_deref_load_eq
  evalStatement_assign_deref_load_ub
  StaleOk.assignDeref
  swapRefs_inFragment
  swapRefs_translate
  swapRefs_anneal_ret
  swapRefs_noUB
  swapRefs_ctxOk
  swapRefs_minirust_ret_from_start
  swapRefs_minirust_noUB
  swapRefs_progress
  swapRefs_minirust_direct
  swapRefs_tb_direct
  derefCopyUninitSrcUb_inFragment
  derefCopyUninitSrcUb_translate
  derefCopyUninitSrcUb_anneal_ub
  derefCopyUninitSrcUb_ctxOk
  derefCopyUninitSrcUb_minirust_ub_from_start
  derefCopyUninitSrcUb_converse_error
  derefCopyUninitSrcUb_outcome_N
  derefCopyUninitSrcUb_minirust_direct
  derefCopyUninitSrcUb_tb_direct
  derefWriteMoveUninitUb_inFragment
  derefWriteMoveUninitUb_translate
  derefWriteMoveUninitUb_anneal_ub
  derefWriteMoveUninitUb_ctxOk
  derefWriteMoveUninitUb_minirust_ub_from_start
  derefWriteMoveUninitUb_converse_error
  derefWriteMoveUninitUb_outcome_N
  derefWriteMoveUninitUb_minirust_direct
  derefWriteMoveUninitUb_tb_direct
  pairSplitReborrowOk_translate
  pairSplitReborrowOk_anneal_ret
  pairSplitReborrowOk_minirust_direct
  pairSplitReborrowOk_tb_direct
  pairParentWriteDisablesChild_translate
  pairParentWriteDisablesChild_anneal_ub
  pairParentWriteDisablesChild_minirust_direct
  pairParentWriteDisablesChild_tb_direct
  unsafeCellUnprotInteriorMut_translate
  unsafeCellUnprotInteriorMut_anneal_ret
  unsafeCellUnprotInteriorMut_minirust_direct
  unsafeCellUnprotInteriorMut_tb_direct
  unsafeCellProtectedInteriorMut_translate
  unsafeCellProtectedInteriorMut_anneal_ret
  unsafeCellProtectedInteriorMut_anneal_noUB
  unsafeCellProtectedInteriorMut_minirust_direct
  unsafeCellProtectedInteriorMut_tb_direct
  unsafeCellProtectedInteriorMut_simulation
  unsafeCellProtectedStorageDead_simulation
  exposeSingleRefMutRoundTrip_translateIntr
  exposeSingleRefMutRoundTrip_anneal_ret
  exposeSingleRefMutRoundTrip_minirust_direct
  exposeSingleRefMutRoundTrip_tb_direct
  exposeSharedRefWriteUb_translateIntr
  exposeSharedRefWriteUb_anneal_ub
  exposeSharedRefWriteUb_minirust_direct
  exposeSharedRefWriteUb_tb_direct
  exposeTwoRefMutAngelicUnsupported_translateIntr
  exposeTwoRefMutAngelicUnsupported_anneal_ret
  exposeTwoRefMutAngelicUnsupported_minirust_direct
  exposeTwoRefMutAngelicUnsupported_tb_direct
  treeBorrowsWeakBoxDeallocAndDeadRelease
  boolMutRefToggle_translate
  boolMutRefToggle_true_three_way
  boolMutRefToggle_false_three_way
  boolInvalidByteRefUb_translate
  boolInvalidByteRefUb_anneal_ub
  boolInvalidByteRefUb_minirust_direct
  boolInvalidByteRefUb_tb_direct
  zstWrappingSubReborrow_bm_ret
  zstWrappingSubReborrow_tb_specPanic
  nonZstWrappingSubReborrow_bm_and_tb_ub
  TreeBorrowsMemory.allocate_no_specPanic
  TreeBorrowsMemory.load_no_specPanic
  TreeBorrowsMemory.store_no_specPanic
  TreeBorrowsMemory.deallocate_no_specPanic
  TreeBorrowsMemory.new_wfLive
  TreeBorrowsMemory.allocate_wfLive
  TreeBorrowsMemory.load_wfLive
  TreeBorrowsMemory.store_wfLive
  TreeBorrowsMemory.deallocate_wfLive
  TreeBorrowsMemory.reborrow_wfLive
  TreeBorrowsMemory.retag_ptr_wfLive
  typedLoadM_tb_wfLive
  typedStoreM_tb_wfLive
  placeLoadM_tb_wfLive
  placeStoreM_tb_wfLive
  evalPlaceM_tb_wfLive
  evalValueM_tb_wfLive
  evalValuesM_tb_wfLive
  storageDeadM_tb_wfLive
  storageLiveM_tb_wfLive
  retagValM_tb_wfLive
  retagTupleFieldsM_tb_wfLive
  retagArrayElemsM_tb_wfLive
  evalStatementM_tb_wfLive
  evalIntrinsicM_tb_wfLive
  evalArgsM_tb_wfLive
  deallocAllM_tb_wfLive
  evalReturnM_tb_wfLive
  evalTerminatorM_tb_wfLive
  stepTB_wfLive
  stepsTB_wfLive
  liftAllocTB_wf
  liftMachToTB_wf
  liftMachToTB_wfLive
  liftMachToTB_stepsTB_wfLive
  startMachineTB_stepsTB_wfLive
  selfDerefCopyOk_inFragment
  selfDerefCopyOk_translate
  selfDerefCopyOk_anneal_ret
  selfDerefCopyOk_noUB
  selfDerefCopyOk_ctxOk
  selfDerefCopyOk_minirust_ret_from_start
  selfDerefCopyOk_minirust_noUB
  selfDerefCopyOk_progress
  selfDerefCopyOk_minirust_direct
  selfDerefCopyOk_tb_direct
  parentDerefCopyDisablesChild_notInFragment
  parentDerefCopyDisablesChild_translate
  parentDerefCopyDisablesChild_anneal_ub
  parentDerefCopyDisablesChild_minirust_direct
  parentDerefCopyDisablesChild_tb_direct
  loopDerefCopyCountdown_inFragment
  loopDerefCopyCountdown_translate
  loopDerefCopyCountdown_anneal_ret
  loopDerefCopyCountdown_noUB
  loopDerefCopyCountdown_ctxOk
  loopDerefCopyCountdown_minirust_ret_from_start
  loopDerefCopyCountdown_minirust_noUB
  loopDerefCopyCountdown_progress
  loopDerefCopyCountdown_minirust_direct
  loopDerefCopyCountdown_tb_direct
  stdOrderingMutRefCmp_translate
  stdOrderingMutRefCmp_five_three_way
  stdOrderingMutRefCmp_twenty_three_way
  unitTupleMutRefRoundTrip_translate
  unitTupleMutRefRoundTrip_three_way
  boolInvalidLoadDirectUb_translate
  boolInvalidLoadDirectUb_three_way_ub
  boolInvalidLoadDirectUb_notInFragment
  boolInvalidLoadDirectUb_valid_three_way_ret
  storageCycleDisablesBorrowUb_notInFragment
  storageCycleDisablesBorrowUb_translate
  storageCycleDisablesBorrowUb_three_way_ub
  derefReadFreezesActiveMutUb_notInFragment
  derefReadFreezesActiveMutUb_translate
  derefReadFreezesActiveMutUb_three_way
  mutReborrowForeignReadRoundTrip_inFragment
  mutReborrowForeignReadRoundTrip_translate
  mutReborrowForeignReadRoundTrip_ctxOk
  mutReborrowForeignReadRoundTrip_anneal_ret
  mutReborrowForeignReadRoundTrip_noUB
  mutReborrowForeignReadRoundTrip_minirust_ret_from_start
  mutReborrowForeignReadRoundTrip_minirust_noUB
  mutReborrowForeignReadRoundTrip_progress
  mutReborrowForeignReadRoundTrip_three_way
  storageLiveReallocDisablesBorrowUb_notInFragment
  storageLiveReallocDisablesBorrowUb_translate
  storageLiveReallocDisablesBorrowUb_three_way_ub

open MiniRustSpec.Interp MiniRustSpec.Correspondence MiniRustSpec.Correspondence.TbWitness
  MiniRustSpec.Correspondence.ProvenanceWitness in
#assert_standard_axioms
  translateStmtOrIntrinsic_expose
  translateStmtOrIntrinsic_withExposed
  translateStmtOrIntrinsic_of_not_provCast
  translateStmtOrIntrinsic_of_translateStatement
  provCastStmtOk_some
  splitBlockAtIntrinsics_no_intrinsics
  splitBlockAtIntrinsics_fresh_eq
  splitBlockAtIntrinsics_length
  splitBlockAtIntrinsics_single_intrinsic
  mapM_translateStmtOrIntrinsic_of_translateStatements
  translateBlocksWithIntrinsics_of_translateBlocks
  translateFnWithIntrinsics_of_translateFn
  inFragment_implies_inFragmentWithIntrinsics
  targetProv_inj
  IntPtrCast.expose_none
  IntPtrCast.expose_some
  IntPtrCast.exposeM_none
  IntPtrCast.exposeM_some
  setContains_iff_mem
  setContains_setInsert_iff
  setInsert_nodup
  IntPtrCast.expose_nodup
  IntPtrCast.exposeM_nodup
  setContains_expose_some_iff
  setContains_exposeM_some_iff
  ExposedTargetOk.toExposedAllocOk
  ProvenanceRel.empty
  ProvenanceRel.expose_none
  ProvenanceRel.expose_some
  ProvenanceRel.exposed_alloc_live
  int2ptrProvenance_empty
  IntPtrCast.int2ptr_empty
  int2ptrProvenanceM_empty
  IntPtrCast.int2ptrM_empty
  int2ptrProvenance_singleton
  IntPtrCast.int2ptr_singleton
  int2ptrProvenanceM_singleton
  IntPtrCast.int2ptrM_singleton
  int2ptrProvenance_multi_unique
  IntPtrCast.int2ptr_multi_unique
  int2ptrProvenanceM_multi_unique
  IntPtrCast.int2ptrM_multi_unique
  int2ptrProvenance_multi_none_unsupported
  IntPtrCast.int2ptr_multi_none_unsupported
  int2ptrProvenanceM_multi_none_unsupported
  int2ptrProvenance_multi_ambiguous_unsupported
  IntPtrCast.int2ptr_multi_ambiguous_unsupported
  int2ptrProvenanceM_multi_ambiguous_unsupported
  mem_int2ptrCandidates_iff
  evalIntrinsic_expose_ok
  evalIntrinsicM_expose_ok
  evalIntrinsic_withExposed_eq
  evalIntrinsic_withExposed_ok
  evalIntrinsic_withExposed_err
  evalIntrinsicM_withExposed_ok
  evalIntrinsicM_withExposed_err
  checkPtr_none_ub
  checkPtr_dead_ub
  evalStmt_assign_expose
  evalStmt_assign_withExposed
  expose_withExposed_roundtrip
  StateRelNProv.empty
  StateRelN.expose_provenance_rel
  StateRelNProv.exposed_target_localPtr
  exposeTwice_translateIntr
  exposeSingleRefMutRoundTrip_inFragmentWithIntrinsics
  exposeSharedRefWriteUb_notInFragmentWithIntrinsics
  exposeTwoRefMutAngelicUnsupported_inFragmentWithIntrinsics
  int2ptrRawRoundTripOk_inFragmentWithIntrinsics
  int2ptrRawRoundTripOk_translateIntr
  int2ptrRawRoundTripOk_minirust_direct
  int2ptrRawRoundTripOk_tb_direct
  int2ptrUnexposedDerefUb_notInFragmentWithIntrinsics
  int2ptrUnexposedDerefUb_translateIntr
  int2ptrUnexposedDerefUb_minirust_direct
  int2ptrUnexposedDerefUb_tb_direct
  int2ptrMultiAllocBoundaryUnsupported_translateIntr
  int2ptrMultiAllocOutOfBounds_bm
  int2ptrAdjacentBoundaryMeeting_bm
  int2ptrDeadAllocDerefUb_translateIntr
  int2ptrDeadAllocDerefUb_minirust_direct
  int2ptrDeadAllocDerefUb_tb_direct
  translateStatement_not_provCast
  mapM_translateStatement_not_provCast
  translateBlocks_not_provCast
  translateFn_not_hasProvCast
  inFragment_not_hasProvCast
  provCastFlowOk_of_not_hasProvCast
  provCastAliasView_of_not_hasProvCast
  mem_int2ptrCandidates
  int2ptrCandidates_mem_of
  int2ptrCandidates_exposed
  setContains_of_elems_eq_singleton
  setContains_of_elems_eq_singleton_self
  int2ptrProvenance_admissible
  IntPtrCast.int2ptr_admissible
  int2ptrProvenance_eq_none_iff
  int2ptrProvenance_error_unsupported
  IntPtrCast.int2ptr_error_unsupported
  exposedInBoundsSound_BM
  mem_tbmExposedInBounds
  exposedInBoundsSound_TBM
  int2ptrProvenanceM_admissible
  int2ptrProvenanceM_admissible_BM
  int2ptrProvenanceM_admissible_TBM
  int2ptrProvenanceM_error_unsupported
  int2ptrProvenanceM_unique
  int2ptrProvenance_unique_cand
  int2ptrProvenance_unique
  checkPtr_ok_some_inv
  checkPtr_none_error
  int2ptr_checkPtr_angelic_optimal
  int2ptr_checkPtr_ub_forced
  int2ptrCandidates_two_boundary
  int2ptrProvenance_boundary_unsupported
  setContains_expose_self_some
  IntPtrCast.int2ptr_expose_empty_roundtrip
  int2ptrCandidates_nodup
  IntPtrCast.int2ptr_of_unique_candidate
  IntPtrCast.int2ptr_expose_unique_roundtrip
  int2ptrProvenanceM_tb_two_tags_unsupported
  inFragmentWithIntrinsics_imp_A1
  exposeTwice_inFragmentWithIntrinsicsA1
  exposeTwice_provCastFlowOk_false
  exposeTwice_notInFragmentWithIntrinsics
  exposeTwice_intr_minirust_direct
  exposeTwice_intr_tb_direct
  exposeTwice_three_way_divergence
  exposeTwice_three_way_agreement
  int2ptrForgedTag_inFragmentWithIntrinsicsA1
  int2ptrForgedTag_notInFragmentWithIntrinsics
  int2ptrForgedTag_anneal_ub
  int2ptrForgedTag_minirust_direct
  int2ptrForgedTag_tb_direct
  int2ptrForgedTag_three_way_divergence
  int2ptrForgedTag_three_way_ub_agreement
  directWrite_inFragmentWithIntrinsicsA1
  directWrite_notInFragmentWithIntrinsics
  directWrite_A1_divergence
  exposeSharedRefWriteUb_inFragmentWithIntrinsicsA1
  exposeSharedRefWriteUb_A1_divergence
  int2ptrRawRoundTripOk_anneal_ret
  int2ptrRoundTripOk_three_way
  int2ptrRawRoundTripOk_annealExposeRoundTripOk
  int2ptrUnexposedDerefUb_anneal_ub
  int2ptrUnexposedUb_three_way
  int2ptrAdjacentArgsAmbiguous_inFragmentWithIntrinsics
  int2ptrAdjacentArgsAmbiguous_anneal_ret
  int2ptrAdjacentArgsAmbiguous_minirust_direct
  int2ptrAdjacentArgsAmbiguous_tb_direct
  int2ptrAdjacentArgsAmbiguous_spaced_minirust_direct
  int2ptrAdjacentArgsAmbiguous_spaced_tb_direct
  int2ptrAmbiguityUnsupported_three_way
  int2ptrAfterStorageDeadUb_translateIntr
  int2ptrAfterStorageDeadUb_notInFragmentWithIntrinsics
  int2ptrAfterStorageDeadUb_anneal_ub
  int2ptrAfterStorageDeadUb_minirust_direct
  int2ptrAfterStorageDeadUb_tb_direct
  int2ptrDeadAllocUb_three_way
  int2ptrDeadAllocDerefUb_notInFragmentWithIntrinsics
  int2ptrDeadAllocDerefUb_inFragmentWithIntrinsicsA1
  int2ptrDeadAllocDerefUb_anneal_ub
  int2ptrDeadAllocDerefUb_three_way
  int2ptrMultiAllocBoundaryUnsupported_notInFragmentWithIntrinsics
  int2ptrMultiAllocBoundaryUnsupported_anneal_ub
  int2ptrMultiAllocBoundaryUnsupported_three_way
  exposedAllLive_of_provenanceRel
  int2ptrDeadAllocDerefUb_exposed_dead
  int2ptrDeadAllocDerefUb_provenanceRel_fails
  int2ptrAfterStorageDeadTwoExposed_three_way
  singleExposeSiteOk_of_not_hasProvCast
  ExposedLocalRel.anneal_roundtrip
  ExposedLocalRel.candidate_mem
  evalArgs_singleton
  evalArgsM_singleton
  evalTerminator_intrinsic_expose_ok
  evalTerminatorM_intrinsic_expose_ok
  evalTerminator_intrinsic_withExposed_ok
  evalTerminator_intrinsic_withExposed_err
  evalTerminatorM_intrinsic_withExposed_ok
  evalTerminatorM_intrinsic_withExposed_err
  interpBind_ok
  listIndex_ok_get
  listSet_ok_eq
  writeSubsliceAtIndex_length
  AllocShapeEq.refl
  AllocShapeEq.trans
  AllocShapeEq.set
  BM.store_shape
  BM.load_shape
  placeStore_shape
  placeLoad_shape
  evalPlace_local_eq
  evalValue_load_local_shape
  jumpToBlock_mem
  ExposedTargetOk.of_shape
  ProvenanceRel.of_shape
  ProvenanceRel.of_advanceStmt
  ProvenanceRel.expose_step
  ProvenanceRel.withExposed_step
  rtState_pending_expose
  rtState_pending_withExposed
  rtState_expose_changes_allocs
  rtState_withExposed_changes_allocs
  passA2_hm4_allocs_unsatisfiable_expose
  passA2_hm4_allocs_unsatisfiable_withExposed
  rtState_expose_subevals_ok
  int2ptr_singleton_offset_checkPtr_optimal
  int2ptrSingletonZstNegOffset_tb_specPanic_vs_none_ok
  int2ptrRawRoundTripOk_singleExposeSiteOk
  exposeSingleRefMutRoundTrip_singleExposeSiteOk
  exposeTwoRefMutAngelicUnsupported_singleExposeSiteOk_false
  exposeTwoRefMutAngelicUnsupported_three_way
  singleExposeSiteOk_imp_acyclic
  ExposedTargetAtAddr.toExposedTargetOk
  ExposedTargetAtAddr.in_bounds
  ExposedTargetAtAddr.of_target_offset
  ExposedTargetAtAddr.of_shape
  copyOp_eq_copy_local_iff
  evalStmt_assign_expose_op
  evalStmt_assign_withExposed_op
  subsliceWithLength_of_writeSubsliceAtIndex
  BM.load_eq
  placeLoad_mem_eq
  evalValue_load_local_eq
  listIndex_set_self
  listSet_set_self
  BM.check_ptr_set_data
  BM.load_of_store
  placeLoad_of_placeStore_int
  placeLoad_of_placeStore_usize
  placeStore_curFrame
  evalValue_load_local_curFrame
  jumpToBlock_curFrame
  evalPlace_local_of_curFrame
  ProvenanceRel.expose_step_synced
  ProvenanceRel.withExposed_step_synced
  ProvenanceRel.expose_then_withExposed_step
  BorrowsOk.target_ptrs_vacuous_of_hasProvCast
  BorrowsOk.exposedTargetAtAddr_of_ptr_slot
  rtState_withExposed_subevals_ok
  rtState_expose_then_withExposed_synced
  exposeLoopSingleSite_countExposeStmts_eq_one
  exposeLoopSingleSite_isAcyclicCfg_false
  exposeLoopSingleSite_singleExposeSiteOk_false
  int2ptrCandidates_shape_back
  ProvenanceRel.expose_then_withExposed_reconstructs
  exposeLoopSingleSite_tb_exposed_singleton
  exposeLoopReborrow_inFragmentWithIntrinsics
  exposeLoopReborrow_singleExposeSiteOk_false
  exposeLoopReborrow_tb_two_tags
  exposeLoopReborrow_tb_unsupported
  exposeLoopReborrow_bm_runs
  exposeLoopReborrow_anneal_no_fault_60
  provCastAliasStmt_directBorrow
  bodyAddrTakenLocals_provCastAliasView
  stmtPreservesAddrTaken_provCastAliasStmt
  inFragmentWithIntrinsics_addrTaken_spec
  AddrTakenTargetsOk.of_start
  AddrTakenTargetsOk.set
  AddrTakenTargetsOk.set_init
  AddrTakenTargetsOk.opPost
  stmtPreservesAddrTaken_assign_dst_not_mem
  BorrowsOk.target_ne_of_stmtPreserves
  translateFnWithIntrinsics_locals
  FrameOkWithIntrinsics.mk'
  FrameOkWithIntrinsics.of_FrameOk
  FrameOkWithIntrinsics.nlocals
  FrameOkWithIntrinsics.slots
  FrameOkWithIntrinsics.decl_localTy
  FrameOkWithIntrinsics.slot_exists
  FrameOkWithIntrinsics.local_ty
  ptrTargetSpec_aligned_and_good
  ptrTargetSpec_valid_withIntrinsics
  evalPtrLoad_withIntrinsics
  placeLoad_active_thread
  evalValue_load_local_preserves_shape
  ProvenanceRel.expose_step_from_frameOk
  ProvenanceRel.withExposed_step_from_frameOk
  ProvenanceRel.expose_then_withExposed_from_frameOk
  int2ptrAdjacentArgsAmbiguous_countExposeStmts_eq_two
  int2ptrAdjacentArgsAmbiguous_singleExposeSiteOk_false
  int2ptrAdjacentArgsAmbiguous_spaced_reconstructs_with_prior_exposure
  translateStmtOrIntrinsic_assume
  termPreservesAddrTaken_call_spec
  progStatementOk_of_statementOk
  translateStmtResultWithIntrinsics_eq_of_not_provCast
  translateStmtResult_not_provCast
  translateFnInProgWithIntrinsics_eq_of_no_provCast
  callArgsOkWithIntrinsics_of_callArgsOk
  callTerminatorOkWithIntrinsics_of_callTerminatorOk
  terminatorInProgOkWithIntrinsics_of_terminatorInProgOk
  LocalsOkA.store_decl
  FrameOkWithIntrinsics.toFrameOk
  FrameOkWithIntrinsics.assume_step
  ProvenanceRel.assume_step_from_frameOk
  assumeReborrowExposeRoundTrip_inFragmentWithIntrinsics
  assumeReborrowExposeRoundTrip_singleExposeSiteOk
  assumeReborrowExposeRoundTrip_anneal_ret
  assumeReborrowExposeRoundTrip_minirust_direct
  assumeReborrowExposeRoundTrip_tb_direct
  assumeReborrowExposeRoundTrip_three_way
  assumeReborrowFalseUb_inFragmentWithIntrinsics
  assumeReborrowFalseUb_anneal_ub
  assumeReborrowFalseUb_minirust_direct
  assumeReborrowFalseUb_tb_direct
  assumeReborrowFalseUb_three_way
  callRefMutProtected_inFragmentWithIntrinsics
  callerRefMutProtectedBadCallDst_notInFragmentWithIntrinsics
  callRefMutProtected_translateProgWithIntrinsics
  callRefMutProtected_anneal_ret
  callRefMutProtectedRoundTrip_mach_and_tb
  callRefMutProtectedRoundTrip_three_way
  callProtectorConflict_inFragmentWithIntrinsics
  callProtectorConflict_translateProgWithIntrinsics
  callProtectorConflict_anneal_ub
  callRefMutProtectorViolation_mach_vs_tb
  callRefMutProtectorViolation_three_way
  callCrossFrameExpose_inFragmentWithIntrinsics
  callCrossFrameExpose_translateProgWithIntrinsics
  callCrossFrameExpose_anneal_ret
  callCrossFrameExposeWithExposed_mach_and_tb
  callCrossFrameExposeWithExposed_three_way
  ptrTermStep_eq_of_not_call
  stepPtrAliasProgEntries_eq_of_no_calls
  iterPtrAliasProgEntries_eq_of_no_calls
  ptrProgEnvAtEntry_eq_of_no_calls
  ptrAliasingProgOk_eq_of_no_calls
  ptrAliasingProgOk_of_scalar
  translateProgFnsWithIntrinsics_eq_of_no_provCast
  translateProgWithIntrinsics_eq_of_no_provCast
  translateFnInProg_not_provCast
  terminatorOk_not_call
  callCalleesOf_eq_nil_of_terminatorOk
  translateFnInProgWithIntrinsics_isSome_of_translateFnWithIntrinsics
  bodyInProgFragment_implies_withIntrinsics
  translateProgWithIntrinsics_eq_of_progInFragment
  progInFragment_implies_progInFragmentWithIntrinsics
  bodyInProgFragmentWithIntrinsics_implies_crossFrameTranslatable
  progInFragmentWithIntrinsics_implies_progCrossFrameTranslatable
  AddrTakenTargetsOk.of_stale
  ProvenanceRel.assume_then_expose_then_withExposed_from_frameOk
  inFragmentWithIntrinsics_implies_progInFragmentWithIntrinsics
  inFragment_implies_progInFragmentWithIntrinsics
  progCrossFrameTranslatable_imp_B3
  progInFragmentWithIntrinsics_imp_B3
  exposeTwice_B3_divergence
  int2ptrForgedTag_B3_divergence
  childReborrowWriteDisablesParent_B3_divergence
  exposeSharedRefWriteUb_B3_divergence
  callerRawPtrRetagFnEntry_anneal_ub
  callerRawPtrRetagFnEntry_B3_divergence
  callerRefMutSilentWrongLocal_anneal_ret
  callerRefMutSilentWrongLocal_simulation
  callerBorrowAcrossScalarCall_anneal_ret
  callerBorrowAcrossScalarCall_simulation
  callerBorrowExposeAndScalarCall_anneal_92
  callerBorrowExposeAndScalarCall_three_way
  progSingleExposeSiteOk_nil
  progInFragment_implies_progSingleExposeSiteOk
  exposeSourceCompatible_iff
  BorrowsOk.ptr_slots_after_expose_withExposed
  ProvenanceRel.assume_then_expose_then_withExposed_usable_from_frameOk
  callerBorrowExposeAndScalarCall_progSingleExposeSiteOk
  callerPrePostCallExpose_anneal_42
  callerPrePostCallExpose_three_way_divergence
  inFragment_implies_progSingleExposeSiteOk
  inFragmentWithIntrinsics_and_singleExpose_implies_prog
  BorrowsOk.after_expose_withExposed
  ProvenanceRel.assume_then_expose_then_withExposed_closed_from_frameOk
  lookupBorrow_split_of_nodup
  BorrowsOk.lookupBorrow_tag_ne_zero
  borrowPlaceByteOffset?_of_ptrTargetSpec
  canonicalLocalAddr_lt_two_pow_64
  NoCompetingExposedBorrow.of_same_or_unexposed
  NoCompetingExposedBorrow.of_unexposed
  AnnealExposeRoundTripOk.of_borrows
  AnnealExposeRoundTripOk.of_structural
  ProvenanceRel.expose_then_withExposed_unexposed_from_frameOk
  ProvenanceRel.assume_then_expose_then_withExposed_closed_unexposed_from_frameOk
  exposeCompetingDisabledParent_annealExposeRoundTripOk
  ExposeTargetSlotOk.of_stale_wholeLocal
  ExposeTargetSlotOk.of_addrTaken_wholeLocal
  canonicalLocalAddr_lt_two_pow_64_iff
  bodyPreservesAddrTaken_iff
  bodyPreservesAddrTaken_of_ptrAliasingOk
  bodyPreservesAddrTaken_of_inFragmentWithIntrinsics
  localDecls_lt_of_inFragmentWithIntrinsics
  movedBefore_not_addrTaken_of_preserves
  StaleOk.addrTaken_eq_of_preserves
  ExposeTargetSlotOk.of_frameOk
  ProvenanceRel.assume_then_expose_then_withExposed_closed_of_inFragmentWithIntrinsics
  int2ptrArraySubPlaceRoundTripOk_inFragmentWithIntrinsics
  int2ptrArraySubPlaceRoundTripOk_anneal_ret
  int2ptrArraySubPlaceRoundTripOk_three_way
  int2ptrArraySubPlaceRoundTripOk_annealExposeRoundTripOk
  int2ptrArraySubPlaceRoundTripOk_subPlace_static
  int2ptrArraySubPlaceRoundTripOk_hsub_static
  callerLoopCallExposeCallee_anneal_79
  callerLoopCallExposeCallee_three_way
  ptrDeclLayoutsOk_of_inFragmentWithIntrinsics
  ptrDeclLayoutsOk_of_inFragment
  bodyBorrowTargetsFitPage_spec
  BorrowsOk.entry_rangeLen_zero
  ptrTargetPlaceSpan_lt_page
  NoCompetingExposedBorrow.of_borrows_distinct
  NoCompetingExposedBorrow.of_distinct_locals_or_lower_perm
  ProvenanceRel.assume_then_expose_then_withExposed_closed_distinct_from_frameOk
  ProvenanceRel.assume_then_expose_then_withExposed_closed_distinct_of_inFragmentWithIntrinsics
  exposePriorOtherLocal_annealExposeRoundTripOk
  shadowedUsizeLayoutDivergence_aliasOk_but_layoutBad
  shadowedUsizeLayoutDivergence_anneal_ub
  shadowedUsizeLayoutDivergence_three_way
  transmuteExposedAddrToRawPtrDerefUb_translateIntr
  transmuteExposedAddrToRawPtrDerefUb_notInFragmentWithIntrinsics
  transmuteExposedAddrToRawPtrDerefUb_anneal_ub
  transmuteExposedAddrToRawPtrDerefUb_three_way
  int2ptrArraySubPlaceRoundTripOk_hsub_page
  CtxSpaced_spec
  ProvenanceRel.int2ptrCandidates_eq_targetProv_of_ctxSpaced
  ProvenanceRel.assume_then_expose_then_withExposed_closed_spaced_of_inFragmentWithIntrinsics
  int2ptrAdjacentArgsAmbiguous_ctxSpaced_iff

open MiniRustSpec.Interp MiniRustSpec.Correspondence MiniRustSpec.Correspondence.TbWitness
  MiniRustSpec.Correspondence.ProvenanceWitness in
#check_theorem_deps "[PROV-AUDIT]"
  translateStmtOrIntrinsic_expose
  translateStmtOrIntrinsic_withExposed
  translateStmtOrIntrinsic_of_not_provCast
  translateStmtOrIntrinsic_of_translateStatement
  provCastStmtOk_some
  splitBlockAtIntrinsics_no_intrinsics
  splitBlockAtIntrinsics_fresh_eq
  splitBlockAtIntrinsics_length
  splitBlockAtIntrinsics_single_intrinsic
  mapM_translateStmtOrIntrinsic_of_translateStatements
  translateBlocksWithIntrinsics_of_translateBlocks
  translateFnWithIntrinsics_of_translateFn
  inFragment_implies_inFragmentWithIntrinsics
  targetProv_inj
  IntPtrCast.expose_none
  IntPtrCast.expose_some
  IntPtrCast.exposeM_none
  IntPtrCast.exposeM_some
  setContains_iff_mem
  setContains_setInsert_iff
  setInsert_nodup
  IntPtrCast.expose_nodup
  IntPtrCast.exposeM_nodup
  setContains_expose_some_iff
  setContains_exposeM_some_iff
  ExposedTargetOk.toExposedAllocOk
  ProvenanceRel.empty
  ProvenanceRel.expose_none
  ProvenanceRel.expose_some
  ProvenanceRel.exposed_alloc_live
  int2ptrProvenance_empty
  IntPtrCast.int2ptr_empty
  int2ptrProvenanceM_empty
  IntPtrCast.int2ptrM_empty
  int2ptrProvenance_singleton
  IntPtrCast.int2ptr_singleton
  int2ptrProvenanceM_singleton
  IntPtrCast.int2ptrM_singleton
  int2ptrProvenance_multi_unique
  IntPtrCast.int2ptr_multi_unique
  int2ptrProvenanceM_multi_unique
  IntPtrCast.int2ptrM_multi_unique
  int2ptrProvenance_multi_none_unsupported
  IntPtrCast.int2ptr_multi_none_unsupported
  int2ptrProvenanceM_multi_none_unsupported
  int2ptrProvenance_multi_ambiguous_unsupported
  IntPtrCast.int2ptr_multi_ambiguous_unsupported
  int2ptrProvenanceM_multi_ambiguous_unsupported
  mem_int2ptrCandidates_iff
  evalIntrinsic_expose_ok
  evalIntrinsicM_expose_ok
  evalIntrinsic_withExposed_eq
  evalIntrinsic_withExposed_ok
  evalIntrinsic_withExposed_err
  evalIntrinsicM_withExposed_ok
  evalIntrinsicM_withExposed_err
  checkPtr_none_ub
  checkPtr_dead_ub
  evalStmt_assign_expose
  evalStmt_assign_withExposed
  expose_withExposed_roundtrip
  StateRelNProv.empty
  StateRelN.expose_provenance_rel
  StateRelNProv.exposed_target_localPtr
  exposeTwice_translateIntr
  exposeSingleRefMutRoundTrip_inFragmentWithIntrinsics
  exposeSharedRefWriteUb_notInFragmentWithIntrinsics
  exposeTwoRefMutAngelicUnsupported_inFragmentWithIntrinsics
  int2ptrRawRoundTripOk_inFragmentWithIntrinsics
  int2ptrRawRoundTripOk_translateIntr
  int2ptrRawRoundTripOk_minirust_direct
  int2ptrRawRoundTripOk_tb_direct
  int2ptrUnexposedDerefUb_notInFragmentWithIntrinsics
  int2ptrUnexposedDerefUb_translateIntr
  int2ptrUnexposedDerefUb_minirust_direct
  int2ptrUnexposedDerefUb_tb_direct
  int2ptrMultiAllocBoundaryUnsupported_translateIntr
  int2ptrMultiAllocOutOfBounds_bm
  int2ptrAdjacentBoundaryMeeting_bm
  int2ptrDeadAllocDerefUb_translateIntr
  int2ptrDeadAllocDerefUb_minirust_direct
  int2ptrDeadAllocDerefUb_tb_direct
  translateStatement_not_provCast
  mapM_translateStatement_not_provCast
  translateBlocks_not_provCast
  translateFn_not_hasProvCast
  inFragment_not_hasProvCast
  provCastFlowOk_of_not_hasProvCast
  provCastAliasView_of_not_hasProvCast
  mem_int2ptrCandidates
  int2ptrCandidates_mem_of
  int2ptrCandidates_exposed
  setContains_of_elems_eq_singleton
  setContains_of_elems_eq_singleton_self
  int2ptrProvenance_admissible
  IntPtrCast.int2ptr_admissible
  int2ptrProvenance_eq_none_iff
  int2ptrProvenance_error_unsupported
  IntPtrCast.int2ptr_error_unsupported
  exposedInBoundsSound_BM
  mem_tbmExposedInBounds
  exposedInBoundsSound_TBM
  int2ptrProvenanceM_admissible
  int2ptrProvenanceM_admissible_BM
  int2ptrProvenanceM_admissible_TBM
  int2ptrProvenanceM_error_unsupported
  int2ptrProvenanceM_unique
  int2ptrProvenance_unique_cand
  int2ptrProvenance_unique
  checkPtr_ok_some_inv
  checkPtr_none_error
  int2ptr_checkPtr_angelic_optimal
  int2ptr_checkPtr_ub_forced
  int2ptrCandidates_two_boundary
  int2ptrProvenance_boundary_unsupported
  setContains_expose_self_some
  IntPtrCast.int2ptr_expose_empty_roundtrip
  int2ptrCandidates_nodup
  IntPtrCast.int2ptr_of_unique_candidate
  IntPtrCast.int2ptr_expose_unique_roundtrip
  int2ptrProvenanceM_tb_two_tags_unsupported
  inFragmentWithIntrinsics_imp_A1
  exposeTwice_inFragmentWithIntrinsicsA1
  exposeTwice_provCastFlowOk_false
  exposeTwice_notInFragmentWithIntrinsics
  exposeTwice_intr_minirust_direct
  exposeTwice_intr_tb_direct
  exposeTwice_three_way_divergence
  exposeTwice_three_way_agreement
  int2ptrForgedTag_inFragmentWithIntrinsicsA1
  int2ptrForgedTag_notInFragmentWithIntrinsics
  int2ptrForgedTag_anneal_ub
  int2ptrForgedTag_minirust_direct
  int2ptrForgedTag_tb_direct
  int2ptrForgedTag_three_way_divergence
  int2ptrForgedTag_three_way_ub_agreement
  directWrite_inFragmentWithIntrinsicsA1
  directWrite_notInFragmentWithIntrinsics
  directWrite_A1_divergence
  exposeSharedRefWriteUb_inFragmentWithIntrinsicsA1
  exposeSharedRefWriteUb_A1_divergence
  int2ptrRawRoundTripOk_anneal_ret
  int2ptrRoundTripOk_three_way
  int2ptrRawRoundTripOk_annealExposeRoundTripOk
  int2ptrUnexposedDerefUb_anneal_ub
  int2ptrUnexposedUb_three_way
  int2ptrAdjacentArgsAmbiguous_inFragmentWithIntrinsics
  int2ptrAdjacentArgsAmbiguous_anneal_ret
  int2ptrAdjacentArgsAmbiguous_minirust_direct
  int2ptrAdjacentArgsAmbiguous_tb_direct
  int2ptrAdjacentArgsAmbiguous_spaced_minirust_direct
  int2ptrAdjacentArgsAmbiguous_spaced_tb_direct
  int2ptrAmbiguityUnsupported_three_way
  int2ptrAfterStorageDeadUb_translateIntr
  int2ptrAfterStorageDeadUb_notInFragmentWithIntrinsics
  int2ptrAfterStorageDeadUb_anneal_ub
  int2ptrAfterStorageDeadUb_minirust_direct
  int2ptrAfterStorageDeadUb_tb_direct
  int2ptrDeadAllocUb_three_way
  int2ptrDeadAllocDerefUb_notInFragmentWithIntrinsics
  int2ptrDeadAllocDerefUb_inFragmentWithIntrinsicsA1
  int2ptrDeadAllocDerefUb_anneal_ub
  int2ptrDeadAllocDerefUb_three_way
  int2ptrMultiAllocBoundaryUnsupported_notInFragmentWithIntrinsics
  int2ptrMultiAllocBoundaryUnsupported_anneal_ub
  int2ptrMultiAllocBoundaryUnsupported_three_way
  exposedAllLive_of_provenanceRel
  int2ptrDeadAllocDerefUb_exposed_dead
  int2ptrDeadAllocDerefUb_provenanceRel_fails
  int2ptrAfterStorageDeadTwoExposed_three_way
  singleExposeSiteOk_of_not_hasProvCast
  ExposedLocalRel.anneal_roundtrip
  ExposedLocalRel.candidate_mem
  evalArgs_singleton
  evalArgsM_singleton
  evalTerminator_intrinsic_expose_ok
  evalTerminatorM_intrinsic_expose_ok
  evalTerminator_intrinsic_withExposed_ok
  evalTerminator_intrinsic_withExposed_err
  evalTerminatorM_intrinsic_withExposed_ok
  evalTerminatorM_intrinsic_withExposed_err
  interpBind_ok
  listIndex_ok_get
  listSet_ok_eq
  writeSubsliceAtIndex_length
  AllocShapeEq.refl
  AllocShapeEq.trans
  AllocShapeEq.set
  BM.store_shape
  BM.load_shape
  placeStore_shape
  placeLoad_shape
  evalPlace_local_eq
  evalValue_load_local_shape
  jumpToBlock_mem
  ExposedTargetOk.of_shape
  ProvenanceRel.of_shape
  ProvenanceRel.of_advanceStmt
  ProvenanceRel.expose_step
  ProvenanceRel.withExposed_step
  rtState_pending_expose
  rtState_pending_withExposed
  rtState_expose_changes_allocs
  rtState_withExposed_changes_allocs
  passA2_hm4_allocs_unsatisfiable_expose
  passA2_hm4_allocs_unsatisfiable_withExposed
  rtState_expose_subevals_ok
  int2ptr_singleton_offset_checkPtr_optimal
  int2ptrSingletonZstNegOffset_tb_specPanic_vs_none_ok
  int2ptrRawRoundTripOk_singleExposeSiteOk
  exposeSingleRefMutRoundTrip_singleExposeSiteOk
  exposeTwoRefMutAngelicUnsupported_singleExposeSiteOk_false
  exposeTwoRefMutAngelicUnsupported_three_way
  singleExposeSiteOk_imp_acyclic
  ExposedTargetAtAddr.toExposedTargetOk
  ExposedTargetAtAddr.in_bounds
  ExposedTargetAtAddr.of_target_offset
  ExposedTargetAtAddr.of_shape
  copyOp_eq_copy_local_iff
  evalStmt_assign_expose_op
  evalStmt_assign_withExposed_op
  subsliceWithLength_of_writeSubsliceAtIndex
  BM.load_eq
  placeLoad_mem_eq
  evalValue_load_local_eq
  listIndex_set_self
  listSet_set_self
  BM.check_ptr_set_data
  BM.load_of_store
  placeLoad_of_placeStore_int
  placeLoad_of_placeStore_usize
  placeStore_curFrame
  evalValue_load_local_curFrame
  jumpToBlock_curFrame
  evalPlace_local_of_curFrame
  ProvenanceRel.expose_step_synced
  ProvenanceRel.withExposed_step_synced
  ProvenanceRel.expose_then_withExposed_step
  BorrowsOk.target_ptrs_vacuous_of_hasProvCast
  BorrowsOk.exposedTargetAtAddr_of_ptr_slot
  rtState_withExposed_subevals_ok
  rtState_expose_then_withExposed_synced
  exposeLoopSingleSite_countExposeStmts_eq_one
  exposeLoopSingleSite_isAcyclicCfg_false
  exposeLoopSingleSite_singleExposeSiteOk_false
  int2ptrCandidates_shape_back
  ProvenanceRel.expose_then_withExposed_reconstructs
  exposeLoopSingleSite_tb_exposed_singleton
  exposeLoopReborrow_inFragmentWithIntrinsics
  exposeLoopReborrow_singleExposeSiteOk_false
  exposeLoopReborrow_tb_two_tags
  exposeLoopReborrow_tb_unsupported
  exposeLoopReborrow_bm_runs
  exposeLoopReborrow_anneal_no_fault_60
  provCastAliasStmt_directBorrow
  bodyAddrTakenLocals_provCastAliasView
  stmtPreservesAddrTaken_provCastAliasStmt
  inFragmentWithIntrinsics_addrTaken_spec
  AddrTakenTargetsOk.of_start
  AddrTakenTargetsOk.set
  AddrTakenTargetsOk.set_init
  AddrTakenTargetsOk.opPost
  stmtPreservesAddrTaken_assign_dst_not_mem
  BorrowsOk.target_ne_of_stmtPreserves
  translateFnWithIntrinsics_locals
  FrameOkWithIntrinsics.mk'
  FrameOkWithIntrinsics.of_FrameOk
  FrameOkWithIntrinsics.nlocals
  FrameOkWithIntrinsics.slots
  FrameOkWithIntrinsics.decl_localTy
  FrameOkWithIntrinsics.slot_exists
  FrameOkWithIntrinsics.local_ty
  ptrTargetSpec_aligned_and_good
  ptrTargetSpec_valid_withIntrinsics
  evalPtrLoad_withIntrinsics
  placeLoad_active_thread
  evalValue_load_local_preserves_shape
  ProvenanceRel.expose_step_from_frameOk
  ProvenanceRel.withExposed_step_from_frameOk
  ProvenanceRel.expose_then_withExposed_from_frameOk
  int2ptrAdjacentArgsAmbiguous_countExposeStmts_eq_two
  int2ptrAdjacentArgsAmbiguous_singleExposeSiteOk_false
  int2ptrAdjacentArgsAmbiguous_spaced_reconstructs_with_prior_exposure
  translateStmtOrIntrinsic_assume
  termPreservesAddrTaken_call_spec
  progStatementOk_of_statementOk
  translateStmtResultWithIntrinsics_eq_of_not_provCast
  translateStmtResult_not_provCast
  translateFnInProgWithIntrinsics_eq_of_no_provCast
  callArgsOkWithIntrinsics_of_callArgsOk
  callTerminatorOkWithIntrinsics_of_callTerminatorOk
  terminatorInProgOkWithIntrinsics_of_terminatorInProgOk
  LocalsOkA.store_decl
  FrameOkWithIntrinsics.toFrameOk
  FrameOkWithIntrinsics.assume_step
  ProvenanceRel.assume_step_from_frameOk
  assumeReborrowExposeRoundTrip_inFragmentWithIntrinsics
  assumeReborrowExposeRoundTrip_singleExposeSiteOk
  assumeReborrowExposeRoundTrip_anneal_ret
  assumeReborrowExposeRoundTrip_minirust_direct
  assumeReborrowExposeRoundTrip_tb_direct
  assumeReborrowExposeRoundTrip_three_way
  assumeReborrowFalseUb_inFragmentWithIntrinsics
  assumeReborrowFalseUb_anneal_ub
  assumeReborrowFalseUb_minirust_direct
  assumeReborrowFalseUb_tb_direct
  assumeReborrowFalseUb_three_way
  callRefMutProtected_inFragmentWithIntrinsics
  callerRefMutProtectedBadCallDst_notInFragmentWithIntrinsics
  callRefMutProtected_translateProgWithIntrinsics
  callRefMutProtected_anneal_ret
  callRefMutProtectedRoundTrip_mach_and_tb
  callRefMutProtectedRoundTrip_three_way
  callProtectorConflict_inFragmentWithIntrinsics
  callProtectorConflict_translateProgWithIntrinsics
  callProtectorConflict_anneal_ub
  callRefMutProtectorViolation_mach_vs_tb
  callRefMutProtectorViolation_three_way
  callCrossFrameExpose_inFragmentWithIntrinsics
  callCrossFrameExpose_translateProgWithIntrinsics
  callCrossFrameExpose_anneal_ret
  callCrossFrameExposeWithExposed_mach_and_tb
  callCrossFrameExposeWithExposed_three_way
  ptrTermStep_eq_of_not_call
  stepPtrAliasProgEntries_eq_of_no_calls
  iterPtrAliasProgEntries_eq_of_no_calls
  ptrProgEnvAtEntry_eq_of_no_calls
  ptrAliasingProgOk_eq_of_no_calls
  ptrAliasingProgOk_of_scalar
  translateProgFnsWithIntrinsics_eq_of_no_provCast
  translateProgWithIntrinsics_eq_of_no_provCast
  translateFnInProg_not_provCast
  terminatorOk_not_call
  callCalleesOf_eq_nil_of_terminatorOk
  translateFnInProgWithIntrinsics_isSome_of_translateFnWithIntrinsics
  bodyInProgFragment_implies_withIntrinsics
  translateProgWithIntrinsics_eq_of_progInFragment
  progInFragment_implies_progInFragmentWithIntrinsics
  bodyInProgFragmentWithIntrinsics_implies_crossFrameTranslatable
  progInFragmentWithIntrinsics_implies_progCrossFrameTranslatable
  AddrTakenTargetsOk.of_stale
  ProvenanceRel.assume_then_expose_then_withExposed_from_frameOk
  inFragmentWithIntrinsics_implies_progInFragmentWithIntrinsics
  inFragment_implies_progInFragmentWithIntrinsics
  progCrossFrameTranslatable_imp_B3
  progInFragmentWithIntrinsics_imp_B3
  exposeTwice_B3_divergence
  int2ptrForgedTag_B3_divergence
  childReborrowWriteDisablesParent_B3_divergence
  exposeSharedRefWriteUb_B3_divergence
  callerRawPtrRetagFnEntry_anneal_ub
  callerRawPtrRetagFnEntry_B3_divergence
  callerRefMutSilentWrongLocal_anneal_ret
  callerRefMutSilentWrongLocal_simulation
  callerBorrowAcrossScalarCall_anneal_ret
  callerBorrowAcrossScalarCall_simulation
  callerBorrowExposeAndScalarCall_anneal_92
  callerBorrowExposeAndScalarCall_three_way
  progSingleExposeSiteOk_nil
  progInFragment_implies_progSingleExposeSiteOk
  exposeSourceCompatible_iff
  BorrowsOk.ptr_slots_after_expose_withExposed
  ProvenanceRel.assume_then_expose_then_withExposed_usable_from_frameOk
  callerBorrowExposeAndScalarCall_progSingleExposeSiteOk
  callerPrePostCallExpose_anneal_42
  callerPrePostCallExpose_three_way_divergence
  inFragment_implies_progSingleExposeSiteOk
  inFragmentWithIntrinsics_and_singleExpose_implies_prog
  BorrowsOk.after_expose_withExposed
  ProvenanceRel.assume_then_expose_then_withExposed_closed_from_frameOk
  lookupBorrow_split_of_nodup
  BorrowsOk.lookupBorrow_tag_ne_zero
  borrowPlaceByteOffset?_of_ptrTargetSpec
  canonicalLocalAddr_lt_two_pow_64
  NoCompetingExposedBorrow.of_same_or_unexposed
  NoCompetingExposedBorrow.of_unexposed
  AnnealExposeRoundTripOk.of_borrows
  AnnealExposeRoundTripOk.of_structural
  ProvenanceRel.expose_then_withExposed_unexposed_from_frameOk
  ProvenanceRel.assume_then_expose_then_withExposed_closed_unexposed_from_frameOk
  exposeCompetingDisabledParent_annealExposeRoundTripOk
  ExposeTargetSlotOk.of_stale_wholeLocal
  ExposeTargetSlotOk.of_addrTaken_wholeLocal
  canonicalLocalAddr_lt_two_pow_64_iff
  bodyPreservesAddrTaken_iff
  bodyPreservesAddrTaken_of_ptrAliasingOk
  bodyPreservesAddrTaken_of_inFragmentWithIntrinsics
  localDecls_lt_of_inFragmentWithIntrinsics
  movedBefore_not_addrTaken_of_preserves
  StaleOk.addrTaken_eq_of_preserves
  ExposeTargetSlotOk.of_frameOk
  ProvenanceRel.assume_then_expose_then_withExposed_closed_of_inFragmentWithIntrinsics
  int2ptrArraySubPlaceRoundTripOk_inFragmentWithIntrinsics
  int2ptrArraySubPlaceRoundTripOk_anneal_ret
  int2ptrArraySubPlaceRoundTripOk_three_way
  int2ptrArraySubPlaceRoundTripOk_annealExposeRoundTripOk
  int2ptrArraySubPlaceRoundTripOk_subPlace_static
  int2ptrArraySubPlaceRoundTripOk_hsub_static
  callerLoopCallExposeCallee_anneal_79
  callerLoopCallExposeCallee_three_way
  ptrDeclLayoutsOk_of_inFragmentWithIntrinsics
  ptrDeclLayoutsOk_of_inFragment
  bodyBorrowTargetsFitPage_spec
  BorrowsOk.entry_rangeLen_zero
  ptrTargetPlaceSpan_lt_page
  NoCompetingExposedBorrow.of_borrows_distinct
  NoCompetingExposedBorrow.of_distinct_locals_or_lower_perm
  ProvenanceRel.assume_then_expose_then_withExposed_closed_distinct_from_frameOk
  ProvenanceRel.assume_then_expose_then_withExposed_closed_distinct_of_inFragmentWithIntrinsics
  exposePriorOtherLocal_annealExposeRoundTripOk
  shadowedUsizeLayoutDivergence_aliasOk_but_layoutBad
  shadowedUsizeLayoutDivergence_anneal_ub
  shadowedUsizeLayoutDivergence_three_way
  transmuteExposedAddrToRawPtrDerefUb_translateIntr
  transmuteExposedAddrToRawPtrDerefUb_notInFragmentWithIntrinsics
  transmuteExposedAddrToRawPtrDerefUb_anneal_ub
  transmuteExposedAddrToRawPtrDerefUb_three_way
  int2ptrArraySubPlaceRoundTripOk_hsub_page
  CtxSpaced_spec
  ProvenanceRel.int2ptrCandidates_eq_targetProv_of_ctxSpaced
  ProvenanceRel.assume_then_expose_then_withExposed_closed_spaced_of_inFragmentWithIntrinsics
  int2ptrAdjacentArgsAmbiguous_ctxSpaced_iff

open MiniRustSpec.Correspondence in
#check_theorem_deps "[WITNESS-AUDIT]"
  CtxOk.of_scalar
  fbCtxU32_ok_u8
  fbCtxU32_ok_u32
  fbCtxU32_ok_u32u32
  fbCtxU8_ok_u8
  fbCtxU8_ok_u8u8
  fbCtxI8_ok_i8i8
  fbRunsTo_sound
  fb_forall_lt_of_all
  fb_forall_mem_of_all
  fb_returnRel_alloc
  fb_minirust_ret
  fb_minirust_of_runsTo
  fbCtlz_inFragment
  fbCtlz_translate
  fbCtlzCaller_translateInProg
  fbCtlz_check
  fbCtlz_anneal_all
  fbCtlz_minirust_all
  fbCtlz128_anneal_ret
  fbCtlz128_noUB
  fbCtlz128_minirust_ret
  fbCtlz128_minirust_direct
  fbCttz_inFragment
  fbCttz_translate
  fbCttzCaller_translateInProg
  fbCttz_check
  fbCttz_anneal_all
  fbCttz_minirust_all
  fbCttz12_anneal_ret
  fbCttz12_noUB
  fbCttz12_minirust_ret
  fbCttz12_minirust_direct
  fbBswap_inFragment
  fbBswap_translate
  fbBswapCaller_translateInProg
  fbBswap_check
  fbBswap_anneal_samples
  fbBswap_minirust_samples
  fbBswapMid_anneal_ret
  fbBswapMid_noUB
  fbBswapMid_minirust_ret
  fbBswapMid_minirust_direct
  fbBitrev_inFragment
  fbBitrev_translate
  fbBitrevCaller_translateInProg
  fbBitrev_check
  fbBitrev_anneal_all
  fbBitrev_minirust_all
  fbBitrev35_anneal_ret
  fbBitrev35_noUB
  fbBitrev35_minirust_ret
  fbBitrev35_minirust_direct
  fbSatAdd_inFragment
  fbSatAdd_translate
  fbSatAddCaller_translateInProg
  fbSatAdd_checkRow
  fbSatAdd_checkGrid
  fbSatAdd_anneal_row
  fbSatAdd_anneal_grid
  fbSatAdd_minirust_row
  fbSatAdd_minirust_grid
  fbSatAddOv_anneal_ret
  fbSatAddOv_noUB
  fbSatAddOv_minirust_ret
  fbSatAddOv_minirust_direct
  fbSatSub_inFragment
  fbSatSub_translate
  fbSatSubCaller_translateInProg
  fbSatSub_checkRow
  fbSatSub_checkCols
  fbSatSub_checkGrid
  fbSatSub_anneal_row
  fbSatSub_anneal_cols
  fbSatSub_anneal_grid
  fbSatSub_minirust_row
  fbSatSub_minirust_cols
  fbSatSub_minirust_grid
  fbSatSubMin_anneal_ret
  fbSatSubMin_noUB
  fbSatSubMin_minirust_ret
  fbSatSubMin_minirust_direct
  fbShl_inFragment
  fbShr_inFragment
  fbShl_translate
  fbShr_translate
  fbShlCaller_translateInProg
  fbShrCaller_translateInProg
  fbShl_checkRow
  fbShl_checkSamples
  fbShr_checkRow
  fbShr_checkSamples
  fbShl_anneal_row
  fbShl_anneal_samples
  fbShr_anneal_row
  fbShr_anneal_samples
  fbShl_minirust_row
  fbShl_minirust_samples
  fbShr_minirust_row
  fbShr_minirust_samples
  fbShl33_anneal_ret
  fbShl33_noUB
  fbShl33_minirust_ret
  fbShl33_minirust_direct
  fbShr63_anneal_ret
  fbShr63_noUB
  fbShr63_minirust_ret
  fbShr63_minirust_direct
  fbBlackBox_inFragment
  fbBlackBox_translate
  fbBlackBoxCaller_translateInProg
  fbBlackBox_runA
  fbBlackBox_argsOk
  fbBlackBox_anneal_all
  fbBlackBox_minirust_all
  fbBlackBoxMid_anneal_ret
  fbBlackBoxMid_noUB
  fbBlackBoxMid_minirust_ret
  fbBlackBoxMid_minirust_direct

open MiniRustSpec.Correspondence in
#check_theorem_deps "[WITNESS-AUDIT]"
  bdNullaryOp_ubChecks_contractChecks
  bdUbChecks_anneal_ret
  bdNullaryOp_translateRvalue
  bdUbChecks_rejected
  bdCopy0_anneal_ret
  bdCopy1_anneal_ret
  bdCopy2_anneal_ret
  bdCopy2_noUB
  bdCopyZeroScalars_step
  bdCopy_translateStatement
  bdCopy_rejected
  bdOffset1_anneal_ret
  bdOffsetNeg1_anneal_ub
  bdOffsetNeg1_not_noUB
  bdOffset_rejected
  bdArithOffset_anneal_ret
  bdMirCallReq_fields
  bdWriteBytes_untracked_unsupported
  bdRawEq_extCall
  bdColdPath_extCall
  bdCtpop_anneal_ret
  bdExactDivI32_anneal_ret
  bdAbort_anneal_abort
  bdExactDiv_param_types
  bdExactDiv_typeArgs_distinct
  bdExactDiv_decode
  bdExactDiv_minirust_i32
  bdExactDiv_minirust_u32
  bdExtCallers_rejected
  countOnesLoop_mod
  evalCountOnes_intFromBits
  evalCountOnes_signedness_indep
  bdColdPath_handled
  bdCtpop_inline
  bdExactDiv_inline
  exactDivHandler_iff_minirust
  bdWriteBytes_untracked_not_noUB
  bdUbChecksCall_anneal_ret
  bdUbChecksCall_handled
  bdUnreach_anneal_ub
  bdUnreach_anneal_fault
  bd_minirust_unreachable_ub
  bdUnreach_rejected
  bdUnreachableTerminator_covered
  bdPolymorphicCallee_rejected
  bdPolymorphicCall_anneal_failClosed
  bdUnmonoParamAliasBody_failClosed
  ctpopLoop_eq_popcountBits
  optScalarIs_iff
  evalLIntrinsic_ctpop_eq_minirust
  evalLIntrinsic_bitops_fallback_correspondence
  lowerIntrinsicKind_boundary_correspondence
  evalIntBinOp_ok_or_ub
  evalBinOp_int_ok_or_ub
  evalLIntrinsic_unchecked_binop_isSome_iff_minirust_ok
  evalLIntrinsic_unchecked_shift_isSome_iff_minirust_ok
  evalLIntrinsic_exactDiv_isSome_iff_minirust_ok
  evalLIntrinsic_threeWayCompare_ordering_tag
  evalLIntrinsic_ubChecks_bool_encoding
  evalLIntrinsic_abort_minirust_correspondence
  evalLIntrinsic_unreachable_minirust_correspondence
  evalLIntrinsic_nonzero_minirust_assume
  minirust_intrinsic_negative_controls
  evalLIntrinsic_bitops_i8_signedness_independent
  leValue_append
  leValue_lt
  leBytes_leValue
  bswapLoop_eq_leValue_reverse
  evalLIntrinsic_bswap_minirust_endianness_all_widths
  leBits_length
  leBitValue_append
  leBitValue_lt
  leBitValue_leBits
  leBits_leBitValue
  bitreverseLoop_eq_leBitValue_reverse
  cttzLoop_eq_takeWhile_leBits
  popcountBits_eq_countP_leBits
  evalLIntrinsic_bitops_symbolic_all_widths
  evalLIntrinsic_unchecked_and_exactDiv_value_iff_minirust
  evalLIntrinsic_saturating_valOf_minirust
  evalLIntrinsic_threeWayCompare_char_minirust
  evalLIntrinsic_sizeOfVal_alignOfVal_minirust_layout
  evalLIntrinsic_panicUnwind_minirust_correspondence
  minirust_bitops_char_and_layout_negative_controls
  minirust_unwind_terminators_supported
  minirust_unwind_concrete_witnesses
  minirust_setDiscriminant_supported
  minirust_setDiscriminant_tagger_order
  minirust_setDiscriminant_accesses_law
  minirust_setDiscriminant_memory_frame_law
  minirust_resumeUnwind_teardown_error
  minirust_unwind_setDiscriminant_step_witness
  minirust_nested_unwind_step_witness
  minirust_tb_call_validate_unwind_protector_step_witness
  minirust_setDiscriminant_field_and_encode_witness
  minirust_unwind_provenance_multithread_step_witness
  minirust_setDiscriminant_load_roundtrip_witness
  evalLIntrinsic_sizeOfVal_alignOfVal_str_minirust_layout
  evalLoweredIntrinsicCall_target_none_minirust_ub
  lintrinsicOp_exhaustive_minirust_classification

/-! ## Projected `Deinit`, `Rvalue::Discriminant`, and the sub-place audit hook

`[DEINIT-AUDIT]` pins the projected-`Deinit` / projected-`Retag` fragment `inFragmentD` of
`Correspondence.DeinitWindow` (its window rules, the one-step correspondence
`step_correspondence_D`, and the whole-execution lifts), the byte-store bridge of
`Correspondence.DeinitLemmas` / `Correspondence.DeinitBridge` (including
`subplace_audit_closure`, whose proof term mentions every Episode 2 theorem of
`Anneal.Mir.AdtAndControl` Section 4 and its Stage-1 `Retag` reconciliation), the Episode 2
lowered-intrinsic ↔ `MiniRustSpec.Interp` bridges of `Correspondence.DeinitBridge`, the audit hooks
`call_intrinsic_audit_closure` (every Episode 2 `.call` / `LIntrinsicOp` / `LCallTable` theorem of
`Anneal.Mir.AdtAndControl`) and `adt_control_residual_audit_closure` (every remaining public
`Anneal.Mir.AdtAndControl` theorem; see `[ADT-AUDIT-COVERAGE]`), the
`Rvalue::Discriminant` lowering and its gating characterizations, and the concrete
projected-`Deinit`, projected-`Retag` (Stage-1 parity and `inFragmentD` admission), and
`Discriminant` witnesses of
`Correspondence.Witness`, including the negative controls. -/

open MiniRustSpec.Correspondence MiniRustSpec.Correspondence.DeinitBridge
  MiniRustSpec.Correspondence.Witness in
#check_theorem_deps "[DEINIT-AUDIT]"
  inFragment_implies_inFragmentD
  inFragmentD_spec
  deinitWindowOk_spec
  blockWindowOk_spec
  holeAt_succ
  step_projDeinit
  reinitOk_spec
  siblingReadOk_spec
  reinitCopyOk_spec
  localCopyWindowOk_spec
  castSiblingReadOk_spec
  reinitBinOpOk_spec
  binOpWindowOk_spec
  evalStatement_reinit_any
  evalStatement_siblingRead_any
  evalStatement_reinitCopy_any
  evalStatement_localCopy_any
  evalStatement_castSiblingRead_any
  evalStatement_reinitBinOp_any
  evalStatement_binOpWindow_any
  step_window_reinit
  step_window_read
  step_window_reinit_copy
  step_window_local_copy
  step_window_cast_read
  step_window_reinit_binop
  step_window_binop_local
  step_correspondence_D
  reaches_rel_D
  run_ret_D
  step_start_D
  run_ret_from_start_D
  mirCall_ret_D
  run_ub_rel_D
  run_ub_D
  run_ub_from_start_D
  steps_error_D
  mirNoUB_safe_D
  steps_outcome_D
  mirNoUB_progress_D
  mirNoUB_diverges_steps_ok_D
  mirNoUB_diverges_rel_from_start_D
  mirCall_ub_D
  mirCall_ub_rel_D
  mirCall_noUB_D
  mirCall_steps_error_D
  mirCall_outcome_D
  mirCall_progress_D
  mirCall_diverges_steps_ok_D
  mirCall_diverges_rel_D
  resolveFieldPath_deinit_unit
  evalStatement_deinit_fieldPath
  spliceAt_eq_self
  evalStmt_deinit_field
  evalStmt_retag_field
  siblingRetagOk_deinitTargetOk
  windowStmtOk_retag
  evalStatement_validate_field_any
  siblingRetagOk_spec
  step_window_retag
  length_toAbstractBytes
  toAbstractBytes_deinitBytes
  evalDeinitPlace_spec_minirust_store_simulation
  paddedDeinitSiblingReinit_anneal_shell_agreement
  subplace_audit_closure
  intTyBytes_intrinsic_props
  evalLIntrinsic_wrapping_eq_minirust
  evalLIntrinsic_unchecked_binop_iff_minirust
  evalLIntrinsic_unchecked_shift_iff_minirust
  evalLIntrinsic_exactDiv_iff_minirust
  evalLIntrinsic_saturating_eq_minirust
  evalLIntrinsic_threeWayCompare_eq_minirust
  evalLIntrinsic_ubChecks_eq_minirust
  evalLIntrinsic_arithOffset_eq_minirust
  evalLoweredTerminator_diverging_intrinsics_correspondence
  call_intrinsic_audit_closure
  adt_control_residual_audit_closure
  translateRvalue_discriminant
  evalValue_orderingDiscrExpr
  evalValue_orderingDiscrExpr_ub
  orderingDiscrExpr_eq_getDiscriminant
  rvalueOk_discriminant_nonOrdering
  rvalueOk_discriminant_proj
  cmpDiscrSwitch_inFragment
  cmpDiscrSwitch_discriminant_statementOk
  cmpDiscrSwitch_translate
  ctxI8_ok_cmpDiscrSwitch
  cmpDiscrLess_anneal_ret
  cmpDiscrLess_noUB
  cmpDiscrLess_minirust_ret_from_start
  cmpDiscrLess_minirust_direct
  cmpDiscrEqual_anneal_ret
  cmpDiscrGreater_anneal_ret
  cmpDiscrGreater_minirust_direct
  statementOk_deinit_proj
  statementOk_retag_proj
  evalStmt_retag_scalar_ub
  evalStmt_retag_scalar_noop
  evalStmt_deinit_proj_deinits
  paddedDeinitRead_not_inFragment
  paddedDeinitRead_translate
  paddedDeinitRead_anneal_ub
  paddedDeinitRead_minirust_ub
  paddedRetagRead_not_inFragment
  paddedRetagRead_translate
  paddedRetagRead_retag_noop
  paddedRetagRead_anneal_noop
  retagVal_int_id
  paddedRetagRead_minirust_ret
  paddedRetagRead_stage1_parity
  paddedDeinitSiblingReinit_not_inFragment
  paddedDeinitSiblingReinit_translate
  paddedDeinitSiblingReinit_anneal_ret
  paddedDeinitSiblingReinit_noUB
  paddedDeinitSiblingReinit_minirust_ret
  deinitSiblingReinit_not_inFragment
  deinitSiblingReinit_translate
  ctxPadded2_ok_u8
  deinitSiblingReinit_ctxOk
  deinitSiblingReinit_argsOk
  deinitSiblingReinitMInit_threads
  deinitSiblingReinitMInit_active
  deinitSiblingReinitMInit_allocs
  deinitSiblingReinit_anneal_ret
  deinitSiblingReinit_anneal_noUB
  deinitSiblingReinit_erased
  deinitSiblingReinit_minirust_direct
  deinitSiblingReinit_minirust_ret_direct
  deinitSiblingReinit_holeAt
  deinitSiblingReinit_minirust_returnRel
  paddedDeinitRead_not_inFragmentD
  paddedRetagRead_inFragmentD
  ctxPadded2_ok_u32
  paddedRetagRead_ctxOk
  paddedRetagRead_argsOk
  paddedRetagRead_anneal_noUB
  paddedRetagRead_minirust_ret_from_start
  paddedRetagRead_minirust_noUB
  paddedDeinitSiblingRetagReinit_inFragmentD
  paddedDeinitSiblingRetagReinit_translate
  paddedDeinitSiblingRetagReinit_anneal_ret
  paddedDeinitSiblingRetagReinit_minirust_ret_from_start
  paddedDeinitRetagHole_not_inFragmentD
  paddedDeinitRetagHole_both_ub
  deinitSiblingReinit_inFragmentD
  deinitSiblingReinit_minirust_ret_from_start
  deinitSiblingReinit_minirust_noUB
  deinitSiblingReinit_minirust_progress
  ctxPadded3_ok_u32
  paddedDeinitSiblingReinit_ctxOk
  paddedDeinitSiblingReinit_argsOk
  ctxPadded2_ok_u8_u32
  deinitSiblingCopyReinit_inFragmentD
  deinitSiblingCopyReinit_not_inFragment
  deinitSiblingCopyReinit_translate
  deinitSiblingCopyReinit_ctxOk
  deinitSiblingCopyReinit_argsOk
  deinitSiblingCopyReinit_anneal_ret
  deinitSiblingCopyReinit_anneal_noUB
  deinitSiblingCopyReinit_minirust_ret_from_start
  deinitSiblingCopyReinit_minirust_noUB
  deinitSiblingReinitUb_inFragmentD
  deinitSiblingReinitUb_translate
  deinitSiblingReinitUb_ctxOk
  deinitSiblingReinitUb_anneal_ub
  deinitSiblingReinitUb_minirust_ub_from_start
  ctxPadded2_ok_u8_u32_u32
  deinitSiblingRelayReinit_inFragmentD
  deinitSiblingRelayReinit_not_inFragment
  deinitSiblingRelayReinit_translate
  deinitSiblingRelayReinit_ctxOk
  deinitSiblingRelayReinit_argsOk
  deinitSiblingRelayReinit_anneal_ret
  deinitSiblingRelayReinit_anneal_noUB
  deinitSiblingRelayReinit_holeAt
  deinitSiblingRelayReinit_minirust_ret_from_start
  deinitSiblingRelayReinit_minirust_noUB
  paddedDeinitSiblingReinit_inFragmentD
  paddedDeinitSiblingReinit_window_rules
  paddedDeinitSiblingReinit_minirust_ret_from_start
  paddedDeinitSiblingReinit_minirust_noUB
  paddedDeinitBinOpDivZero_inFragmentD
  paddedDeinitBinOpDivZero_translate
  paddedDeinitBinOpDivZero_anneal_ub
  paddedDeinitBinOpDivZero_minirust_ub_from_start
  paddedDeinitBinOpDivZero_minirust_ub_direct
  paddedDeinitHoleBinOp_not_inFragmentD
  paddedDeinitHoleBinOp_translate
  paddedDeinitHoleBinOp_both_ub
  paddedDeinitHoleCastRead_not_inFragmentD
  paddedDeinitHoleCastRead_translate
  paddedDeinitHoleCastRead_both_ub
  ctxPadded3_ok_u32_u32
  deinitSiblingBinOpWindowReinit_inFragmentD
  deinitSiblingBinOpWindowReinit_not_inFragment
  deinitSiblingBinOpWindowReinit_translate
  deinitSiblingBinOpWindowReinit_window_rules
  deinitSiblingBinOpWindowReinit_ctxOk
  deinitSiblingBinOpWindowReinit_argsOk
  deinitSiblingBinOpWindowReinit_anneal_ret
  deinitSiblingBinOpWindowReinit_anneal_noUB
  deinitSiblingBinOpWindowReinit_minirust_ret_from_start
  deinitSiblingBinOpWindowReinit_minirust_noUB

/-- Verify that every listed declaration is distinct and strictly `Classical.choice`-free
(depending at most on `propext` and `Quot.sound`). -/
elab "#assert_choice_free " ids:ident* : command => do
  let mut seen : Lean.NameSet := {}
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    if seen.contains n then
      throwError "duplicate declaration {n} in #assert_choice_free"
    seen := seen.insert n
    let axs ← liftCoreM <| Lean.collectAxioms n
    for a in axs do
      unless a == ``propext || a == ``Quot.sound do
        throwError "{n} is not Classical.choice-free: depends on axiom {a}"
  logInfo m!"MiniRustSpec.Audit: verified Classical.choice-freedom for {ids.size} DIV-MR declarations"

section DivMrAuditPins

open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp
open MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.Witness
open MiniRustSpec.Correspondence.PointerWitness
open MiniRustSpec.Correspondence.RefWitness
open MiniRustSpec.Correspondence.TbWitness
open MiniRustSpec.Correspondence.ProvenanceWitness

#assert_choice_free
  callerRefMutSilentWrongLocalMInit
  callerRefMutSilentWrongLocalTBInit
  callerRefMutSilentWrongLocal_simulation
  callerBorrowAcrossScalarCallMInit
  callerBorrowAcrossScalarCallTBInit
  callerBorrowAcrossScalarCall_simulation
  callRefMutProtectedMInit
  callRefMutProtectedRoundTrip_three_way
  twoPhaseDirectWriteTreeBorrows_simulation
  retagFnEntryLocalDealloc_simulation
  unsafeCellProtectedInteriorMut_anneal_noUB
  unsafeCellProtectedInteriorMut_simulation
  unsafeCellProtectedStorageDead_simulation

namespace StatementPins

example :
    progInFragmentWithIntrinsicsB3 callerRefMutSilentWrongLocalMir [calleeReadRefWithLocalMir] = true ∧
    progCrossFrameTranslatable callerRefMutSilentWrongLocalMir [calleeReadRefWithLocalMir] = true ∧
    progInFragmentWithIntrinsics callerRefMutSilentWrongLocalMir [calleeReadRefWithLocalMir] = false ∧
    (∃ tr mem, ReachesRet
      (mirCallTreeWithCallees callerRefMutSilentWrongLocalMir [.scalar ⟨5, 4⟩]
        [calleeReadRefWithLocalMir])
      tr (.normal (.scalar ⟨42, 4⟩, mem))) ∧
    MirNoUBTree
      (mirCallTreeWithCallees callerRefMutSilentWrongLocalMir [.scalar ⟨5, 4⟩]
        [calleeReadRefWithLocalMir]) ∧
    (Interp.steps 13 callerRefMutSilentWrongLocalMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) ∧
    (Interp.stepsTB 13 callerRefMutSilentWrongLocalTBInit).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 42 :=
  callerRefMutSilentWrongLocal_simulation

example :
    ptrAliasingOk callerBorrowAcrossScalarCallMir = true ∧
    ptrAliasingOk calleeScalarAssignLocal1Mir = true ∧
    ptrAliasingProgOk callerBorrowAcrossScalarCallMir = false ∧
    progInFragmentWithIntrinsicsB3 callerBorrowAcrossScalarCallMir [calleeScalarAssignLocal1Mir] = true ∧
    progInFragmentWithIntrinsics callerBorrowAcrossScalarCallMir [calleeScalarAssignLocal1Mir] = false ∧
    (∃ tr mem, ReachesRet
      (mirCallTreeWithCallees callerBorrowAcrossScalarCallMir [.scalar ⟨5, 4⟩]
        [calleeScalarAssignLocal1Mir])
      tr (.normal (.scalar ⟨42, 4⟩, mem))) ∧
    MirNoUBTree
      (mirCallTreeWithCallees callerBorrowAcrossScalarCallMir [.scalar ⟨5, 4⟩]
        [calleeScalarAssignLocal1Mir]) ∧
    (Interp.steps 14 callerBorrowAcrossScalarCallMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) ∧
    (Interp.stepsTB 14 callerBorrowAcrossScalarCallTBInit).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 42 :=
  callerBorrowAcrossScalarCall_simulation

example :
    progInFragment callerRefMutProtectedMir [calleeAdd37RefMutMir] = false ∧
    progCrossFrameTranslatable callerRefMutProtectedMir [calleeAdd37RefMutMir] = true ∧
    progInFragmentWithIntrinsics callerRefMutProtectedMir [calleeAdd37RefMutMir] = false ∧
    translateProgWithIntrinsics callerRefMutProtectedMir [calleeAdd37RefMutMir] =
      some callRefMutProtectedProg ∧
    (∃ tr mem, ReachesRet
      (mirCallTreeWithCallees callerRefMutProtectedMir [.scalar ⟨5, 4⟩] [calleeAdd37RefMutMir])
      tr (.normal (.scalar ⟨84, 4⟩, mem))) ∧
    MirNoUBTree
      (mirCallTreeWithCallees callerRefMutProtectedMir [.scalar ⟨5, 4⟩] [calleeAdd37RefMutMir]) ∧
    (Interp.steps 17 callRefMutProtectedMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 84 }, [1]) ∧
    (Interp.stepsTB 17 callRefMutProtectedTBInit).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 84 :=
  callRefMutProtectedRoundTrip_three_way

example :
    (translateFn twoPhaseDirectWriteTreeBorrows).isSome = true ∧
    inFragment twoPhaseDirectWriteTreeBorrows = false ∧
    (∃ tr u, Reaches (mirTree twoPhaseDirectWriteTreeBorrows
      (initMachineState twoPhaseDirectWriteTreeBorrows [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u) ∧
    retAfter twoPhaseDirectWriteTreeBorrows [.scalar ⟨5, 4⟩] 6 =
      some (some { retAlloc with data := scalarBytes u32 99 }, [1]) ∧
    ubAfterTB twoPhaseDirectWriteTreeBorrows [.scalar ⟨5, 4⟩] 5 =
      some "Tree Borrows: local read of Disabled reference" :=
  twoPhaseDirectWriteTreeBorrows_simulation

example :
    (translateFn retagFnEntryLocalDealloc).isSome = true ∧
    inFragment retagFnEntryLocalDealloc = false ∧
    (∃ tr u, Reaches (mirTree retagFnEntryLocalDealloc
      (initMachineState retagFnEntryLocalDealloc [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u) ∧
    retAfter retagFnEntryLocalDealloc [.scalar ⟨5, 4⟩] 6 =
      some (some { retAlloc with data := scalarBytes u32 5 }, [1]) ∧
    ubAfterTB retagFnEntryLocalDealloc [.scalar ⟨5, 4⟩] 6 =
      some "Tree Borrows: foreign write of protected Frozen reference which had a local read" :=
  retagFnEntryLocalDealloc_simulation

example :
    (translateFn unsafeCellProtectedInteriorMutMir).isSome = true ∧
    (∃ mem, ReachesRet (mirTree unsafeCellProtectedInteriorMutMir
      (initMachineState unsafeCellProtectedInteriorMutMir [initUnsafeCellU32])) []
      (.normal (.scalar ⟨77, 4⟩, mem))) ∧
    MirNoUBTree (mirTree unsafeCellProtectedInteriorMutMir
      (initMachineState unsafeCellProtectedInteriorMutMir [initUnsafeCellU32])) ∧
    retAfter unsafeCellProtectedInteriorMutMir [initUnsafeCellU32] 9 =
      some (some { retAlloc with data := scalarBytes u32 77 }, [1]) ∧
    retAfterTB unsafeCellProtectedInteriorMutMir [initUnsafeCellU32] 9 = tbRetU32 77 :=
  unsafeCellProtectedInteriorMut_simulation

example :
    (translateFn unsafeCellProtectedStorageDeadMir).isSome = true ∧
    (∃ mem, ReachesRet (mirTree unsafeCellProtectedStorageDeadMir
      (initMachineState unsafeCellProtectedStorageDeadMir [initUnsafeCellU32])) []
      (.normal (.scalar ⟨77, 4⟩, mem))) ∧
    MirNoUBTree (mirTree unsafeCellProtectedStorageDeadMir
      (initMachineState unsafeCellProtectedStorageDeadMir [initUnsafeCellU32])) ∧
    retAfter unsafeCellProtectedStorageDeadMir [initUnsafeCellU32] 10 =
      some (some { retAlloc with data := scalarBytes u32 77 }, [1]) ∧
    retAfterTB unsafeCellProtectedStorageDeadMir [initUnsafeCellU32] 10 = tbRetU32 77 :=
  unsafeCellProtectedStorageDead_simulation

end StatementPins

end DivMrAuditPins

section WideSliceDstAuditPins

open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open MiniRustSpec
open MiniRustSpec.Gen
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp
open MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.Witness
open MiniRustSpec.Correspondence.PointerWitness
open MiniRustSpec.Correspondence.RefWitness
open MiniRustSpec.Correspondence.TbWitness
open MiniRustSpec.Correspondence.WideSliceDst

#check_theorem_deps "[WIDE-SLICE-DST-AUDIT]"
  mrWideRawPtr_as_wide_pair_eq
  mrWidePtr_type_layout_eq
  mrSlice_type_layout_eq
  encodeWidePtr_eq_encode_widePairTuple
  checkPtrMetadata_elementCount_iff_anneal_usize
  ptrMetadata_wide_and_thin_lockstep
  translateRvalue_cast_ptrToPtr_wide_to_thin_and_wide
  ptrToPtr_wide_to_thin_and_wide_to_wide_lockstep
  ptrToPtr_wide_to_thin_already_subslice_lockstep
  aggregate_rawPtr_and_to_raw_parts_roundtrip_lockstep
  sizeOfVal_and_alignOfVal_slice_lockstep
  sizeOfVal_and_alignOfVal_str_empty_zst_lockstep
  checkPtr_sliceRef_overflow_ub
  checkPtr_sliceRef_empty_ok
  evalRvalue_len_wide_slice_borrow_and_disabled_contrast
  wideSliceFromRawPartsMetadataRoundTrip_three_way
  wideSliceIndexReadWriteAndOobUb_three_way
  wideSliceTreeBorrowsDisabledVsMetadataOk_three_way
  wideSliceSizeAndAlignOfVal_u32_str_empty_zst_witnesses
  wideSliceIsizeMaxBoundary_and_scalarAddrDivergence_canaries
  compute_size_and_align_slice_eq
  x86_64_valid_size_nat_eq
  computeSize_computeAlign_slice_total
  checkPtr_rawSlice_ok
  sliceSizeOverflow_minirust_ub_locus
  minirust_interp_metadata_unops_exec_and_vtable_unsupported
  div_rawSliceSizeOfVal_isizeMax_anneal_ub_vs_minirust_total
  wideSliceParentWrite_aliasingDivergence_and_metadata_three_way
  WideSliceThinPtrRel.of_ctxWithBorrows
  WideSliceThinPtrRel.inBounds_addr
  WideSliceValRel.checkPtr_rawSlice_ok
  ptrMetadata_wideSliceValRel_lockstep
  ptrToPtr_wideSliceValRel_global_to_from_raw_parts_roundtrip
  ptrToPtr_wideSliceValRel_borrowBacked_subslice_and_retag
  translatePlace_and_translateRvalue_wideSlice_boundary
  wideSliceWitnesses_translateStatement_correspondence
  WideSliceDst.dropValues_eq_drop
  WideSliceDst.takeValues_eq_take
  evalRvalue_len_and_frozen_mut_reborrow_wide_slice
  minirust_evalPlace_index_rawSlice
  evalPlaceRead_index_wide_slice_borrowBacked_lockstep
  checkPtr_sliceRef_null_and_zeroByte_reborrow_divergence
  writeProjectedValue_and_subslice_reborrow_wide_slice
  readProjectedValue_constantIndex_wide_slice_and_saturation

namespace WideSliceDstStatementPins

example (mutbl : MirAst.Mutability) (elemSize : LibSpecr.Size)
    (elemAlign : LibSpecr.Align) (freeze : Bool) :
    PtrType.meta_kind (.Raw .ElementCount) = .ElementCount ∧
    PtrType.meta_kind (sliceRefPtrType mutbl elemSize elemAlign freeze) = .ElementCount ∧
    PtrType.as_wide_pair (.Raw .ElementCount) = some mrWidePairTupleTy ∧
    PtrType.as_wide_pair (sliceRefPtrType mutbl elemSize elemAlign freeze) =
      some mrWidePairTupleTy :=
  mrWideRawPtr_as_wide_pair_eq mutbl elemSize elemAlign freeze

example (mutbl : MirAst.Mutability) (elemSize : LibSpecr.Size)
    (elemAlign : LibSpecr.Align) (freeze : Bool) :
    Type.layout (.Ptr (.Raw .ElementCount)) = .ok (.Sized ⟨16⟩ ⟨8⟩) ∧
    Type.layout (.Ptr (sliceRefPtrType mutbl elemSize elemAlign freeze)) = .ok (.Sized ⟨16⟩ ⟨8⟩) ∧
    Type.layout mrWidePairTupleTy = .ok (.Sized ⟨16⟩ ⟨8⟩) ∧
    2 * layoutPointerBytes emptyLayoutTable = 16 :=
  mrWidePtr_type_layout_eq mutbl elemSize elemAlign freeze

example :
    let u8It : IntType := ⟨.Unsigned, ⟨1⟩⟩
    Type.layout (.Slice (.Int u32)) = .ok (.Slice ⟨4⟩ ⟨4⟩) ∧
    Type.layout (.Slice (.Int u8It)) = .ok (.Slice ⟨1⟩ ⟨1⟩) ∧
    LayoutStrategy.is_sized (.Slice ⟨4⟩ ⟨4⟩) = false ∧
    LayoutStrategy.is_sized (.Slice ⟨1⟩ ⟨1⟩) = false :=
  mrSlice_type_layout_eq

example (thin : Ptr) (len : Int)
    (mutbl : MirAst.Mutability) (elemSize : LibSpecr.Size) (elemAlign : LibSpecr.Align)
    (freeze : Bool) (bytes : List Byte) :
    Type.encode (.Ptr (.Raw .ElementCount)) (mrWidePtrVal thin len) =
      encodeWidePtr .ElementCount (ThinPointer.widen thin (some (.ElementCount len))) ∧
    Type.encode (.Ptr (sliceRefPtrType mutbl elemSize elemAlign freeze))
        (mrWidePtrVal thin len) =
      encodeWidePtr .ElementCount (ThinPointer.widen thin (some (.ElementCount len))) ∧
    Type.decode (.Ptr (.Raw .ElementCount)) bytes = decodeWidePtr .ElementCount bytes ∧
    Type.decode (.Ptr (sliceRefPtrType mutbl elemSize elemAlign freeze)) bytes =
      decodeWidePtr .ElementCount bytes ∧
    (∀ thinBytes metaBytes,
      encodePtr thin = .ok thinBytes →
      thinBytes.length = 8 →
      Type.encodeInt IntType.usize_ty (.Int len) = .ok metaBytes →
      metaBytes.length = 8 →
      encodeWidePtr .ElementCount (ThinPointer.widen thin (some (.ElementCount len))) =
        .ok (thinBytes ++ metaBytes) ∧
      Type.encode mrWidePairTupleTy (.Tuple [.Ptr (ThinPointer.widen thin none), .Int len]) =
        .ok (thinBytes ++ metaBytes)) :=
  encodeWidePtr_eq_encode_widePairTuple thin len mutbl elemSize elemAlign freeze bytes

example (len : Nat) :
    (checkPtrMetadata (some (.ElementCount (Int.ofNat len))) .ElementCount = .ok () ↔
      len < scalarModulus 8) ∧
    (scalarModulus 8 ≤ len →
      checkPtrMetadata (some (.ElementCount (Int.ofNat len))) .ElementCount =
        .error (.ub "Value::Int: invalid integer value")) ∧
    checkPtrMetadata none .ElementCount = .error (.ub "Value::Ptr: invalid metadata") ∧
    checkPtrMetadata (some (.ElementCount (Int.ofNat len))) .None =
      .error (.ub "Value::Ptr: invalid metadata") :=
  checkPtrMetadata_elementCount_iff_anneal_usize len

example
    (locals locals' : List LocalSlot) (wideOp scalarWideOp thinOp : Operand)
    (mem : MirSemantics.Memory) (localDecls : List MirAst.LocalDecl)
    (p : ProvenancePtr) (thin : Ptr) (addr len : Nat)
    (hWideOp : evalOperand locals wideOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok (annealWidePtrVal p len 8) locals')
    (hScalarTy : isNonWidePtrAggregateTy (operandTy localDecls emptyLayoutTable scalarWideOp) =
      false)
    (hLen : len < scalarModulus 8)
    (hScalarOp : evalOperand locals scalarWideOp mem.borrows mem.globals emptyLayoutTable
      mem.callerLocals localDecls mem.callStack = .ok (annealWideScalarPtrVal addr len 8) locals')
    (hThinOp : evalOperand locals thinOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok (.ptr p 8) locals') :
    (evalRvalue locals (.unaryOp .ptrMetadata wideOp) mem localDecls emptyLayoutTable =
       .ok (.scalar ⟨len, 8⟩) locals' mem ∧
     PointerMetaKind.encode_as_value .ElementCount
         (ThinPointer.widen thin (some (.ElementCount (Int.ofNat len)))).metadata =
       .ok (.Int (Int.ofNat len))) ∧
    (evalRvalue locals (.unaryOp .ptrMetadata scalarWideOp) mem localDecls emptyLayoutTable =
       .ok (.scalar ⟨len, 8⟩) locals' mem ∧
     PointerMetaKind.encode_as_value .ElementCount (some (.ElementCount (Int.ofNat len))) =
       .ok (.Int (Int.ofNat len))) ∧
    (evalRvalue locals (.unaryOp .ptrMetadata thinOp) mem localDecls emptyLayoutTable =
       .ok .unit locals' mem ∧
     PointerMetaKind.encode_as_value .None none = .ok (.Tuple [])) :=
  ptrMetadata_wide_and_thin_lockstep
    locals locals' wideOp scalarWideOp thinOp mem localDecls p thin addr len
    hWideOp hScalarTy hLen hScalarOp hThinOp

example
    (layouts : LayoutTable) (decls : List MirAst.LocalDecl) (i : Nat) (d : MirAst.LocalDecl)
    (thinCastTy wideCastTy : Ty)
    (hDecl : decls[i]? = some d)
    (hSrcMeta : rawPtrMetaOf d.ty = some .ElementCount)
    (hThinMeta : rawPtrMetaOf thinCastTy = some .None)
    (hWideMeta : rawPtrMetaOf wideCastTy = some .ElementCount) :
    translateRvalue layouts decls none (.cast .ptrToPtr (.copy (local_ i)) thinCastTy) =
      some (.UnOp .GetThinPointer (.Load (.Local (localName i)))) ∧
    translateRvalue layouts decls none (.cast .ptrToPtr (.copy (local_ i)) wideCastTy) =
      some (.Load (.Local (localName i))) :=
  translateRvalue_cast_ptrToPtr_wide_to_thin_and_wide
    layouts decls i d thinCastTy wideCastTy hDecl hSrcMeta hThinMeta hWideMeta

example
    (locals locals' : List LocalSlot) (op : Operand) (thinTargetTy wideTargetTy : Ty)
    (mem : MirSemantics.Memory) (localDecls : List MirAst.LocalDecl)
    (p : ProvenancePtr) (len : Nat) (thin : Ptr)
    (thinTB : ThinPointer TreeBorrowsProvenance) (ptrTy : PtrType)
    (hThin : isThinRawPtrTy thinTargetTy = true)
    (hNotThin : isThinRawPtrTy wideTargetTy = false)
    (hWide : wideRawPtrIsDyn? wideTargetTy = some false)
    (hOp : evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok (annealWidePtrVal p len 8) locals') :
    ((lookupBorrow mem.borrows p.tag = none →
        evalRvalue locals (.cast .ptrToPtr op thinTargetTy) mem localDecls emptyLayoutTable =
          .ok (.ptr p 8) locals' mem) ∧
     evalUnOp .GetThinPointer (mrWidePtrVal thin (Int.ofNat len), .Ptr ptrTy) =
       .ok (.Ptr (ThinPointer.widen thin none), .Ptr (.Raw .None)) ∧
     evalUnOpM (M := TBM) .GetThinPointer (mrWidePtrValM thinTB (Int.ofNat len), .Ptr ptrTy) =
       .ok (.Ptr (ThinPointer.widen thinTB none), .Ptr (.Raw .None))) ∧
    evalRvalue locals (.cast .ptrToPtr op wideTargetTy) mem localDecls emptyLayoutTable =
      .ok (annealWidePtrVal p len 8) locals' mem :=
  ptrToPtr_wide_to_thin_and_wide_to_wide_lockstep
    locals locals' op thinTargetTy wideTargetTy mem localDecls p len thin thinTB ptrTy
    hThin hNotThin hWide hOp

example
    (locals locals' : List LocalSlot) (op : Operand) (thinTargetTy : Ty)
    (mem : MirSemantics.Memory) (localDecls : List MirAst.LocalDecl)
    (p : ProvenancePtr) (len : Nat) (parentEntry : BorrowEntry) (rootVal : MirSemantics.Value)
    (containerProj : List ProjectionElem) (baseIdx : Nat) (elems : List MirSemantics.Value)
    (rawElemOffset : Nat) (thin : Ptr) (thinTB : ThinPointer TreeBorrowsProvenance)
    (ptrTy : PtrType)
    (hThin : isThinRawPtrTy thinTargetTy = true)
    (hOp : evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok (annealWidePtrVal p len 8) locals')
    (hBorrow : lookupBorrow mem.borrows p.tag = some parentEntry)
    (hPerm : parentEntry.perm ≠ .disabled)
    (hRoot : activeFrameSlot? locals' mem.callStack parentEntry.targetFrameDepth
      parentEntry.targetLocal = some (.init rootVal))
    (hRead : readSliceBackingAggregate? locals' rootVal
      (normalizeSubsliceProjections (stripTransparentProjections parentEntry.targetProjection))
      len = some (containerProj, baseIdx, elems))
    (hOff : byteOffsetToElemIdx? p.offsetBytes (inferElemListByteStride elems) =
      some rawElemOffset)
    (hBound : Nat.ble (Nat.add (Nat.add rawElemOffset baseIdx) len) (Trusted.Sequence.length elems) = true)
    (hAlready : Bool.and (endsWithSubslice containerProj)
      (Bool.and (Nat.beq (Nat.add rawElemOffset baseIdx) 0) (Nat.beq len (Trusted.Sequence.length elems))) =
        true) :
    evalRvalue locals (.cast .ptrToPtr op thinTargetTy) mem localDecls emptyLayoutTable =
      .ok (.ptr p 8) locals' mem ∧
    evalUnOp .GetThinPointer (mrWidePtrVal thin (Int.ofNat len), .Ptr ptrTy) =
      .ok (.Ptr (ThinPointer.widen thin none), .Ptr (.Raw .None)) ∧
    evalUnOpM (M := TBM) .GetThinPointer (mrWidePtrValM thinTB (Int.ofNat len), .Ptr ptrTy) =
      .ok (.Ptr (ThinPointer.widen thinTB none), .Ptr (.Raw .None)) :=
  ptrToPtr_wide_to_thin_already_subslice_lockstep
    locals locals' op thinTargetTy mem localDecls p len parentEntry rootVal
    containerProj baseIdx elems rawElemOffset thin thinTB ptrTy
    hThin hOp hBorrow hPerm hRoot hRead hOff hBound hAlready

example
    (locals locals₁ locals₂ : List LocalSlot) (pointeeTy : Ty) (mutability : MirAst.Mutability)
    (dataOp metaOp : Operand) (mem : MirSemantics.Memory) (localDecls : List MirAst.LocalDecl)
    (p : ProvenancePtr) (len : Nat) (thin : Ptr) (thinTB : ThinPointer TreeBorrowsProvenance)
    (hWide : wideAggregatePointeeIsDyn? pointeeTy = some false)
    (hData : evalOperand locals dataOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok (.ptr p 8) locals₁)
    (hMeta : evalOperand locals₁ metaOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok (.scalar ⟨len, 8⟩) locals₂) :
    evalRvalue locals (.aggregate (.rawPtr pointeeTy mutability) [dataOp, metaOp]) mem localDecls
        emptyLayoutTable =
      .ok (annealWidePtrVal p len 8) locals₂ mem ∧
    (do
      let (thinVal, _) ← evalUnOp .GetThinPointer
        (mrWidePtrVal thin (Int.ofNat len), .Ptr (.Raw .ElementCount))
      let metaVal ← PointerMetaKind.encode_as_value .ElementCount
        (ThinPointer.widen thin (some (.ElementCount (Int.ofNat len)))).metadata
      let decodedMeta ← PointerMetaKind.decode_value .ElementCount metaVal
      match thinVal with
      | .Ptr ⟨thin', none⟩ => pure (Gen.Value.Ptr (ThinPointer.widen thin' decodedMeta))
      | _ => specPanic "expected thin pointer") =
      .ok (mrWidePtrVal thin (Int.ofNat len)) ∧
    (do
      let (thinValTB, _) ← evalUnOpM (M := TBM) .GetThinPointer
        (mrWidePtrValM thinTB (Int.ofNat len), .Ptr (.Raw .ElementCount))
      match thinValTB with
      | .Ptr ⟨thinTB', none⟩ => pure (mrWidePtrValM thinTB' (Int.ofNat len))
      | _ => specPanic "expected thin pointer") =
      .ok (mrWidePtrValM thinTB (Int.ofNat len)) :=
  aggregate_rawPtr_and_to_raw_parts_roundtrip_lockstep
    locals locals₁ locals₂ pointeeTy mutability dataOp metaOp mem localDecls p len thin thinTB
    hWide hData hMeta

example
    (s : MachineState) (target : ResolvedCallTarget) (bodyLocalDecls : List MirAst.LocalDecl)
    (bodyLayouts : LayoutTable) (argOps : List Operand) (locals' : List LocalSlot)
    (destination : MirAst.Place) (targetBb : BasicBlockIdx)
    (elemTy : RigidTy) (elemSz elemAlign : Nat) (p : ProvenancePtr) (len : Nat)
    (vtables : Ptr → Interp VTable)
    (hPt : resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps =
      some (.slice elemTy))
    (hSz : intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy = some elemSz)
    (hAlign : intrinsicRigidTyAlign bodyLocalDecls bodyLayouts elemTy = some elemAlign)
    (hLen : len < scalarModulus 8) :
    LayoutStrategy.compute_size_and_align vtables (.Slice ⟨elemSz⟩ ⟨elemAlign⟩)
        (some (.ElementCount (Int.ofNat len))) =
      .ok (⟨len * elemSz⟩, ⟨elemAlign⟩) ∧
    x86_64.valid_size ⟨len * elemSz⟩ = decide (len * elemSz < signedHalfModulus 8) ∧
    (len * elemSz < signedHalfModulus 8 →
      x86_64.valid_size ⟨len * elemSz⟩ = true ∧
      evalSliceSizeOfVal elemSz ⟨len, 8⟩ = some ⟨len * elemSz, 8⟩ ∧
      evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts argOps
          [annealWidePtrVal p len 8] locals' destination targetBb =
        writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨len * elemSz, 8⟩) ∧
      evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts argOps
          [annealWidePtrVal p len 8] locals' destination targetBb =
        writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨elemAlign, 8⟩)) ∧
    (signedHalfModulus 8 ≤ len * elemSz →
      x86_64.valid_size ⟨len * elemSz⟩ = false ∧
      evalSliceSizeOfVal elemSz ⟨len, 8⟩ = none ∧
      evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts argOps
          [annealWidePtrVal p len 8] locals' destination targetBb = MirStepNode.fail .ub ∧
      evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts argOps
          [annealWidePtrVal p len 8] locals' destination targetBb = MirStepNode.fail .ub) :=
  sizeOfVal_and_alignOfVal_slice_lockstep
    s target bodyLocalDecls bodyLayouts argOps locals' destination targetBb
    elemTy elemSz elemAlign p len vtables hPt hSz hAlign hLen

example
    (s : MachineState) (target : ResolvedCallTarget) (bodyLocalDecls : List MirAst.LocalDecl)
    (bodyLayouts : LayoutTable) (argOps : List Operand) (locals' : List LocalSlot)
    (destination : MirAst.Place) (targetBb : BasicBlockIdx)
    (p : ProvenancePtr) (len elemSz elemAlign : Nat) (vtables : Ptr → Interp VTable)
    (hPtStr : resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps = some .str)
    (hLen : len < scalarModulus 8) :
    LayoutStrategy.compute_size_and_align vtables (.Slice ⟨1⟩ ⟨1⟩)
        (some (.ElementCount (Int.ofNat len))) =
      .ok (⟨len⟩, ⟨1⟩) ∧
    (len < signedHalfModulus 8 →
      evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts argOps
          [annealWidePtrVal p len 8] locals' destination targetBb =
        writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨len, 8⟩) ∧
      evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts argOps
          [annealWidePtrVal p len 8] locals' destination targetBb =
        writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨1, 8⟩)) ∧
    (signedHalfModulus 8 ≤ len →
      evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts argOps
          [annealWidePtrVal p len 8] locals' destination targetBb = MirStepNode.fail .ub ∧
      evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts argOps
          [annealWidePtrVal p len 8] locals' destination targetBb = MirStepNode.fail .ub) ∧
    (evalSliceSizeOfVal elemSz ⟨0, 8⟩ = some ⟨0, 8⟩ ∧
     LayoutStrategy.compute_size_and_align vtables (.Slice ⟨elemSz⟩ ⟨elemAlign⟩)
         (some (.ElementCount 0)) =
       .ok (⟨0⟩, ⟨elemAlign⟩)) ∧
    (evalSliceSizeOfVal 0 ⟨len, 8⟩ = some ⟨0, 8⟩ ∧
     LayoutStrategy.compute_size_and_align vtables (.Slice ⟨0⟩ ⟨elemAlign⟩)
         (some (.ElementCount (Int.ofNat len))) =
       .ok (⟨0⟩, ⟨elemAlign⟩)) :=
  sizeOfVal_and_alignOfVal_str_empty_zst_lockstep
    s target bodyLocalDecls bodyLayouts argOps locals' destination targetBb
    p len elemSz elemAlign vtables hPtStr hLen

example
    (locals locals' : List LocalSlot) (place : MirAst.Place) (ptrOp : Operand)
    (mem : MirSemantics.Memory) (localDecls : List MirAst.LocalDecl)
    (initProj : List ProjectionElem) (elem : RigidTy) (lIdx : LayoutIdx)
    (entry : BorrowEntry) (p : ProvenancePtr) (len : Nat)
    (hTy : placeTy localDecls emptyLayoutTable place =
      some { kind := .slice elem, layoutIdx := lIdx })
    (hSplit : splitLastDeref? place.projection = some initProj)
    (hRead : evalPlaceRead locals { local_ := place.local_, projection := initProj } mem.borrows
      mem.globals emptyLayoutTable mem.callerLocals localDecls mem.callStack =
        .ok (annealWidePtrVal p len 8) locals')
    (hOp : evalOperand locals ptrOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok (annealWidePtrVal p len 8) locals')
    (hBorrow : lookupBorrow mem.borrows p.tag = some entry)
    (hDis : entry.perm = .disabled) :
    evalRvalue locals (.len place) mem localDecls emptyLayoutTable = .ub ∧
    evalRvalue locals (.unaryOp .ptrMetadata ptrOp) mem localDecls emptyLayoutTable =
      .ok (.scalar ⟨len, 8⟩) locals' mem :=
  evalRvalue_len_wide_slice_borrow_and_disabled_contrast
    locals locals' place ptrOp mem localDecls initProj elem lIdx entry p len
    hTy hSplit hRead hOp hBorrow hDis

example (n : Nat) (xs : List MirSemantics.Value) : dropValues n xs = xs.drop n :=
  WideSliceDst.dropValues_eq_drop n xs

example (n : Nat) (xs : List MirSemantics.Value) : takeValues n xs = xs.take n :=
  WideSliceDst.takeValues_eq_take n xs

example
    (thin : Ptr) (mutbl : MirAst.Mutability) (elemSz elemAlign : Nat) (freeze : Bool)
    (len : Nat) (m : Option Mach)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hLen : len < scalarModulus 8)
    (hOverflow : x86_64.valid_size ⟨len * elemSz⟩ = false) :
    checkPtr (ThinPointer.widen thin (some (.ElementCount (Int.ofNat len))))
      (sliceRefPtrType mutbl ⟨elemSz⟩ ⟨elemAlign⟩ freeze) m =
      .error (.ub "Value::Ptr: total size exeeds isize::MAX") :=
  checkPtr_sliceRef_overflow_ub thin mutbl elemSz elemAlign freeze len m hAddr hLen hOverflow

example
    (thin : Ptr) (mutbl : MirAst.Mutability) (elemSz elemAlign : Nat) (freeze : Bool)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hNonNull : (thin.addr != 0) = true)
    (hAligned : Align.is_aligned ⟨elemAlign⟩ thin.addr = true) :
    checkPtr (ThinPointer.widen thin (some (.ElementCount 0)))
      (sliceRefPtrType mutbl ⟨elemSz⟩ ⟨elemAlign⟩ freeze) none = .ok () :=
  checkPtr_sliceRef_empty_ok thin mutbl elemSz elemAlign freeze hAddr hNonNull hAligned

example :
    let u32SlMir := wideSliceSizeAlignMir (.uint .u32) 4
    let emptySlMir := wideSliceSizeAlignMir (.uint .u32) 0
    let zstSlMir := wideSliceSizeAlignMir (.tuple []) 1000
    let strMir := wideStrSizeAlignMir 5
    (∃ mem, ReachesRet (mirTree u32SlMir (initMachineState u32SlMir [.scalar ⟨0, 4⟩])) []
      (.normal (.scalar ⟨20, 4⟩, mem))) ∧
    computeSize wideRawPartsMInit (.Slice ⟨4⟩ ⟨4⟩) (some (.ElementCount 4)) = .ok ⟨16⟩ ∧
    computeAlign wideRawPartsMInit (.Slice ⟨4⟩ ⟨4⟩) (some (.ElementCount 4)) = .ok ⟨4⟩ ∧
    (∃ mem, ReachesRet (mirTree strMir (initMachineState strMir [.scalar ⟨0, 4⟩])) []
      (.normal (.scalar ⟨6, 4⟩, mem))) ∧
    computeSize wideRawPartsMInit (.Slice ⟨1⟩ ⟨1⟩) (some (.ElementCount 5)) = .ok ⟨5⟩ ∧
    computeAlign wideRawPartsMInit (.Slice ⟨1⟩ ⟨1⟩) (some (.ElementCount 5)) = .ok ⟨1⟩ ∧
    (∃ mem, ReachesRet (mirTree emptySlMir (initMachineState emptySlMir [.scalar ⟨0, 4⟩])) []
      (.normal (.scalar ⟨4, 4⟩, mem))) ∧
    computeSize wideRawPartsMInit (.Slice ⟨4⟩ ⟨4⟩) (some (.ElementCount 0)) = .ok ⟨0⟩ ∧
    computeAlign wideRawPartsMInit (.Slice ⟨4⟩ ⟨4⟩) (some (.ElementCount 0)) = .ok ⟨4⟩ ∧
    (∃ mem, ReachesRet (mirTree zstSlMir (initMachineState zstSlMir [.scalar ⟨0, 4⟩])) []
      (.normal (.scalar ⟨1, 4⟩, mem))) ∧
    computeSize wideRawPartsMInit (.Slice ⟨0⟩ ⟨1⟩) (some (.ElementCount 1000)) = .ok ⟨0⟩ ∧
    computeAlign wideRawPartsMInit (.Slice ⟨0⟩ ⟨1⟩) (some (.ElementCount 1000)) = .ok ⟨1⟩ :=
  wideSliceSizeAndAlignOfVal_u32_str_empty_zst_witnesses

example :
    evalSliceSizeOfVal 4 ⟨u32SliceMaxOkLen, 8⟩ = some ⟨u32SliceMaxOkLen * 4, 8⟩ ∧
    x86_64.valid_size ⟨u32SliceMaxOkLen * 4⟩ = true ∧
    evalSliceSizeOfVal 4 ⟨u32SliceOverflowLen, 8⟩ = none ∧
    x86_64.valid_size ⟨u32SliceOverflowLen * 4⟩ = false ∧
    (∃ tr u, Reaches
      (mirTree u32SliceOverflowMir (initMachineState u32SliceOverflowMir [.scalar ⟨0, 4⟩])) tr u ∧
      FaultNow u) ∧
    checkPtr overflowingU32SlicePtr (sliceRefPtrType .not ⟨4⟩ ⟨4⟩) (some wideRawPartsMInit) =
      .error (.ub "Value::Ptr: total size exeeds isize::MAX") ∧
    checkPtr danglingEmptyU32SlicePtr (sliceRefPtrType .not ⟨4⟩ ⟨4⟩) none = .ok () ∧
    evalNonSelectIntrinsicCall .sizeOfVal wideRawPartsS0 sizeOfValSliceU32Target
        wideRawPartsMir.localDecls emptyLayoutTable [] [annealWideScalarPtrVal 4 0 8]
        wideRawPartsS0.frame.locals (local_ 0) 1 =
      MirStepNode.fail .ub ∧
    evalNonSelectIntrinsicCall .alignOfVal wideRawPartsS0 alignOfValSliceU32Target
        wideRawPartsMir.localDecls emptyLayoutTable [] [annealWideScalarPtrVal 4 0 8]
        wideRawPartsS0.frame.locals (local_ 0) 1 =
      MirStepNode.fail .ub :=
  wideSliceIsizeMaxBoundary_and_scalarAddrDivergence_canaries

example (lookup : Ptr → Interp VTable) (elemSz elemAlign len : Nat) :
    LayoutStrategy.compute_size_and_align lookup (.Slice ⟨elemSz⟩ ⟨elemAlign⟩)
        (some (.ElementCount (Int.ofNat len))) =
      .ok (⟨len * elemSz⟩, ⟨elemAlign⟩) :=
  compute_size_and_align_slice_eq lookup elemSz elemAlign len

example (n : Nat) :
    x86_64.valid_size ⟨n⟩ = decide (n < signedHalfModulus 8) :=
  x86_64_valid_size_nat_eq n

example (m : Mach) (elemSz elemAlign len : Nat) :
    computeSize m (.Slice ⟨elemSz⟩ ⟨elemAlign⟩) (some (.ElementCount (Int.ofNat len))) =
      .ok ⟨len * elemSz⟩ ∧
    computeAlign m (.Slice ⟨elemSz⟩ ⟨elemAlign⟩) (some (.ElementCount (Int.ofNat len))) =
      .ok ⟨elemAlign⟩ :=
  computeSize_computeAlign_slice_total m elemSz elemAlign len

example (thin : Ptr) (len : Nat) (m : Option Mach)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hLen : len < scalarModulus 8) :
    checkPtr (ThinPointer.widen thin (some (.ElementCount (Int.ofNat len)))) (.Raw .ElementCount)
        m = .ok () :=
  WideSliceDst.checkPtr_rawSlice_ok thin len m hAddr hLen

example (thin vptr : Ptr) (thinTB vptrTB : ThinPointer TreeBorrowsProvenance)
    (elemTy : Gen.Type) (elemSz elemAlign len : Nat)
    (traitName : Gen.TraitName) (meth : Gen.TraitMethodName)
    (m : Option Mach) (mTB : Option MachTB) (mach : Mach) (machTB : MachTB)
    (hElemLayout : Type.layout elemTy = .ok (.Sized ⟨elemSz⟩ ⟨elemAlign⟩))
    (hLen : IntType.can_represent IntType.usize_ty (Int.ofNat len) = true) :
    evalUnOp .GetMetadata (.Ptr (ThinPointer.widen thin none), .Ptr (.Raw .None)) m =
      .ok (.Tuple [], unitType) ∧
    evalUnOp .GetMetadata
        (.Ptr (ThinPointer.widen thin (some (.ElementCount (Int.ofNat len)))),
         .Ptr (.Raw .ElementCount)) m =
      .ok (.Int (Int.ofNat len), .Int IntType.usize_ty) ∧
    evalUnOp (.ComputeSize elemTy) (.Tuple [], unitType) m =
      .ok (.Int (elemSz : Int), .Int IntType.usize_ty) ∧
    evalUnOp (.ComputeAlign elemTy) (.Tuple [], unitType) m =
      .ok (.Int (elemAlign : Int), .Int IntType.usize_ty) ∧
    evalUnOp (.ComputeSize (.Slice elemTy)) (.Int (Int.ofNat len), .Int IntType.usize_ty) m =
      .ok (.Int ((len * elemSz : Nat) : Int), .Int IntType.usize_ty) ∧
    evalUnOp (.ComputeAlign (.Slice elemTy)) (.Int (Int.ofNat len), .Int IntType.usize_ty) m =
      .ok (.Int (elemAlign : Int), .Int IntType.usize_ty) ∧
    evalUnOp .GetMetadata
        (.Ptr (ThinPointer.widen thin (some (.VTablePointer vptr))),
         .Ptr (.Raw (.VTablePointer traitName))) none =
      unsupported "eval_un_op UnOp::GetMetadata for vtable pointer metadata" ∧
    evalUnOp (.ComputeSize (.TraitObject traitName))
        (.Ptr (ThinPointer.widen vptr none), .Ptr (.VTablePtr traitName)) none =
      unsupported "eval_un_op UnOp::ComputeSize for vtable pointer metadata" ∧
    evalUnOp (.ComputeAlign (.TraitObject traitName))
        (.Ptr (ThinPointer.widen vptr none), .Ptr (.VTablePtr traitName)) none =
      unsupported "eval_un_op UnOp::ComputeAlign for vtable pointer metadata" ∧
    evalUnOp (.VTableMethodLookup meth)
        (.Ptr (ThinPointer.widen vptr none), .Ptr (.VTablePtr traitName)) none =
      unsupported "eval_un_op for UnOp::VTableMethodLookup" ∧
    (checkPtr (ThinPointer.widen vptr none) (.VTablePtr traitName) (some mach) = .ok () →
      evalUnOp .GetMetadata
          (.Ptr (ThinPointer.widen thin (some (.VTablePointer vptr))),
           .Ptr (.Raw (.VTablePointer traitName))) (some mach) =
        .ok (.Ptr (ThinPointer.widen vptr none), .Ptr (.VTablePtr traitName))) ∧
    (∀ vt, vtableLookup mach vptr = .ok vt →
      evalUnOp (.ComputeSize (.TraitObject traitName))
          (.Ptr (ThinPointer.widen vptr none), .Ptr (.VTablePtr traitName)) (some mach) =
        .ok (.Int (vt.size.bytes : Int), .Int IntType.usize_ty) ∧
      evalUnOp (.ComputeAlign (.TraitObject traitName))
          (.Ptr (ThinPointer.widen vptr none), .Ptr (.VTablePtr traitName)) (some mach) =
        .ok (.Int (vt.align.bytes : Int), .Int IntType.usize_ty)) ∧
    (∀ vt fnName fnThin, vtableLookup mach vptr = .ok vt →
      mapIndex vt.methods meth "vtable.methods[method]" = .ok fnName →
      mapIndex mach.fn_ptrs fnName "self.fn_ptrs[fn_name]" = .ok fnThin →
      evalUnOp (.VTableMethodLookup meth)
          (.Ptr (ThinPointer.widen vptr none), .Ptr (.VTablePtr traitName)) (some mach) =
        .ok (.Ptr (ThinPointer.widen fnThin none), .Ptr .FnPtr)) ∧
    evalUnOpM (M := TBM) .GetMetadata
        (.Ptr (ThinPointer.widen thinTB none), .Ptr (.Raw .None)) mTB =
      .ok (.Tuple [], unitType) ∧
    evalUnOpM (M := TBM) .GetMetadata
        (.Ptr (ThinPointer.widen thinTB (some (.ElementCount (Int.ofNat len)))),
         .Ptr (.Raw .ElementCount)) mTB =
      .ok (.Int (Int.ofNat len), .Int IntType.usize_ty) ∧
    evalUnOpM (M := TBM) (.ComputeSize elemTy) (.Tuple [], unitType) mTB =
      .ok (.Int (elemSz : Int), .Int IntType.usize_ty) ∧
    evalUnOpM (M := TBM) (.ComputeAlign elemTy) (.Tuple [], unitType) mTB =
      .ok (.Int (elemAlign : Int), .Int IntType.usize_ty) ∧
    evalUnOpM (M := TBM) (.ComputeSize (.Slice elemTy))
        (.Int (Int.ofNat len), .Int IntType.usize_ty) mTB =
      .ok (.Int ((len * elemSz : Nat) : Int), .Int IntType.usize_ty) ∧
    evalUnOpM (M := TBM) (.ComputeAlign (.Slice elemTy))
        (.Int (Int.ofNat len), .Int IntType.usize_ty) mTB =
      .ok (.Int (elemAlign : Int), .Int IntType.usize_ty) ∧
    evalUnOpM (M := TBM) .GetMetadata
        (.Ptr (ThinPointer.widen thinTB (some (.VTablePointer vptrTB))),
         .Ptr (.Raw (.VTablePointer traitName))) none =
      unsupported "eval_un_op UnOp::GetMetadata for vtable pointer metadata" ∧
    evalUnOpM (M := TBM) (.ComputeSize (.TraitObject traitName))
        (.Ptr (ThinPointer.widen vptrTB none), .Ptr (.VTablePtr traitName)) none =
      unsupported "eval_un_op UnOp::ComputeSize for vtable pointer metadata" ∧
    evalUnOpM (M := TBM) (.ComputeAlign (.TraitObject traitName))
        (.Ptr (ThinPointer.widen vptrTB none), .Ptr (.VTablePtr traitName)) none =
      unsupported "eval_un_op UnOp::ComputeAlign for vtable pointer metadata" ∧
    evalUnOpM (M := TBM) (.VTableMethodLookup meth)
        (.Ptr (ThinPointer.widen vptrTB none), .Ptr (.VTablePtr traitName)) none =
      unsupported "eval_un_op for UnOp::VTableMethodLookup" ∧
    (checkPtrM (M := TBM) (ThinPointer.widen vptrTB none) (.VTablePtr traitName) (some machTB) =
        .ok () →
      evalUnOpM (M := TBM) .GetMetadata
          (.Ptr (ThinPointer.widen thinTB (some (.VTablePointer vptrTB))),
           .Ptr (.Raw (.VTablePointer traitName))) (some machTB) =
        .ok (.Ptr (ThinPointer.widen vptrTB none), .Ptr (.VTablePtr traitName))) ∧
    (∀ vt, vtableLookupM machTB vptrTB = .ok vt →
      evalUnOpM (M := TBM) (.ComputeSize (.TraitObject traitName))
          (.Ptr (ThinPointer.widen vptrTB none), .Ptr (.VTablePtr traitName)) (some machTB) =
        .ok (.Int (vt.size.bytes : Int), .Int IntType.usize_ty) ∧
      evalUnOpM (M := TBM) (.ComputeAlign (.TraitObject traitName))
          (.Ptr (ThinPointer.widen vptrTB none), .Ptr (.VTablePtr traitName)) (some machTB) =
        .ok (.Int (vt.align.bytes : Int), .Int IntType.usize_ty)) ∧
    (∀ vt fnName fnThin, vtableLookupM machTB vptrTB = .ok vt →
      mapIndex vt.methods meth "vtable.methods[method]" = .ok fnName →
      mapIndex machTB.fn_ptrs fnName "self.fn_ptrs[fn_name]" = .ok fnThin →
      evalUnOpM (M := TBM) (.VTableMethodLookup meth)
          (.Ptr (ThinPointer.widen vptrTB none), .Ptr (.VTablePtr traitName)) (some machTB) =
        .ok (.Ptr (ThinPointer.widen fnThin none), .Ptr .FnPtr)) :=
  minirust_interp_metadata_unops_exec_and_vtable_unsupported
    thin vptr thinTB vptrTB elemTy elemSz elemAlign len traitName meth m mTB mach machTB
    hElemLayout hLen

example :
    (∃ mem, ReachesRet (mirTree wideRawPartsMir wideRawPartsS0) []
      (.normal (.scalar ⟨46, 4⟩, mem))) ∧
    MirNoUBTree (mirTree wideRawPartsMir wideRawPartsS0) ∧
    (Interp.steps 25 wideRawPartsMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 46 }, [1]) ∧
    (Interp.stepsTB 25 wideRawPartsTBInit).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 46 :=
  wideSliceFromRawPartsMetadataRoundTrip_three_way

example :
    (∃ mem, ReachesRet (mirTree wideSliceIdxReadWriteMir wideSliceIdxReadWriteS0) []
      (.normal (.scalar ⟨133, 4⟩, mem))) ∧
    MirNoUBTree (mirTree wideSliceIdxReadWriteMir wideSliceIdxReadWriteS0) ∧
    (Interp.steps 26 wideSliceIdxReadWriteMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 133 }, [1]) ∧
    (Interp.stepsTB 26 wideSliceIdxReadWriteTBInit).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 133 ∧
    (∃ tr u, Reaches (mirTree wideSliceIdxOobMir wideSliceIdxOobS0) tr u ∧ FaultNow u) ∧
    stopAfterM wideSliceIdxOobMInit 10 = some (.ub "access to out-of-bounds index") ∧
    stopAfterTB wideSliceIdxOobTBInit 10 = some (.ub "access to out-of-bounds index") :=
  wideSliceIndexReadWriteAndOobUb_three_way

example :
    (∃ tr u, Reaches (mirTree wideSliceDisabledDerefUbMir wideSliceDisabledDerefUbS0) tr u ∧
      FaultNow u) ∧
    stopAfterTB wideSliceDisabledDerefUbTBInit 12 =
      some (.ub "Tree Borrows: local read of Disabled reference") ∧
    (∃ mem, ReachesRet
      (mirTree wideSliceMetadataAfterParentWriteMir wideSliceMetadataAfterParentWriteS0) []
      (.normal (.scalar ⟨4, 4⟩, mem))) ∧
    MirNoUBTree
      (mirTree wideSliceMetadataAfterParentWriteMir wideSliceMetadataAfterParentWriteS0) :=
  wideSliceTreeBorrowsDisabledVsMetadataOk_three_way

/- MiniRust's `isize::MAX` UB is raised only by `check_ptr` on safe references; raw wide pointers
and `compute_size` / `compute_align` are total. -/
example (m : Mach) (thin : Ptr) (mutbl : MirAst.Mutability) (elemSz elemAlign : Nat)
    (freeze : Bool) (len : Nat)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hLen : len < scalarModulus 8)
    (hOverflow : signedHalfModulus 8 ≤ len * elemSz) :
    checkPtr (ThinPointer.widen thin (some (.ElementCount (Int.ofNat len))))
        (sliceRefPtrType mutbl ⟨elemSz⟩ ⟨elemAlign⟩ freeze) (some m) =
      .error (.ub "Value::Ptr: total size exeeds isize::MAX") ∧
    checkPtr (ThinPointer.widen thin (some (.ElementCount (Int.ofNat len)))) (.Raw .ElementCount)
        (some m) = .ok () ∧
    computeSize m (.Slice ⟨elemSz⟩ ⟨elemAlign⟩) (some (.ElementCount (Int.ofNat len))) =
      .ok ⟨len * elemSz⟩ ∧
    computeAlign m (.Slice ⟨elemSz⟩ ⟨elemAlign⟩) (some (.ElementCount (Int.ofNat len))) =
      .ok ⟨elemAlign⟩ :=
  sliceSizeOverflow_minirust_ub_locus m thin mutbl elemSz elemAlign freeze len hAddr hLen hOverflow

/- `DIV-MR-RAW-SLICE-SIZE-OF-VAL-ISIZE-MAX`. -/
example :
    (∃ tr u, Reaches
      (mirTree u32SliceOverflowMir (initMachineState u32SliceOverflowMir [.scalar ⟨0, 4⟩])) tr u ∧
      FaultNow u) ∧
    computeSize wideRawPartsMInit (.Slice ⟨4⟩ ⟨4⟩)
        (some (.ElementCount (Int.ofNat u32SliceOverflowLen))) = .ok ⟨2 ^ 63⟩ ∧
    computeAlign wideRawPartsMInit (.Slice ⟨4⟩ ⟨4⟩)
        (some (.ElementCount (Int.ofNat u32SliceOverflowLen))) = .ok ⟨4⟩ ∧
    checkPtr overflowingU32SlicePtr (.Raw .ElementCount) (some wideRawPartsMInit) = .ok () ∧
    checkPtr overflowingU32SlicePtr (sliceRefPtrType .not ⟨4⟩ ⟨4⟩) (some wideRawPartsMInit) =
      .error (.ub "Value::Ptr: total size exeeds isize::MAX") ∧
    evalRvalue [.uninit, .init (annealWideScalarPtrVal 4 0 8)]
        (.unaryOp .ptrMetadata (.copy (local_ 1))) emptyMemory
        [u32Decl, rawConstSliceU32Decl] emptyLayoutTable =
      .ok (.scalar ⟨0, 8⟩) [.uninit, .init (annealWideScalarPtrVal 4 0 8)] emptyMemory ∧
    PointerMetaKind.encode_as_value .ElementCount danglingEmptyU32SlicePtr.metadata =
      .ok (.Int 0) ∧
    evalRvalue [.uninit, .init (annealWideScalarPtrVal 4 0 8)]
        (.cast .ptrToPtr (.copy (local_ 1)) rawConstUnitTy) emptyMemory
        [u32Decl, rawConstSliceU32Decl] emptyLayoutTable =
      .ok (.scalar ⟨4, 8⟩) [.uninit, .init (annealWideScalarPtrVal 4 0 8)] emptyMemory ∧
    evalUnOp .GetThinPointer (Gen.Value.Ptr danglingEmptyU32SlicePtr, .Ptr (.Raw .ElementCount)) =
      .ok (Gen.Value.Ptr (ThinPointer.widen { addr := 4, provenance := none } none),
        .Ptr (.Raw .None)) :=
  div_rawSliceSizeOfVal_isizeMax_anneal_ub_vs_minirust_total

/- `DIV-MR-RAW-PARENT-WRITE-SB-VS-TB` plus the `Mach` / `MachTB` metadata agreement. -/
example :
    (∃ tr u, Reaches (mirTree wideSliceDisabledDerefUbMir wideSliceDisabledDerefUbS0) tr u ∧
      FaultNow u) ∧
    (Interp.steps 12 wideSliceRawParentWriteMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 1 }, [1]) ∧
    (Interp.stepsTB 12 wideSliceRawParentWriteTBInit).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 1 ∧
    (Interp.steps 13 wideSliceDisabledDerefUbMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 1 }, [1]) ∧
    stopAfterTB wideSliceDisabledDerefUbTBInit 12 =
      some (.ub "Tree Borrows: local read of Disabled reference") ∧
    (∃ mem, ReachesRet
      (mirTree wideSliceMetadataAfterParentWriteMir wideSliceMetadataAfterParentWriteS0) []
      (.normal (.scalar ⟨4, 4⟩, mem))) ∧
    MirNoUBTree
      (mirTree wideSliceMetadataAfterParentWriteMir wideSliceMetadataAfterParentWriteS0) ∧
    (Interp.steps 14 wideSliceMetadataAfterParentWriteMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 4 }, [1]) ∧
    (Interp.stepsTB 14 wideSliceMetadataAfterParentWriteTBInit).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 4 :=
  wideSliceParentWrite_aliasingDivergence_and_metadata_three_way

example
    (body : CapturedMir) (ctx : Ctx) (borrows : List BorrowEntry)
    (p : ProvenancePtr) (e : BorrowEntry) (it : Gen.IntType) (relOff : Nat)
    (hlookup : lookupBorrow borrows p.tag = some e)
    (htspec : ptrTargetSpec body.layouts body.localDecls ⟨e.targetLocal, e.targetProjection⟩ =
      some (it, relOff))
    (haddr : (ctx.addrs.getD e.targetLocal 0 + (relOff : Int)).toNat + p.offsetBytes <
      scalarModulus 8) :
    let baseAddr := (ctx.addrs.getD e.targetLocal 0 + (relOff : Int)).toNat
    let aid : Gen.AllocId := ⟨((ctx.base.length + e.targetLocal : Nat) : Int)⟩
    WideSliceThinPtrRel (ctxWithBorrows body ctx borrows) p
      { addr := ((baseAddr + p.offsetBytes : Nat) : Int), provenance := some (aid, ()) }
      { addr := ((baseAddr + p.offsetBytes : Nat) : Int)
        provenance := some (liftProvTB (aid, ())) }
      [] :=
  WideSliceThinPtrRel.of_ctxWithBorrows body ctx borrows p e it relOff hlookup htspec haddr

example {ctx : Ctx} {p : ProvenancePtr}
    {thin : Ptr} {thinTB : ThinPointer TreeBorrowsProvenance} {tbPath : Gen.Path}
    (hrel : WideSliceThinPtrRel ctx p thin thinTB tbPath) :
    inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true :=
  WideSliceThinPtrRel.inBounds_addr hrel

example {ctx : Ctx}
    {v : MirSemantics.Value} {mrVal : Val} {mrValTB : Gen.Value TBM}
    (hrel : WideSliceValRel ctx v mrVal mrValTB) (m : Option Mach) :
    ∃ widePtr,
      mrVal = .Ptr widePtr ∧
      checkPtr widePtr (.Raw .ElementCount) m = .ok () :=
  WideSliceValRel.checkPtr_rawSlice_ok hrel m

example
    {ctx : Ctx} {locals locals' : List LocalSlot} {op : Operand}
    {mem : MirSemantics.Memory} {localDecls : List MirAst.LocalDecl}
    {v : MirSemantics.Value} {mrVal : Val} {mrValTB : Gen.Value TBM}
    (hNonWide : isNonWidePtrAggregateTy (operandTy localDecls emptyLayoutTable op) = false)
    (hOp : evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok v locals')
    (hrel : WideSliceValRel ctx v mrVal mrValTB) :
    ∃ (len : Nat) (widePtr : Pointer Prov),
      len < scalarModulus 8 ∧
      mrVal = .Ptr widePtr ∧
      evalRvalue locals (.unaryOp .ptrMetadata op) mem localDecls emptyLayoutTable =
        .ok (.scalar ⟨len, 8⟩) locals' mem ∧
      PointerMetaKind.encode_as_value .ElementCount widePtr.metadata =
        .ok (.Int (Int.ofNat len)) :=
  ptrMetadata_wideSliceValRel_lockstep hNonWide hOp hrel

example
    {ctx : Ctx} {tbPath : Gen.Path} (locals locals₁ : List LocalSlot)
    (wideOp : Operand) (thinTargetTy wideTargetTy pointeeTy : Ty)
    (mutability : MirAst.Mutability) (mem : MirSemantics.Memory) (localDecls : List MirAst.LocalDecl)
    (p : ProvenancePtr) (len : Nat) (thin : Ptr)
    (thinTB : ThinPointer TreeBorrowsProvenance) (ptrTy : PtrType)
    (hptr : WideSliceThinPtrRel ctx p thin thinTB tbPath)
    (hlen : len < scalarModulus 8)
    (hNoBorrow : lookupBorrow mem.borrows p.tag = none)
    (hThin : isThinRawPtrTy thinTargetTy = true)
    (hNotThin : isThinRawPtrTy wideTargetTy = false)
    (hWide : wideRawPtrIsDyn? wideTargetTy = some false)
    (hWideAgg : wideAggregatePointeeIsDyn? pointeeTy = some false)
    (hWideOp : evalOperand locals wideOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok (annealWidePtrVal p len 8) locals₁) :
    WideSliceValRel ctx
      (annealWidePtrVal p len 8)
      (mrWidePtrVal thin (Int.ofNat len))
      (mrWidePtrValM thinTB (Int.ofNat len)) ∧
    evalRvalue locals (.cast .ptrToPtr wideOp wideTargetTy) mem localDecls emptyLayoutTable =
      .ok (annealWidePtrVal p len 8) locals₁ mem ∧
    evalUnOp .GetThinPointer (mrWidePtrVal thin (Int.ofNat len), .Ptr ptrTy) =
      .ok (.Ptr (ThinPointer.widen thin none), .Ptr (.Raw .None)) ∧
    evalUnOpM (M := TBM) .GetThinPointer (mrWidePtrValM thinTB (Int.ofNat len), .Ptr ptrTy) =
      .ok (.Ptr (ThinPointer.widen thinTB none), .Ptr (.Raw .None)) ∧
    ∃ thinVal metaVal,
      evalRvalue locals (.cast .ptrToPtr wideOp thinTargetTy) mem localDecls emptyLayoutTable =
        .ok thinVal locals₁ mem ∧
      evalRvalue locals (.unaryOp .ptrMetadata wideOp) mem localDecls emptyLayoutTable =
        .ok metaVal locals₁ mem ∧
      thinVal = .ptr p 8 ∧
      metaVal = .scalar ⟨len, 8⟩ ∧
      WideSliceThinPtrRel ctx p thin thinTB tbPath ∧
      evalRvalue [.init thinVal, .init metaVal]
          (.aggregate (.rawPtr pointeeTy mutability) [.copy (local_ 0), .copy (local_ 1)])
          mem [] emptyLayoutTable =
        .ok (annealWidePtrVal p len 8) [.init thinVal, .init metaVal] mem :=
  ptrToPtr_wideSliceValRel_global_to_from_raw_parts_roundtrip
    locals locals₁ wideOp thinTargetTy wideTargetTy pointeeTy mutability
    mem localDecls p len thin thinTB ptrTy hptr hlen hNoBorrow hThin hNotThin hWide hWideAgg
    hWideOp

example
    (body : CapturedMir) (ctx : Ctx)
    (locals locals₁ : List LocalSlot) (wideOp : Operand) (thinTargetTy pointeeTy : Ty)
    (mutability : MirAst.Mutability) (mem : MirSemantics.Memory) (localDecls : List MirAst.LocalDecl)
    (p : ProvenancePtr) (len : Nat) (parentEntry : BorrowEntry)
    (it : Gen.IntType) (relOff : Nat) (rootVal : MirSemantics.Value)
    (containerProj : List ProjectionElem) (baseIdx : Nat) (elems : List MirSemantics.Value)
    (rawElemOffset : Nat) (ptrTy : PtrType)
    (hlen : len < scalarModulus 8)
    (hThin : isThinRawPtrTy thinTargetTy = true)
    (hWideAgg : wideAggregatePointeeIsDyn? pointeeTy = some false)
    (hWideOp : evalOperand locals wideOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok (annealWidePtrVal p len 8) locals₁)
    (hBorrow : lookupBorrow mem.borrows p.tag = some parentEntry)
    (htspec : ptrTargetSpec body.layouts body.localDecls ⟨parentEntry.targetLocal, parentEntry.targetProjection⟩ =
      some (it, relOff))
    (haddr : (ctx.addrs.getD parentEntry.targetLocal 0 + (relOff : Int)).toNat + p.offsetBytes <
      scalarModulus 8)
    (hPerm : parentEntry.perm ≠ .disabled)
    (hRoot : activeFrameSlot? locals₁ mem.callStack parentEntry.targetFrameDepth
      parentEntry.targetLocal = some (.init rootVal))
    (hRead : readSliceBackingAggregate? locals₁ rootVal
      (normalizeSubsliceProjections (stripTransparentProjections parentEntry.targetProjection))
      len = some (containerProj, baseIdx, elems))
    (hOff : byteOffsetToElemIdx? p.offsetBytes (inferElemListByteStride elems) =
      some rawElemOffset)
    (hBound : Nat.ble (Nat.add (Nat.add rawElemOffset baseIdx) len) (Trusted.Sequence.length elems) = true) :
    let baseAddr := (ctx.addrs.getD parentEntry.targetLocal 0 + (relOff : Int)).toNat
    let aid : Gen.AllocId := ⟨((ctx.base.length + parentEntry.targetLocal : Nat) : Int)⟩
    let thin : Ptr := { addr := ((baseAddr + p.offsetBytes : Nat) : Int), provenance := some (aid, ()) }
    let thinTB : ThinPointer TreeBorrowsProvenance :=
      { addr := ((baseAddr + p.offsetBytes : Nat) : Int), provenance := some (liftProvTB (aid, ())) }
    let alreadySub :=
      Bool.and (endsWithSubslice containerProj)
        (Bool.and (Nat.beq (Nat.add rawElemOffset baseIdx) 0) (Nat.beq len (Trusted.Sequence.length elems)))
    WideSliceThinPtrRel (ctxWithBorrows body ctx mem.borrows) p thin thinTB [] ∧
    evalUnOp .GetThinPointer (mrWidePtrVal thin (Int.ofNat len), .Ptr ptrTy) =
      .ok (.Ptr (ThinPointer.widen thin none), .Ptr (.Raw .None)) ∧
    evalUnOpM (M := TBM) .GetThinPointer (mrWidePtrValM thinTB (Int.ofNat len), .Ptr ptrTy) =
      .ok (.Ptr (ThinPointer.widen thinTB none), .Ptr (.Raw .None)) ∧
    (alreadySub = true →
      evalRvalue locals (.cast .ptrToPtr wideOp thinTargetTy) mem localDecls emptyLayoutTable =
        .ok (.ptr p 8) locals₁ mem ∧
      evalRvalue [.init (.ptr p 8), .init (.scalar ⟨len, 8⟩)]
          (.aggregate (.rawPtr pointeeTy mutability) [.copy (local_ 0), .copy (local_ 1)])
          mem [] emptyLayoutTable =
        .ok (annealWidePtrVal p len 8) [.init (.ptr p 8), .init (.scalar ⟨len, 8⟩)] mem) ∧
    (alreadySub = false →
      ∃ mem',
        mem'.nextTag = mem.nextTag + 1 ∧
        evalRvalue locals (.cast .ptrToPtr wideOp thinTargetTy) mem localDecls emptyLayoutTable =
          .ok (.ptr { allocId := mem.nextTag, offsetBytes := 0 } 8) locals₁ mem' ∧
        evalRvalue [.init (.ptr { allocId := mem.nextTag, offsetBytes := 0 } 8),
                    .init (.scalar ⟨len, 8⟩)]
            (.aggregate (.rawPtr pointeeTy mutability) [.copy (local_ 0), .copy (local_ 1)])
            mem' [] emptyLayoutTable =
          .ok (annealWidePtrVal { allocId := mem.nextTag, offsetBytes := 0 } len 8)
            [.init (.ptr { allocId := mem.nextTag, offsetBytes := 0 } 8),
             .init (.scalar ⟨len, 8⟩)] mem') :=
  ptrToPtr_wideSliceValRel_borrowBacked_subslice_and_retag
    body ctx locals locals₁ wideOp thinTargetTy pointeeTy mutability mem localDecls
    p len parentEntry it relOff rootVal containerProj baseIdx elems rawElemOffset ptrTy
    hlen hThin hWideAgg hWideOp hBorrow htspec haddr hPerm hRoot hRead hOff hBound

example :
    let decls := wideRawPartsMir.localDecls
    translatePlace decls { local_ := 8, projection := [.deref, .index 9] } = none ∧
    translateRvalue emptyLayoutTable decls (some rawMutSliceU32Ty)
      (.aggregate (.rawPtr sliceU32PointeeTy .mut) [.copy (local_ 3), WideSliceDst.constUsize 4]) = none ∧
    translateRvalue emptyLayoutTable decls (some usizeMirTy)
      (.unaryOp .ptrMetadata (.copy (local_ 5))) = none ∧
    translateRvalue emptyLayoutTable decls (some usizeMirTy)
      (.len (derefPlace 4)) = none :=
  translatePlace_and_translateRvalue_wideSlice_boundary

example :
    let d1 := wideRawPartsMir.localDecls
    let d2 := wideSliceIdxReadWriteMir.localDecls
    translateStatement d1
      (mkStmt (.assign (local_ 2)
        (.aggregate (.array u32Ty) [.copy (local_ 1), constU32 20, constU32 30, constU32 40])))
      emptyLayoutTable =
      some (.Assign (.Local (localName 2))
        (.Tuple [.Load (.Local (localName 1)), .Constant (.Int 20) (.Int u32),
                 .Constant (.Int 30) (.Int u32), .Constant (.Int 40) (.Int u32)]
          (.Array (.Int u32) 4))) ∧
    translateStatement d1
      (mkStmt (.assign (local_ 5) (.cast .ptrToPtr (.copy (local_ 4)) rawConstSliceU32Ty)))
      emptyLayoutTable =
      some (.Assign (.Local (localName 5)) (.Load (.Local (localName 4)))) ∧
    translateStatement d1
      (mkStmt (.assign (local_ 6) (.cast .ptrToPtr (.copy (local_ 5)) rawConstUnitTy)))
      emptyLayoutTable =
      some (.Assign (.Local (localName 6)) (.UnOp .GetThinPointer (.Load (.Local (localName 5))))) ∧
    translateStatement d1 (mkStmt (.assign (local_ 9) (.use (WideSliceDst.constUsize 0)))) emptyLayoutTable =
      some (.Assign (.Local (localName 9)) (.Constant (.Int 0) (.Int IntType.usize_ty))) ∧
    translateStatement d1
      (mkStmt (.assign (local_ 11) (.cast .intToInt (.copy (local_ 7)) u32Ty))) emptyLayoutTable =
      some (.Assign (.Local (localName 11))
        (.UnOp (.Cast (.IntToInt u32)) (.Load (.Local (localName 7))))) ∧
    translateStatement d1
      (mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 10)) (.copy (local_ 11)))))
      emptyLayoutTable =
      some (.Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 10))) (.Load (.Local (localName 11))))) ∧
    translateStatement d2 (mkStmt (.assign (local_ 5) (.use (WideSliceDst.constUsize 2)))) emptyLayoutTable =
      some (.Assign (.Local (localName 5)) (.Constant (.Int 2) (.Int IntType.usize_ty))) ∧
    translateStatement d2 (mkStmt (.assign (local_ 6) (.use (WideSliceDst.constUsize 1)))) emptyLayoutTable =
      some (.Assign (.Local (localName 6)) (.Constant (.Int 1) (.Int IntType.usize_ty))) ∧
    translateStatement d2
      (mkStmt (.assign (local_ 10) (.cast .intToInt (.copy (local_ 9)) u32Ty))) emptyLayoutTable =
      some (.Assign (.Local (localName 10))
        (.UnOp (.Cast (.IntToInt u32)) (.Load (.Local (localName 9))))) :=
  wideSliceWitnesses_translateStatement_correspondence

example
    (locals locals' : List LocalSlot) (mem : MirSemantics.Memory)
    (localDecls : List MirAst.LocalDecl) (sIdx : Local) (elem : RigidTy) (lIdx : LayoutIdx)
    (entry : BorrowEntry) (rootVal : MirSemantics.Value)
    (containerProj : List ProjectionElem) (baseIdx rawElemOffset : Nat)
    (elems : List MirSemantics.Value) (p : ProvenancePtr) (len : Nat)
    (hTy : placeTy localDecls emptyLayoutTable ⟨sIdx, [.deref]⟩ =
      some { kind := .slice elem, layoutIdx := lIdx })
    (hRead : evalPlaceRead locals ⟨sIdx, []⟩ mem.borrows mem.globals emptyLayoutTable
      mem.callerLocals localDecls mem.callStack = .ok (annealWidePtrVal p len 8) locals')
    (hBorrow : lookupBorrow mem.borrows p.tag = some entry)
    (hSlot : activeFrameSlot? locals' mem.callStack entry.targetFrameDepth entry.targetLocal =
      some (.init rootVal))
    (hBacking : readSliceBackingAggregate? locals' rootVal entry.targetProjection len
      (tyByteSize localDecls emptyLayoutTable { kind := elem, layoutIdx := unresolvedLayoutIdx emptyLayoutTable }) =
      some (containerProj, baseIdx, elems))
    (hOff : byteOffsetToElemIdx? p.offsetBytes (inferElemListByteStride elems) = some rawElemOffset) :
    (entry.perm ≠ .disabled → rawElemOffset + baseIdx + len ≤ elems.length →
      evalRvalue locals (.len ⟨sIdx, [.deref]⟩) mem localDecls emptyLayoutTable =
        .ok (.scalar ⟨len, 8⟩) locals' mem) ∧
    (entry.perm ≠ .disabled → elems.length < rawElemOffset + baseIdx + len →
      evalRvalue locals (.len ⟨sIdx, [.deref]⟩) mem localDecls emptyLayoutTable = .ub) ∧
    (entry.perm = .frozen →
      Trusted.Sequence.get? locals sIdx = some (.init (annealWidePtrVal p len 8)) →
      evalRvalue locals (.ref (.mut false) ⟨sIdx, [.deref]⟩) mem localDecls emptyLayoutTable =
        .ub) :=
  evalRvalue_len_and_frozen_mut_reborrow_wide_slice
    locals locals' mem localDecls sIdx elem lIdx entry rootVal containerProj baseIdx rawElemOffset
    elems p len hTy hRead hBorrow hSlot hBacking hOff

example
    (m : Mach) (ptrExpr idxExpr : ValueExpr) (elemTy : Gen.Type)
    (elemSz elemAlign : Nat) (thin : Ptr) (len idx : Nat)
    (hElemLayout : Type.layout elemTy = .ok (.Sized ⟨elemSz⟩ ⟨elemAlign⟩))
    (hPtrEval :
      evalValue m ptrExpr =
        .ok ((mrWidePtrVal thin (Int.ofNat len), .Ptr (.Raw .ElementCount)), m))
    (hIdxEval :
      evalValue m idxExpr =
        .ok ((.Int (Int.ofNat idx), .Int IntType.usize_ty), m)) :
    (len ≤ idx →
      Interp.evalPlace m (.Index (.Deref ptrExpr (.Slice elemTy)) idxExpr) =
        .error (.ub "access to out-of-bounds index")) ∧
    (idx < len →
      CM.signed_dereferenceable m.mem thin ((elemSz * idx : Nat) : Int) = .ok () →
      inBounds ((elemSz * idx : Nat) : Int) .Signed x86_64.PTR_SIZE = true →
      inBounds (thin.addr + ((elemSz * idx : Nat) : Int)) .Unsigned x86_64.PTR_SIZE = true →
      Interp.evalPlace m (.Index (.Deref ptrExpr (.Slice elemTy)) idxExpr) =
        .ok (({ ptr := ThinPointer.widen
                  { thin with addr := thin.addr + ((elemSz * idx : Nat) : Int) } none
                aligned := Align.is_aligned ⟨elemAlign⟩ thin.addr }, elemTy), m)) :=
  minirust_evalPlace_index_rawSlice
    m ptrExpr idxExpr elemTy elemSz elemAlign thin len idx hElemLayout hPtrEval hIdxEval

example
    (locals : List LocalSlot) (mem : MirSemantics.Memory)
    (localDecls : List MirAst.LocalDecl) (sIdx idxLocal : Local)
    (elemKind : RigidTy) (lIdx : LayoutIdx)
    (p : ProvenancePtr) (len idx szIdx : Nat)
    (entry : BorrowEntry) (rootVal : MirSemantics.Value)
    (containerProj : List ProjectionElem) (baseIdx rawElemOffset : Nat)
    (elems : List MirSemantics.Value)
    (m : Mach) (ptrExpr idxExpr : ValueExpr) (elemTy : Gen.Type)
    (elemSz elemAlign : Nat) (thin : Ptr)
    (hPointeeTy : placeTyResolved localDecls emptyLayoutTable ⟨sIdx, [.deref]⟩ =
      some { kind := .slice elemKind, layoutIdx := lIdx })
    (hSlSlot : Trusted.Sequence.get? locals sIdx = some (.init (annealWidePtrVal p len 8)))
    (hAlignDeref : checkDerefAlign localDecls emptyLayoutTable
      (some { kind := .slice elemKind, layoutIdx := lIdx }) p.offsetBytes = true)
    (hBorrow : lookupBorrow mem.borrows p.tag = some entry)
    (hPerm : entry.perm ≠ .disabled)
    (hSlot : activeFrameSlot? locals mem.callStack entry.targetFrameDepth entry.targetLocal =
      some (.init rootVal))
    (hAlignTarget : checkTargetPlaceAlign localDecls emptyLayoutTable
      (some { kind := .slice elemKind, layoutIdx := lIdx })
      entry p (some rootVal) emptyLayoutTable localDecls = true)
    (hBacking : readSliceBackingAggregate? locals rootVal entry.targetProjection len
      (rigidTyKindByteSize elemKind) = some (containerProj, baseIdx, elems))
    (hOff : byteOffsetToElemIdx? p.offsetBytes
      ((rigidTyKindByteSize elemKind).getD (inferElemListByteStride elems)) = some rawElemOffset)
    (hInBacking : rawElemOffset + baseIdx + len ≤ elems.length)
    (hIdxSlot : Trusted.Sequence.get? locals idxLocal = some (.init (.scalar ⟨idx, szIdx⟩)))
    (hElemLayout : Type.layout elemTy = .ok (.Sized ⟨elemSz⟩ ⟨elemAlign⟩))
    (hPtrEval :
      evalValue m ptrExpr =
        .ok ((mrWidePtrVal thin (Int.ofNat len), .Ptr (.Raw .ElementCount)), m))
    (hIdxEval :
      evalValue m idxExpr =
        .ok ((.Int (Int.ofNat idx), .Int IntType.usize_ty), m)) :
    (len ≤ idx →
      evalPlaceRead locals ⟨sIdx, [.deref, .index idxLocal]⟩ mem.borrows mem.globals
        emptyLayoutTable mem.callerLocals localDecls mem.callStack = .ub ∧
      Interp.evalPlace m (.Index (.Deref ptrExpr (.Slice elemTy)) idxExpr) =
        .error (.ub "access to out-of-bounds index")) ∧
    (∀ elemVal,
      idx < len →
      Trusted.Sequence.get? elems (rawElemOffset + baseIdx + idx) = some elemVal →
      valueContainsUninit elemVal = false →
      validateValueForTy? emptyLayoutTable
        (placeTyResolved localDecls emptyLayoutTable ⟨sIdx, [.deref, .index idxLocal]⟩) elemVal = true →
      evalPlaceRead locals ⟨sIdx, [.deref, .index idxLocal]⟩ mem.borrows mem.globals
        emptyLayoutTable mem.callerLocals localDecls mem.callStack = .ok elemVal locals ∧
      (CM.signed_dereferenceable m.mem thin ((elemSz * idx : Nat) : Int) = .ok () →
        inBounds ((elemSz * idx : Nat) : Int) .Signed x86_64.PTR_SIZE = true →
        inBounds (thin.addr + ((elemSz * idx : Nat) : Int)) .Unsigned x86_64.PTR_SIZE = true →
        Interp.evalPlace m (.Index (.Deref ptrExpr (.Slice elemTy)) idxExpr) =
          .ok (({ ptr := ThinPointer.widen
                    { thin with addr := thin.addr + ((elemSz * idx : Nat) : Int) } none
                  aligned := Align.is_aligned ⟨elemAlign⟩ thin.addr }, elemTy), m))) :=
  evalPlaceRead_index_wide_slice_borrowBacked_lockstep
    locals mem localDecls sIdx idxLocal elemKind lIdx p len idx szIdx entry rootVal
    containerProj baseIdx rawElemOffset elems m ptrExpr idxExpr elemTy elemSz elemAlign thin
    hPointeeTy hSlSlot hAlignDeref hBorrow hPerm hSlot hAlignTarget hBacking hOff hInBacking
    hIdxSlot hElemLayout hPtrEval hIdxEval

example
    (thin : Ptr) (prov : Option Prov) (mutbl : MirAst.Mutability)
    (elemSz elemAlign addr len : Nat) (freeze : Bool) (m : Option Mach)
    (pDang : ProvenancePtr)
    (localsNullProv localsSc localsDangMut : List LocalSlot)
    (localDecls : List MirAst.LocalDecl) (sIdx : Local)
    (hLen : len < scalarModulus 8)
    (hNullProvSlot :
      Trusted.Sequence.get? localsNullProv sIdx =
        some (.init (annealWidePtrVal { allocId := 0, offsetBytes := 0 } 0 8)))
    (hScSlot :
      Trusted.Sequence.get? localsSc sIdx =
        some (.init (annealWideScalarPtrVal addr len 8)))
    (hDangMutSlot :
      Trusted.Sequence.get? localsDangMut sIdx =
        some (.init (annealWidePtrVal pDang 0 8))) :
    (x86_64.valid_size ⟨len * elemSz⟩ = true →
      checkPtr (ThinPointer.widen { addr := 0, provenance := prov } (some (.ElementCount (Int.ofNat len))))
        (sliceRefPtrType mutbl ⟨elemSz⟩ ⟨elemAlign⟩ freeze) m =
        .error (.ub "Value::Ptr: null safe pointer")) ∧
    evalRvalue localsNullProv (.ref .shared ⟨sIdx, [.deref]⟩) emptyMemory localDecls emptyLayoutTable = .ub ∧
    evalRvalue localsSc (.ref .shared ⟨sIdx, [.deref]⟩) emptyMemory localDecls emptyLayoutTable = .ub ∧
    evalRvalue localsDangMut (.ref (.mut false) ⟨sIdx, [.deref]⟩) emptyMemory localDecls emptyLayoutTable = .ub ∧
    (inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true →
      (thin.addr != 0) = true →
      Align.is_aligned ⟨elemAlign⟩ thin.addr = true →
      checkPtr (ThinPointer.widen thin (some (.ElementCount 0)))
        (sliceRefPtrType mutbl ⟨elemSz⟩ ⟨elemAlign⟩ freeze) m = .ok () ∧
      checkPtr (ThinPointer.widen thin (some (.ElementCount (Int.ofNat len))))
        (sliceRefPtrType mutbl ⟨0⟩ ⟨elemAlign⟩ freeze) m = .ok ()) :=
  checkPtr_sliceRef_null_and_zeroByte_reborrow_divergence
    thin prov mutbl elemSz elemAlign addr len freeze m pDang
    localsNullProv localsSc localsDangMut localDecls sIdx
    hLen hNullProvSlot hScSlot hDangMutSlot

example
    (locals : List LocalSlot) (mem : MirSemantics.Memory)
    (localDecls : List MirAst.LocalDecl) (idxLocal : Local)
    (p : ProvenancePtr) (len idx szIdx fromIdx toIdx : Nat)
    (perm : TreeBorrowPerm) (isMut : Bool) (elemKind : RigidTy)
    (entry : BorrowEntry) (rootVal newVal : MirSemantics.Value)
    (containerProj : List ProjectionElem) (baseIdx rawElemOffset : Nat)
    (elems : List MirSemantics.Value)
    (hIdxSlot : Trusted.Sequence.get? locals idxLocal = some (.init (.scalar ⟨idx, szIdx⟩)))
    (hBorrow : lookupBorrow mem.borrows p.tag = some entry)
    (hParentPerm : entry.perm = .active)
    (hSlot : activeFrameSlot? locals mem.callStack entry.targetFrameDepth entry.targetLocal =
      some (.init rootVal))
    (hBacking : readSliceBackingAggregate? locals rootVal entry.targetProjection len
      (tyByteSize .nil emptyLayoutTable { kind := elemKind, layoutIdx := 0 }) =
      some (containerProj, baseIdx, elems))
    (hOff : byteOffsetToElemIdx? p.offsetBytes (inferElemListByteStride elems) = some rawElemOffset)
    (hInBacking : rawElemOffset + baseIdx + len ≤ elems.length) :
    let window := takeValues len (dropValues (Nat.add rawElemOffset baseIdx) elems)
    let slicePointeeTy : Ty := { kind := .slice elemKind, layoutIdx := 0 }
    (len ≤ idx →
      writeProjectedValue locals (.aggregate 0 window) [.index idxLocal] newVal = .ub) ∧
    (∀ oldElem updatedWindow,
      idx < len →
      Trusted.Sequence.get? window idx = some oldElem →
      Trusted.Sequence.set? window idx newVal = some updatedWindow →
      writeProjectedValue locals (.aggregate 0 window) [.index idxLocal] newVal =
        .ok (.aggregate 0 updatedWindow)) ∧
    (len < fromIdx + toIdx →
      evalSliceFatPtrDerefBorrow locals mem p 8 ⟨len, 8⟩ [.subslice fromIdx toIdx true]
        perm isMut (some slicePointeeTy) emptyLayoutTable true localDecls none false = .ub) ∧
    (fromIdx + toIdx ≤ len →
      ∃ mem',
        evalSliceFatPtrDerefBorrow locals mem p 8 ⟨len, 8⟩ [.subslice fromIdx toIdx true]
          perm isMut (some slicePointeeTy) emptyLayoutTable true localDecls none false =
          .ok (annealWidePtrVal { allocId := mem.nextTag, offsetBytes := 0 }
                (len - toIdx - fromIdx) 8) locals mem' ∧
        mem'.nextTag = mem.nextTag + 1) :=
  writeProjectedValue_and_subslice_reborrow_wide_slice
    locals mem localDecls idxLocal p len idx szIdx fromIdx toIdx perm isMut elemKind
    entry rootVal newVal containerProj baseIdx rawElemOffset elems hIdxSlot hBorrow
    hParentPerm hSlot hBacking hOff hInBacking

example
    (locals : List LocalSlot) (decls : List MirAst.LocalDecl)
    (len offset minLen baseIdx rawElemOffset : Nat) (fromEnd : Bool)
    (elems : List MirSemantics.Value)
    (hInBacking : rawElemOffset + baseIdx + len ≤ elems.length)
    (hLenLt : len < 2 ^ 63) :
    let window := takeValues len (dropValues (Nat.add rawElemOffset baseIdx) elems)
    let idx := if fromEnd then len - offset else offset
    (len < minLen →
      readProjectedValue locals (.aggregate 0 window) [.constantIndex offset minLen fromEnd] = .ub ∧
      projOk decls len (.constantIndex offset minLen fromEnd) = false) ∧
    (∀ elemVal,
      minLen ≤ len →
      ((fromEnd = false ∧ offset < minLen) ∨ (fromEnd = true ∧ 1 ≤ offset ∧ offset ≤ minLen)) →
      Trusted.Sequence.get? elems (rawElemOffset + baseIdx + idx) = some elemVal →
      valueContainsUninit elemVal = false →
      projOk decls len (.constantIndex offset minLen fromEnd) = true ∧
      readProjectedValue locals (.aggregate 0 window) [.constantIndex offset minLen fromEnd] =
        .ok elemVal) ∧
    (∀ elem0,
      0 < len →
      minLen ≤ len →
      len < offset →
      Trusted.Sequence.get? elems (rawElemOffset + baseIdx) = some elem0 →
      valueContainsUninit elem0 = false →
      projOk decls len (.constantIndex offset minLen true) = false ∧
      readProjectedValue locals (.aggregate 0 window) [.constantIndex offset minLen true] =
        .ok elem0) :=
  readProjectedValue_constantIndex_wide_slice_and_saturation
    locals decls len offset minLen baseIdx rawElemOffset fromEnd elems hInBacking hLenLt

end WideSliceDstStatementPins

end WideSliceDstAuditPins

section Ep1ExprAndMetaUnOpAudit

open MiniRustSpec
open MiniRustSpec.Gen
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp
open MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.RefWitness
open MiniRustSpec.Correspondence.TbWitness

/-! ## Episode 1: `UnOp.{GetMetadata, ComputeSize, ComputeAlign}`, `PlaceExpr.Downcast`,
and `ValueExpr.{Union, Variant, GetDiscriminant}` — Equational Laws, Preservation, and Witnesses -/

/-- `Type::meta_kind` agrees with `LayoutStrategy::meta_kind` for every type whose
`Type::layout` succeeds (proving upstream `spec/lang/types.md:182`). -/
theorem ep1_type_meta_kind_eq_layout_meta_kind :
    ∀ (ty : Gen.Type) (lay : Gen.LayoutStrategy),
      Type.layout ty = .ok lay → Type.meta_kind ty = LayoutStrategy.meta_kind lay
  | .Int t, lay, h => by
    unfold Type.layout at h
    cases hal : IntType.align t with
    | error _ => simp [hal, bind, Except.bind] at h
    | ok a =>
      simp [hal, bind, Except.bind, pure, Except.pure] at h
      subst h; rfl
  | .Bool, lay, h => by
    simp [Type.layout, pure, Except.pure] at h; subst h; rfl
  | .Ptr p, lay, h => by
    unfold Type.layout at h
    split at h <;> (simp [pure, Except.pure] at h; subst h; rfl)
  | .Union _ _ _ _, lay, h => by
    simp [Type.layout, pure, Except.pure] at h; subst h; rfl
  | .Enum _ _ _ _ _, lay, h => by
    simp [Type.layout, pure, Except.pure] at h; subst h; rfl
  | .Tuple _ _ none, lay, h => by
    simp [Type.layout, pure, Except.pure] at h; subst h; rfl
  | .Tuple _ head (some tail), lay, h => by
    unfold Type.layout at h
    cases htl : Type.layout tail with
    | error _ => simp [htl, bind, Except.bind] at h
    | ok tailLay =>
      simp [htl, bind, Except.bind, pure, Except.pure] at h
      subst h
      simpa [Type.meta_kind, LayoutStrategy.meta_kind] using
        ep1_type_meta_kind_eq_layout_meta_kind tail tailLay htl
  | .Array elem count, lay, h => by
    unfold Type.layout at h
    cases hel : Type.layout elem with
    | error _ => simp [hel, bind, Except.bind] at h
    | ok el =>
      simp [hel, bind, Except.bind] at h
      cases hsz : LayoutStrategy.expect_size el "WF ensures array element is sized" with
      | error _ => simp [hsz] at h
      | ok es =>
        simp [hsz] at h
        cases hal : LayoutStrategy.expect_align el "WF ensures array element is sized" with
        | error _ => simp [hal] at h
        | ok ea =>
          simp [hal] at h
          cases hmul : Size.mulInt es count with
          | error _ => simp [hmul] at h
          | ok sz =>
            simp [hmul] at h
            subst h; rfl
  | .Slice elem, lay, h => by
    unfold Type.layout at h
    cases hel : Type.layout elem with
    | error _ => simp [hel, bind, Except.bind] at h
    | ok el =>
      simp [hel, bind, Except.bind] at h
      cases hsz : LayoutStrategy.expect_size el "WF ensures slice element is sized" with
      | error _ => simp [hsz] at h
      | ok es =>
        simp [hsz] at h
        cases hal : LayoutStrategy.expect_align el "WF ensures array element is sized" with
        | error _ => simp [hal] at h
        | ok ea =>
          simp [hal] at h
          subst h; rfl
  | .TraitObject _, lay, h => by
    simp [Type.layout, pure, Except.pure] at h; subst h; rfl

private theorem ep1_compute_size_and_align_nonVTable_indep {P : Type}
    (vt1 vt2 : Gen.ThinPointer P → Interp Gen.VTable) :
    ∀ (lay : Gen.LayoutStrategy) (pm : Option (Gen.PointerMeta P)),
      (∀ p, pm ≠ some (.VTablePointer p)) →
      LayoutStrategy.compute_size_and_align vt1 lay pm =
        LayoutStrategy.compute_size_and_align vt2 lay pm
  | .Sized _ _, none, _ => rfl
  | .Sized _ _, some _, _ => rfl
  | .Slice _ _, none, _ => rfl
  | .Slice _ _, some (.ElementCount _), _ => rfl
  | .Slice _ _, some (.VTablePointer p), h => absurd rfl (h p)
  | .TraitObject _, none, _ => rfl
  | .TraitObject _, some (.ElementCount _), _ => rfl
  | .TraitObject _, some (.VTablePointer p), h => absurd rfl (h p)
  | .Tuple _ _, none, _ => rfl
  | .Tuple head tail, some pm, h => by
    unfold LayoutStrategy.compute_size_and_align
    rw [ep1_compute_size_and_align_nonVTable_indep vt1 vt2 tail (some pm) h]

private theorem ep1_decode_valueM_nonVTable {M : Type} [Gen.Memory M]
    (ty : Gen.Type) (v : Gen.Value M)
    (hnv : ∀ t, Type.meta_kind ty ≠ .VTablePointer t)
    (pm : Option (Gen.PointerMeta (Gen.Memory.Provenance M)))
    (hdv : PointerMetaKind.decode_valueM (M := M) (Type.meta_kind ty) v = .ok pm) :
    ∀ p, pm ≠ some (.VTablePointer p) := by
  intro p hEq
  subst hEq
  cases hk : Type.meta_kind ty with
  | VTablePointer t => exact absurd hk (hnv t)
  | None =>
    rw [hk] at hdv; unfold PointerMetaKind.decode_valueM at hdv
    split at hdv <;> simp_all [pure, Except.pure, specPanic]
  | ElementCount =>
    rw [hk] at hdv; unfold PointerMetaKind.decode_valueM at hdv
    split at hdv <;> simp_all [pure, Except.pure, specPanic]

/-- Non-vtable `ComputeSize` and `ComputeAlign` never invoke `vtableLookupM`, so
evaluating them with `some mach` and with `none` agree identically on every
`Memory` `M` (and on `Mach` via `evalUnOpM_bm_eq`). On a trait-object type
(`Type.meta_kind ty = .VTablePointer _`) the two differ: `some mach` reads the
machine's vtables, while `none` fails closed. -/
theorem ep1_evalUnOpM_computeSize_computeAlign_mach_indep
    {M : Type} [Gen.Memory M] [MemoryOps M]
    (ty opTy : Gen.Type) (v : Gen.Value M) (mach : Gen.Machine M)
    (hNonVT : ∀ t, Type.meta_kind ty ≠ .VTablePointer t) :
    evalUnOpM (.ComputeSize ty) (v, opTy) (some mach) =
      evalUnOpM (.ComputeSize ty) (v, opTy) none ∧
    evalUnOpM (.ComputeAlign ty) (v, opTy) (some mach) =
      evalUnOpM (.ComputeAlign ty) (v, opTy) none := by
  constructor
  · unfold evalUnOpM; dsimp only; simp only [bind, Except.bind]
    cases hdv : PointerMetaKind.decode_valueM (M := M) (Type.meta_kind ty) v with
    | error _ => rfl
    | ok pm =>
      dsimp only
      cases hlay : Type.layout ty with
      | error _ => rfl
      | ok lay =>
        simp only [computeSizeM, Functor.map, Except.map, bind, Except.bind, pure, Except.pure]
        rw [ep1_compute_size_and_align_nonVTable_indep (vtableLookupM mach)
          (fun _ => unsupported "eval_un_op UnOp::ComputeSize for vtable pointer metadata")
          lay pm (ep1_decode_valueM_nonVTable ty v hNonVT pm hdv)]
  · unfold evalUnOpM; dsimp only; simp only [bind, Except.bind]
    cases hdv : PointerMetaKind.decode_valueM (M := M) (Type.meta_kind ty) v with
    | error _ => rfl
    | ok pm =>
      dsimp only
      cases hlay : Type.layout ty with
      | error _ => rfl
      | ok lay =>
        simp only [computeAlignM, Functor.map, Except.map, bind, Except.bind, pure, Except.pure]
        rw [ep1_compute_size_and_align_nonVTable_indep (vtableLookupM mach)
          (fun _ => unsupported "eval_un_op UnOp::ComputeAlign for vtable pointer metadata")
          lay pm (ep1_decode_valueM_nonVTable ty v hNonVT pm hdv)]

/-- Universal specification of `evalUnOpM` on `GetMetadata`, `ComputeSize`,
`ComputeAlign` (including unsized structs with a slice tail), the machine-free
(`m = none`) fail-closed vtable boundaries (`VTablePointer` metadata and
`VTableMethodLookup` on a pointer operand), and upstream's
`panic!("vtable lookup on non-pointer")` on a non-pointer operand (with or
without a machine). -/
theorem ep1_evalUnOpM_meta_unops_spec {M : Type} [Gen.Memory M] [MemoryOps M]
    (thin vptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (fields : List (Gen.Offset × Gen.Type)) (head : Gen.TupleHeadLayout)
    (elemTy opTy : Gen.Type) (elemSz elemAlign len : Nat)
    (badCount : Int) (traitName : Gen.TraitName) (meth : Gen.TraitMethodName)
    (m : Option (Gen.Machine M))
    (hElemLayout : Type.layout elemTy = .ok (.Sized ⟨elemSz⟩ ⟨elemAlign⟩))
    (hBadCount : IntType.can_represent IntType.usize_ty badCount = false) :
    let dstTy : Gen.Type := .Tuple fields head (some (.Slice elemTy))
    let dstPair := TupleHeadLayout.full_size_and_align head ⟨len * elemSz⟩ ⟨elemAlign⟩
    evalUnOpM (M := M) .GetMetadata
        (.Ptr (ThinPointer.widen thin (some (.ElementCount badCount))), .Ptr (.Raw .ElementCount)) m =
      specPanic "GetMetadata: sanity check, returned meta is well-formed" ∧
    evalUnOpM (M := M) .GetMetadata (.Int 0, .Ptr (.Raw .None)) m =
      specPanic "non-pointer GetMetadata" ∧
    evalUnOpM (M := M) .GetMetadata (.Ptr (ThinPointer.widen thin none), .Ptr (.Raw .ElementCount)) m =
      specPanic "PointerMeta::encode_as_value called with invalid value" ∧
    evalUnOpM (M := M) (.ComputeSize dstTy) (.Int (Int.ofNat len), .Int IntType.usize_ty) m =
      .ok (.Int (dstPair.1.bytes : Int), .Int IntType.usize_ty) ∧
    evalUnOpM (M := M) (.ComputeAlign dstTy) (.Int (Int.ofNat len), .Int IntType.usize_ty) m =
      .ok (.Int (dstPair.2.bytes : Int), .Int IntType.usize_ty) ∧
    evalUnOpM (M := M) (.ComputeSize (.Tuple fields head (some (.TraitObject traitName))))
        (.Ptr (ThinPointer.widen vptr none), .Ptr (.VTablePtr traitName)) none =
      unsupported "eval_un_op UnOp::ComputeSize for vtable pointer metadata" ∧
    evalUnOpM (M := M) (.ComputeAlign (.Tuple fields head (some (.TraitObject traitName))))
        (.Ptr (ThinPointer.widen vptr none), .Ptr (.VTablePtr traitName)) none =
      unsupported "eval_un_op UnOp::ComputeAlign for vtable pointer metadata" ∧
    evalUnOpM (M := M) (.VTableMethodLookup meth)
        (.Ptr (ThinPointer.widen vptr none), .Ptr (.VTablePtr traitName)) none =
      unsupported "eval_un_op for UnOp::VTableMethodLookup" ∧
    evalUnOpM (M := M) (.VTableMethodLookup meth) (.Int 0, opTy) m =
      specPanic "vtable lookup on non-pointer" := by
  have hDstLayout : Type.layout (.Tuple fields head (some (.Slice elemTy))) =
      .ok (.Tuple head (.Slice ⟨elemSz⟩ ⟨elemAlign⟩)) := by
    simp [Type.layout, hElemLayout, LayoutStrategy.expect_size, LayoutStrategy.expect_align,
      bind, Except.bind, pure, Except.pure]
  refine ⟨?_, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp [evalUnOpM, ThinPointer.widen, PtrType.meta_kind, PointerMetaKind.encode_as_valueM,
      PointerMetaKind.ty, checkValueM, ensureElseUb, hBadCount, ub, bind, Except.bind, pure,
      Except.pure]
  · cases m <;>
      simp [evalUnOpM, Type.meta_kind, PointerMetaKind.decode_valueM, hDstLayout, computeSizeM,
        LayoutStrategy.compute_size_and_align, Functor.map, Except.map,
        bind, Except.bind, pure, Except.pure]
  · cases m <;>
      simp [evalUnOpM, Type.meta_kind, PointerMetaKind.decode_valueM, hDstLayout, computeAlignM,
        LayoutStrategy.compute_size_and_align, Functor.map, Except.map,
        bind, Except.bind, pure, Except.pure]

/-- Universal specification of `PlaceExpr.Downcast` across polymorphic `Machine M`,
`Mach` ↔ `Machine BM` agreement, and `MachTB.wfLive` preservation. -/
theorem ep1_evalPlaceM_downcast_spec_and_wfLive {M : Type} [Gen.Memory M] [MemoryOps M]
    (m m1 : Gen.Machine M) (root : Gen.PlaceExpr) (rp : Gen.Place M) (d : Int) :
    (∀ variants dty discr sz al var,
      evalPlaceM m root = .ok ((rp, .Enum variants dty discr sz al), m1) →
      mapIndex variants d "variants[discriminant]" = .ok var →
      evalPlaceM m (.Downcast root d) = .ok ((rp, var.ty), m1)) ∧
    (∀ variants dty discr sz al err,
      evalPlaceM m root = .ok ((rp, .Enum variants dty discr sz al), m1) →
      mapIndex variants d "variants[discriminant]" = .error err →
      evalPlaceM m (.Downcast root d) = .error err) ∧
    (∀ it,
      evalPlaceM m root = .ok ((rp, .Int it), m1) →
      evalPlaceM m (.Downcast root d) = specPanic "enum downcast on non-enum") ∧
    (∀ (mBM : Mach), evalPlaceM (M := BM) mBM (.Downcast root d) = evalPlace mBM (.Downcast root d)) ∧
    (∀ (mTB mTB' : MachTB) (out : Gen.Place TBM × Gen.Type),
      MachTB.wfLive mTB → evalPlaceM mTB (.Downcast root d) = .ok (out, mTB') →
      MachTB.wfLive mTB') := by
  refine ⟨?_, ?_, ?_, fun mBM => evalPlaceM_bm_eq mBM (.Downcast root d),
    fun mTB mTB' out hwf h => evalPlaceM_tb_wfLive (.Downcast root d) hwf h⟩
  · intro variants dty discr sz al var hroot hidx
    simp [evalPlaceM, hroot, hidx, bind, Except.bind, pure, Except.pure]
  · intro variants dty discr sz al err hroot hidx
    simp [evalPlaceM, hroot, hidx, bind, Except.bind]
  · intro it hroot
    simp [evalPlaceM, hroot, specPanic, bind, Except.bind]

/-- Universal specification of `ValueExpr.{Union, Variant, GetDiscriminant}` across
polymorphic `Machine M`, `Mach` ↔ `Machine BM` agreement, and `MachTB.wfLive`
preservation. -/
theorem ep1_evalValueM_union_variant_getDiscriminant_spec_and_wfLive
    {M : Type} [Gen.Memory M] [MemoryOps M]
    (m m1 : Gen.Machine M) :
    (∀ d data enumTy val vty,
      evalValueM m data = .ok ((val, vty), m1) →
      evalValueM m (.Variant d data enumTy) = .ok ((.Variant d val, enumTy), m1)) ∧
    (∀ field expr it,
      evalValueM m (.Union field expr (.Int it)) = specPanic "ValueExpr::Union requires union type") ∧
    (∀ field expr fields chunks sz al err,
      listIndex fields field "fields[field]" = .error err →
      evalValueM m (.Union field expr (.Union fields chunks sz al)) = .error err) ∧
    (∀ place rp it,
      evalPlaceM m place = .ok ((rp, .Int it), m1) →
      evalValueM m (.GetDiscriminant place) =
        specPanic "ValueExpr::GetDiscriminant requires enum type") ∧
    (∀ place rp variants dty discr sz al,
      evalPlaceM m place = .ok ((rp, .Enum variants dty discr sz al), m1) →
      rp.aligned = false →
      evalValueM m (.GetDiscriminant place) =
        ub "Getting the discriminant of a place based on a misaligned pointer.") ∧
    (∀ place rp variants dty discrVal sz al,
      evalPlaceM m place = .ok ((rp, .Enum variants dty (.Known discrVal) sz al), m1) →
      rp.aligned = true →
      evalValueM m (.GetDiscriminant place) = .ok ((.Int discrVal, .Int dty), m1)) ∧
    (∀ place rp variants dty sz al,
      evalPlaceM m place = .ok ((rp, .Enum variants dty .Invalid sz al), m1) →
      rp.aligned = true →
      evalValueM m (.GetDiscriminant place) =
        ub "ValueExpr::GetDiscriminant encountered invalid discriminant.") ∧
    (∀ (mBM : Mach) (ve : Gen.ValueExpr), evalValueM (M := BM) mBM ve = evalValue mBM ve) ∧
    (∀ (mTB mTB' : MachTB) (ve : Gen.ValueExpr) (out : Gen.Value TBM × Gen.Type),
      MachTB.wfLive mTB → evalValueM mTB ve = .ok (out, mTB') → MachTB.wfLive mTB') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun mBM ve => evalValueM_bm_eq mBM ve,
    fun mTB mTB' ve out hwf h => evalValueM_tb_wfLive ve hwf h⟩
  · intro d data enumTy val vty hd
    simp [evalValueM, hd, bind, Except.bind, pure, Except.pure]
  · intro field expr it
    simp [evalValueM, specPanic, bind, Except.bind]
  · intro field expr fields chunks sz al err hidx
    simp [evalValueM, hidx, bind, Except.bind, pure, Except.pure]
  · intro place rp it hp
    simp [evalValueM, hp, specPanic, bind, Except.bind]
  · intro place rp variants dty discr sz al hp hmis
    simp [evalValueM, hp, hmis, ub, bind, Except.bind]
  · intro place rp variants dty discrVal sz al hp hal
    simp [evalValueM, hp, hal, decodeDiscriminantM, bind, Except.bind, pure, Except.pure]
  · intro place rp variants dty sz al hp hal
    simp [evalValueM, hp, hal, decodeDiscriminantM, ub, bind, Except.bind, pure, Except.pure]

private def ep1U8 : Gen.IntType := ⟨.Unsigned, ⟨1⟩⟩
private def ep1U16 : Gen.IntType := ⟨.Unsigned, ⟨2⟩⟩
private def ep1U32 : Gen.IntType := ⟨.Unsigned, ⟨4⟩⟩

private def ep1EmptyProg : Gen.Program :=
  { functions := ⟨[]⟩, start := ⟨⟨0⟩⟩, globals := ⟨[]⟩, traits := ⟨[]⟩, vtables := ⟨[]⟩ }

private theorem ep1_bind_ok {α β : Type} {x : Interp α} {f : α → Interp β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases hx : x with
  | error e => simp [hx, bind, Except.bind] at h
  | ok a => simp [hx, bind, Except.bind] at h; exact ⟨a, rfl, h⟩

private theorem ep1_pure_ok {α : Type} {a b : α} (h : (pure a : Interp α) = .ok b) : a = b := by
  simpa [pure, Except.pure] using h

private def ep1Fn (locals : List (Gen.LocalName × Gen.Type)) : Gen.Function :=
  { locals := ⟨locals⟩, args := [], ret := ⟨⟨0⟩⟩, calling_convention := .Rust,
    blocks := ⟨[(⟨⟨0⟩⟩, ⟨[], .Unreachable, .Regular⟩)]⟩, start := ⟨⟨0⟩⟩,
    implicit_writes := false }

private def ep1MachBM (allocs : List (Gen.Allocation Unit Unit))
    (locals : List (Gen.LocalName × Ptr)) (localTys : List (Gen.LocalName × Gen.Type)) : Mach :=
  { prog := ep1EmptyProg
    mem := { memory := { allocations := allocs, _phantom := ⟨⟩ }, accesses := [] }
    intptrcast := ⟨⟨[]⟩⟩
    threads := [{ stack := [{ func := ep1Fn localTys, locals := ⟨locals⟩,
                              stack_pop_action := .BottomOfStack, next_block := ⟨⟨0⟩⟩,
                              next_stmt := 0, extra := () }],
                  state := .Enabled, unwind_payloads := [] }]
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[]⟩
    fn_ptrs := ⟨[]⟩
    vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

private def ep1AllocTB (addr : Int) (al : Nat)
    (bs : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (children : List Gen.Node := [])
    (rootPerms : List Gen.Permission := List.replicate bs.length (.Unprot .Unique)) :
    Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra :=
  { data := bs, addr := addr, align := ⟨al⟩, kind := .Stack, live := true,
    extra := { root := { children := children, permissions := rootPerms, «protected» := .No } } }

private def ep1MachTB (allocs : List (Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra))
    (locals : List (Gen.LocalName × Gen.ThinPointer Gen.TreeBorrowsProvenance))
    (localTys : List (Gen.LocalName × Gen.Type)) : MachTB :=
  { prog := ep1EmptyProg
    mem := { memory := { params := { implicit_writes := false },
                         mem := { allocations := allocs, _phantom := ⟨⟩ } },
             accesses := [] }
    intptrcast := ⟨⟨[]⟩⟩
    threads := [{ stack := [{ func := ep1Fn localTys, locals := ⟨locals⟩,
                              stack_pop_action := .BottomOfStack, next_block := ⟨⟨0⟩⟩,
                              next_stmt := 0, extra := ⟨[]⟩ }],
                  state := .Enabled, unwind_payloads := [] }]
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[]⟩
    fn_ptrs := ⟨[]⟩
    vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

private def ep1Var0TupleTy : Gen.Type := .Tuple [] ⟨⟨8⟩, ⟨4⟩, none⟩ none
private def ep1Var1TupleTy : Gen.Type := .Tuple [(⟨4⟩, .Int ep1U32)] ⟨⟨8⟩, ⟨4⟩, none⟩ none

/-- 8-byte align-4 enum: `u8` tag at offset `0`, variant `0` unit, variant `1` with
`u32` payload at offset `4`. -/
private def ep1EnumTy : Gen.Type :=
  let v0 : Gen.Variant := { ty := ep1Var0TupleTy, tagger := ⟨[(⟨0⟩, (ep1U8, 0))]⟩ }
  let v1 : Gen.Variant := { ty := ep1Var1TupleTy, tagger := ⟨[(⟨0⟩, (ep1U8, 1))]⟩ }
  let disc : Gen.Discriminator :=
    .Branch ⟨0⟩ ep1U8 .Invalid ⟨[((0, 1), .Known 0), ((1, 2), .Known 1)]⟩
  .Enum ⟨[(0, v0), (1, v1)]⟩ ep1U8 disc ⟨8⟩ ⟨4⟩

/-- Concrete kernel-checked witness for `ValueExpr.Variant`, `PlaceExpr.Downcast` +
`PlaceExpr.Field`, `ValueExpr.GetDiscriminant` (positive roundtrip, partial-read with
uninit payload vs `Load` UB, uninit tag UB, invalid tag UB, misaligned place UB, and
missing-variant / non-enum `Downcast` panics) across both `Mach` and `MachTB` (with
`MachTB.wfLive` preservation). -/
theorem ep1_enum_variant_downcast_getDiscriminant_witness :
    let localTys : List (Gen.LocalName × Gen.Type) :=
      [(⟨⟨0⟩⟩, .Int ep1U32), (⟨⟨1⟩⟩, ep1EnumTy), (⟨⟨2⟩⟩, ep1EnumTy), (⟨⟨3⟩⟩, .Int ep1U32)]
    let uninit8 {P : Type} : List (Gen.AbstractByte P) := List.replicate 8 .Uninit
    let badTag8 {P : Type} : List (Gen.AbstractByte P) :=
      [.Init 5 none, .Uninit, .Uninit, .Uninit, .Init 42 none, .Init 0 none, .Init 0 none, .Init 0 none]
    let mBM := ep1MachBM
      [{ data := uninit8, addr := 0x100, align := ⟨4⟩, kind := .Stack, live := true, extra := () },
       { data := badTag8, addr := 0x200, align := ⟨4⟩, kind := .Stack, live := true, extra := () },
       { data := List.replicate 4 .Uninit, addr := 0x300, align := ⟨4⟩, kind := .Stack, live := true, extra := () }]
      [(⟨⟨1⟩⟩, ⟨0x100, some (⟨0⟩, ())⟩), (⟨⟨2⟩⟩, ⟨0x200, some (⟨1⟩, ())⟩),
       (⟨⟨3⟩⟩, ⟨0x300, some (⟨2⟩, ())⟩)]
      localTys
    let mTB := liftMachToTB mBM
    let var1Expr : Gen.ValueExpr :=
      .Variant 1 (.Tuple [.Constant (.Int 42) (.Int ep1U32)] ep1Var1TupleTy) ep1EnumTy
    let payloadPlace : Gen.PlaceExpr := .Field (.Downcast (.Local ⟨⟨1⟩⟩) 1) 0
    let misalignPlace : Gen.PlaceExpr :=
      .Deref (.Constant (.PointerWithoutProvenance 0x101) (.Ptr (.Raw .None))) ep1EnumTy
    let loadUb := "load at type but the data in memory violates the language invariant"
    let invalidDiscrUb := "ValueExpr::GetDiscriminant encountered invalid discriminant."
    let misalignDiscrUb := "Getting the discriminant of a place based on a misaligned pointer."
    -- 1. Mach positive roundtrip: Variant store -> GetDiscriminant -> Downcast+Field load -> Downcast+Field store -> GetDiscriminant + full Load
    (∃ m1 m2 m3 m4 m5 m6,
      evalStatement mBM (.Assign (.Local ⟨⟨1⟩⟩) var1Expr) = .ok m1 ∧
      evalValue m1 (.GetDiscriminant (.Local ⟨⟨1⟩⟩)) = .ok ((.Int 1, .Int ep1U8), m2) ∧
      evalValue m2 (.Load payloadPlace) = .ok ((.Int 42, .Int ep1U32), m3) ∧
      evalStatement m3 (.Assign payloadPlace (.Constant (.Int 99) (.Int ep1U32))) = .ok m4 ∧
      evalValue m4 (.GetDiscriminant (.Local ⟨⟨1⟩⟩)) = .ok ((.Int 1, .Int ep1U8), m5) ∧
      evalValue m5 (.Load (.Local ⟨⟨1⟩⟩)) =
        .ok ((.Variant 1 (.Tuple [.Int 99]), ep1EnumTy), m6)) ∧
    -- 2. MachTB positive roundtrip + MachTB.wfLive preservation
    (∃ m1 m2 m3 m4 m5 m6,
      evalStatementM mTB (.Assign (.Local ⟨⟨1⟩⟩) var1Expr) = .ok m1 ∧
      evalValueM m1 (.GetDiscriminant (.Local ⟨⟨1⟩⟩)) = .ok ((.Int 1, .Int ep1U8), m2) ∧
      evalValueM m2 (.Load payloadPlace) = .ok ((.Int 42, .Int ep1U32), m3) ∧
      evalStatementM m3 (.Assign payloadPlace (.Constant (.Int 99) (.Int ep1U32))) = .ok m4 ∧
      evalValueM m4 (.GetDiscriminant (.Local ⟨⟨1⟩⟩)) = .ok ((.Int 1, .Int ep1U8), m5) ∧
      evalValueM m5 (.Load (.Local ⟨⟨1⟩⟩)) =
        .ok ((.Variant 1 (.Tuple [.Int 99]), ep1EnumTy), m6) ∧
      MachTB.wfLive m6) ∧
    -- 3. Partial-read guarantee: SetDiscriminant on uninit enum lets GetDiscriminant succeed while Load raises UB
    (∃ m1 m2,
      evalStatement mBM (.SetDiscriminant (.Local ⟨⟨1⟩⟩) 1) = .ok m1 ∧
      evalValue m1 (.GetDiscriminant (.Local ⟨⟨1⟩⟩)) = .ok ((.Int 1, .Int ep1U8), m2) ∧
      evalValue m1 (.Load (.Local ⟨⟨1⟩⟩)) = .error (.ub loadUb)) ∧
    (∃ m1 m2,
      evalStatementM mTB (.SetDiscriminant (.Local ⟨⟨1⟩⟩) 1) = .ok m1 ∧
      evalValueM m1 (.GetDiscriminant (.Local ⟨⟨1⟩⟩)) = .ok ((.Int 1, .Int ep1U8), m2) ∧
      evalValueM m1 (.Load (.Local ⟨⟨1⟩⟩)) = .error (.ub loadUb) ∧
      MachTB.wfLive m2) ∧
    -- 4. Negative UB & specPanic controls on both Mach and MachTB
    (evalValue mBM (.GetDiscriminant (.Local ⟨⟨1⟩⟩)) = .error (.ub invalidDiscrUb) ∧
     evalValueM mTB (.GetDiscriminant (.Local ⟨⟨1⟩⟩)) = .error (.ub invalidDiscrUb) ∧
     evalValue mBM (.GetDiscriminant (.Local ⟨⟨2⟩⟩)) = .error (.ub invalidDiscrUb) ∧
     evalValueM mTB (.GetDiscriminant (.Local ⟨⟨2⟩⟩)) = .error (.ub invalidDiscrUb) ∧
     evalValue mBM (.GetDiscriminant misalignPlace) = .error (.ub misalignDiscrUb) ∧
     evalValueM mTB (.GetDiscriminant misalignPlace) = .error (.ub misalignDiscrUb) ∧
     evalPlace mBM (.Downcast (.Local ⟨⟨1⟩⟩) 9) =
       specPanic "map index: missing key (variants[discriminant])" ∧
     evalPlaceM mTB (.Downcast (.Local ⟨⟨1⟩⟩) 9) =
       specPanic "map index: missing key (variants[discriminant])" ∧
     evalPlace mBM (.Downcast (.Local ⟨⟨3⟩⟩) 0) = specPanic "enum downcast on non-enum" ∧
     evalPlaceM mTB (.Downcast (.Local ⟨⟨3⟩⟩) 0) = specPanic "enum downcast on non-enum") := by
  intro localTys uninit8 badTag8 mBM mTB var1Expr payloadPlace misalignPlace loadUb invalidDiscrUb misalignDiscrUb
  refine ⟨⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ?_,
    ⟨_, _, rfl, rfl, rfl⟩,
    ⟨_, _, rfl, rfl, rfl, ?_⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · let seq : Interp ((Gen.Value TBM × Gen.Type) × (Gen.Value TBM × Gen.Type) ×
        (Gen.Value TBM × Gen.Type) × (Gen.Value TBM × Gen.Type) × MachTB) := do
      let m1 ← evalStatementM mTB (.Assign (.Local ⟨⟨1⟩⟩) var1Expr)
      let (r1, m2) ← evalValueM m1 (.GetDiscriminant (.Local ⟨⟨1⟩⟩))
      let (r2, m3) ← evalValueM m2 (.Load payloadPlace)
      let m4 ← evalStatementM m3 (.Assign payloadPlace (.Constant (.Int 99) (.Int ep1U32)))
      let (r3, m5) ← evalValueM m4 (.GetDiscriminant (.Local ⟨⟨1⟩⟩))
      let (r4, m6) ← evalValueM m5 (.Load (.Local ⟨⟨1⟩⟩))
      pure (r1, r2, r3, r4, m6)
    have hDec :
        (match seq with
         | .ok ((.Int 1, .Int ⟨.Unsigned, ⟨1⟩⟩),
                (.Int 42, .Int ⟨.Unsigned, ⟨4⟩⟩),
                (.Int 1, .Int ⟨.Unsigned, ⟨1⟩⟩),
                (.Variant 1 (.Tuple [.Int 99]),
                 .Enum ⟨[(0, { ty := .Tuple [] ⟨⟨8⟩, ⟨4⟩, none⟩ none,
                               tagger := ⟨[(⟨0⟩, (⟨.Unsigned, ⟨1⟩⟩, 0))]⟩ }),
                         (1, { ty := .Tuple [(⟨4⟩, .Int ⟨.Unsigned, ⟨4⟩⟩)] ⟨⟨8⟩, ⟨4⟩, none⟩ none,
                               tagger := ⟨[(⟨0⟩, (⟨.Unsigned, ⟨1⟩⟩, 1))]⟩ })]⟩
                   ⟨.Unsigned, ⟨1⟩⟩
                   (.Branch ⟨0⟩ ⟨.Unsigned, ⟨1⟩⟩ .Invalid ⟨[((0, 1), .Known 0), ((1, 2), .Known 1)]⟩)
                   ⟨8⟩ ⟨4⟩),
                _) => true
         | _ => false) = true := by decide +kernel
    cases hseq : seq with
    | error _ => rw [hseq] at hDec; cases hDec
    | ok res =>
      rw [hseq] at hDec
      rcases res with ⟨r1, r2, r3, r4, m6⟩
      dsimp only [seq] at hseq
      obtain ⟨m1, hs1, hseq⟩ := ep1_bind_ok hseq
      obtain ⟨⟨r1', m2⟩, hs2, hseq⟩ := ep1_bind_ok hseq
      obtain ⟨⟨r2', m3⟩, hs3, hseq⟩ := ep1_bind_ok hseq
      obtain ⟨m4, hs4, hseq⟩ := ep1_bind_ok hseq
      obtain ⟨⟨r3', m5⟩, hs5, hseq⟩ := ep1_bind_ok hseq
      obtain ⟨⟨r4', m6'⟩, hs6, hseq⟩ := ep1_bind_ok hseq
      have hp := ep1_pure_ok hseq
      dsimp only at hs1 hs2 hs3 hs4 hs5 hs6 hp
      simp only [Prod.mk.injEq] at hp
      rcases hp with ⟨rfl, rfl, rfl, rfl, rfl⟩
      have hwf0 : MachTB.wfLive mTB := liftMachToTB_wfLive mBM
      have hwf1 := evalStatementM_tb_wfLive hwf0 hs1
      have hwf2 := evalValueM_tb_wfLive _ hwf1 hs2
      have hwf3 := evalValueM_tb_wfLive _ hwf2 hs3
      have hwf4 := evalStatementM_tb_wfLive hwf3 hs4
      have hwf5 := evalValueM_tb_wfLive _ hwf4 hs5
      have hwf6 := evalValueM_tb_wfLive _ hwf5 hs6
      split at hDec
      · rename_i _ heq
        simp only [Except.ok.injEq, Prod.mk.injEq] at heq
        rcases heq with ⟨hr1, hr2, hr3, hr4, _⟩
        rw [hr1] at hs2; rw [hr2] at hs3; rw [hr3] at hs5; rw [hr4] at hs6
        exact ⟨m1, m2, m3, m4, m5, m6', hs1, hs2, hs3, hs4, hs5, hs6, hwf6⟩
      · cases hDec
  · have h0 : MachTB.wfLive mTB := liftMachToTB_wfLive mBM
    have h1 := evalStatementM_tb_wfLive (stmt := .SetDiscriminant (.Local ⟨⟨1⟩⟩) 1) h0 rfl
    exact evalValueM_tb_wfLive (.GetDiscriminant (.Local ⟨⟨1⟩⟩)) h1 rfl

/-- Byte-exact Tree Borrows read-access witness for `ValueExpr.GetDiscriminant`:
1. Disabled tag byte `0` on child provenance `[0]`: `GetDiscriminant` succeeds with `1`
   on `Mach` (`BasicMemory`) but raises Tree Borrows UB on `MachTB`;
2. Child `[0]` has `.Frozen` on tag bytes `[0..4)` and `.Disabled` on payload bytes
   `[4..8)`: `GetDiscriminant` succeeds on `MachTB` (touching only byte `0`), whereas
   `ValueExpr.Load` through the same child raises Tree Borrows UB;
3. Foreign `GetDiscriminant` read through root `[]` while child `[0]` is `.Unique` on
   all 8 bytes transitions child `[0]`'s byte `0` to `.Frozen` while leaving bytes
   `[1..8)` `.Unique` and preserving `MachTB.wfLive`. -/
theorem ep1_getDiscriminant_tree_borrows_read_access_witness :
    let enumBytes {P : Type} : List (Gen.AbstractByte P) :=
      [.Init 1 none, .Uninit, .Uninit, .Uninit, .Init 42 none, .Init 0 none, .Init 0 none, .Init 0 none]
    let localTys : List (Gen.LocalName × Gen.Type) :=
      [(⟨⟨0⟩⟩, ep1EnumTy), (⟨⟨1⟩⟩, .Ptr (.Raw .None))]
    let ptrBytesBM : List Byte := encodePtrBytes (some (⟨0⟩, ())) 0 [0x00, 0x01, 0, 0, 0, 0, 0, 0]
    let ptrBytesTB : List (Gen.AbstractByte Gen.TreeBorrowsProvenance) :=
      encodePtrBytesM (M := TBM) (some (⟨0⟩, [0])) 0 [0x00, 0x01, 0, 0, 0, 0, 0, 0]
    let mBM := ep1MachBM
      [{ data := enumBytes, addr := 0x100, align := ⟨4⟩, kind := .Stack, live := true, extra := () },
       { data := ptrBytesBM, addr := 0x200, align := ⟨8⟩, kind := .Stack, live := true, extra := () }]
      [(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, ())⟩), (⟨⟨1⟩⟩, ⟨0x200, some (⟨1⟩, ())⟩)]
      localTys
    let childDisabledTag : Gen.Node :=
      { children := [], permissions := List.replicate 8 (.Unprot .Disabled), «protected» := .No }
    let childDisabledPayload : Gen.Node :=
      { children := [],
        permissions := List.replicate 4 (.Unprot .Frozen) ++ List.replicate 4 (.Unprot .Disabled),
        «protected» := .No }
    let childUniqueAll : Gen.Node :=
      { children := [], permissions := List.replicate 8 (.Unprot .Unique), «protected» := .No }
    let mkTB (child : Gen.Node) : MachTB :=
      ep1MachTB
        [ep1AllocTB 0x100 4 enumBytes [child], ep1AllocTB 0x200 8 ptrBytesTB]
        [(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, [])⟩), (⟨⟨1⟩⟩, ⟨0x200, some (⟨1⟩, [])⟩)]
        localTys
    let derefChildPlace : Gen.PlaceExpr := .Deref (.Load (.Local ⟨⟨1⟩⟩)) ep1EnumTy
    let expectedFrozenTagPerms : List Gen.Permission :=
      .Unprot .Frozen :: List.replicate 7 (.Unprot .Unique)
    -- 1. Disabled tag byte: BM succeeds, TB faults with UB
    (∃ m1, evalValue mBM (.GetDiscriminant derefChildPlace) = .ok ((.Int 1, .Int ep1U8), m1)) ∧
    (∃ msg, evalValueM (mkTB childDisabledTag) (.GetDiscriminant derefChildPlace) = .error (.ub msg)) ∧
    -- 2. Disabled payload-only bytes: TB GetDiscriminant succeeds, TB Load faults with UB
    (∃ m1, evalValueM (mkTB childDisabledPayload) (.GetDiscriminant derefChildPlace) =
        .ok ((.Int 1, .Int ep1U8), m1)) ∧
    (∃ msg, evalValueM (mkTB childDisabledPayload) (.Load derefChildPlace) = .error (.ub msg)) ∧
    -- 3. Foreign GetDiscriminant through root freezes ONLY byte 0 of active child `[0]`
    (∃ m1,
      evalValueM (mkTB childUniqueAll) (.GetDiscriminant (.Local ⟨⟨0⟩⟩)) =
        .ok ((.Int 1, .Int ep1U8), m1) ∧
      m1.mem.memory.mem.allocations[0]?.bind (fun a => a.extra.root.children[0]?.map (·.permissions)) =
        some expectedFrozenTagPerms ∧
      MachTB.wfLive m1) := by
  intro enumBytes localTys ptrBytesBM ptrBytesTB mBM childDisabledTag childDisabledPayload childUniqueAll mkTB derefChildPlace expectedFrozenTagPerms
  refine ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl, rfl, ?_⟩⟩
  have hwf0 : MachTB.wfLive (mkTB childUniqueAll) := by
    intro alloc hmem _
    simp only [mkTB, childUniqueAll, ep1MachTB, ep1AllocTB, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · refine ⟨by decide, fun p hp => by simp at hp; subst hp; rfl,
        ⟨⟨by decide, fun p hp => by simp at hp; subst hp; rfl, trivial⟩, trivial⟩⟩
    · exact ⟨by decide, fun p hp => by simp at hp; rcases hp with ⟨_, rfl⟩; rfl, trivial⟩
  exact evalValueM_tb_wfLive (.GetDiscriminant (.Local ⟨⟨0⟩⟩)) hwf0 rfl

private def ep1UnionTy : Gen.Type :=
  .Union [(⟨0⟩, .Int ep1U32), (⟨0⟩, .Int ep1U16), (⟨2⟩, .Int ep1U16)] [(⟨0⟩, ⟨4⟩)] ⟨4⟩ ⟨4⟩

private def ep1PaddedUnionTy : Gen.Type :=
  .Union [(⟨0⟩, .Int ep1U8), (⟨2⟩, .Int ep1U8)] [(⟨0⟩, ⟨1⟩), (⟨2⟩, ⟨1⟩)] ⟨4⟩ ⟨2⟩

/-- Concrete kernel-checked witness for `ValueExpr.Union` construction, store +
little-endian field punning, partial-field write uninit-punning UB, padded-chunk
decoding, and pre-evaluation `specPanic` precedence across `Mach` and `MachTB` (with
`MachTB.wfLive` preservation). -/
theorem ep1_union_construct_punning_and_errors_witness :
    let localTys : List (Gen.LocalName × Gen.Type) :=
      [(⟨⟨0⟩⟩, ep1UnionTy), (⟨⟨1⟩⟩, ep1PaddedUnionTy), (⟨⟨2⟩⟩, .Int ep1U32)]
    let mBM := ep1MachBM
      [{ data := List.replicate 4 .Uninit, addr := 0x100, align := ⟨4⟩, kind := .Stack, live := true, extra := () },
       { data := List.replicate 4 .Uninit, addr := 0x200, align := ⟨2⟩, kind := .Stack, live := true, extra := () }]
      [(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, ())⟩), (⟨⟨1⟩⟩, ⟨0x200, some (⟨1⟩, ())⟩)]
      localTys
    let mTB := liftMachToTB mBM
    let u32UnionExpr : Gen.ValueExpr := .Union 0 (.Constant (.Int 0x00020001) (.Int ep1U32)) ep1UnionTy
    let u16UnionExpr : Gen.ValueExpr := .Union 1 (.Constant (.Int 0x1234) (.Int ep1U16)) ep1UnionTy
    let padUnionExpr : Gen.ValueExpr := .Union 0 (.Constant (.Int 0xAB) (.Int ep1U8)) ep1PaddedUnionTy
    let loadUb := "load at type but the data in memory violates the language invariant"
    -- 1. Mach: u32 write -> u16 punning reads (1 and 2); u16 write -> low ok, u32/high UB; padded union chunks
    (∃ m1 m2 m3 m4 m5,
      evalStatement mBM (.Assign (.Local ⟨⟨0⟩⟩) u32UnionExpr) = .ok m1 ∧
      evalValue m1 (.Load (.Field (.Local ⟨⟨0⟩⟩) 1)) = .ok ((.Int 1, .Int ep1U16), m2) ∧
      evalValue m2 (.Load (.Field (.Local ⟨⟨0⟩⟩) 2)) = .ok ((.Int 2, .Int ep1U16), m3) ∧
      evalStatement m3 (.Assign (.Local ⟨⟨0⟩⟩) u16UnionExpr) = .ok m4 ∧
      evalValue m4 (.Load (.Field (.Local ⟨⟨0⟩⟩) 1)) = .ok ((.Int 0x1234, .Int ep1U16), m5) ∧
      evalValue m5 (.Load (.Field (.Local ⟨⟨0⟩⟩) 0)) = .error (.ub loadUb) ∧
      evalValue m5 (.Load (.Field (.Local ⟨⟨0⟩⟩) 2)) = .error (.ub loadUb)) ∧
    -- 2. MachTB: exact same roundtrip + MachTB.wfLive preservation
    (∃ m1 m2 m3 m4 m5,
      evalStatementM mTB (.Assign (.Local ⟨⟨0⟩⟩) u32UnionExpr) = .ok m1 ∧
      evalValueM m1 (.Load (.Field (.Local ⟨⟨0⟩⟩) 1)) = .ok ((.Int 1, .Int ep1U16), m2) ∧
      evalValueM m2 (.Load (.Field (.Local ⟨⟨0⟩⟩) 2)) = .ok ((.Int 2, .Int ep1U16), m3) ∧
      evalStatementM m3 (.Assign (.Local ⟨⟨0⟩⟩) u16UnionExpr) = .ok m4 ∧
      evalValueM m4 (.Load (.Field (.Local ⟨⟨0⟩⟩) 1)) = .ok ((.Int 0x1234, .Int ep1U16), m5) ∧
      evalValueM m5 (.Load (.Field (.Local ⟨⟨0⟩⟩) 0)) = .error (.ub loadUb) ∧
      evalValueM m5 (.Load (.Field (.Local ⟨⟨0⟩⟩) 2)) = .error (.ub loadUb) ∧
      MachTB.wfLive m5) ∧
    -- 3. Padded union chunk extraction & pre-evaluation specPanic precedence (before dead local UB)
    (evalValue mBM padUnionExpr = .ok ((.Union [[.Init 0xAB none], [.Uninit]], ep1PaddedUnionTy), mBM) ∧
     evalValueM mTB padUnionExpr = .ok ((.Union [[.Init 0xAB none], [.Uninit]], ep1PaddedUnionTy), mTB) ∧
     evalValue mBM (.Union 99 (.Load (.Local ⟨⟨2⟩⟩)) ep1UnionTy) =
       specPanic "list index out of range (fields[field])" ∧
     evalValueM mTB (.Union 99 (.Load (.Local ⟨⟨2⟩⟩)) ep1UnionTy) =
       specPanic "list index out of range (fields[field])" ∧
     evalValue mBM (.Union 0 (.Load (.Local ⟨⟨2⟩⟩)) (.Int ep1U32)) =
       specPanic "ValueExpr::Union requires union type" ∧
     evalValueM mTB (.Union 0 (.Load (.Local ⟨⟨2⟩⟩)) (.Int ep1U32)) =
       specPanic "ValueExpr::Union requires union type") := by
  intro localTys mBM mTB u32UnionExpr u16UnionExpr padUnionExpr loadUb
  refine ⟨⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ?_,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  let seq : Interp ((Gen.Value TBM × Gen.Type) × (Gen.Value TBM × Gen.Type) ×
      (Gen.Value TBM × Gen.Type) × Interp ((Gen.Value TBM × Gen.Type) × MachTB) ×
      Interp ((Gen.Value TBM × Gen.Type) × MachTB) × MachTB) := do
    let m1 ← evalStatementM mTB (.Assign (.Local ⟨⟨0⟩⟩) u32UnionExpr)
    let (r1, m2) ← evalValueM m1 (.Load (.Field (.Local ⟨⟨0⟩⟩) 1))
    let (r2, m3) ← evalValueM m2 (.Load (.Field (.Local ⟨⟨0⟩⟩) 2))
    let m4 ← evalStatementM m3 (.Assign (.Local ⟨⟨0⟩⟩) u16UnionExpr)
    let (r3, m5) ← evalValueM m4 (.Load (.Field (.Local ⟨⟨0⟩⟩) 1))
    let e0 := evalValueM m5 (.Load (.Field (.Local ⟨⟨0⟩⟩) 0))
    let e2 := evalValueM m5 (.Load (.Field (.Local ⟨⟨0⟩⟩) 2))
    pure (r1, r2, r3, e0, e2, m5)
  have hDec :
      (match seq with
       | .ok ((.Int 1, .Int ⟨.Unsigned, ⟨2⟩⟩),
              (.Int 2, .Int ⟨.Unsigned, ⟨2⟩⟩),
              (.Int 0x1234, .Int ⟨.Unsigned, ⟨2⟩⟩),
              .error (.ub msg0),
              .error (.ub msg2),
              _) => decide (msg0 = loadUb ∧ msg2 = loadUb)
       | _ => false) = true := by decide +kernel
  cases hseq : seq with
  | error _ => rw [hseq] at hDec; cases hDec
  | ok res =>
    rw [hseq] at hDec
    rcases res with ⟨r1, r2, r3, e0, e2, m5⟩
    dsimp only [seq] at hseq
    obtain ⟨m1, hs1, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨⟨r1', m2⟩, hs2, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨⟨r2', m3⟩, hs3, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨m4, hs4, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨⟨r3', m5'⟩, hs5, hseq⟩ := ep1_bind_ok hseq
    have hp := ep1_pure_ok hseq
    dsimp only at hs1 hs2 hs3 hs4 hs5 hp
    simp only [Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl, rfl, he0, he2, rfl⟩
    have hwf0 : MachTB.wfLive mTB := liftMachToTB_wfLive mBM
    have hwf1 := evalStatementM_tb_wfLive hwf0 hs1
    have hwf2 := evalValueM_tb_wfLive _ hwf1 hs2
    have hwf3 := evalValueM_tb_wfLive _ hwf2 hs3
    have hwf4 := evalStatementM_tb_wfLive hwf3 hs4
    have hwf5 := evalValueM_tb_wfLive _ hwf4 hs5
    split at hDec
    · rename_i msg0 msg2 _ heq
      have ⟨hm0, hm2⟩ := of_decide_eq_true hDec
      subst hm0; subst hm2
      simp only [Except.ok.injEq, Prod.mk.injEq] at heq
      rcases heq with ⟨hr1, hr2, hr3, hhe0, hhe2, _⟩
      rw [hr1] at hs2; rw [hr2] at hs3; rw [hr3] at hs5
      rw [hhe0] at he0; rw [hhe2] at he2
      exact ⟨m1, m2, m3, m4, m5', hs1, hs2, hs3, hs4, hs5, he0, he2, hwf5⟩
    · cases hDec

/-- Concrete kernel-checked witness for `UnOp.{GetMetadata, ComputeSize, ComputeAlign}`
on sized types, `[u32]` slices, unsized `(u8, [u32])` and `#[repr(packed(2))] (u8, [u32])`
structs, negative/invalid-operand `specPanic` controls, and fail-closed `unsupported`
on vtable metadata and `VTableMethodLookup`, on both `Mach` and `MachTB`. -/
theorem ep1_meta_unops_unsized_dst_and_errors_witness :
    let dstStructTy : Gen.Type :=
      .Tuple [(⟨0⟩, .Int ep1U8)] ⟨⟨1⟩, ⟨1⟩, none⟩ (some (.Slice (.Int ep1U32)))
    let packedDstTy : Gen.Type :=
      .Tuple [(⟨0⟩, .Int ep1U8)] ⟨⟨1⟩, ⟨1⟩, some ⟨2⟩⟩ (some (.Slice (.Int ep1U32)))
    let thinBM : Ptr := ⟨0x1000, none⟩
    let thinTB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x1000, none⟩
    let tr : Gen.TraitName := ⟨⟨0⟩⟩
    let meth : Gen.TraitMethodName := ⟨⟨0⟩⟩
    -- 1. Unsized & packed DST structs + slice + sized on Mach (m = none)
    (evalUnOp .GetMetadata (.Ptr (ThinPointer.widen thinBM none), .Ptr (.Raw .None)) none =
      .ok (.Tuple [], unitType) ∧
     evalUnOp .GetMetadata (.Ptr (ThinPointer.widen thinBM (some (.ElementCount 5))),
        .Ptr (.Raw .ElementCount)) none =
      .ok (.Int 5, .Int IntType.usize_ty) ∧
     evalUnOp (.ComputeSize (.Int ep1U32)) (.Tuple [], unitType) none =
      .ok (.Int 4, .Int IntType.usize_ty) ∧
     evalUnOp (.ComputeAlign (.Int ep1U32)) (.Tuple [], unitType) none =
      .ok (.Int 4, .Int IntType.usize_ty) ∧
     evalUnOp (.ComputeSize (.Slice (.Int ep1U32))) (.Int 5, .Int IntType.usize_ty) none =
      .ok (.Int 20, .Int IntType.usize_ty) ∧
     evalUnOp (.ComputeAlign (.Slice (.Int ep1U32))) (.Int 5, .Int IntType.usize_ty) none =
      .ok (.Int 4, .Int IntType.usize_ty) ∧
     evalUnOp (.ComputeSize dstStructTy) (.Int 3, .Int IntType.usize_ty) none =
      .ok (.Int 16, .Int IntType.usize_ty) ∧
     evalUnOp (.ComputeAlign dstStructTy) (.Int 3, .Int IntType.usize_ty) none =
      .ok (.Int 4, .Int IntType.usize_ty) ∧
     evalUnOp (.ComputeSize packedDstTy) (.Int 3, .Int IntType.usize_ty) none =
      .ok (.Int 14, .Int IntType.usize_ty) ∧
     evalUnOp (.ComputeAlign packedDstTy) (.Int 3, .Int IntType.usize_ty) none =
      .ok (.Int 2, .Int IntType.usize_ty)) ∧
    -- 2. Same on MachTB (`evalUnOpM (M := TBM)`)
    (evalUnOpM (M := TBM) .GetMetadata (.Ptr (ThinPointer.widen thinTB none), .Ptr (.Raw .None)) none =
      .ok (.Tuple [], unitType) ∧
     evalUnOpM (M := TBM) .GetMetadata (.Ptr (ThinPointer.widen thinTB (some (.ElementCount 5))),
        .Ptr (.Raw .ElementCount)) none =
      .ok (.Int 5, .Int IntType.usize_ty) ∧
     evalUnOpM (M := TBM) (.ComputeSize dstStructTy) (.Int 3, .Int IntType.usize_ty) none =
      .ok (.Int 16, .Int IntType.usize_ty) ∧
     evalUnOpM (M := TBM) (.ComputeAlign dstStructTy) (.Int 3, .Int IntType.usize_ty) none =
      .ok (.Int 4, .Int IntType.usize_ty) ∧
     evalUnOpM (M := TBM) (.ComputeSize packedDstTy) (.Int 3, .Int IntType.usize_ty) none =
      .ok (.Int 14, .Int IntType.usize_ty) ∧
     evalUnOpM (M := TBM) (.ComputeAlign packedDstTy) (.Int 3, .Int IntType.usize_ty) none =
      .ok (.Int 2, .Int IntType.usize_ty)) ∧
    -- 3. Negative specPanic and fail-closed vtable unsupported controls
    (evalUnOp .GetMetadata (.Int 7, .Int ep1U32) none = specPanic "non-pointer GetMetadata" ∧
     evalUnOp .GetMetadata (.Ptr (ThinPointer.widen thinBM (some (.ElementCount (-1)))),
        .Ptr (.Raw .ElementCount)) none =
       specPanic "GetMetadata: sanity check, returned meta is well-formed" ∧
     evalUnOp (.ComputeSize (.Slice (.Int ep1U32))) (.Int (-1), .Int IntType.usize_ty) none =
       specPanic "Size::from_bytes(count * elem_size.bytes()).unwrap()" ∧
     evalUnOp (.ComputeSize (.Int ep1U32)) (.Int 0, .Int ep1U32) none =
       specPanic "PointerMeta::decode_value called with invalid value" ∧
     evalUnOp .GetMetadata (.Ptr (ThinPointer.widen thinBM (some (.VTablePointer thinBM))),
        .Ptr (.Raw (.VTablePointer tr))) none =
       unsupported "eval_un_op UnOp::GetMetadata for vtable pointer metadata" ∧
     evalUnOp (.ComputeSize (.TraitObject tr)) (.Ptr (ThinPointer.widen thinBM none),
        .Ptr (.VTablePtr tr)) none =
       unsupported "eval_un_op UnOp::ComputeSize for vtable pointer metadata" ∧
     evalUnOp (.ComputeAlign (.TraitObject tr)) (.Ptr (ThinPointer.widen thinBM none),
        .Ptr (.VTablePtr tr)) none =
       unsupported "eval_un_op UnOp::ComputeAlign for vtable pointer metadata" ∧
     evalUnOp (.VTableMethodLookup meth) (.Ptr (ThinPointer.widen thinBM none),
        .Ptr (.VTablePtr tr)) none =
       unsupported "eval_un_op for UnOp::VTableMethodLookup" ∧
     evalUnOpM (M := TBM) .GetMetadata (.Ptr (ThinPointer.widen thinTB (some (.VTablePointer thinTB))),
        .Ptr (.Raw (.VTablePointer tr))) none =
       unsupported "eval_un_op UnOp::GetMetadata for vtable pointer metadata" ∧
     evalUnOpM (M := TBM) (.VTableMethodLookup meth) (.Ptr (ThinPointer.widen thinTB none),
        .Ptr (.VTablePtr tr)) none =
       unsupported "eval_un_op for UnOp::VTableMethodLookup") :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-! ### `[adv B1]` Universal laws: `decode_discriminant` fidelity, complete `GetDiscriminant` /
`Union` characterizations, non-enum panics, error propagation, and no fabricated UB -/

/-- Upstream's choice of the next discriminator in `decode_discriminant`
(`spec/lang/representation.md`), stated exactly as upstream writes it
(`children.iter().find_map(|((start, end), child)| if start <= val && val < end { Some(child) }
else { None }).unwrap_or(fallback)`) rather than in the continuation-passing form that
`decodeDiscriminantChildren[M]` uses to stay structurally recursive. -/
def ep1NextDiscriminator (children : List ((Int × Int) × Gen.Discriminator))
    (fallback : Gen.Discriminator) (val : Int) : Gen.Discriminator :=
  ((children.find? (fun c => decide (c.1.1 ≤ val ∧ val < c.1.2))).map Prod.snd).getD fallback

/-- **Transcription fidelity of `decode_discriminant`'s `Branch` arm**: the
continuation-passing child scan `decodeDiscriminantChildrenM` (with the fallback
continuation that `decodeDiscriminantM` supplies) is exactly upstream's `find_map` /
`unwrap_or(fallback)` followed by the recursive `decode_discriminant` call, for every
accessor and every threaded state. -/
theorem ep1_decodeDiscriminantChildrenM_eq_find_map {M : Type} [Gen.Memory M] {σ : Type}
    (accessor : σ → Gen.Offset → Size →
      Interp (List (Gen.AbstractByte (Gen.Memory.Provenance M)) × σ))
    (val : Int) (fallback : Gen.Discriminator) :
    ∀ (children : List ((Int × Int) × Gen.Discriminator)) (s : σ),
      decodeDiscriminantChildrenM (M := M) accessor val
          (decodeDiscriminantM (M := M) accessor fallback) children s =
        decodeDiscriminantM (M := M) accessor (ep1NextDiscriminator children fallback val) s
  | [], s => by
    unfold decodeDiscriminantChildrenM
    rfl
  | ((start, end_), child) :: rest, s => by
    unfold decodeDiscriminantChildrenM
    by_cases h : start ≤ val ∧ val < end_
    · simp [h, ep1NextDiscriminator, List.find?]
    · have ih := ep1_decodeDiscriminantChildrenM_eq_find_map accessor val fallback rest s
      simp only [h, ↓reduceIte, ih]
      simp [ep1NextDiscriminator, List.find?, h]

/-- Same fidelity law for the `BasicMemory` transcription `decodeDiscriminantChildren`. -/
theorem ep1_decodeDiscriminantChildren_eq_find_map {σ : Type}
    (accessor : σ → Gen.Offset → Size → Interp (List Byte × σ))
    (val : Int) (fallback : Gen.Discriminator) :
    ∀ (children : List ((Int × Int) × Gen.Discriminator)) (s : σ),
      decodeDiscriminantChildren accessor val (decodeDiscriminant accessor fallback) children s =
        decodeDiscriminant accessor (ep1NextDiscriminator children fallback val) s
  | [], s => by
    unfold decodeDiscriminantChildren
    rfl
  | ((start, end_), child) :: rest, s => by
    unfold decodeDiscriminantChildren
    by_cases h : start ≤ val ∧ val < end_
    · simp [h, ep1NextDiscriminator, List.find?]
    · have ih := ep1_decodeDiscriminantChildren_eq_find_map accessor val fallback rest s
      simp only [h, ↓reduceIte, ih]
      simp [ep1NextDiscriminator, List.find?, h]

/-- The body of `ValueExpr::GetDiscriminant` after the enum-type and alignment checks
(`spec/lang/step/expressions.md`): `decode_discriminant` with the machine-threading accessor
(`ptr_offset_inbounds` + `self.mem.load(ptr, size, Align::ONE, Atomicity::None)`) at place
`rp`, then `throw_ub!` on `None`. -/
def ep1GetDiscriminantCore {M : Type} [Gen.Memory M] [MemoryOps M]
    (rp : Gen.Place M) (dty : Gen.IntType) (d : Gen.Discriminator) (m : Gen.Machine M) :
    Interp ((Gen.Value M × Gen.Type) × Gen.Machine M) := do
  let accessor := fun (m : Gen.Machine M) (idx : Gen.Offset) (size : Size) => do
    let ptr ← ptrOffsetInboundsM m rp.ptr.thin_pointer (idx.bytes : Int)
    let (bytes, cm) ← ConcurrentMemory.load m.mem ptr size ⟨1⟩ .None
    pure (bytes, { m with mem := cm })
  let (discrOpt, m) ← decodeDiscriminantM (M := M) accessor d m
  match discrOpt with
  | some discriminant => pure ((.Int discriminant, .Int dty), m)
  | none => ub "ValueExpr::GetDiscriminant encountered invalid discriminant."

/-- **Complete universal characterization of `ValueExpr::GetDiscriminant`** on every
`Memory` `M`, every enum type, and every `Discriminator` tree (not only the memory-free
`Known` / `Invalid` leaves):

1. on an aligned enum place, `GetDiscriminant` is exactly `ep1GetDiscriminantCore` at the
   machine returned by `eval_place`;
2. a `Known` leaf returns its discriminant and an `Invalid` leaf is UB, neither touching
   memory nor the machine;
3. a `Branch` node performs **exactly one** `ptr_offset_inbounds` + `mem.load` of
   `value_type.size` bytes at `offset` (with `Align::ONE`, `Atomicity::None`) on the
   *current* machine, propagates either failure unchanged (so a dangling / out-of-bounds /
   Tree-Borrows-forbidden tag read is whatever the memory model raises, i.e. UB), raises
   UB when the tag bytes do not decode at `Type::Int(value_type)` (uninitialized tag), and
   otherwise continues at upstream's `find_map` / `unwrap_or(fallback)` child on the
   machine **updated by that load** (state threading). -/
theorem ep1_evalValueM_getDiscriminant_complete_spec {M : Type} [Gen.Memory M] [MemoryOps M] :
    (∀ (m m1 : Gen.Machine M) (place : Gen.PlaceExpr) (rp : Gen.Place M)
        variants dty discr sz al,
      evalPlaceM m place = .ok ((rp, .Enum variants dty discr sz al), m1) →
      rp.aligned = true →
      evalValueM m (.GetDiscriminant place) = ep1GetDiscriminantCore rp dty discr m1) ∧
    (∀ (rp : Gen.Place M) dty d (m : Gen.Machine M),
      ep1GetDiscriminantCore rp dty (.Known d) m = .ok ((.Int d, .Int dty), m)) ∧
    (∀ (rp : Gen.Place M) dty (m : Gen.Machine M),
      ep1GetDiscriminantCore rp dty .Invalid m =
        ub "ValueExpr::GetDiscriminant encountered invalid discriminant.") ∧
    (∀ (rp : Gen.Place M) dty off vt fallback children (m : Gen.Machine M),
      ep1GetDiscriminantCore rp dty (.Branch off vt fallback ⟨children⟩) m = (do
        let ptr ← ptrOffsetInboundsM m rp.ptr.thin_pointer (off.bytes : Int)
        let (bytes, cm) ← ConcurrentMemory.load m.mem ptr vt.size ⟨1⟩ .None
        match ← Type.decodeIntM (M := M) vt bytes with
        | some (.Int tag) =>
          ep1GetDiscriminantCore rp dty (ep1NextDiscriminator children fallback tag)
            { m with mem := cm }
        | _ => ub "ValueExpr::GetDiscriminant encountered invalid discriminant.")) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m m1 place rp variants dty discr sz al hp hal
    simp only [evalValueM, hp, hal, ep1GetDiscriminantCore, bind, Except.bind,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  · intro rp dty d m
    simp [ep1GetDiscriminantCore, decodeDiscriminantM, bind, Except.bind, pure, Except.pure]
  · intro rp dty m
    simp [ep1GetDiscriminantCore, decodeDiscriminantM, ub, bind, Except.bind, pure, Except.pure]
  · intro rp dty off vt fallback children m
    simp only [ep1GetDiscriminantCore, decodeDiscriminantM, bind, Except.bind]
    cases hptr : ptrOffsetInboundsM m rp.ptr.thin_pointer (off.bytes : Int) with
    | error e => rfl
    | ok ptr =>
      dsimp only
      cases hld : ConcurrentMemory.load m.mem ptr vt.size ⟨1⟩ .None with
      | error e => rfl
      | ok bc =>
        obtain ⟨bytes, cm⟩ := bc
        dsimp only [pure, Except.pure]
        cases hdec : Type.decodeIntM (M := M) vt bytes with
        | error e => rfl
        | ok optv =>
          dsimp only
          cases optv with
          | none => rfl
          | some v =>
            cases v with
            | Int tag =>
              dsimp only
              rw [ep1_decodeDiscriminantChildrenM_eq_find_map]
            | _ => rfl

/-- **Complete universal characterization of `ValueExpr::Union`** on every `Memory` `M`:
at a union type, `eval_value` is exactly upstream's sequence — `fields[field]`, the
evaluation of `expr`, `expr_ty.encode(val)`, `write_subslice_at_index` into
`size.bytes()` `Uninit` bytes — followed by the per-chunk `subslice_with_length` of
`Type::decode` at `Union`. In particular neither `Type::decode`'s length check
(`"decode of Type::Union with invalid length"`) nor upstream's `.unwrap()` can ever
fire: `write_subslice_at_index` preserves the length `size.bytes()`, and `decode` at a
union type never returns `None`. -/
theorem ep1_evalValueM_union_complete_spec {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Gen.Machine M) (field : Int) (expr : Gen.ValueExpr)
    (fields : List (Gen.Offset × Gen.Type)) (chunks : List (Gen.Offset × Size))
    (sz : Size) (al : Align) :
    evalValueM m (.Union field expr (.Union fields chunks sz al)) = (do
      let (offset, exprTy) ← listIndex fields field "fields[field]"
      let ((val, _), m) ← evalValueM m expr
      let encoded ← Type.encodeM exprTy val
      let data ← writeSubsliceAtIndex
        (List.replicate sz.bytes (.Uninit : Gen.AbstractByte (Gen.Memory.Provenance M)))
        (offset.bytes : Int) encoded
      let chunkData ← chunks.mapM (fun (offset, chunkSize) =>
        subsliceWithLength data offset.bytes chunkSize.bytes)
      pure ((.Union chunkData, .Union fields chunks sz al), m)) := by
  simp only [evalValueM, bind, Except.bind, pure, Except.pure]
  cases hidx : listIndex fields field "fields[field]" with
  | error e => rfl
  | ok ofty =>
    obtain ⟨offset, exprTy⟩ := ofty
    dsimp only
    cases hev : evalValueM m expr with
    | error e => rfl
    | ok vm =>
      obtain ⟨⟨val, vty⟩, m1⟩ := vm
      dsimp only
      cases henc : Type.encodeM exprTy val with
      | error e => rfl
      | ok encoded =>
        dsimp only
        cases hws : writeSubsliceAtIndex
            (List.replicate sz.bytes (.Uninit : Gen.AbstractByte (Gen.Memory.Provenance M)))
            (offset.bytes : Int) encoded with
        | error e => rfl
        | ok data =>
          dsimp only
          have hlen : data.length = sz.bytes := by
            rw [writeSubsliceAtIndex_length hws, List.length_replicate]
          unfold Type.decodeM
          simp only [hlen, ne_eq, not_true_eq_false, ↓reduceIte, bind, Except.bind, pure,
            Except.pure]
          cases hch : chunks.mapM (fun (x : Gen.Offset × Size) =>
              subsliceWithLength data (x.1.bytes : Int) (x.2.bytes : Int)) with
          | error e => rfl
          | ok chunkData => rfl

/-- **Type-mismatch spec panics and error propagation**, universally over every `Memory`
`M` and every non-matching type (not only `Type::Int`):

* `PlaceExpr::Downcast` and `ValueExpr::GetDiscriminant` on any non-enum place and
  `ValueExpr::Union` at any non-union type are upstream's `panic!`s. The
  `GetDiscriminant` panic precedes the misalignment check (it holds whatever
  `rp.aligned` is), and the `Union` panic precedes the evaluation of `expr`.
* A failing sub-evaluation (`eval_place(root)`, `eval_place(place)`, `eval_value(data)`,
  `eval_value(expr)`) propagates unchanged, so UB of an operand is never masked. -/
theorem ep1_evalM_type_mismatch_panics_and_error_propagation
    {M : Type} [Gen.Memory M] [MemoryOps M] (m m1 : Gen.Machine M) :
    (∀ root rp ty d, evalPlaceM m root = .ok ((rp, ty), m1) →
      (∀ v dt dc s a, ty ≠ .Enum v dt dc s a) →
      evalPlaceM m (.Downcast root d) = specPanic "enum downcast on non-enum") ∧
    (∀ place rp ty, evalPlaceM m place = .ok ((rp, ty), m1) →
      (∀ v dt dc s a, ty ≠ .Enum v dt dc s a) →
      evalValueM m (.GetDiscriminant place) =
        specPanic "ValueExpr::GetDiscriminant requires enum type") ∧
    (∀ field expr ty, (∀ f c s a, ty ≠ .Union f c s a) →
      evalValueM m (.Union field expr ty) = specPanic "ValueExpr::Union requires union type") ∧
    (∀ root d e, evalPlaceM m root = .error e → evalPlaceM m (.Downcast root d) = .error e) ∧
    (∀ place e, evalPlaceM m place = .error e →
      evalValueM m (.GetDiscriminant place) = .error e) ∧
    (∀ d data enumTy e, evalValueM m data = .error e →
      evalValueM m (.Variant d data enumTy) = .error e) ∧
    (∀ field expr fields chunks sz al off ety e,
      listIndex fields field "fields[field]" = .ok (off, ety) →
      evalValueM m expr = .error e →
      evalValueM m (.Union field expr (.Union fields chunks sz al)) = .error e) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro root rp ty d hroot hne
    cases ty with
    | Enum v dt dc s a => exact absurd rfl (hne v dt dc s a)
    | _ => simp [evalPlaceM, hroot, specPanic, bind, Except.bind]
  · intro place rp ty hp hne
    cases ty with
    | Enum v dt dc s a => exact absurd rfl (hne v dt dc s a)
    | _ => simp [evalValueM, hp, specPanic, bind, Except.bind]
  · intro field expr ty hne
    cases ty with
    | Union f c s a => exact absurd rfl (hne f c s a)
    | _ => simp [evalValueM, specPanic, bind, Except.bind]
  · intro root d e hroot
    simp [evalPlaceM, hroot, bind, Except.bind]
  · intro place e hp
    simp [evalValueM, hp, bind, Except.bind]
  · intro d data enumTy e hd
    simp [evalValueM, hd, bind, Except.bind]
  · intro field expr fields chunks sz al off ety e hidx hev
    simp [evalValueM, hidx, hev, bind, Except.bind, pure, Except.pure]

/-- **Complete universal characterization of `UnOp::GetMetadata`** over every pointer
type (`Raw`, `Ref`, `Box`, `FnPtr`, `VTablePtr`, through `PtrType::meta_kind`) and every
metadata, on every `Memory` `M` and with or without a machine:

* thin kind + no metadata returns `unit_value()` at `unit_type()`;
* `ElementCount` kind + element count `c` returns `Value::Int(c)` at `usize` exactly when
  `c` fits in a `usize`, and otherwise is upstream's failed O(1) sanity check
  (`check_value(..).expect(..)`, a spec panic — never UB);
* `VTablePointer` kind + vtable metadata is fail-closed `unsupported` without a machine
  (`m = none`); with a machine it returns the vtable pointer at
  `Type::Ptr(PtrType::VTablePtr(trait_name))` exactly when that pointer passes
  `check_ptr` (`Machine::vtable_from_ptr` and the trait check), turns UB from
  `check_ptr` into upstream's `.expect(..)` spec panic, and propagates any
  internal spec panic (such as a missing `prog.vtables` entry) directly;
* every kind/metadata mismatch (all five) is upstream's `encode_as_value` panic, which
  therefore takes precedence over the machine-free vtable fail-closed stop. -/
theorem ep1_evalUnOpM_getMetadata_complete_spec {M : Type} [Gen.Memory M] [MemoryOps M]
    (thin : Gen.ThinPointer (Gen.Memory.Provenance M)) (ptrTy : Gen.PtrType)
    (m : Option (Gen.Machine M)) :
    (PtrType.meta_kind ptrTy = .None →
      evalUnOpM .GetMetadata (.Ptr ⟨thin, none⟩, .Ptr ptrTy) m = .ok (.Tuple [], unitType)) ∧
    (∀ c, PtrType.meta_kind ptrTy = .ElementCount →
      evalUnOpM .GetMetadata (.Ptr ⟨thin, some (.ElementCount c)⟩, .Ptr ptrTy) m =
        match IntType.can_represent IntType.usize_ty c with
        | true => .ok (.Int c, .Int IntType.usize_ty)
        | false => specPanic "GetMetadata: sanity check, returned meta is well-formed") ∧
    (∀ t p, PtrType.meta_kind ptrTy = .VTablePointer t →
      evalUnOpM (M := M) .GetMetadata (.Ptr ⟨thin, some (.VTablePointer p)⟩, .Ptr ptrTy) none =
        unsupported "eval_un_op UnOp::GetMetadata for vtable pointer metadata") ∧
    (∀ pm, PtrType.meta_kind ptrTy = .None →
      evalUnOpM .GetMetadata (.Ptr ⟨thin, some pm⟩, .Ptr ptrTy) m =
        specPanic "PointerMeta::encode_as_value called with invalid value") ∧
    (PtrType.meta_kind ptrTy = .ElementCount →
      evalUnOpM .GetMetadata (.Ptr ⟨thin, none⟩, .Ptr ptrTy) m =
        specPanic "PointerMeta::encode_as_value called with invalid value") ∧
    (∀ p, PtrType.meta_kind ptrTy = .ElementCount →
      evalUnOpM .GetMetadata (.Ptr ⟨thin, some (.VTablePointer p)⟩, .Ptr ptrTy) m =
        specPanic "PointerMeta::encode_as_value called with invalid value") ∧
    (∀ t, PtrType.meta_kind ptrTy = .VTablePointer t →
      evalUnOpM .GetMetadata (.Ptr ⟨thin, none⟩, .Ptr ptrTy) m =
        specPanic "PointerMeta::encode_as_value called with invalid value") ∧
    (∀ t c, PtrType.meta_kind ptrTy = .VTablePointer t →
      evalUnOpM .GetMetadata (.Ptr ⟨thin, some (.ElementCount c)⟩, .Ptr ptrTy) m =
        specPanic "PointerMeta::encode_as_value called with invalid value") ∧
    (∀ t p mach, PtrType.meta_kind ptrTy = .VTablePointer t →
      evalUnOpM .GetMetadata (.Ptr ⟨thin, some (.VTablePointer p)⟩, .Ptr ptrTy) (some mach) =
        match checkPtrM (M := M) ⟨p, none⟩ (.VTablePtr t) (some mach) with
        | .ok () => .ok (.Ptr ⟨p, none⟩, .Ptr (.VTablePtr t))
        | .error (.ub _) => specPanic "GetMetadata: sanity check, returned meta is well-formed"
        | .error e => .error e) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hk
    have hCheck : checkValueM (M := M) (.Tuple []) unitType m = .ok () := by
      rw [unitType, checkValueM]; rfl
    rw [evalUnOpM]
    simp only [hk, PointerMetaKind.encode_as_valueM, PointerMetaKind.ty, bind, Except.bind,
      pure, Except.pure]
    rw [hCheck]
  · intro c hk
    rw [evalUnOpM]
    simp only [hk, PointerMetaKind.encode_as_valueM, PointerMetaKind.ty, bind, Except.bind,
      pure, Except.pure]
    cases hc : IntType.can_represent IntType.usize_ty c with
    | true =>
      have hCheck : checkValueM (M := M) (.Int c) (.Int IntType.usize_ty) m = .ok () := by
        rw [checkValueM, ensureElseUb, hc]; rfl
      rw [hCheck]
    | false =>
      have hCheck : checkValueM (M := M) (.Int c) (.Int IntType.usize_ty) m =
          .error (.ub "Value::Int: invalid integer value") := by
        rw [checkValueM, ensureElseUb, hc]; rfl
      rw [hCheck]
  · intro t p hk
    simp [evalUnOpM, hk, PointerMetaKind.encode_as_valueM, bind, Except.bind, pure, Except.pure]
  · intro pm hk
    simp [evalUnOpM, hk, PointerMetaKind.encode_as_valueM, specPanic, bind, Except.bind]
  · intro hk
    simp [evalUnOpM, hk, PointerMetaKind.encode_as_valueM, specPanic, bind, Except.bind]
  · intro p hk
    simp [evalUnOpM, hk, PointerMetaKind.encode_as_valueM, specPanic, bind, Except.bind]
  · intro t hk
    simp [evalUnOpM, hk, PointerMetaKind.encode_as_valueM, specPanic, bind, Except.bind]
  · intro t c hk
    simp [evalUnOpM, hk, PointerMetaKind.encode_as_valueM, specPanic, bind, Except.bind]
  · intro t p mach hk
    have hcv : checkValueM (M := M) (.Ptr ⟨p, none⟩) (.Ptr (.VTablePtr t)) (some mach) =
        checkPtrM (M := M) ⟨p, none⟩ (.VTablePtr t) (some mach) := by
      rw [checkValueM]
    rw [evalUnOpM]
    simp only [hk, PointerMetaKind.encode_as_valueM, PointerMetaKind.ty, bind, Except.bind,
      pure, Except.pure]
    rw [hcv]
    cases checkPtrM (M := M) ⟨p, none⟩ (.VTablePtr t) (some mach) with
    | ok u => cases u; rfl
    | error e => cases e <;> rfl

private theorem ep1_bind_error {α β : Type} {x : Interp α} {f : α → Interp β} {e : Stop}
    (h : (x >>= f) = .error e) : x = .error e ∨ ∃ a, x = .ok a ∧ f a = .error e := by
  cases hx : x with
  | error e' =>
    simp only [hx, bind, Except.bind] at h
    cases h
    exact Or.inl rfl
  | ok a =>
    simp only [hx, bind, Except.bind] at h
    exact Or.inr ⟨a, rfl, h⟩

private theorem ep1_map_error {α β : Type} {x : Interp α} {f : α → β} {e : Stop}
    (h : (f <$> x) = .error e) : x = .error e := by
  cases hx : x with
  | error e' => simpa [hx, Functor.map, Except.map] using h
  | ok a => simp [hx, Functor.map, Except.map] at h

private theorem ep1_expect_size_error_is_specPanic {l : Gen.LayoutStrategy} {msg : String}
    {e : Stop} (h : LayoutStrategy.expect_size l msg = .error e) : ∃ m, e = .specPanic m := by
  cases l <;> simp [LayoutStrategy.expect_size, specPanic, pure, Except.pure] at h
  all_goals exact ⟨_, h.symm⟩

private theorem ep1_expect_align_error_is_specPanic {l : Gen.LayoutStrategy} {msg : String}
    {e : Stop} (h : LayoutStrategy.expect_align l msg = .error e) : ∃ m, e = .specPanic m := by
  cases l <;> simp [LayoutStrategy.expect_align, specPanic, pure, Except.pure] at h
  all_goals exact ⟨_, h.symm⟩

private theorem ep1_Size_mulInt_error_is_specPanic {s : Size} {n : Int} {e : Stop}
    (h : Size.mulInt s n = .error e) : ∃ m, e = .specPanic m := by
  unfold Size.mulInt at h
  split at h
  · simp [pure, Except.pure] at h
  · simp [specPanic] at h; exact ⟨_, h.symm⟩

/-- `Type::layout` fails only by a spec panic (`expect_size` / `expect_align` on an unsized
element, a negative `Size * Int`, or a non-power-of-two integer size): it has no
`throw_ub!`. -/
theorem ep1_Type_layout_error_is_specPanic :
    ∀ (ty : Gen.Type) (e : Stop), Type.layout ty = .error e → ∃ msg, e = .specPanic msg
  | .Int t, e, h => by
    unfold Type.layout at h
    rcases ep1_bind_error h with ha | ⟨a, _, hp⟩
    · unfold IntType.align at ha
      split at ha
      · simp [pure, Except.pure] at ha
      · simp [specPanic] at ha; exact ⟨_, ha.symm⟩
    · simp [pure, Except.pure] at hp
  | .Bool, e, h => by simp [Type.layout, pure, Except.pure] at h
  | .Ptr p, e, h => by
    unfold Type.layout at h
    split at h <;> simp [pure, Except.pure] at h
  | .Union _ _ _ _, e, h => by simp [Type.layout, pure, Except.pure] at h
  | .Enum _ _ _ _ _, e, h => by simp [Type.layout, pure, Except.pure] at h
  | .Tuple _ _ none, e, h => by simp [Type.layout, pure, Except.pure] at h
  | .Tuple _ head (some tail), e, h => by
    unfold Type.layout at h
    rcases ep1_bind_error h with ht | ⟨a, _, hp⟩
    · exact ep1_Type_layout_error_is_specPanic tail e ht
    · simp [pure, Except.pure] at hp
  | .Array elem count, e, h => by
    unfold Type.layout at h
    rcases ep1_bind_error h with hl | ⟨el, _, h⟩
    · exact ep1_Type_layout_error_is_specPanic elem e hl
    · rcases ep1_bind_error h with hs | ⟨es, _, h⟩
      · exact ep1_expect_size_error_is_specPanic hs
      · rcases ep1_bind_error h with ha | ⟨ea, _, h⟩
        · exact ep1_expect_align_error_is_specPanic ha
        · rcases ep1_bind_error h with hm | ⟨sz, _, hp⟩
          · exact ep1_Size_mulInt_error_is_specPanic hm
          · simp [pure, Except.pure] at hp
  | .Slice elem, e, h => by
    unfold Type.layout at h
    rcases ep1_bind_error h with hl | ⟨el, _, h⟩
    · exact ep1_Type_layout_error_is_specPanic elem e hl
    · rcases ep1_bind_error h with hs | ⟨es, _, h⟩
      · exact ep1_expect_size_error_is_specPanic hs
      · rcases ep1_bind_error h with hl2 | ⟨el2, _, h⟩
        · exact ep1_Type_layout_error_is_specPanic elem e hl2
        · rcases ep1_bind_error h with ha | ⟨ea, _, hp⟩
          · exact ep1_expect_align_error_is_specPanic ha
          · simp [pure, Except.pure] at hp
  | .TraitObject _, e, h => by simp [Type.layout, pure, Except.pure] at h

private theorem ep1_compute_size_and_align_nonVTable_error_is_specPanic {P : Type}
    (vt : Gen.ThinPointer P → Interp Gen.VTable) :
    ∀ (lay : Gen.LayoutStrategy) (pm : Option (Gen.PointerMeta P)) (e : Stop),
      (∀ p, pm ≠ some (.VTablePointer p)) →
      LayoutStrategy.compute_size_and_align vt lay pm = .error e → ∃ msg, e = .specPanic msg
  | .Sized _ _, none, e, _, h => by
    simp [LayoutStrategy.compute_size_and_align, pure, Except.pure] at h
  | .Sized _ _, some _, e, _, h => by
    simp [LayoutStrategy.compute_size_and_align, specPanic] at h; exact ⟨_, h.symm⟩
  | .Slice _ _, none, e, _, h => by
    simp [LayoutStrategy.compute_size_and_align, specPanic] at h; exact ⟨_, h.symm⟩
  | .Slice elemSize _, some (.ElementCount count), e, _, h => by
    unfold LayoutStrategy.compute_size_and_align at h
    dsimp only at h
    split at h
    · simp [pure, Except.pure] at h
    · simp [specPanic] at h; exact ⟨_, h.symm⟩
  | .Slice _ _, some (.VTablePointer p), e, hn, _ => absurd rfl (hn p)
  | .TraitObject _, none, e, _, h => by
    simp [LayoutStrategy.compute_size_and_align, specPanic] at h; exact ⟨_, h.symm⟩
  | .TraitObject _, some (.ElementCount _), e, _, h => by
    simp [LayoutStrategy.compute_size_and_align, specPanic] at h; exact ⟨_, h.symm⟩
  | .TraitObject _, some (.VTablePointer p), e, hn, _ => absurd rfl (hn p)
  | .Tuple _ _, none, e, _, h => by
    simp [LayoutStrategy.compute_size_and_align, specPanic] at h; exact ⟨_, h.symm⟩
  | .Tuple head tail, some pm, e, hn, h => by
    unfold LayoutStrategy.compute_size_and_align at h
    rcases ep1_bind_error h with ht | ⟨r, _, hp⟩
    · exact ep1_compute_size_and_align_nonVTable_error_is_specPanic vt tail (some pm) e hn ht
    · simp [pure, Except.pure] at hp

private theorem ep1_meta_layout_tail_error_is_specPanic {M : Type} [Gen.Memory M] {α : Type}
    (proj : Size × Align → α) (k : α → Gen.Value M × Gen.Type) (what : String) (ty : Gen.Type)
    (pm : Option (Gen.PointerMeta (Gen.Memory.Provenance M)))
    (hn : ∀ p, pm ≠ some (.VTablePointer p)) (e : Stop)
    (h : (do
      let layout ← Type.layout ty
      let x ← proj <$> LayoutStrategy.compute_size_and_align
        (fun _ => (unsupported what : Interp Gen.VTable)) layout pm
      (pure (k x) : Interp (Gen.Value M × Gen.Type))) = .error e) :
    ∃ msg, e = .specPanic msg := by
  rcases ep1_bind_error h with hl | ⟨lay, _, h⟩
  · exact ep1_Type_layout_error_is_specPanic ty e hl
  · rcases ep1_bind_error h with hc | ⟨x, _, hp⟩
    · exact ep1_compute_size_and_align_nonVTable_error_is_specPanic _ lay pm e hn
        (ep1_map_error hc)
    · simp [pure, Except.pure] at hp

private theorem ep1_mapIndex_error_is_specPanic {K V : Type} [DecidableEq K]
    {mp : Map K V} {k : K} {what : String} {e : Stop}
    (h : mapIndex mp k what = .error e) : ∃ msg, e = .specPanic msg := by
  unfold mapIndex at h
  split at h
  · simp [pure, Except.pure] at h
  · simp [specPanic] at h; exact ⟨_, h.symm⟩

/-- `Machine::vtable_lookup` fails only by a spec panic (its `unwrap()` and its map
index): it has no `throw_ub!`. -/
private theorem ep1_vtableLookupM_error_is_specPanic {M : Type} [Gen.Memory M] [MemoryOps M]
    (mach : Gen.Machine M) (p : Gen.ThinPointer (Gen.Memory.Provenance M)) (e : Stop)
    (h : vtableLookupM mach p = .error e) : ∃ msg, e = .specPanic msg := by
  unfold vtableLookupM at h
  split at h
  · exact ep1_mapIndex_error_is_specPanic h
  · simp [specPanic] at h; exact ⟨_, h.symm⟩

/-- `LayoutStrategy::compute_size_and_align` fails only by a spec panic or by a failure
of its vtable lookup `vt`: every failure satisfies `Q` as soon as spec panics and the
failures of `vt` do. -/
private theorem ep1_compute_size_and_align_error_of_lookup {P : Type}
    (vt : Gen.ThinPointer P → Interp Gen.VTable) (Q : Stop → Prop)
    (hSpec : ∀ msg, Q (.specPanic msg)) (hvt : ∀ p e, vt p = .error e → Q e) :
    ∀ (lay : Gen.LayoutStrategy) (pm : Option (Gen.PointerMeta P)) (e : Stop),
      LayoutStrategy.compute_size_and_align vt lay pm = .error e → Q e
  | .Sized _ _, none, e, h => by
    simp [LayoutStrategy.compute_size_and_align, pure, Except.pure] at h
  | .Sized _ _, some _, e, h => by
    simp [LayoutStrategy.compute_size_and_align, specPanic] at h; subst h; exact hSpec _
  | .Slice _ _, none, e, h => by
    simp [LayoutStrategy.compute_size_and_align, specPanic] at h; subst h; exact hSpec _
  | .Slice elemSize _, some (.ElementCount count), e, h => by
    unfold LayoutStrategy.compute_size_and_align at h
    dsimp only at h
    split at h
    · simp [pure, Except.pure] at h
    · simp [specPanic] at h; subst h; exact hSpec _
  | .Slice _ _, some (.VTablePointer _), e, h => by
    simp [LayoutStrategy.compute_size_and_align, specPanic] at h; subst h; exact hSpec _
  | .TraitObject _, none, e, h => by
    simp [LayoutStrategy.compute_size_and_align, specPanic] at h; subst h; exact hSpec _
  | .TraitObject _, some (.ElementCount _), e, h => by
    simp [LayoutStrategy.compute_size_and_align, specPanic] at h; subst h; exact hSpec _
  | .TraitObject _, some (.VTablePointer p), e, h => by
    unfold LayoutStrategy.compute_size_and_align at h
    rcases ep1_bind_error h with hv | ⟨_, _, hp⟩
    · exact hvt p e hv
    · simp [pure, Except.pure] at hp
  | .Tuple _ _, none, e, h => by
    simp [LayoutStrategy.compute_size_and_align, specPanic] at h; subst h; exact hSpec _
  | .Tuple head tail, some pm, e, h => by
    unfold LayoutStrategy.compute_size_and_align at h
    rcases ep1_bind_error h with ht | ⟨r, _, hp⟩
    · exact ep1_compute_size_and_align_error_of_lookup vt Q hSpec hvt tail (some pm) e ht
    · simp [pure, Except.pure] at hp

/-- `Machine::vtable_from_ptr` fails only by UB (unmapped vtable pointer) or by
a `prog.vtables` map-index spec panic. -/
private theorem ep1_vtableFromPtrM_error_is_ub_or_specPanic {M : Type} [Gen.Memory M]
    [MemoryOps M] (mach : Gen.Machine M) (p : Gen.ThinPointer (Gen.Memory.Provenance M))
    (e : Stop) (h : vtableFromPtrM mach p = .error e) :
    (∃ msg, e = .ub msg) ∨ (∃ msg, e = .specPanic msg) := by
  unfold vtableFromPtrM at h
  split at h
  · exact Or.inr (ep1_mapIndex_error_is_specPanic h)
  · simp [ub] at h; exact Or.inl ⟨_, h.symm⟩

/-- `check_ptr` at `PtrType::VTablePtr` with a machine (`some mach`) fails only
by UB or a `prog.vtables` map-index spec panic — never `unsupported`. -/
private theorem ep1_checkPtrM_vtablePtr_error_is_ub_or_specPanic {M : Type} [Gen.Memory M]
    [MemoryOps M] (mach : Gen.Machine M) (p : Gen.ThinPointer (Gen.Memory.Provenance M))
    (t : Gen.TraitName) (e : Stop)
    (h : checkPtrM (M := M) ⟨p, none⟩ (.VTablePtr t) (some mach) = .error e) :
    (∃ msg, e = .ub msg) ∨ (∃ msg, e = .specPanic msg) := by
  unfold checkPtrM at h
  dsimp only [PtrType.meta_kind, PtrType.safe_pointee] at h
  rcases ep1_bind_error h with h1 | ⟨_, _, h⟩
  · unfold ensureElseUb at h1
    split at h1
    · simp [ub] at h1; exact Or.inl ⟨_, h1.symm⟩
    · simp [pure, Except.pure] at h1
  · rw [checkPtrMetadataM_none] at h
    dsimp only [bind, Except.bind] at h
    rcases ep1_bind_error h with h2 | ⟨vt, _, h3⟩
    · exact ep1_vtableFromPtrM_error_is_ub_or_specPanic mach p e h2
    · unfold ensureElseUb at h3
      split at h3
      · simp [ub] at h3; exact Or.inl ⟨_, h3.symm⟩
      · simp [pure, Except.pure] at h3

/-- **Strict machine-supplied panic totality across all four metadata/vtable
unary operators**: when a machine `some mach` is supplied, every failure of
`UnOp::{GetMetadata, ComputeSize, ComputeAlign, VTableMethodLookup}` on any
`Memory` `M`, any type (including `TraitObject` and unsized structs with a
trait-object tail), and any operand is strictly `Stop.specPanic` — never
`unsupported` and never `Stop.ub`. -/
theorem ep1_evalUnOpM_meta_unops_some_mach_error_is_specPanic
    {M : Type} [Gen.Memory M] [MemoryOps M]
    (ty : Gen.Type) (meth : Gen.TraitMethodName) (arg : Gen.Value M × Gen.Type)
    (mach : Gen.Machine M) (e : Stop) :
    (evalUnOpM .GetMetadata arg (some mach) = .error e ∨
     evalUnOpM (.ComputeSize ty) arg (some mach) = .error e ∨
     evalUnOpM (.ComputeAlign ty) arg (some mach) = .error e ∨
     evalUnOpM (.VTableMethodLookup meth) arg (some mach) = .error e) →
    ∃ msg, e = .specPanic msg := by
  obtain ⟨v, opTy⟩ := arg
  have hDecode : ∀ (k : Gen.PointerMetaKind) (e' : Stop),
      PointerMetaKind.decode_valueM (M := M) k v = .error e' → ∃ msg, e' = .specPanic msg := by
    intro k e' h
    unfold PointerMetaKind.decode_valueM at h
    split at h <;> simp [specPanic, pure, Except.pure] at h
    exact ⟨_, h.symm⟩
  have hSpecQ : ∀ (msg : String), ∃ msg', Stop.specPanic msg = .specPanic msg' :=
    fun msg => ⟨msg, rfl⟩
  have hLookupSome : ∀ (p : Gen.ThinPointer (Gen.Memory.Provenance M)) (e' : Stop),
      vtableLookupM mach p = .error e' → ∃ msg, e' = .specPanic msg :=
    ep1_vtableLookupM_error_is_specPanic mach
  rintro (h | h | h | h)
  · -- GetMetadata
    have hPanic : ∀ (x : Interp (Gen.Value M × Gen.Type)),
        x = specPanic "non-pointer GetMetadata" → x = .error e →
        ∃ msg, e = .specPanic msg := by
      intro x hx hxe
      rw [hx] at hxe
      simp [specPanic] at hxe
      exact ⟨_, hxe.symm⟩
    cases v with
    | Ptr ptr =>
      cases opTy with
      | Ptr ptrTy =>
        unfold evalUnOpM at h
        dsimp only at h
        rcases ep1_bind_error h with hd | ⟨mv, hmv, h⟩
        · unfold PointerMetaKind.encode_as_valueM at hd
          split at hd <;> simp [specPanic, pure, Except.pure] at hd
          exact ⟨_, hd.symm⟩
        · cases hk : PtrType.meta_kind ptrTy with
          | VTablePointer t =>
            rw [hk] at h hmv
            cases hpm : ptr.metadata with
            | none => simp [hpm, PointerMetaKind.encode_as_valueM, specPanic] at hmv
            | some pm =>
              cases pm with
              | ElementCount _ => simp [hpm, PointerMetaKind.encode_as_valueM, specPanic] at hmv
              | VTablePointer p =>
                simp only [hpm, PointerMetaKind.encode_as_valueM, pure, Except.pure,
                  Except.ok.injEq] at hmv
                subst hmv
                have hcv : checkValueM (M := M) (.Ptr ⟨p, none⟩)
                    (PointerMetaKind.ty (.VTablePointer t)) (some mach) =
                    checkPtrM (M := M) ⟨p, none⟩ (.VTablePtr t) (some mach) := by
                  rw [PointerMetaKind.ty, checkValueM]
                dsimp only at h
                rw [hcv] at h
                cases hchk : checkPtrM (M := M) ⟨p, none⟩ (.VTablePtr t) (some mach) with
                | ok u =>
                  cases u
                  rw [hchk] at h
                  simp [pure, Except.pure] at h
                | error e' =>
                  rw [hchk] at h
                  rcases ep1_checkPtrM_vtablePtr_error_is_ub_or_specPanic mach p t e' hchk with
                    ⟨msg, rfl⟩ | ⟨msg, rfl⟩
                  · simp [specPanic] at h; exact ⟨_, h.symm⟩
                  · dsimp only at h; simp only [Except.error.injEq] at h; exact ⟨msg, h.symm⟩
          | None =>
            rw [hk] at h
            dsimp only at h
            split at h
            · simp [pure, Except.pure] at h
            · simp [specPanic] at h; exact ⟨_, h.symm⟩
          | ElementCount =>
            rw [hk] at h
            dsimp only at h
            split at h
            · simp [pure, Except.pure] at h
            · simp [specPanic] at h; exact ⟨_, h.symm⟩
      | _ => exact hPanic _ rfl h
    | _ => exact hPanic _ rfl h
  · -- ComputeSize
    unfold evalUnOpM at h
    dsimp only at h
    rcases ep1_bind_error h with hd | ⟨pm, _, h⟩
    · exact hDecode _ _ hd
    · rcases ep1_bind_error h with hl | ⟨lay, _, h⟩
      · exact ep1_Type_layout_error_is_specPanic ty e hl
      · rcases ep1_bind_error h with hc | ⟨x, _, hp⟩
        · unfold computeSizeM at hc
          rcases ep1_bind_error hc with hcsa | ⟨⟨_, _⟩, _, hp⟩
          · exact ep1_compute_size_and_align_error_of_lookup _ _ hSpecQ hLookupSome lay pm e hcsa
          · simp [pure, Except.pure] at hp
        · simp [pure, Except.pure] at hp
  · -- ComputeAlign
    unfold evalUnOpM at h
    dsimp only at h
    rcases ep1_bind_error h with hd | ⟨pm, _, h⟩
    · exact hDecode _ _ hd
    · rcases ep1_bind_error h with hl | ⟨lay, _, h⟩
      · exact ep1_Type_layout_error_is_specPanic ty e hl
      · rcases ep1_bind_error h with hc | ⟨x, _, hp⟩
        · unfold computeAlignM at hc
          rcases ep1_bind_error hc with hcsa | ⟨⟨_, _⟩, _, hp⟩
          · exact ep1_compute_size_and_align_error_of_lookup _ _ hSpecQ hLookupSome lay pm e hcsa
          · simp [pure, Except.pure] at hp
        · simp [pure, Except.pure] at hp
  · -- VTableMethodLookup
    have hPanic : ∀ (x : Interp (Gen.Value M × Gen.Type)),
        x = specPanic "vtable lookup on non-pointer" → x = .error e →
        ∃ msg, e = .specPanic msg := by
      intro x hx hxe
      rw [hx] at hxe
      simp [specPanic] at hxe
      exact ⟨_, hxe.symm⟩
    cases v with
    | Ptr ptr =>
      cases opTy with
      | Ptr ptrTy =>
        unfold evalUnOpM at h
        dsimp only at h
        rcases ep1_bind_error h with hv | ⟨vt, _, h⟩
        · exact ep1_vtableLookupM_error_is_specPanic mach _ e hv
        · rcases ep1_bind_error h with hf | ⟨fnName, _, h⟩
          · exact ep1_mapIndex_error_is_specPanic hf
          · rcases ep1_bind_error h with hp | ⟨fnThin, _, hp⟩
            · exact ep1_mapIndex_error_is_specPanic hp
            · simp [pure, Except.pure] at hp
      | _ => exact hPanic _ rfl h
    | _ => exact hPanic _ rfl h

/-- **No fabricated UB in the metadata operators.** Upstream's `eval_un_op` arms for
`GetMetadata`, `ComputeSize`, `ComputeAlign`, and `VTableMethodLookup` contain no
`throw_ub!` (only `panic!`s, `.expect(..)`, `unwrap()`s, and map indexing; the
`check_value` failure in `GetMetadata` is caught by `.expect(..)`). Accordingly, on
every `Memory` `M`, every operand, and with or without a machine, each of these four
operators either succeeds or stops with `Stop.specPanic` or (machine-free vtable cases
only) with the `unsupported` stop — never `Stop.ub` (nor `abort`, `deadlock`,
`machineStop`, or `memoryLeak`). -/
theorem ep1_evalUnOpM_meta_unops_error_is_specPanic_or_unsupported
    {M : Type} [Gen.Memory M] [MemoryOps M]
    (ty : Gen.Type) (meth : Gen.TraitMethodName) (arg : Gen.Value M × Gen.Type)
    (m : Option (Gen.Machine M)) (e : Stop) :
    (evalUnOpM .GetMetadata arg m = .error e ∨
     evalUnOpM (.ComputeSize ty) arg m = .error e ∨
     evalUnOpM (.ComputeAlign ty) arg m = .error e ∨
     evalUnOpM (.VTableMethodLookup meth) arg m = .error e) →
    (∃ msg, e = .specPanic msg) ∨ (∃ msg, e = .unsupported msg) := by
  cases m with
  | some mach =>
    intro h
    exact Or.inl (ep1_evalUnOpM_meta_unops_some_mach_error_is_specPanic ty meth arg mach e h)
  | none =>
    obtain ⟨v, opTy⟩ := arg
    have hDecode : ∀ (k : Gen.PointerMetaKind) (e' : Stop),
        PointerMetaKind.decode_valueM (M := M) k v = .error e' → ∃ msg, e' = .specPanic msg := by
      intro k e' h
      unfold PointerMetaKind.decode_valueM at h
      split at h <;> simp [specPanic, pure, Except.pure] at h
      exact ⟨_, h.symm⟩
    have hSpecQ : ∀ (msg : String),
        (∃ msg', Stop.specPanic msg = .specPanic msg') ∨
          (∃ msg', Stop.specPanic msg = .unsupported msg') :=
      fun msg => Or.inl ⟨msg, rfl⟩
    have hLookupNone : ∀ (what : String) (e' : Stop),
        (unsupported what : Interp Gen.VTable) = .error e' →
        (∃ msg, e' = .specPanic msg) ∨ (∃ msg, e' = .unsupported msg) := by
      intro what e' h
      simp [unsupported] at h
      exact Or.inr ⟨_, h.symm⟩
    rintro (h | h | h | h)
    · -- GetMetadata (`m = none`)
      have hPanic : ∀ (x : Interp (Gen.Value M × Gen.Type)),
          x = specPanic "non-pointer GetMetadata" → x = .error e →
          (∃ msg, e = .specPanic msg) ∨ (∃ msg, e = .unsupported msg) := by
        intro x hx hxe
        rw [hx] at hxe
        simp [specPanic] at hxe
        exact Or.inl ⟨_, hxe.symm⟩
      cases v with
      | Ptr ptr =>
        cases opTy with
        | Ptr ptrTy =>
          unfold evalUnOpM at h
          dsimp only at h
          rcases ep1_bind_error h with hd | ⟨mv, _, h⟩
          · unfold PointerMetaKind.encode_as_valueM at hd
            split at hd <;> simp [specPanic, pure, Except.pure] at hd
            exact Or.inl ⟨_, hd.symm⟩
          · cases hk : PtrType.meta_kind ptrTy with
            | VTablePointer t =>
              rw [hk] at h
              cases h
              exact Or.inr ⟨_, rfl⟩
            | None =>
              rw [hk] at h
              dsimp only at h
              split at h
              · simp [pure, Except.pure] at h
              · simp [specPanic] at h; exact Or.inl ⟨_, h.symm⟩
            | ElementCount =>
              rw [hk] at h
              dsimp only at h
              split at h
              · simp [pure, Except.pure] at h
              · simp [specPanic] at h; exact Or.inl ⟨_, h.symm⟩
        | _ => exact hPanic _ rfl h
      | _ => exact hPanic _ rfl h
    · -- ComputeSize (`m = none`)
      unfold evalUnOpM at h
      dsimp only at h
      rcases ep1_bind_error h with hd | ⟨pm, _, h⟩
      · exact Or.inl (hDecode _ _ hd)
      · rcases ep1_bind_error h with hl | ⟨lay, _, h⟩
        · exact Or.inl (ep1_Type_layout_error_is_specPanic ty e hl)
        · rcases ep1_bind_error h with hc | ⟨x, _, hp⟩
          · exact ep1_compute_size_and_align_error_of_lookup _ _ hSpecQ
              (fun _ e' hx => hLookupNone _ e' hx) lay pm e (ep1_map_error hc)
          · simp [pure, Except.pure] at hp
    · -- ComputeAlign (`m = none`)
      unfold evalUnOpM at h
      dsimp only at h
      rcases ep1_bind_error h with hd | ⟨pm, _, h⟩
      · exact Or.inl (hDecode _ _ hd)
      · rcases ep1_bind_error h with hl | ⟨lay, _, h⟩
        · exact Or.inl (ep1_Type_layout_error_is_specPanic ty e hl)
        · rcases ep1_bind_error h with hc | ⟨x, _, hp⟩
          · exact ep1_compute_size_and_align_error_of_lookup _ _ hSpecQ
              (fun _ e' hx => hLookupNone _ e' hx) lay pm e (ep1_map_error hc)
          · simp [pure, Except.pure] at hp
    · -- VTableMethodLookup (`m = none`)
      have hPanic : ∀ (x : Interp (Gen.Value M × Gen.Type)),
          x = specPanic "vtable lookup on non-pointer" → x = .error e →
          (∃ msg, e = .specPanic msg) ∨ (∃ msg, e = .unsupported msg) := by
        intro x hx hxe
        rw [hx] at hxe
        simp [specPanic] at hxe
        exact Or.inl ⟨_, hxe.symm⟩
      cases v with
      | Ptr ptr =>
        cases opTy with
        | Ptr ptrTy =>
          simp [evalUnOpM, unsupported] at h
          exact Or.inr ⟨_, h.symm⟩
        | _ => exact hPanic _ rfl h
      | _ => exact hPanic _ rfl h

/-! ### `[adv B1]` Concrete edge-case witnesses -/

/-- 8-byte align-4 enum whose `u8` tag lives at offset `4` (not `0`), with unit variants. -/
private def ep1EnumTagAt4Ty : Gen.Type :=
  let unitVar : Gen.Type := .Tuple [] ⟨⟨8⟩, ⟨4⟩, none⟩ none
  let v0 : Gen.Variant := { ty := unitVar, tagger := ⟨[(⟨4⟩, (ep1U8, 0))]⟩ }
  let v1 : Gen.Variant := { ty := unitVar, tagger := ⟨[(⟨4⟩, (ep1U8, 1))]⟩ }
  .Enum ⟨[(0, v0), (1, v1)]⟩ ep1U8
    (.Branch ⟨4⟩ ep1U8 .Invalid ⟨[((0, 1), .Known 0), ((1, 2), .Known 1)]⟩) ⟨8⟩ ⟨4⟩

/-- 4-byte align-2 enum with a two-level discriminator: a *signed* `i8` tag at offset `0`;
tag `-1` selects a second-level `u16` tag at offset `2` (bytes `[2..4)`), tag `0` is
discriminant `0`, and every other first-level tag falls back to discriminant `7`. Byte `1`
is read by no path. `GetDiscriminant` never consults `variants`, so they are left empty. -/
private def ep1NestedEnumTy : Gen.Type :=
  let inner : Gen.Discriminator :=
    .Branch ⟨2⟩ ep1U16 .Invalid ⟨[((0x100, 0x200), .Known 1), ((0x200, 0x300), .Known 2)]⟩
  let disc : Gen.Discriminator :=
    .Branch ⟨0⟩ ⟨.Signed, ⟨1⟩⟩ (.Known 7) ⟨[((-1, 0), inner), ((0, 1), .Known 0)]⟩
  .Enum ⟨[]⟩ ep1U8 disc ⟨4⟩ ⟨2⟩

/-- **`GetDiscriminant` reads exactly the bytes the discriminator touches — in order, threading
the machine — and nothing else** (multi-level discriminator, signed tag, fallback, data-race
access log, dereferenceability), on both `Mach` and `MachTB`:

1. two-level decode: first tag `-1` (`0xFF` at `i8`) then second tag `0x0150` gives
   discriminant `1`, and the machine's access log records exactly the two tag loads
   (`1` byte at `+0`, then `2` bytes at `+2`) in that order — byte `1` (uninitialized) is
   never read;
2. fallback: first tag `5` matches no child, so the result is the fallback discriminant `7`
   after exactly one 1-byte load, although bytes `[1..4)` are uninitialized;
3. second-level tag out of every child range (`0x0400`) reaches `Discriminator::Invalid`:
   UB; an uninitialized second-level tag is UB too (after the first load succeeded);
4. dereferenceability is required only for the bytes read: over a 2-byte allocation, the
   fallback path (`+0` only) succeeds although the 4-byte enum is not dereferenceable (and
   `Load` at the enum type is UB), whereas the two-level path's second load at `+2` is UB;
5. a tag at offset `4` over a 4-byte allocation: `ptr_offset_inbounds(ptr, 4)` succeeds
   (one-past-the-end) and the 1-byte load is out-of-bounds UB; through a pointer without
   provenance the same read is UB in `ptr_offset_inbounds` itself. Every UB message is
   pinned. -/
theorem ep1_getDiscriminant_nested_tags_access_log_and_dereferenceability_witness :
    let localTys : List (Gen.LocalName × Gen.Type) :=
      [(⟨⟨0⟩⟩, ep1NestedEnumTy), (⟨⟨1⟩⟩, ep1NestedEnumTy), (⟨⟨2⟩⟩, ep1NestedEnumTy),
       (⟨⟨3⟩⟩, ep1NestedEnumTy), (⟨⟨4⟩⟩, .Int ep1U16), (⟨⟨5⟩⟩, .Int ep1U16),
       (⟨⟨6⟩⟩, .Int ep1U32)]
    let mBM := ep1MachBM
      [{ data := [.Init 0xFF none, .Uninit, .Init 0x50 none, .Init 0x01 none],
         addr := 0x100, align := ⟨2⟩, kind := .Stack, live := true, extra := () },
       { data := [.Init 5 none, .Uninit, .Uninit, .Uninit],
         addr := 0x200, align := ⟨2⟩, kind := .Stack, live := true, extra := () },
       { data := [.Init 0xFF none, .Uninit, .Init 0x00 none, .Init 0x04 none],
         addr := 0x300, align := ⟨2⟩, kind := .Stack, live := true, extra := () },
       { data := [.Init 0xFF none, .Uninit, .Uninit, .Init 0x01 none],
         addr := 0x400, align := ⟨2⟩, kind := .Stack, live := true, extra := () },
       { data := [.Init 0xFF none, .Init 0 none],
         addr := 0x500, align := ⟨2⟩, kind := .Stack, live := true, extra := () },
       { data := [.Init 5 none, .Init 0 none],
         addr := 0x600, align := ⟨2⟩, kind := .Stack, live := true, extra := () },
       { data := List.replicate 4 (.Init 1 none),
         addr := 0x700, align := ⟨4⟩, kind := .Stack, live := true, extra := () }]
      [(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, ())⟩), (⟨⟨1⟩⟩, ⟨0x200, some (⟨1⟩, ())⟩),
       (⟨⟨2⟩⟩, ⟨0x300, some (⟨2⟩, ())⟩), (⟨⟨3⟩⟩, ⟨0x400, some (⟨3⟩, ())⟩),
       (⟨⟨4⟩⟩, ⟨0x500, some (⟨4⟩, ())⟩), (⟨⟨5⟩⟩, ⟨0x600, some (⟨5⟩, ())⟩),
       (⟨⟨6⟩⟩, ⟨0x700, some (⟨6⟩, ())⟩)]
      localTys
    let mTB := liftMachToTB mBM
    let viaRaw (l : Nat) (ty : Gen.Type) : Gen.PlaceExpr :=
      .Deref (.AddrOf (.Local ⟨⟨l⟩⟩) (.Raw .None)) ty
    let noProv (ty : Gen.Type) : Gen.PlaceExpr :=
      .Deref (.Constant (.PointerWithoutProvenance 0x700) (.Ptr (.Raw .None))) ty
    let invalidDiscrUb := "ValueExpr::GetDiscriminant encountered invalid discriminant."
    let oobUb := "dereferencing pointer outside the bounds of its allocation"
    let noProvUb := "dereferencing pointer without provenance"
    -- 1. two-level decode + exact access log
    (∃ m1, evalValue mBM (.GetDiscriminant (.Local ⟨⟨0⟩⟩)) = .ok ((.Int 1, .Int ep1U8), m1) ∧
      m1.mem.accesses = [⟨.Load, .None, 0x100, ⟨1⟩⟩, ⟨.Load, .None, 0x102, ⟨2⟩⟩]) ∧
    (∃ m1, evalValueM mTB (.GetDiscriminant (.Local ⟨⟨0⟩⟩)) = .ok ((.Int 1, .Int ep1U8), m1) ∧
      m1.mem.accesses = [⟨.Load, .None, 0x100, ⟨1⟩⟩, ⟨.Load, .None, 0x102, ⟨2⟩⟩]) ∧
    -- 2. fallback after exactly one load
    (∃ m1, evalValue mBM (.GetDiscriminant (.Local ⟨⟨1⟩⟩)) = .ok ((.Int 7, .Int ep1U8), m1) ∧
      m1.mem.accesses = [⟨.Load, .None, 0x200, ⟨1⟩⟩]) ∧
    (∃ m1, evalValueM mTB (.GetDiscriminant (.Local ⟨⟨1⟩⟩)) = .ok ((.Int 7, .Int ep1U8), m1) ∧
      m1.mem.accesses = [⟨.Load, .None, 0x200, ⟨1⟩⟩]) ∧
    -- 3. second-level `Invalid` and uninitialized second-level tag: UB
    (evalValue mBM (.GetDiscriminant (.Local ⟨⟨2⟩⟩)) = .error (.ub invalidDiscrUb) ∧
     evalValueM mTB (.GetDiscriminant (.Local ⟨⟨2⟩⟩)) = .error (.ub invalidDiscrUb) ∧
     evalValue mBM (.GetDiscriminant (.Local ⟨⟨3⟩⟩)) = .error (.ub invalidDiscrUb) ∧
     evalValueM mTB (.GetDiscriminant (.Local ⟨⟨3⟩⟩)) = .error (.ub invalidDiscrUb)) ∧
    -- 4. only the bytes read must be dereferenceable
    ((∃ m1, evalValue mBM (.GetDiscriminant (viaRaw 5 ep1NestedEnumTy)) =
        .ok ((.Int 7, .Int ep1U8), m1)) ∧
     (∃ m1, evalValueM mTB (.GetDiscriminant (viaRaw 5 ep1NestedEnumTy)) =
        .ok ((.Int 7, .Int ep1U8), m1)) ∧
     evalValue mBM (.Load (viaRaw 5 ep1NestedEnumTy)) = .error (.ub oobUb) ∧
     evalValueM mTB (.Load (viaRaw 5 ep1NestedEnumTy)) = .error (.ub oobUb) ∧
     evalValue mBM (.GetDiscriminant (viaRaw 4 ep1NestedEnumTy)) = .error (.ub oobUb) ∧
     evalValueM mTB (.GetDiscriminant (viaRaw 4 ep1NestedEnumTy)) = .error (.ub oobUb)) ∧
    -- 5. tag at offset 4: out-of-bounds load UB vs. `ptr_offset_inbounds` UB
    (evalValue mBM (.GetDiscriminant (viaRaw 6 ep1EnumTagAt4Ty)) = .error (.ub oobUb) ∧
     evalValueM mTB (.GetDiscriminant (viaRaw 6 ep1EnumTagAt4Ty)) = .error (.ub oobUb) ∧
     evalValue mBM (.GetDiscriminant (noProv ep1EnumTagAt4Ty)) = .error (.ub noProvUb) ∧
     evalValueM mTB (.GetDiscriminant (noProv ep1EnumTagAt4Ty)) = .error (.ub noProvUb)) := by
  intro localTys mBM mTB viaRaw noProv invalidDiscrUb oobUb noProvUb
  exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl⟩,
    ⟨⟨_, rfl⟩, ⟨_, rfl⟩, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl⟩⟩

/-- **Tree Borrows: a two-level `GetDiscriminant` skips the gap byte between its two tag
reads.** Through a child tag (`[0]`) of the enum allocation:

1. the child is `Frozen` on bytes `0`, `2`, `3` and `Disabled` on the gap byte `1`: the
   two-level decode (1 byte at `+0`, 2 bytes at `+2`) succeeds on `MachTB`, because byte
   `1` is never accessed, whereas a typed `Load` of the whole enum through the same child
   is Tree Borrows UB;
2. the child is `Disabled` on byte `3` (inside the second-level tag): the first tag read
   succeeds and the second is Tree Borrows UB on `MachTB`, while `BasicMemory` (no
   aliasing model) still returns discriminant `1`. -/
theorem ep1_getDiscriminant_tree_borrows_nested_gap_byte_witness :
    let enumBytes {P : Type} : List (Gen.AbstractByte P) :=
      [.Init 0xFF none, .Init 0 none, .Init 0x50 none, .Init 0x01 none]
    let localTys : List (Gen.LocalName × Gen.Type) :=
      [(⟨⟨0⟩⟩, ep1NestedEnumTy), (⟨⟨1⟩⟩, .Ptr (.Raw .None))]
    let ptrBytesBM : List Byte := encodePtrBytes (some (⟨0⟩, ())) 0 [0x00, 0x01, 0, 0, 0, 0, 0, 0]
    let ptrBytesTB : List (Gen.AbstractByte Gen.TreeBorrowsProvenance) :=
      encodePtrBytesM (M := TBM) (some (⟨0⟩, [0])) 0 [0x00, 0x01, 0, 0, 0, 0, 0, 0]
    let mBM := ep1MachBM
      [{ data := enumBytes, addr := 0x100, align := ⟨2⟩, kind := .Stack, live := true, extra := () },
       { data := ptrBytesBM, addr := 0x200, align := ⟨8⟩, kind := .Stack, live := true, extra := () }]
      [(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, ())⟩), (⟨⟨1⟩⟩, ⟨0x200, some (⟨1⟩, ())⟩)]
      localTys
    let childGapDisabled : Gen.Node :=
      { children := [],
        permissions := [.Unprot .Frozen, .Unprot .Disabled, .Unprot .Frozen, .Unprot .Frozen],
        «protected» := .No }
    let childSecondTagDisabled : Gen.Node :=
      { children := [],
        permissions := [.Unprot .Frozen, .Unprot .Frozen, .Unprot .Frozen, .Unprot .Disabled],
        «protected» := .No }
    let mkTB (child : Gen.Node) : MachTB :=
      ep1MachTB
        [ep1AllocTB 0x100 2 enumBytes [child], ep1AllocTB 0x200 8 ptrBytesTB]
        [(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, [])⟩), (⟨⟨1⟩⟩, ⟨0x200, some (⟨1⟩, [])⟩)]
        localTys
    let derefChildPlace : Gen.PlaceExpr := .Deref (.Load (.Local ⟨⟨1⟩⟩)) ep1NestedEnumTy
    let tbDisabledUb := "Tree Borrows: local read of Disabled reference"
    (∃ m1, evalValueM (mkTB childGapDisabled) (.GetDiscriminant derefChildPlace) =
        .ok ((.Int 1, .Int ep1U8), m1) ∧
      m1.mem.accesses.drop 1 = [⟨.Load, .None, 0x100, ⟨1⟩⟩, ⟨.Load, .None, 0x102, ⟨2⟩⟩]) ∧
    evalValueM (mkTB childGapDisabled) (.Load derefChildPlace) = .error (.ub tbDisabledUb) ∧
    evalValueM (mkTB childSecondTagDisabled) (.GetDiscriminant derefChildPlace) =
      .error (.ub tbDisabledUb) ∧
    (∃ m1, evalValue mBM (.GetDiscriminant derefChildPlace) = .ok ((.Int 1, .Int ep1U8), m1)) := by
  intro enumBytes localTys ptrBytesBM ptrBytesTB mBM childGapDisabled childSecondTagDisabled
    mkTB derefChildPlace tbDisabledUb
  exact ⟨⟨_, rfl, rfl⟩, rfl, rfl, ⟨_, rfl⟩⟩

/-- Kernel-checked reflexivity: closes `lhs = rhs` with `Eq.refl lhs`, leaving the
definitional-equality check to the kernel (no native evaluation, no `Lean.ofReduceBool`). -/
local elab "ep1_kernel_rfl" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let tgt ← Lean.MVarId.getType' mvarId
  let some (ty, lhs, _) := tgt.eq? |
    Lean.Meta.throwTacticEx `ep1_kernel_rfl mvarId "expected equality goal"
  let u ← Lean.Meta.getLevel ty
  mvarId.assign (Lean.mkApp2 (Lean.mkConst ``Eq.refl [u]) ty lhs)
  Lean.Elab.Tactic.replaceMainGoal []

private theorem ep1_ok_of_map_fst {α μ : Type} {r : Interp (α × μ)} {a : α}
    (h : Prod.fst <$> r = .ok a) : ∃ m, r = .ok (a, m) := by
  cases hr : r with
  | error e => simp [hr, Functor.map, Except.map] at h
  | ok p =>
    obtain ⟨a', m⟩ := p
    simp only [hr, Functor.map, Except.map, Except.ok.injEq] at h
    exact ⟨m, by rw [h]⟩

/-- **End-to-end `UnOp::{GetMetadata, ComputeSize, ComputeAlign}` through `eval_value`** on a
machine (the `some m` path of `eval_un_op`, after loading the operand pointer from memory),
on both `Mach` and `MachTB`: a wide `*const [u32]` of length `3` and a thin pointer are
loaded from locals; `GetMetadata` returns `3 : usize` resp. `()`, and feeding that metadata
to `ComputeSize` / `ComputeAlign` yields `12` / `4` for `[u32]` (slice layout) and for
`[u32; 3]` (sized layout). Metadata of the wrong kind for the type, and a non-pointer
`GetMetadata` operand, are spec panics (never UB). -/
theorem ep1_meta_unops_end_to_end_evalValue_witness :
    let sliceTy : Gen.Type := .Slice (.Int ep1U32)
    let arrTy : Gen.Type := .Array (.Int ep1U32) 3
    let usize : Gen.Type := .Int IntType.usize_ty
    let localTys : List (Gen.LocalName × Gen.Type) :=
      [(⟨⟨0⟩⟩, arrTy), (⟨⟨1⟩⟩, .Ptr (.Raw .ElementCount)), (⟨⟨2⟩⟩, .Ptr (.Raw .None))]
    let thinBytes : List Byte := encodePtrBytes (some (⟨0⟩, ())) 0 [0x00, 0x01, 0, 0, 0, 0, 0, 0]
    let lenBytes : List Byte :=
      [.Init 3 none, .Init 0 none, .Init 0 none, .Init 0 none,
       .Init 0 none, .Init 0 none, .Init 0 none, .Init 0 none]
    let mBM := ep1MachBM
      [{ data := List.replicate 12 (.Init 0 none), addr := 0x100, align := ⟨4⟩, kind := .Stack,
         live := true, extra := () },
       { data := thinBytes ++ lenBytes, addr := 0x200, align := ⟨8⟩, kind := .Stack,
         live := true, extra := () },
       { data := thinBytes, addr := 0x300, align := ⟨8⟩, kind := .Stack,
         live := true, extra := () }]
      [(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, ())⟩), (⟨⟨1⟩⟩, ⟨0x200, some (⟨1⟩, ())⟩),
       (⟨⟨2⟩⟩, ⟨0x300, some (⟨2⟩, ())⟩)]
      localTys
    let mTB := liftMachToTB mBM
    let wideMeta : Gen.ValueExpr := .UnOp .GetMetadata (.Load (.Local ⟨⟨1⟩⟩))
    let thinMeta : Gen.ValueExpr := .UnOp .GetMetadata (.Load (.Local ⟨⟨2⟩⟩))
    -- 1. Mach
    ((∃ m1, evalValue mBM wideMeta = .ok ((.Int 3, usize), m1)) ∧
     (∃ m1, evalValue mBM (.UnOp (.ComputeSize sliceTy) wideMeta) = .ok ((.Int 12, usize), m1)) ∧
     (∃ m1, evalValue mBM (.UnOp (.ComputeAlign sliceTy) wideMeta) = .ok ((.Int 4, usize), m1)) ∧
     (∃ m1, evalValue mBM thinMeta = .ok ((.Tuple [], unitType), m1)) ∧
     (∃ m1, evalValue mBM (.UnOp (.ComputeSize arrTy) thinMeta) = .ok ((.Int 12, usize), m1)) ∧
     (∃ m1, evalValue mBM (.UnOp (.ComputeAlign arrTy) thinMeta) = .ok ((.Int 4, usize), m1))) ∧
    -- 2. MachTB
    ((∃ m1, evalValueM mTB wideMeta = .ok ((.Int 3, usize), m1)) ∧
     (∃ m1, evalValueM mTB (.UnOp (.ComputeSize sliceTy) wideMeta) = .ok ((.Int 12, usize), m1)) ∧
     (∃ m1, evalValueM mTB (.UnOp (.ComputeAlign sliceTy) wideMeta) = .ok ((.Int 4, usize), m1)) ∧
     (∃ m1, evalValueM mTB thinMeta = .ok ((.Tuple [], unitType), m1)) ∧
     (∃ m1, evalValueM mTB (.UnOp (.ComputeSize arrTy) thinMeta) = .ok ((.Int 12, usize), m1)) ∧
     (∃ m1, evalValueM mTB (.UnOp (.ComputeAlign arrTy) thinMeta) = .ok ((.Int 4, usize), m1))) ∧
    -- 3. wrong metadata kind for the type and non-pointer operand: spec panics
    (evalValue mBM (.UnOp (.ComputeSize sliceTy) thinMeta) =
       specPanic "PointerMeta::decode_value called with invalid value" ∧
     evalValueM mTB (.UnOp (.ComputeSize sliceTy) thinMeta) =
       specPanic "PointerMeta::decode_value called with invalid value" ∧
     evalValue mBM (.UnOp (.ComputeAlign arrTy) wideMeta) =
       specPanic "PointerMeta::decode_value called with invalid value" ∧
     evalValueM mTB (.UnOp (.ComputeAlign arrTy) wideMeta) =
       specPanic "PointerMeta::decode_value called with invalid value" ∧
     evalValue mBM (.UnOp .GetMetadata (.Load (.Local ⟨⟨0⟩⟩))) =
       specPanic "non-pointer GetMetadata" ∧
     evalValueM mTB (.UnOp .GetMetadata (.Load (.Local ⟨⟨0⟩⟩))) =
       specPanic "non-pointer GetMetadata") := by
  intro sliceTy arrTy usize localTys thinBytes lenBytes mBM mTB wideMeta thinMeta
  refine ⟨⟨ep1_ok_of_map_fst ?_, ep1_ok_of_map_fst ?_, ep1_ok_of_map_fst ?_,
      ep1_ok_of_map_fst ?_, ep1_ok_of_map_fst ?_, ep1_ok_of_map_fst ?_⟩,
    ⟨ep1_ok_of_map_fst ?_, ep1_ok_of_map_fst ?_, ep1_ok_of_map_fst ?_,
      ep1_ok_of_map_fst ?_, ep1_ok_of_map_fst ?_, ep1_ok_of_map_fst ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  all_goals ep1_kernel_rfl

/-! ### Vtable pointers, trait-object safe pointers, and vtable unary operators with a machine

Concrete kernel-checked witnesses, on both `Mach` (`BasicMemory`) and `MachTB` (Tree
Borrows), for `Machine::vtable_from_ptr`, `check_ptr` at `PtrType::VTablePtr` and on
trait-object safe pointers (`&dyn Trait`, `Box<dyn Trait>`), and the vtable cases of
`UnOp::{GetMetadata, ComputeSize, ComputeAlign, VTableMethodLookup}`. The universal
statements are in `MiniRustSpec.Correspondence.Pointers` (`checkPtr_traitObject_ok`,
`checkPtr_vtablePtr_wrong_trait_ub`, ...). -/

private def ep1VtTrait0 : Gen.TraitName := ⟨⟨0⟩⟩
private def ep1VtTrait1 : Gen.TraitName := ⟨⟨1⟩⟩
private def ep1VtMeth0 : Gen.TraitMethodName := ⟨⟨0⟩⟩
private def ep1VtMeth1 : Gen.TraitMethodName := ⟨⟨1⟩⟩

/-- A vtable for trait `0`: size `8`, alignment `8`, and method `0` implemented by
function `1`. -/
private def ep1VTable0 : Gen.VTable :=
  { trait_name := ep1VtTrait0, size := ⟨8⟩, align := ⟨8⟩, cells := [],
    methods := ⟨[(ep1VtMeth0, ⟨⟨1⟩⟩)]⟩ }

/-- A vtable for trait `1`: size `4`, alignment `4`, no methods. -/
private def ep1VTable1 : Gen.VTable :=
  { trait_name := ep1VtTrait1, size := ⟨4⟩, align := ⟨4⟩, cells := [], methods := ⟨[]⟩ }

private def ep1VtProg : Gen.Program :=
  { functions := ⟨[]⟩, start := ⟨⟨0⟩⟩, globals := ⟨[]⟩,
    traits := ⟨[(ep1VtTrait0, ⟨[ep1VtMeth0]⟩), (ep1VtTrait1, ⟨[]⟩)]⟩,
    vtables := ⟨[(⟨⟨0⟩⟩, ep1VTable0), (⟨⟨1⟩⟩, ep1VTable1)]⟩ }

/-- Allocations of `ep1VtMachBM`: `0` is a live 8-byte object at `0x1000`, `1` a live
4-byte object at `0x2000`, `2` a dead 8-byte object at `0x3000`, `3` and `4` the vtables
for traits `0` and `1` at `0x4000` and `0x4008`, and `5` function `1` at `0x5000`. -/
private def ep1VtAllocsBM : List (Gen.Allocation Unit Unit) :=
  [{ data := List.replicate 8 (.Init 0 none), addr := 0x1000, align := ⟨8⟩, kind := .Heap,
     live := true, extra := () },
   { data := List.replicate 4 (.Init 0 none), addr := 0x2000, align := ⟨8⟩, kind := .Heap,
     live := true, extra := () },
   { data := List.replicate 8 (.Init 0 none), addr := 0x3000, align := ⟨8⟩, kind := .Heap,
     live := false, extra := () },
   { data := [], addr := 0x4000, align := ⟨1⟩, kind := .VTable, live := true, extra := () },
   { data := [], addr := 0x4008, align := ⟨1⟩, kind := .VTable, live := true, extra := () },
   { data := [], addr := 0x5000, align := ⟨1⟩, kind := .Function, live := true, extra := () }]

/-- A `BasicMemory` machine with two vtables and one function pointer. -/
private def ep1VtMachBM : Mach :=
  { prog := ep1VtProg
    mem := { memory := { allocations := ep1VtAllocsBM, _phantom := ⟨⟩ }, accesses := [] }
    intptrcast := ⟨⟨[]⟩⟩
    threads := []
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[]⟩
    fn_ptrs := ⟨[(⟨⟨1⟩⟩, ⟨0x5000, some (⟨5⟩, ())⟩)]⟩
    vtable_ptrs := ⟨[(⟨⟨0⟩⟩, ⟨0x4000, some (⟨3⟩, ())⟩), (⟨⟨1⟩⟩, ⟨0x4008, some (⟨4⟩, ())⟩)]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

private def ep1VtAllocTB (addr : Int) (al n : Nat) (kind : Gen.AllocationKind) (live : Bool) :
    Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra :=
  { data := List.replicate n (.Init 0 none), addr := addr, align := ⟨al⟩, kind := kind,
    live := live,
    extra := { root := { children := [], permissions := List.replicate n (.Unprot .Unique),
                         «protected» := .No } } }

/-- The Tree Borrows allocations corresponding to `ep1VtAllocsBM`. -/
private def ep1VtAllocsTB : List (Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) :=
  [ep1VtAllocTB 0x1000 8 8 .Heap true, ep1VtAllocTB 0x2000 8 4 .Heap true,
   ep1VtAllocTB 0x3000 8 8 .Heap false, ep1VtAllocTB 0x4000 1 0 .VTable true,
   ep1VtAllocTB 0x4008 1 0 .VTable true, ep1VtAllocTB 0x5000 1 0 .Function true]

/-- The Tree Borrows machine with the same allocations, vtables, and function pointer as
`ep1VtMachBM` (root provenance `[]`). -/
private def ep1VtMachTB : MachTB :=
  { prog := ep1VtProg
    mem := { memory := { params := { implicit_writes := false },
                         mem := { allocations := ep1VtAllocsTB, _phantom := ⟨⟩ } },
             accesses := [] }
    intptrcast := ⟨⟨[]⟩⟩
    threads := []
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[]⟩
    fn_ptrs := ⟨[(⟨⟨1⟩⟩, ⟨0x5000, some (⟨5⟩, [])⟩)]⟩
    vtable_ptrs := ⟨[(⟨⟨0⟩⟩, ⟨0x4000, some (⟨3⟩, [])⟩), (⟨⟨1⟩⟩, ⟨0x4008, some (⟨4⟩, [])⟩)]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

/-- `PointeeInfo` of `dyn Trait` for the given trait. -/
private def ep1DynPointee (t : Gen.TraitName) : Gen.PointeeInfo :=
  { layout := .TraitObject t, inhabited := true, unsafe_cells := .TraitObject, freeze := true,
    unpin := true }

/-- **Positive witness: vtable pointers, `&dyn Trait` / `Box<dyn Trait>` validity, and the
vtable unary operators with a machine**, on both `Mach` and `MachTB`. For the data
pointer `0x1000` (a live 8-byte, 8-aligned object) with the vtable pointer `0x4000` of
trait `0` (dynamic size `8`, alignment `8`):
1. `Machine::vtable_from_ptr` finds the vtable, and `check_ptr` accepts the stand-alone
   vtable pointer at `PtrType::VTablePtr` and the trait objects `&dyn Trait` and
   `Box<dyn Trait>` (vtable lookup, trait match, dynamic size and alignment, and
   `Memory::dereferenceable`);
2. `UnOp::GetMetadata` extracts the vtable pointer at `Type::Ptr(PtrType::VTablePtr(..))`;
3. `UnOp::ComputeSize` / `UnOp::ComputeAlign` on `Type::TraitObject` return the vtable's
   size `8` and alignment `8`;
4. `UnOp::VTableMethodLookup` resolves method `0` to the function pointer of function
   `1` at `Type::Ptr(PtrType::FnPtr)`, and chaining `GetMetadata` into
   `VTableMethodLookup` yields exactly the value of `Constant::FnPointer` for function
   `1`, the callee value that `Terminator::Call` resolves with `Machine::fn_from_ptr`
   (dynamic dispatch; `dynDispatch_call_mach_and_machTB_witness` in
   `MiniRustSpec.UnwindSetDiscrAndFnPtrMR` runs the call itself). -/
theorem ep1_vtable_dyn_safe_ptr_and_unops_witness :
    let dynRef : Gen.PtrType := .Ref .Immutable (ep1DynPointee ep1VtTrait0)
    let dynBox : Gen.PtrType := .Box (ep1DynPointee ep1VtTrait0)
    let vtTy : Gen.Type := .Ptr (.VTablePtr ep1VtTrait0)
    let usize : Gen.Type := .Int IntType.usize_ty
    let vt0 : Ptr := ⟨0x4000, some (⟨3⟩, ())⟩
    let fn1 : Ptr := ⟨0x5000, some (⟨5⟩, ())⟩
    let wide : Gen.Pointer Prov := ⟨⟨0x1000, some (⟨0⟩, ())⟩, some (.VTablePointer vt0)⟩
    let vt0TB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x4000, some (⟨3⟩, [])⟩
    let fn1TB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x5000, some (⟨5⟩, [])⟩
    let wideTB : Gen.Pointer Gen.TreeBorrowsProvenance :=
      ⟨⟨0x1000, some (⟨0⟩, [])⟩, some (.VTablePointer vt0TB)⟩
    -- 1. `Mach`: vtable lookup and pointer validity
    (vtableFromPtr ep1VtMachBM vt0 = .ok ep1VTable0 ∧
     checkPtr (ThinPointer.widen vt0 none) (.VTablePtr ep1VtTrait0) (some ep1VtMachBM) = .ok () ∧
     checkPtr wide dynRef (some ep1VtMachBM) = .ok () ∧
     checkPtr wide dynBox (some ep1VtMachBM) = .ok () ∧
     checkValue (.Ptr wide) (.Ptr dynRef) (some ep1VtMachBM) = .ok ()) ∧
    -- 2.-4. `Mach`: vtable unary operators and the callee value of `Terminator::Call`
    (evalUnOp .GetMetadata (.Ptr wide, .Ptr dynRef) (some ep1VtMachBM) =
       .ok (.Ptr (ThinPointer.widen vt0 none), vtTy) ∧
     evalUnOp (.ComputeSize (.TraitObject ep1VtTrait0)) (.Ptr (ThinPointer.widen vt0 none), vtTy)
         (some ep1VtMachBM) = .ok (.Int 8, usize) ∧
     evalUnOp (.ComputeAlign (.TraitObject ep1VtTrait0)) (.Ptr (ThinPointer.widen vt0 none), vtTy)
         (some ep1VtMachBM) = .ok (.Int 8, usize) ∧
     evalUnOp (.VTableMethodLookup ep1VtMeth0) (.Ptr (ThinPointer.widen vt0 none), vtTy)
         (some ep1VtMachBM) = .ok (.Ptr (ThinPointer.widen fn1 none), .Ptr .FnPtr) ∧
     (do
        let (metaVal, metaTy) ← evalUnOp .GetMetadata (.Ptr wide, .Ptr dynRef) (some ep1VtMachBM)
        let (fnVal, _) ← evalUnOp (.VTableMethodLookup ep1VtMeth0) (metaVal, metaTy)
          (some ep1VtMachBM)
        pure fnVal) =
       evalConstant ep1VtMachBM (.FnPointer ⟨⟨1⟩⟩)) ∧
    -- 1. `MachTB`: vtable lookup and pointer validity
    (vtableFromPtrM ep1VtMachTB vt0TB = .ok ep1VTable0 ∧
     checkPtrM (M := TBM) (ThinPointer.widen vt0TB none) (.VTablePtr ep1VtTrait0)
         (some ep1VtMachTB) = .ok () ∧
     checkPtrM (M := TBM) wideTB dynRef (some ep1VtMachTB) = .ok () ∧
     checkPtrM (M := TBM) wideTB dynBox (some ep1VtMachTB) = .ok () ∧
     checkValueM (M := TBM) (.Ptr wideTB) (.Ptr dynRef) (some ep1VtMachTB) = .ok ()) ∧
    -- 2.-4. `MachTB`: vtable unary operators and the callee value of `Terminator::Call`
    (evalUnOpM (M := TBM) .GetMetadata (.Ptr wideTB, .Ptr dynRef) (some ep1VtMachTB) =
       .ok (.Ptr (ThinPointer.widen vt0TB none), vtTy) ∧
     evalUnOpM (M := TBM) (.ComputeSize (.TraitObject ep1VtTrait0))
         (.Ptr (ThinPointer.widen vt0TB none), vtTy) (some ep1VtMachTB) = .ok (.Int 8, usize) ∧
     evalUnOpM (M := TBM) (.ComputeAlign (.TraitObject ep1VtTrait0))
         (.Ptr (ThinPointer.widen vt0TB none), vtTy) (some ep1VtMachTB) = .ok (.Int 8, usize) ∧
     evalUnOpM (M := TBM) (.VTableMethodLookup ep1VtMeth0)
         (.Ptr (ThinPointer.widen vt0TB none), vtTy) (some ep1VtMachTB) =
       .ok (.Ptr (ThinPointer.widen fn1TB none), .Ptr .FnPtr) ∧
     (do
        let (metaVal, metaTy) ← evalUnOpM (M := TBM) .GetMetadata (.Ptr wideTB, .Ptr dynRef)
          (some ep1VtMachTB)
        let (fnVal, _) ← evalUnOpM (M := TBM) (.VTableMethodLookup ep1VtMeth0) (metaVal, metaTy)
          (some ep1VtMachTB)
        pure fnVal) =
       evalConstantM ep1VtMachTB (.FnPointer ⟨⟨1⟩⟩)) := by
  intro dynRef dynBox vtTy usize vt0 fn1 wide vt0TB fn1TB wideTB
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  all_goals ep1_kernel_rfl

/-- **Negative witness: UB and panics of vtable pointers and trait-object safe pointers**,
on both `Mach` and `MachTB` (`ucg#516`: the vtable of a `dyn Trait` wide pointer must be
a vtable for that trait):
1. a null, dangling, or unmapped (data) pointer used as a vtable pointer is UB
   (`"invalid pointer for vtable lookup"`), stand-alone and as trait-object metadata;
2. a valid vtable pointer for the wrong trait is UB
   (`"Value::Ptr: invalid vtable in metadata"`);
3. a `&dyn Trait` with valid vtable metadata whose data pointer is not aligned to the
   vtable's alignment `8` is UB (`"Value::Ptr: unaligned safe pointer"`);
4. a `&dyn Trait` with valid vtable metadata whose data allocation is smaller than the
   vtable's size `8`, or dead, is UB (`"Value::Ptr: non-dereferenceable safe pointer"`);
5. the corresponding sanity check of `UnOp::GetMetadata` and the `unwrap()`s and map
   indices of `UnOp::VTableMethodLookup` are spec panics, never UB. -/
theorem ep1_vtable_dyn_safe_ptr_ub_witness :
    let dynRef : Gen.PtrType := .Ref .Immutable (ep1DynPointee ep1VtTrait0)
    let vtTy : Gen.Type := .Ptr (.VTablePtr ep1VtTrait0)
    let invalidVt := "invalid pointer for vtable lookup"
    let wrongTrait := "Value::Ptr: invalid vtable in metadata"
    let unaligned := "Value::Ptr: unaligned safe pointer"
    let nonDeref := "Value::Ptr: non-dereferenceable safe pointer"
    let lookupPanic := "ptrs.iter().find(|(_, vtable_ptr)| *vtable_ptr == ptr).unwrap()"
    let vt0 : Ptr := ⟨0x4000, some (⟨3⟩, ())⟩
    let vt1 : Ptr := ⟨0x4008, some (⟨4⟩, ())⟩
    let obj : Ptr := ⟨0x1000, some (⟨0⟩, ())⟩
    let vt0TB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x4000, some (⟨3⟩, [])⟩
    let vt1TB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x4008, some (⟨4⟩, [])⟩
    let objTB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x1000, some (⟨0⟩, [])⟩
    -- `Mach`
    (-- 1. null, dangling, and unmapped vtable pointers
     checkPtr (ThinPointer.widen ⟨0, none⟩ none) (.VTablePtr ep1VtTrait0) (some ep1VtMachBM) =
       .error (.ub invalidVt) ∧
     checkPtr ⟨obj, some (.VTablePointer ⟨0, none⟩)⟩ dynRef (some ep1VtMachBM) =
       .error (.ub invalidVt) ∧
     checkPtr ⟨obj, some (.VTablePointer ⟨0x4000, none⟩)⟩ dynRef (some ep1VtMachBM) =
       .error (.ub invalidVt) ∧
     checkPtr ⟨obj, some (.VTablePointer obj)⟩ dynRef (some ep1VtMachBM) =
       .error (.ub invalidVt) ∧
     -- 2. vtable for the wrong trait
     checkPtr (ThinPointer.widen vt1 none) (.VTablePtr ep1VtTrait0) (some ep1VtMachBM) =
       .error (.ub wrongTrait) ∧
     checkPtr ⟨obj, some (.VTablePointer vt1)⟩ dynRef (some ep1VtMachBM) =
       .error (.ub wrongTrait) ∧
     -- 3. data pointer not aligned to the vtable's alignment
     checkPtr ⟨⟨0x1004, some (⟨0⟩, ())⟩, some (.VTablePointer vt0)⟩ dynRef (some ep1VtMachBM) =
       .error (.ub unaligned) ∧
     -- 4. data allocation smaller than the vtable's size, or dead
     checkPtr ⟨⟨0x2000, some (⟨1⟩, ())⟩, some (.VTablePointer vt0)⟩ dynRef (some ep1VtMachBM) =
       .error (.ub nonDeref) ∧
     checkPtr ⟨⟨0x3000, some (⟨2⟩, ())⟩, some (.VTablePointer vt0)⟩ dynRef (some ep1VtMachBM) =
       .error (.ub nonDeref) ∧
     -- 5. spec panics of the unary operators
     evalUnOp .GetMetadata (.Ptr ⟨obj, some (.VTablePointer vt1)⟩, .Ptr dynRef)
         (some ep1VtMachBM) =
       specPanic "GetMetadata: sanity check, returned meta is well-formed" ∧
     evalUnOp (.VTableMethodLookup ep1VtMeth0) (.Ptr (ThinPointer.widen obj none), vtTy)
         (some ep1VtMachBM) = specPanic lookupPanic ∧
     evalUnOp (.VTableMethodLookup ep1VtMeth1) (.Ptr (ThinPointer.widen vt0 none), vtTy)
         (some ep1VtMachBM) = specPanic "map index: missing key (vtable.methods[method])" ∧
     evalUnOp (.VTableMethodLookup ep1VtMeth0) (.Int 0, vtTy) (some ep1VtMachBM) =
       specPanic "vtable lookup on non-pointer") ∧
    -- `MachTB`
    (checkPtrM (M := TBM) (ThinPointer.widen ⟨0, none⟩ none) (.VTablePtr ep1VtTrait0)
         (some ep1VtMachTB) = .error (.ub invalidVt) ∧
     checkPtrM (M := TBM) ⟨objTB, some (.VTablePointer ⟨0, none⟩)⟩ dynRef (some ep1VtMachTB) =
       .error (.ub invalidVt) ∧
     checkPtrM (M := TBM) ⟨objTB, some (.VTablePointer ⟨0x4000, none⟩)⟩ dynRef
         (some ep1VtMachTB) = .error (.ub invalidVt) ∧
     checkPtrM (M := TBM) ⟨objTB, some (.VTablePointer objTB)⟩ dynRef (some ep1VtMachTB) =
       .error (.ub invalidVt) ∧
     checkPtrM (M := TBM) (ThinPointer.widen vt1TB none) (.VTablePtr ep1VtTrait0)
         (some ep1VtMachTB) = .error (.ub wrongTrait) ∧
     checkPtrM (M := TBM) ⟨objTB, some (.VTablePointer vt1TB)⟩ dynRef (some ep1VtMachTB) =
       .error (.ub wrongTrait) ∧
     checkPtrM (M := TBM) ⟨⟨0x1004, some (⟨0⟩, [])⟩, some (.VTablePointer vt0TB)⟩ dynRef
         (some ep1VtMachTB) = .error (.ub unaligned) ∧
     checkPtrM (M := TBM) ⟨⟨0x2000, some (⟨1⟩, [])⟩, some (.VTablePointer vt0TB)⟩ dynRef
         (some ep1VtMachTB) = .error (.ub nonDeref) ∧
     checkPtrM (M := TBM) ⟨⟨0x3000, some (⟨2⟩, [])⟩, some (.VTablePointer vt0TB)⟩ dynRef
         (some ep1VtMachTB) = .error (.ub nonDeref) ∧
     evalUnOpM (M := TBM) .GetMetadata (.Ptr ⟨objTB, some (.VTablePointer vt1TB)⟩, .Ptr dynRef)
         (some ep1VtMachTB) =
       specPanic "GetMetadata: sanity check, returned meta is well-formed" ∧
     evalUnOpM (M := TBM) (.VTableMethodLookup ep1VtMeth0)
         (.Ptr (ThinPointer.widen objTB none), vtTy) (some ep1VtMachTB) = specPanic lookupPanic ∧
     evalUnOpM (M := TBM) (.VTableMethodLookup ep1VtMeth1)
         (.Ptr (ThinPointer.widen vt0TB none), vtTy) (some ep1VtMachTB) =
       specPanic "map index: missing key (vtable.methods[method])" ∧
     evalUnOpM (M := TBM) (.VTableMethodLookup ep1VtMeth0) (.Int 0, vtTy) (some ep1VtMachTB) =
       specPanic "vtable lookup on non-pointer") := by
  intro dynRef vtTy invalidVt wrongTrait unaligned nonDeref lookupPanic vt0 vt1 obj vt0TB vt1TB
    objTB
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  all_goals ep1_kernel_rfl

/-- **Error-kind, raw `*const dyn Trait` (`ucg#516`), corrupt-table panic
precedence, and check-order witness**, on both `Mach` and `MachTB`:
1. out-of-bounds vtable addresses (`-1`, `2^64`) are UB (`pointer out-of-bounds`)
   in `check_ptr` and trigger the `.expect(..)` spec panic in `GetMetadata`;
2. non-empty metadata on `PtrType::VTablePtr` is UB (`invalid metadata`);
3. raw `*const dyn Trait` accepts null/unaligned/no-provenance data pointers
   when the vtable metadata is valid, and rejects invalid or wrong-trait vtable
   pointers with UB;
4. when `vtable_ptrs` maps a pointer to a `VTableName` absent from `prog.vtables`,
   `vtable_from_ptr`, `check_ptr`, and `GetMetadata` all propagate the exact
   `self.prog.vtables[vtable_name]` map-index spec panic (upstream `.expect(..)`
   does not mask an inner panic), while `ComputeSize` reports `vtables[name]`,
   a missing `fn_ptrs` entry in `VTableMethodLookup` reports `self.fn_ptrs[fn_name]`,
   and a pointer value with a non-pointer type reports `vtable lookup on non-pointer`;
5. `check_ptr` precedence: out-of-bounds thin address precedes invalid vtable,
   wrong trait precedes null safe pointer, and `isize::MAX` overflow precedes
   null/uninhabited checks. -/
theorem ep1_vtable_error_precedence_and_corrupt_table_witness :
    let vtMissingFn : Gen.VTable :=
      { trait_name := ep1VtTrait0, size := ⟨8⟩, align := ⟨8⟩, cells := [],
        methods := ⟨[(ep1VtMeth0, ⟨⟨9⟩⟩)]⟩ }
    let vtTooBig : Gen.VTable :=
      { trait_name := ep1VtTrait0, size := ⟨9223372036854775808⟩, align := ⟨8⟩, cells := [],
        methods := ⟨[]⟩ }
    let corruptProg : Gen.Program :=
      { ep1VtProg with
        vtables := ⟨[(⟨⟨0⟩⟩, ep1VTable0), (⟨⟨1⟩⟩, ep1VTable1),
          (⟨⟨2⟩⟩, vtMissingFn), (⟨⟨3⟩⟩, vtTooBig)]⟩ }
    let corruptAllocs : List (Gen.Allocation Unit Unit) :=
      ep1VtAllocsBM ++
        [{ data := [], addr := 0x4010, align := ⟨1⟩, kind := .VTable, live := true, extra := () },
         { data := [], addr := 0x4018, align := ⟨1⟩, kind := .VTable, live := true, extra := () },
         { data := [], addr := 0x4020, align := ⟨1⟩, kind := .VTable, live := true, extra := () }]
    let vt0 : Ptr := ⟨0x4000, some (⟨3⟩, ())⟩
    let vt1 : Ptr := ⟨0x4008, some (⟨4⟩, ())⟩
    let vtMissing : Ptr := ⟨0x4010, some (⟨6⟩, ())⟩
    let vtMissingFnPtr : Ptr := ⟨0x4018, some (⟨7⟩, ())⟩
    let vtTooBigPtr : Ptr := ⟨0x4020, some (⟨8⟩, ())⟩
    let obj : Ptr := ⟨0x1000, some (⟨0⟩, ())⟩
    let corruptBM : Mach :=
      { ep1VtMachBM with
        prog := corruptProg
        mem := { memory := { allocations := corruptAllocs, _phantom := ⟨⟩ }, accesses := [] }
        vtable_ptrs := ⟨[(⟨⟨0⟩⟩, vt0), (⟨⟨1⟩⟩, vt1), (⟨⟨9⟩⟩, vtMissing),
          (⟨⟨2⟩⟩, vtMissingFnPtr), (⟨⟨3⟩⟩, vtTooBigPtr)]⟩ }
    let corruptTB : MachTB := liftMachToTB corruptBM
    let vt0TB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x4000, some (⟨3⟩, [])⟩
    let vt1TB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x4008, some (⟨4⟩, [])⟩
    let vtMissingTB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x4010, some (⟨6⟩, [])⟩
    let vtMissingFnTB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x4018, some (⟨7⟩, [])⟩
    let vtTooBigTB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x4020, some (⟨8⟩, [])⟩
    let objTB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x1000, some (⟨0⟩, [])⟩
    let dynRef : Gen.PtrType := .Ref .Immutable (ep1DynPointee ep1VtTrait0)
    let dynUninhab : Gen.PtrType :=
      .Ref .Immutable { ep1DynPointee ep1VtTrait0 with inhabited := false }
    let rawDyn : Gen.PtrType := .Raw (.VTablePointer ep1VtTrait0)
    let vtTy : Gen.Type := .Ptr (.VTablePtr ep1VtTrait0)
    let oobPtr := "Value::Ptr: pointer out-of-bounds"
    let invalidMeta := "Value::Ptr: invalid metadata"
    let invalidVt := "invalid pointer for vtable lookup"
    let wrongTrait := "Value::Ptr: invalid vtable in metadata"
    let sizeOverflow := "Value::Ptr: total size exeeds isize::MAX"
    let sanityPanic := "GetMetadata: sanity check, returned meta is well-formed"
    let missingProgVt := "map index: missing key (self.prog.vtables[vtable_name])"
    let missingLookupVt := "map index: missing key (vtables[name])"
    let missingFnPtr := "map index: missing key (self.fn_ptrs[fn_name])"
    let nonPtrLookup := "vtable lookup on non-pointer"
    -- `Mach`
    (checkPtr (ThinPointer.widen ⟨-1, none⟩ none) (.VTablePtr ep1VtTrait0) (some corruptBM) =
       .error (.ub oobPtr) ∧
     checkPtr (ThinPointer.widen ⟨18446744073709551616, none⟩ none) (.VTablePtr ep1VtTrait0)
         (some corruptBM) = .error (.ub oobPtr) ∧
     evalUnOp .GetMetadata (.Ptr ⟨obj, some (.VTablePointer ⟨-1, none⟩)⟩, .Ptr dynRef)
         (some corruptBM) = specPanic sanityPanic ∧
     checkPtr (ThinPointer.widen vt0 (some (.ElementCount 0))) (.VTablePtr ep1VtTrait0)
         (some corruptBM) = .error (.ub invalidMeta) ∧
     checkPtr ⟨⟨0, none⟩, some (.VTablePointer vt0)⟩ rawDyn (some corruptBM) = .ok () ∧
     checkPtr ⟨⟨0x1003, none⟩, some (.VTablePointer vt0)⟩ rawDyn (some corruptBM) = .ok () ∧
     checkPtr ⟨⟨0, none⟩, some (.VTablePointer ⟨0, none⟩)⟩ rawDyn (some corruptBM) =
       .error (.ub invalidVt) ∧
     checkPtr ⟨⟨0, none⟩, some (.VTablePointer vt1)⟩ rawDyn (some corruptBM) =
       .error (.ub wrongTrait) ∧
     vtableFromPtr corruptBM vtMissing = specPanic missingProgVt ∧
     checkPtr (ThinPointer.widen vtMissing none) (.VTablePtr ep1VtTrait0) (some corruptBM) =
       specPanic missingProgVt ∧
     evalUnOp .GetMetadata (.Ptr ⟨obj, some (.VTablePointer vtMissing)⟩, .Ptr dynRef)
         (some corruptBM) = specPanic missingProgVt ∧
     evalUnOp (.ComputeSize (.TraitObject ep1VtTrait0))
         (.Ptr (ThinPointer.widen vtMissing none), vtTy) (some corruptBM) =
       specPanic missingLookupVt ∧
     evalUnOp (.VTableMethodLookup ep1VtMeth0)
         (.Ptr (ThinPointer.widen vtMissingFnPtr none), vtTy) (some corruptBM) =
       specPanic missingFnPtr ∧
     evalUnOp (.VTableMethodLookup ep1VtMeth0)
         (.Ptr (ThinPointer.widen vt0 none), .Int ep1U32) (some corruptBM) =
       specPanic nonPtrLookup ∧
     checkPtr ⟨⟨-1, none⟩, some (.VTablePointer ⟨0, none⟩)⟩ dynRef (some corruptBM) =
       .error (.ub oobPtr) ∧
     checkPtr ⟨⟨0, none⟩, some (.VTablePointer vt1)⟩ dynRef (some corruptBM) =
       .error (.ub wrongTrait) ∧
     checkPtr ⟨⟨0, none⟩, some (.VTablePointer vtTooBigPtr)⟩ dynUninhab (some corruptBM) =
       .error (.ub sizeOverflow)) ∧
    -- `MachTB`
    (checkPtrM (M := TBM) (ThinPointer.widen ⟨-1, none⟩ none) (.VTablePtr ep1VtTrait0)
         (some corruptTB) = .error (.ub oobPtr) ∧
     checkPtrM (M := TBM) (ThinPointer.widen ⟨18446744073709551616, none⟩ none)
         (.VTablePtr ep1VtTrait0) (some corruptTB) = .error (.ub oobPtr) ∧
     evalUnOpM (M := TBM) .GetMetadata
         (.Ptr ⟨objTB, some (.VTablePointer ⟨-1, none⟩)⟩, .Ptr dynRef) (some corruptTB) =
       specPanic sanityPanic ∧
     checkPtrM (M := TBM) (ThinPointer.widen vt0TB (some (.ElementCount 0)))
         (.VTablePtr ep1VtTrait0) (some corruptTB) = .error (.ub invalidMeta) ∧
     checkPtrM (M := TBM) ⟨⟨0, none⟩, some (.VTablePointer vt0TB)⟩ rawDyn (some corruptTB) =
       .ok () ∧
     checkPtrM (M := TBM) ⟨⟨0x1003, none⟩, some (.VTablePointer vt0TB)⟩ rawDyn (some corruptTB) =
       .ok () ∧
     checkPtrM (M := TBM) ⟨⟨0, none⟩, some (.VTablePointer ⟨0, none⟩)⟩ rawDyn (some corruptTB) =
       .error (.ub invalidVt) ∧
     checkPtrM (M := TBM) ⟨⟨0, none⟩, some (.VTablePointer vt1TB)⟩ rawDyn (some corruptTB) =
       .error (.ub wrongTrait) ∧
     vtableFromPtrM corruptTB vtMissingTB = specPanic missingProgVt ∧
     checkPtrM (M := TBM) (ThinPointer.widen vtMissingTB none) (.VTablePtr ep1VtTrait0)
         (some corruptTB) = specPanic missingProgVt ∧
     evalUnOpM (M := TBM) .GetMetadata
         (.Ptr ⟨objTB, some (.VTablePointer vtMissingTB)⟩, .Ptr dynRef) (some corruptTB) =
       specPanic missingProgVt ∧
     evalUnOpM (M := TBM) (.ComputeSize (.TraitObject ep1VtTrait0))
         (.Ptr (ThinPointer.widen vtMissingTB none), vtTy) (some corruptTB) =
       specPanic missingLookupVt ∧
     evalUnOpM (M := TBM) (.VTableMethodLookup ep1VtMeth0)
         (.Ptr (ThinPointer.widen vtMissingFnTB none), vtTy) (some corruptTB) =
       specPanic missingFnPtr ∧
     evalUnOpM (M := TBM) (.VTableMethodLookup ep1VtMeth0)
         (.Ptr (ThinPointer.widen vt0TB none), .Int ep1U32) (some corruptTB) =
       specPanic nonPtrLookup ∧
     checkPtrM (M := TBM) ⟨⟨-1, none⟩, some (.VTablePointer ⟨0, none⟩)⟩ dynRef (some corruptTB) =
       .error (.ub oobPtr) ∧
     checkPtrM (M := TBM) ⟨⟨0, none⟩, some (.VTablePointer vt1TB)⟩ dynRef (some corruptTB) =
       .error (.ub wrongTrait) ∧
     checkPtrM (M := TBM) ⟨⟨0, none⟩, some (.VTablePointer vtTooBigTB)⟩ dynUninhab
         (some corruptTB) = .error (.ub sizeOverflow)) := by
  intro vtMissingFn vtTooBig corruptProg corruptAllocs vt0 vt1 vtMissing vtMissingFnPtr
    vtTooBigPtr obj corruptBM corruptTB vt0TB vt1TB vtMissingTB vtMissingFnTB vtTooBigTB objTB
    dynRef dynUninhab rawDyn vtTy oobPtr invalidMeta invalidVt wrongTrait sizeOverflow sanityPanic
    missingProgVt missingLookupVt missingFnPtr nonPtrLookup
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  all_goals ep1_kernel_rfl

set_option maxRecDepth 8192 in
/-- **Unsized structs with `dyn Trait` tails: `head`/`packed_align` layout,
`isize::MAX` overflow, and `PlaceExpr::Field` tail projection**, on both `Mach`
and `MachTB` (with `MachTB.wfLive` preservation):
1. unpacked `#[repr(C)] struct { tag: u8, body: dyn Trait0 }` (`head = ⟨1, 1, none⟩`,
   vtable `(8, 8)` -> `tail_offset = 8`, `size = 16`, `align = 8`): `GetMetadata`,
   `ComputeSize = 16`, `ComputeAlign = 8`, `check_ptr` accepts a 16-byte 8-aligned
   object and rejects 4-aligned or 8-byte allocations, and `PlaceExpr::Field 1`
   advances the address by `tail_offset = 8` while preserving vtable metadata and
   `MachTB.wfLive`;
2. `#[repr(C, packed(2))]` (`packed_align = some 2`, vtable `(8, 8)` ->
   `capped_tail_align = 2`, `align = 2`, `tail_offset = 2`, `size = 10`):
   `ComputeSize = 10`, `ComputeAlign = 2`, `check_ptr` accepts 2-aligned `0x6002`
   and rejects 1-aligned `0x6001`;
3. head-dominated alignment (`head = ⟨8, 16, none⟩`, vtable `(4, 4)` ->
   `align = 16`, `size = 16`): `check_ptr` rejects 8-aligned `0x6008` even though
   the vtable's alignment `4` divides it;
4. `isize::MAX` overflow on `head + vtable.size`: with `vtable.size = 2^63 - 8`
   (which alone fits in `isize::MAX`, so bare `&dyn Trait0` reaches the null check),
   `head = ⟨8, 8, none⟩` yields total size `2^63`: `ComputeSize` stays total, while
   `check_ptr` raises `"Value::Ptr: total size exeeds isize::MAX"`. -/
theorem ep1_vtable_unsized_struct_tail_packed_and_overflow_witness :
    let vtNearMax : Gen.VTable :=
      { trait_name := ep1VtTrait0, size := ⟨9223372036854775800⟩, align := ⟨8⟩, cells := [],
        methods := ⟨[]⟩ }
    let headPair : Gen.TupleHeadLayout := ⟨⟨1⟩, ⟨1⟩, none⟩
    let headPacked : Gen.TupleHeadLayout := ⟨⟨1⟩, ⟨1⟩, some ⟨2⟩⟩
    let headDom : Gen.TupleHeadLayout := ⟨⟨8⟩, ⟨16⟩, none⟩
    let head8 : Gen.TupleHeadLayout := ⟨⟨8⟩, ⟨8⟩, none⟩
    let pairTy : Gen.Type :=
      .Tuple [(⟨0⟩, .Int ep1U8)] headPair (some (.TraitObject ep1VtTrait0))
    let packedTy : Gen.Type :=
      .Tuple [(⟨0⟩, .Int ep1U8)] headPacked (some (.TraitObject ep1VtTrait0))
    let domTy : Gen.Type := .Tuple [] headDom (some (.TraitObject ep1VtTrait1))
    let head8Ty : Gen.Type := .Tuple [] head8 (some (.TraitObject ep1VtTrait0))
    let mkStructPointee (h : Gen.TupleHeadLayout) (t : Gen.TraitName) : Gen.PointeeInfo :=
      { layout := .Tuple h (.TraitObject t), inhabited := true,
        unsafe_cells := .Tuple [] .TraitObject, freeze := true, unpin := true }
    let pairPointee := mkStructPointee headPair ep1VtTrait0
    let pairRef : Gen.PtrType := .Ref .Immutable pairPointee
    let pairBox : Gen.PtrType := .Box pairPointee
    let packedRef : Gen.PtrType := .Ref .Immutable (mkStructPointee headPacked ep1VtTrait0)
    let domRef : Gen.PtrType := .Ref .Immutable (mkStructPointee headDom ep1VtTrait1)
    let head8Ref : Gen.PtrType := .Ref .Immutable (mkStructPointee head8 ep1VtTrait0)
    let dynRef0 : Gen.PtrType := .Ref .Immutable (ep1DynPointee ep1VtTrait0)
    let vtTy0 : Gen.Type := .Ptr (.VTablePtr ep1VtTrait0)
    let vtTy1 : Gen.Type := .Ptr (.VTablePtr ep1VtTrait1)
    let usize : Gen.Type := .Int IntType.usize_ty
    let vt0 : Ptr := ⟨0x4000, some (⟨3⟩, ())⟩
    let vt1 : Ptr := ⟨0x4008, some (⟨4⟩, ())⟩
    let vtNear : Ptr := ⟨0x4010, some (⟨5⟩, ())⟩
    let widePair : Gen.Pointer Prov := ⟨⟨0x6000, some (⟨1⟩, ())⟩, some (.VTablePointer vt0)⟩
    let widePairBytes : List Byte :=
      encodePtrBytes (some (⟨1⟩, ())) 0 [0x00, 0x60, 0, 0, 0, 0, 0, 0] ++
      encodePtrBytes (some (⟨3⟩, ())) 0 [0x00, 0x40, 0, 0, 0, 0, 0, 0]
    let structProg : Gen.Program :=
      { ep1VtProg with
        vtables := ⟨[(⟨⟨0⟩⟩, ep1VTable0), (⟨⟨1⟩⟩, ep1VTable1), (⟨⟨2⟩⟩, vtNearMax)]⟩ }
    let structBM : Mach :=
      { ep1MachBM
          [{ data := List.replicate 8 (.Init 0 none), addr := 0x1000, align := ⟨8⟩,
             kind := .Heap, live := true, extra := () },
           { data := List.replicate 16 (.Init 0 none), addr := 0x6000, align := ⟨16⟩,
             kind := .Heap, live := true, extra := () },
           { data := widePairBytes, addr := 0x2000, align := ⟨8⟩,
             kind := .Stack, live := true, extra := () },
           { data := [], addr := 0x4000, align := ⟨1⟩, kind := .VTable, live := true, extra := () },
           { data := [], addr := 0x4008, align := ⟨1⟩, kind := .VTable, live := true, extra := () },
           { data := [], addr := 0x4010, align := ⟨1⟩, kind := .VTable, live := true, extra := () }]
          [(⟨⟨0⟩⟩, ⟨0x2000, some (⟨2⟩, ())⟩)]
          [(⟨⟨0⟩⟩, .Ptr pairRef)] with
        prog := structProg
        vtable_ptrs := ⟨[(⟨⟨0⟩⟩, vt0), (⟨⟨1⟩⟩, vt1), (⟨⟨2⟩⟩, vtNear)]⟩ }
    let structTB : MachTB := liftMachToTB structBM
    let vt0TB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x4000, some (⟨3⟩, [])⟩
    let vt1TB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x4008, some (⟨4⟩, [])⟩
    let vtNearTB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x4010, some (⟨5⟩, [])⟩
    let widePairTB : Gen.Pointer Gen.TreeBorrowsProvenance :=
      ⟨⟨0x6000, some (⟨1⟩, [])⟩, some (.VTablePointer vt0TB)⟩
    let fieldTailExpr : Gen.PlaceExpr := .Field (.Deref (.Load (.Local ⟨⟨0⟩⟩)) pairTy) 1
    let unaligned := "Value::Ptr: unaligned safe pointer"
    let nonDeref := "Value::Ptr: non-dereferenceable safe pointer"
    let nullPtr := "Value::Ptr: null safe pointer"
    let sizeOverflow := "Value::Ptr: total size exeeds isize::MAX"
    -- `Mach`
    (evalUnOp .GetMetadata (.Ptr widePair, .Ptr pairRef) (some structBM) =
       .ok (.Ptr (ThinPointer.widen vt0 none), vtTy0) ∧
     evalUnOp (.ComputeSize pairTy) (.Ptr (ThinPointer.widen vt0 none), vtTy0) (some structBM) =
       .ok (.Int 16, usize) ∧
     evalUnOp (.ComputeAlign pairTy) (.Ptr (ThinPointer.widen vt0 none), vtTy0) (some structBM) =
       .ok (.Int 8, usize) ∧
     checkPtr widePair pairRef (some structBM) = .ok () ∧
     checkPtr widePair pairBox (some structBM) = .ok () ∧
     checkPtr ⟨⟨0x6004, some (⟨1⟩, ())⟩, some (.VTablePointer vt0)⟩ pairRef (some structBM) =
       .error (.ub unaligned) ∧
     checkPtr ⟨⟨0x1000, some (⟨0⟩, ())⟩, some (.VTablePointer vt0)⟩ pairRef (some structBM) =
       .error (.ub nonDeref) ∧
     evalUnOp (.ComputeSize packedTy) (.Ptr (ThinPointer.widen vt0 none), vtTy0) (some structBM) =
       .ok (.Int 10, usize) ∧
     evalUnOp (.ComputeAlign packedTy) (.Ptr (ThinPointer.widen vt0 none), vtTy0) (some structBM) =
       .ok (.Int 2, usize) ∧
     checkPtr ⟨⟨0x6002, some (⟨1⟩, ())⟩, some (.VTablePointer vt0)⟩ packedRef (some structBM) =
       .ok () ∧
     checkPtr ⟨⟨0x6001, some (⟨1⟩, ())⟩, some (.VTablePointer vt0)⟩ packedRef (some structBM) =
       .error (.ub unaligned) ∧
     evalUnOp (.ComputeSize domTy) (.Ptr (ThinPointer.widen vt1 none), vtTy1) (some structBM) =
       .ok (.Int 16, usize) ∧
     evalUnOp (.ComputeAlign domTy) (.Ptr (ThinPointer.widen vt1 none), vtTy1) (some structBM) =
       .ok (.Int 16, usize) ∧
     checkPtr ⟨⟨0x6008, some (⟨1⟩, ())⟩, some (.VTablePointer vt1)⟩ domRef (some structBM) =
       .error (.ub unaligned) ∧
     checkPtr ⟨⟨0, none⟩, some (.VTablePointer vtNear)⟩ dynRef0 (some structBM) =
       .error (.ub nullPtr) ∧
     evalUnOp (.ComputeSize head8Ty) (.Ptr (ThinPointer.widen vtNear none), vtTy0)
         (some structBM) = .ok (.Int 9223372036854775808, usize) ∧
     checkPtr ⟨⟨0, none⟩, some (.VTablePointer vtNear)⟩ head8Ref (some structBM) =
       .error (.ub sizeOverflow) ∧
     (∃ m1, evalPlace structBM fieldTailExpr =
       .ok (({ ptr := ⟨⟨0x6008, some (⟨1⟩, ())⟩, some (.VTablePointer vt0)⟩, aligned := true },
         .TraitObject ep1VtTrait0), m1))) ∧
    -- `MachTB` (+ `MachTB.wfLive`)
    (evalUnOpM (M := TBM) .GetMetadata (.Ptr widePairTB, .Ptr pairRef) (some structTB) =
       .ok (.Ptr (ThinPointer.widen vt0TB none), vtTy0) ∧
     evalUnOpM (M := TBM) (.ComputeSize pairTy) (.Ptr (ThinPointer.widen vt0TB none), vtTy0)
         (some structTB) = .ok (.Int 16, usize) ∧
     evalUnOpM (M := TBM) (.ComputeAlign pairTy) (.Ptr (ThinPointer.widen vt0TB none), vtTy0)
         (some structTB) = .ok (.Int 8, usize) ∧
     checkPtrM (M := TBM) widePairTB pairRef (some structTB) = .ok () ∧
     checkPtrM (M := TBM) widePairTB pairBox (some structTB) = .ok () ∧
     checkPtrM (M := TBM) ⟨⟨0x6004, some (⟨1⟩, [])⟩, some (.VTablePointer vt0TB)⟩ pairRef
         (some structTB) = .error (.ub unaligned) ∧
     checkPtrM (M := TBM) ⟨⟨0x1000, some (⟨0⟩, [])⟩, some (.VTablePointer vt0TB)⟩ pairRef
         (some structTB) = .error (.ub nonDeref) ∧
     evalUnOpM (M := TBM) (.ComputeSize packedTy) (.Ptr (ThinPointer.widen vt0TB none), vtTy0)
         (some structTB) = .ok (.Int 10, usize) ∧
     evalUnOpM (M := TBM) (.ComputeAlign packedTy) (.Ptr (ThinPointer.widen vt0TB none), vtTy0)
         (some structTB) = .ok (.Int 2, usize) ∧
     checkPtrM (M := TBM) ⟨⟨0x6002, some (⟨1⟩, [])⟩, some (.VTablePointer vt0TB)⟩ packedRef
         (some structTB) = .ok () ∧
     checkPtrM (M := TBM) ⟨⟨0x6001, some (⟨1⟩, [])⟩, some (.VTablePointer vt0TB)⟩ packedRef
         (some structTB) = .error (.ub unaligned) ∧
     evalUnOpM (M := TBM) (.ComputeSize domTy) (.Ptr (ThinPointer.widen vt1TB none), vtTy1)
         (some structTB) = .ok (.Int 16, usize) ∧
     evalUnOpM (M := TBM) (.ComputeAlign domTy) (.Ptr (ThinPointer.widen vt1TB none), vtTy1)
         (some structTB) = .ok (.Int 16, usize) ∧
     checkPtrM (M := TBM) ⟨⟨0x6008, some (⟨1⟩, [])⟩, some (.VTablePointer vt1TB)⟩ domRef
         (some structTB) = .error (.ub unaligned) ∧
     checkPtrM (M := TBM) ⟨⟨0, none⟩, some (.VTablePointer vtNearTB)⟩ dynRef0 (some structTB) =
       .error (.ub nullPtr) ∧
     evalUnOpM (M := TBM) (.ComputeSize head8Ty) (.Ptr (ThinPointer.widen vtNearTB none), vtTy0)
         (some structTB) = .ok (.Int 9223372036854775808, usize) ∧
     checkPtrM (M := TBM) ⟨⟨0, none⟩, some (.VTablePointer vtNearTB)⟩ head8Ref (some structTB) =
       .error (.ub sizeOverflow) ∧
     (∃ m1, evalPlaceM structTB fieldTailExpr =
       .ok (({ ptr := ⟨⟨0x6008, some (⟨1⟩, [])⟩, some (.VTablePointer vt0TB)⟩, aligned := true },
         .TraitObject ep1VtTrait0), m1) ∧ MachTB.wfLive m1)) := by
  intro vtNearMax headPair headPacked headDom head8 pairTy packedTy domTy head8Ty mkStructPointee
    pairPointee pairRef pairBox packedRef domRef head8Ref dynRef0 vtTy0 vtTy1 usize vt0 vt1 vtNear
    widePair widePairBytes structProg structBM structTB vt0TB vt1TB vtNearTB widePairTB
    fieldTailExpr unaligned nonDeref nullPtr sizeOverflow
  have hFull : TupleHeadLayout.full_size_and_align head8 vtNearMax.size vtNearMax.align =
      (⟨9223372036854775808⟩, ⟨8⟩) := by
    dsimp only [head8, vtNearMax, TupleHeadLayout.full_size_and_align,
      TupleHeadLayout.capped_tail_align, TupleHeadLayout.tail_offset, Size.align_to]
    exact Prod.ext (congrArg Size.mk (by simp only [Nat.max_self])) rfl
  have hOv : inBounds ((TupleHeadLayout.full_size_and_align head8 vtNearMax.size
      vtNearMax.align).1.bytes : Int) .Signed x86_64.PTR_SIZE = false := by
    rw [hFull]
    ep1_kernel_rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · have hvt : vtableLookup structBM vtNear = .ok vtNearMax := by ep1_kernel_rfl
    have h := (evalUnOp_tuple_traitObject_size_align structBM vtNear [] head8 ep1VtTrait0 vtTy0
      vtNearMax hvt).1
    rw [hFull] at h
    exact h
  · have hvt : vtableFromPtr structBM vtNear = .ok vtNearMax := by ep1_kernel_rfl
    exact checkPtr_tuple_traitObject_size_overflow_ub ⟨0, none⟩ vtNear
      (Gen.PtrType.Ref .Immutable) (mkStructPointee head8 ep1VtTrait0) head8 ep1VtTrait0
      structBM vtNearMax (Or.inl ⟨.Immutable, rfl⟩) rfl (by ep1_kernel_rfl) (by ep1_kernel_rfl)
      hvt rfl hOv
  · have hBM : Prod.fst <$> evalPlace structBM fieldTailExpr =
        .ok ({ ptr := ⟨⟨0x6008, some (⟨1⟩, ())⟩, some (.VTablePointer vt0)⟩, aligned := true },
          .TraitObject ep1VtTrait0) := by ep1_kernel_rfl
    exact ep1_ok_of_map_fst hBM
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · have hvt : vtableLookupM structTB vtNearTB = .ok vtNearMax := by ep1_kernel_rfl
    have h := (evalUnOpM_tuple_traitObject_size_align (M := TBM) structTB vtNearTB [] head8
      ep1VtTrait0 vtTy0 vtNearMax hvt).1
    rw [hFull] at h
    exact h
  · have hvt : vtableFromPtrM structTB vtNearTB = .ok vtNearMax := by ep1_kernel_rfl
    exact checkPtrM_tuple_traitObject_size_overflow_ub (M := TBM) ⟨0, none⟩ vtNearTB
      (Gen.PtrType.Ref .Immutable) (mkStructPointee head8 ep1VtTrait0) head8 ep1VtTrait0
      structTB vtNearMax (Or.inl ⟨.Immutable, rfl⟩) rfl (by ep1_kernel_rfl) (by ep1_kernel_rfl)
      hvt rfl hOv
  · have hTB : Prod.fst <$> evalPlaceM structTB fieldTailExpr =
        .ok ({ ptr := ⟨⟨0x6008, some (⟨1⟩, [])⟩, some (.VTablePointer vt0TB)⟩, aligned := true },
          .TraitObject ep1VtTrait0) := by ep1_kernel_rfl
    obtain ⟨m1, hm1⟩ := ep1_ok_of_map_fst hTB
    exact ⟨m1, hm1, evalPlaceM_tb_wfLive _ (liftMachToTB_wfLive structBM) hm1⟩

set_option maxRecDepth 8192 in
/-- **Tree Borrows (`MachTB`) safe-pointer retag, `vtable.cells` (`UnsafeCell`),
`Disabled` vs `dereferenceable`, and Strong/Weak protectors on `&dyn Trait`,
`&mut dyn Trait`, and `Box<dyn Trait>`** (with `MachTB.wfLive` preservation):
1. `&dyn Trait0` with `vtable.cells = [(0, 4)]` inside an 8-byte object:
   `Statement::Validate` retags via `ReborrowSettings::new` and
   `UnsafeCellStrategy::freeze_mask` into `[Cell × 4, Frozen × 4]`; writing to
   bytes `[0..4)` (`UnsafeCell`) succeeds on `MachTB` (preserving `MachTB.wfLive`),
   while writing to bytes `[4..8)` raises `"Tree Borrows: local write of Frozen reference"`
   (whereas `Mach` / `BasicMemory` allows both writes);
2. unprotected `&mut dyn Trait0`: a foreign write through root `[]` to `[4..8)`
   disables child `[0]` on `[4..8)` while keeping `[0..4)` `ReservedIm`;
   `checkPtrM` (`TreeBorrowsMemory::dereferenceable`, which checks bounds/liveness
   only) still returns `.ok ()` and reading `[0..4)` succeeds, whereas reading
   `[4..8)` or re-running `Statement::Validate` raises
   `"Tree Borrows: local read of Disabled reference"`;
3. `fn_entry = true` active protectors: `&mut dyn Trait0` installs
   `Protected::Strong` (blocking both foreign writes and `deallocate` with
   `"Tree Borrows: deallocating strongly protected allocation"`), whereas
   `Box<dyn Trait0>` installs `Protected::Weak` (still blocking foreign writes,
   while permitting self-deallocation and `end_call` protector release with
   `TreeBorrowsMemory.wfLive` preserved). -/
theorem ep1_vtable_dyn_tree_borrows_retag_protector_and_cells_witness :
    let vtCells : Gen.VTable :=
      { trait_name := ep1VtTrait0, size := ⟨8⟩, align := ⟨8⟩, cells := [(⟨0⟩, ⟨4⟩)],
        methods := ⟨[]⟩ }
    let vtProg : Gen.Program :=
      { functions := ⟨[]⟩, start := ⟨⟨0⟩⟩, globals := ⟨[]⟩,
        traits := ⟨[(ep1VtTrait0, ⟨[]⟩)]⟩, vtables := ⟨[(⟨⟨0⟩⟩, vtCells)]⟩ }
    let dynPointee := ep1DynPointee ep1VtTrait0
    let dynRef : Gen.PtrType := .Ref .Immutable dynPointee
    let dynMut : Gen.PtrType := .Ref .Mutable dynPointee
    let dynBox : Gen.PtrType := .Box dynPointee
    let u32PairTy : Gen.Type :=
      .Tuple [(⟨0⟩, .Int ep1U32), (⟨4⟩, .Int ep1U32)] ⟨⟨8⟩, ⟨4⟩, none⟩ none
    let dataPtrBytes : List Byte :=
      encodePtrBytes (some (⟨0⟩, ())) 0 [0x00, 0x10, 0, 0, 0, 0, 0, 0]
    let vtPtrBytes : List Byte :=
      encodePtrBytes (some (⟨3⟩, ())) 0 [0x00, 0x40, 0, 0, 0, 0, 0, 0]
    let wideBytes : List Byte := dataPtrBytes ++ vtPtrBytes
    let vt0 : Ptr := ⟨0x4000, some (⟨3⟩, ())⟩
    let vt0TB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x4000, some (⟨3⟩, [])⟩
    let mkBM (ptrTy : Gen.PtrType) : Mach :=
      { ep1MachBM
          [{ data := List.replicate 8 (.Init 0 none), addr := 0x1000, align := ⟨8⟩,
             kind := .Heap, live := true, extra := () },
           { data := wideBytes, addr := 0x2000, align := ⟨8⟩,
             kind := .Stack, live := true, extra := () },
           { data := dataPtrBytes, addr := 0x2100, align := ⟨8⟩,
             kind := .Stack, live := true, extra := () },
           { data := [], addr := 0x4000, align := ⟨1⟩,
             kind := .VTable, live := true, extra := () }]
          [(⟨⟨1⟩⟩, ⟨0x2000, some (⟨1⟩, ())⟩), (⟨⟨2⟩⟩, ⟨0x2100, some (⟨2⟩, ())⟩)]
          [(⟨⟨0⟩⟩, .Int ep1U32), (⟨⟨1⟩⟩, .Ptr ptrTy), (⟨⟨2⟩⟩, .Ptr (.Raw .None))] with
        prog := vtProg
        vtable_ptrs := ⟨[(⟨⟨0⟩⟩, vt0)]⟩ }
    let mkTB (ptrTy : Gen.PtrType) : MachTB := liftMachToTB (mkBM ptrTy)
    let dynFieldPlace (idx : Int) : Gen.PlaceExpr :=
      .Field (.Deref (.UnOp .GetThinPointer (.Load (.Local ⟨⟨1⟩⟩))) u32PairTy) idx
    let rootFieldPlace (idx : Int) : Gen.PlaceExpr :=
      .Field (.Deref (.Load (.Local ⟨⟨2⟩⟩)) u32PairTy) idx
    let stmtWriteCell : Gen.Statement :=
      .Assign (dynFieldPlace 0) (.Constant (.Int 42) (.Int ep1U32))
    let stmtWriteFrozen : Gen.Statement :=
      .Assign (dynFieldPlace 1) (.Constant (.Int 99) (.Int ep1U32))
    let stmtForeignWrite1 : Gen.Statement :=
      .Assign (rootFieldPlace 1) (.Constant (.Int 7) (.Int ep1U32))
    -- 1. `&dyn Trait0` with `vtable.cells = [(0, 4)]`: `MachTB` vs `Mach`
    (∃ m1 m2,
      evalStatementM (mkTB dynRef) (.Validate (.Local ⟨⟨1⟩⟩) false) = .ok m1 ∧
      evalStatementM m1 stmtWriteCell = .ok m2 ∧
      MachTB.wfLive m2 ∧
      evalStatementM m2 stmtWriteFrozen =
        .error (.ub "Tree Borrows: local write of Frozen reference")) ∧
    (∃ m1 m2 m3,
      evalStatement (mkBM dynRef) (.Validate (.Local ⟨⟨1⟩⟩) false) = .ok m1 ∧
      evalStatement m1 stmtWriteCell = .ok m2 ∧
      evalStatement m2 stmtWriteFrozen = .ok m3) ∧
    -- 2. unprotected `&mut dyn Trait0`: `Disabled` vs `dereferenceable`
    (∃ m1 m2 m3,
      evalStatementM (mkTB dynMut) (.Validate (.Local ⟨⟨1⟩⟩) false) = .ok m1 ∧
      evalStatementM m1 stmtForeignWrite1 = .ok m2 ∧
      MachTB.wfLive m2 ∧
      checkPtrM (M := TBM)
        ⟨⟨0x1000, some (⟨0⟩, [0])⟩, some (.VTablePointer vt0TB)⟩ dynMut (some m2) = .ok () ∧
      evalValueM m2 (.Load (dynFieldPlace 0)) = .ok ((.Int 0, .Int ep1U32), m3) ∧
      MachTB.wfLive m3 ∧
      evalValueM m2 (.Load (dynFieldPlace 1)) =
        .error (.ub "Tree Borrows: local read of Disabled reference") ∧
      evalStatementM m2 (.Validate (.Local ⟨⟨1⟩⟩) false) =
        .error (.ub "Tree Borrows: local read of Disabled reference")) ∧
    -- 3a. `&mut dyn Trait0` (`fn_entry = true`, `Protected::Strong`)
    (∃ m1,
      evalStatementM (mkTB dynMut) (.Validate (.Local ⟨⟨1⟩⟩) true) = .ok m1 ∧
      MachTB.wfLive m1 ∧
      evalStatementM m1 stmtForeignWrite1 =
        .error (.ub "Tree Borrows: foreign write of protected Reserved reference which had a local read") ∧
      TreeBorrowsMemory.deallocate m1.mem.memory ⟨0x1000, some (⟨0⟩, [0])⟩ .Heap ⟨8⟩ ⟨8⟩ =
        .error (.ub "Tree Borrows: deallocating strongly protected allocation")) ∧
    -- 3b. `Box<dyn Trait0>` (`fn_entry = true`, `Protected::Weak`)
    (∃ m1 tbm2 tbm3,
      evalStatementM (mkTB dynBox) (.Validate (.Local ⟨⟨1⟩⟩) true) = .ok m1 ∧
      MachTB.wfLive m1 ∧
      evalStatementM m1 stmtForeignWrite1 =
        .error (.ub "Tree Borrows: foreign write of protected Reserved reference which had a local read") ∧
      TreeBorrowsMemory.deallocate m1.mem.memory ⟨0x1000, some (⟨0⟩, [0])⟩ .Heap ⟨8⟩ ⟨8⟩ =
        .ok tbm2 ∧
      TreeBorrowsMemory.wfLive tbm2 ∧
      tbm2.mem.allocations[0]?.map Gen.Allocation.live = some false ∧
      TreeBorrowsMemory.end_call tbm2 { protectors := [(⟨0⟩, [0])] } = .ok tbm3 ∧
      TreeBorrowsMemory.wfLive tbm3) := by
  intro vtCells vtProg dynPointee dynRef dynMut dynBox u32PairTy dataPtrBytes vtPtrBytes wideBytes
    vt0 vt0TB mkBM mkTB dynFieldPlace rootFieldPlace stmtWriteCell stmtWriteFrozen
    stmtForeignWrite1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hseq :
        (do
          let m1 ← evalStatementM (mkTB dynRef) (.Validate (.Local ⟨⟨1⟩⟩) false)
          let m2 ← evalStatementM m1 stmtWriteCell
          pure (evalStatementM m2 stmtWriteFrozen)) =
          .ok (.error (.ub "Tree Borrows: local write of Frozen reference")) := by
      ep1_kernel_rfl
    obtain ⟨m1, hm1, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨m2, hm2, hseq⟩ := ep1_bind_ok hseq
    have hfrozen := ep1_pure_ok hseq
    have hwf1 := evalStatementM_tb_wfLive (liftMachToTB_wfLive (mkBM dynRef)) hm1
    have hwf2 := evalStatementM_tb_wfLive hwf1 hm2
    exact ⟨m1, m2, hm1, hm2, hwf2, hfrozen⟩
  · have hseq :
        (do
          let m1 ← evalStatement (mkBM dynRef) (.Validate (.Local ⟨⟨1⟩⟩) false)
          let m2 ← evalStatement m1 stmtWriteCell
          let _m3 ← evalStatement m2 stmtWriteFrozen
          pure ()) = .ok () := by
      ep1_kernel_rfl
    obtain ⟨m1, hm1, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨m2, hm2, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨m3, hm3, _⟩ := ep1_bind_ok hseq
    exact ⟨m1, m2, m3, hm1, hm2, hm3⟩
  · have hseq :
        (do
          let m1 ← evalStatementM (mkTB dynMut) (.Validate (.Local ⟨⟨1⟩⟩) false)
          let m2 ← evalStatementM m1 stmtForeignWrite1
          let (v0, _m3) ← evalValueM m2 (.Load (dynFieldPlace 0))
          pure (v0,
            checkPtrM (M := TBM)
              ⟨⟨0x1000, some (⟨0⟩, [0])⟩, some (.VTablePointer vt0TB)⟩ dynMut (some m2),
            evalValueM m2 (.Load (dynFieldPlace 1)),
            evalStatementM m2 (.Validate (.Local ⟨⟨1⟩⟩) false))) =
          .ok ((.Int 0, .Int ep1U32), .ok (),
            .error (.ub "Tree Borrows: local read of Disabled reference"),
            .error (.ub "Tree Borrows: local read of Disabled reference")) := by
      ep1_kernel_rfl
    obtain ⟨m1, hm1, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨m2, hm2, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨⟨v0, m3⟩, hm3, hseq⟩ := ep1_bind_ok hseq
    have hp := ep1_pure_ok hseq
    obtain ⟨hv0, hrest⟩ := Prod.mk.inj hp
    obtain ⟨hchk, hrest⟩ := Prod.mk.inj hrest
    obtain ⟨hload1, hval2⟩ := Prod.mk.inj hrest
    rw [hv0] at hm3
    have hwf1 := evalStatementM_tb_wfLive (liftMachToTB_wfLive (mkBM dynMut)) hm1
    have hwf2 := evalStatementM_tb_wfLive hwf1 hm2
    have hwf3 := evalValueM_tb_wfLive _ hwf2 hm3
    exact ⟨m1, m2, m3, hm1, hm2, hwf2, hchk, hm3, hwf3, hload1, hval2⟩
  · have hseq :
        (do
          let m1 ← evalStatementM (mkTB dynMut) (.Validate (.Local ⟨⟨1⟩⟩) true)
          pure (evalStatementM m1 stmtForeignWrite1,
            TreeBorrowsMemory.deallocate m1.mem.memory ⟨0x1000, some (⟨0⟩, [0])⟩ .Heap ⟨8⟩ ⟨8⟩)) =
          .ok (.error (.ub "Tree Borrows: foreign write of protected Reserved reference which had a local read"),
            .error (.ub "Tree Borrows: deallocating strongly protected allocation")) := by
      ep1_kernel_rfl
    obtain ⟨m1, hm1, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨hfw, hdealloc⟩ := Prod.mk.inj (ep1_pure_ok hseq)
    have hwf1 := evalStatementM_tb_wfLive (liftMachToTB_wfLive (mkBM dynMut)) hm1
    exact ⟨m1, hm1, hwf1, hfw, hdealloc⟩
  · have hseq :
        (do
          let m1 ← evalStatementM (mkTB dynBox) (.Validate (.Local ⟨⟨1⟩⟩) true)
          let tbm2 ← TreeBorrowsMemory.deallocate m1.mem.memory
            ⟨0x1000, some (⟨0⟩, [0])⟩ .Heap ⟨8⟩ ⟨8⟩
          let _tbm3 ← TreeBorrowsMemory.end_call tbm2 { protectors := [(⟨0⟩, [0])] }
          pure (evalStatementM m1 stmtForeignWrite1,
            tbm2.mem.allocations[0]?.map Gen.Allocation.live)) =
          .ok (.error (.ub "Tree Borrows: foreign write of protected Reserved reference which had a local read"),
            some false) := by
      ep1_kernel_rfl
    obtain ⟨m1, hm1, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨tbm2, htbm2, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨tbm3, htbm3, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨hfw, hdead⟩ := Prod.mk.inj (ep1_pure_ok hseq)
    have hwf1 := evalStatementM_tb_wfLive (liftMachToTB_wfLive (mkBM dynBox)) hm1
    have hwf2 := TreeBorrowsMemory.deallocate_wfLive hwf1 htbm2
    have hwf3 := TreeBorrowsMemory.end_call_wfLive hwf2 htbm3
    exact ⟨m1, tbm2, tbm3, hm1, hwf1, hfw, htbm2, hwf2, hdead, htbm3, hwf3⟩

set_option maxRecDepth 8192 in
/-- **ZST `dyn Trait` (`vtable.size = 0`, `vtable.align = 8`), uninhabited
`PointeeInfo.inhabited = false` precedence, and safe `&dyn Trait`
`PlaceExpr::Deref`** on both `Mach` and `MachTB` (with `MachTB.wfLive`):
1. ZST `dyn Trait0` (`size = 0`, `align = 8`, `cells = []`) across `&dyn Trait0`,
   `&mut dyn Trait0`, and `Box<dyn Trait0>` with a dead data allocation:
   * dangling provenance-free aligned `⟨0x8, none⟩` passes `checkPtr[M]`,
     `Statement::Validate` (`fn_entry = false` and `true`, preserving
     `MachTB.wfLive` and pushing zero Tree Borrows protectors), and safe
     `PlaceExpr::Deref` (`aligned = true`);
   * null `⟨0x0, none⟩` raises `"Value::Ptr: null safe pointer"`;
   * misaligned `⟨0x4, none⟩` raises `"Value::Ptr: unaligned safe pointer"`;
2. `PointeeInfo.inhabited = false` precedence across `&dyn Trait0`,
   `&mut dyn Trait0`, and `Box<dyn Trait0>`:
   * aligned non-null ZST `⟨0x8, none⟩` raises
     `"Value::Ptr: safe pointer to uninhabited type"`;
   * misaligned `⟨0x4, none⟩` raises `"Value::Ptr: unaligned safe pointer"`
     (alignment precedes inhabitedness) and `⟨0x0, none⟩` raises
     `"Value::Ptr: null safe pointer"` (non-null precedes alignment);
   * non-ZST (`size = 8`) non-dereferenceable `⟨0x1000, none⟩` still raises
     `"Value::Ptr: safe pointer to uninhabited type"` (inhabitedness precedes
     `Memory::dereferenceable`);
3. `PlaceExpr::Deref` on non-ZST safe `&dyn Trait0` (`size = 8`, `align = 8`):
   succeeds with `aligned = true` (and `MachTB.wfLive`) on a live 8-byte
   allocation, and raises `"Value::Ptr: non-dereferenceable safe pointer"` when
   the backing allocation is dead. -/
theorem ep1_vtable_zst_uninhabited_and_deref_witness :
    let vtZst : Gen.VTable :=
      { trait_name := ep1VtTrait0, size := ⟨0⟩, align := ⟨8⟩, cells := [], methods := ⟨[]⟩ }
    let vtSize8 : Gen.VTable :=
      { trait_name := ep1VtTrait0, size := ⟨8⟩, align := ⟨8⟩, cells := [], methods := ⟨[]⟩ }
    let zstProg : Gen.Program :=
      { functions := ⟨[]⟩, start := ⟨⟨0⟩⟩, globals := ⟨[]⟩,
        traits := ⟨[(ep1VtTrait0, ⟨[]⟩)]⟩,
        vtables := ⟨[(⟨⟨0⟩⟩, vtZst), (⟨⟨1⟩⟩, vtSize8)]⟩ }
    let dynPointee := ep1DynPointee ep1VtTrait0
    let uninhPointee : Gen.PointeeInfo := { dynPointee with inhabited := false }
    let dynRef : Gen.PtrType := .Ref .Immutable dynPointee
    let dynMut : Gen.PtrType := .Ref .Mutable dynPointee
    let dynBox : Gen.PtrType := .Box dynPointee
    let uninhRef : Gen.PtrType := .Ref .Immutable uninhPointee
    let uninhMut : Gen.PtrType := .Ref .Mutable uninhPointee
    let uninhBox : Gen.PtrType := .Box uninhPointee
    let vtZstPtr : Ptr := ⟨0x4000, some (⟨2⟩, ())⟩
    let vt8Ptr : Ptr := ⟨0x4008, some (⟨3⟩, ())⟩
    let vtZstTB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x4000, some (⟨2⟩, [])⟩
    let vt8TB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x4008, some (⟨3⟩, [])⟩
    let zstWideBytes : List Byte :=
      encodePtrBytes none 0 [0x08, 0, 0, 0, 0, 0, 0, 0] ++
      encodePtrBytes (some (⟨2⟩, ())) 0 [0x00, 0x40, 0, 0, 0, 0, 0, 0]
    let liveWideBytes : List Byte :=
      encodePtrBytes (some (⟨0⟩, ())) 0 [0x00, 0x10, 0, 0, 0, 0, 0, 0] ++
      encodePtrBytes (some (⟨3⟩, ())) 0 [0x08, 0x40, 0, 0, 0, 0, 0, 0]
    let mkBM (ptrTy : Gen.PtrType) (dataLive : Bool) (local1Bytes : List Byte) : Mach :=
      { ep1MachBM
          [{ data := List.replicate 8 (.Init 0 none), addr := 0x1000, align := ⟨8⟩,
             kind := .Heap, live := dataLive, extra := () },
           { data := local1Bytes, addr := 0x2000, align := ⟨8⟩,
             kind := .Stack, live := true, extra := () },
           { data := [], addr := 0x4000, align := ⟨1⟩, kind := .VTable, live := true, extra := () },
           { data := [], addr := 0x4008, align := ⟨1⟩, kind := .VTable, live := true, extra := () }]
          [(⟨⟨1⟩⟩, ⟨0x2000, some (⟨1⟩, ())⟩)]
          [(⟨⟨1⟩⟩, .Ptr ptrTy)] with
        prog := zstProg
        vtable_ptrs := ⟨[(⟨⟨0⟩⟩, vtZstPtr), (⟨⟨1⟩⟩, vt8Ptr)]⟩ }
    let mkTB (ptrTy : Gen.PtrType) (dataLive : Bool) (local1Bytes : List Byte) : MachTB :=
      liftMachToTB (mkBM ptrTy dataLive local1Bytes)
    let bmZst := mkBM dynRef false zstWideBytes
    let tbZst := mkTB dynRef false zstWideBytes
    let derefExpr : Gen.PlaceExpr := .Deref (.Load (.Local ⟨⟨1⟩⟩)) (.TraitObject ep1VtTrait0)
    let nullUb := "Value::Ptr: null safe pointer"
    let alignUb := "Value::Ptr: unaligned safe pointer"
    let uninhUb := "Value::Ptr: safe pointer to uninhabited type"
    let nonDerefUb := "Value::Ptr: non-dereferenceable safe pointer"
    -- 1a. `Mach`: ZST `checkPtr`, `Validate`, and `PlaceExpr::Deref`
    (checkPtr ⟨⟨0x8, none⟩, some (.VTablePointer vtZstPtr)⟩ dynRef (some bmZst) = .ok () ∧
     checkPtr ⟨⟨0x8, none⟩, some (.VTablePointer vtZstPtr)⟩ dynMut (some bmZst) = .ok () ∧
     checkPtr ⟨⟨0x8, none⟩, some (.VTablePointer vtZstPtr)⟩ dynBox (some bmZst) = .ok () ∧
     checkPtr ⟨⟨0x0, none⟩, some (.VTablePointer vtZstPtr)⟩ dynRef (some bmZst) = .error (.ub nullUb) ∧
     checkPtr ⟨⟨0x0, none⟩, some (.VTablePointer vtZstPtr)⟩ dynMut (some bmZst) = .error (.ub nullUb) ∧
     checkPtr ⟨⟨0x0, none⟩, some (.VTablePointer vtZstPtr)⟩ dynBox (some bmZst) = .error (.ub nullUb) ∧
     checkPtr ⟨⟨0x4, none⟩, some (.VTablePointer vtZstPtr)⟩ dynRef (some bmZst) = .error (.ub alignUb) ∧
     checkPtr ⟨⟨0x4, none⟩, some (.VTablePointer vtZstPtr)⟩ dynMut (some bmZst) = .error (.ub alignUb) ∧
     checkPtr ⟨⟨0x4, none⟩, some (.VTablePointer vtZstPtr)⟩ dynBox (some bmZst) = .error (.ub alignUb) ∧
     (∃ m1, evalStatement (mkBM dynRef false zstWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) true) = .ok m1) ∧
     (∃ m1, evalStatement (mkBM dynMut false zstWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) true) = .ok m1) ∧
     (∃ m1, evalStatement (mkBM dynBox false zstWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) true) = .ok m1) ∧
     (∃ m1, evalPlace bmZst derefExpr =
       .ok (({ ptr := ⟨⟨0x8, none⟩, some (.VTablePointer vtZstPtr)⟩, aligned := true },
         .TraitObject ep1VtTrait0), m1))) ∧
    -- 1b. `MachTB`: ZST `checkPtrM`, `Validate` (`fn_entry = false/true`, 0 protectors), `Deref`
    (checkPtrM (M := TBM) ⟨⟨0x8, none⟩, some (.VTablePointer vtZstTB)⟩ dynRef (some tbZst) = .ok () ∧
     checkPtrM (M := TBM) ⟨⟨0x8, none⟩, some (.VTablePointer vtZstTB)⟩ dynMut (some tbZst) = .ok () ∧
     checkPtrM (M := TBM) ⟨⟨0x8, none⟩, some (.VTablePointer vtZstTB)⟩ dynBox (some tbZst) = .ok () ∧
     checkPtrM (M := TBM) ⟨⟨0x0, none⟩, some (.VTablePointer vtZstTB)⟩ dynRef (some tbZst) =
       .error (.ub nullUb) ∧
     checkPtrM (M := TBM) ⟨⟨0x0, none⟩, some (.VTablePointer vtZstTB)⟩ dynMut (some tbZst) =
       .error (.ub nullUb) ∧
     checkPtrM (M := TBM) ⟨⟨0x0, none⟩, some (.VTablePointer vtZstTB)⟩ dynBox (some tbZst) =
       .error (.ub nullUb) ∧
     checkPtrM (M := TBM) ⟨⟨0x4, none⟩, some (.VTablePointer vtZstTB)⟩ dynRef (some tbZst) =
       .error (.ub alignUb) ∧
     checkPtrM (M := TBM) ⟨⟨0x4, none⟩, some (.VTablePointer vtZstTB)⟩ dynMut (some tbZst) =
       .error (.ub alignUb) ∧
     checkPtrM (M := TBM) ⟨⟨0x4, none⟩, some (.VTablePointer vtZstTB)⟩ dynBox (some tbZst) =
       .error (.ub alignUb) ∧
     (∃ m1, evalStatementM (mkTB dynRef false zstWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) true) = .ok m1 ∧
       MachTB.wfLive m1 ∧
       m1.threads[0]?.bind (fun t : Gen.Thread TBM =>
         t.stack.getLast?.map (fun f : Gen.StackFrame TBM => f.extra.protectors)) = some []) ∧
     (∃ m1, evalStatementM (mkTB dynMut false zstWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) true) = .ok m1 ∧
       MachTB.wfLive m1 ∧
       m1.threads[0]?.bind (fun t : Gen.Thread TBM =>
         t.stack.getLast?.map (fun f : Gen.StackFrame TBM => f.extra.protectors)) = some []) ∧
     (∃ m1, evalStatementM (mkTB dynBox false zstWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) false) = .ok m1 ∧
       MachTB.wfLive m1) ∧
     (∃ m1, evalStatementM (mkTB dynBox false zstWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) true) = .ok m1 ∧
       MachTB.wfLive m1 ∧
       m1.threads[0]?.bind (fun t : Gen.Thread TBM =>
         t.stack.getLast?.map (fun f : Gen.StackFrame TBM => f.extra.protectors)) = some []) ∧
     (∃ m1, evalPlaceM tbZst derefExpr =
       .ok (({ ptr := ⟨⟨0x8, none⟩, some (.VTablePointer vtZstTB)⟩, aligned := true },
         .TraitObject ep1VtTrait0), m1) ∧ MachTB.wfLive m1)) ∧
    -- 2. Uninhabited (`PointeeInfo.inhabited = false`) & error precedence (`Mach` & `MachTB`)
    (checkPtr ⟨⟨0x8, none⟩, some (.VTablePointer vtZstPtr)⟩ uninhRef (some bmZst) = .error (.ub uninhUb) ∧
     checkPtr ⟨⟨0x8, none⟩, some (.VTablePointer vtZstPtr)⟩ uninhMut (some bmZst) = .error (.ub uninhUb) ∧
     checkPtr ⟨⟨0x8, none⟩, some (.VTablePointer vtZstPtr)⟩ uninhBox (some bmZst) = .error (.ub uninhUb) ∧
     checkPtr ⟨⟨0x4, none⟩, some (.VTablePointer vtZstPtr)⟩ uninhRef (some bmZst) = .error (.ub alignUb) ∧
     checkPtr ⟨⟨0x0, none⟩, some (.VTablePointer vtZstPtr)⟩ uninhRef (some bmZst) = .error (.ub nullUb) ∧
     checkPtr ⟨⟨0x1000, none⟩, some (.VTablePointer vt8Ptr)⟩ uninhRef (some bmZst) = .error (.ub uninhUb) ∧
     checkPtrM (M := TBM) ⟨⟨0x8, none⟩, some (.VTablePointer vtZstTB)⟩ uninhRef (some tbZst) =
       .error (.ub uninhUb) ∧
     checkPtrM (M := TBM) ⟨⟨0x8, none⟩, some (.VTablePointer vtZstTB)⟩ uninhMut (some tbZst) =
       .error (.ub uninhUb) ∧
     checkPtrM (M := TBM) ⟨⟨0x8, none⟩, some (.VTablePointer vtZstTB)⟩ uninhBox (some tbZst) =
       .error (.ub uninhUb) ∧
     checkPtrM (M := TBM) ⟨⟨0x4, none⟩, some (.VTablePointer vtZstTB)⟩ uninhRef (some tbZst) =
       .error (.ub alignUb) ∧
     checkPtrM (M := TBM) ⟨⟨0x0, none⟩, some (.VTablePointer vtZstTB)⟩ uninhRef (some tbZst) =
       .error (.ub nullUb) ∧
     checkPtrM (M := TBM) ⟨⟨0x1000, none⟩, some (.VTablePointer vt8TB)⟩ uninhRef (some tbZst) =
       .error (.ub uninhUb)) ∧
    -- 3. `PlaceExpr::Deref` on non-ZST safe `&dyn Trait0` (live ok vs dead UB)
    ((∃ m1, evalPlace (mkBM dynRef true liveWideBytes) derefExpr =
       .ok (({ ptr := ⟨⟨0x1000, some (⟨0⟩, ())⟩, some (.VTablePointer vt8Ptr)⟩, aligned := true },
         .TraitObject ep1VtTrait0), m1)) ∧
     evalPlace (mkBM dynRef false liveWideBytes) derefExpr = .error (.ub nonDerefUb) ∧
     (∃ m1, evalPlaceM (mkTB dynRef true liveWideBytes) derefExpr =
       .ok (({ ptr := ⟨⟨0x1000, some (⟨0⟩, [])⟩, some (.VTablePointer vt8TB)⟩, aligned := true },
         .TraitObject ep1VtTrait0), m1) ∧ MachTB.wfLive m1) ∧
     evalPlaceM (mkTB dynRef false liveWideBytes) derefExpr = .error (.ub nonDerefUb)) := by
  intro vtZst vtSize8 zstProg dynPointee uninhPointee dynRef dynMut dynBox uninhRef uninhMut
    uninhBox vtZstPtr vt8Ptr vtZstTB vt8TB zstWideBytes liveWideBytes mkBM mkTB bmZst tbZst
    derefExpr nullUb alignUb uninhUb nonDerefUb
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_⟩⟩
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · have h : (do
        let _ ← evalStatement (mkBM dynRef false zstWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) true)
        pure ()) = .ok () := by ep1_kernel_rfl
    obtain ⟨m1, hm1, _⟩ := ep1_bind_ok h; exact ⟨m1, hm1⟩
  · have h : (do
        let _ ← evalStatement (mkBM dynMut false zstWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) true)
        pure ()) = .ok () := by ep1_kernel_rfl
    obtain ⟨m1, hm1, _⟩ := ep1_bind_ok h; exact ⟨m1, hm1⟩
  · have h : (do
        let _ ← evalStatement (mkBM dynBox false zstWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) true)
        pure ()) = .ok () := by ep1_kernel_rfl
    obtain ⟨m1, hm1, _⟩ := ep1_bind_ok h; exact ⟨m1, hm1⟩
  · have h : Prod.fst <$> evalPlace bmZst derefExpr =
        .ok ({ ptr := ⟨⟨0x8, none⟩, some (.VTablePointer vtZstPtr)⟩, aligned := true },
          .TraitObject ep1VtTrait0) := by ep1_kernel_rfl
    exact ep1_ok_of_map_fst h
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · have h : (do
        let m1 ← evalStatementM (mkTB dynRef false zstWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) true)
        pure (m1.threads[0]?.bind (fun t : Gen.Thread TBM =>
          t.stack.getLast?.map (fun f : Gen.StackFrame TBM => f.extra.protectors)))) =
        .ok (some []) := by ep1_kernel_rfl
    obtain ⟨m1, hm1, h⟩ := ep1_bind_ok h
    exact ⟨m1, hm1, evalStatementM_tb_wfLive (liftMachToTB_wfLive (mkBM dynRef false zstWideBytes)) hm1,
      ep1_pure_ok h⟩
  · have h : (do
        let m1 ← evalStatementM (mkTB dynMut false zstWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) true)
        pure (m1.threads[0]?.bind (fun t : Gen.Thread TBM =>
          t.stack.getLast?.map (fun f : Gen.StackFrame TBM => f.extra.protectors)))) =
        .ok (some []) := by ep1_kernel_rfl
    obtain ⟨m1, hm1, h⟩ := ep1_bind_ok h
    exact ⟨m1, hm1, evalStatementM_tb_wfLive (liftMachToTB_wfLive (mkBM dynMut false zstWideBytes)) hm1,
      ep1_pure_ok h⟩
  · have h : (do
        let _ ← evalStatementM (mkTB dynBox false zstWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) false)
        pure ()) = .ok () := by ep1_kernel_rfl
    obtain ⟨m1, hm1, _⟩ := ep1_bind_ok h
    exact ⟨m1, hm1, evalStatementM_tb_wfLive (liftMachToTB_wfLive (mkBM dynBox false zstWideBytes)) hm1⟩
  · have h : (do
        let m1 ← evalStatementM (mkTB dynBox false zstWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) true)
        pure (m1.threads[0]?.bind (fun t : Gen.Thread TBM =>
          t.stack.getLast?.map (fun f : Gen.StackFrame TBM => f.extra.protectors)))) =
        .ok (some []) := by ep1_kernel_rfl
    obtain ⟨m1, hm1, h⟩ := ep1_bind_ok h
    exact ⟨m1, hm1, evalStatementM_tb_wfLive (liftMachToTB_wfLive (mkBM dynBox false zstWideBytes)) hm1,
      ep1_pure_ok h⟩
  · have h : Prod.fst <$> evalPlaceM tbZst derefExpr =
        .ok ({ ptr := ⟨⟨0x8, none⟩, some (.VTablePointer vtZstTB)⟩, aligned := true },
          .TraitObject ep1VtTrait0) := by ep1_kernel_rfl
    obtain ⟨m1, hm1⟩ := ep1_ok_of_map_fst h
    exact ⟨m1, hm1, evalPlaceM_tb_wfLive _ (liftMachToTB_wfLive bmZst) hm1⟩
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · have h : Prod.fst <$> evalPlace (mkBM dynRef true liveWideBytes) derefExpr =
        .ok ({ ptr := ⟨⟨0x1000, some (⟨0⟩, ())⟩, some (.VTablePointer vt8Ptr)⟩, aligned := true },
          .TraitObject ep1VtTrait0) := by ep1_kernel_rfl
    exact ep1_ok_of_map_fst h
  · ep1_kernel_rfl
  · have h : Prod.fst <$> evalPlaceM (mkTB dynRef true liveWideBytes) derefExpr =
        .ok ({ ptr := ⟨⟨0x1000, some (⟨0⟩, [])⟩, some (.VTablePointer vt8TB)⟩, aligned := true },
          .TraitObject ep1VtTrait0) := by ep1_kernel_rfl
    obtain ⟨m1, hm1⟩ := ep1_ok_of_map_fst h
    exact ⟨m1, hm1, evalPlaceM_tb_wfLive _ (liftMachToTB_wfLive (mkBM dynRef true liveWideBytes)) hm1⟩
  · ep1_kernel_rfl

/-- **`BinOp::ConstructWidePointer` fail-closed boundary and `VTablePointer`
decode + check witness**, on both `Mach` and `MachTB`:
1. `evalBinOp[M]` and `evalValue[M]` on `BinOp::ConstructWidePointer` evaluate
   both operands first (propagating dead-local UB from either operand) and then
   fail closed with `unsupported`;
2. `PointerMetaKind::decode_value[M]` + `checkValue[M]` on `dyn Trait0` wide
   pointers accepts a valid thin vtable pointer for trait `0`, rejects wrong
   trait (`"Value::Ptr: invalid vtable in metadata"`) and unmapped vtable
   pointers (`"invalid pointer for vtable lookup"`), and panics with
   `"PointerMeta::decode_value called with invalid value"` on non-pointer or
   wide-pointer metadata inputs. -/
theorem ep1_vtable_constructWidePointer_boundary_and_decode_witness :
    let dynRef : Gen.PtrType := .Ref .Immutable (ep1DynPointee ep1VtTrait0)
    let rawDyn : Gen.PtrType := .Raw (.VTablePointer ep1VtTrait0)
    let vtTy0 : Gen.Type := .Ptr (.VTablePtr ep1VtTrait0)
    let cwpBM : Mach :=
      { ep1MachBM ep1VtAllocsBM [] [(⟨⟨0⟩⟩, .Ptr (.Raw .None))] with
        prog := ep1VtProg
        fn_ptrs := ep1VtMachBM.fn_ptrs
        vtable_ptrs := ep1VtMachBM.vtable_ptrs }
    let cwpTB : MachTB := liftMachToTB cwpBM
    let thinExpr : Gen.ValueExpr :=
      .Constant (.PointerWithoutProvenance 0x1000) (.Ptr (.Raw .None))
    let vtExpr : Gen.ValueExpr := .Constant (.VTablePointer ⟨⟨0⟩⟩) vtTy0
    let deadExpr : Gen.ValueExpr := .Load (.Local ⟨⟨0⟩⟩)
    let unsupMsg :=
      "eval_bin_op for an operator outside BinOp::Int, BinOp::IntWithOverflow, and BinOp::Rel"
    let decodePanic := "PointerMeta::decode_value called with invalid value"
    let obj : Ptr := ⟨0x1000, some (⟨0⟩, ())⟩
    let vt0 : Ptr := ⟨0x4000, some (⟨3⟩, ())⟩
    let vt1 : Ptr := ⟨0x4008, some (⟨4⟩, ())⟩
    let objTB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x1000, some (⟨0⟩, [])⟩
    let vt0TB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x4000, some (⟨3⟩, [])⟩
    let vt1TB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x4008, some (⟨4⟩, [])⟩
    -- 1. `ConstructWidePointer` fail-closed boundary & operand UB precedence (`Mach` & `MachTB`)
    (evalBinOp (.ConstructWidePointer dynRef)
        (.Ptr (ThinPointer.widen obj none), .Ptr (.Raw .None))
        (.Ptr (ThinPointer.widen vt0 none), vtTy0) = .error (.unsupported unsupMsg) ∧
     evalValue cwpBM (.BinOp (.ConstructWidePointer dynRef) thinExpr vtExpr) =
       .error (.unsupported unsupMsg) ∧
     evalValue cwpBM (.BinOp (.ConstructWidePointer dynRef) deadExpr vtExpr) =
       .error (.ub "access to a dead local") ∧
     evalValue cwpBM (.BinOp (.ConstructWidePointer dynRef) thinExpr deadExpr) =
       .error (.ub "access to a dead local") ∧
     evalBinOpM (M := TBM) (.ConstructWidePointer dynRef)
        (.Ptr (ThinPointer.widen objTB none), .Ptr (.Raw .None))
        (.Ptr (ThinPointer.widen vt0TB none), vtTy0) = .error (.unsupported unsupMsg) ∧
     evalValueM cwpTB (.BinOp (.ConstructWidePointer dynRef) thinExpr vtExpr) =
       .error (.unsupported unsupMsg) ∧
     evalValueM cwpTB (.BinOp (.ConstructWidePointer dynRef) deadExpr vtExpr) =
       .error (.ub "access to a dead local") ∧
     evalValueM cwpTB (.BinOp (.ConstructWidePointer dynRef) thinExpr deadExpr) =
       .error (.ub "access to a dead local")) ∧
    -- 2. `decode_value[M]` + `checkValue[M]` for `dyn Trait0` (`Mach` & `MachTB`)
    ((do
        let ptrMeta ← PointerMetaKind.decode_value (PtrType.meta_kind dynRef)
          (.Ptr (ThinPointer.widen vt0 none))
        checkValue (.Ptr (ThinPointer.widen obj ptrMeta)) (.Ptr dynRef) (some cwpBM)) = .ok () ∧
     (do
        let ptrMeta ← PointerMetaKind.decode_value (PtrType.meta_kind rawDyn)
          (.Ptr (ThinPointer.widen vt1 none))
        checkValue (.Ptr (ThinPointer.widen obj ptrMeta)) (.Ptr rawDyn) (some cwpBM)) =
       .error (.ub "Value::Ptr: invalid vtable in metadata") ∧
     (do
        let ptrMeta ← PointerMetaKind.decode_value (PtrType.meta_kind dynRef)
          (.Ptr (ThinPointer.widen ⟨0, none⟩ none))
        checkValue (.Ptr (ThinPointer.widen obj ptrMeta)) (.Ptr dynRef) (some cwpBM)) =
       .error (.ub "invalid pointer for vtable lookup") ∧
     PointerMetaKind.decode_value (.VTablePointer ep1VtTrait0) (.Int 0) = specPanic decodePanic ∧
     PointerMetaKind.decode_value (.VTablePointer ep1VtTrait0)
       (.Ptr ⟨vt0, some (.VTablePointer vt0)⟩) = specPanic decodePanic ∧
     (do
        let ptrMeta ← PointerMetaKind.decode_valueM (M := TBM) (PtrType.meta_kind dynRef)
          (.Ptr (ThinPointer.widen vt0TB none))
        checkValueM (.Ptr (ThinPointer.widen objTB ptrMeta)) (.Ptr dynRef) (some cwpTB)) = .ok () ∧
     (do
        let ptrMeta ← PointerMetaKind.decode_valueM (M := TBM) (PtrType.meta_kind rawDyn)
          (.Ptr (ThinPointer.widen vt1TB none))
        checkValueM (.Ptr (ThinPointer.widen objTB ptrMeta)) (.Ptr rawDyn) (some cwpTB)) =
       .error (.ub "Value::Ptr: invalid vtable in metadata") ∧
     (do
        let ptrMeta ← PointerMetaKind.decode_valueM (M := TBM) (PtrType.meta_kind dynRef)
          (.Ptr (ThinPointer.widen ⟨0, none⟩ none))
        checkValueM (.Ptr (ThinPointer.widen objTB ptrMeta)) (.Ptr dynRef) (some cwpTB)) =
       .error (.ub "invalid pointer for vtable lookup") ∧
     PointerMetaKind.decode_valueM (M := TBM) (.VTablePointer ep1VtTrait0) (.Int 0) =
       specPanic decodePanic ∧
     PointerMetaKind.decode_valueM (M := TBM) (.VTablePointer ep1VtTrait0)
       (.Ptr ⟨vt0TB, some (.VTablePointer vt0TB)⟩) = specPanic decodePanic) := by
  intro dynRef rawDyn vtTy0 cwpBM cwpTB thinExpr vtExpr deadExpr unsupMsg decodePanic
    obj vt0 vt1 objTB vt0TB vt1TB
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  all_goals ep1_kernel_rfl

/-- **Exactness and non-vacuity of machine-congruence hypotheses**
(`checkPtr_congr_vtables`, `checkPtrM_congr_mach`, `evalUnOp_congr_vtables`,
`evalUnOpM_congr_mach`), on both `Mach` and `MachTB`:
1. Changing non-`vtables` `Program` fields (`start`, `traits`, so `M'.prog ≠ M.prog`
   while `M'.prog.vtables = M.prog.vtables`) leaves both `checkPtr[M]` and
   `evalUnOp[M]` unchanged;
2. Perturbing **any single** required field alone — `mem` (killing alloc `0`),
   `vtable_ptrs` (clearing the table), `prog.vtables` (changing the vtable's
   `trait_name`), or `fn_ptrs` (clearing function pointers, while `checkPtr[M]`
   remains invariant!) — strictly changes the result of `checkPtr[M]` or
   `evalUnOp[M] (.VTableMethodLookup _)`. -/
theorem ep1_vtable_congr_mach_hypotheses_necessary_witness :
    let dynRef : Gen.PtrType := .Ref .Immutable (ep1DynPointee ep1VtTrait0)
    let vtTy : Gen.Type := .Ptr (.VTablePtr ep1VtTrait0)
    let vt0 : Ptr := ⟨0x4000, some (⟨3⟩, ())⟩
    let fn1 : Ptr := ⟨0x5000, some (⟨5⟩, ())⟩
    let wide : Gen.Pointer Prov := ⟨⟨0x1000, some (⟨0⟩, ())⟩, some (.VTablePointer vt0)⟩
    let vt0TB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x4000, some (⟨3⟩, [])⟩
    let fn1TB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x5000, some (⟨5⟩, [])⟩
    let wideTB : Gen.Pointer Gen.TreeBorrowsProvenance :=
      ⟨⟨0x1000, some (⟨0⟩, [])⟩, some (.VTablePointer vt0TB)⟩
    let mProgOtherBM : Mach :=
      { ep1VtMachBM with prog := { ep1VtMachBM.prog with start := ⟨⟨99⟩⟩, traits := ⟨[]⟩ } }
    let mProgOtherTB : MachTB :=
      { ep1VtMachTB with prog := { ep1VtMachTB.prog with start := ⟨⟨99⟩⟩, traits := ⟨[]⟩ } }
    let deadAlloc0BM : Gen.Allocation Unit Unit :=
      { data := List.replicate 8 (.Init 0 none), addr := 0x1000, align := ⟨8⟩,
        kind := .Heap, live := false, extra := () }
    let mDeadMemBM : Mach :=
      { ep1VtMachBM with
        mem := { ep1VtMachBM.mem with
          memory := { ep1VtMachBM.mem.memory with
            allocations := deadAlloc0BM :: ep1VtAllocsBM.drop 1 } } }
    let mDeadMemTB : MachTB :=
      { ep1VtMachTB with
        mem := { ep1VtMachTB.mem with
          memory := { ep1VtMachTB.mem.memory with
            mem := { ep1VtMachTB.mem.memory.mem with
              allocations := ep1VtAllocTB 0x1000 8 8 .Heap false :: ep1VtAllocsTB.drop 1 } } } }
    let mNoVtPtrsBM : Mach := { ep1VtMachBM with vtable_ptrs := ⟨[]⟩ }
    let mNoVtPtrsTB : MachTB := { ep1VtMachTB with vtable_ptrs := ⟨[]⟩ }
    let mWrongVtsBM : Mach :=
      { ep1VtMachBM with
        prog := { ep1VtMachBM.prog with
          vtables := ⟨[(⟨⟨0⟩⟩, { ep1VTable0 with trait_name := ep1VtTrait1 })]⟩ } }
    let mWrongVtsTB : MachTB :=
      { ep1VtMachTB with
        prog := { ep1VtMachTB.prog with
          vtables := ⟨[(⟨⟨0⟩⟩, { ep1VTable0 with trait_name := ep1VtTrait1 })]⟩ } }
    let mNoFnPtrsBM : Mach := { ep1VtMachBM with fn_ptrs := ⟨[]⟩ }
    let mNoFnPtrsTB : MachTB := { ep1VtMachTB with fn_ptrs := ⟨[]⟩ }
    let missingFnPanic := "map index: missing key (self.fn_ptrs[fn_name])"
    -- 1. Non-`vtables` `Program` fields are irrelevant (`Mach` & `MachTB`)
    (mProgOtherBM.prog ≠ ep1VtMachBM.prog ∧
     checkPtr wide dynRef (some mProgOtherBM) = checkPtr wide dynRef (some ep1VtMachBM) ∧
     evalUnOp (.VTableMethodLookup ep1VtMeth0) (.Ptr (ThinPointer.widen vt0 none), vtTy)
         (some mProgOtherBM) =
       evalUnOp (.VTableMethodLookup ep1VtMeth0) (.Ptr (ThinPointer.widen vt0 none), vtTy)
         (some ep1VtMachBM) ∧
     mProgOtherTB.prog ≠ ep1VtMachTB.prog ∧
     checkPtrM wideTB dynRef (some mProgOtherTB) = checkPtrM wideTB dynRef (some ep1VtMachTB) ∧
     evalUnOpM (.VTableMethodLookup ep1VtMeth0) (.Ptr (ThinPointer.widen vt0TB none), vtTy)
         (some mProgOtherTB) =
       evalUnOpM (.VTableMethodLookup ep1VtMeth0) (.Ptr (ThinPointer.widen vt0TB none), vtTy)
         (some ep1VtMachTB)) ∧
    -- 2. Necessity of `hmem`, `hvt`, `hvts`, and `hfn` (`Mach`)
    (checkPtr wide dynRef (some ep1VtMachBM) = .ok () ∧
     checkPtr wide dynRef (some mDeadMemBM) =
       .error (.ub "Value::Ptr: non-dereferenceable safe pointer") ∧
     checkPtr wide dynRef (some mNoVtPtrsBM) =
       .error (.ub "invalid pointer for vtable lookup") ∧
     checkPtr wide dynRef (some mWrongVtsBM) =
       .error (.ub "Value::Ptr: invalid vtable in metadata") ∧
     checkPtr wide dynRef (some mNoFnPtrsBM) = .ok () ∧
     evalUnOp (.VTableMethodLookup ep1VtMeth0) (.Ptr (ThinPointer.widen vt0 none), vtTy)
         (some ep1VtMachBM) = .ok (.Ptr (ThinPointer.widen fn1 none), .Ptr .FnPtr) ∧
     evalUnOp (.VTableMethodLookup ep1VtMeth0) (.Ptr (ThinPointer.widen vt0 none), vtTy)
         (some mNoFnPtrsBM) = specPanic missingFnPanic) ∧
    -- 3. Necessity of `hmem`, `hvt`, `hvts`, and `hfn` (`MachTB`)
    (checkPtrM wideTB dynRef (some ep1VtMachTB) = .ok () ∧
     checkPtrM wideTB dynRef (some mDeadMemTB) =
       .error (.ub "Value::Ptr: non-dereferenceable safe pointer") ∧
     checkPtrM wideTB dynRef (some mNoVtPtrsTB) =
       .error (.ub "invalid pointer for vtable lookup") ∧
     checkPtrM wideTB dynRef (some mWrongVtsTB) =
       .error (.ub "Value::Ptr: invalid vtable in metadata") ∧
     checkPtrM wideTB dynRef (some mNoFnPtrsTB) = .ok () ∧
     evalUnOpM (.VTableMethodLookup ep1VtMeth0) (.Ptr (ThinPointer.widen vt0TB none), vtTy)
         (some ep1VtMachTB) = .ok (.Ptr (ThinPointer.widen fn1TB none), .Ptr .FnPtr) ∧
     evalUnOpM (.VTableMethodLookup ep1VtMeth0) (.Ptr (ThinPointer.widen vt0TB none), vtTy)
         (some mNoFnPtrsTB) = specPanic missingFnPanic) := by
  intro dynRef vtTy vt0 fn1 wide vt0TB fn1TB wideTB mProgOtherBM mProgOtherTB deadAlloc0BM
    mDeadMemBM mDeadMemTB mNoVtPtrsBM mNoVtPtrsTB mWrongVtsBM mWrongVtsTB mNoFnPtrsBM
    mNoFnPtrsTB missingFnPanic
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro h; have hs := congrArg Gen.Program.start h
    simp [mProgOtherBM, ep1VtMachBM, ep1VtProg] at hs
  · exact checkPtr_congr_vtables rfl rfl rfl wide dynRef
  · exact evalUnOp_congr_vtables rfl rfl rfl rfl (.VTableMethodLookup ep1VtMeth0)
      (.Ptr (ThinPointer.widen vt0 none), vtTy)
  · intro h; have hs := congrArg Gen.Program.start h
    simp [mProgOtherTB, ep1VtMachTB, ep1VtProg] at hs
  · exact checkPtrM_congr_mach (M1 := mProgOtherTB) (M2 := ep1VtMachTB) rfl rfl rfl wideTB dynRef
  · exact evalUnOpM_congr_mach (M1 := mProgOtherTB) (M2 := ep1VtMachTB) rfl rfl rfl rfl
      (.VTableMethodLookup ep1VtMeth0) (.Ptr (ThinPointer.widen vt0TB none), vtTy)
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · exact (checkPtr_congr_vtables (M1 := mNoFnPtrsBM) (M2 := ep1VtMachBM) rfl rfl rfl wide
      dynRef).trans (by ep1_kernel_rfl)
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · exact (checkPtrM_congr_mach (M1 := mNoFnPtrsTB) (M2 := ep1VtMachTB) rfl rfl rfl wideTB
      dynRef).trans (by ep1_kernel_rfl)
  · ep1_kernel_rfl
  · ep1_kernel_rfl

/-- **`Statement::Deinit` on an unsized `Type::TraitObject` place (`Mach`)**
follows upstream `spec/lang/step/statements.md` verbatim: a misaligned place
raises UB (`"de-initializing a place based on a misaligned pointer"`) first,
while an aligned `Type::TraitObject` place hits
`LayoutStrategy::expect_size("WF ensures deinits are sized")` (a spec panic,
never dynamic-size deinit). -/
theorem ep1_evalStatement_deinit_traitObject_spec (m m1 : Mach) (place : Gen.PlaceExpr)
    (p : Gen.Place BM) (traitName : Gen.TraitName)
    (hPl : evalPlace m place = .ok ((p, .TraitObject traitName), m1)) :
    (p.aligned = false →
      evalStatement m (.Deinit place) =
        .error (.ub "de-initializing a place based on a misaligned pointer")) ∧
    (p.aligned = true →
      evalStatement m (.Deinit place) =
        specPanic "expect_size called on unsized type: WF ensures deinits are sized") := by
  refine ⟨fun hAl => ?_, fun hAl => ?_⟩
  · unfold evalStatement
    simp only [hPl, ok_bind, hAl, Bool.not_false, ↓reduceIte, ub]
  · unfold evalStatement
    simp only [hPl, ok_bind, hAl, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- Polymorphic `ep1_evalStatement_deinit_traitObject_spec`, across every
`Memory` `M` (in particular `MachTB` / `TreeBorrowsMemory`). -/
theorem ep1_evalStatementM_deinit_traitObject_spec {M : Type} [Gen.Memory M] [MemoryOps M]
    (m m1 : Gen.Machine M) (place : Gen.PlaceExpr)
    (p : Gen.Place M) (traitName : Gen.TraitName)
    (hPl : evalPlaceM m place = .ok ((p, .TraitObject traitName), m1)) :
    (p.aligned = false →
      evalStatementM m (.Deinit place) =
        .error (.ub "de-initializing a place based on a misaligned pointer")) ∧
    (p.aligned = true →
      evalStatementM m (.Deinit place) =
        specPanic "expect_size called on unsized type: WF ensures deinits are sized") := by
  refine ⟨fun hAl => ?_, fun hAl => ?_⟩
  · unfold evalStatementM
    simp only [hPl, ok_bind, hAl, Bool.not_false, ↓reduceIte, ub]
  · unfold evalStatementM
    simp only [hPl, ok_bind, hAl, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl

set_option maxRecDepth 8192 in
/-- **Trait-object `Statement::Deinit` semantics, sized view/head deinit, and
Tree Borrows write-access mode sensitivity** (`Mach` & `MachTB`, with
`MachTB.wfLive`):
1. Direct `Statement::Deinit` on `*p : Type::TraitObject` raises
   `specPanic "expect_size called on unsized type: WF ensures deinits are sized"`
   when aligned, and UB `"de-initializing a place based on a misaligned pointer"`
   when misaligned for `vtable.align = 4` (upstream
   `spec/lang/step/statements.md`);
2. Sized 4-byte `Statement::Deinit` through `&mut dyn Trait0` (via
   `GetThinPointer`) and through `Field 0` of `&mut { head: u32, tail: dyn Trait0 }`
   turns bytes `[0..4)` to `.Uninit` while preserving bytes `[4..8)` intact on
   both `Mach` and `MachTB` (preserving `MachTB.wfLive`);
3. `Statement::Deinit` through validated `&dyn Trait0` succeeds on `Mach` and
   faults `"Tree Borrows: local write of Frozen reference"` on `MachTB`;
4. `Statement::Deinit` on a 16-byte `&dyn Trait0` local itself wipes all 16
   bytes to `.Uninit`, so reloading it raises
   `"load at type but the data in memory violates the language invariant"`. -/
theorem ep1_vtable_deinit_traitObject_and_sized_view_witness :
    let vt4 : Gen.VTable :=
      { trait_name := ep1VtTrait0, size := ⟨4⟩, align := ⟨4⟩, cells := [], methods := ⟨[]⟩ }
    let deinitProg : Gen.Program :=
      { functions := ⟨[]⟩, start := ⟨⟨0⟩⟩, globals := ⟨[]⟩,
        traits := ⟨[(ep1VtTrait0, ⟨[]⟩)]⟩, vtables := ⟨[(⟨⟨0⟩⟩, vt4)]⟩ }
    let dynPointee := ep1DynPointee ep1VtTrait0
    let dynRef : Gen.PtrType := .Ref .Immutable dynPointee
    let dynMut : Gen.PtrType := .Ref .Mutable dynPointee
    let rawDyn : Gen.PtrType := .Raw (.VTablePointer ep1VtTrait0)
    let head4 : Gen.TupleHeadLayout := ⟨⟨4⟩, ⟨4⟩, none⟩
    let structTy : Gen.Type :=
      .Tuple [(⟨0⟩, .Int ep1U32)] head4 (some (.TraitObject ep1VtTrait0))
    let structPointee : Gen.PointeeInfo :=
      { layout := .Tuple head4 (.TraitObject ep1VtTrait0), inhabited := true,
        unsafe_cells := .Tuple [] .TraitObject, freeze := true, unpin := true }
    let structMut : Gen.PtrType := .Ref .Mutable structPointee
    let initBuf : List Byte :=
      [.Init 1 none, .Init 2 none, .Init 3 none, .Init 4 none,
       .Init 5 none, .Init 6 none, .Init 7 none, .Init 8 none]
    let afterDeinit4 : List Byte :=
      [.Uninit, .Uninit, .Uninit, .Uninit,
       .Init 5 none, .Init 6 none, .Init 7 none, .Init 8 none]
    let afterDeinit4TB : List (Gen.AbstractByte Gen.TreeBorrowsProvenance) :=
      [.Uninit, .Uninit, .Uninit, .Uninit,
       .Init 5 none, .Init 6 none, .Init 7 none, .Init 8 none]
    let vt4Ptr : Ptr := ⟨0x4000, some (⟨2⟩, ())⟩
    let alignedWideBytes : List Byte :=
      encodePtrBytes (some (⟨0⟩, ())) 0 [0x00, 0x10, 0, 0, 0, 0, 0, 0] ++
      encodePtrBytes (some (⟨2⟩, ())) 0 [0x00, 0x40, 0, 0, 0, 0, 0, 0]
    let misalignedWideBytes : List Byte :=
      encodePtrBytes (some (⟨0⟩, ())) 0 [0x02, 0x10, 0, 0, 0, 0, 0, 0] ++
      encodePtrBytes (some (⟨2⟩, ())) 0 [0x00, 0x40, 0, 0, 0, 0, 0, 0]
    let mkBM (ptrTy : Gen.PtrType) (local1Bytes : List Byte) : Mach :=
      { ep1MachBM
          [{ data := initBuf, addr := 0x1000, align := ⟨8⟩,
             kind := .Heap, live := true, extra := () },
           { data := local1Bytes, addr := 0x2000, align := ⟨8⟩,
             kind := .Stack, live := true, extra := () },
           { data := [], addr := 0x4000, align := ⟨1⟩,
             kind := .VTable, live := true, extra := () }]
          [(⟨⟨1⟩⟩, ⟨0x2000, some (⟨1⟩, ())⟩)]
          [(⟨⟨1⟩⟩, .Ptr ptrTy)] with
        prog := deinitProg
        vtable_ptrs := ⟨[(⟨⟨0⟩⟩, vt4Ptr)]⟩ }
    let mkTB (ptrTy : Gen.PtrType) (local1Bytes : List Byte) : MachTB :=
      liftMachToTB (mkBM ptrTy local1Bytes)
    let deinitDynPlace : Gen.Statement :=
      .Deinit (.Deref (.Load (.Local ⟨⟨1⟩⟩)) (.TraitObject ep1VtTrait0))
    let deinitView4 : Gen.Statement :=
      .Deinit (.Deref (.UnOp .GetThinPointer (.Load (.Local ⟨⟨1⟩⟩))) (.Int ep1U32))
    let deinitHead4 : Gen.Statement :=
      .Deinit (.Field (.Deref (.Load (.Local ⟨⟨1⟩⟩)) structTy) 0)
    let deinitWideLocal : Gen.Statement := .Deinit (.Local ⟨⟨1⟩⟩)
    let unsizedPanic := "expect_size called on unsized type: WF ensures deinits are sized"
    let misalignedUb := "de-initializing a place based on a misaligned pointer"
    let frozenUb := "Tree Borrows: local write of Frozen reference"
    let loadInvUb := "load at type but the data in memory violates the language invariant"
    -- 1. Direct `Statement::Deinit` on `Type::TraitObject`: aligned panic vs misaligned UB
    (evalStatement (mkBM dynMut alignedWideBytes) deinitDynPlace = specPanic unsizedPanic ∧
     evalStatementM (mkTB dynMut alignedWideBytes) deinitDynPlace = specPanic unsizedPanic ∧
     evalStatement (mkBM rawDyn misalignedWideBytes) deinitDynPlace = .error (.ub misalignedUb) ∧
     evalStatementM (mkTB rawDyn misalignedWideBytes) deinitDynPlace = .error (.ub misalignedUb)) ∧
    -- 2. Sized 4-byte `Deinit` via `&mut dyn Trait0` and via `Field 0` of unsized struct
    ((∃ m1 m2,
       evalStatement (mkBM dynMut alignedWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) false) = .ok m1 ∧
       evalStatement m1 deinitView4 = .ok m2 ∧
       m2.mem.memory.allocations[0]?.map Gen.Allocation.data = some afterDeinit4) ∧
     (∃ m1 m2,
       evalStatementM (mkTB dynMut alignedWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) false) = .ok m1 ∧
       evalStatementM m1 deinitView4 = .ok m2 ∧
       MachTB.wfLive m2 ∧
       m2.mem.memory.mem.allocations[0]?.map Gen.Allocation.data = some afterDeinit4TB) ∧
     (∃ m1 m2,
       evalStatement (mkBM structMut alignedWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) false) = .ok m1 ∧
       evalStatement m1 deinitHead4 = .ok m2 ∧
       m2.mem.memory.allocations[0]?.map Gen.Allocation.data = some afterDeinit4) ∧
     (∃ m1 m2,
       evalStatementM (mkTB structMut alignedWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) false) = .ok m1 ∧
       evalStatementM m1 deinitHead4 = .ok m2 ∧
       MachTB.wfLive m2 ∧
       m2.mem.memory.mem.allocations[0]?.map Gen.Allocation.data = some afterDeinit4TB)) ∧
    -- 3. Tree Borrows mode sensitivity of `Deinit` on validated `&dyn Trait0`
    ((∃ m1 m2,
       evalStatement (mkBM dynRef alignedWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) false) = .ok m1 ∧
       evalStatement m1 deinitView4 = .ok m2 ∧
       m2.mem.memory.allocations[0]?.map Gen.Allocation.data = some afterDeinit4) ∧
     (∃ m1,
       evalStatementM (mkTB dynRef alignedWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) false) = .ok m1 ∧
       MachTB.wfLive m1 ∧
       evalStatementM m1 deinitView4 = .error (.ub frozenUb))) ∧
    -- 4. `Deinit` on the 16-byte `&dyn Trait0` local itself
    ((∃ m1,
       evalStatement (mkBM dynRef alignedWideBytes) deinitWideLocal = .ok m1 ∧
       m1.mem.memory.allocations[1]?.map Gen.Allocation.data = some (List.replicate 16 .Uninit) ∧
       evalValue m1 (.Load (.Local ⟨⟨1⟩⟩)) = .error (.ub loadInvUb)) ∧
     (∃ m1,
       evalStatementM (mkTB dynRef alignedWideBytes) deinitWideLocal = .ok m1 ∧
       MachTB.wfLive m1 ∧
       m1.mem.memory.mem.allocations[1]?.map Gen.Allocation.data =
         some (List.replicate 16 .Uninit) ∧
       evalValueM m1 (.Load (.Local ⟨⟨1⟩⟩)) = .error (.ub loadInvUb))) := by
  intro vt4 deinitProg dynPointee dynRef dynMut rawDyn head4 structTy structPointee structMut
    initBuf afterDeinit4 afterDeinit4TB vt4Ptr alignedWideBytes misalignedWideBytes mkBM mkTB
    deinitDynPlace deinitView4 deinitHead4 deinitWideLocal unsizedPanic misalignedUb frozenUb
    loadInvUb
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · have hseq :
        (do
          let m1 ← evalStatement (mkBM dynMut alignedWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) false)
          let m2 ← evalStatement m1 deinitView4
          pure (m2.mem.memory.allocations[0]?.map Gen.Allocation.data)) =
        .ok (some afterDeinit4) := by ep1_kernel_rfl
    obtain ⟨m1, hm1, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨m2, hm2, hseq⟩ := ep1_bind_ok hseq
    exact ⟨m1, m2, hm1, hm2, ep1_pure_ok hseq⟩
  · have hseq :
        (do
          let m1 ← evalStatementM (mkTB dynMut alignedWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) false)
          let m2 ← evalStatementM m1 deinitView4
          pure (m2.mem.memory.mem.allocations[0]?.map Gen.Allocation.data)) =
        .ok (some afterDeinit4TB) := by ep1_kernel_rfl
    obtain ⟨m1, hm1, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨m2, hm2, hseq⟩ := ep1_bind_ok hseq
    have hwf1 := evalStatementM_tb_wfLive (liftMachToTB_wfLive (mkBM dynMut alignedWideBytes)) hm1
    have hwf2 := evalStatementM_tb_wfLive hwf1 hm2
    exact ⟨m1, m2, hm1, hm2, hwf2, ep1_pure_ok hseq⟩
  · have hseq :
        (do
          let m1 ← evalStatement (mkBM structMut alignedWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) false)
          let m2 ← evalStatement m1 deinitHead4
          pure (m2.mem.memory.allocations[0]?.map Gen.Allocation.data)) =
        .ok (some afterDeinit4) := by ep1_kernel_rfl
    obtain ⟨m1, hm1, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨m2, hm2, hseq⟩ := ep1_bind_ok hseq
    exact ⟨m1, m2, hm1, hm2, ep1_pure_ok hseq⟩
  · have hseq :
        (do
          let m1 ← evalStatementM (mkTB structMut alignedWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) false)
          let m2 ← evalStatementM m1 deinitHead4
          pure (m2.mem.memory.mem.allocations[0]?.map Gen.Allocation.data)) =
        .ok (some afterDeinit4TB) := by ep1_kernel_rfl
    obtain ⟨m1, hm1, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨m2, hm2, hseq⟩ := ep1_bind_ok hseq
    have hwf1 := evalStatementM_tb_wfLive
      (liftMachToTB_wfLive (mkBM structMut alignedWideBytes)) hm1
    have hwf2 := evalStatementM_tb_wfLive hwf1 hm2
    exact ⟨m1, m2, hm1, hm2, hwf2, ep1_pure_ok hseq⟩
  · have hseq :
        (do
          let m1 ← evalStatement (mkBM dynRef alignedWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) false)
          let m2 ← evalStatement m1 deinitView4
          pure (m2.mem.memory.allocations[0]?.map Gen.Allocation.data)) =
        .ok (some afterDeinit4) := by ep1_kernel_rfl
    obtain ⟨m1, hm1, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨m2, hm2, hseq⟩ := ep1_bind_ok hseq
    exact ⟨m1, m2, hm1, hm2, ep1_pure_ok hseq⟩
  · have hseq :
        (do
          let m1 ← evalStatementM (mkTB dynRef alignedWideBytes) (.Validate (.Local ⟨⟨1⟩⟩) false)
          pure (evalStatementM m1 deinitView4)) =
        .ok (.error (.ub frozenUb)) := by ep1_kernel_rfl
    obtain ⟨m1, hm1, hseq⟩ := ep1_bind_ok hseq
    have hwf1 := evalStatementM_tb_wfLive (liftMachToTB_wfLive (mkBM dynRef alignedWideBytes)) hm1
    exact ⟨m1, hm1, hwf1, ep1_pure_ok hseq⟩
  · have hseq :
        (do
          let m1 ← evalStatement (mkBM dynRef alignedWideBytes) deinitWideLocal
          pure (m1.mem.memory.allocations[1]?.map Gen.Allocation.data,
            evalValue m1 (.Load (.Local ⟨⟨1⟩⟩)))) =
        .ok (some (List.replicate 16 .Uninit), .error (.ub loadInvUb)) := by ep1_kernel_rfl
    obtain ⟨m1, hm1, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨hdata, hload⟩ := Prod.mk.inj (ep1_pure_ok hseq)
    exact ⟨m1, hm1, hdata, hload⟩
  · have hseq :
        (do
          let m1 ← evalStatementM (mkTB dynRef alignedWideBytes) deinitWideLocal
          pure (m1.mem.memory.mem.allocations[1]?.map Gen.Allocation.data,
            evalValueM m1 (.Load (.Local ⟨⟨1⟩⟩)))) =
        .ok (some (List.replicate 16 .Uninit), .error (.ub loadInvUb)) := by ep1_kernel_rfl
    obtain ⟨m1, hm1, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨hdata, hload⟩ := Prod.mk.inj (ep1_pure_ok hseq)
    have hwf1 := evalStatementM_tb_wfLive (liftMachToTB_wfLive (mkBM dynRef alignedWideBytes)) hm1
    exact ⟨m1, hm1, hwf1, hdata, hload⟩

/-- **Misaligned safe trait-object pointer in `PlaceExpr::Deref` (`Mach`)**:
when the operand of `PlaceExpr::Deref` evaluates to a `&dyn Trait`,
`&mut dyn Trait`, or `Box<dyn Trait>` whose address is not aligned to the
vtable's alignment `vt.align`, `evalPlace` hits upstream's internal alignment
assertion (`spec/lang/step/expressions.md:254`) and raises a `specPanic`
before calling `Memory::dereferenceable` (for every destination type `ty`). -/
theorem ep1_evalPlace_deref_safe_traitObject_misaligned_specPanic (m m1 : Mach)
    (operand : Gen.ValueExpr) (ty : Gen.Type) (thin vptr : Ptr)
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (traitName : Gen.TraitName) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hOp : evalValue m operand =
      .ok ((.Ptr (ThinPointer.widen thin (some (.VTablePointer vptr))), .Ptr (mk pointee)), m1))
    (hvt : vtableLookup m1 vptr = .ok vt)
    (hMis : Align.is_aligned vt.align thin.addr = false) :
    evalPlace m (.Deref operand ty) =
      specPanic
        "assertion failed: self.compute_align(pointee.layout, ptr.metadata).is_aligned(ptr.thin_pointer.addr)" := by
  have hca : computeAlign m1 (.TraitObject traitName) (some (.VTablePointer vptr)) =
      .ok vt.align := by
    unfold computeAlign
    rw [compute_size_and_align_traitObject, hvt]
    rfl
  unfold evalPlace
  rw [hOp, ok_bind]
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · dsimp only [ThinPointer.widen, PtrType.safe_pointee]
    rw [hLayout, hca, ok_bind, hMis]
    simp only [Bool.not_false, ↓reduceIte, specPanic, error_bind]
  · dsimp only [ThinPointer.widen, PtrType.safe_pointee]
    rw [hLayout, hca, ok_bind, hMis]
    simp only [Bool.not_false, ↓reduceIte, specPanic, error_bind]

/-- Polymorphic `ep1_evalPlace_deref_safe_traitObject_misaligned_specPanic`,
across every `Memory` `M` (in particular `MachTB` / `TreeBorrowsMemory`). -/
theorem ep1_evalPlaceM_deref_safe_traitObject_misaligned_specPanic {M : Type}
    [Gen.Memory M] [MemoryOps M] (m m1 : Gen.Machine M)
    (operand : Gen.ValueExpr) (ty : Gen.Type)
    (thin vptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (traitName : Gen.TraitName) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hOp : evalValueM m operand =
      .ok ((.Ptr (ThinPointer.widen thin (some (.VTablePointer vptr))), .Ptr (mk pointee)), m1))
    (hvt : vtableLookupM m1 vptr = .ok vt)
    (hMis : Align.is_aligned vt.align thin.addr = false) :
    evalPlaceM m (.Deref operand ty) =
      specPanic
        "assertion failed: self.compute_align(pointee.layout, ptr.metadata).is_aligned(ptr.thin_pointer.addr)" := by
  have hca : computeAlignM m1 (.TraitObject traitName) (some (.VTablePointer vptr)) =
      .ok vt.align := by
    unfold computeAlignM
    rw [compute_size_and_align_traitObject, hvt]
    rfl
  unfold evalPlaceM
  rw [hOp, ok_bind]
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · dsimp only [ThinPointer.widen, PtrType.safe_pointee]
    rw [hLayout, hca, ok_bind, hMis]
    simp only [Bool.not_false, ↓reduceIte, specPanic, error_bind]
  · dsimp only [ThinPointer.widen, PtrType.safe_pointee]
    rw [hLayout, hca, ok_bind, hMis]
    simp only [Bool.not_false, ↓reduceIte, specPanic, error_bind]

private theorem ep1_cellsToFreezeMaskLoop_zero_step (rest : List (Gen.Offset × Size))
    (mask : List Bool) :
    cellsToFreezeMaskLoop (⟨0⟩, ⟨0⟩) ((⟨0⟩, ⟨0⟩) :: rest) mask =
      cellsToFreezeMaskLoop (⟨0⟩, ⟨0⟩) rest mask := by
  have h : cellsToFreezeMaskLoop (⟨0⟩, ⟨0⟩) ((⟨0⟩, ⟨0⟩) :: rest) mask =
      cellsToFreezeMaskLoop (⟨0⟩, ⟨0⟩) rest (mask ++ [] ++ []) := rfl
  rw [h, List.append_nil, List.append_nil]

private theorem ep1_cellsToFreezeMaskLoop_zero_all :
    ∀ (xs : List (Gen.Offset × Size)) (mask : List Bool),
      (∀ c ∈ xs, c = (⟨0⟩, ⟨0⟩)) →
      cellsToFreezeMaskLoop (⟨0⟩, ⟨0⟩) (xs ++ [(⟨0⟩, ⟨0⟩)]) mask = .ok mask
  | [], mask, _ => by
    rw [List.nil_append, ep1_cellsToFreezeMaskLoop_zero_step]
    rfl
  | c :: rest, mask, hall => by
    have hc : c = (⟨0⟩, ⟨0⟩) := hall c List.mem_cons_self
    subst hc
    rw [List.cons_append, ep1_cellsToFreezeMaskLoop_zero_step]
    exact ep1_cellsToFreezeMaskLoop_zero_all rest mask
      (fun x hx => hall x (List.mem_cons_of_mem _ hx))

private theorem ep1_cellsToFreezeMaskLoop_pos_panic :
    ∀ (xs : List (Gen.Offset × Size)) (cur : Gen.Offset × Size) (mask : List Bool),
      0 < cur.1.bytes + cur.2.bytes →
      cellsToFreezeMaskLoop cur (xs ++ [(⟨0⟩, ⟨0⟩)]) mask =
        specPanic "cells_to_freeze_mask: overlapping or out-of-order UnsafeCell ranges"
  | [], cur, mask, hpos => by
    rw [List.nil_append]
    unfold cellsToFreezeMaskLoop
    have hlt : ((0 : Nat) : Int) - ((cur.1.bytes + cur.2.bytes : Nat) : Int) < 0 := by omega
    dsimp only
    simp only [hlt, ↓reduceIte]
  | next :: rest, cur, mask, hpos => by
    rw [List.cons_append]
    unfold cellsToFreezeMaskLoop
    by_cases hlt : (next.1.bytes : Int) - ((cur.1.bytes + cur.2.bytes : Nat) : Int) < 0
    · simp only [hlt, ↓reduceIte]
    · simp only [hlt, ↓reduceIte]
      exact ep1_cellsToFreezeMaskLoop_pos_panic rest next _ (by omega)

private theorem ep1_cellsToFreezeMaskLoop_bad_panic :
    ∀ (xs : List (Gen.Offset × Size)) (mask : List Bool),
      (∃ c ∈ xs, c ≠ (⟨0⟩, ⟨0⟩)) →
      cellsToFreezeMaskLoop (⟨0⟩, ⟨0⟩) (xs ++ [(⟨0⟩, ⟨0⟩)]) mask =
        specPanic "cells_to_freeze_mask: overlapping or out-of-order UnsafeCell ranges"
  | [], _, ⟨_, hmem, _⟩ => nomatch hmem
  | c :: rest, mask, ⟨bad, hmem, hne⟩ => by
    by_cases hc : c = (⟨0⟩, ⟨0⟩)
    · subst hc
      rw [List.cons_append, ep1_cellsToFreezeMaskLoop_zero_step]
      have hrest : ∃ b ∈ rest, b ≠ (⟨0⟩, ⟨0⟩) := by
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact absurd rfl hne
        · exact ⟨bad, hmem', hne⟩
      exact ep1_cellsToFreezeMaskLoop_bad_panic rest mask hrest
    · have hpos : 0 < c.1.bytes + c.2.bytes := by
        rcases c with ⟨⟨o⟩, ⟨s⟩⟩
        dsimp only
        by_cases h0 : o = 0 ∧ s = 0
        · rcases h0 with ⟨rfl, rfl⟩; exact absurd rfl hc
        · omega
      rw [List.cons_append]
      unfold cellsToFreezeMaskLoop
      dsimp only
      split
      · rfl
      · exact ep1_cellsToFreezeMaskLoop_pos_panic rest c _ hpos

/-- **Complete dichotomy for `cellsToFreezeMask cells ⟨0⟩`** (arbitrary
`UnsafeCell` ranges on a zero-sized type):
1. if every cell is `(⟨0⟩, ⟨0⟩)` (empty list or zero-sized `UnsafeCell<()>` at
   offset `0`), `cellsToFreezeMask cells ⟨0⟩ = .ok []`;
2. if any cell has non-zero offset or non-zero size, `cellsToFreezeMask`
   panics with `"cells_to_freeze_mask: overlapping or out-of-order UnsafeCell ranges"`. -/
theorem ep1_cellsToFreezeMask_zero_dichotomy (cells : List (Gen.Offset × Size)) :
    ((∀ c ∈ cells, c = (⟨0⟩, ⟨0⟩)) → cellsToFreezeMask cells ⟨0⟩ = .ok []) ∧
    ((∃ c ∈ cells, c ≠ (⟨0⟩, ⟨0⟩)) →
      cellsToFreezeMask cells ⟨0⟩ =
        specPanic "cells_to_freeze_mask: overlapping or out-of-order UnsafeCell ranges") := by
  refine ⟨fun hall => ?_, fun hbad => ?_⟩
  · unfold cellsToFreezeMask
    rw [ep1_cellsToFreezeMaskLoop_zero_all cells [] hall, ok_bind]
    rfl
  · unfold cellsToFreezeMask
    rw [ep1_cellsToFreezeMaskLoop_bad_panic cells [] hbad]
    unfold specPanic
    rw [error_bind]

/-- **General ZST `TreeBorrowsMemory.retag_ptr` dichotomy for arbitrary
`vt.cells`** on a provenance-free trait-object pointer (`vt.size = 0`,
`thin.provenance = none`), lifting the `vt.cells = []` restriction of
`retag_ptr_traitObject_zst_noProv`:
1. whenever every entry in `vt.cells` is `(⟨0⟩, ⟨0⟩)` (including `[]` and
   zero-sized `UnsafeCell<()>` fields at offset `0`), `retag_ptr` is the
   identity `(ptr, tbm, frameExtra)` for `&dyn`, `&mut dyn`, and `Box<dyn>` at
   every `fnEntry`, `fnImplicitWrites`, `freeze`, and `unpin`;
2. if `vt.cells` contains any cell `≠ (⟨0⟩, ⟨0⟩)`, then:
   * when retagging runs (`&dyn Trait`, or `&mut dyn Trait` / `Box<dyn Trait>`
     with `pointee.unpin = true`), `retag_ptr` propagates the `cellsToFreezeMask`
     `specPanic`;
   * for pinned `!pointee.unpin` `&mut dyn Trait` / `Box<dyn Trait>`,
     `ReborrowSettings::new` returns `none` before calling `freeze_mask`, so
     `retag_ptr` remains the identity. -/
theorem ep1_retag_ptr_traitObject_zst_noProv_cells_dichotomy
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64) (frameExtra : Gen.TreeBorrowsFrameExtra)
    (thin vptr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (traitName : Gen.TraitName) (fnEntry fnImplicitWrites : Bool)
    (vtableLookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable)
    (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hCells : pointee.unsafe_cells = .TraitObject)
    (hvt : vtableLookup vptr = .ok vt)
    (hSize : vt.size = ⟨0⟩)
    (hProv : thin.provenance = none) :
    let ptr := ThinPointer.widen thin (some (.VTablePointer vptr))
    ((∀ c ∈ vt.cells, c = (⟨0⟩, ⟨0⟩)) →
      TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (mk pointee) fnEntry fnImplicitWrites
          vtableLookup = .ok (ptr, tbm, frameExtra)) ∧
    ((∃ c ∈ vt.cells, c ≠ (⟨0⟩, ⟨0⟩)) →
      ((mk = Gen.PtrType.Ref .Immutable ∨ pointee.unpin = true) →
        TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (mk pointee) fnEntry fnImplicitWrites
            vtableLookup =
          specPanic "cells_to_freeze_mask: overlapping or out-of-order UnsafeCell ranges") ∧
      (((mk = Gen.PtrType.Ref .Mutable ∨ mk = Gen.PtrType.Box) ∧ pointee.unpin = false) →
        TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (mk pointee) fnEntry fnImplicitWrites
            vtableLookup = .ok (ptr, tbm, frameExtra))) := by
  intro ptr
  have hReb : ∀ (outside : Gen.Permission) (prot : Gen.Protected),
      TreeBorrowsMemory.reborrow tbm thin
        { inside := [], outside := outside, «protected» := prot } frameExtra =
        .ok (thin, tbm, frameExtra) := by
    intro outside prot
    unfold TreeBorrowsMemory.reborrow
    have hchk : BasicMemory.check_ptr tbm.mem thin ⟨0⟩ = .ok none := rfl
    dsimp only [List.length]
    rw [hchk, ok_bind, hProv]
    rfl
  obtain ⟨layout, inhabited, cells, freeze, unpin⟩ := pointee
  dsimp only at hLayout hCells
  subst hLayout; subst hCells
  refine ⟨fun hall => ?_, fun hbad => ?_⟩
  · have hFreeze : UnsafeCellStrategy.freeze_mask vtableLookup .TraitObject
        (.TraitObject traitName) (some (.VTablePointer vptr)) = .ok [] := by
      unfold UnsafeCellStrategy.freeze_mask
      rw [hvt, ok_bind, hSize, (ep1_cellsToFreezeMask_zero_dichotomy vt.cells).1 hall]
    rcases hMk with ⟨mutbl, rfl⟩ | rfl
    · cases mutbl with
      | Immutable =>
        unfold TreeBorrowsMemory.retag_ptr ReborrowSettings.new
        simp only [ptr, ThinPointer.widen, PtrType.safe_pointee, Bool.false_eq_true, ↓reduceIte,
          hFreeze, ok_bind, List.mapM_nil, pure_ok, ReborrowSettings.perm]
        cases freeze <;> simp only [Bool.false_eq_true, ↓reduceIte, ok_bind, hReb]
      | Mutable =>
        cases unpin with
        | false =>
          unfold TreeBorrowsMemory.retag_ptr ReborrowSettings.new
          simp only [ptr, ThinPointer.widen, PtrType.safe_pointee, Bool.not_false, ↓reduceIte,
            pure_ok, ok_bind]
        | true =>
          unfold TreeBorrowsMemory.retag_ptr ReborrowSettings.new
          simp only [ptr, ThinPointer.widen, PtrType.safe_pointee, Bool.not_true,
            Bool.false_eq_true, ↓reduceIte, hFreeze, ok_bind, List.mapM_nil, pure_ok,
            ReborrowSettings.perm, Bool.and_false, hReb]
    · cases unpin with
      | false =>
        unfold TreeBorrowsMemory.retag_ptr ReborrowSettings.new
        simp only [ptr, ThinPointer.widen, PtrType.safe_pointee, Bool.not_false, ↓reduceIte,
          pure_ok, ok_bind]
      | true =>
        unfold TreeBorrowsMemory.retag_ptr ReborrowSettings.new
        simp only [ptr, ThinPointer.widen, PtrType.safe_pointee, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte, hFreeze, ok_bind, List.mapM_nil, pure_ok,
          ReborrowSettings.perm, Bool.and_false, hReb]
  · have hFreezeBad : UnsafeCellStrategy.freeze_mask vtableLookup .TraitObject
        (.TraitObject traitName) (some (.VTablePointer vptr)) =
        specPanic "cells_to_freeze_mask: overlapping or out-of-order UnsafeCell ranges" := by
      unfold UnsafeCellStrategy.freeze_mask
      rw [hvt, ok_bind, hSize, (ep1_cellsToFreezeMask_zero_dichotomy vt.cells).2 hbad]
    refine ⟨fun hActive => ?_, fun ⟨hMutOrBox, hUnpin⟩ => ?_⟩
    · rcases hMk with ⟨mutbl, rfl⟩ | rfl
      · cases mutbl with
        | Immutable =>
          unfold TreeBorrowsMemory.retag_ptr ReborrowSettings.new
          simp only [ptr, ThinPointer.widen, PtrType.safe_pointee, Bool.false_eq_true, ↓reduceIte,
            hFreezeBad, specPanic, error_bind]
        | Mutable =>
          rcases hActive with hEq | hUnpin
          · exfalso
            have h0 := congrArg (fun f => f ⟨.TraitObject traitName, inhabited, .TraitObject, freeze, unpin⟩) hEq
            injection h0 with hmut
            cases hmut
          · subst hUnpin
            unfold TreeBorrowsMemory.retag_ptr ReborrowSettings.new
            simp only [ptr, ThinPointer.widen, PtrType.safe_pointee, Bool.not_true,
              Bool.false_eq_true, ↓reduceIte, hFreezeBad, specPanic, error_bind]
      · rcases hActive with hEq | hUnpin
        · exfalso
          have h0 := congrArg (fun f => f ⟨.TraitObject traitName, inhabited, .TraitObject, freeze, unpin⟩) hEq
          cases h0
        · subst hUnpin
          unfold TreeBorrowsMemory.retag_ptr ReborrowSettings.new
          simp only [ptr, ThinPointer.widen, PtrType.safe_pointee, Bool.not_true,
            Bool.false_eq_true, ↓reduceIte, hFreezeBad, specPanic, error_bind]
    · subst hUnpin
      rcases hMutOrBox with rfl | rfl
      · unfold TreeBorrowsMemory.retag_ptr ReborrowSettings.new
        simp only [ptr, ThinPointer.widen, PtrType.safe_pointee, Bool.not_false, ↓reduceIte,
          pure_ok, ok_bind]
      · unfold TreeBorrowsMemory.retag_ptr ReborrowSettings.new
        simp only [ptr, ThinPointer.widen, PtrType.safe_pointee, Bool.not_false, ↓reduceIte,
          pure_ok, ok_bind]

/-- **Ill-formed `ValueExpr::Variant` / `ValueExpr::Union` ASTs are spec panics, not UB**, on
both `Mach` and `MachTB`:

1. `ValueExpr::Variant` performs no check of its own (upstream just builds
   `Value::Variant { discriminant, data }`), so an undeclared discriminant `9` evaluates
   successfully; storing it is then upstream's failed
   `assert!(self.check_value(val, ty).is_ok(), ..)` in `typed_store` — a spec panic, although
   the inner `check_value` failure is a `throw_ub!`;
2. `ValueExpr::Union` with a field whose encoding does not fit in the union
   (`write_subslice_at_index` out of range) or whose operand value does not match the field
   type (`expr_ty.encode(val)`) is a spec panic;
3. UB of the operand of a well-indexed `Union` / of a `Variant` propagates as UB. -/
theorem ep1_variant_union_ill_formed_ast_specPanic_witness :
    let localTys : List (Gen.LocalName × Gen.Type) :=
      [(⟨⟨0⟩⟩, ep1EnumTy), (⟨⟨1⟩⟩, .Int ep1U32)]
    let mBM := ep1MachBM
      [{ data := List.replicate 8 .Uninit, addr := 0x100, align := ⟨4⟩, kind := .Stack,
         live := true, extra := () }]
      [(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, ())⟩)]
      localTys
    let mTB := liftMachToTB mBM
    let badVariant : Gen.ValueExpr :=
      .Variant 9 (.Tuple [] ep1Var0TupleTy) ep1EnumTy
    let overflowUnionTy : Gen.Type := .Union [(⟨2⟩, .Int ep1U32)] [(⟨0⟩, ⟨4⟩)] ⟨4⟩ ⟨4⟩
    let storePanic := "trying to store a value which is ill-formed for its type"
    let deadLocalUb := "access to a dead local"
    -- 1. undeclared discriminant: evaluates, then `typed_store` asserts
    (evalValue mBM badVariant = .ok ((.Variant 9 (.Tuple []), ep1EnumTy), mBM) ∧
     evalValueM mTB badVariant = .ok ((.Variant 9 (.Tuple []), ep1EnumTy), mTB) ∧
     evalStatement mBM (.Assign (.Local ⟨⟨0⟩⟩) badVariant) = specPanic storePanic ∧
     evalStatementM mTB (.Assign (.Local ⟨⟨0⟩⟩) badVariant) = specPanic storePanic) ∧
    -- 2. `Union` field encoding out of range / operand of the wrong type
    (evalValue mBM (.Union 0 (.Constant (.Int 1) (.Int ep1U32)) overflowUnionTy) =
       specPanic "write_subslice_at_index out of range" ∧
     evalValueM mTB (.Union 0 (.Constant (.Int 1) (.Int ep1U32)) overflowUnionTy) =
       specPanic "write_subslice_at_index out of range" ∧
     evalValue mBM (.Union 0 (.Constant (.Bool true) .Bool) ep1UnionTy) =
       specPanic "encode: Type::Int with a non-Int value" ∧
     evalValueM mTB (.Union 0 (.Constant (.Bool true) .Bool) ep1UnionTy) =
       specPanic "encode: Type::Int with a non-Int value") ∧
    -- 3. operand UB propagates
    (evalValue mBM (.Union 0 (.Load (.Local ⟨⟨1⟩⟩)) ep1UnionTy) = .error (.ub deadLocalUb) ∧
     evalValueM mTB (.Union 0 (.Load (.Local ⟨⟨1⟩⟩)) ep1UnionTy) = .error (.ub deadLocalUb) ∧
     evalValue mBM (.Variant 1 (.Load (.Local ⟨⟨1⟩⟩)) ep1EnumTy) = .error (.ub deadLocalUb) ∧
     evalValueM mTB (.Variant 1 (.Load (.Local ⟨⟨1⟩⟩)) ep1EnumTy) = .error (.ub deadLocalUb)) := by
  intro localTys mBM mTB badVariant overflowUnionTy storePanic deadLocalUb
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

/-- A machine whose single local `_0 : orderingTy` (the correspondence's `Ordering` enum,
`MiniRustSpec.Correspondence.orderingTy`) occupies the one byte `b`. -/
private def ep1OrderingMach (b : Byte) : Mach :=
  ep1MachBM
    [{ data := [b], addr := 0x100, align := ⟨1⟩, kind := .Stack, live := true, extra := () }]
    [(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, ())⟩)]
    [(⟨⟨0⟩⟩, orderingTy)]

/-- The discriminant outcome of an evaluation at `IntType::I8`: `some (some i)` for success
with `Value::Int(i)` at `i8`, `some none` for UB, and `none` for anything else (a spec
panic, `unsupported`, or a result of another shape). -/
private def ep1DiscrOutcome {M : Type} [Gen.Memory M] {μ : Type}
    (r : Interp ((Gen.Value M × Gen.Type) × μ)) : Option (Option Int) :=
  match r with
  | .ok ((.Int i, .Int ⟨.Signed, ⟨1⟩⟩), _) => some (some i)
  | .error (.ub _) => some none
  | _ => none

/-- **The executable `GetDiscriminant` validates the correspondence's `Rvalue::Discriminant`
lowering and its hand-written model.** Before Episode 1 the interpreter had no
`GetDiscriminant`, so `Correspondence.Translate` lowers `Rvalue::Discriminant` on an
`Ordering` local to `orderingDiscrExpr (Load place)` and
`orderingDiscrExpr_eq_getDiscriminant` could compare that lowering only with a
*hand-written model* (`orderingGetDiscriminant`). On **every** byte an `Ordering` local can
hold — the uninitialized byte and all 256 initialized bytes — the now-executable
`eval_value(GetDiscriminant(_0))` on both `Mach` and `MachTB` has exactly the outcome of
that model (`Int` of the tag at `i8`, or UB), and so does the lowering
`eval_value(orderingDiscrExpr(Load(_0)))` on both machines. -/
theorem ep1_getDiscriminant_ordering_agrees_with_model_and_lowering :
    ((Gen.AbstractByte.Uninit :: (List.range 256).map (fun n => .Init (UInt8.ofNat n) none)).all
      (fun (b : Byte) =>
        let m := ep1OrderingMach b
        let place : Gen.PlaceExpr := .Local ⟨⟨0⟩⟩
        let model : Option (Option Int) :=
          match orderingGetDiscriminant b with
          | .ok d => some d
          | .error _ => none
        ep1DiscrOutcome (evalValue m (.GetDiscriminant place)) == model &&
        ep1DiscrOutcome (evalValueM (liftMachToTB m) (.GetDiscriminant place)) == model &&
        ep1DiscrOutcome (evalValue m (orderingDiscrExpr (.Load place))) == model &&
        ep1DiscrOutcome (evalValueM (liftMachToTB m) (orderingDiscrExpr (.Load place))) == model))
      = true ∧
    (∃ m1, evalValue (ep1OrderingMach (.Init 255 none)) (.GetDiscriminant (.Local ⟨⟨0⟩⟩)) =
      .ok ((.Int (-1), .Int IntType.I8), m1)) ∧
    evalValue (ep1OrderingMach (.Init 2 none)) (.GetDiscriminant (.Local ⟨⟨0⟩⟩)) =
      ub "ValueExpr::GetDiscriminant encountered invalid discriminant." ∧
    evalValue (ep1OrderingMach .Uninit) (.GetDiscriminant (.Local ⟨⟨0⟩⟩)) =
      ub "ValueExpr::GetDiscriminant encountered invalid discriminant." := by
  refine ⟨by decide +kernel, ⟨_, rfl⟩, rfl, rfl⟩


/-- **`Downcast`'s variant lookup is the representation relation's variant lookup.**
`PlaceExpr::Downcast` types the place at `variants[discriminant].ty` through `mapIndex`
(`Map::index`), whereas `Type::decode`, `Type::encode`, and `check_value` at an enum walk
the association list themselves (`Type.decodeVariant[M]`, `Type.encodeVariant[M]`,
`checkVariant[M]`). For every association list — including lists with shadowed duplicate
keys, which `libspecr::Map` cannot hold but the Lean `Map` can — all four pick the same
(first) entry for `discriminant`, on every `Memory` `M`:

* if `variants.get(discriminant)` is `Some(var)`, then decoding, checking, and encoding the
  enum at that discriminant are decoding, checking, and encoding at `var.ty` (the type
  `Downcast` assigns to the place) followed, for `encode`, by `encode_discriminant` with
  `var.tagger`;
* if it is `None`, `Downcast` and `decode` / `encode` are the `Map::index` spec panic and
  `check_value` is UB (`"Value::Variant: invalid discrimant"`).

So a `Downcast` + `Field` projection addresses exactly the variant payload type that a
`Load` / `Assign` of the whole enum uses. -/
theorem ep1_downcast_variant_lookup_agrees_with_representation
    {M : Type} [Gen.Memory M] [MemoryOps M] (d : Int) :
    ∀ (variants : List (Int × Gen.Variant)),
      (∀ var, mapGet (⟨variants⟩ : Map Int Gen.Variant) d = some var →
        mapIndex (⟨variants⟩ : Map Int Gen.Variant) d "variants[discriminant]" = .ok var ∧
        (∀ bytes, Type.decodeVariantM (M := M) variants d bytes = Type.decodeM var.ty bytes) ∧
        (∀ data m, checkVariantM (M := M) variants d data m = checkValueM data var.ty m) ∧
        (∀ data, Type.encodeVariantM (M := M) variants d data = (do
          let bytes ← Type.encodeM var.ty data
          encodeDiscriminantM (M := M)
            (fun bytes offset valueBytes => writeSubsliceAtIndex bytes offset.bytes valueBytes)
            var.tagger bytes))) ∧
      (mapGet (⟨variants⟩ : Map Int Gen.Variant) d = none →
        mapIndex (⟨variants⟩ : Map Int Gen.Variant) d "variants[discriminant]" =
          specPanic "map index: missing key (variants[discriminant])" ∧
        (∀ bytes, Type.decodeVariantM (M := M) variants d bytes =
          specPanic "map index: missing key (variants[discriminant])") ∧
        (∀ data m, checkVariantM (M := M) variants d data m =
          ub "Value::Variant: invalid discrimant") ∧
        (∀ data, Type.encodeVariantM (M := M) variants d data =
          specPanic "map index: missing key (variants[discriminant])"))
  | [] => by
    refine ⟨fun var h => by simp [mapGet] at h, fun _ => ⟨rfl, fun _ => ?_, fun _ _ => ?_, fun _ => ?_⟩⟩
    · unfold Type.decodeVariantM; rfl
    · unfold checkVariantM; rfl
    · unfold Type.encodeVariantM; rfl
  | (d', ⟨ty, tagger⟩) :: rest => by
    have ih := ep1_downcast_variant_lookup_agrees_with_representation (M := M) d rest
    by_cases hd : d' = d
    · subst hd
      refine ⟨fun var h => ?_, fun h => by simp [mapGet] at h⟩
      have hvar : var = ⟨ty, tagger⟩ := by
        simp [mapGet] at h
        exact h.symm
      subst hvar
      refine ⟨by simp [mapIndex, mapGet, pure, Except.pure], fun bytes => ?_, fun data m => ?_,
        fun data => ?_⟩
      · unfold Type.decodeVariantM; simp
      · unfold checkVariantM; simp
      · unfold Type.encodeVariantM; simp
    · have hget : mapGet (⟨(d', ⟨ty, tagger⟩) :: rest⟩ : Map Int Gen.Variant) d =
          mapGet (⟨rest⟩ : Map Int Gen.Variant) d := by
        simp [mapGet, hd]
      have hidx : mapIndex (⟨(d', ⟨ty, tagger⟩) :: rest⟩ : Map Int Gen.Variant) d
            "variants[discriminant]" =
          mapIndex (⟨rest⟩ : Map Int Gen.Variant) d "variants[discriminant]" := by
        simp only [mapIndex, hget]
      have hdec : ∀ bytes, Type.decodeVariantM (M := M) ((d', ⟨ty, tagger⟩) :: rest) d bytes =
          Type.decodeVariantM (M := M) rest d bytes := by
        intro bytes; rw [Type.decodeVariantM]; simp [hd]
      have hchk : ∀ data m, checkVariantM (M := M) ((d', ⟨ty, tagger⟩) :: rest) d data m =
          checkVariantM (M := M) rest d data m := by
        intro data m; rw [checkVariantM]; simp [hd]
      have henc : ∀ data, Type.encodeVariantM (M := M) ((d', ⟨ty, tagger⟩) :: rest) d data =
          Type.encodeVariantM (M := M) rest d data := by
        intro data; rw [Type.encodeVariantM]; simp [hd]
      rw [hget, hidx]
      refine ⟨fun var h => ?_, fun h => ?_⟩
      · obtain ⟨h1, h2, h3, h4⟩ := ih.1 var h
        exact ⟨h1, fun b => (hdec b).trans (h2 b), fun x m => (hchk x m).trans (h3 x m),
          fun x => (henc x).trans (h4 x)⟩
      · obtain ⟨h1, h2, h3, h4⟩ := ih.2 h
        exact ⟨h1, fun b => (hdec b).trans (h2 b), fun x m => (hchk x m).trans (h3 x m),
          fun x => (henc x).trans (h4 x)⟩

/-! ### `[adv A1]` Universal `Load ⇒ GetDiscriminant` soundness (Mach & MachTB), `Union` validity/roundtrip, non-vtable totality, algebraic `GetMetadata`→`ComputeSize`/`ComputeAlign` composition, and edge-case witnesses -/

/-- **Tree Borrows `Read` idempotence:** for every `Permission` (`Unprot` or `Prot`) and
every tree relation (`Local` or `Foreign`), once a `Read` transition succeeds yielding `p'`,
repeating any number of `Read` transitions at the same relation leaves `p'` unchanged and
never triggers UB. This is the core algebraic invariant enabling `Load ⇒ GetDiscriminant`
soundness on `MachTB` for arbitrary multi-level and overlapping discriminator trees. -/
theorem ep1_tb_permission_read_idempotent (p p' : Gen.Permission) (rel : Gen.NodeRelation)
    (h : Permission.transition p .Read rel = .ok p') :
    Permission.transition p' .Read rel = .ok p' := by
  cases p with
  | Unprot u =>
    cases u <;> cases rel <;>
      simp [Permission.transition, PermissionUnprot.transition,
        PermissionUnprot.local_read, PermissionUnprot.foreign_read,
        ub, bind, Except.bind, pure, Except.pure] at h
    all_goals subst h; rfl
  | Prot u =>
    cases u <;> cases rel <;>
      simp [Permission.transition, PermissionProt.transition,
        PermissionProt.local_read, PermissionProt.foreign_read,
        ub, bind, Except.bind, pure, Except.pure] at h
    all_goals subst h; rfl

mutual
private def ep1NodeReadOk (path : Option Gen.Path) (base len : Nat) : Gen.Node → Prop
  | ⟨children, permissions, _⟩ =>
    let rel : Gen.NodeRelation := if path.isSome then .Local else .Foreign
    (∀ i, base ≤ i → i < base + len →
      ∃ hi : i < permissions.length, ∃ p', Permission.transition permissions[i] .Read rel = .ok p') ∧
    ep1ChildrenReadOk 0 path base len children

private def ep1ChildrenReadOk (childId : Int) (path : Option Gen.Path) (base len : Nat) :
    List Gen.Node → Prop
  | [] => True
  | c :: cs =>
    let subPath : Option Gen.Path :=
      match path with
      | some (head :: tail) => if head == childId then some tail else none
      | _ => none
    ep1NodeReadOk subPath base len c ∧ ep1ChildrenReadOk (childId + 1) path base len cs
end

private theorem ep1_listIndex_eq_getElem {T : Type} {xs : List T} {i : Nat} {what : String} {v : T}
    (h : listIndex xs (Int.ofNat i) what = .ok v) :
    ∃ hi : i < xs.length, xs[i] = v := by
  unfold listIndex at h
  have hnn : (0 : Int) ≤ Int.ofNat i := Int.natCast_nonneg i
  have hto : (Int.ofNat i).toNat = i := Int.toNat_natCast i
  simp only [hnn, ↓reduceIte, hto] at h
  cases hget : xs[i]? with
  | none => simp [hget, specPanic] at h
  | some x =>
    simp only [hget, pure, Except.pure, Except.ok.injEq] at h
    have hi : i < xs.length := (List.getElem?_eq_some_iff.mp hget).1
    have hval : xs[i] = x := (List.getElem?_eq_some_iff.mp hget).2
    exact ⟨hi, hval.trans h⟩

private theorem ep1_listIndex_of_getElem {T : Type} {xs : List T} {i : Nat} (what : String)
    (hi : i < xs.length) :
    listIndex xs (Int.ofNat i) what = .ok xs[i] := by
  unfold listIndex
  have hnn : (0 : Int) ≤ Int.ofNat i := Int.natCast_nonneg i
  have hto : (Int.ofNat i).toNat = i := Int.toNat_natCast i
  simp only [hnn, ↓reduceIte, hto, List.getElem?_eq_getElem hi, pure, Except.pure]

private theorem ep1_listSet_of_lt {T : Type} {xs : List T} {i : Nat} (v : T) (what : String)
    (hi : i < xs.length) :
    listSet xs (Int.ofNat i) v what = .ok (xs.set i v) := by
  unfold listSet
  have hnn : (0 : Int) ≤ Int.ofNat i := Int.natCast_nonneg i
  have hto : (Int.ofNat i).toNat = i := Int.toNat_natCast i
  simp only [hnn, hto, hi, and_self, ↓reduceIte, pure, Except.pure]

private theorem ep1_listSet_eq {T : Type} {xs ys : List T} {i : Nat} {v : T} {what : String}
    (h : listSet xs (Int.ofNat i) v what = .ok ys) :
    i < xs.length ∧ ys = xs.set i v := by
  unfold listSet at h
  have hnn : (0 : Int) ≤ Int.ofNat i := Int.natCast_nonneg i
  have hto : (Int.ofNat i).toNat = i := Int.toNat_natCast i
  simp only [hnn, hto, true_and] at h
  split at h
  · rename_i hi
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨hi, h.symm⟩
  · simp [specPanic] at h

private theorem ep1_listIndex_int_eq_getElem {T : Type} {xs : List T} {idx : Int} {what : String} {v : T}
    (h : listIndex xs idx what = .ok v) :
    0 ≤ idx ∧ ∃ hi : idx.toNat < xs.length, xs[idx.toNat] = v := by
  unfold listIndex at h
  split at h
  · rename_i hnn
    cases hget : xs[idx.toNat]? with
    | none => simp [hget, specPanic] at h
    | some x =>
      simp only [hget, pure, Except.pure, Except.ok.injEq] at h
      have hi : idx.toNat < xs.length := (List.getElem?_eq_some_iff.mp hget).1
      have hval : xs[idx.toNat] = x := (List.getElem?_eq_some_iff.mp hget).2
      exact ⟨hnn, hi, hval.trans h⟩
  · simp [specPanic] at h

private theorem ep1_listIndex_int_of_getElem {T : Type} {xs : List T} {idx : Int} (what : String)
    (hnn : 0 ≤ idx) (hi : idx.toNat < xs.length) :
    listIndex xs idx what = .ok xs[idx.toNat] := by
  unfold listIndex
  simp only [hnn, ↓reduceIte, List.getElem?_eq_getElem hi, pure, Except.pure]

private theorem ep1_listSet_int_of_lt {T : Type} {xs : List T} {idx : Int} (v : T) (what : String)
    (hnn : 0 ≤ idx) (hi : idx.toNat < xs.length) :
    listSet xs idx v what = .ok (xs.set idx.toNat v) := by
  unfold listSet
  simp only [hnn, hi, and_self, ↓reduceIte, pure, Except.pure]

private theorem ep1_transitionRange_read_extract (rel : Gen.NodeRelation) :
    ∀ (off rem : Nat) (perms perms' : List Gen.Permission),
      Node.transitionRange rel .Read off rem perms = .ok perms' →
      perms'.length = perms.length ∧
      (∀ i, off ≤ i → i < off + rem →
        ∃ hi : i < perms.length, ∃ p', Permission.transition perms[i] .Read rel = .ok p')
  | off, 0, perms, perms', h => by
    have hp := ep1_pure_ok h
    subst hp
    exact ⟨rfl, fun i h1 h2 => by omega⟩
  | off, rem + 1, perms, perms', h => by
    unfold Node.transitionRange at h
    obtain ⟨⟨_, perms1⟩, hmut, hrest⟩ := ep1_bind_ok h
    unfold listMutateAt at hmut
    obtain ⟨elem, hidx, hmut⟩ := ep1_bind_ok hmut
    obtain ⟨⟨_, p'⟩, htr_b, hmut⟩ := ep1_bind_ok hmut
    obtain ⟨p1, htr, hp1⟩ := ep1_bind_ok htr_b
    have hp1' := ep1_pure_ok hp1
    rcases Prod.mk.inj hp1' with ⟨_, rfl⟩
    obtain ⟨perms1', hset, hmut⟩ := ep1_bind_ok hmut
    have hm := ep1_pure_ok hmut
    rcases Prod.mk.inj hm with ⟨_, rfl⟩
    obtain ⟨hhi, helem⟩ := ep1_listIndex_eq_getElem hidx
    obtain ⟨_, rfl⟩ := ep1_listSet_eq hset
    obtain ⟨hlen', hsub⟩ :=
      ep1_transitionRange_read_extract rel (off + 1) rem (perms.set off p1) perms' hrest
    refine ⟨by rw [hlen', List.length_set], fun i h1 h2 => ?_⟩
    by_cases heq : i = off
    · subst heq
      exact ⟨hhi, p1, helem ▸ htr⟩
    · obtain ⟨hi1, p2, htr2⟩ := hsub i (by omega) (by omega)
      have hi0 : i < perms.length := by simpa [List.length_set] using hi1
      have hne : off ≠ i := fun h => heq h.symm
      rw [List.getElem_set_ne hne] at htr2
      exact ⟨hi0, p2, htr2⟩

private theorem ep1_transitionRange_read_exec (rel : Gen.NodeRelation) (base len : Nat) :
    ∀ (off rem : Nat) (perms : List Gen.Permission),
      base ≤ off → off + rem ≤ base + len →
      (∀ i, base ≤ i → i < base + len →
        ∃ hi : i < perms.length, ∃ p', Permission.transition perms[i] .Read rel = .ok p') →
      ∃ perms', Node.transitionRange rel .Read off rem perms = .ok perms' ∧
        perms'.length = perms.length ∧
        (∀ i, base ≤ i → i < base + len →
          ∃ hi : i < perms'.length, ∃ p', Permission.transition perms'[i] .Read rel = .ok p')
  | off, 0, perms, _, _, hok => ⟨perms, rfl, rfl, hok⟩
  | off, rem + 1, perms, hlo, hhi, hok => by
    obtain ⟨hoff, p1, htr1⟩ := hok off hlo (by omega)
    have hmut : listMutateAt perms (Int.ofNat off) "Node::transition"
        (fun permission => do
          let p' ← Permission.transition permission .Read rel
          pure ((), p')) = .ok ((), perms.set off p1) := by
      unfold listMutateAt
      rw [ep1_listIndex_of_getElem "Node::transition" hoff]
      simp only [bind, Except.bind, htr1, pure, Except.pure,
        ep1_listSet_of_lt p1 "Node::transition" hoff]
    have hok1 : ∀ i, base ≤ i → i < base + len →
        ∃ hi : i < (perms.set off p1).length,
          ∃ p', Permission.transition (perms.set off p1)[i] .Read rel = .ok p' := by
      intro i hi1 hi2
      by_cases heq : i = off
      · subst heq
        refine ⟨by simpa [List.length_set] using hoff, p1, ?_⟩
        rw [List.getElem_set_self]
        exact ep1_tb_permission_read_idempotent perms[i] p1 rel htr1
      · obtain ⟨hi, p2, htr2⟩ := hok i hi1 hi2
        refine ⟨by simpa [List.length_set] using hi, p2, ?_⟩
        rw [List.getElem_set_ne (fun h => heq h.symm)]
        exact htr2
    obtain ⟨perms', hrest, hlen', hok'⟩ :=
      ep1_transitionRange_read_exec rel base len (off + 1) rem (perms.set off p1)
        (by omega) (by omega) hok1
    refine ⟨perms', ?_, by rw [hlen', List.length_set], hok'⟩
    unfold Node.transitionRange
    rw [hmut]
    exact hrest

mutual
private theorem ep1_node_access_read_extract :
    ∀ (n n' : Gen.Node) (path : Option Gen.Path) (base len : Nat),
      Node.access n path .Read ⟨base⟩ ⟨len⟩ = .ok n' →
      ep1NodeReadOk path base len n
  | ⟨children, perms, prot⟩, n', path, base, len, h => by
    unfold Node.access at h
    obtain ⟨n1, htr, h⟩ := ep1_bind_ok h
    obtain ⟨cs', hcs, _⟩ := ep1_bind_ok h
    unfold Node.transition at htr
    obtain ⟨perms', htrR, _⟩ := ep1_bind_ok htr
    exact ⟨(ep1_transitionRange_read_extract _ base len perms perms' htrR).2,
      ep1_children_access_read_extract children cs' 0 path base len hcs⟩

private theorem ep1_children_access_read_extract :
    ∀ (cs cs' : List Gen.Node) (childId : Int) (path : Option Gen.Path) (base len : Nat),
      Node.accessChildren childId path .Read ⟨base⟩ ⟨len⟩ cs = .ok cs' →
      ep1ChildrenReadOk childId path base len cs
  | [], _, _, _, _, _, _ => trivial
  | c :: rest, cs', childId, path, base, len, h => by
    unfold Node.accessChildren at h
    obtain ⟨c', hc, h⟩ := ep1_bind_ok h
    obtain ⟨rest', hr, _⟩ := ep1_bind_ok h
    exact ⟨ep1_node_access_read_extract c c' _ base len hc,
      ep1_children_access_read_extract rest rest' (childId + 1) path base len hr⟩
end

mutual
private theorem ep1_node_access_read_exec (base len off subLen : Nat)
    (hlo : base ≤ off) (hhi : off + subLen ≤ base + len) :
    ∀ (n : Gen.Node) (path : Option Gen.Path),
      ep1NodeReadOk path base len n →
      ∃ n', Node.access n path .Read ⟨off⟩ ⟨subLen⟩ = .ok n' ∧ ep1NodeReadOk path base len n'
  | ⟨children, perms, prot⟩, path, ⟨hperms, hcs⟩ => by
    obtain ⟨perms', htrR, _, hperms'⟩ :=
      ep1_transitionRange_read_exec (if path.isSome then .Local else .Foreign) base len off subLen
        perms hlo hhi hperms
    obtain ⟨cs', hcsExec, hcs'⟩ :=
      ep1_children_access_read_exec base len off subLen hlo hhi children 0 path hcs
    refine ⟨⟨cs', perms', prot⟩, ?_, ⟨hperms', hcs'⟩⟩
    unfold Node.access Node.transition
    simp only [htrR, hcsExec, bind, Except.bind, pure, Except.pure]

private theorem ep1_children_access_read_exec (base len off subLen : Nat)
    (hlo : base ≤ off) (hhi : off + subLen ≤ base + len) :
    ∀ (cs : List Gen.Node) (childId : Int) (path : Option Gen.Path),
      ep1ChildrenReadOk childId path base len cs →
      ∃ cs', Node.accessChildren childId path .Read ⟨off⟩ ⟨subLen⟩ cs = .ok cs' ∧
        ep1ChildrenReadOk childId path base len cs'
  | [], _, _, _ => ⟨[], rfl, trivial⟩
  | c :: rest, childId, path, ⟨hc, hr⟩ => by
    rcases path with _ | (_ | ⟨head, tail⟩)
    · obtain ⟨c', hcExec, hc'⟩ := ep1_node_access_read_exec base len off subLen hlo hhi c none hc
      obtain ⟨rest', hrExec, hr'⟩ :=
        ep1_children_access_read_exec base len off subLen hlo hhi rest (childId + 1) none hr
      refine ⟨c' :: rest', ?_, ⟨hc', hr'⟩⟩
      simp only [Node.accessChildren, hcExec, hrExec, bind, Except.bind, pure, Except.pure]
    · obtain ⟨c', hcExec, hc'⟩ := ep1_node_access_read_exec base len off subLen hlo hhi c none hc
      obtain ⟨rest', hrExec, hr'⟩ :=
        ep1_children_access_read_exec base len off subLen hlo hhi rest (childId + 1) (some []) hr
      refine ⟨c' :: rest', ?_, ⟨hc', hr'⟩⟩
      simp only [Node.accessChildren, hcExec, hrExec, bind, Except.bind, pure, Except.pure]
    · cases heq : (head == childId)
      · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hc
        obtain ⟨c', hcExec, hc'⟩ := ep1_node_access_read_exec base len off subLen hlo hhi c none hc
        obtain ⟨rest', hrExec, hr'⟩ :=
          ep1_children_access_read_exec base len off subLen hlo hhi rest (childId + 1) (some (head :: tail)) hr
        refine ⟨c' :: rest', ?_, ?_⟩
        · simp only [Node.accessChildren, heq, Bool.false_eq_true, ↓reduceIte, hcExec, hrExec,
            bind, Except.bind, pure, Except.pure]
        · exact ⟨by simpa [heq] using hc', hr'⟩
      · simp only [heq, ↓reduceIte] at hc
        obtain ⟨c', hcExec, hc'⟩ := ep1_node_access_read_exec base len off subLen hlo hhi c (some tail) hc
        obtain ⟨rest', hrExec, hr'⟩ :=
          ep1_children_access_read_exec base len off subLen hlo hhi rest (childId + 1) (some (head :: tail)) hr
        refine ⟨c' :: rest', ?_, ?_⟩
        · simp only [Node.accessChildren, heq, ↓reduceIte, hcExec, hrExec,
            bind, Except.bind, pure, Except.pure]
        · exact ⟨by simpa [heq] using hc', hr'⟩
end

mutual
private theorem ep1_decodeDiscriminantM_sim {M : Type} [Gen.Memory M] {σ : Type}
    (Inv : σ → Prop)
    (acc1 : Unit → Gen.Offset → Size →
      Interp (List (Gen.AbstractByte (Gen.Memory.Provenance M)) × Unit))
    (acc2 : σ → Gen.Offset → Size →
      Interp (List (Gen.AbstractByte (Gen.Memory.Provenance M)) × σ))
    (hstep : ∀ s off sz bs, Inv s → acc1 () off sz = .ok (bs, ()) →
      ∃ s', acc2 s off sz = .ok (bs, s') ∧ Inv s') :
    ∀ (d : Gen.Discriminator) (res : Option Int) (s : σ),
      Inv s → decodeDiscriminantM (M := M) acc1 d () = .ok (res, ()) →
      ∃ s', decodeDiscriminantM (M := M) acc2 d s = .ok (res, s') ∧ Inv s'
  | .Known val, res, s, hinv, h => by
    have hp := ep1_pure_ok h
    rcases Prod.mk.inj hp with ⟨rfl, _⟩
    exact ⟨s, rfl, hinv⟩
  | .Invalid, res, s, hinv, h => by
    have hp := ep1_pure_ok h
    rcases Prod.mk.inj hp with ⟨rfl, _⟩
    exact ⟨s, rfl, hinv⟩
  | .Branch off vt fallback ⟨children⟩, res, s, hinv, h => by
    unfold decodeDiscriminantM at h ⊢
    obtain ⟨⟨bs, u⟩, ha1, h⟩ := ep1_bind_ok h
    cases u
    obtain ⟨s1, ha2, hinv1⟩ := hstep s off vt.size bs hinv ha1
    rw [ha2]
    dsimp only [bind, Except.bind] at h ⊢
    obtain ⟨optv, hdec, h⟩ := ep1_bind_ok h
    rw [hdec]
    dsimp only at h ⊢
    cases optv with
    | none =>
      have hp := ep1_pure_ok h
      rcases Prod.mk.inj hp with ⟨rfl, _⟩
      exact ⟨s1, rfl, hinv1⟩
    | some v =>
      cases v with
      | Int tag =>
        exact ep1_decodeDiscriminantChildrenM_sim Inv acc1 acc2 hstep tag
          (decodeDiscriminantM (M := M) acc1 fallback)
          (decodeDiscriminantM (M := M) acc2 fallback)
          (fun res' s' hinv' hf =>
            ep1_decodeDiscriminantM_sim Inv acc1 acc2 hstep fallback res' s' hinv' hf)
          children res s1 hinv1 h
      | _ =>
        have hp := ep1_pure_ok h
        rcases Prod.mk.inj hp with ⟨rfl, _⟩
        exact ⟨s1, rfl, hinv1⟩

private theorem ep1_decodeDiscriminantChildrenM_sim {M : Type} [Gen.Memory M] {σ : Type}
    (Inv : σ → Prop)
    (acc1 : Unit → Gen.Offset → Size →
      Interp (List (Gen.AbstractByte (Gen.Memory.Provenance M)) × Unit))
    (acc2 : σ → Gen.Offset → Size →
      Interp (List (Gen.AbstractByte (Gen.Memory.Provenance M)) × σ))
    (hstep : ∀ s off sz bs, Inv s → acc1 () off sz = .ok (bs, ()) →
      ∃ s', acc2 s off sz = .ok (bs, s') ∧ Inv s')
    (tag : Int)
    (fb1 : Unit → Interp (Option Int × Unit)) (fb2 : σ → Interp (Option Int × σ))
    (hfb : ∀ res s, Inv s → fb1 () = .ok (res, ()) → ∃ s', fb2 s = .ok (res, s') ∧ Inv s') :
    ∀ (children : List ((Int × Int) × Gen.Discriminator)) (res : Option Int) (s : σ),
      Inv s → decodeDiscriminantChildrenM (M := M) acc1 tag fb1 children () = .ok (res, ()) →
      ∃ s', decodeDiscriminantChildrenM (M := M) acc2 tag fb2 children s = .ok (res, s') ∧ Inv s'
  | [], res, s, hinv, h => hfb res s hinv h
  | ((lo, hi), child) :: rest, res, s, hinv, h => by
    unfold decodeDiscriminantChildrenM at h ⊢
    by_cases hcond : lo ≤ tag ∧ tag < hi
    · simp only [hcond] at h ⊢
      exact ep1_decodeDiscriminantM_sim Inv acc1 acc2 hstep child res s hinv h
    · simp only [hcond] at h ⊢
      exact ep1_decodeDiscriminantChildrenM_sim Inv acc1 acc2 hstep tag fb1 fb2 hfb rest res s hinv h
end

private theorem ep1_subsliceWithLength_eq {T : Type} {xs bs : List T} {start len : Nat}
    (h : subsliceWithLength xs (start : Int) (len : Int) = .ok bs) :
    start + len ≤ xs.length ∧ bs = (xs.drop start).take len := by
  unfold subsliceWithLength at h
  have hts : ((start : Int)).toNat = start := Int.toNat_natCast start
  have htl : ((len : Int)).toNat = len := Int.toNat_natCast len
  split at h
  · rename_i hcond
    simp only [pure, Except.pure, Except.ok.injEq, hts, htl] at h
    exact ⟨by omega, h.symm⟩
  · simp [specPanic] at h

private theorem ep1_subsliceWithLength_of_le {T : Type} (xs : List T) {start len : Nat}
    (h : start + len ≤ xs.length) :
    subsliceWithLength xs (start : Int) (len : Int) = .ok ((xs.drop start).take len) := by
  unfold subsliceWithLength
  have h1 : (0 : Int) ≤ (start : Int) := Int.natCast_nonneg start
  have h2 : (0 : Int) ≤ (len : Int) := Int.natCast_nonneg len
  have h3 : (start : Int) + (len : Int) ≤ (xs.length : Int) := by omega
  simp only [h1, h2, h3, and_self, ↓reduceIte, Int.toNat_natCast, pure, Except.pure]

private theorem ep1_drop_take_subslice {T : Type} (xs : List T) {base sz off subLen : Nat}
    (h : off + subLen ≤ sz) :
    (((xs.drop base).take sz).drop off).take subLen = (xs.drop (base + off)).take subLen := by
  rw [List.drop_take, List.take_take, List.drop_drop]
  have hmin : min subLen (sz - off) = subLen := Nat.min_eq_left (by omega)
  rw [hmin]

private theorem ep1_inBounds_nonneg_signed (n : Nat) (h : (n : Int) < (2 : Int) ^ 63) :
    inBounds (n : Int) .Signed x86_64.PTR_SIZE = true := by
  unfold inBounds x86_64.PTR_SIZE Size.bits
  have hpow : (2 : Int) ^ (8 * 8 - 1) = (2 : Int) ^ 63 := rfl
  have h1 : -((2 : Int) ^ (8 * 8 - 1)) ≤ (n : Int) := by rw [hpow]; omega
  have h2 : (n : Int) < (2 : Int) ^ (8 * 8 - 1) := by rw [hpow]; exact h
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  exact ⟨h1, h2⟩

private theorem ep1_inBounds_unsigned (a : Int) (h0 : 0 ≤ a) (hhi : a < (2 : Int) ^ 64) :
    inBounds a .Unsigned x86_64.PTR_SIZE = true := by
  unfold inBounds x86_64.PTR_SIZE Size.bits
  have hpow : (2 : Int) ^ (8 * 8) = (2 : Int) ^ 64 := rfl
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  exact ⟨h0, by rw [hpow]; exact hhi⟩

private theorem ep1_align_one_is_aligned (addr : Int) : Align.is_aligned ⟨1⟩ addr = true := by
  simp [Align.is_aligned]

private theorem ep1_not_oob_int {x y z : Int} (hx : 0 ≤ x) (hxy : x + y ≤ z) :
    ¬(x < 0 ∨ x + y > z) := by
  rintro (h | h) <;> omega

private theorem ep1_ptrOffsetInboundsM_ok {M : Type} [Gen.Memory M] [MemoryOps M]
    (mc : Gen.Machine M) (ptr : Gen.ThinPointer (Gen.Memory.Provenance M)) (off : Int)
    (hsd : ConcurrentMemory.signed_dereferenceable mc.mem ptr off = .ok ())
    (hib1 : inBounds off .Signed x86_64.PTR_SIZE = true)
    (hib2 : inBounds (ptr.addr + off) .Unsigned x86_64.PTR_SIZE = true) :
    ptrOffsetInboundsM mc ptr off = .ok { ptr with addr := ptr.addr + off } := by
  unfold ptrOffsetInboundsM
  simp only [hsd, hib1, hib2, bind, Except.bind, pure, Except.pure,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]

private theorem ep1_concurrent_load_of_mem_load {M : Type} [Gen.Memory M] [MemoryOps M]
    (cm : Gen.ConcurrentMemory M) (ptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (sz : Size) (al : Align) (at_ : Gen.Atomicity)
    (bs : List (Gen.AbstractByte (Gen.Memory.Provenance M))) (mem' : M)
    (h : MemoryOps.load cm.memory ptr sz al = .ok (bs, mem')) :
    ConcurrentMemory.load cm ptr sz al at_ =
      .ok (bs, { memory := mem', accesses := cm.accesses ++ [⟨.Load, at_, ptr.addr, sz⟩] }) := by
  unfold ConcurrentMemory.load
  simp only [h, bind, Except.bind, pure, Except.pure]

/-- **Universal `Load ⇒ GetDiscriminant` soundness on `MachTB` (`TreeBorrowsMemory`):**
for every enum type, every finite `Discriminator` tree (multi-level, signed/unsigned,
overlapping/repeated tag reads, fallbacks, or zero-sized), and every machine `m` where the
place address/size satisfy MiniRust's pointer bounds (`0 ≤ addr`, `size < 2^63`,
`addr + size < 2^64`), whenever `evalValueM m (.Load place)` succeeds returning
`Value.Variant d data`, `evalValueM m (.GetDiscriminant place)` ALSO succeeds on the exact
same initial machine `m` and returns `(.Int d, .Int dty)`. -/
theorem ep1_evalValueM_load_enum_implies_getDiscriminant_tb
    (m m1 mLoad : MachTB) (place : Gen.PlaceExpr) (rp : Gen.Place TBM)
    (variants : Map Int Gen.Variant) (dty : Gen.IntType) (discr : Gen.Discriminator)
    (sz : Size) (al : Align) (d : Int) (data : Gen.Value TBM)
    (hp : evalPlaceM m place = .ok ((rp, .Enum variants dty discr sz al), m1))
    (haddr0 : 0 ≤ rp.ptr.thin_pointer.addr)
    (hsz : (sz.bytes : Int) < (2 : Int) ^ 63)
    (haddrHi : rp.ptr.thin_pointer.addr + (sz.bytes : Int) < (2 : Int) ^ 64)
    (hload : evalValueM m (.Load place) = .ok ((.Variant d data, .Enum variants dty discr sz al), mLoad)) :
    ∃ mDiscr, evalValueM m (.GetDiscriminant place) = .ok ((.Int d, .Int dty), mDiscr) := by
  unfold evalValueM at hload
  rw [hp] at hload
  dsimp only [bind, Except.bind] at hload
  obtain ⟨⟨v, mLoad'⟩, hpl, hret⟩ := ep1_bind_ok hload
  have hret' := ep1_pure_ok hret
  rcases Prod.mk.inj hret' with ⟨hvt, rfl⟩
  rcases Prod.mk.inj hvt with ⟨rfl, _⟩
  unfold placeLoadM at hpl
  have hal : rp.aligned = true := by
    cases h : rp.aligned
    · simp [h, ub] at hpl
    · rfl
  simp only [hal, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpl
  unfold typedLoadM at hpl
  simp only [Type.layout, LayoutStrategy.expect_size, bind, Except.bind, pure, Except.pure] at hpl
  obtain ⟨⟨bytes, cm⟩, hcmLoad, hpl⟩ := ep1_bind_ok hpl
  obtain ⟨decOpt, hdec, hpl⟩ := ep1_bind_ok hpl
  have hdecSome : decOpt = some (.Variant d data) := by
    cases decOpt with
    | none => simp [ub] at hpl
    | some v' =>
      obtain ⟨_, _, hpl⟩ := ep1_bind_ok hpl
      have hp' := ep1_pure_ok hpl
      rcases Prod.mk.inj hp' with ⟨rfl, _⟩
      rfl
  subst hdecSome
  unfold ConcurrentMemory.load at hcmLoad
  obtain ⟨⟨bytes', tbm'⟩, htbLoad, hcmRet⟩ := ep1_bind_ok hcmLoad
  have hcmRet' := ep1_pure_ok hcmRet
  rcases Prod.mk.inj hcmRet' with ⟨rfl, _⟩
  change TreeBorrowsMemory.load m1.mem.memory rp.ptr.thin_pointer sz ⟨1⟩ = .ok (bytes', tbm') at htbLoad
  unfold TreeBorrowsMemory.load at htbLoad
  obtain ⟨⟨bytes'', bm'⟩, hbmLoad, htbRet⟩ := ep1_bind_ok htbLoad
  have htbRet' := ep1_pure_ok htbRet
  rcases Prod.mk.inj htbRet' with ⟨rfl, _⟩
  unfold BasicMemory.load at hbmLoad
  simp only [ep1_align_one_is_aligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hbmLoad
  obtain ⟨chkOpt, hchk, hbmLoad⟩ := ep1_bind_ok hbmLoad
  have hbytesLen : bytes''.length = sz.bytes := by
    cases chkOpt with
    | none =>
      unfold BasicMemory.check_ptr at hchk
      split at hchk
      · rename_i hsz0
        have hp' := ep1_pure_ok hbmLoad
        rcases Prod.mk.inj hp' with ⟨rfl, _⟩
        exact hsz0.symm
      · cases hpr : rp.ptr.thin_pointer.provenance with
        | none => simp [hpr, ub] at hchk
        | some ip =>
          rcases ip with ⟨id, path⟩
          simp only [hpr] at hchk
          obtain ⟨alloc, _, hchk⟩ := ep1_bind_ok hchk
          split at hchk
          · simp [ub] at hchk
          · split at hchk
            · simp [ub] at hchk
            · have hp' := ep1_pure_ok hchk; cases hp'
    | some trip =>
      rcases trip with ⟨id, path, baseOff⟩
      obtain ⟨alloc, _, hbmLoad⟩ := ep1_bind_ok hbmLoad
      obtain ⟨_, _, hbmLoad⟩ := ep1_bind_ok hbmLoad
      obtain ⟨_, _, hbmLoad⟩ := ep1_bind_ok hbmLoad
      obtain ⟨bs, hsub, hbmLoad⟩ := ep1_bind_ok hbmLoad
      have hp' := ep1_pure_ok hbmLoad
      rcases Prod.mk.inj hp' with ⟨rfl, _⟩
      obtain ⟨hle, rfl⟩ := ep1_subsliceWithLength_eq hsub
      simp [List.length_take, List.length_drop]; omega
  unfold Type.decodeM at hdec
  simp only [hbytesLen, ne_eq, not_true_eq_false, ↓reduceIte] at hdec
  obtain ⟨⟨discrOpt, u⟩, hdd, hdec⟩ := ep1_bind_ok hdec
  cases u
  have hdiscrSome : discrOpt = some d := by
    cases discrOpt with
    | none => simp [pure, Except.pure] at hdec
    | some d' =>
      obtain ⟨vopt, _, hdec⟩ := ep1_bind_ok hdec
      cases vopt with
      | none => simp [pure, Except.pure] at hdec
      | some _ =>
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
          Gen.Value.Variant.injEq] at hdec
        exact congrArg some hdec.1
  subst hdiscrSome
  let accPure := fun (_ : Unit) (offset : Gen.Offset) (s : Size) => do
    let bs ← subsliceWithLength bytes'' offset.bytes s.bytes
    pure (bs, ())
  let accLive := fun (mc : MachTB) (idx : Gen.Offset) (s : Size) => do
    let ptr ← ptrOffsetInboundsM mc rp.ptr.thin_pointer (idx.bytes : Int)
    let (bs, cm) ← ConcurrentMemory.load mc.mem ptr s ⟨1⟩ .None
    pure (bs, { mc with mem := cm })
  have hsim : ∃ mDiscr, decodeDiscriminantM (M := TBM) accLive discr m1 = .ok (some d, mDiscr) := by
    cases chkOpt with
    | none =>
      have hsz0 : sz.bytes = 0 := by
        unfold BasicMemory.check_ptr at hchk
        split at hchk
        · assumption
        · cases hpr : rp.ptr.thin_pointer.provenance with
          | none => simp [hpr, ub] at hchk
          | some ip =>
            simp only [hpr] at hchk
            obtain ⟨alloc, _, hchk⟩ := ep1_bind_ok hchk
            split at hchk
            · simp [ub] at hchk
            · split at hchk
              · simp [ub] at hchk
              · have hp' := ep1_pure_ok hchk; cases hp'
      have hbytesNil : bytes'' = [] := List.eq_nil_of_length_eq_zero (hbytesLen.trans hsz0)
      subst hbytesNil
      let Inv : MachTB → Prop := fun mc => mc.mem.memory = m1.mem.memory
      have hstep : ∀ mc off s bs, Inv mc → accPure () off s = .ok (bs, ()) →
          ∃ mc', accLive mc off s = .ok (bs, mc') ∧ Inv mc' := by
        intro mc off s bs hinv ha
        obtain ⟨bs', hsub, hret⟩ := ep1_bind_ok ha
        have hret' := ep1_pure_ok hret
        rcases Prod.mk.inj hret' with ⟨rfl, _⟩
        obtain ⟨hle, rfl⟩ := ep1_subsliceWithLength_eq hsub
        have hoff0 : off.bytes = 0 := by simp at hle; omega
        have hs0 : s.bytes = 0 := by simp at hle; omega
        have hpoi : ptrOffsetInboundsM mc rp.ptr.thin_pointer (off.bytes : Int) = .ok rp.ptr.thin_pointer := by
          have hsd : ConcurrentMemory.signed_dereferenceable mc.mem rp.ptr.thin_pointer (off.bytes : Int) = .ok () := by
            unfold ConcurrentMemory.signed_dereferenceable
            change TreeBorrowsMemory.signed_dereferenceable mc.mem.memory rp.ptr.thin_pointer (off.bytes : Int) = .ok ()
            simp only [TreeBorrowsMemory.signed_dereferenceable, TreeBorrowsMemory.dereferenceable,
              BasicMemory.check_ptr, hoff0, Int.natCast_zero, Int.lt_irrefl, ↓reduceIte, Int.neg_zero,
              Int.toNat_zero, bind, Except.bind, pure, Except.pure]
          have hib1 : inBounds (off.bytes : Int) .Signed x86_64.PTR_SIZE = true :=
            ep1_inBounds_nonneg_signed off.bytes (by rw [hoff0]; omega)
          have hib2 : inBounds (rp.ptr.thin_pointer.addr + (off.bytes : Int)) .Unsigned x86_64.PTR_SIZE = true :=
            ep1_inBounds_unsigned _ (by rw [hoff0]; simp [haddr0])
              (by rw [hsz0] at haddrHi; rw [hoff0]; omega)
          rw [ep1_ptrOffsetInboundsM_ok mc rp.ptr.thin_pointer (off.bytes : Int) hsd hib1 hib2]
          simp only [hoff0, Int.natCast_zero, Int.add_zero]
        have hld : ConcurrentMemory.load mc.mem rp.ptr.thin_pointer s ⟨1⟩ .None =
            .ok ([], { mc.mem with accesses := mc.mem.accesses ++ [⟨.Load, .None, rp.ptr.thin_pointer.addr, s⟩] }) := by
          apply ep1_concurrent_load_of_mem_load
          change TreeBorrowsMemory.load mc.mem.memory rp.ptr.thin_pointer s ⟨1⟩ = .ok ([], mc.mem.memory)
          simp only [TreeBorrowsMemory.load, BasicMemory.load,
            ep1_align_one_is_aligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            BasicMemory.check_ptr, hs0, bind, Except.bind, pure, Except.pure]
        refine ⟨{ mc with mem := { mc.mem with accesses := mc.mem.accesses ++ [⟨.Load, .None, rp.ptr.thin_pointer.addr, s⟩] } }, ?_, hinv⟩
        dsimp only [accLive]
        rw [hpoi]
        simp only [bind, Except.bind, hld, pure, Except.pure, List.drop_nil, List.take_nil]
      obtain ⟨mDiscr, hmDiscr, _⟩ :=
        ep1_decodeDiscriminantM_sim Inv accPure accLive hstep discr (some d) m1 rfl hdd
      exact ⟨mDiscr, hmDiscr⟩
    | some trip =>
      rcases trip with ⟨id, path, baseOff⟩
      unfold BasicMemory.check_ptr at hchk
      have hszPos : sz.bytes ≠ 0 := by
        intro h0; simp [h0, pure, Except.pure] at hchk
      simp only [hszPos, ↓reduceIte] at hchk
      have hprov : rp.ptr.thin_pointer.provenance = some (id, path) := by
        cases hpr : rp.ptr.thin_pointer.provenance with
        | none => simp [hpr, ub] at hchk
        | some ip =>
          rcases ip with ⟨id', path'⟩
          simp only [hpr] at hchk
          obtain ⟨alloc, _, hchk⟩ := ep1_bind_ok hchk
          split at hchk
          · simp [ub] at hchk
          · split at hchk
            · simp [ub] at hchk
            · have hp' := ep1_pure_ok hchk
              simp only [Option.some.injEq, Prod.mk.injEq] at hp'
              rcases hp' with ⟨rfl, rfl, _⟩
              rfl
      simp only [hprov] at hchk
      obtain ⟨alloc0, hidx0, hchk⟩ := ep1_bind_ok hchk
      have hlive0 : alloc0.live = true := by
        cases hl : alloc0.live
        · simp [hl, ub] at hchk
        · rfl
      simp only [hlive0, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hchk
      have hbounds0 : ¬(rp.ptr.thin_pointer.addr - alloc0.addr < 0 ∨
          rp.ptr.thin_pointer.addr - alloc0.addr + (sz.bytes : Int) > (Allocation.size alloc0).bytes) := by
        intro hbad; simp [hbad, ub] at hchk
      simp only [hbounds0, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Option.some.injEq,
        Prod.mk.injEq] at hchk
      rcases hchk with ⟨_, _, hbaseOff⟩
      obtain ⟨alloc0', hidx0', hbmLoad⟩ := ep1_bind_ok hbmLoad
      have hallocEq : alloc0' = alloc0 := by rw [hidx0] at hidx0'; cases hidx0'; rfl
      subst alloc0'
      obtain ⟨extra', hextra, hbmLoad⟩ := ep1_bind_ok hbmLoad
      obtain ⟨root', hnodeAcc, _⟩ := ep1_bind_ok hextra
      obtain ⟨allocs', _, hbmLoad⟩ := ep1_bind_ok hbmLoad
      obtain ⟨bs0, hsub0, hbmLoad⟩ := ep1_bind_ok hbmLoad
      have hbmRet := ep1_pure_ok hbmLoad
      rcases Prod.mk.inj hbmRet with ⟨rfl, _⟩
      obtain ⟨hle0, rfl⟩ := ep1_subsliceWithLength_eq hsub0
      have hreadOk0 : ep1NodeReadOk (some path) baseOff.bytes sz.bytes alloc0.extra.root :=
        ep1_node_access_read_extract alloc0.extra.root root' (some path) baseOff.bytes sz.bytes hnodeAcc
      have hbaseOffNat : (rp.ptr.thin_pointer.addr - alloc0.addr) = (baseOff.bytes : Int) := by
        have hnotlt : ¬((rp.ptr.thin_pointer.addr : Int) - (alloc0.addr : Int) < (0 : Int)) :=
          fun h => hbounds0 (Or.inl h)
        have hnn : (0 : Int) ≤ (rp.ptr.thin_pointer.addr : Int) - (alloc0.addr : Int) :=
          Int.not_lt.mp hnotlt
        have hb : baseOff.bytes = (rp.ptr.thin_pointer.addr - alloc0.addr).toNat := by
          cases hbaseOff; rfl
        rw [hb]; exact (Int.toNat_of_nonneg hnn).symm
      let Inv : MachTB → Prop := fun mc =>
        ∃ allocC, listIndex mc.mem.memory.mem.allocations id._0 "self.allocations[id.0]" = .ok allocC ∧
          allocC.data = alloc0.data ∧ allocC.addr = alloc0.addr ∧ allocC.live = true ∧
          ep1NodeReadOk (some path) baseOff.bytes sz.bytes allocC.extra.root
      have hinv0 : Inv m1 := ⟨alloc0, hidx0, rfl, rfl, hlive0, hreadOk0⟩
      have hstep : ∀ mc off s bs, Inv mc → accPure () off s = .ok (bs, ()) →
          ∃ mc', accLive mc off s = .ok (bs, mc') ∧ Inv mc' := by
        intro mc off s bs ⟨allocC, hidxC, hdataC, haddrC, hliveC, hreadOkC⟩ ha
        obtain ⟨bs', hsub, hret⟩ := ep1_bind_ok ha
        have hret' := ep1_pure_ok hret
        rcases Prod.mk.inj hret' with ⟨rfl, _⟩
        obtain ⟨hleSub, rfl⟩ := ep1_subsliceWithLength_eq hsub
        have hsubLeSz : off.bytes + s.bytes ≤ sz.bytes := by
          rw [hbytesLen] at hleSub; exact hleSub
        have hptrEq : (rp.ptr.thin_pointer.addr : Int) - (allocC.addr : Int) = (baseOff.bytes : Int) := by
          rw [haddrC]; exact hbaseOffNat
        have hpoi : ptrOffsetInboundsM mc rp.ptr.thin_pointer (off.bytes : Int) =
            .ok { rp.ptr.thin_pointer with addr := rp.ptr.thin_pointer.addr + (off.bytes : Int) } := by
          have hsd : ConcurrentMemory.signed_dereferenceable mc.mem rp.ptr.thin_pointer (off.bytes : Int) = .ok () := by
            unfold ConcurrentMemory.signed_dereferenceable
            change TreeBorrowsMemory.signed_dereferenceable mc.mem.memory rp.ptr.thin_pointer (off.bytes : Int) = .ok ()
            unfold TreeBorrowsMemory.signed_dereferenceable TreeBorrowsMemory.dereferenceable
            by_cases hoff0 : off.bytes = 0
            · simp only [hoff0, Int.natCast_zero, Int.lt_irrefl, ↓reduceIte, Int.neg_zero, Int.toNat_zero,
                BasicMemory.check_ptr, bind, Except.bind, pure, Except.pure]
            · have hoffPos : (off.bytes : Int) > 0 := by omega
              simp only [hoffPos, ↓reduceIte, Int.toNat_natCast]
              unfold BasicMemory.check_ptr
              simp only [hoff0, ↓reduceIte, hprov, hidxC, hliveC, Bool.not_true, Bool.false_eq_true,
                bind, Except.bind]
              have hnotOob : ¬(rp.ptr.thin_pointer.addr - allocC.addr < 0 ∨
                  rp.ptr.thin_pointer.addr - allocC.addr + (off.bytes : Int) > (Allocation.size allocC).bytes) := by
                unfold Allocation.size; dsimp only
                rw [hdataC, hptrEq]
                exact ep1_not_oob_int (Int.natCast_nonneg _) (by omega)
              simp only [hnotOob, ↓reduceIte, pure, Except.pure]
          have hib1 : inBounds (off.bytes : Int) .Signed x86_64.PTR_SIZE = true :=
            ep1_inBounds_nonneg_signed off.bytes (by omega)
          have hib2 : inBounds (rp.ptr.thin_pointer.addr + (off.bytes : Int)) .Unsigned x86_64.PTR_SIZE = true :=
            ep1_inBounds_unsigned ((rp.ptr.thin_pointer.addr : Int) + (off.bytes : Int))
              (Int.add_nonneg haddr0 (Int.natCast_nonneg _))
              (Int.lt_of_le_of_lt
                (Int.add_le_add_left (Int.ofNat_le.mpr (Nat.le_trans (Nat.le_add_right _ _) hsubLeSz)) _)
                haddrHi)
          exact ep1_ptrOffsetInboundsM_ok mc rp.ptr.thin_pointer (off.bytes : Int) hsd hib1 hib2
        by_cases hs0 : s.bytes = 0
        · have hld : ConcurrentMemory.load mc.mem
              { rp.ptr.thin_pointer with addr := rp.ptr.thin_pointer.addr + (off.bytes : Int) }
              s ⟨1⟩ .None =
              .ok ([], { mc.mem with accesses := mc.mem.accesses ++
                [⟨.Load, .None, rp.ptr.thin_pointer.addr + (off.bytes : Int), s⟩] }) := by
            apply ep1_concurrent_load_of_mem_load
            change TreeBorrowsMemory.load mc.mem.memory
                { rp.ptr.thin_pointer with addr := rp.ptr.thin_pointer.addr + (off.bytes : Int) }
                s ⟨1⟩ = .ok ([], mc.mem.memory)
            simp only [TreeBorrowsMemory.load, BasicMemory.load,
              ep1_align_one_is_aligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              BasicMemory.check_ptr, hs0, bind, Except.bind, pure, Except.pure]
          refine ⟨{ mc with mem := { mc.mem with accesses := mc.mem.accesses ++
              [⟨.Load, .None, rp.ptr.thin_pointer.addr + (off.bytes : Int), s⟩] } }, ?_,
            ⟨allocC, hidxC, hdataC, haddrC, hliveC, hreadOkC⟩⟩
          dsimp only [accLive]
          rw [hpoi]
          simp only [bind, Except.bind, hld, hs0, List.take_zero, pure, Except.pure]
        · have hchkSub : BasicMemory.check_ptr mc.mem.memory.mem
              { rp.ptr.thin_pointer with addr := rp.ptr.thin_pointer.addr + (off.bytes : Int) } s =
              .ok (some (id, path, ⟨baseOff.bytes + off.bytes⟩)) := by
            unfold BasicMemory.check_ptr
            simp only [hs0, ↓reduceIte, hprov, hidxC, hliveC, Bool.not_true, Bool.false_eq_true,
              bind, Except.bind]
            have hdiff : (rp.ptr.thin_pointer.addr : Int) + (off.bytes : Int) - (allocC.addr : Int) =
                ((baseOff.bytes + off.bytes : Nat) : Int) := by
              have hcomm : ∀ (x y z : Int), x + y - z = (x - z) + y := fun x y z => by omega
              rw [hcomm, hptrEq]
              exact (Int.natCast_add _ _).symm
            have hnotOob : ¬(rp.ptr.thin_pointer.addr + (off.bytes : Int) - allocC.addr < 0 ∨
                rp.ptr.thin_pointer.addr + (off.bytes : Int) - allocC.addr + (s.bytes : Int) >
                  (Allocation.size allocC).bytes) := by
              unfold Allocation.size; dsimp only
              rw [hdataC, hdiff]
              exact ep1_not_oob_int (Int.natCast_nonneg _) (by omega)
            simp only [hnotOob, ↓reduceIte]
            simp only [hdiff, Int.toNat_natCast, pure, Except.pure]
          obtain ⟨rootC', hnodeAccC, hreadOkC'⟩ :=
            ep1_node_access_read_exec baseOff.bytes sz.bytes (baseOff.bytes + off.bytes) s.bytes
              (by omega) (by omega) allocC.extra.root (some path) hreadOkC
          obtain ⟨hidNN, hidLt, _⟩ := ep1_listIndex_int_eq_getElem hidxC
          let allocC' : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra :=
            { allocC with extra := { root := rootC' } }
          have hsetC : listSet mc.mem.memory.mem.allocations id._0
              { data := allocC.data, addr := allocC.addr, align := allocC.align, kind := allocC.kind,
                live := allocC.live, extra := { root := rootC' } } "set" =
              .ok (mc.mem.memory.mem.allocations.set id._0.toNat allocC') :=
            ep1_listSet_int_of_lt allocC' "set" hidNN hidLt
          have hsubC : subsliceWithLength allocC.data ((baseOff.bytes + off.bytes : Nat) : Int) (s.bytes : Int) =
              .ok ((alloc0.data.drop (baseOff.bytes + off.bytes)).take s.bytes) := by
            rw [hdataC]
            exact ep1_subsliceWithLength_of_le alloc0.data (by omega)
          let cmNext : Gen.ConcurrentMemory TBM :=
            { memory := { mc.mem.memory with
                mem := { mc.mem.memory.mem with
                  allocations := mc.mem.memory.mem.allocations.set id._0.toNat allocC' } },
              accesses := mc.mem.accesses ++
                [⟨.Load, .None, rp.ptr.thin_pointer.addr + (off.bytes : Int), s⟩] }
          have hld : ConcurrentMemory.load mc.mem
              { rp.ptr.thin_pointer with addr := rp.ptr.thin_pointer.addr + (off.bytes : Int) }
              s ⟨1⟩ .None =
              .ok (((alloc0.data.drop (baseOff.bytes + off.bytes)).take s.bytes), cmNext) := by
            apply ep1_concurrent_load_of_mem_load
            change TreeBorrowsMemory.load mc.mem.memory
                { rp.ptr.thin_pointer with addr := rp.ptr.thin_pointer.addr + (off.bytes : Int) }
                s ⟨1⟩ = .ok (((alloc0.data.drop (baseOff.bytes + off.bytes)).take s.bytes), cmNext.memory)
            unfold TreeBorrowsMemory.load BasicMemory.load
            simp only [ep1_align_one_is_aligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              hchkSub, hidxC, hnodeAccC, hsetC, hsubC, bind, Except.bind, pure, Except.pure]
            rfl
          refine ⟨{ mc with mem := cmNext }, ?_, ?_⟩
          · dsimp only [accLive]
            rw [hpoi]
            simp only [bind, Except.bind, hld, pure, Except.pure, ep1_drop_take_subslice alloc0.data hsubLeSz]
          · refine ⟨allocC', ?_, hdataC, haddrC, hliveC, hreadOkC'⟩
            have hlt' : id._0.toNat < (mc.mem.memory.mem.allocations.set id._0.toNat allocC').length := by
              simpa [List.length_set] using hidLt
            rw [ep1_listIndex_int_of_getElem "self.allocations[id.0]" hidNN hlt', List.getElem_set_self]
      obtain ⟨mDiscr, hmDiscr, _⟩ :=
        ep1_decodeDiscriminantM_sim Inv accPure accLive hstep discr (some d) m1 hinv0 hdd
      exact ⟨mDiscr, hmDiscr⟩
  obtain ⟨mDiscr, hmDiscr⟩ := hsim
  refine ⟨mDiscr, ?_⟩
  unfold evalValueM
  rw [hp]
  simp only [hal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
  simp only [accLive, bind, Except.bind] at hmDiscr
  rw [hmDiscr]
  rfl

/-- **Universal `Load ⇒ GetDiscriminant` soundness on `Mach` (`BasicMemory`):**
whenever `evalValue m (.Load place)` succeeds returning `Value.Variant d data` at an enum
place satisfying MiniRust's pointer bounds, `evalValue m (.GetDiscriminant place)` ALSO
succeeds returning `(.Int d, .Int dty)` with identical underlying memory
(`mDiscr.mem.memory = mLoad.mem.memory`). -/
theorem ep1_evalValue_load_enum_implies_getDiscriminant_bm
    (m m1 mLoad : Mach) (place : Gen.PlaceExpr) (rp : Gen.Place BM)
    (variants : Map Int Gen.Variant) (dty : Gen.IntType) (discr : Gen.Discriminator)
    (sz : Size) (al : Align) (d : Int) (data : Val)
    (hp : evalPlace m place = .ok ((rp, .Enum variants dty discr sz al), m1))
    (haddr0 : 0 ≤ rp.ptr.thin_pointer.addr)
    (hsz : (sz.bytes : Int) < (2 : Int) ^ 63)
    (haddrHi : rp.ptr.thin_pointer.addr + (sz.bytes : Int) < (2 : Int) ^ 64)
    (hload : evalValue m (.Load place) = .ok ((.Variant d data, .Enum variants dty discr sz al), mLoad)) :
    ∃ mDiscr, evalValue m (.GetDiscriminant place) = .ok ((.Int d, .Int dty), mDiscr) ∧
      mDiscr.mem.memory = mLoad.mem.memory := by
  rw [← evalPlaceM_bm_eq] at hp
  rw [← evalValueM_bm_eq] at hload
  suffices h : ∃ mDiscr, evalValueM (M := BM) m (.GetDiscriminant place) = .ok ((.Int d, .Int dty), mDiscr) ∧
      mDiscr.mem.memory = mLoad.mem.memory by
    obtain ⟨mDiscr, h1, h2⟩ := h
    rw [evalValueM_bm_eq] at h1
    exact ⟨mDiscr, h1, h2⟩
  unfold evalValueM at hload
  rw [hp] at hload
  dsimp only [bind, Except.bind] at hload
  obtain ⟨⟨v, mLoad'⟩, hpl, hret⟩ := ep1_bind_ok hload
  have hret' := ep1_pure_ok hret
  rcases Prod.mk.inj hret' with ⟨hvt, rfl⟩
  rcases Prod.mk.inj hvt with ⟨rfl, _⟩
  unfold placeLoadM at hpl
  have hal : rp.aligned = true := by
    cases h : rp.aligned
    · simp [h, ub] at hpl
    · rfl
  simp only [hal, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpl
  unfold typedLoadM at hpl
  simp only [Type.layout, LayoutStrategy.expect_size, bind, Except.bind, pure, Except.pure] at hpl
  obtain ⟨⟨bytes, cm⟩, hcmLoad, hpl⟩ := ep1_bind_ok hpl
  obtain ⟨decOpt, hdec, hpl⟩ := ep1_bind_ok hpl
  have hdecSome : decOpt = some (.Variant d data) := by
    cases decOpt with
    | none => simp [ub] at hpl
    | some v' =>
      obtain ⟨_, _, hpl⟩ := ep1_bind_ok hpl
      have hp' := ep1_pure_ok hpl
      rcases Prod.mk.inj hp' with ⟨rfl, _⟩
      rfl
  subst hdecSome
  have hmLoadMem : mLoad'.mem.memory = cm.memory := by
    obtain ⟨_, _, hpl⟩ := ep1_bind_ok hpl
    have hp' := ep1_pure_ok hpl
    rcases Prod.mk.inj hp' with ⟨_, rfl⟩
    rfl
  unfold ConcurrentMemory.load at hcmLoad
  obtain ⟨⟨bytes', bm'⟩, hbmLoad, hcmRet⟩ := ep1_bind_ok hcmLoad
  have hcmRet' := ep1_pure_ok hcmRet
  rcases Prod.mk.inj hcmRet' with ⟨rfl, rfl⟩
  change BM.load m1.mem.memory rp.ptr.thin_pointer sz ⟨1⟩ = .ok (bytes', bm') at hbmLoad
  unfold BM.load at hbmLoad
  simp only [ep1_align_one_is_aligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hbmLoad
  obtain ⟨chkOpt, hchk, hbmLoad⟩ := ep1_bind_ok hbmLoad
  have hbmMemEq : bm' = m1.mem.memory := by
    cases chkOpt with
    | none =>
      have hp' := ep1_pure_ok hbmLoad
      rcases Prod.mk.inj hp' with ⟨_, rfl⟩; rfl
    | some trip =>
      rcases trip with ⟨id, _, baseOff⟩
      obtain ⟨alloc, hidx, hbmLoad⟩ := ep1_bind_ok hbmLoad
      obtain ⟨allocs', hset, hbmLoad⟩ := ep1_bind_ok hbmLoad
      obtain ⟨_, _, hbmLoad⟩ := ep1_bind_ok hbmLoad
      have hp' := ep1_pure_ok hbmLoad
      rcases Prod.mk.inj hp' with ⟨_, rfl⟩
      obtain ⟨hidNN, hidLt, helem⟩ := ep1_listIndex_int_eq_getElem hidx
      have hsetEq := ep1_listSet_int_of_lt alloc "set" hidNN hidLt
      rw [hsetEq] at hset; cases hset
      rw [← helem, List.set_getElem_self]
  have hbytesLen : bytes'.length = sz.bytes := by
    cases chkOpt with
    | none =>
      unfold BM.check_ptr at hchk
      split at hchk
      · rename_i hsz0
        have hp' := ep1_pure_ok hbmLoad
        rcases Prod.mk.inj hp' with ⟨rfl, _⟩
        exact hsz0.symm
      · cases hpr : rp.ptr.thin_pointer.provenance with
        | none => simp [hpr, ub] at hchk
        | some ip =>
          simp only [hpr] at hchk
          obtain ⟨alloc, _, hchk⟩ := ep1_bind_ok hchk
          split at hchk
          · simp [ub] at hchk
          · split at hchk
            · simp [ub] at hchk
            · have hp' := ep1_pure_ok hchk; cases hp'
    | some trip =>
      rcases trip with ⟨id, _, baseOff⟩
      obtain ⟨alloc, _, hbmLoad⟩ := ep1_bind_ok hbmLoad
      obtain ⟨_, _, hbmLoad⟩ := ep1_bind_ok hbmLoad
      obtain ⟨bs, hsub, hbmLoad⟩ := ep1_bind_ok hbmLoad
      have hp' := ep1_pure_ok hbmLoad
      rcases Prod.mk.inj hp' with ⟨rfl, _⟩
      obtain ⟨hle, rfl⟩ := ep1_subsliceWithLength_eq hsub
      simp [List.length_take, List.length_drop]; omega
  unfold Type.decodeM at hdec
  simp only [hbytesLen, ne_eq, not_true_eq_false, ↓reduceIte] at hdec
  obtain ⟨⟨discrOpt, u⟩, hdd, hdec⟩ := ep1_bind_ok hdec
  cases u
  have hdiscrSome : discrOpt = some d := by
    cases discrOpt with
    | none => simp [pure, Except.pure] at hdec
    | some d' =>
      obtain ⟨vopt, _, hdec⟩ := ep1_bind_ok hdec
      cases vopt with
      | none => simp [pure, Except.pure] at hdec
      | some _ =>
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
          Gen.Value.Variant.injEq] at hdec
        exact congrArg some hdec.1
  subst hdiscrSome
  let accPure := fun (_ : Unit) (offset : Gen.Offset) (s : Size) => do
    let bs ← subsliceWithLength bytes' offset.bytes s.bytes
    pure (bs, ())
  let accLive := fun (mc : Mach) (idx : Gen.Offset) (s : Size) => do
    let ptr ← ptrOffsetInboundsM (M := BM) mc rp.ptr.thin_pointer (idx.bytes : Int)
    let (bs, cm) ← ConcurrentMemory.load (M := BM) mc.mem ptr s ⟨1⟩ .None
    pure (bs, { mc with mem := cm })
  let Inv : Mach → Prop := fun mc => mc.mem.memory = m1.mem.memory
  have hsim : ∃ mDiscr, decodeDiscriminantM (M := BM) accLive discr m1 = .ok (some d, mDiscr) ∧ Inv mDiscr := by
    cases chkOpt with
    | none =>
      have hsz0 : sz.bytes = 0 := by
        unfold BM.check_ptr at hchk
        split at hchk
        · assumption
        · cases hpr : rp.ptr.thin_pointer.provenance with
          | none => simp [hpr, ub] at hchk
          | some ip =>
            simp only [hpr] at hchk
            obtain ⟨alloc, _, hchk⟩ := ep1_bind_ok hchk
            split at hchk
            · simp [ub] at hchk
            · split at hchk
              · simp [ub] at hchk
              · have hp' := ep1_pure_ok hchk; cases hp'
      have hbytesNil : bytes' = [] := List.eq_nil_of_length_eq_zero (hbytesLen.trans hsz0)
      subst hbytesNil
      have hstep : ∀ mc off s bs, Inv mc → accPure () off s = .ok (bs, ()) →
          ∃ mc', accLive mc off s = .ok (bs, mc') ∧ Inv mc' := by
        intro mc off s bs hinv ha
        obtain ⟨bs', hsub, hret⟩ := ep1_bind_ok ha
        have hret' := ep1_pure_ok hret
        rcases Prod.mk.inj hret' with ⟨rfl, _⟩
        obtain ⟨hle, rfl⟩ := ep1_subsliceWithLength_eq hsub
        have hoff0 : off.bytes = 0 := by simp at hle; omega
        have hs0 : s.bytes = 0 := by simp at hle; omega
        have hpoi : ptrOffsetInboundsM (M := BM) mc rp.ptr.thin_pointer (off.bytes : Int) = .ok rp.ptr.thin_pointer := by
          have hsd : ConcurrentMemory.signed_dereferenceable (M := BM) mc.mem rp.ptr.thin_pointer (off.bytes : Int) = .ok () := by
            unfold ConcurrentMemory.signed_dereferenceable
            change BM.signed_dereferenceable mc.mem.memory rp.ptr.thin_pointer (off.bytes : Int) = .ok ()
            simp only [BM.signed_dereferenceable, BM.dereferenceable, BM.check_ptr, hoff0,
              Int.natCast_zero, Int.lt_irrefl, ↓reduceIte, Int.neg_zero, Int.toNat_zero,
              bind, Except.bind, pure, Except.pure]
          have hib1 : inBounds (off.bytes : Int) .Signed x86_64.PTR_SIZE = true :=
            ep1_inBounds_nonneg_signed off.bytes (by rw [hoff0]; omega)
          have hib2 : inBounds (rp.ptr.thin_pointer.addr + (off.bytes : Int)) .Unsigned x86_64.PTR_SIZE = true :=
            ep1_inBounds_unsigned _ (by rw [hoff0]; simp [haddr0])
              (by rw [hsz0] at haddrHi; rw [hoff0]; omega)
          rw [ep1_ptrOffsetInboundsM_ok (M := BM) mc rp.ptr.thin_pointer (off.bytes : Int) hsd hib1 hib2]
          simp only [hoff0, Int.natCast_zero, Int.add_zero]
        have hld : ConcurrentMemory.load (M := BM) mc.mem rp.ptr.thin_pointer s ⟨1⟩ .None =
            .ok ([], { mc.mem with accesses := mc.mem.accesses ++ [⟨.Load, .None, rp.ptr.thin_pointer.addr, s⟩] }) := by
          apply ep1_concurrent_load_of_mem_load (M := BM)
          change BM.load mc.mem.memory rp.ptr.thin_pointer s ⟨1⟩ = .ok ([], mc.mem.memory)
          simp only [BM.load, ep1_align_one_is_aligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            BM.check_ptr, hs0, bind, Except.bind, pure, Except.pure]
        refine ⟨{ mc with mem := { mc.mem with accesses := mc.mem.accesses ++ [⟨.Load, .None, rp.ptr.thin_pointer.addr, s⟩] } }, ?_, hinv⟩
        dsimp only [accLive]
        rw [hpoi]
        simp only [bind, Except.bind, hld, pure, Except.pure, List.drop_nil, List.take_nil]
      exact ep1_decodeDiscriminantM_sim Inv accPure accLive hstep discr (some d) m1 rfl hdd
    | some trip =>
      rcases trip with ⟨id, pu, baseOff⟩
      cases pu
      unfold BM.check_ptr at hchk
      have hszPos : sz.bytes ≠ 0 := by
        intro h0; simp [h0, pure, Except.pure] at hchk
      simp only [hszPos, ↓reduceIte] at hchk
      have hprov : rp.ptr.thin_pointer.provenance = some (id, ()) := by
        cases hpr : rp.ptr.thin_pointer.provenance with
        | none => simp [hpr, ub] at hchk
        | some ip =>
          rcases ip with ⟨id', pu'⟩
          cases pu'
          simp only [hpr] at hchk
          obtain ⟨alloc, _, hchk⟩ := ep1_bind_ok hchk
          split at hchk
          · simp [ub] at hchk
          · split at hchk
            · simp [ub] at hchk
            · have hp' := ep1_pure_ok hchk
              simp only [Option.some.injEq, Prod.mk.injEq] at hp'
              rcases hp' with ⟨rfl, _, _⟩
              rfl
      simp only [hprov] at hchk
      obtain ⟨alloc0, hidx0, hchk⟩ := ep1_bind_ok hchk
      have hlive0 : alloc0.live = true := by
        cases hl : alloc0.live
        · simp [hl, ub] at hchk
        · rfl
      simp only [hlive0, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hchk
      have hbounds0 : ¬(rp.ptr.thin_pointer.addr - alloc0.addr < 0 ∨
          rp.ptr.thin_pointer.addr - alloc0.addr + (sz.bytes : Int) > (Allocation.size alloc0).bytes) := by
        intro hbad; simp [hbad, ub] at hchk
      simp only [hbounds0, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Option.some.injEq,
        Prod.mk.injEq] at hchk
      rcases hchk with ⟨_, _, hbaseOff⟩
      obtain ⟨alloc0', hidx0', hbmLoad⟩ := ep1_bind_ok hbmLoad
      have hallocEq : alloc0' = alloc0 := by rw [hidx0] at hidx0'; cases hidx0'; rfl
      subst alloc0'
      obtain ⟨_, _, hbmLoad⟩ := ep1_bind_ok hbmLoad
      obtain ⟨bs0, hsub0, hbmLoad⟩ := ep1_bind_ok hbmLoad
      have hbmRet := ep1_pure_ok hbmLoad
      rcases Prod.mk.inj hbmRet with ⟨rfl, _⟩
      obtain ⟨hle0, rfl⟩ := ep1_subsliceWithLength_eq hsub0
      have hbaseOffNat : (rp.ptr.thin_pointer.addr : Int) - (alloc0.addr : Int) = (baseOff.bytes : Int) := by
        have hnotlt : ¬((rp.ptr.thin_pointer.addr : Int) - (alloc0.addr : Int) < (0 : Int)) :=
          fun h => hbounds0 (Or.inl h)
        have hnn : (0 : Int) ≤ (rp.ptr.thin_pointer.addr : Int) - (alloc0.addr : Int) :=
          Int.not_lt.mp hnotlt
        have hb : baseOff.bytes = (rp.ptr.thin_pointer.addr - alloc0.addr).toNat := by
          cases hbaseOff; rfl
        rw [hb]; exact (Int.toNat_of_nonneg hnn).symm
      have hstep : ∀ mc off s bs, Inv mc → accPure () off s = .ok (bs, ()) →
          ∃ mc', accLive mc off s = .ok (bs, mc') ∧ Inv mc' := by
        intro mc off s bs hinv ha
        obtain ⟨bs', hsub, hret⟩ := ep1_bind_ok ha
        have hret' := ep1_pure_ok hret
        rcases Prod.mk.inj hret' with ⟨rfl, _⟩
        obtain ⟨hleSub, rfl⟩ := ep1_subsliceWithLength_eq hsub
        have hsubLeSz : off.bytes + s.bytes ≤ sz.bytes := by
          rw [hbytesLen] at hleSub; exact hleSub
        have hidxC : listIndex mc.mem.memory.allocations id._0 "self.allocations[id.0]" = .ok alloc0 := by
          rw [hinv]; exact hidx0
        have hpoi : ptrOffsetInboundsM (M := BM) mc rp.ptr.thin_pointer (off.bytes : Int) =
            .ok { rp.ptr.thin_pointer with addr := rp.ptr.thin_pointer.addr + (off.bytes : Int) } := by
          have hsd : ConcurrentMemory.signed_dereferenceable (M := BM) mc.mem rp.ptr.thin_pointer (off.bytes : Int) = .ok () := by
            unfold ConcurrentMemory.signed_dereferenceable
            change BM.signed_dereferenceable mc.mem.memory rp.ptr.thin_pointer (off.bytes : Int) = .ok ()
            unfold BM.signed_dereferenceable BM.dereferenceable
            by_cases hoff0 : off.bytes = 0
            · simp only [hoff0, Int.natCast_zero, Int.lt_irrefl, ↓reduceIte, Int.neg_zero, Int.toNat_zero,
                BM.check_ptr, bind, Except.bind, pure, Except.pure]
            · have hoffPos : (off.bytes : Int) > 0 := by omega
              simp only [hoffPos, ↓reduceIte, Int.toNat_natCast]
              unfold BM.check_ptr
              simp only [hoff0, ↓reduceIte, hprov, hidxC, hlive0, Bool.not_true, Bool.false_eq_true,
                bind, Except.bind]
              have hnotOob : ¬(rp.ptr.thin_pointer.addr - alloc0.addr < 0 ∨
                  rp.ptr.thin_pointer.addr - alloc0.addr + (off.bytes : Int) > (Allocation.size alloc0).bytes) := by
                unfold Allocation.size; dsimp only
                rw [hbaseOffNat]
                exact ep1_not_oob_int (Int.natCast_nonneg _) (by omega)
              simp only [hnotOob, ↓reduceIte, pure, Except.pure]
          have hib1 : inBounds (off.bytes : Int) .Signed x86_64.PTR_SIZE = true :=
            ep1_inBounds_nonneg_signed off.bytes (by omega)
          have hib2 : inBounds (rp.ptr.thin_pointer.addr + (off.bytes : Int)) .Unsigned x86_64.PTR_SIZE = true :=
            ep1_inBounds_unsigned ((rp.ptr.thin_pointer.addr : Int) + (off.bytes : Int))
              (Int.add_nonneg haddr0 (Int.natCast_nonneg _))
              (Int.lt_of_le_of_lt
                (Int.add_le_add_left (Int.ofNat_le.mpr (Nat.le_trans (Nat.le_add_right _ _) hsubLeSz)) _)
                haddrHi)
          exact ep1_ptrOffsetInboundsM_ok (M := BM) mc rp.ptr.thin_pointer (off.bytes : Int) hsd hib1 hib2
        by_cases hs0 : s.bytes = 0
        · have hld : ConcurrentMemory.load (M := BM) mc.mem
              { rp.ptr.thin_pointer with addr := rp.ptr.thin_pointer.addr + (off.bytes : Int) }
              s ⟨1⟩ .None =
              .ok ([], { mc.mem with accesses := mc.mem.accesses ++
                [⟨.Load, .None, rp.ptr.thin_pointer.addr + (off.bytes : Int), s⟩] }) := by
            apply ep1_concurrent_load_of_mem_load (M := BM)
            change BM.load mc.mem.memory
                { rp.ptr.thin_pointer with addr := rp.ptr.thin_pointer.addr + (off.bytes : Int) }
                s ⟨1⟩ = .ok ([], mc.mem.memory)
            simp only [BM.load, ep1_align_one_is_aligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              BM.check_ptr, hs0, bind, Except.bind, pure, Except.pure]
          refine ⟨{ mc with mem := { mc.mem with accesses := mc.mem.accesses ++
              [⟨.Load, .None, rp.ptr.thin_pointer.addr + (off.bytes : Int), s⟩] } }, ?_, hinv⟩
          dsimp only [accLive]
          rw [hpoi]
          simp only [bind, Except.bind, hld, hs0, List.take_zero, pure, Except.pure]
        · have hchkSub : BM.check_ptr mc.mem.memory
              { rp.ptr.thin_pointer with addr := rp.ptr.thin_pointer.addr + (off.bytes : Int) } s =
              .ok (some (id, (), ⟨baseOff.bytes + off.bytes⟩)) := by
            unfold BM.check_ptr
            simp only [hs0, ↓reduceIte, hprov, hidxC, hlive0, Bool.not_true, Bool.false_eq_true,
              bind, Except.bind]
            have hdiff : (rp.ptr.thin_pointer.addr : Int) + (off.bytes : Int) - (alloc0.addr : Int) =
                ((baseOff.bytes + off.bytes : Nat) : Int) := by
              have hcomm : ∀ (x y z : Int), x + y - z = (x - z) + y := fun x y z => by omega
              rw [hcomm, hbaseOffNat]
              exact (Int.natCast_add _ _).symm
            have hnotOob : ¬(rp.ptr.thin_pointer.addr + (off.bytes : Int) - alloc0.addr < 0 ∨
                rp.ptr.thin_pointer.addr + (off.bytes : Int) - alloc0.addr + (s.bytes : Int) >
                  (Allocation.size alloc0).bytes) := by
              unfold Allocation.size; dsimp only
              rw [hdiff]
              exact ep1_not_oob_int (Int.natCast_nonneg _) (by omega)
            simp only [hnotOob, ↓reduceIte]
            simp only [hdiff, Int.toNat_natCast, pure, Except.pure]
          obtain ⟨hidNN, hidLt, helem⟩ := ep1_listIndex_int_eq_getElem hidxC
          have hsetC : listSet mc.mem.memory.allocations id._0 alloc0 "set" =
              .ok mc.mem.memory.allocations := by
            rw [ep1_listSet_int_of_lt _ "set" hidNN hidLt, ← helem, List.set_getElem_self]
          have hsubC : subsliceWithLength alloc0.data ((baseOff.bytes + off.bytes : Nat) : Int) (s.bytes : Int) =
              .ok ((alloc0.data.drop (baseOff.bytes + off.bytes)).take s.bytes) :=
            ep1_subsliceWithLength_of_le alloc0.data (by omega)
          let cmNext : Gen.ConcurrentMemory BM :=
            { memory := mc.mem.memory,
              accesses := mc.mem.accesses ++
                [⟨.Load, .None, rp.ptr.thin_pointer.addr + (off.bytes : Int), s⟩] }
          have hld : ConcurrentMemory.load (M := BM) mc.mem
              { rp.ptr.thin_pointer with addr := rp.ptr.thin_pointer.addr + (off.bytes : Int) }
              s ⟨1⟩ .None =
              .ok (((alloc0.data.drop (baseOff.bytes + off.bytes)).take s.bytes), cmNext) := by
            apply ep1_concurrent_load_of_mem_load (M := BM)
            change BM.load mc.mem.memory
                { rp.ptr.thin_pointer with addr := rp.ptr.thin_pointer.addr + (off.bytes : Int) }
                s ⟨1⟩ = .ok (((alloc0.data.drop (baseOff.bytes + off.bytes)).take s.bytes), mc.mem.memory)
            unfold BM.load
            simp only [ep1_align_one_is_aligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              hchkSub, hidxC, hsetC, hsubC, bind, Except.bind, pure, Except.pure]
          refine ⟨{ mc with mem := cmNext }, ?_, hinv⟩
          dsimp only [accLive]
          rw [hpoi]
          simp only [bind, Except.bind, hld, pure, Except.pure, ep1_drop_take_subslice alloc0.data hsubLeSz]
      exact ep1_decodeDiscriminantM_sim Inv accPure accLive hstep discr (some d) m1 rfl hdd
  obtain ⟨mDiscr, hmDiscr, hinv⟩ := hsim
  refine ⟨mDiscr, ?_, by rw [hinv, hmLoadMem, hbmMemEq]⟩
  unfold evalValueM
  rw [hp]
  simp only [hal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
  simp only [accLive, bind, Except.bind] at hmDiscr
  rw [hmDiscr]
  rfl

private theorem ep1_subsliceWithLength_len {T : Type} {xs bs : List T} {start len : Nat}
    (h : subsliceWithLength xs (start : Int) (len : Int) = .ok bs) :
    bs.length = len := by
  unfold subsliceWithLength at h
  split at h
  · rename_i hcond
    simp only [pure, Except.pure, Except.ok.injEq, Int.toNat_natCast] at h
    subst h
    simp only [List.length_take, List.length_drop]
    omega
  · simp [specPanic] at h

private theorem ep1_checkUnionChunksM_mapM {M : Type} [Gen.Memory M]
    (data : List (Gen.AbstractByte (Gen.Memory.Provenance M))) :
    ∀ (chunks : List (Gen.Offset × Size)) (chunkData : List (List (Gen.AbstractByte (Gen.Memory.Provenance M)))),
      chunks.mapM (fun (offset, chunkSize) => subsliceWithLength data offset.bytes chunkSize.bytes) = .ok chunkData →
      chunkData.length = chunks.length ∧
        checkUnionChunksM (Provenance := Gen.Memory.Provenance M) chunkData chunks = Except.ok ()
  | [], chunkData, h => by
    have hp := ep1_pure_ok h; subst hp
    exact ⟨rfl, rfl⟩
  | (off, csz) :: rest, chunkData, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨bs, hsub, h⟩ := ep1_bind_ok h
    obtain ⟨restData, hrest, hp⟩ := ep1_bind_ok h
    have hp' := ep1_pure_ok hp; subst hp'
    have hlen : bs.length = csz.bytes := ep1_subsliceWithLength_len hsub
    obtain ⟨hrestLen, hrestChk⟩ := ep1_checkUnionChunksM_mapM data rest restData hrest
    refine ⟨by simp [hrestLen], ?_⟩
    unfold checkUnionChunksM ensureElseUb
    simp only [hlen, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      bind, Except.bind, pure, Except.pure, hrestChk]

/-- **Universal `ValueExpr::Union` validity and full-chunk encode-decode roundtrip:**
on every `Memory` `M`:
1. every successful `evalValueM m (.Union field expr unionTy)` yields a value of type
   `unionTy` that satisfies `checkValueM v unionTy mOpt = .ok ()` for any `mOpt`;
2. for a full-chunk union (`chunks = [(⟨0⟩, sz)]`), constructing via `ValueExpr::Union`
   produces `.Union [data]`, re-encoding via `Type.encodeM` recovers the exact byte array
   `data`, and slicing `data` at `(off, encoded.length)` recovers the exact `encoded` field
   bytes. -/
theorem ep1_evalValueM_union_produces_valid_value_and_roundtrip
    {M : Type} [Gen.Memory M] [MemoryOps M] :
    (∀ (m m' : Gen.Machine M) (field : Int) (expr : Gen.ValueExpr) (unionTy ty : Gen.Type)
        (v : Gen.Value M) (mOpt : Option (Gen.Machine M)),
      evalValueM m (.Union field expr unionTy) = .ok ((v, ty), m') →
      ty = unionTy ∧ checkValueM v unionTy mOpt = .ok ()) ∧
    (∀ (m m1 : Gen.Machine M) (field : Int) (expr : Gen.ValueExpr)
        (fields : List (Gen.Offset × Gen.Type)) (sz : Size) (al : Align)
        (off : Gen.Offset) (exprTy : Gen.Type) (val : Gen.Value M) (vty : Gen.Type)
        (encoded data : List (Gen.AbstractByte (Gen.Memory.Provenance M))),
      let unionTy : Gen.Type := .Union fields [(⟨0⟩, sz)] sz al
      listIndex fields field "fields[field]" = .ok (off, exprTy) →
      evalValueM m expr = .ok ((val, vty), m1) →
      Type.encodeM exprTy val = .ok encoded →
      writeSubsliceAtIndex (List.replicate sz.bytes .Uninit) (off.bytes : Int) encoded = .ok data →
      evalValueM m (.Union field expr unionTy) = .ok ((.Union [data], unionTy), m1) ∧
      Type.encodeM unionTy (.Union [data]) = .ok data ∧
      subsliceWithLength data (off.bytes : Int) (encoded.length : Int) = .ok encoded) := by
  constructor
  · intro m m' field expr unionTy ty v mOpt h
    cases unionTy with
    | Union fields chunks sz al =>
      rw [ep1_evalValueM_union_complete_spec] at h
      obtain ⟨⟨off, exprTy⟩, _, h⟩ := ep1_bind_ok h
      obtain ⟨⟨⟨val, _⟩, m1⟩, _, h⟩ := ep1_bind_ok h
      obtain ⟨encoded, _, h⟩ := ep1_bind_ok h
      obtain ⟨data, _, h⟩ := ep1_bind_ok h
      obtain ⟨chunkData, hmap, hp⟩ := ep1_bind_ok h
      have hp' := ep1_pure_ok hp
      rcases Prod.mk.inj hp' with ⟨hvt, _⟩
      rcases Prod.mk.inj hvt with ⟨rfl, rfl⟩
      obtain ⟨hlen, hchk⟩ := ep1_checkUnionChunksM_mapM data chunks chunkData hmap
      refine ⟨rfl, ?_⟩
      unfold checkValueM ensureElseUb
      simp only [hlen, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        bind, Except.bind, pure, Except.pure, hchk]
    | _ =>
      simp [evalValueM, specPanic, bind, Except.bind] at h
  · intro m m1 field expr fields sz al off exprTy val vty encoded data unionTy hidx hev henc hws
    have hdataLen : data.length = sz.bytes := by
      rw [writeSubsliceAtIndex_length hws, List.length_replicate]
    have hsubFull : subsliceWithLength data ((0 : Nat) : Int) (sz.bytes : Int) = .ok data := by
      unfold subsliceWithLength
      have hcond : (0 : Int) ≤ ((0 : Nat) : Int) ∧ (0 : Int) ≤ (sz.bytes : Int) ∧
          ((0 : Nat) : Int) + (sz.bytes : Int) ≤ (data.length : Int) := by
        rw [hdataLen]; omega
      simp only [hcond, and_self, ↓reduceIte]
      simp only [Int.natCast_zero, Int.toNat_zero, Int.toNat_natCast, List.drop_zero,
        ← hdataLen, List.take_length, pure, Except.pure]
    have hUnionEval : evalValueM m (.Union field expr unionTy) = .ok ((.Union [data], unionTy), m1) := by
      dsimp only [unionTy]
      rw [ep1_evalValueM_union_complete_spec]
      simp only [hidx, hev, henc, hws, List.mapM_cons, List.mapM_nil, hsubFull,
        bind, Except.bind, pure, Except.pure]
    have hEncode : Type.encodeM unionTy (.Union [data]) = .ok data := by
      dsimp only [unionTy]
      unfold Type.encodeM Type.encodeUnionChunksM
      simp only [List.length_singleton, ne_eq, not_true_eq_false, ↓reduceIte, hdataLen,
        bind, Except.bind]
      unfold writeSubsliceAtIndex
      have hcond : (0 : Int) ≤ ((0 : Nat) : Int) ∧ ((0 : Nat) : Int) + (data.length : Int) ≤
          ((List.replicate sz.bytes
            (.Uninit : Gen.AbstractByte (Gen.Memory.Provenance M))).length : Int) := by
        rw [List.length_replicate, hdataLen]; omega
      simp only [hcond, and_self, ↓reduceIte]
      simp only [Int.natCast_zero, Int.toNat_zero, List.take_zero, List.nil_append,
        Nat.zero_add, hdataLen, List.drop_replicate, Nat.sub_self, List.replicate_zero,
        List.append_nil, pure, Except.pure]
      rfl
    have hRecover : subsliceWithLength data (off.bytes : Int) (encoded.length : Int) = .ok encoded := by
      unfold writeSubsliceAtIndex at hws
      split at hws
      · rename_i hcond
        have hdataEq := ep1_pure_ok hws
        subst hdataEq
        unfold subsliceWithLength
        have hlenTake : (List.take off.bytes
            (List.replicate sz.bytes (.Uninit : Gen.AbstractByte (Gen.Memory.Provenance M)))).length = off.bytes := by
          simp only [List.length_take, List.length_replicate]
          rw [List.length_replicate] at hcond
          omega
        have hcond2 : (0 : Int) ≤ (off.bytes : Int) ∧ (0 : Int) ≤ (encoded.length : Int) ∧
            (off.bytes : Int) + (encoded.length : Int) ≤
              ((List.take (off.bytes : Int).toNat
                (List.replicate sz.bytes (.Uninit : Gen.AbstractByte (Gen.Memory.Provenance M))) ++
                encoded ++
                List.drop ((off.bytes : Int).toNat + encoded.length)
                  (List.replicate sz.bytes (.Uninit : Gen.AbstractByte (Gen.Memory.Provenance M)))).length : Int) := by
          simp only [List.length_append, Int.toNat_natCast, hlenTake, List.length_drop, List.length_replicate]
          omega
        simp only [hcond2, and_self, ↓reduceIte]
        simp only [Int.toNat_natCast]
        rw [List.append_assoc, List.drop_append, hlenTake]
        simp only [Nat.sub_self, List.drop_zero,
          List.drop_eq_nil_of_le (Nat.le_of_eq hlenTake), List.nil_append, List.take_left,
          pure, Except.pure]
      · simp [specPanic] at hws
    exact ⟨hUnionEval, hEncode, hRecover⟩

private theorem ep1_vtable_layout_total :
    ∀ (ty : Gen.Type) (t : Gen.TraitName),
      Type.meta_kind ty = .VTablePointer t →
      ∃ lay, Type.layout ty = .ok lay ∧ LayoutStrategy.meta_kind lay = .VTablePointer t
  | .TraitObject tn, t, h => by
    simp only [Type.meta_kind, Gen.PointerMetaKind.VTablePointer.injEq] at h
    subst h
    exact ⟨.TraitObject tn, rfl, rfl⟩
  | .Tuple _ head (some tail), t, h => by
    simp only [Type.meta_kind] at h
    obtain ⟨tlay, htlay, hmk⟩ := ep1_vtable_layout_total tail t h
    refine ⟨.Tuple head tlay, ?_, by simpa [LayoutStrategy.meta_kind] using hmk⟩
    simp only [Type.layout, htlay, bind, Except.bind, pure, Except.pure]
  | .Tuple _ _ none, _, h => by simp [Type.meta_kind] at h
  | .Int _, _, h => by simp [Type.meta_kind] at h
  | .Bool, _, h => by simp [Type.meta_kind] at h
  | .Ptr _, _, h => by simp [Type.meta_kind] at h
  | .Union _ _ _ _, _, h => by simp [Type.meta_kind] at h
  | .Enum _ _ _ _ _, _, h => by simp [Type.meta_kind] at h
  | .Array _ _, _, h => by simp [Type.meta_kind] at h
  | .Slice _, _, h => by simp [Type.meta_kind] at h

/-- **Strict non-vtable panic totality and `Type::layout` totality on vtable types:**
strengthening `ep1_evalUnOpM_meta_unops_error_is_specPanic_or_unsupported` on every `Memory` `M`:
1. whenever `Type.meta_kind ty = .VTablePointer t`, `Type.layout ty` is total (succeeds with
   a layout of kind `.VTablePointer t`), so on a trait-object type `ComputeSize` /
   `ComputeAlign` always reach the vtable lookup of
   `LayoutStrategy::compute_size_and_align` (the machine's `Machine::vtable_lookup`, or the
   machine-free fail-closed stop) and never stop at a `Type.layout` spec panic;
2. for any non-vtable pointer type (`PtrType.meta_kind ptrTy ≠ .VTablePointer _`), any failure
   of `GetMetadata` is strictly `Stop.specPanic` (never `unsupported` and never `ub`);
3. for any non-vtable pointee type (`Type.meta_kind ty ≠ .VTablePointer _`), any failure of
   `ComputeSize ty` or `ComputeAlign ty` is strictly `Stop.specPanic` (never `unsupported`
   and never `ub`). -/
theorem ep1_meta_unops_nonVTable_never_unsupported_and_vtable_layout_total
    {M : Type} [Gen.Memory M] [MemoryOps M] :
    (∀ (ty : Gen.Type) (t : Gen.TraitName),
      Type.meta_kind ty = .VTablePointer t →
      ∃ lay, Type.layout ty = .ok lay ∧ LayoutStrategy.meta_kind lay = .VTablePointer t) ∧
    (∀ (ptr : Gen.Pointer (Gen.Memory.Provenance M)) (ptrTy : Gen.PtrType)
        (m : Option (Gen.Machine M)) (e : Stop),
      (∀ t, PtrType.meta_kind ptrTy ≠ .VTablePointer t) →
      evalUnOpM .GetMetadata (.Ptr ptr, .Ptr ptrTy) m = .error e →
      ∃ msg, e = .specPanic msg) ∧
    (∀ (ty opTy : Gen.Type) (v : Gen.Value M) (m : Option (Gen.Machine M)) (e : Stop),
      (∀ t, Type.meta_kind ty ≠ .VTablePointer t) →
      (evalUnOpM (.ComputeSize ty) (v, opTy) m = .error e ∨
       evalUnOpM (.ComputeAlign ty) (v, opTy) m = .error e) →
      ∃ msg, e = .specPanic msg) := by
  refine ⟨ep1_vtable_layout_total, ?_, ?_⟩
  · intro ptr ptrTy m e hnv h
    rcases ptr with ⟨thin, metaOpt⟩
    cases hk : PtrType.meta_kind ptrTy with
    | VTablePointer t => exact absurd hk (hnv t)
    | None =>
      cases metaOpt with
      | none =>
        rw [(ep1_evalUnOpM_getMetadata_complete_spec thin ptrTy m).1 hk] at h
        cases h
      | some pm =>
        rw [(ep1_evalUnOpM_getMetadata_complete_spec thin ptrTy m).2.2.2.1 pm hk] at h
        cases h; exact ⟨_, rfl⟩
    | ElementCount =>
      cases metaOpt with
      | none =>
        rw [(ep1_evalUnOpM_getMetadata_complete_spec thin ptrTy m).2.2.2.2.1 hk] at h
        cases h; exact ⟨_, rfl⟩
      | some pm =>
        cases pm with
        | ElementCount c =>
          rw [(ep1_evalUnOpM_getMetadata_complete_spec thin ptrTy m).2.1 c hk] at h
          cases hc : IntType.can_represent IntType.usize_ty c <;> simp [hc, specPanic] at h
          exact ⟨_, h.symm⟩
        | VTablePointer p =>
          rw [(ep1_evalUnOpM_getMetadata_complete_spec thin ptrTy m).2.2.2.2.2.1 p hk] at h
          cases h; exact ⟨_, rfl⟩
  · intro ty opTy v m e hnv h
    have hDecodeNonVT : ∀ (pm : Option (Gen.PointerMeta (Gen.Memory.Provenance M))),
        PointerMetaKind.decode_valueM (M := M) (Type.meta_kind ty) v = .ok pm →
        ∀ p, pm ≠ some (.VTablePointer p) := by
      intro pm hdv p hEq
      subst hEq
      cases hk : Type.meta_kind ty with
      | VTablePointer t => exact absurd hk (hnv t)
      | None =>
        rw [hk] at hdv; unfold PointerMetaKind.decode_valueM at hdv
        split at hdv <;> simp_all [pure, Except.pure, specPanic]
      | ElementCount =>
        rw [hk] at hdv; unfold PointerMetaKind.decode_valueM at hdv
        split at hdv <;> simp_all [pure, Except.pure, specPanic]
    have hCsaNonVT : ∀ (vt : Gen.ThinPointer (Gen.Memory.Provenance M) → Interp Gen.VTable)
        (lay : Gen.LayoutStrategy) (pm : Option (Gen.PointerMeta (Gen.Memory.Provenance M))) (e' : Stop),
        (∀ p, pm ≠ some (.VTablePointer p)) →
        LayoutStrategy.compute_size_and_align vt lay pm = .error e' →
        ∃ msg, e' = .specPanic msg := by
      intro vt lay
      induction lay with
      | Sized _ _ =>
        intro pm e' _ hcsa
        cases pm <;> simp [LayoutStrategy.compute_size_and_align, pure, Except.pure, specPanic] at hcsa
        exact ⟨_, hcsa.symm⟩
      | Slice _ _ =>
        intro pm e' hnotVT hcsa
        cases pm with
        | none => simp [LayoutStrategy.compute_size_and_align, specPanic] at hcsa; exact ⟨_, hcsa.symm⟩
        | some mv =>
          cases mv with
          | VTablePointer p => exact absurd rfl (hnotVT p)
          | ElementCount c =>
            unfold LayoutStrategy.compute_size_and_align at hcsa; dsimp only at hcsa
            split at hcsa <;> simp [pure, Except.pure, specPanic] at hcsa
            exact ⟨_, hcsa.symm⟩
      | TraitObject _ =>
        intro pm e' hnotVT hcsa
        cases pm with
        | none => simp [LayoutStrategy.compute_size_and_align, specPanic] at hcsa; exact ⟨_, hcsa.symm⟩
        | some mv =>
          cases mv with
          | VTablePointer p => exact absurd rfl (hnotVT p)
          | ElementCount _ => simp [LayoutStrategy.compute_size_and_align, specPanic] at hcsa; exact ⟨_, hcsa.symm⟩
      | Tuple _ tail ih =>
        intro pm e' hnotVT hcsa
        cases pm with
        | none => simp [LayoutStrategy.compute_size_and_align, specPanic] at hcsa; exact ⟨_, hcsa.symm⟩
        | some mv =>
          unfold LayoutStrategy.compute_size_and_align at hcsa
          rcases ep1_bind_error hcsa with ht | ⟨_, _, hp2⟩
          · exact ih (some mv) e' hnotVT ht
          · simp [pure, Except.pure] at hp2
    have hRun : ∀ (isSize : Bool),
        (if isSize then evalUnOpM (.ComputeSize ty) (v, opTy) none
         else evalUnOpM (.ComputeAlign ty) (v, opTy) none) = .error e →
        ∃ msg, e = .specPanic msg := by
      intro isSize he
      cases isSize <;> simp only [↓reduceIte, Bool.false_eq_true] at he <;> unfold evalUnOpM at he
      · rcases ep1_bind_error he with hdv | ⟨pm, hdv, htail⟩
        · unfold PointerMetaKind.decode_valueM at hdv
          split at hdv <;> simp [pure, Except.pure, specPanic] at hdv
          exact ⟨_, hdv.symm⟩
        · have hnotVT := hDecodeNonVT pm hdv
          cases pm with
          | none =>
            rcases ep1_bind_error htail with hl | ⟨lay, _, htail⟩
            · exact ep1_Type_layout_error_is_specPanic ty e hl
            · rcases ep1_bind_error htail with hc | ⟨_, _, hp⟩
              · exact hCsaNonVT _ lay none e hnotVT (ep1_map_error hc)
              · simp [pure, Except.pure] at hp
          | some mval =>
            cases mval with
            | VTablePointer p => exact absurd rfl (hnotVT p)
            | ElementCount c =>
              rcases ep1_bind_error htail with hl | ⟨lay, _, htail⟩
              · exact ep1_Type_layout_error_is_specPanic ty e hl
              · rcases ep1_bind_error htail with hc | ⟨_, _, hp⟩
                · exact hCsaNonVT _ lay (some (.ElementCount c)) e hnotVT (ep1_map_error hc)
                · simp [pure, Except.pure] at hp
      · rcases ep1_bind_error he with hdv | ⟨pm, hdv, htail⟩
        · unfold PointerMetaKind.decode_valueM at hdv
          split at hdv <;> simp [pure, Except.pure, specPanic] at hdv
          exact ⟨_, hdv.symm⟩
        · have hnotVT := hDecodeNonVT pm hdv
          cases pm with
          | none =>
            rcases ep1_bind_error htail with hl | ⟨lay, _, htail⟩
            · exact ep1_Type_layout_error_is_specPanic ty e hl
            · rcases ep1_bind_error htail with hc | ⟨_, _, hp⟩
              · exact hCsaNonVT _ lay none e hnotVT (ep1_map_error hc)
              · simp [pure, Except.pure] at hp
          | some mval =>
            cases mval with
            | VTablePointer p => exact absurd rfl (hnotVT p)
            | ElementCount c =>
              rcases ep1_bind_error htail with hl | ⟨lay, _, htail⟩
              · exact ep1_Type_layout_error_is_specPanic ty e hl
              · rcases ep1_bind_error htail with hc | ⟨_, _, hp⟩
                · exact hCsaNonVT _ lay (some (.ElementCount c)) e hnotVT (ep1_map_error hc)
                · simp [pure, Except.pure] at hp
    rcases h with hS | hA
    · cases m with
      | none => exact hRun true hS
      | some mach =>
        rw [(ep1_evalUnOpM_computeSize_computeAlign_mach_indep ty opTy v mach hnv).1] at hS
        exact hRun true hS
    · cases m with
      | none => exact hRun false hA
      | some mach =>
        rw [(ep1_evalUnOpM_computeSize_computeAlign_mach_indep ty opTy v mach hnv).2] at hA
        exact hRun false hA

/-- **Algebraic composition law `GetMetadata` → `ComputeSize` / `ComputeAlign`:**
whenever `evalUnOpM .GetMetadata (.Ptr ptr, .Ptr ptrTy) m = .ok (metaVal, metaTy)` and `ty`
has matching `Type.meta_kind ty = PtrType.meta_kind ptrTy` and `Type.layout ty = .ok lay`:
1. `PointerMetaKind.decode_valueM (Type.meta_kind ty) metaVal = .ok ptr.metadata` (exact
   encode/decode roundtrip, including vtable metadata, which `GetMetadata` returns only
   with a machine);
2. whenever `LayoutStrategy.compute_size_and_align vt lay ptr.metadata = .ok (sz, al)`,
   where `vt` is arbitrary for non-vtable metadata and is the machine's
   `Machine::vtable_lookup` (`vtableLookupM`) for vtable metadata, feeding
   `(metaVal, metaTy)` directly into `ComputeSize ty` and `ComputeAlign ty` returns
   `(.Int sz.bytes, usize)` and `(.Int al.bytes, usize)` respectively. -/
theorem ep1_evalUnOpM_getMetadata_then_computeSize_computeAlign
    {M : Type} [Gen.Memory M] [MemoryOps M]
    (ptr : Gen.Pointer (Gen.Memory.Provenance M)) (ptrTy : Gen.PtrType)
    (ty : Gen.Type) (lay : Gen.LayoutStrategy)
    (metaVal : Gen.Value M) (metaTy : Gen.Type) (m : Option (Gen.Machine M))
    (hGet : evalUnOpM .GetMetadata (.Ptr ptr, .Ptr ptrTy) m = .ok (metaVal, metaTy))
    (hKind : Type.meta_kind ty = PtrType.meta_kind ptrTy)
    (hLay : Type.layout ty = .ok lay) :
    PointerMetaKind.decode_valueM (M := M) (Type.meta_kind ty) metaVal = .ok ptr.metadata ∧
    (∀ (sz : Size) (al : Align)
        (vt : Gen.ThinPointer (Gen.Memory.Provenance M) → Interp Gen.VTable),
      ((∀ p, ptr.metadata ≠ some (.VTablePointer p)) ∨
        (∃ mach, m = some mach ∧ vt = vtableLookupM mach)) →
      LayoutStrategy.compute_size_and_align vt lay ptr.metadata = .ok (sz, al) →
      evalUnOpM (.ComputeSize ty) (metaVal, metaTy) m = .ok (.Int (sz.bytes : Int), .Int IntType.usize_ty) ∧
      evalUnOpM (.ComputeAlign ty) (metaVal, metaTy) m = .ok (.Int (al.bytes : Int), .Int IntType.usize_ty)) := by
  have hCsaIndep : ∀ (vt1 vt2 : Gen.ThinPointer (Gen.Memory.Provenance M) → Interp Gen.VTable)
      (l : Gen.LayoutStrategy) (pm : Option (Gen.PointerMeta (Gen.Memory.Provenance M))),
      (∀ p, pm ≠ some (.VTablePointer p)) →
      LayoutStrategy.compute_size_and_align vt1 l pm = LayoutStrategy.compute_size_and_align vt2 l pm := by
    intro vt1 vt2 l
    induction l with
    | Sized _ _ => intro pm _; cases pm <;> rfl
    | Slice _ _ =>
      intro pm _
      cases pm with
      | none => rfl
      | some mv => cases mv <;> rfl
    | TraitObject _ =>
      intro pm hnv
      cases pm with
      | none => rfl
      | some mv =>
        cases mv with
        | ElementCount _ => rfl
        | VTablePointer p => exact absurd rfl (hnv p)
    | Tuple _ tail ih =>
      intro pm hnv
      cases pm with
      | none => rfl
      | some mv =>
        unfold LayoutStrategy.compute_size_and_align
        rw [ih (some mv) hnv]
  rcases ptr with ⟨thin, metaOpt⟩
  have hDec : PointerMetaKind.decode_valueM (M := M) (Type.meta_kind ty) metaVal = .ok metaOpt := by
    rw [hKind]
    cases hk : PtrType.meta_kind ptrTy with
    | VTablePointer t =>
      cases metaOpt with
      | none =>
        rw [(ep1_evalUnOpM_getMetadata_complete_spec thin ptrTy m).2.2.2.2.2.2.1 t hk] at hGet
        cases hGet
      | some mv =>
        cases mv with
        | ElementCount c =>
          rw [(ep1_evalUnOpM_getMetadata_complete_spec thin ptrTy m).2.2.2.2.2.2.2.1 t c hk] at hGet
          cases hGet
        | VTablePointer p =>
          cases m with
          | none =>
            rw [(ep1_evalUnOpM_getMetadata_complete_spec thin ptrTy none).2.2.1 t p hk] at hGet
            cases hGet
          | some mach =>
            rw [(ep1_evalUnOpM_getMetadata_complete_spec thin ptrTy (some mach)).2.2.2.2.2.2.2.2
              t p mach hk] at hGet
            cases hchk : checkPtrM (M := M) ⟨p, none⟩ (.VTablePtr t) (some mach) with
            | error e =>
              rw [hchk] at hGet
              cases e <;> cases hGet
            | ok u =>
              cases u
              rw [hchk] at hGet
              simp only [Except.ok.injEq, Prod.mk.injEq] at hGet
              rcases hGet with ⟨rfl, _⟩
              rfl
    | None =>
      cases metaOpt with
      | none =>
        rw [(ep1_evalUnOpM_getMetadata_complete_spec thin ptrTy m).1 hk] at hGet
        simp only [Except.ok.injEq, Prod.mk.injEq] at hGet
        rcases hGet with ⟨rfl, _⟩
        rfl
      | some mv =>
        rw [(ep1_evalUnOpM_getMetadata_complete_spec thin ptrTy m).2.2.2.1 mv hk] at hGet
        cases hGet
    | ElementCount =>
      cases metaOpt with
      | none =>
        rw [(ep1_evalUnOpM_getMetadata_complete_spec thin ptrTy m).2.2.2.2.1 hk] at hGet
        cases hGet
      | some mv =>
        cases mv with
        | ElementCount c =>
          rw [(ep1_evalUnOpM_getMetadata_complete_spec thin ptrTy m).2.1 c hk] at hGet
          cases hc : IntType.can_represent IntType.usize_ty c <;> simp [hc, specPanic] at hGet
          rcases hGet with ⟨rfl, _⟩
          rfl
        | VTablePointer p =>
          rw [(ep1_evalUnOpM_getMetadata_complete_spec thin ptrTy m).2.2.2.2.2.1 p hk] at hGet
          cases hGet
  refine ⟨hDec, ?_⟩
  intro sz al vt hSel hCsa
  cases m with
  | none =>
    have hNotVT : ∀ p, metaOpt ≠ some (.VTablePointer p) := by
      rcases hSel with hNot | ⟨mach, hm, _⟩
      · exact hNot
      · cases hm
    have h1 := hCsaIndep (fun _ => unsupported "eval_un_op UnOp::ComputeSize for vtable pointer metadata") vt lay metaOpt hNotVT
    have h2 := hCsaIndep (fun _ => unsupported "eval_un_op UnOp::ComputeAlign for vtable pointer metadata") vt lay metaOpt hNotVT
    constructor
    · unfold evalUnOpM; simp only [hDec, hLay, h1, hCsa, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
    · unfold evalUnOpM; simp only [hDec, hLay, h2, hCsa, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
  | some mach =>
    have hCsaM : LayoutStrategy.compute_size_and_align (vtableLookupM mach) lay metaOpt =
        .ok (sz, al) := by
      rcases hSel with hNot | ⟨mach', hm, hvt⟩
      · rw [hCsaIndep (vtableLookupM mach) vt lay metaOpt hNot]
        exact hCsa
      · cases hm
        rw [← hvt]
        exact hCsa
    constructor
    · unfold evalUnOpM; simp only [hDec, hLay, computeSizeM, hCsaM, bind, Except.bind, pure, Except.pure]
    · unfold evalUnOpM; simp only [hDec, hLay, computeAlignM, hCsaM, bind, Except.bind, pure, Except.pure]

/-- **Sharp `dyn Trait` instance of the composition law `GetMetadata` →
`ComputeSize` / `ComputeAlign`, with a machine.** For every pointer type with
vtable-pointer metadata (`&dyn Trait`, `&mut dyn Trait`, `Box<dyn Trait>`,
`*const dyn Trait`, and pointers to unsized structs with a `dyn Trait` tail)
and every pointer whose metadata `vptr` is in bounds and is the address of a
vtable `vt` for the trait (the metadata part of `check_ptr`), on every memory
model:
1. `GetMetadata` returns `vptr` at `Type::Ptr(PtrType::VTablePtr(trait_name))`;
2. feeding that result to `ComputeSize` / `ComputeAlign` at `Type::TraitObject`
   returns exactly `vt.size` and `vt.align`;
3. feeding it to `ComputeSize` / `ComputeAlign` at an unsized tuple with a
   `dyn Trait` tail returns exactly the full size and alignment that
   `TupleHeadLayout::full_size_and_align` computes from `vt.size` and
   `vt.align`.
None of the five operator applications errors. -/
theorem ep1_evalUnOpM_getMetadata_then_computeSize_computeAlign_dyn
    {M : Type} [Gen.Memory M] [MemoryOps M]
    (thin vptr : Gen.ThinPointer (Gen.Memory.Provenance M)) (ptrTy : Gen.PtrType)
    (t : Gen.TraitName) (mach : Gen.Machine M) (vt : Gen.VTable)
    (fields : List (Gen.Offset × Gen.Type)) (head : Gen.TupleHeadLayout)
    (hKind : PtrType.meta_kind ptrTy = .VTablePointer t)
    (hAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableLookupM mach vptr = .ok vt) (hTrait : vt.trait_name = t) :
    evalUnOpM (M := M) .GetMetadata (.Ptr ⟨thin, some (.VTablePointer vptr)⟩, .Ptr ptrTy)
        (some mach) = .ok (.Ptr ⟨vptr, none⟩, .Ptr (.VTablePtr t)) ∧
    evalUnOpM (M := M) (.ComputeSize (.TraitObject t)) (.Ptr ⟨vptr, none⟩, .Ptr (.VTablePtr t))
        (some mach) = .ok (.Int (vt.size.bytes : Int), .Int IntType.usize_ty) ∧
    evalUnOpM (M := M) (.ComputeAlign (.TraitObject t)) (.Ptr ⟨vptr, none⟩, .Ptr (.VTablePtr t))
        (some mach) = .ok (.Int (vt.align.bytes : Int), .Int IntType.usize_ty) ∧
    evalUnOpM (M := M) (.ComputeSize (.Tuple fields head (some (.TraitObject t))))
        (.Ptr ⟨vptr, none⟩, .Ptr (.VTablePtr t)) (some mach) =
      .ok (.Int ((TupleHeadLayout.full_size_and_align head vt.size vt.align).1.bytes : Int),
        .Int IntType.usize_ty) ∧
    evalUnOpM (M := M) (.ComputeAlign (.Tuple fields head (some (.TraitObject t))))
        (.Ptr ⟨vptr, none⟩, .Ptr (.VTablePtr t)) (some mach) =
      .ok (.Int ((TupleHeadLayout.full_size_and_align head vt.size vt.align).2.bytes : Int),
        .Int IntType.usize_ty) := by
  have hChk : checkPtrM (M := M) ⟨vptr, none⟩ (.VTablePtr t) (some mach) = .ok () :=
    checkPtrM_vtablePtr_ok vptr t mach vt hAddr
      ((vtableFromPtrM_ok_iff_vtableLookupM_ok mach vptr vt).mpr hvt) hTrait
  have hGet : evalUnOpM (M := M) .GetMetadata
      (.Ptr ⟨thin, some (.VTablePointer vptr)⟩, .Ptr ptrTy) (some mach) =
      .ok (.Ptr ⟨vptr, none⟩, .Ptr (.VTablePtr t)) := by
    rw [(ep1_evalUnOpM_getMetadata_complete_spec thin ptrTy (some mach)).2.2.2.2.2.2.2.2
      t vptr mach hKind, hChk]
  have hKindTy : Type.meta_kind (.TraitObject t) = PtrType.meta_kind ptrTy := by
    rw [hKind]; rfl
  have hCsa : LayoutStrategy.compute_size_and_align (vtableLookupM mach) (.TraitObject t)
      (some (.VTablePointer vptr)) = .ok (vt.size, vt.align) := by
    rw [compute_size_and_align_traitObject, hvt]; rfl
  have hBare := (ep1_evalUnOpM_getMetadata_then_computeSize_computeAlign
    ⟨thin, some (.VTablePointer vptr)⟩ ptrTy (.TraitObject t) (.TraitObject t)
    (.Ptr ⟨vptr, none⟩) (.Ptr (.VTablePtr t)) (some mach) hGet hKindTy rfl).2
    vt.size vt.align (vtableLookupM mach) (Or.inr ⟨mach, rfl, rfl⟩) hCsa
  have hTuple := evalUnOpM_tuple_traitObject_size_align mach vptr fields head t
    (.Ptr (.VTablePtr t)) vt hvt
  exact ⟨hGet, hBare.1, hBare.2, hTuple.1, hTuple.2⟩

private def ep1KnownOnlyEnumTy : Gen.Type :=
  let unitVar : Gen.Type := .Tuple [] ⟨⟨4⟩, ⟨4⟩, none⟩ none
  .Enum ⟨[(0, { ty := unitVar, tagger := ⟨[]⟩ })]⟩ ep1U8 (.Known 0) ⟨4⟩ ⟨4⟩

private def ep1MultiTagEnumTy : Gen.Type :=
  let v0Ty : Gen.Type := .Tuple [(⟨2⟩, .Int ep1U16)] ⟨⟨4⟩, ⟨2⟩, none⟩ none
  let v1Ty : Gen.Type := .Tuple [(⟨2⟩, .Int ep1U16)] ⟨⟨4⟩, ⟨2⟩, none⟩ none
  let v0 : Gen.Variant := { ty := v0Ty, tagger := ⟨[(⟨0⟩, (ep1U8, 0x11)), (⟨1⟩, (ep1U8, 0x22))]⟩ }
  let v1 : Gen.Variant := { ty := v1Ty, tagger := ⟨[(⟨0⟩, (ep1U8, 0x11)), (⟨1⟩, (ep1U8, 0x33))]⟩ }
  let inner : Gen.Discriminator :=
    .Branch ⟨1⟩ ep1U8 .Invalid ⟨[((0x22, 0x23), .Known 0), ((0x33, 0x34), .Known 1)]⟩
  let disc : Gen.Discriminator :=
    .Branch ⟨0⟩ ep1U8 .Invalid ⟨[((0x11, 0x12), inner)]⟩
  .Enum ⟨[(0, v0), (1, v1)]⟩ ep1U8 disc ⟨4⟩ ⟨2⟩

/-- **Concrete edge-case witnesses (`[adv A1]`):**
1. misaligned `PlaceExpr::Downcast` preserves `aligned = false` without UB, while
   `GetDiscriminant` on a misaligned `.Known`-only enum place (0 memory loads) still raises
   `"Getting the discriminant of a place based on a misaligned pointer."`;
2. ZST slice `[(); N]` and unsized `(u8, [(); N])` `ComputeSize`/`ComputeAlign` at `N = 0,
   1000, -1` (`Size(0) * (-1) = Size(0)` matching `libspecr`);
3. `GetMetadata` on thin `PtrType::VTablePtr` returns `()` while `Box` to `Tuple+TraitObject`
   returns fail-closed `unsupported` and `Box` to `Slice` returns `ElementCount`;
4. multi-tagger (2-offset) enum roundtrip (`Variant` → `Assign` → `GetDiscriminant` → `Load`)
   on both `Mach` and `MachTB` (with `MachTB.wfLive` preservation). -/
theorem ep1_misaligned_downcast_zst_slice_and_multitag_witness :
    let zstTy : Gen.Type := .Tuple [] ⟨⟨0⟩, ⟨1⟩, none⟩ none
    let zstSliceTy : Gen.Type := .Slice zstTy
    let unsizedZstTailTy : Gen.Type := .Tuple [(⟨0⟩, .Int ep1U8)] ⟨⟨1⟩, ⟨1⟩, none⟩ (some zstSliceTy)
    let traitObjTupleTy : Gen.Type := .Tuple [(⟨0⟩, .Int ep1U32)] ⟨⟨4⟩, ⟨4⟩, none⟩ (some (.TraitObject ⟨⟨0⟩⟩))
    let usize : Gen.Type := .Int IntType.usize_ty
    let mkPointee (lay : Gen.LayoutStrategy) : Gen.PointeeInfo :=
      { layout := lay, inhabited := true, unsafe_cells := .Sized [], freeze := true, unpin := true }
    let dynBoxTy : Gen.PtrType := .Box (mkPointee (.Tuple ⟨⟨4⟩, ⟨4⟩, none⟩ (.TraitObject ⟨⟨0⟩⟩)))
    let sliceBoxTy : Gen.PtrType := .Box (mkPointee (.Slice ⟨4⟩ ⟨4⟩))
    let vtableThin : Gen.ThinPointer (Gen.AllocId × Unit) := ⟨0x400, none⟩
    let vtablePtr : Gen.Pointer (Gen.AllocId × Unit) := ⟨vtableThin, none⟩
    let wideDynPtr : Gen.Pointer (Gen.AllocId × Unit) := ⟨⟨0x500, none⟩, some (.VTablePointer vtableThin)⟩
    let wideSlicePtr : Gen.Pointer (Gen.AllocId × Unit) := ⟨⟨0x500, none⟩, some (.ElementCount 7)⟩
    let vtableThinTB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x400, none⟩
    let vtablePtrTB : Gen.Pointer Gen.TreeBorrowsProvenance := ⟨vtableThinTB, none⟩
    let wideDynPtrTB : Gen.Pointer Gen.TreeBorrowsProvenance := ⟨⟨0x500, none⟩, some (.VTablePointer vtableThinTB)⟩
    let wideSlicePtrTB : Gen.Pointer Gen.TreeBorrowsProvenance := ⟨⟨0x500, none⟩, some (.ElementCount 7)⟩
    let mBM := ep1MachBM
      [{ data := List.replicate 8 (.Init 0 none), addr := 0x102, align := ⟨2⟩, kind := .Stack, live := true, extra := () },
       { data := List.replicate 4 .Uninit, addr := 0x200, align := ⟨2⟩, kind := .Stack, live := true, extra := () }]
      [(⟨⟨0⟩⟩, ⟨0x102, some (⟨0⟩, ())⟩), (⟨⟨1⟩⟩, ⟨0x200, some (⟨1⟩, ())⟩)]
      [(⟨⟨0⟩⟩, ep1KnownOnlyEnumTy), (⟨⟨1⟩⟩, ep1MultiTagEnumTy)]
    let mTB := liftMachToTB mBM
    let misPlace : Gen.PlaceExpr :=
      .Deref (.Constant (.PointerWithoutProvenance 0x102) (.Ptr (.Raw .None))) ep1KnownOnlyEnumTy
    let var1Expr : Gen.ValueExpr :=
      .Variant 1 (.Tuple [.Constant (.Int 0xBEEF) (.Int ep1U16)] (.Tuple [(⟨2⟩, .Int ep1U16)] ⟨⟨4⟩, ⟨2⟩, none⟩ none)) ep1MultiTagEnumTy
    -- 1. Misaligned Downcast preserves aligned = false, and misaligned .Known-only GetDiscriminant is still UB (0 loads)
    (evalPlace mBM (.Downcast misPlace 0) =
        .ok ((⟨⟨⟨0x102, none⟩, none⟩, false⟩, .Tuple [] ⟨⟨4⟩, ⟨4⟩, none⟩ none), mBM) ∧
     evalPlaceM mTB (.Downcast misPlace 0) =
        .ok ((⟨⟨⟨0x102, none⟩, none⟩, false⟩, .Tuple [] ⟨⟨4⟩, ⟨4⟩, none⟩ none), mTB) ∧
     evalValue mBM (.GetDiscriminant misPlace) =
        .error (.ub "Getting the discriminant of a place based on a misaligned pointer.") ∧
     evalValueM mTB (.GetDiscriminant misPlace) =
        .error (.ub "Getting the discriminant of a place based on a misaligned pointer.")) ∧
    -- 2. ZST slice [(); N] and unsized (u8, [(); N]) ComputeSize/ComputeAlign at N = 0, 1000, -1 (Size 0 * -1 = 0!)
    (evalUnOp (.ComputeSize zstSliceTy) (.Int 0, usize) none = .ok (.Int 0, usize) ∧
     evalUnOp (.ComputeSize zstSliceTy) (.Int 1000, usize) none = .ok (.Int 0, usize) ∧
     evalUnOp (.ComputeSize zstSliceTy) (.Int (-1), usize) none = .ok (.Int 0, usize) ∧
     evalUnOp (.ComputeAlign zstSliceTy) (.Int 1000, usize) none = .ok (.Int 1, usize) ∧
     evalUnOp (.ComputeSize unsizedZstTailTy) (.Int 1000, usize) none = .ok (.Int 1, usize) ∧
     evalUnOp (.ComputeAlign unsizedZstTailTy) (.Int 1000, usize) none = .ok (.Int 1, usize) ∧
     evalUnOpM (M := TBM) (.ComputeSize zstSliceTy) (.Int (-1), usize) none = .ok (.Int 0, usize) ∧
     evalUnOpM (M := TBM) (.ComputeSize unsizedZstTailTy) (.Int 1000, usize) none = .ok (.Int 1, usize)) ∧
    -- 3. GetMetadata: PtrType.VTablePtr is thin (returns ()), whereas Box to Tuple+TraitObject is wide (unsupported),
    --    and Box to Slice is wide (returns ElementCount)
    (evalUnOp .GetMetadata (.Ptr vtablePtr, .Ptr (.VTablePtr ⟨⟨0⟩⟩)) none = .ok (.Tuple [], unitType) ∧
     evalUnOpM (M := TBM) .GetMetadata (.Ptr vtablePtrTB, .Ptr (.VTablePtr ⟨⟨0⟩⟩)) none = .ok (.Tuple [], unitType) ∧
     evalUnOp .GetMetadata (.Ptr wideDynPtr, .Ptr dynBoxTy) none =
       unsupported "eval_un_op UnOp::GetMetadata for vtable pointer metadata" ∧
     evalUnOpM (M := TBM) .GetMetadata (.Ptr wideDynPtrTB, .Ptr dynBoxTy) none =
       unsupported "eval_un_op UnOp::GetMetadata for vtable pointer metadata" ∧
     evalUnOp .GetMetadata (.Ptr wideSlicePtr, .Ptr sliceBoxTy) none = .ok (.Int 7, usize) ∧
     evalUnOpM (M := TBM) .GetMetadata (.Ptr wideSlicePtrTB, .Ptr sliceBoxTy) none = .ok (.Int 7, usize) ∧
     evalUnOp (.ComputeSize traitObjTupleTy) (.Ptr vtablePtr, .Ptr (.VTablePtr ⟨⟨0⟩⟩)) none =
       unsupported "eval_un_op UnOp::ComputeSize for vtable pointer metadata") ∧
    -- 4. Multi-tagger (2-offset) enum roundtrip: Variant -> Assign -> GetDiscriminant -> Load (Mach & MachTB + wfLive)
    (∃ m1 m2 m3,
      evalStatement mBM (.Assign (.Local ⟨⟨1⟩⟩) var1Expr) = .ok m1 ∧
      evalValue m1 (.GetDiscriminant (.Local ⟨⟨1⟩⟩)) = .ok ((.Int 1, .Int ep1U8), m2) ∧
      evalValue m2 (.Load (.Local ⟨⟨1⟩⟩)) = .ok ((.Variant 1 (.Tuple [.Int 0xBEEF]), ep1MultiTagEnumTy), m3)) ∧
    (∃ m1 m2 m3,
      evalStatementM mTB (.Assign (.Local ⟨⟨1⟩⟩) var1Expr) = .ok m1 ∧
      evalValueM m1 (.GetDiscriminant (.Local ⟨⟨1⟩⟩)) = .ok ((.Int 1, .Int ep1U8), m2) ∧
      evalValueM m2 (.Load (.Local ⟨⟨1⟩⟩)) = .ok ((.Variant 1 (.Tuple [.Int 0xBEEF]), ep1MultiTagEnumTy), m3) ∧
      MachTB.wfLive m3) := by
  intro zstTy zstSliceTy unsizedZstTailTy traitObjTupleTy usize mkPointee dynBoxTy sliceBoxTy
    vtableThin vtablePtr wideDynPtr wideSlicePtr
    vtableThinTB vtablePtrTB wideDynPtrTB wideSlicePtrTB
    mBM mTB misPlace var1Expr
  have h1 : evalPlace mBM (.Downcast misPlace 0) =
      .ok ((⟨⟨⟨0x102, none⟩, none⟩, false⟩, .Tuple [] ⟨⟨4⟩, ⟨4⟩, none⟩ none), mBM) := by ep1_kernel_rfl
  have h2 : evalPlaceM mTB (.Downcast misPlace 0) =
      .ok ((⟨⟨⟨0x102, none⟩, none⟩, false⟩, .Tuple [] ⟨⟨4⟩, ⟨4⟩, none⟩ none), mTB) := by ep1_kernel_rfl
  have h3 : evalValue mBM (.GetDiscriminant misPlace) =
      .error (.ub "Getting the discriminant of a place based on a misaligned pointer.") := by ep1_kernel_rfl
  have h4 : evalValueM mTB (.GetDiscriminant misPlace) =
      .error (.ub "Getting the discriminant of a place based on a misaligned pointer.") := by ep1_kernel_rfl
  have hbmRound : (do
      let m1 ← evalStatement mBM (.Assign (.Local ⟨⟨1⟩⟩) var1Expr)
      let (r1, m2) ← evalValue m1 (.GetDiscriminant (.Local ⟨⟨1⟩⟩))
      let (r2, _) ← evalValue m2 (.Load (.Local ⟨⟨1⟩⟩))
      pure (r1, r2)) =
      .ok ((.Int 1, .Int ep1U8), (.Variant 1 (.Tuple [.Int 0xBEEF]), ep1MultiTagEnumTy)) := by
    ep1_kernel_rfl
  have htbRound : (do
      let m1 ← evalStatementM mTB (.Assign (.Local ⟨⟨1⟩⟩) var1Expr)
      let (r1, m2) ← evalValueM m1 (.GetDiscriminant (.Local ⟨⟨1⟩⟩))
      let (r2, m3) ← evalValueM m2 (.Load (.Local ⟨⟨1⟩⟩))
      pure (r1, r2, m3.mem.memory.mem.allocations.length)) =
      .ok ((.Int 1, .Int ep1U8), (.Variant 1 (.Tuple [.Int 0xBEEF]), ep1MultiTagEnumTy), 2) := by
    ep1_kernel_rfl
  obtain ⟨m1, hm1, hbmRest⟩ := ep1_bind_ok hbmRound
  obtain ⟨⟨r1, m2⟩, hm2, hbmRest⟩ := ep1_bind_ok hbmRest
  obtain ⟨⟨r2, m3⟩, hm3, hbmRet⟩ := ep1_bind_ok hbmRest
  have hbmEq := ep1_pure_ok hbmRet
  rcases Prod.mk.inj hbmEq with ⟨rfl, rfl⟩
  obtain ⟨t1, ht1, htbRest⟩ := ep1_bind_ok htbRound
  obtain ⟨⟨tr1, t2⟩, ht2, htbRest⟩ := ep1_bind_ok htbRest
  obtain ⟨⟨tr2, t3⟩, ht3, htbRet⟩ := ep1_bind_ok htbRest
  have htbEq := ep1_pure_ok htbRet
  rcases Prod.mk.inj htbEq with ⟨rfl, htbEq2⟩
  rcases Prod.mk.inj htbEq2 with ⟨rfl, _⟩
  have hwf0 : MachTB.wfLive mTB := liftMachToTB_wfLive mBM
  have hwf1 : MachTB.wfLive t1 := evalStatementM_tb_wfLive hwf0 ht1
  have hwf2 : MachTB.wfLive t2 := evalValueM_tb_wfLive _ hwf1 ht2
  have hwf3 : MachTB.wfLive t3 := evalValueM_tb_wfLive _ hwf2 ht3
  refine ⟨⟨h1, h2, h3, h4⟩, ?_, ?_, ⟨m1, m2, m3, hm1, hm2, hm3⟩, ⟨t1, t2, t3, ht1, ht2, ht3, hwf3⟩⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ep1_kernel_rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ep1_kernel_rfl

/-! ### `[adv B2]` `GetDiscriminant` is a sequence of memory loads: frame laws on every `Memory`,
`BasicMemory` read-only-ness, Tree Borrows byte preservation, `Variant` well-formedness, and the
tightness of the `Load ⇒ GetDiscriminant` address hypotheses -/

mutual

/-- `decodeDiscriminantM` preserves every invariant of the threaded state that each call of
its accessor preserves (Audit-local counterpart of the private helper of
`Correspondence.Pointers`). -/
private theorem ep1_decodeDiscriminantM_inv {M : Type} [Gen.Memory M] {σ : Type} (P : σ → Prop)
    {accessor : σ → Gen.Offset → Size →
      Interp (List (Gen.AbstractByte (Gen.Memory.Provenance M)) × σ)}
    (hacc : ∀ s offset sz bs s', P s → accessor s offset sz = .ok (bs, s') → P s') :
    ∀ (d : Gen.Discriminator) (s s' : σ) (opt : Option Int),
      P s → decodeDiscriminantM (M := M) accessor d s = .ok (opt, s') → P s'
  | .Known _, s, s', opt, hs, h => by
    unfold decodeDiscriminantM at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
    exact hs
  | .Invalid, s, s', opt, hs, h => by
    unfold decodeDiscriminantM at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
    exact hs
  | .Branch offset valueType fallback ⟨children⟩, s, s', opt, hs, h => by
    unfold decodeDiscriminantM at h
    obtain ⟨⟨bs, s1⟩, ha, h⟩ := ep1_bind_ok h
    have hs1 := hacc _ _ _ _ _ hs ha
    obtain ⟨optv, _, h⟩ := ep1_bind_ok h
    cases optv with
    | none =>
      obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
      exact hs1
    | some v =>
      cases v with
      | Int val =>
        exact ep1_decodeDiscriminantChildrenM_inv P hacc val
          (decodeDiscriminantM (M := M) accessor fallback)
          (fun s0 s0' opt0 hs0 hfb => ep1_decodeDiscriminantM_inv P hacc fallback s0 s0' opt0 hs0 hfb)
          children s1 s' opt hs1 h
      | _ =>
        obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
        exact hs1

private theorem ep1_decodeDiscriminantChildrenM_inv {M : Type} [Gen.Memory M] {σ : Type}
    (P : σ → Prop)
    {accessor : σ → Gen.Offset → Size →
      Interp (List (Gen.AbstractByte (Gen.Memory.Provenance M)) × σ)}
    (hacc : ∀ s offset sz bs s', P s → accessor s offset sz = .ok (bs, s') → P s')
    (val : Int) (onFallback : σ → Interp (Option Int × σ))
    (hfb : ∀ (s s' : σ) (opt : Option Int), P s → onFallback s = .ok (opt, s') → P s') :
    ∀ (children : List ((Int × Int) × Gen.Discriminator)) (s s' : σ) (opt : Option Int),
      P s → decodeDiscriminantChildrenM (M := M) accessor val onFallback children s = .ok (opt, s') →
      P s'
  | [], s, s', opt, hs, h => by
    unfold decodeDiscriminantChildrenM at h
    exact hfb s s' opt hs h
  | ((start, end_), child) :: rest, s, s', opt, hs, h => by
    unfold decodeDiscriminantChildrenM at h
    split at h
    · exact ep1_decodeDiscriminantM_inv P hacc child s s' opt hs h
    · exact ep1_decodeDiscriminantChildrenM_inv P hacc val onFallback hfb rest s s' opt hs h

end

/-- **Frame law of `ValueExpr::GetDiscriminant` on every `Memory` `M`** ("value expression
evaluation is reorderable and removable", `spec/lang/step/expressions.md`). A successful
`GetDiscriminant` is `eval_place` followed by nothing but `Memory::load`s:

* every machine field other than `mem` (program, threads and their frames and locals,
  `intptrcast`, locks, global / function / vtable pointers, `stdout`, `stderr`, ...) is
  exactly as `eval_place` left it;
* the data-race access log only grows, by `Load` accesses with `Atomicity::None`;
* the memory is related to the one after `eval_place` by **every** reflexive, transitive
  relation `R` that `Memory::load` preserves.

Instantiating `R` gives `BasicMemory` read-only-ness and Tree Borrows byte preservation
below. -/
theorem ep1_evalValueM_getDiscriminant_frame {M : Type} [Gen.Memory M] [MemoryOps M]
    (R : M → M → Prop) (hrefl : ∀ a, R a a) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hload : ∀ (mem mem' : M) ptr len align bytes,
      MemoryOps.load mem ptr len align = .ok (bytes, mem') → R mem mem')
    (m m1 m' : Gen.Machine M) (place : Gen.PlaceExpr) (rp : Gen.Place M) (ty : Gen.Type)
    (r : Gen.Value M × Gen.Type)
    (hp : evalPlaceM m place = .ok ((rp, ty), m1))
    (h : evalValueM m (.GetDiscriminant place) = .ok (r, m')) :
    { m' with mem := m1.mem } = m1 ∧
    R m1.mem.memory m'.mem.memory ∧
    ∃ extra : List Gen.Access, m'.mem.accesses = m1.mem.accesses ++ extra ∧
      ∀ a ∈ extra, a.ty = .Load ∧ a.atomicity = .None := by
  let P : Gen.Machine M → Prop := fun s =>
    { s with mem := m1.mem } = m1 ∧
    R m1.mem.memory s.mem.memory ∧
    ∃ extra : List Gen.Access, s.mem.accesses = m1.mem.accesses ++ extra ∧
      ∀ a ∈ extra, a.ty = .Load ∧ a.atomicity = .None
  have hP1 : P m1 := ⟨rfl, hrefl _, [], by simp, by simp⟩
  simp only [evalValueM, hp, bind, Except.bind] at h
  cases ty with
  | Enum variants dty discr sz al =>
    dsimp only at h
    split at h
    · simp [ub] at h
    · have hstep : ∀ (s : Gen.Machine M) (off : Gen.Offset) (sz : Size)
          (bs : List (Gen.AbstractByte (Gen.Memory.Provenance M))) (s' : Gen.Machine M),
          P s →
          (do
            let ptr ← ptrOffsetInboundsM s rp.ptr.thin_pointer (off.bytes : Int)
            let (bytes, cm) ← ConcurrentMemory.load s.mem ptr sz ⟨1⟩ .None
            pure (bytes, { s with mem := cm })) = .ok (bs, s') → P s' := by
        intro s off sz bs s' hs hacc
        obtain ⟨ptr, _, hacc⟩ := ep1_bind_ok hacc
        obtain ⟨⟨bytes, cm⟩, hld, hacc⟩ := ep1_bind_ok hacc
        obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hacc)
        unfold ConcurrentMemory.load at hld
        obtain ⟨⟨bytes', mem'⟩, hml, hld⟩ := ep1_bind_ok hld
        obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hld)
        obtain ⟨hframe, hR, extra, hacc', hall⟩ := hs
        refine ⟨hframe, htrans _ _ _ hR (hload _ _ _ _ _ _ hml),
          extra ++ [⟨.Load, .None, ptr.addr, sz⟩], ?_, ?_⟩
        · show s.mem.accesses ++ [_] = _
          rw [hacc', List.append_assoc]
        · intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact hall a ha
          · simp only [List.mem_singleton] at ha
            subst ha
            exact ⟨rfl, rfl⟩
      cases hdd : decodeDiscriminantM (M := M)
          (fun (m : Gen.Machine M) (idx : Gen.Offset) (size : Size) => do
            let ptr ← ptrOffsetInboundsM m rp.ptr.thin_pointer (idx.bytes : Int)
            let (bytes, cm) ← ConcurrentMemory.load m.mem ptr size ⟨1⟩ .None
            pure (bytes, { m with mem := cm })) discr m1 with
      | error e =>
        simp only [bind, Except.bind] at hdd
        rw [hdd] at h
        cases h
      | ok res =>
        obtain ⟨opt, m2⟩ := res
        have hP2 : P m2 := ep1_decodeDiscriminantM_inv P hstep discr m1 m2 opt hP1 hdd
        simp only [bind, Except.bind] at hdd
        rw [hdd] at h
        dsimp only at h
        cases opt with
        | none => simp [ub] at h
        | some dv =>
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact hP2
  | _ => simp [specPanic] at h

/-- **`GetDiscriminant` is read-only on `BasicMemory`** (`Mach`): the machine it returns is the
machine after `eval_place` with the *identical* memory (`mem.memory`, hence every allocation's
bytes, liveness, and address) and identical non-memory state; only the data-race access log
grows, by `Load` / `Atomicity::None` entries. No hypothesis on the place, the enum type, or
the discriminator is needed. -/
theorem ep1_evalValue_getDiscriminant_readonly_bm
    (m m1 m' : Mach) (place : Gen.PlaceExpr) (rp : Gen.Place BM) (ty : Gen.Type)
    (r : Val × Gen.Type)
    (hp : evalPlace m place = .ok ((rp, ty), m1))
    (h : evalValue m (.GetDiscriminant place) = .ok (r, m')) :
    { m' with mem := m1.mem } = m1 ∧
    m'.mem.memory = m1.mem.memory ∧
    ∃ extra : List Gen.Access, m'.mem.accesses = m1.mem.accesses ++ extra ∧
      ∀ a ∈ extra, a.ty = .Load ∧ a.atomicity = .None := by
  rw [← evalPlaceM_bm_eq] at hp
  rw [← evalValueM_bm_eq] at h
  exact ep1_evalValueM_getDiscriminant_frame (M := BM) (fun a b => b = a)
    (fun _ => rfl) (fun _ _ _ hab hbc => hbc.trans hab)
    (fun mem mem' ptr len align bytes hl => BM.load_eq (mem := mem) (mem' := mem') hl)
    m m1 m' place rp ty r hp h

/-- The memory-model-independent content of an allocation: everything except its
aliasing-model `extra` (for Tree Borrows, the borrow tree). -/
def ep1AllocCore {ProvExtra AllocExtra : Type} (a : Gen.Allocation ProvExtra AllocExtra) :
    List (Gen.AbstractByte (Gen.Provenance ProvExtra)) × Gen.Address × Align ×
      Gen.AllocationKind × Bool :=
  (a.data, a.addr, a.align, a.kind, a.live)

/-- `BasicMemory::load` (the generic one underlying `TreeBorrowsMemory::load`) changes at
most the `extra` of the accessed allocation: bytes, address, alignment, kind, liveness, and
the number and order of allocations are preserved. -/
private theorem ep1_BasicMemory_load_core {ProvExtra AllocExtra : Type}
    (mem mem' : Gen.BasicMemory Gen.x86_64 ProvExtra AllocExtra)
    (ptr : Gen.ThinPointer (Gen.Provenance ProvExtra)) (len : Size) (align : Align)
    (handle : AllocExtra → ProvExtra → Gen.Offset → Interp AllocExtra)
    (bytes : List (Gen.AbstractByte (Gen.Provenance ProvExtra)))
    (h : BasicMemory.load mem ptr len align handle = .ok (bytes, mem')) :
    mem'.allocations.map ep1AllocCore = mem.allocations.map ep1AllocCore := by
  unfold BasicMemory.load at h
  split at h
  · simp [ub] at h
  · obtain ⟨chk, _, h⟩ := ep1_bind_ok h
    cases chk with
    | none =>
      obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
      rfl
    | some trip =>
      rcases trip with ⟨id, provExtra, offset⟩
      dsimp only at h
      obtain ⟨alloc, hidx, h⟩ := ep1_bind_ok h
      obtain ⟨extra', _, h⟩ := ep1_bind_ok h
      obtain ⟨allocs', hset, h⟩ := ep1_bind_ok h
      obtain ⟨bs, _, h⟩ := ep1_bind_ok h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
      obtain ⟨_, hi, hget⟩ := ep1_listIndex_int_eq_getElem hidx
      have hallocs : allocs' = mem.allocations.set id._0.toNat { alloc with extra := extra' } := by
        unfold listSet at hset
        split at hset
        · exact (ep1_pure_ok hset).symm
        · simp [specPanic] at hset
      subst hallocs
      show (mem.allocations.set id._0.toNat { alloc with extra := extra' }).map ep1AllocCore = _
      rw [List.map_set]
      have hcore : ep1AllocCore ({ alloc with extra := extra' } :
            Gen.Allocation ProvExtra AllocExtra) =
          (mem.allocations.map ep1AllocCore)[id._0.toNat]'(by simpa using hi) := by
        simp only [List.getElem_map, hget]
        rfl
      rw [hcore, List.set_getElem_self]

/-- **`GetDiscriminant` preserves every byte under Tree Borrows** (`MachTB`): a successful
`GetDiscriminant` leaves all non-memory machine state, the Tree Borrows parameters, and the
content of every allocation (bytes, address, alignment, kind, liveness; same number and order
of allocations) exactly as `eval_place` left them. Only the borrow trees (permission state
machines advanced by the tag reads) and the data-race access log (extended by `Load` /
`Atomicity::None` entries) can change. -/
theorem ep1_evalValueM_getDiscriminant_preserves_bytes_tb
    (m m1 m' : MachTB) (place : Gen.PlaceExpr) (rp : Gen.Place TBM) (ty : Gen.Type)
    (r : Gen.Value TBM × Gen.Type)
    (hp : evalPlaceM m place = .ok ((rp, ty), m1))
    (h : evalValueM m (.GetDiscriminant place) = .ok (r, m')) :
    { m' with mem := m1.mem } = m1 ∧
    (m'.mem.memory.params = m1.mem.memory.params ∧
      m'.mem.memory.mem.allocations.map ep1AllocCore =
        m1.mem.memory.mem.allocations.map ep1AllocCore) ∧
    ∃ extra : List Gen.Access, m'.mem.accesses = m1.mem.accesses ++ extra ∧
      ∀ a ∈ extra, a.ty = .Load ∧ a.atomicity = .None := by
  refine ep1_evalValueM_getDiscriminant_frame (M := TBM)
    (fun a b => b.params = a.params ∧
      b.mem.allocations.map ep1AllocCore = a.mem.allocations.map ep1AllocCore)
    (fun _ => ⟨rfl, rfl⟩)
    (fun _ _ _ hab hbc => ⟨hbc.1.trans hab.1, hbc.2.trans hab.2⟩)
    ?_ m m1 m' place rp ty r hp h
  intro mem mem' ptr len align bytes hl
  change TreeBorrowsMemory.load mem ptr len align = .ok (bytes, mem') at hl
  unfold TreeBorrowsMemory.load at hl
  obtain ⟨⟨bs, bm'⟩, hbl, hl⟩ := ep1_bind_ok hl
  obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hl)
  exact ⟨rfl, ep1_BasicMemory_load_core _ _ _ _ _ _ _ hbl⟩

/-- **`Downcast`, `Variant`, and `Union` add no machine effect of their own** (inversion form,
every `Memory` `M`): whenever one of them succeeds, the machine it returns is exactly the
machine returned by its single sub-evaluation (`eval_place(root)`, `eval_value(data)`,
`eval_value(expr)`), and `Downcast` returns the root place itself (same pointer, same
`aligned` flag). Together with `ep1_evalValueM_getDiscriminant_frame` this covers the
machine effect of every Episode 1 place / value arm. -/
theorem ep1_evalM_downcast_variant_union_add_no_machine_effect
    {M : Type} [Gen.Memory M] [MemoryOps M] (m m' : Gen.Machine M) :
    (∀ root d (r : Gen.Place M × Gen.Type),
      evalPlaceM m (.Downcast root d) = .ok (r, m') →
      ∃ ty, evalPlaceM m root = .ok ((r.1, ty), m')) ∧
    (∀ d data enumTy (r : Gen.Value M × Gen.Type),
      evalValueM m (.Variant d data enumTy) = .ok (r, m') →
      ∃ val vty, evalValueM m data = .ok ((val, vty), m') ∧ r = (.Variant d val, enumTy)) ∧
    (∀ field expr unionTy (r : Gen.Value M × Gen.Type),
      evalValueM m (.Union field expr unionTy) = .ok (r, m') →
      ∃ v, evalValueM m expr = .ok (v, m') ∧ r.2 = unionTy) := by
  refine ⟨?_, ?_, ?_⟩
  · intro root d r h
    simp only [evalPlaceM] at h
    obtain ⟨⟨⟨rp, ty⟩, m1⟩, hroot, h⟩ := ep1_bind_ok h
    cases ty with
    | Enum variants dty discr sz al =>
      dsimp only at h
      cases hmi : mapIndex variants d "variants[discriminant]" with
      | error e => simp [hmi, bind, Except.bind] at h
      | ok var =>
        simp only [hmi, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨_, hroot⟩
    | _ => simp [specPanic, bind, Except.bind] at h
  · intro d data enumTy r h
    simp only [evalValueM] at h
    obtain ⟨⟨⟨val, vty⟩, m1⟩, hd, h⟩ := ep1_bind_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
    exact ⟨val, vty, hd, rfl⟩
  · intro field expr unionTy r h
    cases unionTy with
    | Union fields chunks sz al =>
      rw [ep1_evalValueM_union_complete_spec] at h
      obtain ⟨⟨off, exprTy⟩, _, h⟩ := ep1_bind_ok h
      obtain ⟨⟨⟨val, vty⟩, m1⟩, hev, h⟩ := ep1_bind_ok h
      obtain ⟨encoded, _, h⟩ := ep1_bind_ok h
      obtain ⟨data, _, h⟩ := ep1_bind_ok h
      obtain ⟨chunkData, _, h⟩ := ep1_bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
      exact ⟨(val, vty), hev, rfl⟩
    | _ => simp [evalValueM, specPanic, bind, Except.bind] at h

/-- **Well-formedness of a constructed `Variant` value, exactly.** `ValueExpr::Variant` itself
checks nothing (upstream just builds `Value::Variant { discriminant, data }`). The value it
builds satisfies `check_value` at the enum type exactly when `discriminant` is a declared
variant and the payload satisfies `check_value` at **that variant's type — the very type
`PlaceExpr::Downcast` assigns to the place**; an undeclared discriminant is `check_value`'s
`throw_ub!`, which `typed_store`'s `assert!` then turns into a spec panic (witnessed by
`ep1_variant_union_ill_formed_ast_specPanic_witness`). -/
theorem ep1_evalValueM_variant_checkValue {M : Type} [Gen.Memory M] [MemoryOps M]
    (m m1 : Gen.Machine M) (d : Int) (data : Gen.ValueExpr)
    (variants : List (Int × Gen.Variant)) (dty : Gen.IntType) (discr : Gen.Discriminator)
    (sz : Size) (al : Align) (val : Gen.Value M) (vty : Gen.Type)
    (mOpt : Option (Gen.Machine M))
    (hd : evalValueM m data = .ok ((val, vty), m1)) :
    evalValueM m (.Variant d data (.Enum ⟨variants⟩ dty discr sz al)) =
      .ok ((.Variant d val, .Enum ⟨variants⟩ dty discr sz al), m1) ∧
    checkValueM (.Variant d val) (.Enum ⟨variants⟩ dty discr sz al) mOpt =
      (match mapGet (⟨variants⟩ : Map Int Gen.Variant) d with
       | some var => checkValueM val var.ty mOpt
       | none => ub "Value::Variant: invalid discrimant") := by
  refine ⟨by simp [evalValueM, hd, bind, Except.bind, pure, Except.pure], ?_⟩
  have hlookup := ep1_downcast_variant_lookup_agrees_with_representation (M := M) d variants
  rw [checkValueM]
  cases hget : mapGet (⟨variants⟩ : Map Int Gen.Variant) d with
  | none => exact (hlookup.2 hget).2.2.1 val mOpt
  | some var => exact (hlookup.1 var hget).2.2.1 val mOpt

/-- **The address hypotheses of the `Load ⇒ GetDiscriminant` theorems are necessary, and
`GetDiscriminant` validates nothing beyond what upstream validates.**

1. `ep1_evalValue_load_enum_implies_getDiscriminant_bm` / `_tb` assume `0 ≤ addr` and
   `addr + size < 2^64` for the place. On a machine violating the allocation invariant
   ("`addr + data.len()` fits into a `usize`", `spec/mem/basic.md`) — an allocation at a
   negative address or at `2^64` — a typed `Load` of the enum still succeeds, while
   `GetDiscriminant` stops at `ptr_offset_inbounds`'s
   `assert!((ptr.addr + offset).in_bounds(Unsigned, M::T::PTR_SIZE))`: a spec panic, exactly
   as upstream's assertion would, on both `Mach` and `MachTB`. So neither hypothesis can be
   dropped.
2. `GetDiscriminant` returns `Value::Int(discriminant)` at `discriminant_ty` without a
   `check_value` (as upstream): a `Known(300)` discriminator at `u8` returns `300`, although
   `check_value(300, u8)` is UB. No UB or panic is fabricated for the ill-formed enum type. -/
theorem ep1_getDiscriminant_address_hypotheses_necessary_and_no_result_check_witness :
    let enumBytes : List Byte := .Init 0 none :: List.replicate 7 .Uninit
    let mk (addr : Int) : Mach := ep1MachBM
      [{ data := enumBytes, addr := addr, align := ⟨4⟩, kind := .Stack, live := true, extra := () }]
      [(⟨⟨0⟩⟩, ⟨addr, some (⟨0⟩, ())⟩)]
      [(⟨⟨0⟩⟩, ep1EnumTy)]
    let assertPanic :=
      "assertion failed: (ptr.addr + offset).in_bounds(Unsigned, M::T::PTR_SIZE)"
    let known300Ty : Gen.Type := .Enum ⟨[]⟩ ep1U8 (.Known 300) ⟨0⟩ ⟨1⟩
    let mZst : Mach := ep1MachBM
      [{ data := [], addr := 0x100, align := ⟨1⟩, kind := .Stack, live := true, extra := () }]
      [(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, ())⟩)]
      [(⟨⟨0⟩⟩, known300Ty)]
    -- 0. control: at an in-range address both succeed
    ((∃ m1, evalValue (mk 0x100) (.Load (.Local ⟨⟨0⟩⟩)) =
        .ok ((.Variant 0 (.Tuple []), ep1EnumTy), m1)) ∧
     (∃ m1, evalValue (mk 0x100) (.GetDiscriminant (.Local ⟨⟨0⟩⟩)) =
        .ok ((.Int 0, .Int ep1U8), m1))) ∧
    -- 1a. negative address: `Load` succeeds, `GetDiscriminant` hits the upstream assertion
    ((∃ m1, evalValue (mk (-8)) (.Load (.Local ⟨⟨0⟩⟩)) =
        .ok ((.Variant 0 (.Tuple []), ep1EnumTy), m1)) ∧
     evalValue (mk (-8)) (.GetDiscriminant (.Local ⟨⟨0⟩⟩)) = specPanic assertPanic ∧
     (∃ m1, evalValueM (liftMachToTB (mk (-8))) (.Load (.Local ⟨⟨0⟩⟩)) =
        .ok ((.Variant 0 (.Tuple []), ep1EnumTy), m1)) ∧
     evalValueM (liftMachToTB (mk (-8))) (.GetDiscriminant (.Local ⟨⟨0⟩⟩)) =
        specPanic assertPanic) ∧
    -- 1b. address `2^64`: same
    ((∃ m1, evalValue (mk 0x10000000000000000) (.Load (.Local ⟨⟨0⟩⟩)) =
        .ok ((.Variant 0 (.Tuple []), ep1EnumTy), m1)) ∧
     evalValue (mk 0x10000000000000000) (.GetDiscriminant (.Local ⟨⟨0⟩⟩)) =
        specPanic assertPanic ∧
     (∃ m1, evalValueM (liftMachToTB (mk 0x10000000000000000)) (.Load (.Local ⟨⟨0⟩⟩)) =
        .ok ((.Variant 0 (.Tuple []), ep1EnumTy), m1)) ∧
     evalValueM (liftMachToTB (mk 0x10000000000000000)) (.GetDiscriminant (.Local ⟨⟨0⟩⟩)) =
        specPanic assertPanic) ∧
    -- 2. no `check_value` on the returned discriminant
    (evalValue mZst (.GetDiscriminant (.Local ⟨⟨0⟩⟩)) = .ok ((.Int 300, .Int ep1U8), mZst) ∧
     evalValueM (liftMachToTB mZst) (.GetDiscriminant (.Local ⟨⟨0⟩⟩)) =
       .ok ((.Int 300, .Int ep1U8), liftMachToTB mZst) ∧
     checkValue (.Int 300) (.Int ep1U8) = ub "Value::Int: invalid integer value") := by
  intro enumBytes mk assertPanic known300Ty mZst
  refine ⟨⟨ep1_ok_of_map_fst ?_, ep1_ok_of_map_fst ?_⟩,
    ⟨ep1_ok_of_map_fst ?_, ?_, ep1_ok_of_map_fst ?_, ?_⟩,
    ⟨ep1_ok_of_map_fst ?_, ?_, ep1_ok_of_map_fst ?_, ?_⟩,
    ⟨?_, ?_, ?_⟩⟩
  all_goals ep1_kernel_rfl

/-! #### Tree Borrows only removes behaviours of `GetDiscriminant`: `MachTB` success ⇒ `Mach` success -/

/-- What `GetDiscriminant` can observe of an allocation, on any memory model: the data of its
bytes (provenance erased), its address, and its liveness. -/
def ep1AllocView {ProvExtra AllocExtra : Type} (a : Gen.Allocation ProvExtra AllocExtra) :
    List (Option UInt8) × Gen.Address × Bool :=
  (a.data.map AbstractByte.dataM, a.addr, a.live)

/-- `Type::decode` at `Type::Int` as a function of the byte count and the bytes' data only
(provenance never matters). -/
private def ep1DecodeIntView (vt : Gen.IntType) (len : Nat) (data : Option (List UInt8)) :
    Interp (Option Int) :=
  if len ≠ vt.size.bytes then specPanic "decode of Type::Int with invalid length"
  else
    match data with
    | some d => pure (some (Endianness.decode x86_64.ENDIANNESS vt.signed d))
    | none => pure none

private theorem ep1_decodeIntM_view {M : Type} [Gen.Memory M] (vt : Gen.IntType)
    (bs : List (Gen.AbstractByte (Gen.Memory.Provenance M))) :
    Type.decodeIntM (M := M) vt bs =
      (match ep1DecodeIntView vt bs.length (bs.mapM AbstractByte.dataM) with
       | .ok o => .ok (o.map Gen.Value.Int)
       | .error e => .error e) := by
  obtain ⟨signed, size⟩ := vt
  unfold Type.decodeIntM ep1DecodeIntView
  by_cases hlen : bs.length ≠ size.bytes
  · simp [hlen, specPanic]
  · simp only [hlen, ↓reduceIte]
    cases bs.mapM AbstractByte.dataM <;> rfl

private theorem ep1_mapM_dataM_congr {P1 P2 : Type} :
    ∀ (bs1 : List (Gen.AbstractByte P1)) (bs2 : List (Gen.AbstractByte P2)),
      bs1.map AbstractByte.dataM = bs2.map AbstractByte.dataM →
      bs1.length = bs2.length ∧ bs1.mapM AbstractByte.dataM = bs2.mapM AbstractByte.dataM
  | [], [], _ => ⟨rfl, rfl⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | b1 :: t1, b2 :: t2, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hlen, hm⟩ := ep1_mapM_dataM_congr t1 t2 h.2
    refine ⟨by simp [hlen], ?_⟩
    simp only [List.mapM_cons, h.1, hm]

mutual

/-- Two-memory simulation of `decode_discriminant`: if every accessor call on the first
memory is matched by one on the second returning bytes with the same data, a successful
decode on the first memory is matched by a decode with the same result on the second. -/
private theorem ep1_decodeDiscriminantM_sim2 {M1 M2 : Type} [Gen.Memory M1] [Gen.Memory M2]
    {σ1 σ2 : Type} (Rel : σ1 → σ2 → Prop)
    (acc1 : σ1 → Gen.Offset → Size →
      Interp (List (Gen.AbstractByte (Gen.Memory.Provenance M1)) × σ1))
    (acc2 : σ2 → Gen.Offset → Size →
      Interp (List (Gen.AbstractByte (Gen.Memory.Provenance M2)) × σ2))
    (hstep : ∀ s1 s2 off sz bs1 s1', Rel s1 s2 → acc1 s1 off sz = .ok (bs1, s1') →
      ∃ bs2 s2', acc2 s2 off sz = .ok (bs2, s2') ∧
        bs1.map AbstractByte.dataM = bs2.map AbstractByte.dataM ∧ Rel s1' s2') :
    ∀ (d : Gen.Discriminator) (res : Option Int) (s1 s1' : σ1) (s2 : σ2),
      Rel s1 s2 → decodeDiscriminantM (M := M1) acc1 d s1 = .ok (res, s1') →
      ∃ s2', decodeDiscriminantM (M := M2) acc2 d s2 = .ok (res, s2') ∧ Rel s1' s2'
  | .Known val, res, s1, s1', s2, hrel, h => by
    unfold decodeDiscriminantM at h ⊢
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
    exact ⟨s2, rfl, hrel⟩
  | .Invalid, res, s1, s1', s2, hrel, h => by
    unfold decodeDiscriminantM at h ⊢
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
    exact ⟨s2, rfl, hrel⟩
  | .Branch off vt fallback ⟨children⟩, res, s1, s1', s2, hrel, h => by
    unfold decodeDiscriminantM at h ⊢
    obtain ⟨⟨bs1, s1a⟩, ha1, h⟩ := ep1_bind_ok h
    obtain ⟨bs2, s2a, ha2, hbytes, hrela⟩ := hstep s1 s2 off vt.size bs1 s1a hrel ha1
    rw [ha2]
    dsimp only [bind, Except.bind] at h ⊢
    obtain ⟨hlen, hm⟩ := ep1_mapM_dataM_congr bs1 bs2 hbytes
    rw [ep1_decodeIntM_view] at h ⊢
    rw [← hlen, ← hm]
    cases hv : ep1DecodeIntView vt bs1.length (bs1.mapM AbstractByte.dataM) with
    | error e => rw [hv] at h; cases h
    | ok o =>
      rw [hv] at h
      cases o with
      | none =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
        exact ⟨s2a, rfl, hrela⟩
      | some tag =>
        exact ep1_decodeDiscriminantChildrenM_sim2 Rel acc1 acc2 hstep tag
          (decodeDiscriminantM (M := M1) acc1 fallback)
          (decodeDiscriminantM (M := M2) acc2 fallback)
          (fun res' t1 t1' t2 hr hf =>
            ep1_decodeDiscriminantM_sim2 Rel acc1 acc2 hstep fallback res' t1 t1' t2 hr hf)
          children res s1a s1' s2a hrela h

private theorem ep1_decodeDiscriminantChildrenM_sim2 {M1 M2 : Type} [Gen.Memory M1]
    [Gen.Memory M2] {σ1 σ2 : Type} (Rel : σ1 → σ2 → Prop)
    (acc1 : σ1 → Gen.Offset → Size →
      Interp (List (Gen.AbstractByte (Gen.Memory.Provenance M1)) × σ1))
    (acc2 : σ2 → Gen.Offset → Size →
      Interp (List (Gen.AbstractByte (Gen.Memory.Provenance M2)) × σ2))
    (hstep : ∀ s1 s2 off sz bs1 s1', Rel s1 s2 → acc1 s1 off sz = .ok (bs1, s1') →
      ∃ bs2 s2', acc2 s2 off sz = .ok (bs2, s2') ∧
        bs1.map AbstractByte.dataM = bs2.map AbstractByte.dataM ∧ Rel s1' s2')
    (tag : Int)
    (fb1 : σ1 → Interp (Option Int × σ1)) (fb2 : σ2 → Interp (Option Int × σ2))
    (hfb : ∀ res t1 t1' t2, Rel t1 t2 → fb1 t1 = .ok (res, t1') →
      ∃ t2', fb2 t2 = .ok (res, t2') ∧ Rel t1' t2') :
    ∀ (children : List ((Int × Int) × Gen.Discriminator)) (res : Option Int) (s1 s1' : σ1)
      (s2 : σ2),
      Rel s1 s2 →
      decodeDiscriminantChildrenM (M := M1) acc1 tag fb1 children s1 = .ok (res, s1') →
      ∃ s2', decodeDiscriminantChildrenM (M := M2) acc2 tag fb2 children s2 = .ok (res, s2') ∧
        Rel s1' s2'
  | [], res, s1, s1', s2, hrel, h => by
    unfold decodeDiscriminantChildrenM at h ⊢
    exact hfb res s1 s1' s2 hrel h
  | ((lo, hi), child) :: rest, res, s1, s1', s2, hrel, h => by
    unfold decodeDiscriminantChildrenM at h ⊢
    by_cases hcond : lo ≤ tag ∧ tag < hi
    · simp only [hcond, and_self, ↓reduceIte] at h ⊢
      exact ep1_decodeDiscriminantM_sim2 Rel acc1 acc2 hstep child res s1 s1' s2 hrel h
    · simp only [hcond, ↓reduceIte] at h ⊢
      exact ep1_decodeDiscriminantChildrenM_sim2 Rel acc1 acc2 hstep tag fb1 fb2 hfb rest res
        s1 s1' s2 hrel h

end

/-- What `GetDiscriminant` can observe of a thin pointer, on any memory model: its address and
the allocation it points into (the aliasing-model part of the provenance is erased). -/
def ep1PtrView {Extra : Type} (p : Gen.ThinPointer (Gen.Provenance Extra)) :
    Gen.Address × Option Gen.AllocId :=
  (p.addr, p.provenance.map Prod.fst)

private theorem ep1_alloc_view_of_index {E1 A1 : Type}
    (as1 : List (Gen.Allocation E1 A1)) (as2 : List (Gen.Allocation Unit Unit))
    (hmem : as1.map ep1AllocView = as2.map ep1AllocView) (idx : Int) (what : String)
    (a1 : Gen.Allocation E1 A1) (h : listIndex as1 idx what = .ok a1) :
    0 ≤ idx ∧ ∃ hi2 : idx.toNat < as2.length, ep1AllocView a1 = ep1AllocView as2[idx.toNat] := by
  obtain ⟨hnn, hi, hget⟩ := ep1_listIndex_int_eq_getElem h
  have hlenEq : as1.length = as2.length := by
    simpa using congrArg List.length hmem
  have hi2 : idx.toNat < as2.length := hlenEq ▸ hi
  refine ⟨hnn, hi2, ?_⟩
  have h1 : (as1.map ep1AllocView)[idx.toNat]? = some (ep1AllocView a1) := by
    simp [List.getElem?_map, List.getElem?_eq_getElem hi, hget]
  have h2 : (as2.map ep1AllocView)[idx.toNat]? = some (ep1AllocView as2[idx.toNat]) := by
    simp [List.getElem?_map, List.getElem?_eq_getElem hi2]
  rw [hmem, h2] at h1
  exact (Option.some.inj h1).symm

/-- `check_ptr` on any `BasicMemory`-backed memory (in particular Tree Borrows) succeeding
implies `check_ptr` on `BasicMemory<x86_64>` succeeding with the same allocation and offset,
for memories and pointers with the same `GetDiscriminant`-observable view. -/
private theorem ep1_check_ptr_any_to_bm {E1 A1 : Type}
    (mem1 : Gen.BasicMemory Gen.x86_64 E1 A1) (mem2 : BM)
    (p1 : Gen.ThinPointer (Gen.Provenance E1)) (p2 : Ptr) (len : Size)
    (hmem : mem1.allocations.map ep1AllocView = mem2.allocations.map ep1AllocView)
    (hptr : ep1PtrView p1 = ep1PtrView p2)
    (r1 : Option (Gen.AllocId × E1 × Size))
    (h : BasicMemory.check_ptr mem1 p1 len = .ok r1) :
    ∃ r2, BM.check_ptr mem2 p2 len = .ok r2 ∧
      r1.map (fun t => (t.1, t.2.2)) = r2.map (fun t => (t.1, t.2.2)) := by
  unfold BasicMemory.check_ptr at h
  unfold BM.check_ptr
  have haddr : p1.addr = p2.addr := congrArg Prod.fst hptr
  have hprov : p1.provenance.map Prod.fst = p2.provenance.map Prod.fst := congrArg Prod.snd hptr
  by_cases hz : len.bytes = 0
  · simp only [hz, ↓reduceIte] at h ⊢
    obtain rfl := ep1_pure_ok h
    exact ⟨none, rfl, rfl⟩
  · simp only [hz, ↓reduceIte] at h ⊢
    cases hp1 : p1.provenance with
    | none => simp [hp1, ub] at h
    | some ip1 =>
      obtain ⟨id, e1⟩ := ip1
      cases hp2 : p2.provenance with
      | none => simp [hp1, hp2] at hprov
      | some ip2 =>
        obtain ⟨id2, e2⟩ := ip2
        have hid : id = id2 := by simpa [hp1, hp2] using hprov
        subst hid
        simp only [hp1] at h
        dsimp only
        obtain ⟨a1, hidx, h⟩ := ep1_bind_ok h
        obtain ⟨hnn, hi2, hview⟩ := ep1_alloc_view_of_index _ _ hmem _ _ a1 hidx
        rw [ep1_listIndex_int_of_getElem _ hnn hi2]
        simp only [ep1AllocView, Prod.mk.injEq] at hview
        obtain ⟨hdata, haddrA, hlive⟩ := hview
        have hsize : (Allocation.size a1).bytes =
            (Allocation.size mem2.allocations[id._0.toNat]).bytes := by
          simpa [Allocation.size] using congrArg List.length hdata
        simp only [bind, Except.bind, ← hlive, ← haddrA, ← hsize, ← haddr]
        split at h
        · simp [ub] at h
        · rename_i hl
          simp only [hl, Bool.false_eq_true, ↓reduceIte]
          split at h
          · simp [ub] at h
          · rename_i hb
            simp only [hb, ↓reduceIte]
            obtain rfl := ep1_pure_ok h
            exact ⟨_, rfl, rfl⟩

private theorem ep1_subslice_dataM_congr {P1 P2 : Type}
    (xs1 : List (Gen.AbstractByte P1)) (xs2 : List (Gen.AbstractByte P2)) (start len : Int)
    (hdata : xs1.map AbstractByte.dataM = xs2.map AbstractByte.dataM)
    (bs1 : List (Gen.AbstractByte P1)) (h : subsliceWithLength xs1 start len = .ok bs1) :
    ∃ bs2, subsliceWithLength xs2 start len = .ok bs2 ∧
      bs1.map AbstractByte.dataM = bs2.map AbstractByte.dataM := by
  have hlen : xs1.length = xs2.length := by simpa using congrArg List.length hdata
  unfold subsliceWithLength at h ⊢
  rw [← hlen]
  split at h
  · rename_i hc
    simp only [hc, and_self, ↓reduceIte]
    obtain rfl := ep1_pure_ok h
    refine ⟨_, rfl, ?_⟩
    rw [List.map_take, List.map_drop, List.map_take, List.map_drop, hdata]
  · simp [specPanic] at h

/-- `load` on any `BasicMemory`-backed memory (in particular `TreeBorrowsMemory::load`, whose
`handle_extra` performs the Tree Borrows read access) succeeding implies `BasicMemory::load`
on `BasicMemory<x86_64>` succeeding — leaving that memory unchanged — with bytes carrying the
same data. -/
private theorem ep1_load_any_to_bm {E1 A1 : Type}
    (mem1 mem1' : Gen.BasicMemory Gen.x86_64 E1 A1) (mem2 : BM)
    (p1 : Gen.ThinPointer (Gen.Provenance E1)) (p2 : Ptr) (len : Size) (align : Align)
    (handle : A1 → E1 → Gen.Offset → Interp A1)
    (hmem : mem1.allocations.map ep1AllocView = mem2.allocations.map ep1AllocView)
    (hptr : ep1PtrView p1 = ep1PtrView p2)
    (bs1 : List (Gen.AbstractByte (Gen.Provenance E1)))
    (h : BasicMemory.load mem1 p1 len align handle = .ok (bs1, mem1')) :
    ∃ bs2, BM.load mem2 p2 len align = .ok (bs2, mem2) ∧
      bs1.map AbstractByte.dataM = bs2.map AbstractByte.dataM := by
  suffices hs : ∃ bs2 mem2', BM.load mem2 p2 len align = .ok (bs2, mem2') ∧
      bs1.map AbstractByte.dataM = bs2.map AbstractByte.dataM by
    obtain ⟨bs2, mem2', hl, hd⟩ := hs
    have := BM.load_eq hl
    subst this
    exact ⟨bs2, hl, hd⟩
  have haddr : p1.addr = p2.addr := congrArg Prod.fst hptr
  unfold BasicMemory.load at h
  unfold BM.load
  rw [← haddr]
  split at h
  · simp [ub] at h
  · rename_i hal
    simp only [hal]
    obtain ⟨r1, hchk, h⟩ := ep1_bind_ok h
    obtain ⟨r2, hchk2, hr⟩ := ep1_check_ptr_any_to_bm mem1 mem2 p1 p2 len hmem hptr r1 hchk
    simp only [hchk2, bind, Except.bind]
    cases r1 with
    | none =>
      cases r2 with
      | none =>
        obtain ⟨rfl, _⟩ := Prod.mk.inj (ep1_pure_ok h)
        exact ⟨[], mem2, rfl, rfl⟩
      | some t => simp at hr
    | some t1 =>
      cases r2 with
      | none => simp at hr
      | some t2 =>
        obtain ⟨id, e1, off⟩ := t1
        obtain ⟨id2, e2, off2⟩ := t2
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        dsimp only at h ⊢
        obtain ⟨a1, hidx, h⟩ := ep1_bind_ok h
        obtain ⟨_, _, h⟩ := ep1_bind_ok h
        obtain ⟨_, _, h⟩ := ep1_bind_ok h
        obtain ⟨bs, hsub, h⟩ := ep1_bind_ok h
        obtain ⟨rfl, _⟩ := Prod.mk.inj (ep1_pure_ok h)
        obtain ⟨hnn, hi2, hview⟩ := ep1_alloc_view_of_index _ _ hmem _ _ a1 hidx
        simp only [ep1AllocView, Prod.mk.injEq] at hview
        obtain ⟨bs2, hsub2, hd⟩ :=
          ep1_subslice_dataM_congr a1.data mem2.allocations[id._0.toNat].data _ _ hview.1 bs hsub
        rw [ep1_listIndex_int_of_getElem _ hnn hi2]
        simp only [ep1_listSet_int_of_lt _ _ hnn hi2, hsub2]
        exact ⟨bs2, _, rfl, hd⟩

/-- `ptr_offset_inbounds` succeeding on `MachTB` implies it succeeding on `Mach`, with the
same resulting address and allocation. -/
private theorem ep1_ptrOffsetInbounds_tb_to_bm (sTB : MachTB) (sBM : Mach)
    (p1 : Gen.ThinPointer Gen.TreeBorrowsProvenance) (p2 : Ptr) (off : Int)
    (hmem : sTB.mem.memory.mem.allocations.map ep1AllocView =
      sBM.mem.memory.allocations.map ep1AllocView)
    (hptr : ep1PtrView p1 = ep1PtrView p2)
    (p1' : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (h : ptrOffsetInboundsM sTB p1 off = .ok p1') :
    ∃ p2', ptrOffsetInboundsM (M := BM) sBM p2 off = .ok p2' ∧ ep1PtrView p1' = ep1PtrView p2' := by
  have haddr : p1.addr = p2.addr := congrArg Prod.fst hptr
  have hprov : p1.provenance.map Prod.fst = p2.provenance.map Prod.fst := congrArg Prod.snd hptr
  unfold ptrOffsetInboundsM at h ⊢
  obtain ⟨u, hsd, h⟩ := ep1_bind_ok h
  have hsd2 : ConcurrentMemory.signed_dereferenceable (M := BM) sBM.mem p2 off = .ok () := by
    change TreeBorrowsMemory.signed_dereferenceable sTB.mem.memory p1 off = .ok u at hsd
    change BM.signed_dereferenceable sBM.mem.memory p2 off = .ok ()
    unfold TreeBorrowsMemory.signed_dereferenceable TreeBorrowsMemory.dereferenceable at hsd
    unfold BM.signed_dereferenceable BM.dereferenceable
    split at hsd
    · rename_i hpos
      simp only [hpos, ↓reduceIte]
      obtain ⟨r1, hchk, _⟩ := ep1_bind_ok hsd
      obtain ⟨r2, hchk2, _⟩ :=
        ep1_check_ptr_any_to_bm sTB.mem.memory.mem sBM.mem.memory p1 p2 _ hmem hptr r1 hchk
      simp only [hchk2, bind, Except.bind, pure, Except.pure]
    · rename_i hpos
      simp only [hpos, ↓reduceIte]
      obtain ⟨r1, hchk, _⟩ := ep1_bind_ok hsd
      have hptr' : ep1PtrView ({ p1 with addr := p1.addr + off } :
            Gen.ThinPointer Gen.TreeBorrowsProvenance) =
          ep1PtrView ({ p2 with addr := p2.addr + off } : Ptr) := by
        simp only [ep1PtrView, haddr, hprov]
      obtain ⟨r2, hchk2, _⟩ :=
        ep1_check_ptr_any_to_bm sTB.mem.memory.mem sBM.mem.memory _ _ _ hmem hptr' r1 hchk
      simp only [hchk2, bind, Except.bind, pure, Except.pure]
  simp only [hsd2, bind, Except.bind, ← haddr]
  split at h
  · simp [specPanic] at h
  · rename_i h1
    simp only [h1, Bool.false_eq_true, ↓reduceIte]
    split at h
    · simp [specPanic] at h
    · rename_i h2
      simp only [h2, Bool.false_eq_true, ↓reduceIte]
      obtain rfl := ep1_pure_ok h
      refine ⟨_, rfl, ?_⟩
      simp only [ep1PtrView, haddr, hprov]

/-- **Tree Borrows only removes behaviours of `GetDiscriminant`.** Take a `MachTB` and a `Mach`
evaluation of the same enum place whose results agree on what `GetDiscriminant` can observe:
the places have the same address, allocation, and `aligned` flag (`ep1PtrView`), and the two
memories hold allocations with the same byte data, addresses, and liveness (`ep1AllocView`;
provenance and borrow trees are free to differ — `liftMachToTB` is one instance). Then
whenever `GetDiscriminant` succeeds under Tree Borrows it also succeeds on `BasicMemory`
with the **same discriminant at the same type**.

Together with the witnesses in which `Mach` succeeds while `MachTB` raises Tree Borrows UB
(`ep1_getDiscriminant_tree_borrows_read_access_witness`,
`ep1_getDiscriminant_tree_borrows_nested_gap_byte_witness`), this pins the `Mach` / `MachTB`
divergence of `GetDiscriminant` exactly: the aliasing model can only turn a `Mach` success
into UB, never change the discriminant and never make a `Mach` failure succeed. -/
theorem ep1_getDiscriminant_tb_success_implies_bm_success
    (mTB mTB1 mTB' : MachTB) (m m1 : Mach) (place : Gen.PlaceExpr)
    (rpTB : Gen.Place TBM) (rpBM : Gen.Place BM) (ty : Gen.Type)
    (r : Gen.Value TBM × Gen.Type)
    (hpTB : evalPlaceM mTB place = .ok ((rpTB, ty), mTB1))
    (hpBM : evalPlace m place = .ok ((rpBM, ty), m1))
    (hptr : ep1PtrView rpTB.ptr.thin_pointer = ep1PtrView rpBM.ptr.thin_pointer)
    (hal : rpTB.aligned = rpBM.aligned)
    (hmem : mTB1.mem.memory.mem.allocations.map ep1AllocView =
      m1.mem.memory.allocations.map ep1AllocView)
    (h : evalValueM mTB (.GetDiscriminant place) = .ok (r, mTB')) :
    ∃ (x : Int) (dty : Gen.IntType) (m' : Mach),
      r = (.Int x, .Int dty) ∧
      evalValue m (.GetDiscriminant place) = .ok ((.Int x, .Int dty), m') := by
  rw [← evalPlaceM_bm_eq] at hpBM
  simp only [evalValueM, hpTB, bind, Except.bind] at h
  cases ty with
  | Enum variants dty discr sz al =>
    dsimp only at h
    split at h
    · simp [ub] at h
    · rename_i halTB
      let accTB := fun (s : MachTB) (idx : Gen.Offset) (size : Size) => do
        let ptr ← ptrOffsetInboundsM s rpTB.ptr.thin_pointer (idx.bytes : Int)
        let (bytes, cm) ← ConcurrentMemory.load s.mem ptr size ⟨1⟩ .None
        pure (bytes, { s with mem := cm })
      let accBM := fun (s : Mach) (idx : Gen.Offset) (size : Size) => do
        let ptr ← ptrOffsetInboundsM (M := BM) s rpBM.ptr.thin_pointer (idx.bytes : Int)
        let (bytes, cm) ← ConcurrentMemory.load (M := BM) s.mem ptr size ⟨1⟩ .None
        pure (bytes, { s with mem := cm })
      let Rel : MachTB → Mach → Prop := fun sTB sBM =>
        sTB.mem.memory.mem.allocations.map ep1AllocView =
          sBM.mem.memory.allocations.map ep1AllocView
      have hstep : ∀ (s1 : MachTB) (s2 : Mach) off sz bs1 s1', Rel s1 s2 →
          accTB s1 off sz = .ok (bs1, s1') →
          ∃ bs2 s2', accBM s2 off sz = .ok (bs2, s2') ∧
            bs1.map AbstractByte.dataM = bs2.map AbstractByte.dataM ∧ Rel s1' s2' := by
        intro s1 s2 off sz bs1 s1' hrel hacc
        obtain ⟨p1', hpo, hacc⟩ := ep1_bind_ok hacc
        obtain ⟨p2', hpo2, hview'⟩ :=
          ep1_ptrOffsetInbounds_tb_to_bm s1 s2 _ _ _ hrel hptr p1' hpo
        obtain ⟨⟨bytes, cm⟩, hld, hacc⟩ := ep1_bind_ok hacc
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ep1_pure_ok hacc)
        unfold ConcurrentMemory.load at hld
        obtain ⟨⟨bytes', tbm'⟩, hml, hld⟩ := ep1_bind_ok hld
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ep1_pure_ok hld)
        change TreeBorrowsMemory.load s1.mem.memory p1' sz ⟨1⟩ = .ok (bytes', tbm') at hml
        unfold TreeBorrowsMemory.load at hml
        obtain ⟨⟨bs, bm'⟩, hbl, hml⟩ := ep1_bind_ok hml
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ep1_pure_ok hml)
        obtain ⟨bs2, hbmload, hd⟩ :=
          ep1_load_any_to_bm s1.mem.memory.mem bm' s2.mem.memory p1' p2' sz ⟨1⟩ _ hrel hview' bs hbl
        have hml2 : MemoryOps.load (M := BM) s2.mem.memory p2' sz ⟨1⟩ =
            .ok (bs2, s2.mem.memory) := hbmload
        let cm2 : Gen.ConcurrentMemory BM :=
          ⟨s2.mem.memory, s2.mem.accesses ++ [⟨.Load, .None, p2'.addr, sz⟩]⟩
        refine ⟨bs2, { s2 with mem := cm2 }, ?_, hd, ?_⟩
        · simp only [accBM, cm2, hpo2, ConcurrentMemory.load, hml2, bind, Except.bind, pure,
            Except.pure]
        · have hcore := ep1_BasicMemory_load_core _ _ _ _ _ _ _ hbl
          have hviewEq : bm'.allocations.map ep1AllocView =
              s1.mem.memory.mem.allocations.map ep1AllocView := by
            have := congrArg (List.map (fun (c : List (Gen.AbstractByte Gen.TreeBorrowsProvenance) ×
                Gen.Address × Align × Gen.AllocationKind × Bool) =>
                (c.1.map AbstractByte.dataM, c.2.1, c.2.2.2.2))) hcore
            rw [List.map_map, List.map_map] at this
            exact this
          show bm'.allocations.map ep1AllocView = s2.mem.memory.allocations.map ep1AllocView
          rw [hviewEq]
          exact hrel
      cases hdd : decodeDiscriminantM (M := TBM) accTB discr mTB1 with
      | error e =>
        simp only [accTB, bind, Except.bind] at hdd
        rw [hdd] at h
        cases h
      | ok res =>
        obtain ⟨opt, m2⟩ := res
        obtain ⟨s2', hdd2, _⟩ :=
          ep1_decodeDiscriminantM_sim2 Rel accTB accBM hstep discr opt mTB1 m2 m1 hmem hdd
        simp only [accTB, bind, Except.bind] at hdd
        rw [hdd] at h
        dsimp only at h
        cases opt with
        | none => simp [ub] at h
        | some x =>
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          refine ⟨x, dty, s2', rfl, ?_⟩
          rw [← evalValueM_bm_eq]
          have halBM : rpBM.aligned = true := by
            rw [← hal]
            cases hra : rpTB.aligned
            · simp [hra] at halTB
            · rfl
          simp only [evalValueM, hpBM, halBM, bind, Except.bind, Bool.not_true,
            Bool.false_eq_true, ↓reduceIte]
          simp only [accBM, bind, Except.bind] at hdd2
          rw [hdd2]
          rfl
  | _ => simp [specPanic] at h

/-- `liftMachToTB` preserves what `GetDiscriminant` can observe of every allocation. -/
theorem ep1_liftMachToTB_allocView (m : Mach) :
    (liftMachToTB m).mem.memory.mem.allocations.map ep1AllocView =
      m.mem.memory.allocations.map ep1AllocView := by
  show (m.mem.memory.allocations.map liftAllocTB).map ep1AllocView = _
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  simp only [Function.comp, ep1AllocView, liftAllocTB, List.map_map, Prod.mk.injEq, and_true]
  apply List.map_congr_left
  intro b _
  cases b <;> rfl

private theorem ep1_listIndex_map {α β : Type} (f : α → β) (xs : List α) (i : Int)
    (what : String) :
    listIndex (xs.map f) i what =
      (match listIndex xs i what with
       | .ok a => .ok (f a)
       | .error e => .error e) := by
  unfold listIndex
  by_cases hi : 0 ≤ i
  · simp only [hi, ↓reduceIte, List.getElem?_map]
    cases xs[i.toNat]? <;> rfl
  · simp only [hi, ↓reduceIte]
    rfl

private theorem ep1_mapGet_lift_locals (locals : Map Gen.LocalName Ptr) (name : Gen.LocalName) :
    mapGet (⟨locals.entries.map fun (k, p) => (k, liftThinPtrTB p)⟩ :
        Map Gen.LocalName (Gen.ThinPointer Gen.TreeBorrowsProvenance)) name =
      (mapGet locals name).map liftThinPtrTB := by
  unfold mapGet
  dsimp only
  induction locals.entries with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, p⟩ := e
    by_cases hk : k = name
    · simp [List.find?, hk]
    · simp only [List.map_cons, List.find?, hk, decide_false]
      exact ih

/-- `eval_place(Local)` on a lifted machine is the lift of `eval_place(Local)` on the
`BasicMemory` machine. -/
private theorem ep1_evalPlaceM_local_lift (m : Mach) (name : Gen.LocalName) :
    evalPlaceM (liftMachToTB m) (.Local name) =
      (match evalPlace m (.Local name) with
       | .ok ((rp, ty), _) =>
         .ok ((⟨⟨liftThinPtrTB rp.ptr.thin_pointer, none⟩, rp.aligned⟩, ty), liftMachToTB m)
       | .error e => .error e) := by
  have hthreads : (liftMachToTB m).threads = m.threads.map liftThreadTB := rfl
  have hact : (liftMachToTB m).active_thread = m.active_thread := rfl
  simp only [evalPlaceM, evalPlace, curFrameM, curFrame, activeThreadM, activeThread, hthreads,
    hact, ep1_listIndex_map, bind, Except.bind]
  cases hth : listIndex m.threads m.active_thread "self.threads[self.active_thread]" with
  | error e => rfl
  | ok th =>
    dsimp only
    have hlast : (liftThreadTB th).stack.getLast? = th.stack.getLast?.map liftFrameTB := by
      simp [liftThreadTB, List.getLast?_map]
    rw [hlast]
    cases hfr : th.stack.getLast? with
    | none => rfl
    | some fr =>
      simp only [Option.map_some]
      have hfunc : (liftFrameTB fr).func = fr.func := rfl
      have hlocals : mapGet (liftFrameTB fr).locals name =
          (mapGet fr.locals name).map liftThinPtrTB := ep1_mapGet_lift_locals fr.locals name
      simp only [pure, Except.pure, hfunc, hlocals]
      cases hty : mapIndex fr.func.locals name "self.cur_frame().func.locals[name]" with
      | error e => rfl
      | ok ty =>
        dsimp only
        cases hg : mapGet fr.locals name with
        | none => rfl
        | some p => rfl

/-- **Hypothesis-free instance for locals of a lifted machine**: on `liftMachToTB m`, whenever
`GetDiscriminant` of a local succeeds under Tree Borrows, it succeeds on the `BasicMemory`
machine `m` itself with the same discriminant at the same type. (The premises of
`ep1_getDiscriminant_tb_success_implies_bm_success` are discharged: the lifted local place has
the same address / allocation / alignment, and lifting preserves every allocation's observable
view.) -/
theorem ep1_getDiscriminant_local_lifted_tb_success_implies_bm_success
    (m : Mach) (name : Gen.LocalName) (r : Gen.Value TBM × Gen.Type) (mTB' : MachTB)
    (h : evalValueM (liftMachToTB m) (.GetDiscriminant (.Local name)) = .ok (r, mTB')) :
    ∃ (x : Int) (dty : Gen.IntType) (m' : Mach),
      r = (.Int x, .Int dty) ∧
      evalValue m (.GetDiscriminant (.Local name)) = .ok ((.Int x, .Int dty), m') := by
  have hlift := ep1_evalPlaceM_local_lift m name
  cases hpBM : evalPlace m (.Local name) with
  | error e =>
    rw [hpBM] at hlift
    have := (ep1_evalM_type_mismatch_panics_and_error_propagation (liftMachToTB m)
      (liftMachToTB m)).2.2.2.2.1 (.Local name) e hlift
    rw [this] at h
    cases h
  | ok res =>
    obtain ⟨⟨rp, ty⟩, m1⟩ := res
    rw [hpBM] at hlift
    have hm1 : m1 = m := evalPlace_derefFree_mach (.Local name) rfl m _ _ hpBM
    subst hm1
    refine ep1_getDiscriminant_tb_success_implies_bm_success (liftMachToTB m1) (liftMachToTB m1)
      mTB' m1 m1 (.Local name) _ rp ty r hlift hpBM ?_ rfl (ep1_liftMachToTB_allocView m1) h
    simp only [ep1PtrView, liftThinPtrTB, Option.map_map, Prod.mk.injEq, true_and]
    cases rp.ptr.thin_pointer.provenance <;> rfl

/-! ### `[adv A2]` Tree Borrows `Write → Read` idempotence, universal `SetDiscriminant → GetDiscriminant` roundtrip (Mach & MachTB), structural `PlaceExpr` `liftMachToTB` exact biconditional & compositional `Downcast`/`Field` TB⇒BM transfer, arbitrary-chunk `Union` `encodeM` totality + disjoint-chunk roundtrip, and gapped-union / nested-enum witness -/

/-- **Tree Borrows `Write → Read` idempotence:** for every `Permission` (`Unprot` or `Prot`)
and every `NodeRelation` (`Local` or `Foreign`), once a `Write` transition succeeds yielding
`p'`, a subsequent `Read` transition at the same relation succeeds and leaves `p'` unchanged.
Symmetric partner to `ep1_tb_permission_read_idempotent` (`Read → Read`). -/
theorem ep1_tb_permission_write_then_read_idempotent (p p' : Gen.Permission)
    (rel : Gen.NodeRelation) (h : Permission.transition p .Write rel = .ok p') :
    Permission.transition p' .Read rel = .ok p' := by
  cases p with
  | Unprot u =>
    cases u <;> cases rel <;>
      simp [Permission.transition, PermissionUnprot.transition,
        PermissionUnprot.local_write, PermissionUnprot.foreign_write,
        ub, bind, Except.bind, pure, Except.pure] at h
    all_goals subst h; rfl
  | Prot u =>
    cases u with
    | Reserved b1 b2 =>
      cases b1 <;> cases b2 <;> cases rel <;>
        simp [Permission.transition, PermissionProt.transition,
          PermissionProt.local_write, PermissionProt.foreign_write,
          ub, bind, Except.bind, pure, Except.pure] at h
      all_goals subst h; rfl
    | Frozen b =>
      cases b <;> cases rel <;>
        simp [Permission.transition, PermissionProt.transition,
          PermissionProt.local_write, PermissionProt.foreign_write,
          ub, bind, Except.bind, pure, Except.pure] at h
      all_goals subst h; rfl
    | _ =>
      cases rel <;>
        simp [Permission.transition, PermissionProt.transition,
          PermissionProt.local_write, PermissionProt.foreign_write,
          ub, bind, Except.bind, pure, Except.pure] at h
      all_goals subst h; rfl

private theorem ep1_transitionRange_preserves_other (rel : Gen.NodeRelation) (acc : Gen.AccessKind) :
    ∀ (off rem : Nat) (perms perms' : List Gen.Permission),
      Node.transitionRange rel acc off rem perms = .ok perms' →
      ∃ hlen : perms'.length = perms.length,
        ∀ i, i < off → (hi : i < perms.length) → perms'[i]'(hlen ▸ hi) = perms[i]
  | off, 0, perms, perms', h => by
    have hp := ep1_pure_ok h; subst hp
    exact ⟨rfl, fun _ _ _ => rfl⟩
  | off, rem + 1, perms, perms', h => by
    unfold Node.transitionRange at h
    obtain ⟨⟨_, perms1⟩, hmut, hrest⟩ := ep1_bind_ok h
    unfold listMutateAt at hmut
    obtain ⟨elem, hidx, hmut⟩ := ep1_bind_ok hmut
    obtain ⟨⟨_, p1⟩, htr_b, hmut⟩ := ep1_bind_ok hmut
    obtain ⟨p', htr, hp1⟩ := ep1_bind_ok htr_b
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hp1)
    obtain ⟨perms1', hset, hmut⟩ := ep1_bind_ok hmut
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hmut)
    obtain ⟨hhi, _⟩ := ep1_listIndex_eq_getElem hidx
    obtain ⟨_, rfl⟩ := ep1_listSet_eq hset
    obtain ⟨hlen', hother⟩ :=
      ep1_transitionRange_preserves_other rel acc (off + 1) rem (perms.set off p') perms' hrest
    refine ⟨by rw [hlen', List.length_set], fun i hilt hi => ?_⟩
    have hi1 : i < (perms.set off p').length := by simpa [List.length_set] using hi
    have hstep := hother i (by omega) hi1
    rw [hstep, List.getElem_set_ne (by omega)]

private theorem ep1_transitionRange_write_then_read_eq (rel : Gen.NodeRelation) :
    ∀ (off rem : Nat) (perms perms' : List Gen.Permission),
      Node.transitionRange rel .Write off rem perms = .ok perms' →
      Node.transitionRange rel .Read off rem perms' = .ok perms'
  | off, 0, perms, perms', h => by
    have hp := ep1_pure_ok h; subst hp; rfl
  | off, rem + 1, perms, perms', h => by
    unfold Node.transitionRange at h
    obtain ⟨⟨_, perms1⟩, hmut, hrest⟩ := ep1_bind_ok h
    unfold listMutateAt at hmut
    obtain ⟨elem, hidx, hmut⟩ := ep1_bind_ok hmut
    obtain ⟨⟨_, p1⟩, htr_b, hmut⟩ := ep1_bind_ok hmut
    obtain ⟨p', htr, hp1⟩ := ep1_bind_ok htr_b
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hp1)
    obtain ⟨perms1', hset, hmut⟩ := ep1_bind_ok hmut
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hmut)
    obtain ⟨hhi, helem⟩ := ep1_listIndex_eq_getElem hidx
    obtain ⟨_, rfl⟩ := ep1_listSet_eq hset
    obtain ⟨hlen', hother⟩ :=
      ep1_transitionRange_preserves_other rel .Write (off + 1) rem (perms.set off p') perms' hrest
    have hhi' : off < perms'.length := by rw [hlen', List.length_set]; exact hhi
    have hhiSet : off < (perms.set off p').length := by simpa [List.length_set] using hhi
    have hgetOff : perms'[off]'hhi' = p' := by
      have h1 := hother off (by omega) hhiSet
      simpa [List.getElem_set_self] using h1
    have hread : Permission.transition p' .Read rel = .ok p' :=
      ep1_tb_permission_write_then_read_idempotent perms[off] p' rel (helem ▸ htr)
    have hmutRead : listMutateAt perms' (Int.ofNat off) "Node::transition"
        (fun permission => do
          let p'' ← Permission.transition permission .Read rel
          pure ((), p'')) = .ok ((), perms') := by
      unfold listMutateAt
      rw [ep1_listIndex_of_getElem "Node::transition" hhi', hgetOff]
      simp only [bind, Except.bind, hread, pure, Except.pure]
      rw [ep1_listSet_of_lt p' "Node::transition" hhi']
      have hsetSelf : perms'.set off p' = perms' := by
        conv => lhs; arg 3; rw [← hgetOff]
        exact List.set_getElem_self hhi'
      simp only [hsetSelf]
    have hih := ep1_transitionRange_write_then_read_eq rel (off + 1) rem (perms.set off p') perms' hrest
    unfold Node.transitionRange
    rw [hmutRead]
    exact hih

mutual

private theorem ep1_node_access_write_then_read_eq :
    ∀ (n n' : Gen.Node) (path : Option Gen.Path) (off len : Nat),
      Node.access n path .Write ⟨off⟩ ⟨len⟩ = .ok n' →
      Node.access n' path .Read ⟨off⟩ ⟨len⟩ = .ok n'
  | ⟨children, perms, prot⟩, n', path, off, len, h => by
    unfold Node.access at h
    obtain ⟨n1, htr, h⟩ := ep1_bind_ok h
    obtain ⟨cs', hcs, hp⟩ := ep1_bind_ok h
    have hp' := ep1_pure_ok hp
    subst hp'
    unfold Node.transition at htr
    obtain ⟨perms', htrR, hnp⟩ := ep1_bind_ok htr
    have hnp' := ep1_pure_ok hnp
    subst hnp'
    have htrRead := ep1_transitionRange_write_then_read_eq _ off len perms perms' htrR
    have hcsRead := ep1_children_access_write_then_read_eq children cs' 0 path off len hcs
    unfold Node.access Node.transition
    simp only [htrRead, hcsRead, bind, Except.bind, pure, Except.pure]

private theorem ep1_children_access_write_then_read_eq :
    ∀ (cs cs' : List Gen.Node) (childId : Int) (path : Option Gen.Path) (off len : Nat),
      Node.accessChildren childId path .Write ⟨off⟩ ⟨len⟩ cs = .ok cs' →
      Node.accessChildren childId path .Read ⟨off⟩ ⟨len⟩ cs' = .ok cs'
  | [], cs', _, _, _, _, h => by
    have hp := ep1_pure_ok h; subst hp; rfl
  | c :: rest, cs', childId, path, off, len, h => by
    unfold Node.accessChildren at h
    obtain ⟨c', hc, h⟩ := ep1_bind_ok h
    obtain ⟨rest', hr, hp⟩ := ep1_bind_ok h
    have hp' := ep1_pure_ok hp
    subst hp'
    have hcRead := ep1_node_access_write_then_read_eq c c' _ off len hc
    have hrRead := ep1_children_access_write_then_read_eq rest rest' (childId + 1) path off len hr
    unfold Node.accessChildren
    simp only [hcRead, hrRead, bind, Except.bind, pure, Except.pure]

end

private theorem ep1_writeSubsliceAtIndex_subslice_recover {T : Type}
    {xs ys bs : List T} {off : Nat}
    (hws : writeSubsliceAtIndex xs (off : Int) bs = .ok ys) :
    ys.length = xs.length ∧
    subsliceWithLength ys (off : Int) (bs.length : Int) = .ok bs := by
  have hlen := writeSubsliceAtIndex_length hws
  refine ⟨hlen, ?_⟩
  unfold writeSubsliceAtIndex at hws
  split at hws
  · rename_i hcond
    have hy := ep1_pure_ok hws
    subst hy
    unfold subsliceWithLength
    have hlenTake : (List.take off xs).length = off := by
      simp only [List.length_take]; omega
    have hcond2 : (0 : Int) ≤ (off : Int) ∧ (0 : Int) ≤ (bs.length : Int) ∧
        (off : Int) + (bs.length : Int) ≤
          ((List.take (off : Int).toNat xs ++ bs ++
            List.drop ((off : Int).toNat + bs.length) xs).length : Int) := by
      simp only [List.length_append, Int.toNat_natCast, hlenTake, List.length_drop]
      omega
    simp only [hcond2, and_self, ↓reduceIte]
    simp only [Int.toNat_natCast]
    rw [List.append_assoc, List.drop_append, hlenTake]
    simp only [Nat.sub_self, List.drop_zero,
      List.drop_eq_nil_of_le (Nat.le_of_eq hlenTake), List.nil_append, List.take_left,
      pure, Except.pure]
  · simp [specPanic] at hws

private theorem ep1_leBytes_length : ∀ (u n : Nat), (leBytes u n).length = n
  | _, 0 => rfl
  | u, n + 1 => by simp [leBytes, ep1_leBytes_length]

private theorem ep1_encodeIntM_length {M : Type} [Gen.Memory M]
    {it : Gen.IntType} {val : Int} {bs : List (Gen.AbstractByte (Gen.Memory.Provenance M))}
    (h : Type.encodeIntM (M := M) it (.Int val) = .ok bs) :
    bs.length = it.size.bytes := by
  rcases it with ⟨signed, size⟩
  unfold Type.encodeIntM at h
  cases he : Endianness.encode x86_64.ENDIANNESS signed size val with
  | none => simp [he, specPanic] at h
  | some data =>
    simp only [he, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [List.length_map]
    unfold Endianness.encode at he
    split at he
    · cases he
      exact ep1_leBytes_length _ _
    · cases he

private theorem ep1_check_ptr_same_shape {E A : Type}
    (mem1 mem2 : Gen.BasicMemory Gen.x86_64 E A)
    (hshape : mem1.allocations.map (fun a => (a.data.length, a.addr, a.live)) =
              mem2.allocations.map (fun a => (a.data.length, a.addr, a.live)))
    (ptr : Gen.ThinPointer (Gen.Provenance E)) (len : Size) :
    BasicMemory.check_ptr mem2 ptr len = BasicMemory.check_ptr mem1 ptr len := by
  unfold BasicMemory.check_ptr
  by_cases hz : len.bytes = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte]
    cases ptr.provenance with
    | none => rfl
    | some ip =>
      rcases ip with ⟨id, pe⟩
      dsimp only
      unfold listIndex
      by_cases hnn : 0 ≤ id._0
      · simp only [hnn, ↓reduceIte]
        have hlen : mem1.allocations.length = mem2.allocations.length := by
          simpa using congrArg List.length hshape
        by_cases hi : id._0.toNat < mem1.allocations.length
        · have hi2 : id._0.toNat < mem2.allocations.length := hlen ▸ hi
          rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi2]
          have h1 := congrArg (fun xs => xs[id._0.toNat]?) hshape
          simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi2,
            Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
          obtain ⟨hd, ha, hl⟩ := h1
          simp only [pure, Except.pure, bind, Except.bind, Allocation.size, hd, ha, hl]
          rfl
        · have hi2 : ¬(id._0.toNat < mem2.allocations.length) := hlen ▸ hi
          rw [List.getElem?_eq_none (Nat.le_of_not_lt hi), List.getElem?_eq_none (Nat.le_of_not_lt hi2)]
      · simp only [hnn, ↓reduceIte]

private theorem ep1_BasicMemory_store_shape {E A : Type}
    {mem mem' : Gen.BasicMemory Gen.x86_64 E A}
    {ptr : Gen.ThinPointer (Gen.Provenance E)}
    {bytes : List (Gen.AbstractByte (Gen.Provenance E))} {align : Align}
    {handle : A → E → Gen.Offset → Interp A}
    (h : BasicMemory.store mem ptr bytes align handle = .ok mem') :
    mem'.allocations.map (fun a => (a.data.length, a.addr, a.live)) =
      mem.allocations.map (fun a => (a.data.length, a.addr, a.live)) := by
  unfold BasicMemory.store at h
  split at h
  · simp [ub] at h
  · obtain ⟨chk, _, h⟩ := ep1_bind_ok h
    cases chk with
    | none =>
      have hp := ep1_pure_ok h; subst hp; rfl
    | some trip =>
      rcases trip with ⟨id, pe, off⟩
      obtain ⟨alloc, hidx, h⟩ := ep1_bind_ok h
      obtain ⟨extra', _, h⟩ := ep1_bind_ok h
      obtain ⟨data', hws, h⟩ := ep1_bind_ok h
      obtain ⟨allocs', hset, hp⟩ := ep1_bind_ok h
      have hp' := ep1_pure_ok hp; subst hp'
      obtain ⟨_, hi, hget⟩ := ep1_listIndex_int_eq_getElem hidx
      have hallocs : allocs' = mem.allocations.set id._0.toNat { alloc with data := data', extra := extra' } := by
        unfold listSet at hset
        split at hset
        · exact (ep1_pure_ok hset).symm
        · simp [specPanic] at hset
      subst hallocs
      have hlenData : data'.length = alloc.data.length := writeSubsliceAtIndex_length hws
      show (mem.allocations.set id._0.toNat { alloc with data := data', extra := extra' }).map
          (fun a => (a.data.length, a.addr, a.live)) = _
      rw [List.map_set]
      have hsame : (data'.length, alloc.addr, alloc.live) =
          (mem.allocations.map (fun a => (a.data.length, a.addr, a.live)))[id._0.toNat]'(by simpa using hi) := by
        simp only [List.getElem_map, hget, hlenData]
      exact (congrArg (fun v => (mem.allocations.map _).set id._0.toNat v) hsame).trans
        (List.set_getElem_self (by simpa using hi))

/-- **Universal `SetDiscriminant → GetDiscriminant` roundtrip on `MachTB` (`TreeBorrowsMemory`):**
for any single-tag enum variant whose tagger writes `(tagOff, (tagTy, tagVal))`, whose
`Discriminator::Branch` reads `(tagOff, tagTy)` and maps `tagVal` to `.Known d`, and whose
integer codec roundtrips `tagVal`: whenever `Statement::SetDiscriminant` succeeds on `m`
yielding `m1` (through a place whose `evalPlaceM` is unchanged on `m1`, e.g. any deref-free
place), `ValueExpr::GetDiscriminant` on `m1` **unconditionally succeeds** (with ZERO extra
address/size bounds hypotheses, since `SetDiscriminant` already checked `ptr_offset_inbounds`),
returns `(.Int d, .Int dty)`, and leaves `m2.mem.memory = m1.mem.memory` (every borrow-tree
permission unchanged via `ep1_tb_permission_write_then_read_idempotent`). -/
theorem ep1_setDiscriminant_then_getDiscriminant_tb
    (m m0 m1 : MachTB) (place : Gen.PlaceExpr) (rp : Gen.Place TBM)
    (variants : Map Int Gen.Variant) (dty : Gen.IntType)
    (tagOff : Gen.Offset) (tagTy : Gen.IntType)
    (fallback : Gen.Discriminator) (children : List ((Int × Int) × Gen.Discriminator))
    (sz : Size) (al : Align) (d : Int) (var : Gen.Variant) (tagVal : Int)
    (tagBytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (hp0 : evalPlaceM m place = .ok ((rp, .Enum variants dty (.Branch tagOff tagTy fallback ⟨children⟩) sz al), m0))
    (hp1 : evalPlaceM m1 place = .ok ((rp, .Enum variants dty (.Branch tagOff tagTy fallback ⟨children⟩) sz al), m1))
    (hvar : mapGet variants d = some var)
    (htagger : var.tagger = ⟨[(tagOff, (tagTy, tagVal))]⟩)
    (henc : Type.encodeIntM (M := TBM) tagTy (.Int tagVal) = .ok tagBytes)
    (hdec : Type.decodeIntM (M := TBM) tagTy tagBytes = .ok (some (.Int tagVal)))
    (hnext : ep1NextDiscriminator children fallback tagVal = .Known d)
    (hset : evalStatementM m (.SetDiscriminant place d) = .ok m1) :
    ∃ m2, evalValueM m1 (.GetDiscriminant place) = .ok ((.Int d, .Int dty), m2) ∧
      m2.mem.memory = m1.mem.memory := by
  simp only [evalStatementM, evalSetDiscriminantM] at hset
  rw [hp0] at hset
  dsimp only [bind, Except.bind] at hset
  have hal : rp.aligned = true := by
    cases h : rp.aligned
    · simp [h, ub] at hset
    · rfl
  simp only [hal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hvar] at hset
  unfold encodeDiscriminantM at hset
  rw [htagger] at hset
  simp only [List.foldlM_cons, List.foldlM_nil, henc, bind, Except.bind] at hset
  obtain ⟨m1Tmp, hstep, hpOuter⟩ := ep1_bind_ok hset
  have hm1Outer := ep1_pure_ok hpOuter
  subst hm1Outer
  obtain ⟨ptr, hpoi0, hstep⟩ := ep1_bind_ok hstep
  obtain ⟨cm1, hstore, hpRet⟩ := ep1_bind_ok hstep
  have hm1Eq := ep1_pure_ok hpRet
  subst hm1Eq
  unfold ConcurrentMemory.store at hstore
  obtain ⟨tbm1, htbStore, hcmRet⟩ := ep1_bind_ok hstore
  have hcm1Eq := ep1_pure_ok hcmRet
  subst hcm1Eq
  change TreeBorrowsMemory.store m0.mem.memory ptr tagBytes ⟨1⟩ = .ok tbm1 at htbStore
  unfold TreeBorrowsMemory.store at htbStore
  obtain ⟨bm1, hbmStore, htbRet⟩ := ep1_bind_ok htbStore
  have htbm1Eq := ep1_pure_ok htbRet
  subst htbm1Eq
  have hshape := ep1_BasicMemory_store_shape hbmStore
  have htagLen : tagBytes.length = tagTy.size.bytes := ep1_encodeIntM_length henc
  have hszEq : tagTy.size = ⟨tagBytes.length⟩ := by
    rcases hs : tagTy.size with ⟨b⟩
    rw [hs] at htagLen
    exact congrArg Size.mk htagLen.symm
  let cm1' : Gen.ConcurrentMemory TBM :=
    { memory := { m0.mem.memory with mem := bm1 }
      accesses := m0.mem.accesses ++ [⟨.Store, .None, ptr.addr, ⟨tagBytes.length⟩⟩] }
  let m1' : MachTB := { m0 with mem := cm1' }
  have hpoi1 : ptrOffsetInboundsM m1' rp.ptr.thin_pointer (tagOff.bytes : Int) = .ok ptr := by
    unfold ptrOffsetInboundsM at hpoi0 ⊢
    obtain ⟨u, hsd0, hrest0⟩ := ep1_bind_ok hpoi0
    have hsd1 : ConcurrentMemory.signed_dereferenceable m1'.mem
        rp.ptr.thin_pointer (tagOff.bytes : Int) = .ok u := by
      change TreeBorrowsMemory.signed_dereferenceable m0.mem.memory rp.ptr.thin_pointer (tagOff.bytes : Int) = .ok u at hsd0
      change TreeBorrowsMemory.signed_dereferenceable { m0.mem.memory with mem := bm1 } rp.ptr.thin_pointer (tagOff.bytes : Int) = .ok u
      unfold TreeBorrowsMemory.signed_dereferenceable TreeBorrowsMemory.dereferenceable at hsd0 ⊢
      dsimp only
      by_cases hpos : (tagOff.bytes : Int) > 0
      · simp only [hpos, ↓reduceIte] at hsd0 ⊢
        rw [ep1_check_ptr_same_shape m0.mem.memory.mem bm1 hshape.symm]; exact hsd0
      · simp only [hpos, ↓reduceIte] at hsd0 ⊢
        rw [ep1_check_ptr_same_shape m0.mem.memory.mem bm1 hshape.symm]; exact hsd0
    simp only [hsd1, bind, Except.bind]
    exact hrest0
  have htbLoad : TreeBorrowsMemory.load { m0.mem.memory with mem := bm1 } ptr tagTy.size ⟨1⟩ =
      .ok (tagBytes, { m0.mem.memory with mem := bm1 }) := by
    unfold BasicMemory.store at hbmStore
    simp only [ep1_align_one_is_aligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hbmStore
    obtain ⟨chk, hchk0, hbmStore⟩ := ep1_bind_ok hbmStore
    have hchk1 : BasicMemory.check_ptr bm1 ptr tagTy.size = .ok chk := by
      rw [ep1_check_ptr_same_shape m0.mem.memory.mem bm1 hshape.symm, hszEq]
      exact hchk0
    unfold TreeBorrowsMemory.load BasicMemory.load
    dsimp only
    simp only [ep1_align_one_is_aligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      hchk1, bind, Except.bind]
    cases chk with
    | none =>
      have hbmEq := ep1_pure_ok hbmStore; subst hbmEq
      have hlen0 : tagBytes.length = 0 := by
        unfold BasicMemory.check_ptr at hchk0
        split at hchk0
        · assumption
        · cases hpr : ptr.provenance with
          | none => simp [hpr, ub] at hchk0
          | some ip =>
            simp only [hpr] at hchk0
            obtain ⟨_, _, hchk0⟩ := ep1_bind_ok hchk0
            split at hchk0
            · simp [ub] at hchk0
            · split at hchk0
              · simp [ub] at hchk0
              · cases ep1_pure_ok hchk0
      have hnil : tagBytes = [] := List.eq_nil_of_length_eq_zero hlen0
      subst hnil; rfl
    | some trip =>
      rcases trip with ⟨id, path, off⟩
      obtain ⟨alloc, hidx0, hbmStore⟩ := ep1_bind_ok hbmStore
      obtain ⟨extra', hextra, hbmStore⟩ := ep1_bind_ok hbmStore
      obtain ⟨root', hnodeW, hretE⟩ := ep1_bind_ok hextra
      have hretE' := ep1_pure_ok hretE; subst hretE'
      obtain ⟨data', hws, hbmStore⟩ := ep1_bind_ok hbmStore
      obtain ⟨allocs', hset', hbmRet⟩ := ep1_bind_ok hbmStore
      have hbmRet' := ep1_pure_ok hbmRet; subst hbmRet'
      obtain ⟨hidNN, hidLt, _⟩ := ep1_listIndex_int_eq_getElem hidx0
      have hallocsEq : allocs' = m0.mem.memory.mem.allocations.set id._0.toNat
          { alloc with data := data', extra := { root := root' } } := by
        unfold listSet at hset'
        split at hset'
        · exact (ep1_pure_ok hset').symm
        · simp [specPanic] at hset'
      subst hallocsEq
      have hidLt1 : id._0.toNat <
          (m0.mem.memory.mem.allocations.set id._0.toNat
            { alloc with data := data', extra := { root := root' } }).length := by
        simpa [List.length_set] using hidLt
      have hnodeR : Node.access root' (some path) .Read off tagTy.size = .ok root' := by
        rw [hszEq]
        exact ep1_node_access_write_then_read_eq alloc.extra.root root' (some path) off.bytes tagBytes.length hnodeW
      have hsub1 : subsliceWithLength data' (off.bytes : Int) (tagTy.size.bytes : Int) = .ok tagBytes := by
        rw [← htagLen]
        exact (ep1_writeSubsliceAtIndex_subslice_recover hws).2
      have hsetIdem : ∀ {α : Type} (xs : List α) (i : Nat) (x : α),
          i < xs.length → (xs.set i x).set i x = xs.set i x := fun xs i x hi => by
        have hlt : i < (xs.set i x).length := by simpa [List.length_set] using hi
        have hget : x = (xs.set i x)[i]'hlt := by simp [List.getElem_set_self]
        conv => lhs; arg 3; rw [hget]
        exact List.set_getElem_self hlt
      dsimp only
      rw [ep1_listIndex_int_of_getElem _ hidNN hidLt1, List.getElem_set_self]
      dsimp only [bind, Except.bind]
      rw [hnodeR]
      dsimp only [bind, Except.bind, pure, Except.pure]
      rw [ep1_listSet_int_of_lt _ _ hidNN hidLt1, hsetIdem _ _ _ hidLt]
      dsimp only [bind, Except.bind]
      rw [hsub1]
  let cm2' : Gen.ConcurrentMemory TBM :=
    { memory := m1'.mem.memory
      accesses := m1'.mem.accesses ++ [⟨.Load, .None, ptr.addr, tagTy.size⟩] }
  refine ⟨{ m1' with mem := cm2' }, ?_, rfl⟩
  rw [(ep1_evalValueM_getDiscriminant_complete_spec (M := TBM)).1 m1' m1' place rp variants dty
      (.Branch tagOff tagTy fallback ⟨children⟩) sz al hp1 hal]
  rw [(ep1_evalValueM_getDiscriminant_complete_spec (M := TBM)).2.2.2 rp dty tagOff tagTy fallback children m1']
  have hcmLoad : ConcurrentMemory.load m1'.mem ptr tagTy.size ⟨1⟩ .None = .ok (tagBytes, cm2') :=
    ep1_concurrent_load_of_mem_load m1'.mem ptr tagTy.size ⟨1⟩ .None tagBytes m1'.mem.memory htbLoad
  simp only [hpoi1, hcmLoad, hdec, hnext, bind, Except.bind]
  exact (ep1_evalValueM_getDiscriminant_complete_spec (M := TBM)).2.1 rp dty d _

/-- **Universal `SetDiscriminant → GetDiscriminant` roundtrip on `Mach` (`BasicMemory`):**
counterpart to `ep1_setDiscriminant_then_getDiscriminant_tb` on `BasicMemory`, with ZERO extra
address/size bounds hypotheses and exact memory preservation (`m2.mem.memory = m1.mem.memory`). -/
theorem ep1_setDiscriminant_then_getDiscriminant_bm
    (m m0 m1 : Mach) (place : Gen.PlaceExpr) (rp : Gen.Place BM)
    (variants : Map Int Gen.Variant) (dty : Gen.IntType)
    (tagOff : Gen.Offset) (tagTy : Gen.IntType)
    (fallback : Gen.Discriminator) (children : List ((Int × Int) × Gen.Discriminator))
    (sz : Size) (al : Align) (d : Int) (var : Gen.Variant) (tagVal : Int)
    (tagBytes : List Byte)
    (hp0 : evalPlace m place = .ok ((rp, .Enum variants dty (.Branch tagOff tagTy fallback ⟨children⟩) sz al), m0))
    (hp1 : evalPlace m1 place = .ok ((rp, .Enum variants dty (.Branch tagOff tagTy fallback ⟨children⟩) sz al), m1))
    (hvar : mapGet variants d = some var)
    (htagger : var.tagger = ⟨[(tagOff, (tagTy, tagVal))]⟩)
    (henc : Type.encodeIntM (M := BM) tagTy (.Int tagVal) = .ok tagBytes)
    (hdec : Type.decodeIntM (M := BM) tagTy tagBytes = .ok (some (.Int tagVal)))
    (hnext : ep1NextDiscriminator children fallback tagVal = .Known d)
    (hset : evalStatement m (.SetDiscriminant place d) = .ok m1) :
    ∃ m2, evalValue m1 (.GetDiscriminant place) = .ok ((.Int d, .Int dty), m2) ∧
      m2.mem.memory = m1.mem.memory := by
  rw [← evalPlaceM_bm_eq] at hp0 hp1
  rw [← evalStatementM_bm_eq] at hset
  suffices h : ∃ m2, evalValueM (M := BM) m1 (.GetDiscriminant place) = .ok ((.Int d, .Int dty), m2) ∧
      m2.mem.memory = m1.mem.memory by
    obtain ⟨m2, h1, h2⟩ := h
    rw [evalValueM_bm_eq] at h1
    exact ⟨m2, h1, h2⟩
  simp only [evalStatementM, evalSetDiscriminantM] at hset
  rw [hp0] at hset
  dsimp only [bind, Except.bind] at hset
  have hal : rp.aligned = true := by
    cases h : rp.aligned
    · simp [h, ub] at hset
    · rfl
  simp only [hal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hvar] at hset
  unfold encodeDiscriminantM at hset
  rw [htagger] at hset
  simp only [List.foldlM_cons, List.foldlM_nil, henc, bind, Except.bind] at hset
  obtain ⟨m1Tmp, hstep, hpOuter⟩ := ep1_bind_ok hset
  have hm1Outer := ep1_pure_ok hpOuter
  subst hm1Outer
  obtain ⟨ptr, hpoi0, hstep⟩ := ep1_bind_ok hstep
  obtain ⟨cm1, hstore, hpRet⟩ := ep1_bind_ok hstep
  have hm1Eq := ep1_pure_ok hpRet
  subst hm1Eq
  unfold ConcurrentMemory.store at hstore
  obtain ⟨bm1, hbmStore, hcmRet⟩ := ep1_bind_ok hstore
  have hcm1Eq := ep1_pure_ok hcmRet
  subst hcm1Eq
  change BM.store m0.mem.memory ptr tagBytes ⟨1⟩ = .ok bm1 at hbmStore
  have hcheckEq : ∀ (bm : BM) (p : Ptr) (len : Size),
      BM.check_ptr bm p len = BasicMemory.check_ptr bm p len := by
    intro bm p len
    unfold BM.check_ptr BasicMemory.check_ptr
    by_cases hz : len.bytes = 0
    · simp [hz]
    · simp only [hz, ↓reduceIte]
      cases p.provenance <;> rfl
  have hshape : bm1.allocations.map (fun a => (a.data.length, a.addr, a.live)) =
      m0.mem.memory.allocations.map (fun a => (a.data.length, a.addr, a.live)) := by
    unfold BM.store at hbmStore
    split at hbmStore
    · simp [ub] at hbmStore
    · obtain ⟨chk, _, hbmStore⟩ := ep1_bind_ok hbmStore
      cases chk with
      | none =>
        have hp := ep1_pure_ok hbmStore; subst hp; rfl
      | some trip =>
        rcases trip with ⟨id, pu, off⟩
        obtain ⟨alloc, hidx, hbmStore⟩ := ep1_bind_ok hbmStore
        obtain ⟨data', hws, hbmStore⟩ := ep1_bind_ok hbmStore
        obtain ⟨allocs', hset', hp⟩ := ep1_bind_ok hbmStore
        have hp' := ep1_pure_ok hp; subst hp'
        obtain ⟨_, hi, hget⟩ := ep1_listIndex_int_eq_getElem hidx
        have hallocs : allocs' = m0.mem.memory.allocations.set id._0.toNat { alloc with data := data' } := by
          unfold listSet at hset'
          split at hset'
          · exact (ep1_pure_ok hset').symm
          · simp [specPanic] at hset'
        subst hallocs
        have hlenData : data'.length = alloc.data.length := writeSubsliceAtIndex_length hws
        show (m0.mem.memory.allocations.set id._0.toNat { alloc with data := data' }).map
            (fun a => (a.data.length, a.addr, a.live)) = _
        rw [List.map_set]
        have hsame : (data'.length, alloc.addr, alloc.live) =
            (m0.mem.memory.allocations.map (fun a => (a.data.length, a.addr, a.live)))[id._0.toNat]'(by simpa using hi) := by
          simp only [List.getElem_map, hget, hlenData]
        exact (congrArg (fun v => (m0.mem.memory.allocations.map _).set id._0.toNat v) hsame).trans
          (List.set_getElem_self (by simpa using hi))
  have htagLen : tagBytes.length = tagTy.size.bytes := ep1_encodeIntM_length henc
  have hszEq : tagTy.size = ⟨tagBytes.length⟩ := by
    rcases hs : tagTy.size with ⟨b⟩
    rw [hs] at htagLen
    exact congrArg Size.mk htagLen.symm
  let cm1' : Gen.ConcurrentMemory BM :=
    { memory := bm1
      accesses := m0.mem.accesses ++ [⟨.Store, .None, ptr.addr, ⟨tagBytes.length⟩⟩] }
  let m1' : Mach := { m0 with mem := cm1' }
  have hpoi1 : ptrOffsetInboundsM (M := BM) m1'
      rp.ptr.thin_pointer (tagOff.bytes : Int) = .ok ptr := by
    unfold ptrOffsetInboundsM at hpoi0 ⊢
    obtain ⟨u, hsd0, hrest0⟩ := ep1_bind_ok hpoi0
    have hsd1 : ConcurrentMemory.signed_dereferenceable (M := BM) m1'.mem
        rp.ptr.thin_pointer (tagOff.bytes : Int) = .ok u := by
      change BM.signed_dereferenceable m0.mem.memory rp.ptr.thin_pointer (tagOff.bytes : Int) = .ok u at hsd0
      change BM.signed_dereferenceable bm1 rp.ptr.thin_pointer (tagOff.bytes : Int) = .ok u
      unfold BM.signed_dereferenceable BM.dereferenceable at hsd0 ⊢
      by_cases hpos : (tagOff.bytes : Int) > 0
      · simp only [hpos, ↓reduceIte, hcheckEq] at hsd0 ⊢
        rw [ep1_check_ptr_same_shape m0.mem.memory bm1 hshape.symm]; exact hsd0
      · simp only [hpos, ↓reduceIte, hcheckEq] at hsd0 ⊢
        rw [ep1_check_ptr_same_shape m0.mem.memory bm1 hshape.symm]; exact hsd0
    simp only [hsd1, bind, Except.bind]
    exact hrest0
  have hbmLoad : BM.load bm1 ptr tagTy.size ⟨1⟩ = .ok (tagBytes, bm1) := by
    unfold BM.store at hbmStore
    simp only [ep1_align_one_is_aligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hbmStore
    obtain ⟨chk, hchk0, hbmStore⟩ := ep1_bind_ok hbmStore
    have hchk1 : BM.check_ptr bm1 ptr tagTy.size = .ok chk := by
      rw [hcheckEq, ep1_check_ptr_same_shape m0.mem.memory bm1 hshape.symm, hszEq, ← hcheckEq]
      exact hchk0
    unfold BM.load
    simp only [ep1_align_one_is_aligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      hchk1, bind, Except.bind]
    cases chk with
    | none =>
      have hbmEq := ep1_pure_ok hbmStore; subst hbmEq
      have hlen0 : tagBytes.length = 0 := by
        unfold BM.check_ptr at hchk0
        split at hchk0
        · assumption
        · cases hpr : ptr.provenance with
          | none => simp [hpr, ub] at hchk0
          | some ip =>
            simp only [hpr] at hchk0
            obtain ⟨_, _, hchk0⟩ := ep1_bind_ok hchk0
            split at hchk0
            · simp [ub] at hchk0
            · split at hchk0
              · simp [ub] at hchk0
              · cases ep1_pure_ok hchk0
      have hnil : tagBytes = [] := List.eq_nil_of_length_eq_zero hlen0
      subst hnil; rfl
    | some trip =>
      rcases trip with ⟨id, pu, off⟩
      cases pu
      obtain ⟨alloc, hidx0, hbmStore⟩ := ep1_bind_ok hbmStore
      obtain ⟨data', hws, hbmStore⟩ := ep1_bind_ok hbmStore
      obtain ⟨allocs', hset', hbmRet⟩ := ep1_bind_ok hbmStore
      have hbmRet' := ep1_pure_ok hbmRet; subst hbmRet'
      obtain ⟨hidNN, hidLt, _⟩ := ep1_listIndex_int_eq_getElem hidx0
      have hallocsEq : allocs' = m0.mem.memory.allocations.set id._0.toNat { alloc with data := data' } := by
        unfold listSet at hset'
        split at hset'
        · exact (ep1_pure_ok hset').symm
        · simp [specPanic] at hset'
      subst hallocsEq
      have hidLt1 : id._0.toNat < (m0.mem.memory.allocations.set id._0.toNat { alloc with data := data' }).length := by
        simpa [List.length_set] using hidLt
      have hsub1 : subsliceWithLength data' (off.bytes : Int) (tagTy.size.bytes : Int) = .ok tagBytes := by
        rw [← htagLen]
        exact (ep1_writeSubsliceAtIndex_subslice_recover hws).2
      have hsetIdem : ∀ {α : Type} (xs : List α) (i : Nat) (x : α),
          i < xs.length → (xs.set i x).set i x = xs.set i x := fun xs i x hi => by
        have hlt : i < (xs.set i x).length := by simpa [List.length_set] using hi
        have hget : x = (xs.set i x)[i]'hlt := by simp [List.getElem_set_self]
        conv => lhs; arg 3; rw [hget]
        exact List.set_getElem_self hlt
      dsimp only
      rw [ep1_listIndex_int_of_getElem _ hidNN hidLt1, List.getElem_set_self]
      dsimp only [bind, Except.bind]
      rw [ep1_listSet_int_of_lt _ _ hidNN hidLt1, hsetIdem _ _ _ hidLt]
      dsimp only [bind, Except.bind]
      rw [hsub1]
      rfl
  let cm2' : Gen.ConcurrentMemory BM :=
    { memory := m1'.mem.memory
      accesses := m1'.mem.accesses ++ [⟨.Load, .None, ptr.addr, tagTy.size⟩] }
  refine ⟨{ m1' with mem := cm2' }, ?_, rfl⟩
  rw [(ep1_evalValueM_getDiscriminant_complete_spec (M := BM)).1 m1' m1' place rp variants dty
      (.Branch tagOff tagTy fallback ⟨children⟩) sz al hp1 hal]
  rw [(ep1_evalValueM_getDiscriminant_complete_spec (M := BM)).2.2.2 rp dty tagOff tagTy fallback children m1']
  have hcmLoad : ConcurrentMemory.load (M := BM) m1'.mem ptr tagTy.size ⟨1⟩ .None = .ok (tagBytes, cm2') :=
    ep1_concurrent_load_of_mem_load (M := BM) m1'.mem ptr tagTy.size ⟨1⟩ .None tagBytes m1'.mem.memory hbmLoad
  simp only [hpoi1, hcmLoad, hdec, hnext, bind, Except.bind]
  exact (ep1_evalValueM_getDiscriminant_complete_spec (M := BM)).2.1 rp dty d _

/-! #### Structural `PlaceExpr` chains (`Local` / `Field` / `Downcast`): exact `liftMachToTB` biconditional and compositional TB⇒BM transfer -/

/-- Structural place projection chain built from `Local`, `Field`, and `Downcast` (no `Deref`
or dynamic `Index`). -/
inductive Ep1PlaceChain : Gen.PlaceExpr → Prop where
  | Local (name : Gen.LocalName) : Ep1PlaceChain (.Local name)
  | Field (root : Gen.PlaceExpr) (field : Int) : Ep1PlaceChain root → Ep1PlaceChain (.Field root field)
  | Downcast (root : Gen.PlaceExpr) (discriminant : Int) : Ep1PlaceChain root → Ep1PlaceChain (.Downcast root discriminant)

private theorem ep1_check_ptr_lift_exact (m : Mach) (p : Ptr) (len : Size) :
    BasicMemory.check_ptr (liftMachToTB m).mem.memory.mem (liftThinPtrTB p) len =
      (match BM.check_ptr m.mem.memory p len with
       | .ok none => .ok none
       | .ok (some (id, _, off)) => .ok (some (id, [], off))
       | .error e => .error e) := by
  unfold BasicMemory.check_ptr BM.check_ptr
  by_cases hz : len.bytes = 0
  · simp [hz, pure, Except.pure]
  · simp only [hz, ↓reduceIte]
    cases hp : p.provenance with
    | none => simp [liftThinPtrTB, hp, ub]
    | some ip =>
      rcases ip with ⟨id, pu⟩
      cases pu
      simp only [liftThinPtrTB, hp, Option.map_some, liftProvTB]
      show (do let allocation ← listIndex (m.mem.memory.allocations.map liftAllocTB) id._0 "self.allocations[id.0]"; _) = _
      rw [ep1_listIndex_map]
      cases hidx : listIndex m.mem.memory.allocations id._0 "self.allocations[id.0]" with
      | error e => rfl
      | ok a =>
        have hlen : (Allocation.size (liftAllocTB a)).bytes = (Allocation.size a).bytes := by
          simp [Allocation.size, liftAllocTB]
        have hliveA : (liftAllocTB a).live = a.live := rfl
        have haddrA : (liftAllocTB a).addr = a.addr := rfl
        simp only [bind, Except.bind, hliveA, haddrA, hlen]
        by_cases hlive : !a.live
        · simp [hlive, ub]
        · simp only [hlive]
          by_cases hbounds : p.addr - a.addr < 0 ∨ p.addr - a.addr + (len.bytes : Int) > (Allocation.size a).bytes
          · simp [hbounds, ub]
          · simp [hbounds, pure, Except.pure]

private theorem ep1_ptrOffsetInboundsM_bm_eq (m : Mach) (p : Ptr) (off : Int) :
    ptrOffsetInboundsM (M := BM) m p off = ptrOffsetInbounds m p off := by
  unfold ptrOffsetInboundsM ptrOffsetInbounds
  rfl

private theorem ep1_ptrOffsetInbounds_lift_exact (m : Mach) (p : Ptr) (off : Int) :
    ptrOffsetInboundsM (liftMachToTB m) (liftThinPtrTB p) off =
      (liftThinPtrTB <$> ptrOffsetInbounds m p off) := by
  rw [← ep1_ptrOffsetInboundsM_bm_eq]
  unfold ptrOffsetInboundsM
  have hsd : ConcurrentMemory.signed_dereferenceable (liftMachToTB m).mem (liftThinPtrTB p) off =
      ConcurrentMemory.signed_dereferenceable (M := BM) m.mem p off := by
    change TreeBorrowsMemory.signed_dereferenceable (liftMachToTB m).mem.memory (liftThinPtrTB p) off =
      BM.signed_dereferenceable m.mem.memory p off
    unfold TreeBorrowsMemory.signed_dereferenceable TreeBorrowsMemory.dereferenceable
      BM.signed_dereferenceable BM.dereferenceable
    by_cases hpos : off > 0
    · simp only [hpos, ↓reduceIte, ep1_check_ptr_lift_exact]
      cases BM.check_ptr m.mem.memory p ⟨off.toNat⟩ with
      | error e => rfl
      | ok o => cases o <;> rfl
    · simp only [hpos, ↓reduceIte]
      have hptr : ({ liftThinPtrTB p with addr := (liftThinPtrTB p).addr + off } :
          Gen.ThinPointer Gen.TreeBorrowsProvenance) = liftThinPtrTB { p with addr := p.addr + off } := by
        simp [liftThinPtrTB]
      rw [hptr, ep1_check_ptr_lift_exact]
      cases BM.check_ptr m.mem.memory { p with addr := p.addr + off } ⟨(-off).toNat⟩ with
      | error e => rfl
      | ok o => cases o <;> rfl
  rw [hsd]
  cases ConcurrentMemory.signed_dereferenceable (M := BM) m.mem p off with
  | error e => rfl
  | ok u =>
    dsimp only [liftThinPtrTB, bind, Except.bind, Functor.map, Except.map]
    by_cases h1 : (!inBounds off .Signed x86_64.PTR_SIZE) = true
    · simp [h1, specPanic]
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : (!inBounds (p.addr + off) .Unsigned x86_64.PTR_SIZE) = true
      · simp [h2, specPanic]
      · simp [h2, pure, Except.pure]

private theorem ep1_transitionRange_replicate_unique_read :
    ∀ (off rem n : Nat), off + rem ≤ n →
      Node.transitionRange .Local .Read off rem (List.replicate n (Gen.Permission.Unprot .Unique)) =
        .ok (List.replicate n (Gen.Permission.Unprot .Unique))
  | _, 0, _, _ => rfl
  | off, rem + 1, n, hle => by
    have hoff : off < (List.replicate n (Gen.Permission.Unprot .Unique)).length := by
      rw [List.length_replicate]; omega
    have hget : (List.replicate n (Gen.Permission.Unprot .Unique))[off]'hoff = Gen.Permission.Unprot .Unique :=
      List.getElem_replicate hoff
    have hmut : listMutateAt (List.replicate n (Gen.Permission.Unprot .Unique)) (Int.ofNat off) "Node::transition"
        (fun permission => do
          let p' ← Permission.transition permission .Read .Local
          pure ((), p')) = .ok ((), List.replicate n (Gen.Permission.Unprot .Unique)) := by
      unfold listMutateAt
      rw [ep1_listIndex_of_getElem "Node::transition" hoff, hget]
      have htr : Permission.transition (Gen.Permission.Unprot .Unique) .Read .Local = .ok (Gen.Permission.Unprot .Unique) := rfl
      simp only [bind, Except.bind, htr, pure, Except.pure,
        ep1_listSet_of_lt (Gen.Permission.Unprot .Unique) "Node::transition" hoff]
      have hset : (List.replicate n (Gen.Permission.Unprot .Unique)).set off (Gen.Permission.Unprot .Unique) =
          List.replicate n (Gen.Permission.Unprot .Unique) := by
        conv => lhs; arg 3; rw [← hget]
        exact List.set_getElem_self hoff
      rw [hset]
    unfold Node.transitionRange
    rw [hmut]
    exact ep1_transitionRange_replicate_unique_read (off + 1) rem n (by omega)

private theorem ep1_load_lift_exact (m : Mach) (p : Ptr) (len : Size) (al : Align) :
    TreeBorrowsMemory.load (liftMachToTB m).mem.memory (liftThinPtrTB p) len al =
      (match BM.load m.mem.memory p len al with
       | .ok (bs, _) => .ok (bs.map liftByteTB, (liftMachToTB m).mem.memory)
       | .error e => .error e) := by
  unfold TreeBorrowsMemory.load BasicMemory.load BM.load
  have haddr : (liftThinPtrTB p).addr = p.addr := rfl
  rw [haddr]
  by_cases hal : !Align.is_aligned al p.addr
  · simp [hal, ub]
  · simp only [hal, Bool.false_eq_true, ↓reduceIte, ep1_check_ptr_lift_exact]
    cases hchk : BM.check_ptr m.mem.memory p len with
    | error e => rfl
    | ok chk =>
      cases chk with
      | none => rfl
      | some trip =>
        rcases trip with ⟨id, pu, off⟩
        cases pu
        have hallocTB : (liftMachToTB m).mem.memory.mem.allocations =
            m.mem.memory.allocations.map liftAllocTB := rfl
        simp only [bind, Except.bind, hallocTB, ep1_listIndex_map]
        cases hidx : listIndex m.mem.memory.allocations id._0 "self.allocations[id.0]" with
        | error e => rfl
        | ok a =>
          obtain ⟨hidNN, hidLt, hgetA⟩ := ep1_listIndex_int_eq_getElem hidx
          have hoffLe : off.bytes + len.bytes ≤ a.data.length := by
            unfold BM.check_ptr at hchk
            split at hchk
            · simp [pure, Except.pure] at hchk
            · cases hpr : p.provenance with
              | none => simp [hpr, ub] at hchk
              | some ip =>
                rcases ip with ⟨id', pu'⟩
                cases pu'
                simp only [hpr] at hchk
                obtain ⟨a', hidx', hchk⟩ := ep1_bind_ok hchk
                split at hchk
                · simp [ub] at hchk
                · split at hchk
                  · simp [ub] at hchk
                  · rename_i hnotOob
                    have hp' := ep1_pure_ok hchk
                    simp only [Option.some.injEq, Prod.mk.injEq] at hp'
                    rcases hp' with ⟨rfl, _, hoffEq⟩
                    rw [hidx] at hidx'; cases hidx'
                    have hnotlt : ¬((p.addr : Int) - (a.addr : Int) < (0 : Int)) :=
                      fun h => hnotOob (Or.inl h)
                    have hnotgt : ¬((p.addr : Int) - (a.addr : Int) + (len.bytes : Int) > (a.data.length : Int)) :=
                      fun h => hnotOob (Or.inr h)
                    have hoffB : off.bytes = (p.addr - a.addr).toNat := by cases hoffEq; rfl
                    have hnn : (0 : Int) ≤ (p.addr : Int) - (a.addr : Int) := Int.not_lt.mp hnotlt
                    have hle : (p.addr : Int) - (a.addr : Int) + (len.bytes : Int) ≤ (a.data.length : Int) :=
                      Int.not_lt.mp hnotgt
                    have hcast : (off.bytes : Int) = (p.addr : Int) - (a.addr : Int) := by
                      rw [hoffB]; exact Int.toNat_of_nonneg hnn
                    rw [← hcast] at hle
                    exact Int.ofNat_le.mp (by simpa [Int.natCast_add] using hle)
          have hnode : Node.access (liftAllocTB a).extra.root (some []) .Read off len =
              .ok (liftAllocTB a).extra.root := by
            unfold Node.access Node.transition
            simp only [liftAllocTB, Option.isSome_some, ↓reduceIte,
              ep1_transitionRange_replicate_unique_read off.bytes len.bytes a.data.length hoffLe,
              Node.accessChildren, bind, Except.bind, pure, Except.pure]
          have hsetBM : listSet m.mem.memory.allocations id._0 a "set" = .ok m.mem.memory.allocations := by
            rw [ep1_listSet_int_of_lt _ _ hidNN hidLt, ← hgetA, List.set_getElem_self]
          have hidLtTB : id._0.toNat < (m.mem.memory.allocations.map liftAllocTB).length := by
            simpa [List.length_map] using hidLt
          have hsetTB : listSet (m.mem.memory.allocations.map liftAllocTB) id._0 (liftAllocTB a) "set" =
              .ok (m.mem.memory.allocations.map liftAllocTB) := by
            rw [ep1_listSet_int_of_lt _ _ hidNN hidLtTB]
            have hgetTB : (m.mem.memory.allocations.map liftAllocTB)[id._0.toNat]'hidLtTB = liftAllocTB a := by
              simp [List.getElem_map, hgetA]
            congr 1
            conv => lhs; arg 3; rw [← hgetTB]
            exact List.set_getElem_self hidLtTB
          have hsubBM : subsliceWithLength a.data (off.bytes : Int) (len.bytes : Int) =
              .ok ((a.data.drop off.bytes).take len.bytes) :=
            ep1_subsliceWithLength_of_le a.data hoffLe
          have hsubTB : subsliceWithLength (liftAllocTB a).data (off.bytes : Int) (len.bytes : Int) =
              .ok (((a.data.drop off.bytes).take len.bytes).map liftByteTB) := by
            simp only [liftAllocTB]
            rw [ep1_subsliceWithLength_of_le (a.data.map liftByteTB) (by simpa [List.length_map] using hoffLe),
              List.map_take, List.map_drop]
          simp only [hnode, hsetBM, hsetTB, hsubBM, hsubTB, pure, Except.pure]
          rfl

private theorem ep1_compute_size_and_align_none_indep {P1 P2 : Type}
    (vt1 : Gen.ThinPointer P1 → Interp Gen.VTable)
    (vt2 : Gen.ThinPointer P2 → Interp Gen.VTable) :
    ∀ (lay : Gen.LayoutStrategy),
      LayoutStrategy.compute_size_and_align vt1 lay none =
        LayoutStrategy.compute_size_and_align vt2 lay none
  | .Sized _ _ => rfl
  | .Slice _ _ => rfl
  | .TraitObject _ => rfl
  | .Tuple _ _ => rfl

private theorem ep1_evalPlace_chain_thin_and_readonly (place : Gen.PlaceExpr)
    (hc : Ep1PlaceChain place) :
    ∀ (m m1 : Mach) (rp : Gen.Place BM) (ty : Gen.Type),
      evalPlace m place = .ok ((rp, ty), m1) → m1 = m ∧ rp.ptr.metadata = none := by
  induction hc with
  | Local name =>
    intro m m1 rp ty h
    unfold evalPlace at h
    obtain ⟨fr, _, h⟩ := ep1_bind_ok h
    obtain ⟨ty', _, h⟩ := ep1_bind_ok h
    cases hloc : mapGet fr.locals name with
    | none => simp [hloc, ub] at h
    | some p =>
      simp only [hloc] at h
      obtain ⟨h1, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
      obtain ⟨rfl, _⟩ := Prod.mk.inj h1
      exact ⟨rfl, rfl⟩
  | Field root field hroot ih =>
    intro m m1 rp ty h
    unfold evalPlace at h
    obtain ⟨⟨⟨rp0, ty0⟩, m0⟩, hr0, h⟩ := ep1_bind_ok h
    obtain ⟨rfl, hmeta0⟩ := ih m m0 rp0 ty0 hr0
    have hfin : ∀ (off : Gen.Offset) (fty : Gen.Type),
        (do
          let rootSize ← computeSize m0 (← Type.layout ty0) rp0.ptr.metadata
          if !(off.bytes ≤ rootSize.bytes) then
            specPanic "assertion failed: offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata)"
          else do
            let ptr ← ptrOffsetInbounds m0 rp0.ptr.thin_pointer (off.bytes : Int)
            let ptr := if !LayoutStrategy.is_sized (← Type.layout fty) then
                ThinPointer.widen ptr rp0.ptr.metadata
              else
                ThinPointer.widen ptr none
            pure (({ rp0 with ptr := ptr }, fty), m0)) = .ok ((rp, ty), m1) →
        m1 = m0 ∧ rp.ptr.metadata = none := by
      intro off fty ht
      obtain ⟨lay0, _, ht⟩ := ep1_bind_ok ht
      obtain ⟨rsz, _, ht⟩ := ep1_bind_ok ht
      split at ht
      · simp [specPanic] at ht
      · obtain ⟨ptr', _, ht⟩ := ep1_bind_ok ht
        obtain ⟨flay, _, ht⟩ := ep1_bind_ok ht
        obtain ⟨h1, rfl⟩ := Prod.mk.inj (ep1_pure_ok ht)
        obtain ⟨rfl, _⟩ := Prod.mk.inj h1
        refine ⟨rfl, ?_⟩
        split <;> simp [ThinPointer.widen, hmeta0]
    dsimp only [bind, Except.bind] at h
    cases ty0 with
    | Tuple sf sh uf =>
      dsimp only at h
      split at h
      · obtain ⟨⟨off, fty⟩, _, ht⟩ := ep1_bind_ok h
        exact hfin off fty ht
      · split at h
        · cases uf with
          | none => simp [specPanic] at h
          | some tailTy =>
            obtain ⟨tlay, _, h⟩ := ep1_bind_ok h
            obtain ⟨tal, _, ht⟩ := ep1_bind_ok h
            exact hfin (TupleHeadLayout.tail_offset sh tal) tailTy ht
        · simp [specPanic] at h
    | Union fields _ _ _ =>
      obtain ⟨⟨off, fty⟩, _, ht⟩ := ep1_bind_ok h
      exact hfin off fty ht
    | _ => simp [specPanic] at h
  | Downcast root d hroot ih =>
    intro m m1 rp ty h
    unfold evalPlace at h
    obtain ⟨⟨⟨rp0, ty0⟩, m0⟩, hr0, h⟩ := ep1_bind_ok h
    obtain ⟨rfl, hmeta0⟩ := ih m m0 rp0 ty0 hr0
    dsimp only [bind, Except.bind] at h
    cases ty0 with
    | Enum variants _ _ _ _ =>
      obtain ⟨var, _, h⟩ := ep1_bind_ok h
      obtain ⟨h1, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
      obtain ⟨rfl, _⟩ := Prod.mk.inj h1
      exact ⟨rfl, hmeta0⟩
    | _ => simp [specPanic] at h

/-- **Exact structural `PlaceExpr` lifting (`Local` / `Field` / `Downcast`):** on `liftMachToTB m`,
evaluating any chain of `Local`, `Field`, and `Downcast` projections has the **exact same
outcome** as on `m` (succeeding together with the lifted thin pointer, same alignment, same
type, and unchanged machine, or failing together with the exact same `Stop`). -/
theorem ep1_evalPlaceM_liftMachToTB_exact (m : Mach) (place : Gen.PlaceExpr)
    (hc : Ep1PlaceChain place) :
    evalPlaceM (liftMachToTB m) place =
      (match evalPlace m place with
       | .ok ((rp, ty), _) =>
         .ok ((⟨⟨liftThinPtrTB rp.ptr.thin_pointer, none⟩, rp.aligned⟩, ty), liftMachToTB m)
       | .error e => .error e) := by
  induction hc with
  | Local name => exact ep1_evalPlaceM_local_lift m name
  | Downcast root d hroot ih =>
    unfold evalPlaceM evalPlace
    rw [ih]
    cases hr : evalPlace m root with
    | error e => rfl
    | ok res =>
      obtain ⟨⟨rp, ty⟩, m1⟩ := res
      obtain ⟨rfl, _⟩ := ep1_evalPlace_chain_thin_and_readonly root hroot m m1 rp ty hr
      dsimp only [bind, Except.bind]
      cases ty with
      | Enum variants dty discr sz al =>
        dsimp only
        cases mapIndex variants d "variants[discriminant]" <;> simp [pure, Except.pure]
      | _ => dsimp only; rfl
  | Field root field hroot ih =>
    unfold evalPlaceM evalPlace
    rw [ih]
    cases hr : evalPlace m root with
    | error e => rfl
    | ok res =>
      obtain ⟨⟨rp, ty⟩, m1⟩ := res
      obtain ⟨rfl, hmeta⟩ := ep1_evalPlace_chain_thin_and_readonly root hroot m m1 rp ty hr
      dsimp only [bind, Except.bind]
      have hca : ∀ lay, computeAlignM (liftMachToTB m1) lay none = computeAlign m1 lay none := by
        intro lay
        unfold computeAlignM computeAlign
        rw [ep1_compute_size_and_align_none_indep _ _ lay]
      have hcs : ∀ lay, computeSizeM (liftMachToTB m1) lay none = computeSize m1 lay none := by
        intro lay
        unfold computeSizeM computeSize
        rw [ep1_compute_size_and_align_none_indep _ _ lay]
      have htailEq : ∀ (off : Gen.Offset) (fty : Gen.Type),
          (do
            let rootSize ← computeSizeM (liftMachToTB m1) (← Type.layout ty) none
            if !(off.bytes ≤ rootSize.bytes) then
              specPanic "assertion failed: offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata)"
            else do
              let ptr ← ptrOffsetInboundsM (liftMachToTB m1) (liftThinPtrTB rp.ptr.thin_pointer) (off.bytes : Int)
              let ptr := if !LayoutStrategy.is_sized (← Type.layout fty) then
                  ThinPointer.widen ptr none
                else
                  ThinPointer.widen ptr none
              pure ((({ ptr := ptr, aligned := rp.aligned } : Gen.Place TBM), fty), liftMachToTB m1)) =
          (match (do
            let rootSize ← computeSize m1 (← Type.layout ty) rp.ptr.metadata
            if !(off.bytes ≤ rootSize.bytes) then
              specPanic "assertion failed: offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata)"
            else do
              let ptr ← ptrOffsetInbounds m1 rp.ptr.thin_pointer (off.bytes : Int)
              let ptr := if !LayoutStrategy.is_sized (← Type.layout fty) then
                  ThinPointer.widen ptr rp.ptr.metadata
                else
                  ThinPointer.widen ptr none
              pure ((({ rp with ptr := ptr } : Gen.Place BM), fty), m1)) with
           | .ok ((rp', ty'), _) =>
             let pLift : Gen.Place TBM :=
               { ptr := { thin_pointer := liftThinPtrTB rp'.ptr.thin_pointer, metadata := none }
                 aligned := rp'.aligned }
             .ok ((pLift, ty'), liftMachToTB m1)
           | .error e => .error e) := by
        intro off fty
        cases hlay : Type.layout ty with
        | error e => rfl
        | ok lay =>
          simp only [bind, Except.bind, hmeta, hcs lay]
          cases computeSize m1 lay none with
          | error e => rfl
          | ok rsz =>
            dsimp only
            by_cases hle : (!decide (off.bytes ≤ rsz.bytes)) = true
            · simp only [hle, ↓reduceIte, specPanic]
            · simp only [hle, ep1_ptrOffsetInbounds_lift_exact]
              cases ptrOffsetInbounds m1 rp.ptr.thin_pointer (off.bytes : Int) with
              | error e => rfl
              | ok p' =>
                dsimp only [Functor.map, Except.map]
                cases Type.layout fty with
                | error e => rfl
                | ok flay =>
                  dsimp only [pure, Except.pure, ThinPointer.widen]
                  cases LayoutStrategy.is_sized flay <;> rfl
      cases ty with
      | Tuple sf sh uf =>
        dsimp only
        by_cases hc1 : 0 ≤ field ∧ field < (sf.length : Int)
        · simp only [hc1, and_self, ↓reduceIte]
          cases listIndex sf field "sized_fields[field]" with
          | error e => rfl
          | ok oft => exact htailEq oft.1 oft.2
        · simp only [hc1, ↓reduceIte]
          by_cases hc2 : field = (sf.length : Int)
          · simp only [hc2, ↓reduceIte]
            cases uf with
            | none => rfl
            | some tailTy =>
              dsimp only
              cases htl : Type.layout tailTy with
              | error e => rfl
              | ok tlay =>
                have hca' : computeAlignM (liftMachToTB m1) tlay none = computeAlign m1 tlay rp.ptr.metadata := by
                  rw [hmeta]; exact hca tlay
                dsimp only
                rw [hca']
                cases computeAlign m1 tlay rp.ptr.metadata with
                | error e => rfl
                | ok tal =>
                  dsimp only [pure, Except.pure]
                  exact htailEq (TupleHeadLayout.tail_offset sh tal) tailTy
          · simp only [hc2, ↓reduceIte]; rfl
      | Union fields _ _ _ =>
        dsimp only
        cases listIndex fields field "fields[field]" with
        | error e => rfl
        | ok oft => exact htailEq oft.1 oft.2
      | _ => dsimp only; rfl

/-- **Exact bidirectional `MachTB ↔ Mach` equivalence of `GetDiscriminant` on `liftMachToTB m`**
for **every** structural place chain (`Local` / `Field` / `Downcast`, closing the open item from
B2): on a freshly lifted machine, `GetDiscriminant` succeeds under Tree Borrows **if and only
if** it succeeds on `BasicMemory`, returning the **same discriminant at the same type** AND the
**exact lifted resulting machine `mTB' = liftMachToTB mBM'`** (identical data-race access log
and strictly unchanged borrow trees). -/
theorem ep1_getDiscriminant_liftMachToTB_iff (m : Mach) (place : Gen.PlaceExpr)
    (hc : Ep1PlaceChain place) :
    (∀ (x : Int) (dty : Gen.IntType) (mBM' : Mach),
      evalValue m (.GetDiscriminant place) = .ok ((.Int x, .Int dty), mBM') →
      evalValueM (liftMachToTB m) (.GetDiscriminant place) =
        .ok ((.Int x, .Int dty), liftMachToTB mBM')) ∧
    (∀ (r : Gen.Value TBM × Gen.Type) (mTB' : MachTB),
      evalValueM (liftMachToTB m) (.GetDiscriminant place) = .ok (r, mTB') →
      ∃ (x : Int) (dty : Gen.IntType) (mBM' : Mach),
        r = (.Int x, .Int dty) ∧
        mTB' = liftMachToTB mBM' ∧
        evalValue m (.GetDiscriminant place) = .ok ((.Int x, .Int dty), mBM')) := by
  have hliftP := ep1_evalPlaceM_liftMachToTB_exact m place hc
  have hliftMem : ∀ (mA : Mach) (p : Ptr) (d : Gen.Discriminator),
      let accBM := fun (s : Mach) (idx : Gen.Offset) (sz : Size) => do
        let ptr ← ptrOffsetInboundsM (M := BM) s p (idx.bytes : Int)
        let (bs, cm) ← ConcurrentMemory.load (M := BM) s.mem ptr sz ⟨1⟩ .None
        pure (bs, { s with mem := cm })
      let accTB := fun (s : MachTB) (idx : Gen.Offset) (sz : Size) => do
        let ptr ← ptrOffsetInboundsM s (liftThinPtrTB p) (idx.bytes : Int)
        let (bs, cm) ← ConcurrentMemory.load s.mem ptr sz ⟨1⟩ .None
        pure (bs, { s with mem := cm })
      (∀ (res : Option Int) (mA' : Mach),
        decodeDiscriminantM (M := BM) accBM d mA = .ok (res, mA') →
        decodeDiscriminantM (M := TBM) accTB d (liftMachToTB mA) = .ok (res, liftMachToTB mA')) ∧
      (∀ (res : Option Int) (mTB' : MachTB),
        decodeDiscriminantM (M := TBM) accTB d (liftMachToTB mA) = .ok (res, mTB') →
        ∃ mA', mTB' = liftMachToTB mA' ∧
          decodeDiscriminantM (M := BM) accBM d mA = .ok (res, mA')) := by
    intro mA p d
    let accBM := fun (s : Mach) (idx : Gen.Offset) (sz : Size) => do
      let ptr ← ptrOffsetInboundsM (M := BM) s p (idx.bytes : Int)
      let (bs, cm) ← ConcurrentMemory.load (M := BM) s.mem ptr sz ⟨1⟩ .None
      pure (bs, { s with mem := cm })
    let accTB := fun (s : MachTB) (idx : Gen.Offset) (sz : Size) => do
      let ptr ← ptrOffsetInboundsM s (liftThinPtrTB p) (idx.bytes : Int)
      let (bs, cm) ← ConcurrentMemory.load s.mem ptr sz ⟨1⟩ .None
      pure (bs, { s with mem := cm })
    have hstep1 : ∀ (s1 : Mach) (s2 : MachTB) off sz bs1 s1',
        s2 = liftMachToTB s1 → accBM s1 off sz = .ok (bs1, s1') →
        ∃ bs2 s2', accTB s2 off sz = .ok (bs2, s2') ∧
          bs1.map AbstractByte.dataM = bs2.map AbstractByte.dataM ∧ s2' = liftMachToTB s1' := by
      intro s1 s2 off sz bs1 s1' hEq hacc
      subst hEq
      obtain ⟨p1, hpo1, hacc⟩ := ep1_bind_ok hacc
      obtain ⟨⟨bs, cm1⟩, hld1, hacc⟩ := ep1_bind_ok hacc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ep1_pure_ok hacc)
      unfold ConcurrentMemory.load at hld1
      obtain ⟨⟨bs', bm1⟩, hml1, hcm1⟩ := ep1_bind_ok hld1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ep1_pure_ok hcm1)
      change BM.load s1.mem.memory p1 sz ⟨1⟩ = .ok (bs', bm1) at hml1
      have hbmEq : bm1 = s1.mem.memory := BM.load_eq hml1
      subst hbmEq
      have hpoTB : ptrOffsetInboundsM (liftMachToTB s1) (liftThinPtrTB p) (off.bytes : Int) =
          .ok (liftThinPtrTB p1) := by
        rw [ep1_ptrOffsetInbounds_lift_exact, ← ep1_ptrOffsetInboundsM_bm_eq, hpo1]; rfl
      have hldTB : TreeBorrowsMemory.load (liftMachToTB s1).mem.memory (liftThinPtrTB p1) sz ⟨1⟩ =
          .ok (bs'.map liftByteTB, (liftMachToTB s1).mem.memory) := by
        rw [ep1_load_lift_exact, hml1]
      let s1Next : Mach :=
        { s1 with mem := { memory := s1.mem.memory, accesses := s1.mem.accesses ++ [⟨.Load, .None, p1.addr, sz⟩] } }
      have hcmTB : ConcurrentMemory.load (liftMachToTB s1).mem (liftThinPtrTB p1) sz ⟨1⟩ .None =
          .ok (bs'.map liftByteTB, (liftMachToTB s1Next).mem) :=
        ep1_concurrent_load_of_mem_load (liftMachToTB s1).mem (liftThinPtrTB p1) sz ⟨1⟩ .None
          (bs'.map liftByteTB) (liftMachToTB s1).mem.memory hldTB
      refine ⟨bs'.map liftByteTB, liftMachToTB s1Next, ?_, ?_, rfl⟩
      · simp only [accTB, hpoTB, hcmTB, bind, Except.bind, pure, Except.pure]; rfl
      · rw [List.map_map]
        apply List.map_congr_left
        intro b _; cases b <;> rfl
    have hstep2 : ∀ (s1 : MachTB) (s2 : Mach) off sz bs1 s1',
        s1 = liftMachToTB s2 → accTB s1 off sz = .ok (bs1, s1') →
        ∃ bs2 s2', accBM s2 off sz = .ok (bs2, s2') ∧
          bs1.map AbstractByte.dataM = bs2.map AbstractByte.dataM ∧ s1' = liftMachToTB s2' := by
      intro s1 s2 off sz bs1 s1' hEq hacc
      subst hEq
      obtain ⟨pTB, hpoTB, hacc⟩ := ep1_bind_ok hacc
      rw [ep1_ptrOffsetInbounds_lift_exact, ← ep1_ptrOffsetInboundsM_bm_eq] at hpoTB
      cases hpoBM : ptrOffsetInboundsM (M := BM) s2 p (off.bytes : Int) with
      | error e => simp [hpoBM, Functor.map, Except.map] at hpoTB
      | ok pBM =>
        simp only [hpoBM, Functor.map, Except.map, Except.ok.injEq] at hpoTB
        subst hpoTB
        obtain ⟨⟨bsTB, cmTB⟩, hldTB, hacc⟩ := ep1_bind_ok hacc
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ep1_pure_ok hacc)
        unfold ConcurrentMemory.load at hldTB
        obtain ⟨⟨bsTB', tbm'⟩, hmlTB, hcmTB⟩ := ep1_bind_ok hldTB
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ep1_pure_ok hcmTB)
        change TreeBorrowsMemory.load (liftMachToTB s2).mem.memory (liftThinPtrTB pBM) sz ⟨1⟩ =
          .ok (bsTB', tbm') at hmlTB
        rw [ep1_load_lift_exact] at hmlTB
        cases hmlBM : BM.load s2.mem.memory pBM sz ⟨1⟩ with
        | error e => simp [hmlBM] at hmlTB
        | ok resBM =>
          obtain ⟨bsBM, bm'⟩ := resBM
          have hbmEq : bm' = s2.mem.memory := BM.load_eq hmlBM
          subst hbmEq
          simp only [hmlBM, Except.ok.injEq, Prod.mk.injEq] at hmlTB
          obtain ⟨rfl, rfl⟩ := hmlTB
          let cmBMNext : Gen.ConcurrentMemory BM :=
            { memory := s2.mem.memory, accesses := s2.mem.accesses ++ [⟨.Load, .None, pBM.addr, sz⟩] }
          have hcmBM : ConcurrentMemory.load (M := BM) s2.mem pBM sz ⟨1⟩ .None =
              .ok (bsBM, cmBMNext) :=
            ep1_concurrent_load_of_mem_load (M := BM) s2.mem pBM sz ⟨1⟩ .None bsBM s2.mem.memory hmlBM
          refine ⟨bsBM, { s2 with mem := cmBMNext }, ?_, ?_, rfl⟩
          · simp only [accBM, hpoBM, hcmBM, bind, Except.bind, pure, Except.pure]
          · rw [List.map_map]
            apply List.map_congr_left
            intro b _; cases b <;> rfl
    constructor
    · intro res mA' hbm
      obtain ⟨mTB', htb, hEq⟩ :=
        ep1_decodeDiscriminantM_sim2 (fun a b => b = liftMachToTB a) accBM accTB hstep1 d res mA mA'
          (liftMachToTB mA) rfl hbm
      rw [← hEq]; exact htb
    · intro res mTB' htb
      obtain ⟨mA', hbm, hEq⟩ :=
        ep1_decodeDiscriminantM_sim2 (fun a b => a = liftMachToTB b) accTB accBM hstep2 d res
          (liftMachToTB mA) mTB' mA rfl htb
      exact ⟨mA', hEq, hbm⟩
  constructor
  · intro x dty mBM' hbm
    rw [← evalValueM_bm_eq] at hbm
    cases hp : evalPlace m place with
    | error e =>
      rw [← evalPlaceM_bm_eq] at hp
      simp [evalValueM, hp, bind, Except.bind] at hbm
    | ok res =>
      obtain ⟨⟨rp, ty⟩, m1⟩ := res
      obtain ⟨rfl, _⟩ := ep1_evalPlace_chain_thin_and_readonly place hc m m1 rp ty hp
      rw [hp] at hliftP
      rw [← evalPlaceM_bm_eq] at hp
      unfold evalValueM at hbm ⊢
      rw [hp] at hbm; rw [hliftP]
      dsimp only [bind, Except.bind] at hbm ⊢
      cases ty with
      | Enum variants dty' discr sz al =>
        dsimp only at hbm ⊢
        split at hbm
        · simp [ub] at hbm
        · rename_i hal
          simp only [hal]
          obtain ⟨⟨opt, m2⟩, hdd, hret⟩ := ep1_bind_ok hbm
          cases opt with
          | none => simp [ub] at hret
          | some x' =>
            obtain ⟨hvt, rfl⟩ := Prod.mk.inj (ep1_pure_ok hret)
            obtain ⟨hx, hdty⟩ := Prod.mk.inj hvt
            cases hx; cases hdty
            have hddTB := (hliftMem m1 rp.ptr.thin_pointer discr).1 (some x) m2 hdd
            simp only [bind, Except.bind] at hddTB ⊢
            rw [hddTB]; rfl
      | _ => simp [specPanic] at hbm
  · intro r mTB' htb
    cases hp : evalPlace m place with
    | error e =>
      rw [hp] at hliftP
      simp [evalValueM, hliftP, bind, Except.bind] at htb
    | ok res =>
      obtain ⟨⟨rp, ty⟩, m1⟩ := res
      obtain ⟨rfl, _⟩ := ep1_evalPlace_chain_thin_and_readonly place hc m m1 rp ty hp
      rw [hp] at hliftP
      unfold evalValueM at htb
      rw [hliftP] at htb
      dsimp only [bind, Except.bind] at htb
      cases ty with
      | Enum variants dty discr sz al =>
        dsimp only at htb
        split at htb
        · simp [ub] at htb
        · rename_i hal
          obtain ⟨⟨opt, m2⟩, hdd, hret⟩ := ep1_bind_ok htb
          cases opt with
          | none => simp [ub] at hret
          | some x =>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ep1_pure_ok hret)
            obtain ⟨mBM', hmEq, hddBM⟩ := (hliftMem m1 rp.ptr.thin_pointer discr).2 (some x) m2 hdd
            refine ⟨x, dty, mBM', rfl, hmEq, ?_⟩
            rw [← evalValueM_bm_eq]
            unfold evalValueM
            rw [← evalPlaceM_bm_eq] at hp
            rw [hp]
            simp only [hal, bind, Except.bind] at hddBM ⊢
            rw [hddBM]; rfl
      | _ => simp [specPanic] at htb

/-- **Compositional `MachTB ⇒ Mach` place-relation transfer for `Downcast` and `Field`:**
for **arbitrary** (non-lifted) Tree Borrows states whose base `eval_place` evaluations agree on
`(ep1PtrView, aligned, ty, metadata = none)` and `ep1AllocView`, both `PlaceExpr::Downcast` and
`PlaceExpr::Field` preserve that exact agreement — plugging directly into
`ep1_getDiscriminant_tb_success_implies_bm_success` for arbitrary `Downcast`/`Field` chains
above any related place (including `Deref` through child borrow tags). -/
theorem ep1_evalPlaceM_downcast_field_tb_to_bm
    (mTB mTB1 : MachTB) (mBM mBM1 : Mach) (root : Gen.PlaceExpr)
    (rpTB : Gen.Place TBM) (rpBM : Gen.Place BM) (ty : Gen.Type)
    (hpTB : evalPlaceM mTB root = .ok ((rpTB, ty), mTB1))
    (hpBM : evalPlace mBM root = .ok ((rpBM, ty), mBM1))
    (hptr : ep1PtrView rpTB.ptr.thin_pointer = ep1PtrView rpBM.ptr.thin_pointer)
    (hmetaTB : rpTB.ptr.metadata = none) (hmetaBM : rpBM.ptr.metadata = none)
    (hal : rpTB.aligned = rpBM.aligned)
    (hmem : mTB1.mem.memory.mem.allocations.map ep1AllocView =
      mBM1.mem.memory.allocations.map ep1AllocView) :
    (∀ (d : Int) (rpTB' : Gen.Place TBM) (varTy : Gen.Type) (mTB' : MachTB),
      evalPlaceM mTB (.Downcast root d) = .ok ((rpTB', varTy), mTB') →
      rpTB' = rpTB ∧ mTB' = mTB1 ∧
      evalPlace mBM (.Downcast root d) = .ok ((rpBM, varTy), mBM1)) ∧
    (∀ (field : Int) (rpTB' : Gen.Place TBM) (fieldTy : Gen.Type) (mTB' : MachTB),
      evalPlaceM mTB (.Field root field) = .ok ((rpTB', fieldTy), mTB') →
      ∃ rpBM',
        mTB' = mTB1 ∧
        evalPlace mBM (.Field root field) = .ok ((rpBM', fieldTy), mBM1) ∧
        ep1PtrView rpTB'.ptr.thin_pointer = ep1PtrView rpBM'.ptr.thin_pointer ∧
        rpTB'.ptr.metadata = none ∧ rpBM'.ptr.metadata = none ∧
        rpTB'.aligned = rpBM'.aligned) := by
  constructor
  · intro d rpTB' varTy mTB' h
    unfold evalPlaceM at h
    rw [hpTB] at h
    dsimp only [bind, Except.bind] at h
    cases ty with
    | Enum variants dty discr sz al =>
      obtain ⟨var, hmi, h⟩ := ep1_bind_ok h
      obtain ⟨h1, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
      refine ⟨rfl, rfl, ?_⟩
      unfold evalPlace
      rw [hpBM]
      simp only [hmi, bind, Except.bind, pure, Except.pure]
    | _ => simp [specPanic] at h
  · intro field rpTB' fieldTy mTB' h
    have hca : ∀ lay, computeAlignM mTB1 lay none = computeAlign mBM1 lay none := by
      intro lay; unfold computeAlignM computeAlign
      rw [ep1_compute_size_and_align_none_indep _ _ lay]
    have hcs : ∀ lay, computeSizeM mTB1 lay none = computeSize mBM1 lay none := by
      intro lay; unfold computeSizeM computeSize
      rw [ep1_compute_size_and_align_none_indep _ _ lay]
    have htail : ∀ (off : Gen.Offset) (fty : Gen.Type),
        (do
          let rootSize ← computeSizeM mTB1 (← Type.layout ty) none
          if !(off.bytes ≤ rootSize.bytes) then
            specPanic "assertion failed: offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata)"
          else do
            let ptr ← ptrOffsetInboundsM mTB1 rpTB.ptr.thin_pointer (off.bytes : Int)
            let ptr := if !LayoutStrategy.is_sized (← Type.layout fty) then
                ThinPointer.widen ptr none
              else
                ThinPointer.widen ptr none
            pure (({ rpTB with ptr := ptr }, fty), mTB1)) = .ok ((rpTB', fieldTy), mTB') →
        ∃ rpBM' : Gen.Place BM,
          mTB' = mTB1 ∧
          (do
            let rootSize ← computeSize mBM1 (← Type.layout ty) rpBM.ptr.metadata
            if !(off.bytes ≤ rootSize.bytes) then
              specPanic "assertion failed: offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata)"
            else do
              let ptr ← ptrOffsetInbounds mBM1 rpBM.ptr.thin_pointer (off.bytes : Int)
              let ptr := if !LayoutStrategy.is_sized (← Type.layout fty) then
                  ThinPointer.widen ptr rpBM.ptr.metadata
                else
                  ThinPointer.widen ptr none
              pure (({ rpBM with ptr := ptr }, fty), mBM1)) = .ok ((rpBM', fieldTy), mBM1) ∧
          ep1PtrView rpTB'.ptr.thin_pointer = ep1PtrView rpBM'.ptr.thin_pointer ∧
          rpTB'.ptr.metadata = none ∧ rpBM'.ptr.metadata = none ∧
          rpTB'.aligned = rpBM'.aligned := by
      intro off fty ht
      obtain ⟨lay, hlay, ht⟩ := ep1_bind_ok ht
      obtain ⟨rsz, hrsz, ht⟩ := ep1_bind_ok ht
      have hrszBM : computeSize mBM1 lay rpBM.ptr.metadata = .ok rsz := by
        rw [hmetaBM, ← hcs lay]; exact hrsz
      split at ht
      · simp [specPanic] at ht
      · rename_i hle
        obtain ⟨pTB', hpoTB, ht⟩ := ep1_bind_ok ht
        obtain ⟨flay, hflay, ht⟩ := ep1_bind_ok ht
        obtain ⟨h1, rfl⟩ := Prod.mk.inj (ep1_pure_ok ht)
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
        obtain ⟨pBM', hpoBM, hview'⟩ :=
          ep1_ptrOffsetInbounds_tb_to_bm mTB1 mBM1 rpTB.ptr.thin_pointer rpBM.ptr.thin_pointer
            (off.bytes : Int) hmem hptr pTB' hpoTB
        rw [ep1_ptrOffsetInboundsM_bm_eq] at hpoBM
        refine ⟨{ rpBM with ptr := if !LayoutStrategy.is_sized flay then ThinPointer.widen pBM' rpBM.ptr.metadata
            else ThinPointer.widen pBM' none }, rfl, ?_, ?_, ?_, ?_, hal⟩
        · simp only [hlay, hrszBM, hle, Bool.false_eq_true, ↓reduceIte, hpoBM, hflay, bind, Except.bind, pure, Except.pure]
        · split <;> simpa [ThinPointer.widen] using hview'
        · split <;> simp [ThinPointer.widen]
        · split <;> simp [ThinPointer.widen, hmetaBM]
    simp only [evalPlaceM, hpTB, bind, Except.bind] at h
    rw [hmetaTB] at h
    cases ty with
    | Tuple sf sh uf =>
      dsimp only at h
      by_cases hc1 : 0 ≤ field ∧ field < (sf.length : Int)
      · simp only [hc1, and_self, ↓reduceIte] at h
        obtain ⟨⟨off, fty⟩, hidx, ht⟩ := ep1_bind_ok h
        obtain ⟨rpBM', rfl, hbmT, hv, hm1, hm2, ha⟩ := htail off fty ht
        refine ⟨rpBM', rfl, ?_, hv, hm1, hm2, ha⟩
        simp only [evalPlace, hpBM, hc1, and_self, ↓reduceIte, hidx, bind, Except.bind]
        exact hbmT
      · simp only [hc1, ↓reduceIte] at h
        by_cases hc2 : field = (sf.length : Int)
        · simp only [hc2, ↓reduceIte] at h
          cases uf with
          | none => simp [specPanic] at h
          | some tailTy =>
            obtain ⟨tlay, htlay, h⟩ := ep1_bind_ok h
            obtain ⟨tal, htal, ht⟩ := ep1_bind_ok h
            dsimp only [bind, Except.bind, pure, Except.pure] at ht
            have htalBM : computeAlign mBM1 tlay rpBM.ptr.metadata = .ok tal := by
              rw [hmetaBM, ← hca tlay]; exact htal
            obtain ⟨rpBM', rfl, hbmT, hv, hm1, hm2, ha⟩ :=
              htail (TupleHeadLayout.tail_offset sh tal) tailTy ht
            refine ⟨rpBM', rfl, ?_, hv, hm1, hm2, ha⟩
            simp only [evalPlace, hpBM, hc2, Int.lt_irrefl, and_false, ↓reduceIte,
              htlay, htalBM, bind, Except.bind, pure, Except.pure]
            simpa only [htlay, bind, Except.bind, pure, Except.pure] using hbmT
        · simp [hc2, specPanic] at h
    | Union fields chunks sz al =>
      obtain ⟨⟨off, fty⟩, hidx, ht⟩ := ep1_bind_ok h
      obtain ⟨rpBM', rfl, hbmT, hv, hm1, hm2, ha⟩ := htail off fty ht
      refine ⟨rpBM', rfl, ?_, hv, hm1, hm2, ha⟩
      simp only [evalPlace, hpBM, hidx, bind, Except.bind]
      exact hbmT
    | _ => simp [specPanic] at h

/-! #### Arbitrary-chunk `ValueExpr::Union` `encodeM` totality & disjoint-chunk `decodeM ∘ encodeM` roundtrip -/

/-- Pairwise disjointness of union chunk byte ranges `[off₁, off₁ + len₁)` and
`[off₂, off₂ + len₂)`. -/
def ep1ChunksDisjoint (chunks : List (Gen.Offset × Size)) : Prop :=
  chunks.Pairwise (fun c1 c2 =>
    c1.1.bytes + c1.2.bytes ≤ c2.1.bytes ∨ c2.1.bytes + c2.2.bytes ≤ c1.1.bytes)

private theorem ep1_writeSubsliceAtIndex_disjoint_preserves {T : Type}
    {xs ys bs : List T} {off1 off2 len2 : Nat}
    (hws : writeSubsliceAtIndex xs (off1 : Int) bs = .ok ys)
    (hdisj : off1 + bs.length ≤ off2 ∨ off2 + len2 ≤ off1) :
    subsliceWithLength ys (off2 : Int) (len2 : Int) =
      subsliceWithLength xs (off2 : Int) (len2 : Int) := by
  have hlen := writeSubsliceAtIndex_length hws
  unfold writeSubsliceAtIndex at hws
  split at hws
  · rename_i hcond
    have hy := ep1_pure_ok hws
    subst hy
    unfold subsliceWithLength
    simp only [hlen]
    split
    · rename_i hc2
      simp only [Int.toNat_natCast, pure, Except.pure, Except.ok.injEq]
      have hlenTake : (xs.take off1).length = off1 := by
        simp only [List.length_take]; omega
      rcases hdisj with hle | hle
      · rw [List.append_assoc, List.drop_append]
        have hdrop1 : (xs.take off1).drop off2 = [] :=
          List.drop_eq_nil_of_le (by omega)
        rw [hdrop1, List.nil_append, List.drop_append]
        have hdrop2 : bs.drop (off2 - (xs.take off1).length) = [] :=
          List.drop_eq_nil_of_le (by omega)
        rw [hdrop2, List.nil_append, List.drop_drop, hlenTake]
        have hsum : off1 + bs.length + (off2 - off1 - bs.length) = off2 := by omega
        rw [hsum]
      · rw [List.append_assoc, List.drop_append]
        have hlenDrop : ((xs.take off1).drop off2).length = off1 - off2 := by
          rw [List.length_drop, hlenTake]
        rw [List.take_append_of_le_length (by omega), List.drop_take, List.take_take,
          Nat.min_eq_left (by omega)]
    · rfl
  · simp [specPanic] at hws

private theorem ep1_encodeUnionChunksM_total_and_disjoint {M : Type} [Gen.Memory M]
    (sz : Nat) :
    ∀ (chunks : List (Gen.Offset × Size))
      (chunkData : List (List (Gen.AbstractByte (Gen.Memory.Provenance M))))
      (buf : List (Gen.AbstractByte (Gen.Memory.Provenance M))),
      buf.length = sz →
      (hlen : chunks.length = chunkData.length) →
      (∀ i (hi : i < chunks.length),
        (chunkData[i]'(hlen ▸ hi)).length = chunks[i].2.bytes ∧
        chunks[i].1.bytes + chunks[i].2.bytes ≤ sz) →
      ∃ out, Type.encodeUnionChunksM (M := M) chunks chunkData buf = .ok out ∧
        out.length = sz ∧
        (ep1ChunksDisjoint chunks →
          chunks.mapM (fun (off, csz) => subsliceWithLength out off.bytes csz.bytes) = .ok chunkData) ∧
        (∀ off len,
          (∀ c ∈ chunks, c.1.bytes + c.2.bytes ≤ off ∨ off + len ≤ c.1.bytes) →
          subsliceWithLength out (off : Int) (len : Int) =
            subsliceWithLength buf (off : Int) (len : Int))
  | [], [], buf, hbuf, _, _ =>
    ⟨buf, rfl, hbuf, fun _ => rfl, fun _ _ _ => rfl⟩
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | (off, csz) :: rest, d :: restData, buf, hbuf, hlen, hall => by
    have h0 := hall 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    obtain ⟨hdLen, h0le⟩ := h0
    have hwsCond : (0 : Int) ≤ (off.bytes : Int) ∧
        (off.bytes : Int) + (d.length : Int) ≤ (buf.length : Int) := by
      rw [hbuf, hdLen]; omega
    let buf1 := buf.take off.bytes ++ d ++ buf.drop (off.bytes + d.length)
    have hws : writeSubsliceAtIndex buf (off.bytes : Int) d = .ok buf1 := by
      unfold writeSubsliceAtIndex
      simp only [hwsCond, and_self, ↓reduceIte, Int.toNat_natCast, pure, Except.pure, buf1]
    have hbuf1Len : buf1.length = sz := by
      rw [writeSubsliceAtIndex_length hws, hbuf]
    have hlenRest : rest.length = restData.length := by simp at hlen; omega
    have hallRest : ∀ i (hi : i < rest.length),
        (restData[i]'(hlenRest ▸ hi)).length = rest[i].2.bytes ∧
        rest[i].1.bytes + rest[i].2.bytes ≤ sz := by
      intro i hi
      exact hall (i + 1) (by simp; omega)
    obtain ⟨out, hencRest, houtLen, hdisjRest, hpresRest⟩ :=
      ep1_encodeUnionChunksM_total_and_disjoint sz rest restData buf1 hbuf1Len hlenRest hallRest
    refine ⟨out, ?_, houtLen, ?_, ?_⟩
    · unfold Type.encodeUnionChunksM
      simp only [hdLen, ne_eq, not_true_eq_false, ↓reduceIte, hws, bind, Except.bind, hencRest]
    · intro hdisj
      unfold ep1ChunksDisjoint at hdisj
      rw [List.pairwise_cons] at hdisj
      obtain ⟨hheadDisj, htailDisj⟩ := hdisj
      have hheadRecover : subsliceWithLength out (off.bytes : Int) (csz.bytes : Int) = .ok d := by
        rw [hpresRest off.bytes csz.bytes (fun c hc => by
          rcases hheadDisj c hc with h1 | h2
          · exact Or.inr h1
          · exact Or.inl h2)]
        rw [← hdLen]
        exact (ep1_writeSubsliceAtIndex_subslice_recover hws).2
      have htailRecover := hdisjRest htailDisj
      simp only [List.mapM_cons, hheadRecover, htailRecover, bind, Except.bind, pure, Except.pure]
    · intro off' len' houtDisj
      rw [hpresRest off' len' (fun c hc => houtDisj c (List.mem_cons_of_mem _ hc))]
      have h0d := houtDisj (off, csz) (List.mem_cons_self ..)
      rw [← hdLen] at h0d
      exact ep1_writeSubsliceAtIndex_disjoint_preserves hws h0d

/-- **Universal `ValueExpr::Union` arbitrary-chunk `encodeM` totality and disjoint-chunk
`decodeM ∘ encodeM` roundtrip:** on every `Memory` `M` and for **any** chunk list `chunks`
(empty, multi-chunk, gapped, or overlapping):
1. whenever `evalValueM m (.Union field expr (.Union fields chunks sz al)) = .ok ((v, ty), m1)`,
   `Type.encodeM ty v` **unconditionally succeeds** returning `bs` with `bs.length = sz.bytes`;
2. whenever `chunks` are pairwise disjoint (`ep1ChunksDisjoint chunks`), re-decoding `bs` via
   `Type.decodeM ty bs` recovers **the exact same union value** `some v` (`Type.decodeM ty bs =
   .ok (some v)`). (`ep1_evalValueM_union_decode_encode_roundtrip_any_chunks` proves the
   roundtrip without the disjointness hypothesis.) -/
theorem ep1_evalValueM_union_encode_total_and_disjoint_roundtrip
    {M : Type} [Gen.Memory M] [MemoryOps M]
    (m m1 : Gen.Machine M) (field : Int) (expr : Gen.ValueExpr)
    (fields : List (Gen.Offset × Gen.Type)) (chunks : List (Gen.Offset × Size))
    (sz : Size) (al : Align) (v : Gen.Value M) (ty : Gen.Type)
    (h : evalValueM m (.Union field expr (.Union fields chunks sz al)) = .ok ((v, ty), m1)) :
    ty = .Union fields chunks sz al ∧
    ∃ bs, Type.encodeM ty v = .ok bs ∧ bs.length = sz.bytes ∧
      (ep1ChunksDisjoint chunks → Type.decodeM (M := M) ty bs = .ok (some v)) := by
  rw [ep1_evalValueM_union_complete_spec] at h
  obtain ⟨⟨off, exprTy⟩, _, h⟩ := ep1_bind_ok h
  obtain ⟨⟨⟨val, _⟩, _⟩, _, h⟩ := ep1_bind_ok h
  obtain ⟨encoded, _, h⟩ := ep1_bind_ok h
  obtain ⟨data, hws, h⟩ := ep1_bind_ok h
  obtain ⟨chunkData, hmap, hp⟩ := ep1_bind_ok h
  obtain ⟨hvt, _⟩ := Prod.mk.inj (ep1_pure_ok hp)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hvt
  have hdataLen : data.length = sz.bytes := by
    rw [writeSubsliceAtIndex_length hws, List.length_replicate]
  have hchunksProp : ∀ (cs : List (Gen.Offset × Size))
      (cd : List (List (Gen.AbstractByte (Gen.Memory.Provenance M)))),
      cs.mapM (fun (offset, chunkSize) => subsliceWithLength data offset.bytes chunkSize.bytes) = .ok cd →
      ∃ hlen : cs.length = cd.length,
        ∀ i (hi : i < cs.length),
          (cd[i]'(hlen ▸ hi)).length = cs[i].2.bytes ∧
          cs[i].1.bytes + cs[i].2.bytes ≤ sz.bytes := by
    intro cs
    induction cs with
    | nil =>
      intro cd hm
      have hp' := ep1_pure_ok hm; subst hp'
      exact ⟨rfl, fun i hi => by cases hi⟩
    | cons c rest ih =>
      intro cd hm
      simp only [List.mapM_cons] at hm
      obtain ⟨bs0, hsub0, hm⟩ := ep1_bind_ok hm
      obtain ⟨restCd, hrest, hp'⟩ := ep1_bind_ok hm
      have hp'' := ep1_pure_ok hp'; subst hp''
      obtain ⟨hrestLen, hrestAll⟩ := ih restCd hrest
      obtain ⟨hle0, rfl⟩ := ep1_subsliceWithLength_eq hsub0
      refine ⟨by simp [hrestLen], fun i hi => ?_⟩
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero, List.length_take, List.length_drop]
        omega
      | succ j =>
        simpa using hrestAll j (by simp at hi; omega)
  obtain ⟨hlenEq, hall⟩ := hchunksProp chunks chunkData hmap
  obtain ⟨out, hencOut, houtLen, hdisjOut, _⟩ :=
    ep1_encodeUnionChunksM_total_and_disjoint (M := M) sz.bytes chunks chunkData
      (List.replicate sz.bytes .Uninit) (List.length_replicate) hlenEq hall
  refine ⟨rfl, out, ?_, houtLen, ?_⟩
  · unfold Type.encodeM
    simp only [hlenEq, ne_eq, not_true_eq_false, ↓reduceIte, hencOut]
  · intro hdisj
    unfold Type.decodeM
    simp only [houtLen, ne_eq, not_true_eq_false, ↓reduceIte, hdisjOut hdisj,
      bind, Except.bind, pure, Except.pure]

/-- **Concrete edge-case witness (`[adv A2]`): gapped 2-chunk union padding loss + MIR-style
in-place enum construction (`Downcast` + `Field` + `SetDiscriminant` → `GetDiscriminant` +
`Load`) inside a struct**, on both `Mach` and `MachTB` (with `MachTB.wfLive`):
1. Gapped 2-chunk union `[(⟨0⟩, ⟨2⟩), (⟨4⟩, ⟨4⟩)]` (size 8, padding hole `[2..4)`): constructing
   via `ValueExpr::Union` with a 4-byte `u32` (`0xAABBCCDD`) at offset 0 succeeds, keeps only
   bytes `[0..2)` in chunk 0 and `.Uninit` in chunk 1, drops bytes `[2..4)` to `.Uninit` upon
   `Type::encode`, and `Type::decode` on the re-encoded bytes recovers the exact same `.Union`
   value (both `Mach` and `MachTB`).
2. MIR-style in-place enum construction inside a 2-field struct `(u32, ep1EnumTy)` at local `_0`:
   `Assign (.Field (.Downcast (.Field (.Local 0) 1) 1) 0) 0xCAFEBABE`, then
   `SetDiscriminant (.Field (.Local 0) 1) 1`, then `GetDiscriminant (.Field (.Local 0) 1)`
   returns `1`, and `Load (.Field (.Local 0) 1)` returns `.Variant 1 (.Tuple [.Int 0xCAFEBABE])`,
   with `MachTB.wfLive` preserved and `mTB_final = liftMachToTB mBM_final`. -/
theorem ep1_union_gapped_chunks_and_setDiscr_downcast_field_witness :
    let gappedUnionTy : Gen.Type :=
      .Union [(⟨0⟩, .Int ep1U32), (⟨4⟩, .Int ep1U32)] [(⟨0⟩, ⟨2⟩), (⟨4⟩, ⟨4⟩)] ⟨8⟩ ⟨4⟩
    let structWithEnumTy : Gen.Type :=
      .Tuple [(⟨0⟩, .Int ep1U32), (⟨4⟩, ep1EnumTy)] ⟨⟨12⟩, ⟨4⟩, none⟩ none
    let mBM := ep1MachBM
      [{ data := List.replicate 12 .Uninit, addr := 0x100, align := ⟨4⟩, kind := .Stack, live := true, extra := () }]
      [(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, ())⟩)]
      [(⟨⟨0⟩⟩, structWithEnumTy)]
    let mTB := liftMachToTB mBM
    let uExpr : Gen.ValueExpr := .Union 0 (.Constant (.Int 0xAABBCCDD) (.Int ep1U32)) gappedUnionTy
    let expectedChunksBM : List (List Byte) :=
      [[.Init 0xDD none, .Init 0xCC none], [.Uninit, .Uninit, .Uninit, .Uninit]]
    let expectedEncBM : List Byte :=
      [.Init 0xDD none, .Init 0xCC none, .Uninit, .Uninit, .Uninit, .Uninit, .Uninit, .Uninit]
    let expectedChunksTB : List (List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) :=
      [[.Init 0xDD none, .Init 0xCC none], [.Uninit, .Uninit, .Uninit, .Uninit]]
    let expectedEncTB : List (Gen.AbstractByte Gen.TreeBorrowsProvenance) :=
      [.Init 0xDD none, .Init 0xCC none, .Uninit, .Uninit, .Uninit, .Uninit, .Uninit, .Uninit]
    let enumFieldPlace : Gen.PlaceExpr := .Field (.Local ⟨⟨0⟩⟩) 1
    let payloadPlace : Gen.PlaceExpr := .Field (.Downcast enumFieldPlace 1) 0
    -- 1. Gapped 2-chunk union drops non-chunk bytes [2..4) to Uninit and roundtrips decode ∘ encode
    (evalValue mBM uExpr = .ok ((.Union expectedChunksBM, gappedUnionTy), mBM) ∧
     Type.encode gappedUnionTy (.Union expectedChunksBM) = .ok expectedEncBM ∧
     Type.decode gappedUnionTy expectedEncBM = .ok (some (.Union expectedChunksBM)) ∧
     evalValueM mTB uExpr = .ok ((.Union expectedChunksTB, gappedUnionTy), mTB) ∧
     Type.encodeM (M := TBM) gappedUnionTy (.Union expectedChunksTB) = .ok expectedEncTB ∧
     Type.decodeM (M := TBM) gappedUnionTy expectedEncTB = .ok (some (.Union expectedChunksTB))) ∧
    -- 2. In-place MIR-style Downcast + Field + SetDiscriminant -> GetDiscriminant + Load on nested enum
    (∃ m1 m2 m3 m4,
      evalStatement mBM (.Assign payloadPlace (.Constant (.Int 0xCAFEBABE) (.Int ep1U32))) = .ok m1 ∧
      evalStatement m1 (.SetDiscriminant enumFieldPlace 1) = .ok m2 ∧
      evalValue m2 (.GetDiscriminant enumFieldPlace) = .ok ((.Int 1, .Int ep1U8), m3) ∧
      evalValue m3 (.Load enumFieldPlace) = .ok ((.Variant 1 (.Tuple [.Int 0xCAFEBABE]), ep1EnumTy), m4) ∧
      (∃ t1 t2 t3 t4,
        evalStatementM mTB (.Assign payloadPlace (.Constant (.Int 0xCAFEBABE) (.Int ep1U32))) = .ok t1 ∧
        evalStatementM t1 (.SetDiscriminant enumFieldPlace 1) = .ok t2 ∧
        evalValueM t2 (.GetDiscriminant enumFieldPlace) = .ok ((.Int 1, .Int ep1U8), t3) ∧
        evalValueM t3 (.Load enumFieldPlace) = .ok ((.Variant 1 (.Tuple [.Int 0xCAFEBABE]), ep1EnumTy), t4) ∧
        t3 = liftMachToTB m3 ∧ MachTB.wfLive t4)) := by
  intro gappedUnionTy structWithEnumTy mBM mTB uExpr expectedChunksBM expectedEncBM
    expectedChunksTB expectedEncTB enumFieldPlace payloadPlace
  have hu : evalValue mBM uExpr = .ok ((.Union expectedChunksBM, gappedUnionTy), mBM) ∧
      Type.encode gappedUnionTy (.Union expectedChunksBM) = .ok expectedEncBM ∧
      Type.decode gappedUnionTy expectedEncBM = .ok (some (.Union expectedChunksBM)) ∧
      evalValueM mTB uExpr = .ok ((.Union expectedChunksTB, gappedUnionTy), mTB) ∧
      Type.encodeM (M := TBM) gappedUnionTy (.Union expectedChunksTB) = .ok expectedEncTB ∧
      Type.decodeM (M := TBM) gappedUnionTy expectedEncTB = .ok (some (.Union expectedChunksTB)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ep1_kernel_rfl
  have hbmRun : (do
      let m1 ← evalStatement mBM (.Assign payloadPlace (.Constant (.Int 0xCAFEBABE) (.Int ep1U32)))
      let m2 ← evalStatement m1 (.SetDiscriminant enumFieldPlace 1)
      let (r1, m3) ← evalValue m2 (.GetDiscriminant enumFieldPlace)
      let (r2, _) ← evalValue m3 (.Load enumFieldPlace)
      pure (r1, r2)) =
      .ok ((.Int 1, .Int ep1U8), (.Variant 1 (.Tuple [.Int 0xCAFEBABE]), ep1EnumTy)) := by
    ep1_kernel_rfl
  have htbRun : (do
      let t1 ← evalStatementM mTB (.Assign payloadPlace (.Constant (.Int 0xCAFEBABE) (.Int ep1U32)))
      let t2 ← evalStatementM t1 (.SetDiscriminant enumFieldPlace 1)
      let (r1, t3) ← evalValueM t2 (.GetDiscriminant enumFieldPlace)
      let (r2, t4) ← evalValueM t3 (.Load enumFieldPlace)
      pure (r1, r2, t4.mem.memory.mem.allocations.length)) =
      .ok ((.Int 1, .Int ep1U8), (.Variant 1 (.Tuple [.Int 0xCAFEBABE]), ep1EnumTy), 1) := by
    ep1_kernel_rfl
  obtain ⟨m1, hm1, hbmRest⟩ := ep1_bind_ok hbmRun
  obtain ⟨m2, hm2, hbmRest⟩ := ep1_bind_ok hbmRest
  obtain ⟨⟨r1, m3⟩, hm3, hbmRest⟩ := ep1_bind_ok hbmRest
  obtain ⟨⟨r2, m4⟩, hm4, hbmRet⟩ := ep1_bind_ok hbmRest
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ep1_pure_ok hbmRet)
  obtain ⟨t1, ht1, htbRest⟩ := ep1_bind_ok htbRun
  obtain ⟨t2, ht2, htbRest⟩ := ep1_bind_ok htbRest
  obtain ⟨⟨tr1, t3⟩, ht3, htbRest⟩ := ep1_bind_ok htbRest
  obtain ⟨⟨tr2, t4⟩, ht4, htbRet⟩ := ep1_bind_ok htbRest
  obtain ⟨rfl, htbEq2⟩ := Prod.mk.inj (ep1_pure_ok htbRet)
  obtain ⟨rfl, _⟩ := Prod.mk.inj htbEq2
  have ht3Eq : t3 = liftMachToTB m3 := by
    have ht2Eq : t2 = liftMachToTB m2 := by
      have hsame : (do
          let t1' ← evalStatementM mTB (.Assign payloadPlace (.Constant (.Int 0xCAFEBABE) (.Int ep1U32)))
          evalStatementM t1' (.SetDiscriminant enumFieldPlace 1)) =
        (liftMachToTB <$> (do
          let m1' ← evalStatement mBM (.Assign payloadPlace (.Constant (.Int 0xCAFEBABE) (.Int ep1U32)))
          evalStatement m1' (.SetDiscriminant enumFieldPlace 1))) := by ep1_kernel_rfl
      simp only [ht1, ht2, hm1, hm2, bind, Except.bind, Functor.map, Except.map,
        Except.ok.injEq] at hsame
      exact hsame
    have hgd := (ep1_getDiscriminant_liftMachToTB_iff m2 enumFieldPlace
      (.Field (.Local ⟨⟨0⟩⟩) 1 (.Local ⟨⟨0⟩⟩))).1 1 ep1U8 m3 hm3
    rw [ht2Eq] at ht3
    rw [ht3] at hgd
    cases hgd; rfl
  have hwf0 : MachTB.wfLive mTB := liftMachToTB_wfLive mBM
  have hwf1 : MachTB.wfLive t1 := evalStatementM_tb_wfLive hwf0 ht1
  have hwf2 : MachTB.wfLive t2 := evalStatementM_tb_wfLive hwf1 ht2
  have hwf3 : MachTB.wfLive t3 := evalValueM_tb_wfLive _ hwf2 ht3
  have hwf4 : MachTB.wfLive t4 := evalValueM_tb_wfLive _ hwf3 ht4
  exact ⟨hu, m1, m2, m3, m4, hm1, hm2, hm3, hm4, t1, t2, t3, t4, ht1, ht2, ht3, ht4, ht3Eq, hwf4⟩

/-! ### `[adv B3]` `Union` `decode ∘ encode` needs no chunk disjointness; overlapping-chunk witness -/

/-- Whether byte position `p` lies in some chunk `[off, off + len)` of `chunks`. -/
def ep1Covered (chunks : List (Gen.Offset × Size)) (p : Nat) : Bool :=
  chunks.any (fun c => decide (c.1.bytes ≤ p ∧ p < c.1.bytes + c.2.bytes))

private theorem ep1_writeSubsliceAtIndex_getElem? {T : Type} {xs src ys : List T} {off : Nat}
    (hws : writeSubsliceAtIndex xs (off : Int) src = .ok ys) (p : Nat) :
    ys.length = xs.length ∧
    ys[p]? = if off ≤ p ∧ p < off + src.length then src[p - off]? else xs[p]? := by
  unfold writeSubsliceAtIndex at hws
  split at hws
  · rename_i hc
    obtain rfl := ep1_pure_ok hws
    have hle : off + src.length ≤ xs.length := by omega
    simp only [Int.toNat_natCast]
    have hlt : (xs.take off).length = off := by simp; omega
    refine ⟨by simp; omega, ?_⟩
    by_cases h1 : p < off
    · rw [List.append_assoc, List.getElem?_append_left (by omega)]
      simp only [List.getElem?_take, h1, ↓reduceIte]
      have : ¬(off ≤ p ∧ p < off + src.length) := by omega
      simp [this]
    · rw [List.append_assoc, List.getElem?_append_right (by omega), hlt]
      by_cases h2 : p < off + src.length
      · rw [List.getElem?_append_left (by omega)]
        have : off ≤ p ∧ p < off + src.length := by omega
        simp [this]
      · rw [List.getElem?_append_right (by omega), List.getElem?_drop]
        have : ¬(off ≤ p ∧ p < off + src.length) := by omega
        simp only [this, ↓reduceIte]
        congr 1
        omega
  · simp [specPanic] at hws

/-- Writing the chunks of a *single* buffer `data` (in any order, overlapping or not) yields
a buffer that holds `data` at every covered position and is unchanged elsewhere. -/
private theorem ep1_encodeUnionChunksM_pointwise {M : Type} [Gen.Memory M]
    (data : List (Gen.AbstractByte (Gen.Memory.Provenance M))) :
    ∀ (chunks : List (Gen.Offset × Size)) (buf : List (Gen.AbstractByte (Gen.Memory.Provenance M))),
      buf.length = data.length →
      (∀ c ∈ chunks, c.1.bytes + c.2.bytes ≤ data.length) →
      ∃ out, Type.encodeUnionChunksM (M := M) chunks
          (chunks.map (fun c => (data.drop c.1.bytes).take c.2.bytes)) buf = .ok out ∧
        out.length = data.length ∧
        ∀ p, out[p]? = if ep1Covered chunks p then data[p]? else buf[p]?
  | [], buf, hbuf, _ => by
    refine ⟨buf, by unfold Type.encodeUnionChunksM; rfl, hbuf, fun p => ?_⟩
    simp [ep1Covered]
  | (off, csz) :: rest, buf, hbuf, hrange => by
    have h0 : off.bytes + csz.bytes ≤ data.length := hrange (off, csz) (List.mem_cons_self ..)
    let src := (data.drop off.bytes).take csz.bytes
    have hsrcLen : src.length = csz.bytes := by simp [src]; omega
    have hws : writeSubsliceAtIndex buf (off.bytes : Int) src =
        .ok (buf.take off.bytes ++ src ++ buf.drop (off.bytes + src.length)) := by
      unfold writeSubsliceAtIndex
      have hc : (0 : Int) ≤ (off.bytes : Int) ∧ (off.bytes : Int) + (src.length : Int) ≤
          (buf.length : Int) := by rw [hsrcLen, hbuf]; omega
      simp only [hc, and_self, ↓reduceIte, Int.toNat_natCast, pure, Except.pure]
    obtain ⟨out, hrec, houtLen, hout⟩ := ep1_encodeUnionChunksM_pointwise data rest
      (buf.take off.bytes ++ src ++ buf.drop (off.bytes + src.length))
      ((ep1_writeSubsliceAtIndex_getElem? hws 0).1.trans hbuf)
      (fun c hc => hrange c (List.mem_cons_of_mem _ hc))
    refine ⟨out, ?_, houtLen, fun p => ?_⟩
    · rw [List.map_cons]
      unfold Type.encodeUnionChunksM
      have hsl : ((data.drop off.bytes).take csz.bytes).length = csz.bytes := hsrcLen
      simp only [hsl, ne_eq, not_true_eq_false, ↓reduceIte]
      simp only [bind, Except.bind]
      rw [show writeSubsliceAtIndex buf (off.bytes : Int) ((data.drop off.bytes).take csz.bytes) =
        _ from hws]
      exact hrec
    · rw [hout p, (ep1_writeSubsliceAtIndex_getElem? hws p).2, hsrcLen]
      have hcov : ep1Covered ((off, csz) :: rest) p =
          (decide (off.bytes ≤ p ∧ p < off.bytes + csz.bytes) || ep1Covered rest p) := by
        simp [ep1Covered, List.any_cons]
      rw [hcov]
      by_cases hr : ep1Covered rest p = true
      · simp [hr]
      · have hr' : ep1Covered rest p = false := by simpa using hr
        by_cases hc : off.bytes ≤ p ∧ p < off.bytes + csz.bytes
        · have hlt : p - off.bytes < csz.bytes := by omega
          have hgoal : ((data.drop off.bytes).take csz.bytes)[p - off.bytes]? = data[p]? := by
            rw [List.getElem?_take, List.getElem?_drop]
            simp only [hlt, ↓reduceIte]
            congr 1
            omega
          have hdc : decide (off.bytes ≤ p ∧ p < off.bytes + csz.bytes) = true := decide_eq_true hc
          rw [hr', hdc]
          simp only [Bool.false_eq_true, Bool.true_or, hc, and_self, ↓reduceIte]
          exact hgoal
        · have hdc : decide (off.bytes ≤ p ∧ p < off.bytes + csz.bytes) = false := decide_eq_false hc
          rw [hr', hdc]
          simp [hc]

private theorem ep1_mapM_subslice_eq {T : Type} (data : List T) :
    ∀ (cs : List (Gen.Offset × Size)) (cd : List (List T)),
      cs.mapM (fun (c : Gen.Offset × Size) =>
        subsliceWithLength data (c.1.bytes : Int) (c.2.bytes : Int)) = .ok cd →
      cd = cs.map (fun c => (data.drop c.1.bytes).take c.2.bytes) ∧
        ∀ c ∈ cs, c.1.bytes + c.2.bytes ≤ data.length
  | [], cd, h => by
    obtain rfl := ep1_pure_ok h
    exact ⟨rfl, by simp⟩
  | c :: rest, cd, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨bs, hsub, h⟩ := ep1_bind_ok h
    obtain ⟨bsRest, hrest, h⟩ := ep1_bind_ok h
    obtain rfl := ep1_pure_ok h
    obtain ⟨ihEq, ihRange⟩ := ep1_mapM_subslice_eq data rest bsRest hrest
    unfold subsliceWithLength at hsub
    split at hsub
    · rename_i hc
      obtain rfl := ep1_pure_ok hsub
      refine ⟨by simp [ihEq], ?_⟩
      intro c' hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · omega
      · exact ihRange c' hc'
    · simp [specPanic] at hsub

/-- **`ValueExpr::Union` values survive `encode` then `decode` for every chunk layout** — the
pairwise-disjointness hypothesis of A2's `ep1_evalValueM_union_encode_total_and_disjoint_roundtrip`
is unnecessary. The chunks of a constructed union value are all subslices of one buffer, so
writing them back (`Type::encode` at `Union`, in chunk order) agrees with that buffer at every
covered byte even where chunks overlap, and `Type::decode` re-reads exactly those bytes. On
every `Memory` `M` and for every (empty, gapped, overlapping, or out-of-order) chunk list: -/
theorem ep1_evalValueM_union_decode_encode_roundtrip_any_chunks
    {M : Type} [Gen.Memory M] [MemoryOps M]
    (m m1 : Gen.Machine M) (field : Int) (expr : Gen.ValueExpr)
    (fields : List (Gen.Offset × Gen.Type)) (chunks : List (Gen.Offset × Size))
    (sz : Size) (al : Align) (v : Gen.Value M) (ty : Gen.Type)
    (h : evalValueM m (.Union field expr (.Union fields chunks sz al)) = .ok ((v, ty), m1)) :
    ty = .Union fields chunks sz al ∧
    ∃ bs, Type.encodeM ty v = .ok bs ∧ bs.length = sz.bytes ∧
      Type.decodeM (M := M) ty bs = .ok (some v) := by
  rw [ep1_evalValueM_union_complete_spec] at h
  obtain ⟨⟨off, exprTy⟩, _, h⟩ := ep1_bind_ok h
  obtain ⟨⟨⟨val, _⟩, _⟩, _, h⟩ := ep1_bind_ok h
  obtain ⟨encoded, _, h⟩ := ep1_bind_ok h
  obtain ⟨data, hws, h⟩ := ep1_bind_ok h
  obtain ⟨chunkData, hmap, hp⟩ := ep1_bind_ok h
  obtain ⟨hvt, _⟩ := Prod.mk.inj (ep1_pure_ok hp)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hvt
  have hdataLen : data.length = sz.bytes := by
    rw [writeSubsliceAtIndex_length hws, List.length_replicate]
  obtain ⟨rfl, hrange⟩ := ep1_mapM_subslice_eq data chunks chunkData hmap
  obtain ⟨out, henc, houtLen, hout⟩ := ep1_encodeUnionChunksM_pointwise data chunks
    (List.replicate sz.bytes .Uninit) (by simp [hdataLen]) hrange
  refine ⟨rfl, out, ?_, houtLen.trans hdataLen, ?_⟩
  · unfold Type.encodeM
    simp only [List.length_map, ne_eq, not_true_eq_false, ↓reduceIte]
    exact henc
  · unfold Type.decodeM
    simp only [houtLen, hdataLen, ne_eq, not_true_eq_false, ↓reduceIte]
    have hsame : ∀ c ∈ chunks, (out.drop c.1.bytes).take c.2.bytes =
        (data.drop c.1.bytes).take c.2.bytes := by
      intro c hc
      apply List.ext_getElem?
      intro i
      simp only [List.getElem?_take, List.getElem?_drop]
      by_cases hi : i < c.2.bytes
      · simp only [hi, ↓reduceIte]
        rw [hout]
        have hcov : ep1Covered chunks (c.1.bytes + i) = true := by
          simp only [ep1Covered, List.any_eq_true, decide_eq_true_eq]
          exact ⟨c, hc, by omega, by omega⟩
        simp [hcov]
      · simp [hi]
    have hmapOut : chunks.mapM (fun (x : Gen.Offset × Size) =>
        subsliceWithLength out (x.1.bytes : Int) (x.2.bytes : Int)) =
        .ok (chunks.map (fun c => (data.drop c.1.bytes).take c.2.bytes)) := by
      have key : ∀ cs : List (Gen.Offset × Size), (∀ c ∈ cs, c ∈ chunks) →
          cs.mapM (fun (x : Gen.Offset × Size) =>
            subsliceWithLength out (x.1.bytes : Int) (x.2.bytes : Int)) =
          .ok (cs.map (fun c => (data.drop c.1.bytes).take c.2.bytes)) := by
        intro cs
        induction cs with
        | nil => intro _; rfl
        | cons c rest ih =>
          intro hsub
          have hc := hsub c (List.mem_cons_self ..)
          have hr := hrange c hc
          have hsl : subsliceWithLength out (c.1.bytes : Int) (c.2.bytes : Int) =
              .ok ((data.drop c.1.bytes).take c.2.bytes) := by
            unfold subsliceWithLength
            have hcond : (0 : Int) ≤ (c.1.bytes : Int) ∧ (0 : Int) ≤ (c.2.bytes : Int) ∧
                (c.1.bytes : Int) + (c.2.bytes : Int) ≤ (out.length : Int) := by
              rw [houtLen]; omega
            simp only [hcond, and_self, ↓reduceIte, Int.toNat_natCast, pure, Except.pure,
              hsame c hc]
          simp only [List.mapM_cons, hsl, ih (fun c' hc' => hsub c' (List.mem_cons_of_mem _ hc')),
            List.map_cons, bind, Except.bind, pure, Except.pure]
      exact key chunks (fun _ h => h)
    simp only [hmapOut, bind, Except.bind, pure, Except.pure]

/-- **Overlapping-chunk union witness** (outside A2's disjointness hypothesis): a 4-byte union
with *overlapping* chunks `[(0, 3), (1, 3)]` and a `u32` field. Constructing it with
`0x04030201`, encoding the value, and decoding again returns the very same value, on both
`Mach` and `MachTB`; and an `Assign` + `Load` of the union through a local round-trips it. -/
theorem ep1_union_overlapping_chunks_roundtrip_witness :
    let overlapUnionTy : Gen.Type :=
      .Union [(⟨0⟩, .Int ep1U32)] [(⟨0⟩, ⟨3⟩), (⟨1⟩, ⟨3⟩)] ⟨4⟩ ⟨4⟩
    let uexpr : Gen.ValueExpr := .Union 0 (.Constant (.Int 0x04030201) (.Int ep1U32)) overlapUnionTy
    let uval : Val := .Union [[.Init 1 none, .Init 2 none, .Init 3 none],
                              [.Init 2 none, .Init 3 none, .Init 4 none]]
    let uvalTB : Gen.Value TBM := .Union [[.Init 1 none, .Init 2 none, .Init 3 none],
                                          [.Init 2 none, .Init 3 none, .Init 4 none]]
    let mBM := ep1MachBM
      [{ data := List.replicate 4 .Uninit, addr := 0x100, align := ⟨4⟩, kind := .Stack,
         live := true, extra := () }]
      [(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, ())⟩)]
      [(⟨⟨0⟩⟩, overlapUnionTy)]
    let mTB := liftMachToTB mBM
    ¬ ep1ChunksDisjoint [((⟨0⟩ : Gen.Offset), (⟨3⟩ : Size)), (⟨1⟩, ⟨3⟩)] ∧
    evalValue mBM uexpr = .ok ((uval, overlapUnionTy), mBM) ∧
    evalValueM mTB uexpr = .ok ((uvalTB, overlapUnionTy), mTB) ∧
    (Type.encode overlapUnionTy uval >>= Type.decode overlapUnionTy) = .ok (some uval) ∧
    (Type.encodeM overlapUnionTy uvalTB >>= Type.decodeM (M := TBM) overlapUnionTy) =
      .ok (some uvalTB) ∧
    (∃ m1 m2, evalStatement mBM (.Assign (.Local ⟨⟨0⟩⟩) uexpr) = .ok m1 ∧
      evalValue m1 (.Load (.Local ⟨⟨0⟩⟩)) = .ok ((uval, overlapUnionTy), m2)) ∧
    (∃ m1 m2, evalStatementM mTB (.Assign (.Local ⟨⟨0⟩⟩) uexpr) = .ok m1 ∧
      evalValueM m1 (.Load (.Local ⟨⟨0⟩⟩)) = .ok ((uvalTB, overlapUnionTy), m2)) := by
  intro overlapUnionTy uexpr uval uvalTB mBM mTB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [ep1ChunksDisjoint]
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · have hseq : (do
        let m1 ← evalStatement mBM (.Assign (.Local ⟨⟨0⟩⟩) uexpr)
        let (r, _) ← evalValue m1 (.Load (.Local ⟨⟨0⟩⟩))
        pure r) = .ok (uval, overlapUnionTy) := by ep1_kernel_rfl
    obtain ⟨m1, hm1, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨⟨r, m2⟩, hm2, hret⟩ := ep1_bind_ok hseq
    obtain rfl := ep1_pure_ok hret
    exact ⟨m1, m2, hm1, hm2⟩
  · have hseq : (do
        let m1 ← evalStatementM mTB (.Assign (.Local ⟨⟨0⟩⟩) uexpr)
        let (r, _) ← evalValueM m1 (.Load (.Local ⟨⟨0⟩⟩))
        pure r) = .ok (uvalTB, overlapUnionTy) := by ep1_kernel_rfl
    obtain ⟨m1, hm1, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨⟨r, m2⟩, hm2, hret⟩ := ep1_bind_ok hseq
    obtain rfl := ep1_pure_ok hret
    exact ⟨m1, m2, hm1, hm2⟩

/-! ### `[adv A3]` `Ep1PlaceChain` frame/shape laws, multi-tag `SetDiscriminant → GetDiscriminant` & `Assign (Variant) → GetDiscriminant` (no `hp1`!), and `Type.Union` Galois law + sharp witnesses -/

/-- Allocation shape (`(data.length, addr, live)`) governing `check_ptr` and `ptr_offset_inbounds`. -/
def ep1AllocShape {E A : Type} (allocs : List (Gen.Allocation E A)) : List (Nat × Int × Bool) :=
  allocs.map (fun a => (a.data.length, a.addr, a.live))

/-- Current stack frame's `(func, locals)` view (ignoring memory-model `extra` such as Tree Borrows
protectors). -/
def ep1CurFrameViewM {M : Type} [Gen.Memory M] (m : Gen.Machine M) :
    Interp (Gen.Function × Map Gen.LocalName (Gen.ThinPointer (Gen.Memory.Provenance M))) := do
  let fr ← curFrameM m
  pure (fr.func, fr.locals)

private theorem ep1_evalPlaceM_chain_thin_and_readonly {M : Type} [Gen.Memory M] [MemoryOps M]
    (place : Gen.PlaceExpr) (hc : Ep1PlaceChain place) :
    ∀ (m m1 : Gen.Machine M) (rp : Gen.Place M) (ty : Gen.Type),
      evalPlaceM m place = .ok ((rp, ty), m1) → m1 = m ∧ rp.ptr.metadata = none := by
  induction hc with
  | Local name =>
    intro m m1 rp ty h
    unfold evalPlaceM at h
    obtain ⟨fr, _, h⟩ := ep1_bind_ok h
    obtain ⟨ty', _, h⟩ := ep1_bind_ok h
    cases hloc : mapGet fr.locals name with
    | none => simp [hloc, ub] at h
    | some p =>
      simp only [hloc] at h
      obtain ⟨h1, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
      obtain ⟨rfl, _⟩ := Prod.mk.inj h1
      exact ⟨rfl, rfl⟩
  | Field root field hroot ih =>
    intro m m1 rp ty h
    unfold evalPlaceM at h
    obtain ⟨⟨⟨rp0, ty0⟩, m0⟩, hr0, h⟩ := ep1_bind_ok h
    obtain ⟨rfl, hmeta0⟩ := ih m m0 rp0 ty0 hr0
    have hfin : ∀ (off : Gen.Offset) (fty : Gen.Type),
        (do
          let rootSize ← computeSizeM m0 (← Type.layout ty0) rp0.ptr.metadata
          if !(off.bytes ≤ rootSize.bytes) then
            specPanic "assertion failed: offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata)"
          else do
            let ptr ← ptrOffsetInboundsM m0 rp0.ptr.thin_pointer (off.bytes : Int)
            let ptr := if !LayoutStrategy.is_sized (← Type.layout fty) then
                ThinPointer.widen ptr rp0.ptr.metadata
              else
                ThinPointer.widen ptr none
            pure (({ rp0 with ptr := ptr }, fty), m0)) = .ok ((rp, ty), m1) →
        m1 = m0 ∧ rp.ptr.metadata = none := by
      intro off fty ht
      obtain ⟨lay0, _, ht⟩ := ep1_bind_ok ht
      obtain ⟨rsz, _, ht⟩ := ep1_bind_ok ht
      split at ht
      · simp [specPanic] at ht
      · obtain ⟨ptr', _, ht⟩ := ep1_bind_ok ht
        obtain ⟨flay, _, ht⟩ := ep1_bind_ok ht
        obtain ⟨h1, rfl⟩ := Prod.mk.inj (ep1_pure_ok ht)
        obtain ⟨rfl, _⟩ := Prod.mk.inj h1
        refine ⟨rfl, ?_⟩
        split <;> simp [ThinPointer.widen, hmeta0]
    dsimp only [bind, Except.bind] at h
    cases ty0 with
    | Tuple sf sh uf =>
      dsimp only at h
      split at h
      · obtain ⟨⟨off, fty⟩, _, ht⟩ := ep1_bind_ok h
        exact hfin off fty ht
      · split at h
        · cases uf with
          | none => simp [specPanic] at h
          | some tailTy =>
            obtain ⟨tlay, _, h⟩ := ep1_bind_ok h
            obtain ⟨tal, _, ht⟩ := ep1_bind_ok h
            exact hfin (TupleHeadLayout.tail_offset sh tal) tailTy ht
        · simp [specPanic] at h
    | Union fields _ _ _ =>
      obtain ⟨⟨off, fty⟩, _, ht⟩ := ep1_bind_ok h
      exact hfin off fty ht
    | _ => simp [specPanic] at h
  | Downcast root d hroot ih =>
    intro m m1 rp ty h
    unfold evalPlaceM at h
    obtain ⟨⟨⟨rp0, ty0⟩, m0⟩, hr0, h⟩ := ep1_bind_ok h
    obtain ⟨rfl, hmeta0⟩ := ih m m0 rp0 ty0 hr0
    dsimp only [bind, Except.bind] at h
    cases ty0 with
    | Enum variants _ _ _ _ =>
      obtain ⟨var, _, h⟩ := ep1_bind_ok h
      obtain ⟨h1, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
      obtain ⟨rfl, _⟩ := Prod.mk.inj h1
      exact ⟨rfl, hmeta0⟩
    | _ => simp [specPanic] at h

private theorem ep1_ptrOffsetInboundsM_same_shape_tb {m1 m2 : MachTB}
    (hshape : ep1AllocShape m2.mem.memory.mem.allocations = ep1AllocShape m1.mem.memory.mem.allocations)
    (p : Gen.ThinPointer Gen.TreeBorrowsProvenance) (off : Int) :
    ptrOffsetInboundsM m2 p off = ptrOffsetInboundsM m1 p off := by
  unfold ptrOffsetInboundsM
  have hsd : ConcurrentMemory.signed_dereferenceable m2.mem p off =
      ConcurrentMemory.signed_dereferenceable m1.mem p off := by
    change TreeBorrowsMemory.signed_dereferenceable m2.mem.memory p off =
      TreeBorrowsMemory.signed_dereferenceable m1.mem.memory p off
    unfold TreeBorrowsMemory.signed_dereferenceable TreeBorrowsMemory.dereferenceable
    by_cases hpos : off > 0
    · simp only [hpos, ↓reduceIte]
      rw [ep1_check_ptr_same_shape m1.mem.memory.mem m2.mem.memory.mem hshape.symm]
    · simp only [hpos, ↓reduceIte]
      rw [ep1_check_ptr_same_shape m1.mem.memory.mem m2.mem.memory.mem hshape.symm]
  rw [hsd]

private theorem ep1_BM_check_ptr_eq_BasicMemory (bm : BM) (p : Ptr) (len : Size) :
    BM.check_ptr bm p len = BasicMemory.check_ptr bm p len := by
  unfold BM.check_ptr BasicMemory.check_ptr
  by_cases hz : len.bytes = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte]
    cases p.provenance <;> rfl

private theorem ep1_ptrOffsetInbounds_same_shape_bm {m1 m2 : Mach}
    (hshape : ep1AllocShape m2.mem.memory.allocations = ep1AllocShape m1.mem.memory.allocations)
    (p : Ptr) (off : Int) :
    ptrOffsetInbounds m2 p off = ptrOffsetInbounds m1 p off := by
  rw [← ep1_ptrOffsetInboundsM_bm_eq, ← ep1_ptrOffsetInboundsM_bm_eq]
  unfold ptrOffsetInboundsM
  have hsd : ConcurrentMemory.signed_dereferenceable (M := BM) m2.mem p off =
      ConcurrentMemory.signed_dereferenceable (M := BM) m1.mem p off := by
    change BM.signed_dereferenceable m2.mem.memory p off = BM.signed_dereferenceable m1.mem.memory p off
    unfold BM.signed_dereferenceable BM.dereferenceable
    by_cases hpos : off > 0
    · simp only [hpos, ↓reduceIte, ep1_BM_check_ptr_eq_BasicMemory]
      rw [ep1_check_ptr_same_shape m1.mem.memory m2.mem.memory hshape.symm]
    · simp only [hpos, ↓reduceIte, ep1_BM_check_ptr_eq_BasicMemory]
      rw [ep1_check_ptr_same_shape m1.mem.memory m2.mem.memory hshape.symm]
  rw [hsd]

/-- **`Ep1PlaceChain` frame law under allocation-shape & frame preservation (both `MachTB` and `Mach`):**
for any structural place chain (`Local` / `Field` / `Downcast`), evaluating `place` on two machines
that agree on `ep1CurFrameViewM` and `ep1AllocShape` yields the **exact same place/type or error**
(with the target machine unchanged). -/
theorem ep1_evalPlaceM_chain_same_shape (place : Gen.PlaceExpr) (hc : Ep1PlaceChain place) :
    (∀ (m1 m2 : MachTB),
      ep1CurFrameViewM m2 = ep1CurFrameViewM m1 →
      ep1AllocShape m2.mem.memory.mem.allocations = ep1AllocShape m1.mem.memory.mem.allocations →
      evalPlaceM m2 place =
        (match evalPlaceM m1 place with
         | .ok (r, _) => .ok (r, m2)
         | .error e => .error e)) ∧
    (∀ (m1 m2 : Mach),
      ep1CurFrameViewM (M := BM) m2 = ep1CurFrameViewM (M := BM) m1 →
      ep1AllocShape m2.mem.memory.allocations = ep1AllocShape m1.mem.memory.allocations →
      evalPlace m2 place =
        (match evalPlace m1 place with
         | .ok (r, _) => .ok (r, m2)
         | .error e => .error e)) := by
  have hpoly : ∀ {M : Type} [Gen.Memory M] [MemoryOps M] (m1 m2 : Gen.Machine M),
      ep1CurFrameViewM m2 = ep1CurFrameViewM m1 →
      (∀ p off, ptrOffsetInboundsM m2 p off = ptrOffsetInboundsM m1 p off) →
      evalPlaceM m2 place =
        (match evalPlaceM m1 place with
         | .ok (r, _) => .ok (r, m2)
         | .error e => .error e) := by
    intro M _ _ m1 m2 hfr hpoi
    induction hc with
    | Local name =>
      unfold evalPlaceM
      unfold ep1CurFrameViewM at hfr
      cases hc1 : curFrameM m1 with
      | error e =>
        cases hc2 : curFrameM m2 with
        | error e2 =>
          simp only [hc1, hc2, bind, Except.bind] at hfr ⊢
          exact congrArg Except.error (Except.error.inj hfr)
        | ok fr2 =>
          simp [hc1, hc2, bind, Except.bind, pure, Except.pure] at hfr
      | ok fr1 =>
        cases hc2 : curFrameM m2 with
        | error e2 =>
          simp [hc1, hc2, bind, Except.bind, pure, Except.pure] at hfr
        | ok fr2 =>
          simp only [hc1, hc2, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfr
          obtain ⟨hfunc, hlocs⟩ := hfr
          simp only [bind, Except.bind, hfunc, hlocs]
          cases mapIndex fr1.func.locals name "self.cur_frame().func.locals[name]" with
          | error e => rfl
          | ok ty =>
            cases mapGet fr1.locals name with
            | none => rfl
            | some p => rfl
    | Downcast root d hroot ih =>
      unfold evalPlaceM
      rw [ih]
      cases hr : evalPlaceM m1 root with
      | error e => rfl
      | ok res =>
        obtain ⟨⟨rp, ty⟩, m1'⟩ := res
        obtain ⟨rfl, _⟩ := ep1_evalPlaceM_chain_thin_and_readonly root hroot m1 m1' rp ty hr
        dsimp only [bind, Except.bind]
        cases ty with
        | Enum variants _ _ _ _ =>
          dsimp only
          cases mapIndex variants d "variants[discriminant]" <;> simp [pure, Except.pure]
        | _ => dsimp only; rfl
    | Field root field hroot ih =>
      unfold evalPlaceM
      rw [ih]
      cases hr : evalPlaceM m1 root with
      | error e => rfl
      | ok res =>
        obtain ⟨⟨rp, ty⟩, m1'⟩ := res
        obtain ⟨rfl, hmeta⟩ := ep1_evalPlaceM_chain_thin_and_readonly root hroot m1 m1' rp ty hr
        dsimp only [bind, Except.bind]
        have hcs : ∀ lay, computeSizeM m2 lay none = computeSizeM m1' lay none := fun lay => by
          unfold computeSizeM; rw [ep1_compute_size_and_align_none_indep _ _ lay]
        have hca : ∀ lay, computeAlignM m2 lay none = computeAlignM m1' lay none := fun lay => by
          unfold computeAlignM; rw [ep1_compute_size_and_align_none_indep _ _ lay]
        have htail : ∀ (off : Gen.Offset) (fty : Gen.Type),
            (do
              let rootSize ← computeSizeM m2 (← Type.layout ty) rp.ptr.metadata
              if !(off.bytes ≤ rootSize.bytes) then
                specPanic "assertion failed: offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata)"
              else do
                let ptr ← ptrOffsetInboundsM m2 rp.ptr.thin_pointer (off.bytes : Int)
                let ptr := if !LayoutStrategy.is_sized (← Type.layout fty) then
                    ThinPointer.widen ptr rp.ptr.metadata
                  else
                    ThinPointer.widen ptr none
                pure (({ rp with ptr := ptr }, fty), m2)) =
            (match (do
              let rootSize ← computeSizeM m1' (← Type.layout ty) rp.ptr.metadata
              if !(off.bytes ≤ rootSize.bytes) then
                specPanic "assertion failed: offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata)"
              else do
                let ptr ← ptrOffsetInboundsM m1' rp.ptr.thin_pointer (off.bytes : Int)
                let ptr := if !LayoutStrategy.is_sized (← Type.layout fty) then
                    ThinPointer.widen ptr rp.ptr.metadata
                  else
                    ThinPointer.widen ptr none
                pure (({ rp with ptr := ptr }, fty), m1')) with
             | .ok (r, _) => .ok (r, m2)
             | .error e => .error e) := by
          intro off fty
          cases Type.layout ty with
          | error e => rfl
          | ok lay =>
            simp only [bind, Except.bind, hmeta, hcs lay]
            cases computeSizeM m1' lay none with
            | error e => rfl
            | ok rsz =>
              dsimp only
              by_cases hle : (!decide (off.bytes ≤ rsz.bytes)) = true
              · simp only [hle, ↓reduceIte, specPanic]
              · simp only [hle, hpoi]
                cases ptrOffsetInboundsM m1' rp.ptr.thin_pointer (off.bytes : Int) with
                | error e => rfl
                | ok p' =>
                  cases Type.layout fty with
                  | error e => rfl
                  | ok flay => rfl
        cases ty with
        | Tuple sf sh uf =>
          dsimp only
          by_cases hc1 : 0 ≤ field ∧ field < (sf.length : Int)
          · simp only [hc1, and_self, ↓reduceIte]
            cases listIndex sf field "sized_fields[field]" with
            | error e => rfl
            | ok oft => exact htail oft.1 oft.2
          · simp only [hc1, ↓reduceIte]
            by_cases hc2 : field = (sf.length : Int)
            · simp only [hc2, ↓reduceIte]
              cases uf with
              | none => rfl
              | some tailTy =>
                dsimp only
                cases Type.layout tailTy with
                | error e => rfl
                | ok tlay =>
                  have hca' : computeAlignM m2 tlay rp.ptr.metadata = computeAlignM m1' tlay rp.ptr.metadata := by
                    rw [hmeta]; exact hca tlay
                  dsimp only
                  rw [hca']
                  cases computeAlignM m1' tlay rp.ptr.metadata with
                  | error e => rfl
                  | ok tal =>
                    dsimp only [pure, Except.pure]
                    exact htail (TupleHeadLayout.tail_offset sh tal) tailTy
            · simp only [hc2, ↓reduceIte]; rfl
        | Union fields _ _ _ =>
          dsimp only
          cases listIndex fields field "fields[field]" with
          | error e => rfl
          | ok oft => exact htail oft.1 oft.2
        | _ => dsimp only; rfl
  refine ⟨fun m1 m2 hfr hsh => ?_, fun m1 m2 hfr hsh => ?_⟩
  · rw [hpoly m1 m2 hfr (ep1_ptrOffsetInboundsM_same_shape_tb hsh)]
    cases evalPlaceM m1 place <;> rfl
  · rw [← evalPlaceM_bm_eq, ← evalPlaceM_bm_eq]
    rw [hpoly (M := BM) m1 m2 hfr (fun p off => by
      rw [ep1_ptrOffsetInboundsM_bm_eq, ep1_ptrOffsetInboundsM_bm_eq]
      exact ep1_ptrOffsetInbounds_same_shape_bm hsh p off)]
    cases evalPlaceM (M := BM) m1 place <;> rfl

private theorem ep1_BasicMemory_load_shape {E A : Type}
    {mem mem' : Gen.BasicMemory Gen.x86_64 E A}
    {ptr : Gen.ThinPointer (Gen.Provenance E)} {len : Size} {align : Align}
    {handle : A → E → Gen.Offset → Interp A} {bs : List (Gen.AbstractByte (Gen.Provenance E))}
    (h : BasicMemory.load mem ptr len align handle = .ok (bs, mem')) :
    ep1AllocShape mem'.allocations = ep1AllocShape mem.allocations := by
  unfold BasicMemory.load at h
  split at h
  · simp [ub] at h
  · obtain ⟨chk, _, h⟩ := ep1_bind_ok h
    cases chk with
    | none =>
      obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h); rfl
    | some trip =>
      rcases trip with ⟨id, pe, off⟩
      obtain ⟨alloc, hidx, h⟩ := ep1_bind_ok h
      obtain ⟨extra', _, h⟩ := ep1_bind_ok h
      obtain ⟨allocs', hset, h⟩ := ep1_bind_ok h
      obtain ⟨_, _, h⟩ := ep1_bind_ok h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
      obtain ⟨_, hi, hget⟩ := ep1_listIndex_int_eq_getElem hidx
      have hallocs : allocs' = mem.allocations.set id._0.toNat { alloc with extra := extra' } := by
        unfold listSet at hset
        split at hset
        · exact (ep1_pure_ok hset).symm
        · simp [specPanic] at hset
      subst hallocs
      unfold ep1AllocShape
      rw [List.map_set]
      have hsame : (alloc.data.length, alloc.addr, alloc.live) =
          (mem.allocations.map (fun a => (a.data.length, a.addr, a.live)))[id._0.toNat]'(by simpa using hi) := by
        simp only [List.getElem_map, hget]
      exact (congrArg (fun v => (mem.allocations.map _).set id._0.toNat v) hsame).trans
        (List.set_getElem_self (by simpa using hi))

private theorem ep1_retag_ptr_shape_tb {tbm tbm' : TBM} {fe fe' : Gen.TreeBorrowsFrameExtra}
    {ptr ptr' : Gen.Pointer Gen.TreeBorrowsProvenance} {ptrTy : Gen.PtrType}
    {b1 b2 : Bool} {vt : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable}
    (h : TreeBorrowsMemory.retag_ptr tbm fe ptr ptrTy b1 b2 vt = .ok (ptr', tbm', fe')) :
    ep1AllocShape tbm'.mem.allocations = ep1AllocShape tbm.mem.allocations := by
  unfold TreeBorrowsMemory.retag_ptr at h
  obtain ⟨opt, _, h⟩ := ep1_bind_ok h
  cases opt with
  | none =>
    obtain ⟨_, h2⟩ := Prod.mk.inj (ep1_pure_ok h)
    obtain ⟨rfl, _⟩ := Prod.mk.inj h2
    rfl
  | some perms =>
    obtain ⟨⟨thin', tbm1, fe1⟩, hreb, h⟩ := ep1_bind_ok h
    obtain ⟨_, h2⟩ := Prod.mk.inj (ep1_pure_ok h)
    obtain ⟨rfl, _⟩ := Prod.mk.inj h2
    unfold TreeBorrowsMemory.reborrow at hreb
    obtain ⟨_, _, hreb⟩ := ep1_bind_ok hreb
    cases hpr : ptr.thin_pointer.provenance with
    | none =>
      simp only [hpr] at hreb
      split at hreb
      · simp [specPanic] at hreb
      · obtain ⟨_, h2⟩ := Prod.mk.inj (ep1_pure_ok hreb)
        obtain ⟨rfl, _⟩ := Prod.mk.inj h2
        rfl
    | some ip =>
      rcases ip with ⟨id, parentPath⟩
      simp only [hpr] at hreb
      obtain ⟨⟨childPath, allocs'⟩, hmut, hreb⟩ := ep1_bind_ok hreb
      obtain ⟨_, h2⟩ := Prod.mk.inj (ep1_pure_ok hreb)
      obtain ⟨rfl, _⟩ := Prod.mk.inj h2
      unfold listMutateAt at hmut
      obtain ⟨alloc, hidx, hmut⟩ := ep1_bind_ok hmut
      obtain ⟨⟨cp, alloc'⟩, hfn, hmut⟩ := ep1_bind_ok hmut
      obtain ⟨allocs'', hset, hmut⟩ := ep1_bind_ok hmut
      obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hmut)
      obtain ⟨_, hi, hget⟩ := ep1_listIndex_int_eq_getElem hidx
      have hallocEq : alloc'.data.length = alloc.data.length ∧
          alloc'.addr = alloc.addr ∧ alloc'.live = alloc.live := by
        dsimp only at hfn
        cases hsz : Size.from_bytes (ptr.thin_pointer.addr - alloc.addr) with
        | none => simp [hsz, specPanic] at hfn
        | some off0 =>
          simp only [hsz] at hfn
          obtain ⟨_, _, hfn⟩ := ep1_bind_ok hfn
          split at hfn
          · obtain ⟨_, _, hfn⟩ := ep1_bind_ok hfn
            split at hfn
            · simp [specPanic] at hfn
            · obtain ⟨⟨_, _⟩, _, hfn⟩ := ep1_bind_ok hfn
              obtain ⟨_, _, hfn⟩ := ep1_bind_ok hfn
              obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hfn)
              exact ⟨rfl, rfl, rfl⟩
          · dsimp only [pure, Except.pure, bind, Except.bind] at hfn
            split at hfn
            · simp [specPanic] at hfn
            · obtain ⟨⟨_, _⟩, _, hfn⟩ := ep1_bind_ok hfn
              obtain ⟨_, _, hfn⟩ := ep1_bind_ok hfn
              obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hfn)
              exact ⟨rfl, rfl, rfl⟩
      have hallocs : allocs'' = tbm.mem.allocations.set id._0.toNat alloc' := by
        unfold listSet at hset
        split at hset
        · exact (ep1_pure_ok hset).symm
        · simp [specPanic] at hset
      subst hallocs
      show ep1AllocShape (tbm.mem.allocations.set id._0.toNat alloc') = _
      unfold ep1AllocShape
      rw [List.map_set]
      have hsame : (alloc'.data.length, alloc'.addr, alloc'.live) =
          (tbm.mem.allocations.map (fun a => (a.data.length, a.addr, a.live)))[id._0.toNat]'(by simpa using hi) := by
        simp only [List.getElem_map, hget, hallocEq.1, hallocEq.2.1, hallocEq.2.2]
      exact (congrArg (fun v => (tbm.mem.allocations.map _).set id._0.toNat v) hsame).trans
        (List.set_getElem_self (by simpa using hi))

private theorem ep1_mutateCurFrameOutM_preserves_curFrameView {M : Type} {α : Type} [Gen.Memory M]
    {m m' : Gen.Machine M} {out : α}
    {f : Gen.StackFrame M → Gen.ConcurrentMemory M → Interp (α × Gen.StackFrame M × Gen.ConcurrentMemory M)}
    (hf : ∀ fr cm a fr' cm', f fr cm = .ok (a, fr', cm') → fr'.func = fr.func ∧ fr'.locals = fr.locals)
    (h : mutateCurFrameOutM m f = .ok (out, m')) :
    ep1CurFrameViewM m' = ep1CurFrameViewM m := by
  unfold mutateCurFrameOutM at h
  obtain ⟨t, hidx, h⟩ := ep1_bind_ok h
  cases hlast : t.stack.getLast? with
  | none => simp [hlast, specPanic] at h
  | some fr =>
    simp only [hlast] at h
    obtain ⟨⟨a, fr', cm'⟩, hfr, h⟩ := ep1_bind_ok h
    obtain ⟨hfunc, hlocs⟩ := hf fr m.mem a fr' cm' hfr
    obtain ⟨threads', hset, h⟩ := ep1_bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
    obtain ⟨hidNN, hidLt, hgetT⟩ := ep1_listIndex_int_eq_getElem hidx
    have hthreads : threads' = m.threads.set m.active_thread.toNat
        { t with stack := t.stack.dropLast ++ [fr'] } := by
      unfold listSet at hset
      split at hset
      · exact (ep1_pure_ok hset).symm
      · simp [specPanic] at hset
    subst hthreads
    unfold ep1CurFrameViewM curFrameM activeThreadM
    have hidxM : listIndex m.threads m.active_thread "self.threads[self.active_thread]" = .ok t := by
      rw [ep1_listIndex_int_of_getElem _ hidNN hidLt, hgetT]
    have hidLt' : m.active_thread.toNat <
        (m.threads.set m.active_thread.toNat { t with stack := t.stack.dropLast ++ [fr'] }).length := by
      simpa [List.length_set] using hidLt
    have hidxM' : listIndex (m.threads.set m.active_thread.toNat { t with stack := t.stack.dropLast ++ [fr'] })
        m.active_thread "self.threads[self.active_thread]" =
        .ok { t with stack := t.stack.dropLast ++ [fr'] } := by
      rw [ep1_listIndex_int_of_getElem _ hidNN hidLt', List.getElem_set_self]
    simp only [hidxM, hidxM', hlast, List.getLast?_concat, hfunc, hlocs, bind, Except.bind, pure, Except.pure]

mutual

private theorem ep1_evalPlaceM_preserves_shape_tb :
    ∀ (p : Gen.PlaceExpr) (m m' : MachTB) (r : Gen.Place TBM × Gen.Type),
      evalPlaceM m p = .ok (r, m') →
      ep1CurFrameViewM m' = ep1CurFrameViewM m ∧
      ep1AllocShape m'.mem.memory.mem.allocations = ep1AllocShape m.mem.memory.mem.allocations
  | .Local _, m, m', _, h => by
    obtain ⟨rfl, _⟩ := ep1_evalPlaceM_chain_thin_and_readonly _ (.Local _) m m' _ _ h
    exact ⟨rfl, rfl⟩
  | .Field root _, m, m', r, h => by
    unfold evalPlaceM at h
    obtain ⟨⟨⟨rp0, ty0⟩, m0⟩, hr0, h⟩ := ep1_bind_ok h
    obtain ⟨hf0, hs0⟩ := ep1_evalPlaceM_preserves_shape_tb root m m0 (rp0, ty0) hr0
    have hmEq : m' = m0 := by
      have hfin : ∀ (off : Gen.Offset) (fty : Gen.Type),
          (do
            let rootSize ← computeSizeM m0 (← Type.layout ty0) rp0.ptr.metadata
            if !(off.bytes ≤ rootSize.bytes) then
              specPanic "assertion failed: offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata)"
            else do
              let ptr ← ptrOffsetInboundsM m0 rp0.ptr.thin_pointer (off.bytes : Int)
              let ptr := if !LayoutStrategy.is_sized (← Type.layout fty) then
                  ThinPointer.widen ptr rp0.ptr.metadata
                else
                  ThinPointer.widen ptr none
              pure (({ rp0 with ptr := ptr }, fty), m0)) = .ok (r, m') → m' = m0 := by
        intro off fty ht
        obtain ⟨_, _, ht⟩ := ep1_bind_ok ht
        obtain ⟨_, _, ht⟩ := ep1_bind_ok ht
        split at ht
        · simp [specPanic] at ht
        · obtain ⟨_, _, ht⟩ := ep1_bind_ok ht
          obtain ⟨_, _, ht⟩ := ep1_bind_ok ht
          exact (Prod.mk.inj (ep1_pure_ok ht)).2.symm
      dsimp only [bind, Except.bind] at h
      cases ty0 with
      | Tuple sf sh uf =>
        dsimp only at h
        split at h
        · obtain ⟨⟨off, fty⟩, _, ht⟩ := ep1_bind_ok h; exact hfin off fty ht
        · split at h
          · cases uf with
            | none => simp [specPanic] at h
            | some tailTy =>
              obtain ⟨_, _, h⟩ := ep1_bind_ok h
              obtain ⟨tal, _, ht⟩ := ep1_bind_ok h
              exact hfin (TupleHeadLayout.tail_offset sh tal) tailTy ht
          · simp [specPanic] at h
      | Union fields _ _ _ =>
        obtain ⟨⟨off, fty⟩, _, ht⟩ := ep1_bind_ok h; exact hfin off fty ht
      | _ => simp [specPanic] at h
    subst hmEq; exact ⟨hf0, hs0⟩
  | .Index root idx, m, m', r, h => by
    unfold evalPlaceM at h
    obtain ⟨⟨r0, m0⟩, hr0, h⟩ := ep1_bind_ok h
    obtain ⟨⟨rv, m1⟩, hv1, h⟩ := ep1_bind_ok h
    obtain ⟨hf0, hs0⟩ := ep1_evalPlaceM_preserves_shape_tb root m m0 r0 hr0
    obtain ⟨hf1, hs1⟩ := ep1_evalValueM_preserves_shape_tb idx m0 m1 rv hv1
    have hmEq : m' = m1 := by
      rcases r0 with ⟨rp0, ty0⟩
      rcases rv with ⟨idxVal, idxTy⟩
      dsimp only [bind, Except.bind] at h
      cases idxVal with
      | Int i =>
        dsimp only [pure, Except.pure] at h
        have hidxFin : ∀ (tyI elemTy : Gen.Type) (count : Int)
            (pm : Option (Gen.PointerMeta (Gen.Memory.Provenance TBM))),
            (if i < 0 ∨ i ≥ count then ub "access to out-of-bounds index"
             else do
               let elemLayout ← Type.layout elemTy
               let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array & slice elements are sized"
               let offset ← Size.mulInt elemSize i
               let rootSize ← computeSizeM m1 (← Type.layout tyI) pm
               if offset.bytes ≤ rootSize.bytes then
                 let ptr ← ptrOffsetInboundsM m1 rp0.ptr.thin_pointer (offset.bytes : Int)
                 pure (({ rp0 with ptr := ThinPointer.widen ptr none }, elemTy), m1)
               else
                 specPanic "sanity check: the indexed offset should not be outside what the type allows.") =
              .ok (r, m') → m' = m1 := by
          intro tyI elemTy count pm h0
          split at h0
          · simp [ub] at h0
          · obtain ⟨_, _, h0⟩ := ep1_bind_ok h0
            obtain ⟨_, _, h0⟩ := ep1_bind_ok h0
            obtain ⟨_, _, h0⟩ := ep1_bind_ok h0
            obtain ⟨_, _, h0⟩ := ep1_bind_ok h0
            obtain ⟨_, _, h0⟩ := ep1_bind_ok h0
            split at h0
            · obtain ⟨_, _, h0⟩ := ep1_bind_ok h0
              exact (Prod.mk.inj (ep1_pure_ok h0)).2.symm
            · simp [specPanic] at h0
        cases ty0 with
        | Array elem count => exact hidxFin (.Array elem count) elem count rp0.ptr.metadata h
        | Slice elem =>
          cases hpm : rp0.ptr.metadata with
          | some pm =>
            cases pm with
            | ElementCount count =>
              simp only [hpm] at h
              exact hidxFin (.Slice elem) elem count (some (.ElementCount count)) h
            | _ => simp [hpm, specPanic] at h
          | none => simp [hpm, specPanic] at h
        | _ => simp [specPanic] at h
      | _ => simp [specPanic] at h
    subst hmEq; exact ⟨hf1.trans hf0, hs1.trans hs0⟩
  | .Deref operand tyD, m, m', r, h => by
    unfold evalPlaceM at h
    obtain ⟨⟨rv, m0⟩, hv0, h⟩ := ep1_bind_ok h
    obtain ⟨hf0, hs0⟩ := ep1_evalValueM_preserves_shape_tb operand m m0 rv hv0
    have hmEq : m' = m0 := by
      rcases rv with ⟨v, vTy⟩
      cases v <;> cases vTy <;> try (simp [specPanic] at h)
      rename_i ptr ptrType
      have hdFin : (do
          let align ← computeAlignM m0 (← Type.layout tyD) ptr.metadata
          pure ((({ ptr := ptr, aligned := Align.is_aligned align ptr.thin_pointer.addr } : Gen.Place TBM), tyD), m0)) =
          .ok (r, m') → m' = m0 := by
        intro h0
        obtain ⟨_, _, h0⟩ := ep1_bind_ok h0
        obtain ⟨_, _, h0⟩ := ep1_bind_ok h0
        exact (Prod.mk.inj (ep1_pure_ok h0)).2.symm
      dsimp only [bind, Except.bind] at h
      cases hsp : PtrType.safe_pointee ptrType with
      | none => simp only [hsp] at h; exact hdFin h
      | some pointee =>
        simp only [hsp] at h
        obtain ⟨_, _, h⟩ := ep1_bind_ok h
        split at h
        · simp at h
        · obtain ⟨_, _, h⟩ := ep1_bind_ok h
          obtain ⟨_, _, h⟩ := ep1_bind_ok h
          exact hdFin h
    subst hmEq; exact ⟨hf0, hs0⟩
  | .Downcast root _, m, m', _, h => by
    unfold evalPlaceM at h
    obtain ⟨⟨⟨rp0, ty0⟩, m0⟩, hr0, h⟩ := ep1_bind_ok h
    obtain ⟨hf0, hs0⟩ := ep1_evalPlaceM_preserves_shape_tb root m m0 (rp0, ty0) hr0
    have hmEq : m' = m0 := by
      dsimp only [bind, Except.bind] at h
      cases ty0 with
      | Enum variants _ _ _ _ =>
        obtain ⟨_, _, h⟩ := ep1_bind_ok h
        exact (Prod.mk.inj (ep1_pure_ok h)).2.symm
      | _ => simp [specPanic] at h
    subst hmEq; exact ⟨hf0, hs0⟩

private theorem ep1_evalValueM_preserves_shape_tb :
    ∀ (e : Gen.ValueExpr) (m m' : MachTB) (r : Gen.Value TBM × Gen.Type),
      evalValueM m e = .ok (r, m') →
      ep1CurFrameViewM m' = ep1CurFrameViewM m ∧
      ep1AllocShape m'.mem.memory.mem.allocations = ep1AllocShape m.mem.memory.mem.allocations
  | .Constant _ _, m, m', _, h => by
    unfold evalValueM at h
    obtain ⟨_, _, h⟩ := ep1_bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
    exact ⟨rfl, rfl⟩
  | .Tuple es _, m, m', _, h => by
    unfold evalValueM at h
    obtain ⟨⟨vs, m0⟩, hvs, h⟩ := ep1_bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
    exact ep1_evalValuesM_preserves_shape_tb es m m0 vs hvs
  | .Union _ expr unionTy, m, m', _, h => by
    unfold evalValueM at h
    dsimp only [bind, Except.bind] at h
    cases unionTy with
    | Union fields chunks size align =>
      dsimp only [pure, Except.pure] at h
      obtain ⟨⟨_, _⟩, _, h⟩ := ep1_bind_ok h
      obtain ⟨⟨rv, m0⟩, hv0, h⟩ := ep1_bind_ok h
      obtain ⟨_, _, h⟩ := ep1_bind_ok h
      obtain ⟨_, _, h⟩ := ep1_bind_ok h
      obtain ⟨opt, _, h⟩ := ep1_bind_ok h
      cases opt with
      | none => simp [specPanic] at h
      | some _ =>
        obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
        exact ep1_evalValueM_preserves_shape_tb expr m m0 rv hv0
    | _ => simp [specPanic] at h
  | .Variant _ data _, m, m', _, h => by
    unfold evalValueM at h
    obtain ⟨⟨rv, m0⟩, hv0, h⟩ := ep1_bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
    exact ep1_evalValueM_preserves_shape_tb data m m0 rv hv0
  | .GetDiscriminant place, m, m', _, h => by
    unfold evalValueM at h
    obtain ⟨⟨⟨rp0, ty0⟩, m0⟩, hr0, h⟩ := ep1_bind_ok h
    obtain ⟨hf0, hs0⟩ := ep1_evalPlaceM_preserves_shape_tb place m m0 (rp0, ty0) hr0
    dsimp only [bind, Except.bind] at h
    cases ty0 with
    | Enum _ _ discr _ _ =>
      dsimp only at h
      split at h
      · simp [ub] at h
      · obtain ⟨⟨opt, m1⟩, hdd, hret⟩ := ep1_bind_ok h
        cases opt with
        | none => simp [ub] at hret
        | some _ =>
          obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hret)
          have hinv : ∀ (s : MachTB) (off : Gen.Offset) (sz : Size)
              (bs : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (s' : MachTB),
              (ep1CurFrameViewM s = ep1CurFrameViewM m0 ∧
                ep1AllocShape s.mem.memory.mem.allocations = ep1AllocShape m0.mem.memory.mem.allocations) →
              (do
                let ptr ← ptrOffsetInboundsM s rp0.ptr.thin_pointer (off.bytes : Int)
                let (bytes, cm) ← ConcurrentMemory.load s.mem ptr sz ⟨1⟩ .None
                pure (bytes, { s with mem := cm })) = .ok (bs, s') →
              (ep1CurFrameViewM s' = ep1CurFrameViewM m0 ∧
                ep1AllocShape s'.mem.memory.mem.allocations = ep1AllocShape m0.mem.memory.mem.allocations) := by
            intro s off sz bs s' ⟨hfS, hsS⟩ hacc
            obtain ⟨ptr, _, hacc⟩ := ep1_bind_ok hacc
            obtain ⟨⟨_, cm1⟩, hld, hacc⟩ := ep1_bind_ok hacc
            obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hacc)
            unfold ConcurrentMemory.load at hld
            obtain ⟨⟨_, tbm1⟩, hml, hcm⟩ := ep1_bind_ok hld
            obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hcm)
            change TreeBorrowsMemory.load s.mem.memory ptr sz ⟨1⟩ = .ok (_, tbm1) at hml
            unfold TreeBorrowsMemory.load at hml
            obtain ⟨⟨_, bm1⟩, hbm, htb⟩ := ep1_bind_ok hml
            obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok htb)
            exact ⟨hfS, (ep1_BasicMemory_load_shape hbm).trans hsS⟩
          obtain ⟨hf1, hs1⟩ := ep1_decodeDiscriminantM_inv
            (fun s : MachTB => ep1CurFrameViewM s = ep1CurFrameViewM m0 ∧
              ep1AllocShape s.mem.memory.mem.allocations = ep1AllocShape m0.mem.memory.mem.allocations)
            hinv discr m0 m1 _ ⟨rfl, rfl⟩ hdd
          exact ⟨hf1.trans hf0, hs1.trans hs0⟩
    | _ => simp [specPanic] at h
  | .Load source, m, m', _, h => by
    unfold evalValueM at h
    obtain ⟨⟨⟨rp0, ty0⟩, m0⟩, hr0, h⟩ := ep1_bind_ok h
    obtain ⟨hf0, hs0⟩ := ep1_evalPlaceM_preserves_shape_tb source m m0 (rp0, ty0) hr0
    obtain ⟨⟨_, m1⟩, hpl, hret⟩ := ep1_bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hret)
    unfold placeLoadM at hpl
    split at hpl
    · simp [ub] at hpl
    · unfold typedLoadM at hpl
      obtain ⟨_, _, hpl⟩ := ep1_bind_ok hpl
      obtain ⟨_, _, hpl⟩ := ep1_bind_ok hpl
      obtain ⟨⟨_, cm1⟩, hld, hpl⟩ := ep1_bind_ok hpl
      obtain ⟨opt, _, hpl⟩ := ep1_bind_ok hpl
      cases opt with
      | none => simp [ub] at hpl
      | some _ =>
        obtain ⟨_, _, hpl⟩ := ep1_bind_ok hpl
        obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hpl)
        unfold ConcurrentMemory.load at hld
        obtain ⟨⟨_, tbm1⟩, hml, hcm⟩ := ep1_bind_ok hld
        obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hcm)
        change TreeBorrowsMemory.load m0.mem.memory rp0.ptr.thin_pointer _ ⟨1⟩ = .ok (_, tbm1) at hml
        unfold TreeBorrowsMemory.load at hml
        obtain ⟨⟨_, bm1⟩, hbm, htb⟩ := ep1_bind_ok hml
        obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok htb)
        exact ⟨hf0, (ep1_BasicMemory_load_shape hbm).trans hs0⟩
  | .AddrOf target _, m, m', _, h => by
    unfold evalValueM at h
    obtain ⟨⟨r0, m0⟩, hr0, h⟩ := ep1_bind_ok h
    obtain ⟨hf0, hs0⟩ := ep1_evalPlaceM_preserves_shape_tb target m m0 r0 hr0
    obtain ⟨_, _, h⟩ := ep1_bind_ok h
    obtain ⟨⟨_, m1⟩, hmut, hret⟩ := ep1_bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hret)
    have hf1 : ep1CurFrameViewM m1 = ep1CurFrameViewM m0 :=
      ep1_mutateCurFrameOutM_preserves_curFrameView (fun fr cm a fr' cm' hfn => by
        obtain ⟨⟨_, _, _⟩, _, hfn⟩ := ep1_bind_ok hfn
        obtain ⟨_, h2⟩ := Prod.mk.inj (ep1_pure_ok hfn)
        obtain ⟨rfl, _⟩ := Prod.mk.inj h2
        exact ⟨rfl, rfl⟩) hmut
    have hs1 : ep1AllocShape m1.mem.memory.mem.allocations = ep1AllocShape m0.mem.memory.mem.allocations := by
      unfold mutateCurFrameOutM at hmut
      obtain ⟨t, _, hmut⟩ := ep1_bind_ok hmut
      cases hlast : t.stack.getLast? with
      | none => simp [hlast, specPanic] at hmut
      | some fr =>
        simp only [hlast] at hmut
        obtain ⟨⟨_, _, cm1⟩, hfn, hmut⟩ := ep1_bind_ok hmut
        obtain ⟨_, _, hmut⟩ := ep1_bind_ok hmut
        obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hmut)
        obtain ⟨⟨_, cm2, _⟩, hrt, hfn⟩ := ep1_bind_ok hfn
        obtain ⟨_, h2⟩ := Prod.mk.inj (ep1_pure_ok hfn)
        obtain ⟨_, rfl⟩ := Prod.mk.inj h2
        unfold ConcurrentMemory.retag_ptr at hrt
        obtain ⟨⟨_, tbm1, _⟩, htb, hrt⟩ := ep1_bind_ok hrt
        obtain ⟨_, h2⟩ := Prod.mk.inj (ep1_pure_ok hrt)
        obtain ⟨rfl, _⟩ := Prod.mk.inj h2
        exact ep1_retag_ptr_shape_tb htb
    exact ⟨hf1.trans hf0, hs1.trans hs0⟩
  | .UnOp _ operand, m, m', _, h => by
    unfold evalValueM at h
    obtain ⟨⟨rv, m0⟩, hv0, h⟩ := ep1_bind_ok h
    obtain ⟨_, _, h⟩ := ep1_bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
    exact ep1_evalValueM_preserves_shape_tb operand m m0 rv hv0
  | .BinOp op left right, m, m', _, h => by
    unfold evalValueM at h
    cases op with
    | PtrOffset _ =>
      obtain ⟨⟨rl, m0⟩, hl0, h⟩ := ep1_bind_ok h
      obtain ⟨⟨rr, m1⟩, hr1, h⟩ := ep1_bind_ok h
      obtain ⟨_, _, h⟩ := ep1_bind_ok h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
      obtain ⟨hf0, hs0⟩ := ep1_evalValueM_preserves_shape_tb left m m0 rl hl0
      obtain ⟨hf1, hs1⟩ := ep1_evalValueM_preserves_shape_tb right m0 m1 rr hr1
      exact ⟨hf1.trans hf0, hs1.trans hs0⟩
    | PtrOffsetFrom _ =>
      obtain ⟨⟨rl, m0⟩, hl0, h⟩ := ep1_bind_ok h
      obtain ⟨⟨rr, m1⟩, hr1, h⟩ := ep1_bind_ok h
      obtain ⟨_, _, h⟩ := ep1_bind_ok h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
      obtain ⟨hf0, hs0⟩ := ep1_evalValueM_preserves_shape_tb left m m0 rl hl0
      obtain ⟨hf1, hs1⟩ := ep1_evalValueM_preserves_shape_tb right m0 m1 rr hr1
      exact ⟨hf1.trans hf0, hs1.trans hs0⟩
    | _ =>
      obtain ⟨⟨rl, m0⟩, hl0, h⟩ := ep1_bind_ok h
      obtain ⟨⟨rr, m1⟩, hr1, h⟩ := ep1_bind_ok h
      obtain ⟨_, _, h⟩ := ep1_bind_ok h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
      obtain ⟨hf0, hs0⟩ := ep1_evalValueM_preserves_shape_tb left m m0 rl hl0
      obtain ⟨hf1, hs1⟩ := ep1_evalValueM_preserves_shape_tb right m0 m1 rr hr1
      exact ⟨hf1.trans hf0, hs1.trans hs0⟩

private theorem ep1_evalValuesM_preserves_shape_tb :
    ∀ (es : List Gen.ValueExpr) (m m' : MachTB) (vs : List (Gen.Value TBM)),
      evalValuesM m es = .ok (vs, m') →
      ep1CurFrameViewM m' = ep1CurFrameViewM m ∧
      ep1AllocShape m'.mem.memory.mem.allocations = ep1AllocShape m.mem.memory.mem.allocations
  | [], m, m', _, h => by
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h); exact ⟨rfl, rfl⟩
  | e :: rest, m, m', _, h => by
    unfold evalValuesM at h
    obtain ⟨⟨rv, m0⟩, hv0, h⟩ := ep1_bind_ok h
    obtain ⟨⟨vs', m1⟩, hrest, h⟩ := ep1_bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
    obtain ⟨hf0, hs0⟩ := ep1_evalValueM_preserves_shape_tb e m m0 rv hv0
    obtain ⟨hf1, hs1⟩ := ep1_evalValuesM_preserves_shape_tb rest m0 m1 vs' hrest
    exact ⟨hf1.trans hf0, hs1.trans hs0⟩

end

mutual

private theorem ep1_evalPlaceM_preserves_shape_bm :
    ∀ (p : Gen.PlaceExpr) (m m' : Mach) (r : Gen.Place BM × Gen.Type),
      evalPlaceM m p = .ok (r, m') →
      ep1CurFrameViewM (M := BM) m' = ep1CurFrameViewM (M := BM) m ∧
      m'.mem.memory = m.mem.memory
  | .Local _, m, m', _, h => by
    obtain ⟨rfl, _⟩ := ep1_evalPlaceM_chain_thin_and_readonly _ (.Local _) m m' _ _ h
    exact ⟨rfl, rfl⟩
  | .Field root _, m, m', r, h => by
    unfold evalPlaceM at h
    obtain ⟨⟨⟨rp0, ty0⟩, m0⟩, hr0, h⟩ := ep1_bind_ok h
    obtain ⟨hf0, hs0⟩ := ep1_evalPlaceM_preserves_shape_bm root m m0 (rp0, ty0) hr0
    have hmEq : m' = m0 := by
      have hfin : ∀ (off : Gen.Offset) (fty : Gen.Type),
          (do
            let rootSize ← computeSizeM m0 (← Type.layout ty0) rp0.ptr.metadata
            if !(off.bytes ≤ rootSize.bytes) then
              specPanic "assertion failed: offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata)"
            else do
              let ptr ← ptrOffsetInboundsM m0 rp0.ptr.thin_pointer (off.bytes : Int)
              let ptr := if !LayoutStrategy.is_sized (← Type.layout fty) then
                  ThinPointer.widen ptr rp0.ptr.metadata
                else
                  ThinPointer.widen ptr none
              pure (({ rp0 with ptr := ptr }, fty), m0)) = .ok (r, m') → m' = m0 := by
        intro off fty ht
        obtain ⟨_, _, ht⟩ := ep1_bind_ok ht
        obtain ⟨_, _, ht⟩ := ep1_bind_ok ht
        split at ht
        · simp [specPanic] at ht
        · obtain ⟨_, _, ht⟩ := ep1_bind_ok ht
          obtain ⟨_, _, ht⟩ := ep1_bind_ok ht
          exact (Prod.mk.inj (ep1_pure_ok ht)).2.symm
      dsimp only [bind, Except.bind] at h
      cases ty0 with
      | Tuple sf sh uf =>
        dsimp only at h
        split at h
        · obtain ⟨⟨off, fty⟩, _, ht⟩ := ep1_bind_ok h; exact hfin off fty ht
        · split at h
          · cases uf with
            | none => simp [specPanic] at h
            | some tailTy =>
              obtain ⟨_, _, h⟩ := ep1_bind_ok h
              obtain ⟨tal, _, ht⟩ := ep1_bind_ok h
              exact hfin (TupleHeadLayout.tail_offset sh tal) tailTy ht
          · simp [specPanic] at h
      | Union fields _ _ _ =>
        obtain ⟨⟨off, fty⟩, _, ht⟩ := ep1_bind_ok h; exact hfin off fty ht
      | _ => simp [specPanic] at h
    subst hmEq; exact ⟨hf0, hs0⟩
  | .Index root idx, m, m', r, h => by
    unfold evalPlaceM at h
    obtain ⟨⟨r0, m0⟩, hr0, h⟩ := ep1_bind_ok h
    obtain ⟨⟨rv, m1⟩, hv1, h⟩ := ep1_bind_ok h
    obtain ⟨hf0, hs0⟩ := ep1_evalPlaceM_preserves_shape_bm root m m0 r0 hr0
    obtain ⟨hf1, hs1⟩ := ep1_evalValueM_preserves_shape_bm idx m0 m1 rv hv1
    have hmEq : m' = m1 := by
      rcases r0 with ⟨rp0, ty0⟩
      rcases rv with ⟨idxVal, idxTy⟩
      dsimp only [bind, Except.bind] at h
      cases idxVal with
      | Int i =>
        dsimp only [pure, Except.pure] at h
        have hidxFin : ∀ (tyI elemTy : Gen.Type) (count : Int)
            (pm : Option (Gen.PointerMeta (Gen.Memory.Provenance BM))),
            (if i < 0 ∨ i ≥ count then ub "access to out-of-bounds index"
             else do
               let elemLayout ← Type.layout elemTy
               let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array & slice elements are sized"
               let offset ← Size.mulInt elemSize i
               let rootSize ← computeSizeM (M := BM) m1 (← Type.layout tyI) pm
               if offset.bytes ≤ rootSize.bytes then
                 let ptr ← ptrOffsetInboundsM (M := BM) m1 rp0.ptr.thin_pointer (offset.bytes : Int)
                 pure (({ rp0 with ptr := ThinPointer.widen ptr none }, elemTy), m1)
               else
                 specPanic "sanity check: the indexed offset should not be outside what the type allows.") =
              .ok (r, m') → m' = m1 := by
          intro tyI elemTy count pm h0
          split at h0
          · simp [ub] at h0
          · obtain ⟨_, _, h0⟩ := ep1_bind_ok h0
            obtain ⟨_, _, h0⟩ := ep1_bind_ok h0
            obtain ⟨_, _, h0⟩ := ep1_bind_ok h0
            obtain ⟨_, _, h0⟩ := ep1_bind_ok h0
            obtain ⟨_, _, h0⟩ := ep1_bind_ok h0
            split at h0
            · obtain ⟨_, _, h0⟩ := ep1_bind_ok h0
              exact (Prod.mk.inj (ep1_pure_ok h0)).2.symm
            · simp [specPanic] at h0
        cases ty0 with
        | Array elem count => exact hidxFin (.Array elem count) elem count rp0.ptr.metadata h
        | Slice elem =>
          cases hpm : rp0.ptr.metadata with
          | some pm =>
            cases pm with
            | ElementCount count =>
              simp only [hpm] at h
              exact hidxFin (.Slice elem) elem count (some (.ElementCount count)) h
            | _ => simp [hpm, specPanic] at h
          | none => simp [hpm, specPanic] at h
        | _ => simp [specPanic] at h
      | _ => simp [specPanic] at h
    subst hmEq; exact ⟨hf1.trans hf0, hs1.trans hs0⟩
  | .Deref operand tyD, m, m', r, h => by
    unfold evalPlaceM at h
    obtain ⟨⟨rv, m0⟩, hv0, h⟩ := ep1_bind_ok h
    obtain ⟨hf0, hs0⟩ := ep1_evalValueM_preserves_shape_bm operand m m0 rv hv0
    have hmEq : m' = m0 := by
      rcases rv with ⟨v, vTy⟩
      cases v <;> cases vTy <;> try (simp [specPanic] at h)
      rename_i ptr ptrType
      have hdFin : (do
          let align ← computeAlignM (M := BM) m0 (← Type.layout tyD) ptr.metadata
          pure ((({ ptr := ptr, aligned := Align.is_aligned align ptr.thin_pointer.addr } : Gen.Place BM), tyD), m0)) =
          .ok (r, m') → m' = m0 := by
        intro h0
        obtain ⟨_, _, h0⟩ := ep1_bind_ok h0
        obtain ⟨_, _, h0⟩ := ep1_bind_ok h0
        exact (Prod.mk.inj (ep1_pure_ok h0)).2.symm
      dsimp only [bind, Except.bind] at h
      cases hsp : PtrType.safe_pointee ptrType with
      | none => simp only [hsp] at h; exact hdFin h
      | some pointee =>
        simp only [hsp] at h
        obtain ⟨_, _, h⟩ := ep1_bind_ok h
        split at h
        · simp at h
        · obtain ⟨_, _, h⟩ := ep1_bind_ok h
          obtain ⟨_, _, h⟩ := ep1_bind_ok h
          exact hdFin h
    subst hmEq; exact ⟨hf0, hs0⟩
  | .Downcast root _, m, m', _, h => by
    unfold evalPlaceM at h
    obtain ⟨⟨⟨rp0, ty0⟩, m0⟩, hr0, h⟩ := ep1_bind_ok h
    obtain ⟨hf0, hs0⟩ := ep1_evalPlaceM_preserves_shape_bm root m m0 (rp0, ty0) hr0
    have hmEq : m' = m0 := by
      dsimp only [bind, Except.bind] at h
      cases ty0 with
      | Enum variants _ _ _ _ =>
        obtain ⟨_, _, h⟩ := ep1_bind_ok h
        exact (Prod.mk.inj (ep1_pure_ok h)).2.symm
      | _ => simp [specPanic] at h
    subst hmEq; exact ⟨hf0, hs0⟩

private theorem ep1_evalValueM_preserves_shape_bm :
    ∀ (e : Gen.ValueExpr) (m m' : Mach) (r : Gen.Value BM × Gen.Type),
      evalValueM m e = .ok (r, m') →
      ep1CurFrameViewM (M := BM) m' = ep1CurFrameViewM (M := BM) m ∧
      m'.mem.memory = m.mem.memory
  | .Constant _ _, m, m', _, h => by
    unfold evalValueM at h
    obtain ⟨_, _, h⟩ := ep1_bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
    exact ⟨rfl, rfl⟩
  | .Tuple es _, m, m', _, h => by
    unfold evalValueM at h
    obtain ⟨⟨vs, m0⟩, hvs, h⟩ := ep1_bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
    exact ep1_evalValuesM_preserves_shape_bm es m m0 vs hvs
  | .Union _ expr unionTy, m, m', _, h => by
    unfold evalValueM at h
    dsimp only [bind, Except.bind] at h
    cases unionTy with
    | Union fields chunks size align =>
      dsimp only [pure, Except.pure] at h
      obtain ⟨⟨_, _⟩, _, h⟩ := ep1_bind_ok h
      obtain ⟨⟨rv, m0⟩, hv0, h⟩ := ep1_bind_ok h
      obtain ⟨_, _, h⟩ := ep1_bind_ok h
      obtain ⟨_, _, h⟩ := ep1_bind_ok h
      obtain ⟨opt, _, h⟩ := ep1_bind_ok h
      cases opt with
      | none => simp [specPanic] at h
      | some _ =>
        obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
        exact ep1_evalValueM_preserves_shape_bm expr m m0 rv hv0
    | _ => simp [specPanic] at h
  | .Variant _ data _, m, m', _, h => by
    unfold evalValueM at h
    obtain ⟨⟨rv, m0⟩, hv0, h⟩ := ep1_bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
    exact ep1_evalValueM_preserves_shape_bm data m m0 rv hv0
  | .GetDiscriminant place, m, m', _, h => by
    unfold evalValueM at h
    obtain ⟨⟨⟨rp0, ty0⟩, m0⟩, hr0, h⟩ := ep1_bind_ok h
    obtain ⟨hf0, hs0⟩ := ep1_evalPlaceM_preserves_shape_bm place m m0 (rp0, ty0) hr0
    dsimp only [bind, Except.bind] at h
    cases ty0 with
    | Enum _ _ discr _ _ =>
      dsimp only at h
      split at h
      · simp [ub] at h
      · obtain ⟨⟨opt, m1⟩, hdd, hret⟩ := ep1_bind_ok h
        cases opt with
        | none => simp [ub] at hret
        | some _ =>
          obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hret)
          have hinv : ∀ (s : Mach) (off : Gen.Offset) (sz : Size) (bs : List Byte) (s' : Mach),
              (ep1CurFrameViewM (M := BM) s = ep1CurFrameViewM (M := BM) m0 ∧
                s.mem.memory = m0.mem.memory) →
              (do
                let ptr ← ptrOffsetInboundsM (M := BM) s rp0.ptr.thin_pointer (off.bytes : Int)
                let (bytes, cm) ← ConcurrentMemory.load (M := BM) s.mem ptr sz ⟨1⟩ .None
                pure (bytes, { s with mem := cm })) = .ok (bs, s') →
              (ep1CurFrameViewM (M := BM) s' = ep1CurFrameViewM (M := BM) m0 ∧
                s'.mem.memory = m0.mem.memory) := by
            intro s off sz bs s' ⟨hfS, hsS⟩ hacc
            obtain ⟨ptr, _, hacc⟩ := ep1_bind_ok hacc
            obtain ⟨⟨_, cm1⟩, hld, hacc⟩ := ep1_bind_ok hacc
            obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hacc)
            unfold ConcurrentMemory.load at hld
            obtain ⟨⟨_, bm1⟩, hml, hcm⟩ := ep1_bind_ok hld
            obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hcm)
            change BM.load s.mem.memory ptr sz ⟨1⟩ = .ok (_, bm1) at hml
            exact ⟨hfS, (BM.load_eq hml).trans hsS⟩
          obtain ⟨hf1, hs1⟩ := ep1_decodeDiscriminantM_inv
            (fun s : Mach => ep1CurFrameViewM (M := BM) s = ep1CurFrameViewM (M := BM) m0 ∧
              s.mem.memory = m0.mem.memory)
            hinv discr m0 m1 _ ⟨rfl, rfl⟩ hdd
          exact ⟨hf1.trans hf0, hs1.trans hs0⟩
    | _ => simp [specPanic] at h
  | .Load source, m, m', _, h => by
    unfold evalValueM at h
    obtain ⟨⟨⟨rp0, ty0⟩, m0⟩, hr0, h⟩ := ep1_bind_ok h
    obtain ⟨hf0, hs0⟩ := ep1_evalPlaceM_preserves_shape_bm source m m0 (rp0, ty0) hr0
    obtain ⟨⟨_, m1⟩, hpl, hret⟩ := ep1_bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hret)
    unfold placeLoadM at hpl
    split at hpl
    · simp [ub] at hpl
    · unfold typedLoadM at hpl
      obtain ⟨_, _, hpl⟩ := ep1_bind_ok hpl
      obtain ⟨_, _, hpl⟩ := ep1_bind_ok hpl
      obtain ⟨⟨_, cm1⟩, hld, hpl⟩ := ep1_bind_ok hpl
      obtain ⟨opt, _, hpl⟩ := ep1_bind_ok hpl
      cases opt with
      | none => simp [ub] at hpl
      | some _ =>
        obtain ⟨_, _, hpl⟩ := ep1_bind_ok hpl
        obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hpl)
        unfold ConcurrentMemory.load at hld
        obtain ⟨⟨_, bm1⟩, hml, hcm⟩ := ep1_bind_ok hld
        obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hcm)
        change BM.load m0.mem.memory rp0.ptr.thin_pointer _ ⟨1⟩ = .ok (_, bm1) at hml
        exact ⟨hf0, (BM.load_eq hml).trans hs0⟩
  | .AddrOf target _, m, m', _, h => by
    unfold evalValueM at h
    obtain ⟨⟨r0, m0⟩, hr0, h⟩ := ep1_bind_ok h
    obtain ⟨hf0, hs0⟩ := ep1_evalPlaceM_preserves_shape_bm target m m0 r0 hr0
    obtain ⟨_, _, h⟩ := ep1_bind_ok h
    obtain ⟨⟨_, m1⟩, hmut, hret⟩ := ep1_bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hret)
    have hf1 : ep1CurFrameViewM (M := BM) m1 = ep1CurFrameViewM (M := BM) m0 :=
      ep1_mutateCurFrameOutM_preserves_curFrameView (fun fr cm a fr' cm' hfn => by
        obtain ⟨⟨_, _, _⟩, _, hfn⟩ := ep1_bind_ok hfn
        obtain ⟨_, h2⟩ := Prod.mk.inj (ep1_pure_ok hfn)
        obtain ⟨rfl, _⟩ := Prod.mk.inj h2
        exact ⟨rfl, rfl⟩) hmut
    have hs1 : m1.mem.memory = m0.mem.memory := by
      unfold mutateCurFrameOutM at hmut
      obtain ⟨t, _, hmut⟩ := ep1_bind_ok hmut
      cases hlast : t.stack.getLast? with
      | none => simp [hlast, specPanic] at hmut
      | some fr =>
        simp only [hlast] at hmut
        obtain ⟨⟨_, _, cm1⟩, hfn, hmut⟩ := ep1_bind_ok hmut
        obtain ⟨_, _, hmut⟩ := ep1_bind_ok hmut
        obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hmut)
        obtain ⟨⟨_, cm2, _⟩, hrt, hfn⟩ := ep1_bind_ok hfn
        obtain ⟨_, h2⟩ := Prod.mk.inj (ep1_pure_ok hfn)
        obtain ⟨_, rfl⟩ := Prod.mk.inj h2
        unfold ConcurrentMemory.retag_ptr at hrt
        obtain ⟨⟨pRet, bm1, feRet⟩, hbm, hrt⟩ := ep1_bind_ok hrt
        obtain ⟨_, h2⟩ := Prod.mk.inj (ep1_pure_ok hrt)
        obtain ⟨rfl, _⟩ := Prod.mk.inj h2
        have hbmEq : r0.1.ptr = pRet ∧ m0.mem.memory = bm1 ∧ fr.extra = feRet := by
          simpa [MemoryOps.retag_ptr] using hbm
        exact hbmEq.2.1.symm
    exact ⟨hf1.trans hf0, hs1.trans hs0⟩
  | .UnOp _ operand, m, m', _, h => by
    unfold evalValueM at h
    obtain ⟨⟨rv, m0⟩, hv0, h⟩ := ep1_bind_ok h
    obtain ⟨_, _, h⟩ := ep1_bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
    exact ep1_evalValueM_preserves_shape_bm operand m m0 rv hv0
  | .BinOp op left right, m, m', _, h => by
    unfold evalValueM at h
    cases op with
    | PtrOffset _ =>
      obtain ⟨⟨rl, m0⟩, hl0, h⟩ := ep1_bind_ok h
      obtain ⟨⟨rr, m1⟩, hr1, h⟩ := ep1_bind_ok h
      obtain ⟨_, _, h⟩ := ep1_bind_ok h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
      obtain ⟨hf0, hs0⟩ := ep1_evalValueM_preserves_shape_bm left m m0 rl hl0
      obtain ⟨hf1, hs1⟩ := ep1_evalValueM_preserves_shape_bm right m0 m1 rr hr1
      exact ⟨hf1.trans hf0, hs1.trans hs0⟩
    | PtrOffsetFrom _ =>
      obtain ⟨⟨rl, m0⟩, hl0, h⟩ := ep1_bind_ok h
      obtain ⟨⟨rr, m1⟩, hr1, h⟩ := ep1_bind_ok h
      obtain ⟨_, _, h⟩ := ep1_bind_ok h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
      obtain ⟨hf0, hs0⟩ := ep1_evalValueM_preserves_shape_bm left m m0 rl hl0
      obtain ⟨hf1, hs1⟩ := ep1_evalValueM_preserves_shape_bm right m0 m1 rr hr1
      exact ⟨hf1.trans hf0, hs1.trans hs0⟩
    | _ =>
      obtain ⟨⟨rl, m0⟩, hl0, h⟩ := ep1_bind_ok h
      obtain ⟨⟨rr, m1⟩, hr1, h⟩ := ep1_bind_ok h
      obtain ⟨_, _, h⟩ := ep1_bind_ok h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
      obtain ⟨hf0, hs0⟩ := ep1_evalValueM_preserves_shape_bm left m m0 rl hl0
      obtain ⟨hf1, hs1⟩ := ep1_evalValueM_preserves_shape_bm right m0 m1 rr hr1
      exact ⟨hf1.trans hf0, hs1.trans hs0⟩

private theorem ep1_evalValuesM_preserves_shape_bm :
    ∀ (es : List Gen.ValueExpr) (m m' : Mach) (vs : List Val),
      evalValuesM (M := BM) m es = .ok (vs, m') →
      ep1CurFrameViewM (M := BM) m' = ep1CurFrameViewM (M := BM) m ∧
      m'.mem.memory = m.mem.memory
  | [], m, m', _, h => by
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h); exact ⟨rfl, rfl⟩
  | e :: rest, m, m', _, h => by
    unfold evalValuesM at h
    obtain ⟨⟨rv, m0⟩, hv0, h⟩ := ep1_bind_ok h
    obtain ⟨⟨vs', m1⟩, hrest, h⟩ := ep1_bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok h)
    obtain ⟨hf0, hs0⟩ := ep1_evalValueM_preserves_shape_bm e m m0 rv hv0
    obtain ⟨hf1, hs1⟩ := ep1_evalValuesM_preserves_shape_bm rest m0 m1 vs' hrest
    exact ⟨hf1.trans hf0, hs1.trans hs0⟩

end

/-! #### Per-byte Tree Borrows `Write → Read` idempotence (sub-ranges & disjoint-write preservation) -/

mutual

private def ep1NodeReadIdem (path : Option Gen.Path) (off len : Nat) : Gen.Node → Prop
  | ⟨children, perms, _⟩ =>
    (∀ i, off ≤ i → i < off + len →
      ∃ hi : i < perms.length,
        Permission.transition perms[i] .Read (if path.isSome then .Local else .Foreign) = .ok perms[i]) ∧
    ep1ChildrenReadIdem 0 path off len children

private def ep1ChildrenReadIdem (childId : Int) (path : Option Gen.Path) (off len : Nat) :
    List Gen.Node → Prop
  | [] => True
  | c :: rest =>
    let subPath : Option Gen.Path :=
      match path with
      | some (head :: tail) => if head == childId then some tail else none
      | _ => none
    ep1NodeReadIdem subPath off len c ∧
    ep1ChildrenReadIdem (childId + 1) path off len rest

end

private theorem ep1_transitionRange_preserves_outside (rel : Gen.NodeRelation) (acc : Gen.AccessKind) :
    ∀ (off rem : Nat) (perms perms' : List Gen.Permission),
      Node.transitionRange rel acc off rem perms = .ok perms' →
      ∃ hlen : perms'.length = perms.length,
        ∀ i, (i < off ∨ off + rem ≤ i) → (hi : i < perms.length) →
          perms'[i]'(hlen ▸ hi) = perms[i]
  | _, 0, perms, perms', h => by
    obtain rfl := ep1_pure_ok h
    exact ⟨rfl, fun _ _ _ => rfl⟩
  | off, rem + 1, perms, perms', h => by
    unfold Node.transitionRange at h
    obtain ⟨⟨_, perms1⟩, hmut, hrest⟩ := ep1_bind_ok h
    unfold listMutateAt at hmut
    obtain ⟨elem, hidx, hmut⟩ := ep1_bind_ok hmut
    obtain ⟨⟨_, p1⟩, htr_b, hmut⟩ := ep1_bind_ok hmut
    obtain ⟨p', _, hp1⟩ := ep1_bind_ok htr_b
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hp1)
    obtain ⟨perms1', hset, hmut⟩ := ep1_bind_ok hmut
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hmut)
    obtain ⟨_, _⟩ := ep1_listIndex_eq_getElem hidx
    obtain ⟨_, rfl⟩ := ep1_listSet_eq hset
    obtain ⟨hlen', hih⟩ :=
      ep1_transitionRange_preserves_outside rel acc (off + 1) rem (perms.set off p') perms' hrest
    refine ⟨by rw [hlen', List.length_set], fun i hout hi => ?_⟩
    have hi1 : i < (perms.set off p').length := by simpa [List.length_set] using hi
    have hout1 : i < off + 1 ∨ (off + 1) + rem ≤ i := by omega
    rw [hih i hout1 hi1, List.getElem_set_ne (by omega)]

private theorem ep1_transitionRange_write_establishes_readIdem (rel : Gen.NodeRelation) :
    ∀ (off rem : Nat) (perms perms' : List Gen.Permission),
      Node.transitionRange rel .Write off rem perms = .ok perms' →
      perms'.length = perms.length ∧
      (∀ i, off ≤ i → i < off + rem →
        ∃ hi : i < perms'.length, Permission.transition perms'[i] .Read rel = .ok perms'[i])
  | _, 0, perms, perms', h => by
    obtain rfl := ep1_pure_ok h
    exact ⟨rfl, fun _ h1 h2 => by omega⟩
  | off, rem + 1, perms, perms', h => by
    unfold Node.transitionRange at h
    obtain ⟨⟨_, perms1⟩, hmut, hrest⟩ := ep1_bind_ok h
    unfold listMutateAt at hmut
    obtain ⟨elem, hidx, hmut⟩ := ep1_bind_ok hmut
    obtain ⟨⟨_, p1⟩, htr_b, hmut⟩ := ep1_bind_ok hmut
    obtain ⟨p', htr, hp1⟩ := ep1_bind_ok htr_b
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hp1)
    obtain ⟨perms1', hset, hmut⟩ := ep1_bind_ok hmut
    obtain ⟨_, rfl⟩ := Prod.mk.inj (ep1_pure_ok hmut)
    obtain ⟨hhi, helem⟩ := ep1_listIndex_eq_getElem hidx
    obtain ⟨_, rfl⟩ := ep1_listSet_eq hset
    obtain ⟨hlen', hih⟩ := ep1_transitionRange_write_establishes_readIdem rel (off + 1) rem (perms.set off p') perms' hrest
    refine ⟨by rw [hlen', List.length_set], fun i h1 h2 => ?_⟩
    by_cases heq : i = off
    · subst heq
      obtain ⟨hlenP, hpres⟩ := ep1_transitionRange_preserves_other rel .Write (i + 1) rem (perms.set i p') perms' hrest
      have hi1 : i < (perms.set i p').length := by simpa [List.length_set] using hhi
      have hi' : i < perms'.length := hlenP ▸ hi1
      have hget : perms'[i]'hi' = p' := by
        rw [hpres i (by omega) hi1, List.getElem_set_self]
      refine ⟨hi', ?_⟩
      rw [hget]
      exact ep1_tb_permission_write_then_read_idempotent elem p' rel htr
    · exact hih i (by omega) (by omega)

private theorem ep1_transitionRange_read_eq_of_readIdem (rel : Gen.NodeRelation) :
    ∀ (off rem : Nat) (perms : List Gen.Permission),
      (∀ i, off ≤ i → i < off + rem →
        ∃ hi : i < perms.length, Permission.transition perms[i] .Read rel = .ok perms[i]) →
      Node.transitionRange rel .Read off rem perms = .ok perms
  | _, 0, _, _ => rfl
  | off, rem + 1, perms, hok => by
    obtain ⟨hoff, htr⟩ := hok off (Nat.le_refl _) (by omega)
    have hmut : listMutateAt perms (Int.ofNat off) "Node::transition"
        (fun permission => do
          let p' ← Permission.transition permission .Read rel
          pure ((), p')) = .ok ((), perms) := by
      unfold listMutateAt
      rw [ep1_listIndex_of_getElem "Node::transition" hoff]
      simp only [bind, Except.bind, htr, pure, Except.pure,
        ep1_listSet_of_lt perms[off] "Node::transition" hoff, List.set_getElem_self hoff]
    unfold Node.transitionRange
    rw [hmut]
    exact ep1_transitionRange_read_eq_of_readIdem rel (off + 1) rem perms
      (fun i h1 h2 => hok i (by omega) (by omega))

mutual

private theorem ep1_node_access_write_establishes_readIdem :
    ∀ (n n' : Gen.Node) (path : Option Gen.Path) (base len : Nat),
      Node.access n path .Write ⟨base⟩ ⟨len⟩ = .ok n' →
      ep1NodeReadIdem path base len n'
  | ⟨children, perms, prot⟩, n', path, base, len, h => by
    unfold Node.access at h
    obtain ⟨n1, htr, h⟩ := ep1_bind_ok h
    obtain ⟨cs', hcs, hp⟩ := ep1_bind_ok h
    obtain rfl := ep1_pure_ok hp
    unfold Node.transition at htr
    obtain ⟨perms', htrR, hnp⟩ := ep1_bind_ok htr
    obtain rfl := ep1_pure_ok hnp
    exact ⟨(ep1_transitionRange_write_establishes_readIdem _ base len perms perms' htrR).2,
      ep1_children_access_write_establishes_readIdem children cs' 0 path base len hcs⟩

private theorem ep1_children_access_write_establishes_readIdem :
    ∀ (cs cs' : List Gen.Node) (childId : Int) (path : Option Gen.Path) (base len : Nat),
      Node.accessChildren childId path .Write ⟨base⟩ ⟨len⟩ cs = .ok cs' →
      ep1ChildrenReadIdem childId path base len cs'
  | [], cs', _, _, _, _, h => by obtain rfl := ep1_pure_ok h; trivial
  | c :: rest, cs', childId, path, base, len, h => by
    unfold Node.accessChildren at h
    obtain ⟨c', hc, h⟩ := ep1_bind_ok h
    obtain ⟨rest', hr, hp⟩ := ep1_bind_ok h
    obtain rfl := ep1_pure_ok hp
    exact ⟨ep1_node_access_write_establishes_readIdem c c' _ base len hc,
      ep1_children_access_write_establishes_readIdem rest rest' (childId + 1) path base len hr⟩

end

mutual

private theorem ep1_node_access_disjoint_preserves_readIdem (off len off' len' : Nat)
    (hdisj : off + len ≤ off' ∨ off' + len' ≤ off) :
    ∀ (n n' : Gen.Node) (path path' : Option Gen.Path) (acc : Gen.AccessKind),
      Node.access n path' acc ⟨off'⟩ ⟨len'⟩ = .ok n' →
      ep1NodeReadIdem path off len n →
      ep1NodeReadIdem path off len n'
  | ⟨children, perms, prot⟩, n', path, path', acc, h, ⟨hperms, hcs⟩ => by
    unfold Node.access at h
    obtain ⟨n1, htr, h⟩ := ep1_bind_ok h
    obtain ⟨cs', hcsExec, hp⟩ := ep1_bind_ok h
    obtain rfl := ep1_pure_ok hp
    unfold Node.transition at htr
    obtain ⟨perms', htrR, hnp⟩ := ep1_bind_ok htr
    obtain rfl := ep1_pure_ok hnp
    obtain ⟨hlen', hpres⟩ := ep1_transitionRange_preserves_outside _ acc off' len' perms perms' htrR
    refine ⟨fun i h1 h2 => ?_,
      ep1_children_access_disjoint_preserves_readIdem off len off' len' hdisj children cs' 0 path path' acc hcsExec hcs⟩
    obtain ⟨hi, htrI⟩ := hperms i h1 h2
    have hi' : i < perms'.length := hlen' ▸ hi
    have hnot : i < off' ∨ off' + len' ≤ i := by omega
    have hget : perms'[i]'hi' = perms[i]'hi := hpres i hnot hi
    refine ⟨hi', ?_⟩
    rw [hget]
    exact htrI

private theorem ep1_children_access_disjoint_preserves_readIdem (off len off' len' : Nat)
    (hdisj : off + len ≤ off' ∨ off' + len' ≤ off) :
    ∀ (cs cs' : List Gen.Node) (childId : Int) (path path' : Option Gen.Path) (acc : Gen.AccessKind),
      Node.accessChildren childId path' acc ⟨off'⟩ ⟨len'⟩ cs = .ok cs' →
      ep1ChildrenReadIdem childId path off len cs →
      ep1ChildrenReadIdem childId path off len cs'
  | [], cs', _, _, _, _, h, _ => by obtain rfl := ep1_pure_ok h; trivial
  | c :: rest, cs', childId, path, path', acc, h, ⟨hc, hr⟩ => by
    unfold Node.accessChildren at h
    obtain ⟨c', hcExec, h⟩ := ep1_bind_ok h
    obtain ⟨rest', hrExec, hp⟩ := ep1_bind_ok h
    obtain rfl := ep1_pure_ok hp
    exact ⟨ep1_node_access_disjoint_preserves_readIdem off len off' len' hdisj c c' _ _ acc hcExec hc,
      ep1_children_access_disjoint_preserves_readIdem off len off' len' hdisj rest rest' (childId + 1) path path' acc hrExec hr⟩

end

mutual

private theorem ep1_node_access_read_eq_of_readIdem (base len subOff subLen : Nat)
    (hlo : base ≤ subOff) (hhi : subOff + subLen ≤ base + len) :
    ∀ (n : Gen.Node) (path : Option Gen.Path),
      ep1NodeReadIdem path base len n →
      Node.access n path .Read ⟨subOff⟩ ⟨subLen⟩ = .ok n
  | ⟨children, perms, prot⟩, path, ⟨hperms, hcs⟩ => by
    have htr : Node.transitionRange (if path.isSome then .Local else .Foreign) .Read subOff subLen perms = .ok perms :=
      ep1_transitionRange_read_eq_of_readIdem _ subOff subLen perms
        (fun i h1 h2 => hperms i (by omega) (by omega))
    have hcsR := ep1_children_access_read_eq_of_readIdem base len subOff subLen hlo hhi children 0 path hcs
    unfold Node.access Node.transition
    simp only [htr, hcsR, bind, Except.bind, pure, Except.pure]

private theorem ep1_children_access_read_eq_of_readIdem (base len subOff subLen : Nat)
    (hlo : base ≤ subOff) (hhi : subOff + subLen ≤ base + len) :
    ∀ (cs : List Gen.Node) (childId : Int) (path : Option Gen.Path),
      ep1ChildrenReadIdem childId path base len cs →
      Node.accessChildren childId path .Read ⟨subOff⟩ ⟨subLen⟩ cs = .ok cs
  | [], _, _, _ => rfl
  | c :: rest, childId, path, ⟨hc, hr⟩ => by
    have hrR := ep1_children_access_read_eq_of_readIdem base len subOff subLen hlo hhi rest (childId + 1) path hr
    rcases path with _ | (_ | ⟨head, tail⟩)
    · have hcR := ep1_node_access_read_eq_of_readIdem base len subOff subLen hlo hhi c none hc
      unfold Node.accessChildren
      simp only [hcR, hrR, bind, Except.bind, pure, Except.pure]
    · have hcR := ep1_node_access_read_eq_of_readIdem base len subOff subLen hlo hhi c none hc
      unfold Node.accessChildren
      simp only [hcR, hrR, bind, Except.bind, pure, Except.pure]
    · cases heq : (head == childId)
      · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hc
        have hcR := ep1_node_access_read_eq_of_readIdem base len subOff subLen hlo hhi c none hc
        unfold Node.accessChildren
        simp only [heq, Bool.false_eq_true, ↓reduceIte, hcR, hrR, bind, Except.bind, pure, Except.pure]
      · simp only [heq, ↓reduceIte] at hc
        have hcR := ep1_node_access_read_eq_of_readIdem base len subOff subLen hlo hhi c (some tail) hc
        unfold Node.accessChildren
        simp only [heq, ↓reduceIte, hcR, hrR, bind, Except.bind, pure, Except.pure]

end

mutual

private theorem ep1_nodeReadIdem_subrange (base len subOff subLen : Nat)
    (hlo : base ≤ subOff) (hhi : subOff + subLen ≤ base + len) :
    ∀ (n : Gen.Node) (path : Option Gen.Path),
      ep1NodeReadIdem path base len n →
      ep1NodeReadIdem path subOff subLen n
  | ⟨children, _, _⟩, path, ⟨hperms, hcs⟩ =>
    ⟨fun i h1 h2 => hperms i (by omega) (by omega),
     ep1_childrenReadIdem_subrange base len subOff subLen hlo hhi children 0 path hcs⟩

private theorem ep1_childrenReadIdem_subrange (base len subOff subLen : Nat)
    (hlo : base ≤ subOff) (hhi : subOff + subLen ≤ base + len) :
    ∀ (cs : List Gen.Node) (childId : Int) (path : Option Gen.Path),
      ep1ChildrenReadIdem childId path base len cs →
      ep1ChildrenReadIdem childId path subOff subLen cs
  | [], _, _, _ => trivial
  | c :: rest, childId, path, ⟨hc, hr⟩ => by
    refine ⟨?_, ep1_childrenReadIdem_subrange base len subOff subLen hlo hhi rest (childId + 1) path hr⟩
    rcases path with _ | (_ | ⟨head, tail⟩)
    · exact ep1_nodeReadIdem_subrange base len subOff subLen hlo hhi c none hc
    · exact ep1_nodeReadIdem_subrange base len subOff subLen hlo hhi c none hc
    · cases heq : (head == childId)
      · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hc ⊢
        exact ep1_nodeReadIdem_subrange base len subOff subLen hlo hhi c none hc
      · simp only [heq, ↓reduceIte] at hc ⊢
        exact ep1_nodeReadIdem_subrange base len subOff subLen hlo hhi c (some tail) hc

end

/-! #### Multi-tag `SetDiscriminant → GetDiscriminant` & `Assign (Variant) → GetDiscriminant` (no `hp1`!) -/

/-- A `Discriminator` decision tree matches a variant's tagger list `tags` to discriminant `d`:
each `Branch` reached along the decision path reads an `(off, ty)` whose tag entry `(off, (ty, tagVal))`
was written by `tags`, whose integer codec round-trips `tagVal`, and which is not overwritten by any
later entry in `tags`. Covers `Known d` (0-tag single-variant enums), single-tag enums, and arbitrary
multi-level multi-tag enums. -/
inductive Ep1DiscrMatchesTags (M : Type) [Gen.Memory M]
    (tags : List (Gen.Offset × (Gen.IntType × Int))) : Gen.Discriminator → Int → Prop where
  | Known (d : Int) : Ep1DiscrMatchesTags M tags (.Known d) d
  | Branch (off : Gen.Offset) (ty : Gen.IntType) (fb : Gen.Discriminator)
      (children : List ((Int × Int) × Gen.Discriminator)) (tagVal d : Int)
      (pre suf : List (Gen.Offset × (Gen.IntType × Int)))
      (bs : List (Gen.AbstractByte (Gen.Memory.Provenance M))) :
      tags = pre ++ (off, (ty, tagVal)) :: suf →
      Type.encodeIntM (M := M) ty (.Int tagVal) = .ok bs →
      Type.decodeIntM (M := M) ty bs = .ok (some (.Int tagVal)) →
      (∀ t ∈ suf, off.bytes + ty.size.bytes ≤ t.1.bytes ∨ t.1.bytes + t.2.1.size.bytes ≤ off.bytes) →
      Ep1DiscrMatchesTags M tags (ep1NextDiscriminator children fb tagVal) d →
      Ep1DiscrMatchesTags M tags (.Branch off ty fb ⟨children⟩) d

private theorem ep1_list_set_idem {α : Type} (xs : List α) (i : Nat) (x : α) (hi : i < xs.length) :
    (xs.set i x).set i x = xs.set i x := by
  have hlt : i < (xs.set i x).length := by simpa [List.length_set] using hi
  have hget : x = (xs.set i x)[i]'hlt := by simp [List.getElem_set_self]
  conv => lhs; arg 3; rw [hget]
  exact List.set_getElem_self hlt

/-- Post-write tag readability invariant on `MachTB`: `basePtr + off` resolves in-bounds and
`TreeBorrowsMemory.load` reads `bs` while leaving `m.mem.memory` unchanged (both bytes and borrow
trees preserved). -/
private def ep1TagReadableTB (m : MachTB) (basePtr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (off : Gen.Offset) (ty : Gen.IntType) (bs : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) : Prop :=
  ∃ ptr, ptrOffsetInboundsM m basePtr (off.bytes : Int) = .ok ptr ∧
    (∀ (id : Gen.AllocId) (path : Gen.Path) (aOff : Size)
        (a : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra),
      BasicMemory.check_ptr m.mem.memory.mem ptr ty.size = .ok (some (id, path, aOff)) →
      listIndex m.mem.memory.mem.allocations id._0 "self.allocations[id.0]" = .ok a →
      subsliceWithLength a.data (aOff.bytes : Int) (ty.size.bytes : Int) = .ok bs ∧
      ep1NodeReadIdem (some path) aOff.bytes ty.size.bytes a.extra.root) ∧
    (BasicMemory.check_ptr m.mem.memory.mem ptr ty.size = .ok none → bs = []) ∧
    (∃ chk, BasicMemory.check_ptr m.mem.memory.mem ptr ty.size = .ok chk)

private theorem ep1_tagReadableTB_implies_load {m : MachTB}
    {basePtr : Gen.ThinPointer Gen.TreeBorrowsProvenance}
    {off : Gen.Offset} {ty : Gen.IntType} {bs : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)}
    (h : ep1TagReadableTB m basePtr off ty bs) :
    ∃ ptr, ptrOffsetInboundsM m basePtr (off.bytes : Int) = .ok ptr ∧
      TreeBorrowsMemory.load m.mem.memory ptr ty.size ⟨1⟩ = .ok (bs, m.mem.memory) := by
  obtain ⟨ptr, hpoi, hsome, hnone, chk, hchk⟩ := h
  refine ⟨ptr, hpoi, ?_⟩
  unfold TreeBorrowsMemory.load BasicMemory.load
  simp only [ep1_align_one_is_aligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    hchk, bind, Except.bind]
  cases chk with
  | none =>
    obtain rfl := hnone hchk
    rfl
  | some trip =>
    rcases trip with ⟨id, path, aOff⟩
    have hidxEx : ∃ a, listIndex m.mem.memory.mem.allocations id._0 "self.allocations[id.0]" = .ok a := by
      unfold BasicMemory.check_ptr at hchk
      split at hchk
      · cases ep1_pure_ok hchk
      · cases hpr : ptr.provenance with
        | none => simp [hpr, ub] at hchk
        | some ip =>
          simp only [hpr] at hchk
          obtain ⟨a, hidx, hchk⟩ := ep1_bind_ok hchk
          split at hchk
          · simp [ub] at hchk
          · split at hchk
            · simp [ub] at hchk
            · have hp := ep1_pure_ok hchk
              simp only [Option.some.injEq, Prod.mk.injEq] at hp
              rcases hp with ⟨rfl, _, _⟩
              exact ⟨a, hidx⟩
    obtain ⟨a, hidx⟩ := hidxEx
    obtain ⟨hsub, hidem⟩ := hsome id path aOff a hchk hidx
    obtain ⟨hidNN, hidLt, hgetA⟩ := ep1_listIndex_int_eq_getElem hidx
    have hnode : Node.access a.extra.root (some path) .Read aOff ty.size = .ok a.extra.root :=
      ep1_node_access_read_eq_of_readIdem aOff.bytes ty.size.bytes aOff.bytes ty.size.bytes
        (Nat.le_refl _) (Nat.le_refl _) a.extra.root (some path) hidem
    have hset : listSet m.mem.memory.mem.allocations id._0 a "set" = .ok m.mem.memory.mem.allocations := by
      rw [ep1_listSet_int_of_lt _ _ hidNN hidLt]
      congr 1
      conv => lhs; arg 3; rw [← hgetA]
      exact List.set_getElem_self hidLt
    simp only [hidx, hnode, hset, hsub, pure, Except.pure]

private theorem ep1_ptrOffsetInboundsM_addr_prov {M : Type} [Gen.Memory M] [MemoryOps M]
    {m : Gen.Machine M} {base ptr : Gen.ThinPointer (Gen.Memory.Provenance M)} {off : Int}
    (h : ptrOffsetInboundsM m base off = .ok ptr) :
    ptr.addr = base.addr + off ∧ ptr.provenance = base.provenance := by
  unfold ptrOffsetInboundsM at h
  obtain ⟨_, _, h⟩ := ep1_bind_ok h
  split at h
  · simp [specPanic] at h
  · split at h
    · simp [specPanic] at h
    · obtain rfl := ep1_pure_ok h
      exact ⟨rfl, rfl⟩

private theorem ep1_check_ptr_some_info {E A : Type}
    {mem : Gen.BasicMemory Gen.x86_64 E A} {ptr : Gen.ThinPointer (Gen.Provenance E)}
    {len : Size} {id : Gen.AllocId} {pe : E} {aOff : Size}
    (h : BasicMemory.check_ptr mem ptr len = .ok (some (id, pe, aOff))) :
    len.bytes ≠ 0 ∧ ptr.provenance = some (id, pe) ∧
    ∃ a, listIndex mem.allocations id._0 "self.allocations[id.0]" = .ok a ∧
      (aOff.bytes : Int) = ptr.addr - a.addr := by
  unfold BasicMemory.check_ptr at h
  split at h
  · cases ep1_pure_ok h
  · rename_i hnz
    cases hpr : ptr.provenance with
    | none => simp [hpr, ub] at h
    | some ip =>
      rcases ip with ⟨id', pe'⟩
      simp only [hpr] at h
      obtain ⟨a, hidx, h⟩ := ep1_bind_ok h
      split at h
      · simp [ub] at h
      · split at h
        · simp [ub] at h
        · rename_i hnotOob
          have hp := ep1_pure_ok h
          simp only [Option.some.injEq, Prod.mk.injEq] at hp
          rcases hp with ⟨rfl, rfl, hoff⟩
          have hnn : (0 : Int) ≤ (ptr.addr : Int) - (a.addr : Int) :=
            Int.not_lt.mp (fun hlt => hnotOob (Or.inl hlt))
          have hbytes : (aOff.bytes : Int) = (ptr.addr : Int) - (a.addr : Int) := by
            cases hoff
            exact Int.toNat_of_nonneg hnn
          exact ⟨hnz, rfl, a, hidx, hbytes⟩

private theorem ep1_store_step_tb {m m' : MachTB}
    {basePtr : Gen.ThinPointer Gen.TreeBorrowsProvenance}
    {off' : Gen.Offset} {ty' : Gen.IntType} {val' : Int}
    {bs' : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)}
    (henc : Type.encodeIntM (M := TBM) ty' (.Int val') = .ok bs')
    (hstep : (do
      let ptr ← ptrOffsetInboundsM m basePtr (off'.bytes : Int)
      let cm ← ConcurrentMemory.store m.mem ptr bs' ⟨1⟩ .None
      pure { m with mem := cm }) = .ok m') :
    ep1CurFrameViewM m' = ep1CurFrameViewM m ∧
    ep1AllocShape m'.mem.memory.mem.allocations = ep1AllocShape m.mem.memory.mem.allocations ∧
    ep1TagReadableTB m' basePtr off' ty' bs' ∧
    (∀ off ty bs,
      (off.bytes + ty.size.bytes ≤ off'.bytes ∨ off'.bytes + ty'.size.bytes ≤ off.bytes) →
      ep1TagReadableTB m basePtr off ty bs →
      ep1TagReadableTB m' basePtr off ty bs) := by
  obtain ⟨ptr', hpoi', hstep⟩ := ep1_bind_ok hstep
  obtain ⟨cm', hstore, hpRet⟩ := ep1_bind_ok hstep
  obtain rfl := ep1_pure_ok hpRet
  unfold ConcurrentMemory.store at hstore
  obtain ⟨tbm', htbStore, hcmRet⟩ := ep1_bind_ok hstore
  obtain rfl := ep1_pure_ok hcmRet
  change TreeBorrowsMemory.store m.mem.memory ptr' bs' ⟨1⟩ = .ok tbm' at htbStore
  unfold TreeBorrowsMemory.store at htbStore
  obtain ⟨bm', hbmStore, htbRet⟩ := ep1_bind_ok htbStore
  obtain rfl := ep1_pure_ok htbRet
  have hshape : ep1AllocShape bm'.allocations = ep1AllocShape m.mem.memory.mem.allocations :=
    ep1_BasicMemory_store_shape hbmStore
  have htagLen : bs'.length = ty'.size.bytes := ep1_encodeIntM_length henc
  have hszEq : ty'.size = ⟨bs'.length⟩ := by
    rcases hs : ty'.size with ⟨b⟩
    rw [hs] at htagLen
    exact congrArg Size.mk htagLen.symm
  let cmNext : Gen.ConcurrentMemory TBM :=
    { memory := { m.mem.memory with mem := bm' }
      accesses := m.mem.accesses ++ [⟨.Store, .None, ptr'.addr, ⟨bs'.length⟩⟩] }
  have hpoiPres : ∀ p o, ptrOffsetInboundsM { m with mem := cmNext } p o =
      ptrOffsetInboundsM m p o :=
    ep1_ptrOffsetInboundsM_same_shape_tb hshape
  have hchkPres : ∀ p s, BasicMemory.check_ptr bm' p s = BasicMemory.check_ptr m.mem.memory.mem p s :=
    ep1_check_ptr_same_shape m.mem.memory.mem bm' hshape.symm
  unfold BasicMemory.store at hbmStore
  simp only [ep1_align_one_is_aligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hbmStore
  obtain ⟨chk', hchk0', hbmStore⟩ := ep1_bind_ok hbmStore
  refine ⟨rfl, hshape, ?_, ?_⟩
  · -- Establish ep1TagReadableTB for the newly written tag (off', ty', bs')
    refine ⟨ptr', by rw [hpoiPres]; exact hpoi', ?_, ?_, chk', by rw [hchkPres, hszEq]; exact hchk0'⟩
    · intro id path aOff a hchk1 hidx1
      rw [hchkPres, hszEq, hchk0'] at hchk1
      cases chk' with
      | none => cases hchk1
      | some trip =>
        rcases trip with ⟨id', path', aOff'⟩
        simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hchk1
        obtain ⟨h1, h2, h3⟩ := hchk1
        subst h1; subst h2; subst h3
        obtain ⟨alloc, hidx0, hbmStore⟩ := ep1_bind_ok hbmStore
        obtain ⟨extra', hextra, hbmStore⟩ := ep1_bind_ok hbmStore
        obtain ⟨root', hnodeW, hretE⟩ := ep1_bind_ok hextra
        obtain rfl := ep1_pure_ok hretE
        obtain ⟨data', hws, hbmStore⟩ := ep1_bind_ok hbmStore
        obtain ⟨allocs', hset', hbmRet⟩ := ep1_bind_ok hbmStore
        obtain rfl := ep1_pure_ok hbmRet
        obtain ⟨hidNN, hidLt, _⟩ := ep1_listIndex_int_eq_getElem hidx0
        have hallocsEq : allocs' = m.mem.memory.mem.allocations.set id'._0.toNat
            { alloc with data := data', extra := { root := root' } } := by
          unfold listSet at hset'
          split at hset'
          · exact (ep1_pure_ok hset').symm
          · simp [specPanic] at hset'
        subst hallocsEq
        have hidLt1 : id'._0.toNat < (m.mem.memory.mem.allocations.set id'._0.toNat
            { alloc with data := data', extra := { root := root' } }).length := by
          simpa [List.length_set] using hidLt
        have haEq : a = { alloc with data := data', extra := { root := root' } } := by
          rw [ep1_listIndex_int_of_getElem _ hidNN hidLt1, List.getElem_set_self] at hidx1
          exact Except.ok.inj hidx1.symm
        subst haEq
        refine ⟨by rw [← htagLen]; exact (ep1_writeSubsliceAtIndex_subslice_recover hws).2, ?_⟩
        rw [← htagLen]
        exact ep1_node_access_write_establishes_readIdem alloc.extra.root root' (some path') aOff'.bytes bs'.length hnodeW
    · intro hnone
      rw [hchkPres, hszEq, hchk0'] at hnone
      cases chk' with
      | some _ => cases hnone
      | none =>
        have hlen0 : bs'.length = 0 := by
          unfold BasicMemory.check_ptr at hchk0'
          split at hchk0'
          · assumption
          · cases hpr : ptr'.provenance with
            | none => simp [hpr, ub] at hchk0'
            | some ip =>
              simp only [hpr] at hchk0'
              obtain ⟨_, _, hchk0'⟩ := ep1_bind_ok hchk0'
              split at hchk0'
              · simp [ub] at hchk0'
              · split at hchk0'
                · simp [ub] at hchk0'
                · cases ep1_pure_ok hchk0'
        exact List.eq_nil_of_length_eq_zero hlen0
  · -- Preserve ep1TagReadableTB for every disjoint earlier tag (off, ty, bs)
    intro off ty bs hdisj ⟨ptr, hpoi, hsome, hnone, chk, hchk⟩
    refine ⟨ptr, by rw [hpoiPres]; exact hpoi, ?_, fun hn => hnone (by rwa [hchkPres] at hn),
      chk, by rw [hchkPres]; exact hchk⟩
    intro id path aOff a hchk1 hidx1
    rw [hchkPres] at hchk1
    cases chk' with
    | none =>
      obtain rfl := ep1_pure_ok hbmStore
      exact hsome id path aOff a hchk1 hidx1
    | some trip =>
      rcases trip with ⟨id', path', aOff'⟩
      obtain ⟨alloc, hidx0, hbmStore⟩ := ep1_bind_ok hbmStore
      obtain ⟨extra', hextra, hbmStore⟩ := ep1_bind_ok hbmStore
      obtain ⟨root', hnodeW, hretE⟩ := ep1_bind_ok hextra
      obtain rfl := ep1_pure_ok hretE
      obtain ⟨data', hws, hbmStore⟩ := ep1_bind_ok hbmStore
      obtain ⟨allocs', hset', hbmRet⟩ := ep1_bind_ok hbmStore
      obtain rfl := ep1_pure_ok hbmRet
      obtain ⟨hidNN', hidLt', hget0⟩ := ep1_listIndex_int_eq_getElem hidx0
      have hallocsEq : allocs' = m.mem.memory.mem.allocations.set id'._0.toNat
          { alloc with data := data', extra := { root := root' } } := by
        unfold listSet at hset'
        split at hset'
        · exact (ep1_pure_ok hset').symm
        · simp [specPanic] at hset'
      subst hallocsEq
      obtain ⟨hidNN, hidLt1, hget1⟩ := ep1_listIndex_int_eq_getElem hidx1
      have hidLt : id._0.toNat < m.mem.memory.mem.allocations.length := by
        simpa [List.length_set] using hidLt1
      by_cases hsameId : id'._0.toNat = id._0.toNat
      · have haEq : a = { alloc with data := data', extra := { root := root' } } := by
          rw [← hget1]
          simp only [List.getElem_set, hsameId, ↓reduceIte]
        subst haEq
        have hgetSame : m.mem.memory.mem.allocations[id._0.toNat]'hidLt = alloc := by
          have hq : m.mem.memory.mem.allocations[id._0.toNat]? = m.mem.memory.mem.allocations[id'._0.toNat]? := by
            rw [hsameId]
          rw [List.getElem?_eq_getElem hidLt, List.getElem?_eq_getElem hidLt', hget0] at hq
          exact Option.some.inj hq
        have hidxPrev : listIndex m.mem.memory.mem.allocations id._0 "self.allocations[id.0]" = .ok alloc := by
          rw [ep1_listIndex_int_of_getElem _ hidNN hidLt, hgetSame]
        obtain ⟨hsubPrev, hidemPrev⟩ := hsome id path aOff alloc hchk1 hidxPrev
        obtain ⟨haddrP, hprovP⟩ := ep1_ptrOffsetInboundsM_addr_prov hpoi
        obtain ⟨haddrP', hprovP'⟩ := ep1_ptrOffsetInboundsM_addr_prov hpoi'
        obtain ⟨_, _, a1, hidxA1, haOffEq⟩ := ep1_check_ptr_some_info hchk1
        obtain ⟨_, _, a2, hidxA2, haOffEq'⟩ := ep1_check_ptr_some_info hchk0'
        rw [hidxPrev] at hidxA1; cases hidxA1
        rw [hidx0] at hidxA2; cases hidxA2
        have hdisjAlloc : aOff'.bytes + bs'.length ≤ aOff.bytes ∨ aOff.bytes + ty.size.bytes ≤ aOff'.bytes := by
          rw [htagLen]
          have h1 : (aOff.bytes : Int) = basePtr.addr + (off.bytes : Int) - alloc.addr := by
            rw [haOffEq, haddrP]
          have h2 : (aOff'.bytes : Int) = basePtr.addr + (off'.bytes : Int) - alloc.addr := by
            rw [haOffEq', haddrP']
          omega
        refine ⟨?_, ?_⟩
        · rw [ep1_writeSubsliceAtIndex_disjoint_preserves hws hdisjAlloc]
          exact hsubPrev
        · exact ep1_node_access_disjoint_preserves_readIdem aOff.bytes ty.size.bytes aOff'.bytes bs'.length
            (by omega) alloc.extra.root root' (some path) (some path') .Write hnodeW hidemPrev
      · have haGet : m.mem.memory.mem.allocations[id._0.toNat]'hidLt = a := by
          rw [← hget1, List.getElem_set_ne hsameId]
        have hidxPrev : listIndex m.mem.memory.mem.allocations id._0 "self.allocations[id.0]" = .ok a := by
          rw [ep1_listIndex_int_of_getElem _ hidNN hidLt, haGet]
        exact hsome id path aOff a hchk1 hidxPrev

private theorem ep1_encodeDiscriminantM_fold_tb (basePtr : Gen.ThinPointer Gen.TreeBorrowsProvenance) :
    ∀ (tags : List (Gen.Offset × (Gen.IntType × Int))) (m m1 : MachTB),
      encodeDiscriminantM (M := TBM)
        (fun m offset bytes => do
          let ptr ← ptrOffsetInboundsM m basePtr (offset.bytes : Int)
          let cm ← ConcurrentMemory.store m.mem ptr bytes ⟨1⟩ .None
          pure { m with mem := cm })
        ⟨tags⟩ m = .ok m1 →
      ep1CurFrameViewM m1 = ep1CurFrameViewM m ∧
      ep1AllocShape m1.mem.memory.mem.allocations = ep1AllocShape m.mem.memory.mem.allocations ∧
      (∀ off ty tagVal pre suf bs,
        tags = pre ++ (off, (ty, tagVal)) :: suf →
        Type.encodeIntM (M := TBM) ty (.Int tagVal) = .ok bs →
        (∀ t ∈ suf, off.bytes + ty.size.bytes ≤ t.1.bytes ∨ t.1.bytes + t.2.1.size.bytes ≤ off.bytes) →
        ep1TagReadableTB m1 basePtr off ty bs)
  | [], m, m1, h => by
    unfold encodeDiscriminantM at h
    obtain rfl := ep1_pure_ok h
    refine ⟨rfl, rfl, fun _ _ _ pre _ _ hEq => ?_⟩
    cases pre <;> simp at hEq
  | (off0, (ty0, val0)) :: rest, m, m1, h => by
    unfold encodeDiscriminantM at h
    simp only [List.foldlM_cons] at h
    obtain ⟨mMid, hstep0, hrest⟩ := ep1_bind_ok h
    obtain ⟨bs0, henc0, hst0⟩ := ep1_bind_ok hstep0
    obtain ⟨hf0, hs0, hread0, hpres0⟩ := ep1_store_step_tb henc0 hst0
    have hrest' : encodeDiscriminantM (M := TBM)
        (fun m offset bytes => do
          let ptr ← ptrOffsetInboundsM m basePtr (offset.bytes : Int)
          let cm ← ConcurrentMemory.store m.mem ptr bytes ⟨1⟩ .None
          pure { m with mem := cm })
        ⟨rest⟩ mMid = .ok m1 := hrest
    obtain ⟨hfR, hsR, hreadR⟩ := ep1_encodeDiscriminantM_fold_tb basePtr rest mMid m1 hrest'
    refine ⟨hfR.trans hf0, hsR.trans hs0, ?_⟩
    intro off ty tagVal pre suf bs hEq henc hdisj
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hEq
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hEq
      subst h1; subst h2; subst h3; subst h4
      rw [henc0] at henc; cases henc
      -- Carry hread0 across all steps in `suf`
      have hcarry : ∀ (xs : List (Gen.Offset × (Gen.IntType × Int))) (s s' : MachTB),
          encodeDiscriminantM (M := TBM)
            (fun m offset bytes => do
              let ptr ← ptrOffsetInboundsM m basePtr (offset.bytes : Int)
              let cm ← ConcurrentMemory.store m.mem ptr bytes ⟨1⟩ .None
              pure { m with mem := cm })
            ⟨xs⟩ s = .ok s' →
          (∀ t ∈ xs, off0.bytes + ty0.size.bytes ≤ t.1.bytes ∨ t.1.bytes + t.2.1.size.bytes ≤ off0.bytes) →
          ep1TagReadableTB s basePtr off0 ty0 bs0 →
          ep1TagReadableTB s' basePtr off0 ty0 bs0 := by
        intro xs
        induction xs with
        | nil =>
          intro s s' hs _ hr
          unfold encodeDiscriminantM at hs
          obtain rfl := ep1_pure_ok hs; exact hr
        | cons t ts ih =>
          intro s s' hs hdj hr
          unfold encodeDiscriminantM at hs
          simp only [List.foldlM_cons] at hs
          obtain ⟨sMid, hst, hts⟩ := ep1_bind_ok hs
          obtain ⟨bsT, hencT, hstT⟩ := ep1_bind_ok hst
          obtain ⟨_, _, _, hpresT⟩ := ep1_store_step_tb hencT hstT
          exact ih sMid s' hts (fun x hx => hdj x (List.mem_cons_of_mem _ hx))
            (hpresT off0 ty0 bs0 (hdj t (List.mem_cons_self ..)) hr)
      exact hcarry rest mMid m1 hrest' hdisj hread0
    | cons hd tl =>
      simp only [List.cons_append, List.cons.injEq] at hEq
      exact hreadR off ty tagVal tl suf bs hEq.2 henc hdisj

private theorem ep1_decodeDiscriminantM_of_matches_tb (m1 : MachTB)
    (basePtr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (tags : List (Gen.Offset × (Gen.IntType × Int)))
    (hreadable : ∀ off ty tagVal pre suf bs,
      tags = pre ++ (off, (ty, tagVal)) :: suf →
      Type.encodeIntM (M := TBM) ty (.Int tagVal) = .ok bs →
      (∀ t ∈ suf, off.bytes + ty.size.bytes ≤ t.1.bytes ∨ t.1.bytes + t.2.1.size.bytes ≤ off.bytes) →
      ep1TagReadableTB m1 basePtr off ty bs)
    {discr : Gen.Discriminator} {d : Int}
    (hmatch : Ep1DiscrMatchesTags TBM tags discr d) :
    ∀ (m : MachTB), m.mem.memory = m1.mem.memory →
      let acc := fun (s : MachTB) (idx : Gen.Offset) (size : Size) => do
        let ptr ← ptrOffsetInboundsM s basePtr (idx.bytes : Int)
        let (bytes, cm) ← ConcurrentMemory.load s.mem ptr size ⟨1⟩ .None
        pure (bytes, { s with mem := cm })
      ∃ m2, decodeDiscriminantM (M := TBM) acc discr m = .ok (some d, m2) ∧
        m2.mem.memory = m1.mem.memory := by
  induction hmatch with
  | Known d =>
    intro m hmem
    exact ⟨m, rfl, hmem⟩
  | Branch off ty fb children tagVal d pre suf bs hEq henc hdec hdisj hnext ih =>
    intro m hmem
    obtain ⟨ptr, hpoi1, hload1⟩ := ep1_tagReadableTB_implies_load (hreadable off ty tagVal pre suf bs hEq henc hdisj)
    have hpoiM : ptrOffsetInboundsM m basePtr (off.bytes : Int) = .ok ptr := by
      have hsh : ep1AllocShape m.mem.memory.mem.allocations = ep1AllocShape m1.mem.memory.mem.allocations := by
        rw [hmem]
      rw [ep1_ptrOffsetInboundsM_same_shape_tb hsh]; exact hpoi1
    have hloadM : TreeBorrowsMemory.load m.mem.memory ptr ty.size ⟨1⟩ = .ok (bs, m.mem.memory) := by
      rw [hmem]; exact hload1
    let cmNext : Gen.ConcurrentMemory TBM :=
      { memory := m.mem.memory, accesses := m.mem.accesses ++ [⟨.Load, .None, ptr.addr, ty.size⟩] }
    have hcmLoad : ConcurrentMemory.load m.mem ptr ty.size ⟨1⟩ .None = .ok (bs, cmNext) :=
      ep1_concurrent_load_of_mem_load m.mem ptr ty.size ⟨1⟩ .None bs m.mem.memory hloadM
    let mNext : MachTB := { m with mem := cmNext }
    obtain ⟨m2, hrec, hmem2⟩ := ih mNext hmem
    refine ⟨m2, ?_, hmem2⟩
    unfold decodeDiscriminantM
    simp only [hpoiM, hcmLoad, bind, Except.bind, pure, Except.pure, hdec]
    rw [ep1_decodeDiscriminantChildrenM_eq_find_map]
    exact hrec

/-- **Universal multi-tag `SetDiscriminant → GetDiscriminant` roundtrip on `MachTB` (NO `hp1`, NO `m0`!):**
for **any** structural place chain (`Ep1PlaceChain`, i.e., arbitrary `Local`/`Field`/`Downcast`
nesting — eliminating the `hp1` premise of A2's single-tag theorem!) and **any** multi-tag variant
whose `tagger` matches an arbitrary-depth `Discriminator` decision tree (`Ep1DiscrMatchesTags`,
covering 0-tag `Known`, 1-tag, and multi-level niche enums): whenever `SetDiscriminant` succeeds
yielding `m1`, `GetDiscriminant` on `m1` **unconditionally succeeds** (with ZERO extra address/size
bounds hypotheses), returns `(.Int d, .Int dty)`, and leaves `m2.mem.memory = m1.mem.memory` (every
Tree Borrows permission unchanged). -/
theorem ep1_setDiscriminant_multitag_then_getDiscriminant_tb
    (m m1 : MachTB) (place : Gen.PlaceExpr) (hc : Ep1PlaceChain place)
    (rp : Gen.Place TBM) (variants : Map Int Gen.Variant) (dty : Gen.IntType)
    (discr : Gen.Discriminator) (sz : Size) (al : Align) (d : Int) (var : Gen.Variant)
    (hp : evalPlaceM m place = .ok ((rp, .Enum variants dty discr sz al), m))
    (hvar : mapGet variants d = some var)
    (hmatch : Ep1DiscrMatchesTags TBM var.tagger.entries discr d)
    (hset : evalStatementM m (.SetDiscriminant place d) = .ok m1) :
    ∃ m2, evalValueM m1 (.GetDiscriminant place) = .ok ((.Int d, .Int dty), m2) ∧
      m2.mem.memory = m1.mem.memory := by
  simp only [evalStatementM, evalSetDiscriminantM] at hset
  rw [hp] at hset
  dsimp only [bind, Except.bind] at hset
  have hal : rp.aligned = true := by
    cases h : rp.aligned
    · simp [h, ub] at hset
    · rfl
  simp only [hal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hvar] at hset
  obtain ⟨hf1, hs1, hreadable⟩ := ep1_encodeDiscriminantM_fold_tb rp.ptr.thin_pointer var.tagger.entries m m1 hset
  have hp1 : evalPlaceM m1 place = .ok ((rp, .Enum variants dty discr sz al), m1) := by
    rw [(ep1_evalPlaceM_chain_same_shape place hc).1 m m1 hf1 hs1, hp]
  obtain ⟨m2, hdd, hmem2⟩ :=
    ep1_decodeDiscriminantM_of_matches_tb m1 rp.ptr.thin_pointer var.tagger.entries hreadable hmatch m1 rfl
  refine ⟨m2, ?_, hmem2⟩
  rw [(ep1_evalValueM_getDiscriminant_complete_spec (M := TBM)).1 m1 m1 place rp variants dty discr sz al hp1 hal]
  unfold ep1GetDiscriminantCore
  dsimp only
  rw [hdd]; rfl

private def ep1TagReadableBM (m : Mach) (basePtr : Ptr)
    (off : Gen.Offset) (ty : Gen.IntType) (bs : List Byte) : Prop :=
  ∃ ptr, ptrOffsetInboundsM (M := BM) m basePtr (off.bytes : Int) = .ok ptr ∧
    (∀ (id : Gen.AllocId) (aOff : Size) (a : Gen.Allocation Unit Unit),
      BM.check_ptr m.mem.memory ptr ty.size = .ok (some (id, (), aOff)) →
      listIndex m.mem.memory.allocations id._0 "self.allocations[id.0]" = .ok a →
      subsliceWithLength a.data (aOff.bytes : Int) (ty.size.bytes : Int) = .ok bs) ∧
    (BM.check_ptr m.mem.memory ptr ty.size = .ok none → bs = []) ∧
    (∃ chk, BM.check_ptr m.mem.memory ptr ty.size = .ok chk)

private theorem ep1_tagReadableBM_implies_load {m : Mach} {basePtr : Ptr}
    {off : Gen.Offset} {ty : Gen.IntType} {bs : List Byte}
    (h : ep1TagReadableBM m basePtr off ty bs) :
    ∃ ptr, ptrOffsetInboundsM (M := BM) m basePtr (off.bytes : Int) = .ok ptr ∧
      BM.load m.mem.memory ptr ty.size ⟨1⟩ = .ok (bs, m.mem.memory) := by
  obtain ⟨ptr, hpoi, hsome, hnone, chk, hchk⟩ := h
  refine ⟨ptr, hpoi, ?_⟩
  unfold BM.load
  simp only [ep1_align_one_is_aligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    hchk, bind, Except.bind]
  cases chk with
  | none =>
    obtain rfl := hnone hchk
    rfl
  | some trip =>
    rcases trip with ⟨id, pu, aOff⟩
    cases pu
    have hchkB : BasicMemory.check_ptr m.mem.memory ptr ty.size = .ok (some (id, (), aOff)) := by
      rwa [← ep1_BM_check_ptr_eq_BasicMemory]
    obtain ⟨_, _, a, hidx, _⟩ := ep1_check_ptr_some_info hchkB
    have hsub := hsome id aOff a hchk hidx
    obtain ⟨hidNN, hidLt, hgetA⟩ := ep1_listIndex_int_eq_getElem hidx
    have hset : listSet m.mem.memory.allocations id._0 a "set" = .ok m.mem.memory.allocations := by
      rw [ep1_listSet_int_of_lt _ _ hidNN hidLt]
      congr 1
      conv => lhs; arg 3; rw [← hgetA]
      exact List.set_getElem_self hidLt
    simp only [hidx, hset, hsub, pure, Except.pure]

private theorem ep1_BM_store_shape {mem mem' : BM} {ptr : Ptr} {bytes : List Byte} {align : Align}
    (h : BM.store mem ptr bytes align = .ok mem') :
    ep1AllocShape mem'.allocations = ep1AllocShape mem.allocations := by
  unfold BM.store at h
  split at h
  · simp [ub] at h
  · obtain ⟨chk, _, h⟩ := ep1_bind_ok h
    cases chk with
    | none => obtain rfl := ep1_pure_ok h; rfl
    | some trip =>
      rcases trip with ⟨id, _, _⟩
      obtain ⟨alloc, hidx, h⟩ := ep1_bind_ok h
      obtain ⟨data', hws, h⟩ := ep1_bind_ok h
      obtain ⟨allocs', hset, hp⟩ := ep1_bind_ok h
      obtain rfl := ep1_pure_ok hp
      obtain ⟨_, hi, hget⟩ := ep1_listIndex_int_eq_getElem hidx
      have hallocs : allocs' = mem.allocations.set id._0.toNat { alloc with data := data' } := by
        unfold listSet at hset
        split at hset
        · exact (ep1_pure_ok hset).symm
        · simp [specPanic] at hset
      subst hallocs
      have hlenData : data'.length = alloc.data.length := writeSubsliceAtIndex_length hws
      unfold ep1AllocShape
      rw [List.map_set]
      have hsame : (data'.length, alloc.addr, alloc.live) =
          (mem.allocations.map (fun a => (a.data.length, a.addr, a.live)))[id._0.toNat]'(by simpa using hi) := by
        simp only [List.getElem_map, hget, hlenData]
      exact (congrArg (fun v => (mem.allocations.map _).set id._0.toNat v) hsame).trans
        (List.set_getElem_self (by simpa using hi))

private theorem ep1_store_step_bm {m m' : Mach} {basePtr : Ptr}
    {off' : Gen.Offset} {ty' : Gen.IntType} {val' : Int} {bs' : List Byte}
    (henc : Type.encodeIntM (M := BM) ty' (.Int val') = .ok bs')
    (hstep : (do
      let ptr ← ptrOffsetInboundsM (M := BM) m basePtr (off'.bytes : Int)
      let cm ← ConcurrentMemory.store (M := BM) m.mem ptr bs' ⟨1⟩ .None
      pure { m with mem := cm }) = .ok m') :
    ep1CurFrameViewM (M := BM) m' = ep1CurFrameViewM (M := BM) m ∧
    ep1AllocShape m'.mem.memory.allocations = ep1AllocShape m.mem.memory.allocations ∧
    ep1TagReadableBM m' basePtr off' ty' bs' ∧
    (∀ off ty bs,
      (off.bytes + ty.size.bytes ≤ off'.bytes ∨ off'.bytes + ty'.size.bytes ≤ off.bytes) →
      ep1TagReadableBM m basePtr off ty bs →
      ep1TagReadableBM m' basePtr off ty bs) := by
  obtain ⟨ptr', hpoi', hstep⟩ := ep1_bind_ok hstep
  obtain ⟨cm', hstore, hpRet⟩ := ep1_bind_ok hstep
  obtain rfl := ep1_pure_ok hpRet
  unfold ConcurrentMemory.store at hstore
  obtain ⟨bm', hbmStore, hcmRet⟩ := ep1_bind_ok hstore
  obtain rfl := ep1_pure_ok hcmRet
  change BM.store m.mem.memory ptr' bs' ⟨1⟩ = .ok bm' at hbmStore
  have hshape : ep1AllocShape bm'.allocations = ep1AllocShape m.mem.memory.allocations :=
    ep1_BM_store_shape hbmStore
  have htagLen : bs'.length = ty'.size.bytes := ep1_encodeIntM_length henc
  have hszEq : ty'.size = ⟨bs'.length⟩ := by
    rcases hs : ty'.size with ⟨b⟩
    rw [hs] at htagLen
    exact congrArg Size.mk htagLen.symm
  let cmNext : Gen.ConcurrentMemory BM :=
    { memory := bm'
      accesses := m.mem.accesses ++ [⟨.Store, .None, ptr'.addr, ⟨bs'.length⟩⟩] }
  have hpoiPres : ∀ p o, ptrOffsetInboundsM (M := BM) { m with mem := cmNext } p o =
      ptrOffsetInboundsM (M := BM) m p o := fun p o => by
    rw [ep1_ptrOffsetInboundsM_bm_eq, ep1_ptrOffsetInboundsM_bm_eq]
    exact ep1_ptrOffsetInbounds_same_shape_bm hshape p o
  have hchkPres : ∀ p s, BM.check_ptr bm' p s = BM.check_ptr m.mem.memory p s := fun p s => by
    rw [ep1_BM_check_ptr_eq_BasicMemory, ep1_BM_check_ptr_eq_BasicMemory]
    exact ep1_check_ptr_same_shape m.mem.memory bm' hshape.symm p s
  unfold BM.store at hbmStore
  simp only [ep1_align_one_is_aligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hbmStore
  obtain ⟨chk', hchk0', hbmStore⟩ := ep1_bind_ok hbmStore
  refine ⟨rfl, hshape, ?_, ?_⟩
  · refine ⟨ptr', by rw [hpoiPres]; exact hpoi', ?_, ?_, chk', by rw [hchkPres, hszEq]; exact hchk0'⟩
    · intro id aOff a hchk1 hidx1
      rw [hchkPres, hszEq, hchk0'] at hchk1
      cases chk' with
      | none => cases hchk1
      | some trip =>
        rcases trip with ⟨id', pu', aOff'⟩
        cases pu'
        simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hchk1
        obtain ⟨h1, _, h3⟩ := hchk1
        subst h1; subst h3
        obtain ⟨alloc, hidx0, hbmStore⟩ := ep1_bind_ok hbmStore
        obtain ⟨data', hws, hbmStore⟩ := ep1_bind_ok hbmStore
        obtain ⟨allocs', hset', hbmRet⟩ := ep1_bind_ok hbmStore
        obtain rfl := ep1_pure_ok hbmRet
        obtain ⟨hidNN, hidLt, _⟩ := ep1_listIndex_int_eq_getElem hidx0
        have hallocsEq : allocs' = m.mem.memory.allocations.set id'._0.toNat { alloc with data := data' } := by
          unfold listSet at hset'
          split at hset'
          · exact (ep1_pure_ok hset').symm
          · simp [specPanic] at hset'
        subst hallocsEq
        have hidLt1 : id'._0.toNat < (m.mem.memory.allocations.set id'._0.toNat { alloc with data := data' }).length := by
          simpa [List.length_set] using hidLt
        have haEq : a = { alloc with data := data' } := by
          rw [ep1_listIndex_int_of_getElem _ hidNN hidLt1, List.getElem_set_self] at hidx1
          exact Except.ok.inj hidx1.symm
        subst haEq
        rw [← htagLen]
        exact (ep1_writeSubsliceAtIndex_subslice_recover hws).2
    · intro hnone
      rw [hchkPres, hszEq, hchk0'] at hnone
      cases chk' with
      | some _ => cases hnone
      | none =>
        have hlen0 : bs'.length = 0 := by
          unfold BM.check_ptr at hchk0'
          split at hchk0'
          · assumption
          · cases hpr : ptr'.provenance with
            | none => simp [hpr, ub] at hchk0'
            | some ip =>
              simp only [hpr] at hchk0'
              obtain ⟨_, _, hchk0'⟩ := ep1_bind_ok hchk0'
              split at hchk0'
              · simp [ub] at hchk0'
              · split at hchk0'
                · simp [ub] at hchk0'
                · cases ep1_pure_ok hchk0'
        exact List.eq_nil_of_length_eq_zero hlen0
  · intro off ty bs hdisj ⟨ptr, hpoi, hsome, hnone, chk, hchk⟩
    refine ⟨ptr, by rw [hpoiPres]; exact hpoi, ?_, fun hn => hnone (by rwa [hchkPres] at hn),
      chk, by rw [hchkPres]; exact hchk⟩
    intro id aOff a hchk1 hidx1
    rw [hchkPres] at hchk1
    cases chk' with
    | none =>
      obtain rfl := ep1_pure_ok hbmStore
      exact hsome id aOff a hchk1 hidx1
    | some trip =>
      rcases trip with ⟨id', pu', aOff'⟩
      cases pu'
      obtain ⟨alloc, hidx0, hbmStore⟩ := ep1_bind_ok hbmStore
      obtain ⟨data', hws, hbmStore⟩ := ep1_bind_ok hbmStore
      obtain ⟨allocs', hset', hbmRet⟩ := ep1_bind_ok hbmStore
      obtain rfl := ep1_pure_ok hbmRet
      obtain ⟨hidNN', hidLt', hget0⟩ := ep1_listIndex_int_eq_getElem hidx0
      have hallocsEq : allocs' = m.mem.memory.allocations.set id'._0.toNat { alloc with data := data' } := by
        unfold listSet at hset'
        split at hset'
        · exact (ep1_pure_ok hset').symm
        · simp [specPanic] at hset'
      subst hallocsEq
      obtain ⟨hidNN, hidLt1, hget1⟩ := ep1_listIndex_int_eq_getElem hidx1
      have hidLt : id._0.toNat < m.mem.memory.allocations.length := by
        simpa [List.length_set] using hidLt1
      by_cases hsameId : id'._0.toNat = id._0.toNat
      · have haEq : a = { alloc with data := data' } := by
          rw [← hget1]
          simp only [List.getElem_set, hsameId, ↓reduceIte]
        subst haEq
        have hgetSame : m.mem.memory.allocations[id._0.toNat]'hidLt = alloc := by
          have hq : m.mem.memory.allocations[id._0.toNat]? = m.mem.memory.allocations[id'._0.toNat]? := by
            rw [hsameId]
          rw [List.getElem?_eq_getElem hidLt, List.getElem?_eq_getElem hidLt', hget0] at hq
          exact Option.some.inj hq
        have hidxPrev : listIndex m.mem.memory.allocations id._0 "self.allocations[id.0]" = .ok alloc := by
          rw [ep1_listIndex_int_of_getElem _ hidNN hidLt, hgetSame]
        have hsubPrev := hsome id aOff alloc hchk1 hidxPrev
        obtain ⟨haddrP, _⟩ := ep1_ptrOffsetInboundsM_addr_prov hpoi
        obtain ⟨haddrP', _⟩ := ep1_ptrOffsetInboundsM_addr_prov hpoi'
        have hchk1B : BasicMemory.check_ptr m.mem.memory ptr ty.size = .ok (some (id, (), aOff)) := by
          rwa [← ep1_BM_check_ptr_eq_BasicMemory]
        have hchk0B : BasicMemory.check_ptr m.mem.memory ptr' ⟨bs'.length⟩ = .ok (some (id', (), aOff')) := by
          rwa [← ep1_BM_check_ptr_eq_BasicMemory]
        obtain ⟨_, _, a1, hidxA1, haOffEq⟩ := ep1_check_ptr_some_info hchk1B
        obtain ⟨_, _, a2, hidxA2, haOffEq'⟩ := ep1_check_ptr_some_info hchk0B
        rw [hidxPrev] at hidxA1; cases hidxA1
        rw [hidx0] at hidxA2; cases hidxA2
        have hdisjAlloc : aOff'.bytes + bs'.length ≤ aOff.bytes ∨ aOff.bytes + ty.size.bytes ≤ aOff'.bytes := by
          rw [htagLen]
          have h1 : (aOff.bytes : Int) = basePtr.addr + (off.bytes : Int) - alloc.addr := by
            rw [haOffEq, haddrP]
          have h2 : (aOff'.bytes : Int) = basePtr.addr + (off'.bytes : Int) - alloc.addr := by
            rw [haOffEq', haddrP']
          omega
        rw [ep1_writeSubsliceAtIndex_disjoint_preserves hws hdisjAlloc]
        exact hsubPrev
      · have haGet : m.mem.memory.allocations[id._0.toNat]'hidLt = a := by
          rw [← hget1, List.getElem_set_ne hsameId]
        have hidxPrev : listIndex m.mem.memory.allocations id._0 "self.allocations[id.0]" = .ok a := by
          rw [ep1_listIndex_int_of_getElem _ hidNN hidLt, haGet]
        exact hsome id aOff a hchk1 hidxPrev

private theorem ep1_encodeDiscriminantM_fold_bm (basePtr : Ptr) :
    ∀ (tags : List (Gen.Offset × (Gen.IntType × Int))) (m m1 : Mach),
      encodeDiscriminantM (M := BM)
        (fun m offset bytes => do
          let ptr ← ptrOffsetInboundsM (M := BM) m basePtr (offset.bytes : Int)
          let cm ← ConcurrentMemory.store (M := BM) m.mem ptr bytes ⟨1⟩ .None
          pure { m with mem := cm })
        ⟨tags⟩ m = .ok m1 →
      ep1CurFrameViewM (M := BM) m1 = ep1CurFrameViewM (M := BM) m ∧
      ep1AllocShape m1.mem.memory.allocations = ep1AllocShape m.mem.memory.allocations ∧
      (∀ off ty tagVal pre suf bs,
        tags = pre ++ (off, (ty, tagVal)) :: suf →
        Type.encodeIntM (M := BM) ty (.Int tagVal) = .ok bs →
        (∀ t ∈ suf, off.bytes + ty.size.bytes ≤ t.1.bytes ∨ t.1.bytes + t.2.1.size.bytes ≤ off.bytes) →
        ep1TagReadableBM m1 basePtr off ty bs)
  | [], m, m1, h => by
    unfold encodeDiscriminantM at h
    obtain rfl := ep1_pure_ok h
    refine ⟨rfl, rfl, fun _ _ _ pre _ _ hEq => ?_⟩
    cases pre <;> simp at hEq
  | (off0, (ty0, val0)) :: rest, m, m1, h => by
    unfold encodeDiscriminantM at h
    simp only [List.foldlM_cons] at h
    obtain ⟨mMid, hstep0, hrest⟩ := ep1_bind_ok h
    obtain ⟨bs0, henc0, hst0⟩ := ep1_bind_ok hstep0
    obtain ⟨hf0, hs0, hread0, _⟩ := ep1_store_step_bm henc0 hst0
    have hrest' : encodeDiscriminantM (M := BM)
        (fun m offset bytes => do
          let ptr ← ptrOffsetInboundsM (M := BM) m basePtr (offset.bytes : Int)
          let cm ← ConcurrentMemory.store (M := BM) m.mem ptr bytes ⟨1⟩ .None
          pure { m with mem := cm })
        ⟨rest⟩ mMid = .ok m1 := hrest
    obtain ⟨hfR, hsR, hreadR⟩ := ep1_encodeDiscriminantM_fold_bm basePtr rest mMid m1 hrest'
    refine ⟨hfR.trans hf0, hsR.trans hs0, ?_⟩
    intro off ty tagVal pre suf bs hEq henc hdisj
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hEq
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hEq
      subst h1; subst h2; subst h3; subst h4
      rw [henc0] at henc; cases henc
      have hcarry : ∀ (xs : List (Gen.Offset × (Gen.IntType × Int))) (s s' : Mach),
          encodeDiscriminantM (M := BM)
            (fun m offset bytes => do
              let ptr ← ptrOffsetInboundsM (M := BM) m basePtr (offset.bytes : Int)
              let cm ← ConcurrentMemory.store (M := BM) m.mem ptr bytes ⟨1⟩ .None
              pure { m with mem := cm })
            ⟨xs⟩ s = .ok s' →
          (∀ t ∈ xs, off0.bytes + ty0.size.bytes ≤ t.1.bytes ∨ t.1.bytes + t.2.1.size.bytes ≤ off0.bytes) →
          ep1TagReadableBM s basePtr off0 ty0 bs0 →
          ep1TagReadableBM s' basePtr off0 ty0 bs0 := by
        intro xs
        induction xs with
        | nil =>
          intro s s' hs _ hr
          unfold encodeDiscriminantM at hs
          obtain rfl := ep1_pure_ok hs; exact hr
        | cons t ts ih =>
          intro s s' hs hdj hr
          unfold encodeDiscriminantM at hs
          simp only [List.foldlM_cons] at hs
          obtain ⟨sMid, hst, hts⟩ := ep1_bind_ok hs
          obtain ⟨bsT, hencT, hstT⟩ := ep1_bind_ok hst
          obtain ⟨_, _, _, hpresT⟩ := ep1_store_step_bm hencT hstT
          exact ih sMid s' hts (fun x hx => hdj x (List.mem_cons_of_mem _ hx))
            (hpresT off0 ty0 bs0 (hdj t (List.mem_cons_self ..)) hr)
      exact hcarry rest mMid m1 hrest' hdisj hread0
    | cons hd tl =>
      simp only [List.cons_append, List.cons.injEq] at hEq
      exact hreadR off ty tagVal tl suf bs hEq.2 henc hdisj

private theorem ep1_decodeDiscriminantM_of_matches_bm (m1 : Mach) (basePtr : Ptr)
    (tags : List (Gen.Offset × (Gen.IntType × Int)))
    (hreadable : ∀ off ty tagVal pre suf bs,
      tags = pre ++ (off, (ty, tagVal)) :: suf →
      Type.encodeIntM (M := BM) ty (.Int tagVal) = .ok bs →
      (∀ t ∈ suf, off.bytes + ty.size.bytes ≤ t.1.bytes ∨ t.1.bytes + t.2.1.size.bytes ≤ off.bytes) →
      ep1TagReadableBM m1 basePtr off ty bs)
    {discr : Gen.Discriminator} {d : Int}
    (hmatch : Ep1DiscrMatchesTags BM tags discr d) :
    ∀ (m : Mach), m.mem.memory = m1.mem.memory →
      let acc := fun (s : Mach) (idx : Gen.Offset) (size : Size) => do
        let ptr ← ptrOffsetInboundsM (M := BM) s basePtr (idx.bytes : Int)
        let (bytes, cm) ← ConcurrentMemory.load (M := BM) s.mem ptr size ⟨1⟩ .None
        pure (bytes, { s with mem := cm })
      ∃ m2, decodeDiscriminantM (M := BM) acc discr m = .ok (some d, m2) ∧
        m2.mem.memory = m1.mem.memory := by
  induction hmatch with
  | Known d =>
    intro m hmem
    exact ⟨m, rfl, hmem⟩
  | Branch off ty fb children tagVal d pre suf bs hEq henc hdec hdisj hnext ih =>
    intro m hmem
    obtain ⟨ptr, hpoi1, hload1⟩ := ep1_tagReadableBM_implies_load (hreadable off ty tagVal pre suf bs hEq henc hdisj)
    have hpoiM : ptrOffsetInboundsM (M := BM) m basePtr (off.bytes : Int) = .ok ptr := by
      have hsh : ep1AllocShape m.mem.memory.allocations = ep1AllocShape m1.mem.memory.allocations := by
        rw [hmem]
      rw [ep1_ptrOffsetInboundsM_bm_eq] at hpoi1 ⊢
      rw [ep1_ptrOffsetInbounds_same_shape_bm hsh]; exact hpoi1
    have hloadM : BM.load m.mem.memory ptr ty.size ⟨1⟩ = .ok (bs, m.mem.memory) := by
      rw [hmem]; exact hload1
    let cmNext : Gen.ConcurrentMemory BM :=
      { memory := m.mem.memory, accesses := m.mem.accesses ++ [⟨.Load, .None, ptr.addr, ty.size⟩] }
    have hcmLoad : ConcurrentMemory.load (M := BM) m.mem ptr ty.size ⟨1⟩ .None = .ok (bs, cmNext) :=
      ep1_concurrent_load_of_mem_load (M := BM) m.mem ptr ty.size ⟨1⟩ .None bs m.mem.memory hloadM
    let mNext : Mach := { m with mem := cmNext }
    obtain ⟨m2, hrec, hmem2⟩ := ih mNext hmem
    refine ⟨m2, ?_, hmem2⟩
    unfold decodeDiscriminantM
    simp only [hpoiM, hcmLoad, bind, Except.bind, pure, Except.pure, hdec]
    rw [ep1_decodeDiscriminantChildrenM_eq_find_map]
    exact hrec

/-- **Universal multi-tag `SetDiscriminant → GetDiscriminant` roundtrip on `Mach` (`BasicMemory`, NO `hp1`, NO `m0`!):**
`BasicMemory` counterpart to `ep1_setDiscriminant_multitag_then_getDiscriminant_tb`, covering arbitrary
`Ep1PlaceChain` projections and arbitrary multi-level `Discriminator` trees with ZERO `hp1` and ZERO
extra address/size bounds hypotheses. -/
theorem ep1_setDiscriminant_multitag_then_getDiscriminant_bm
    (m m1 : Mach) (place : Gen.PlaceExpr) (hc : Ep1PlaceChain place)
    (rp : Gen.Place BM) (variants : Map Int Gen.Variant) (dty : Gen.IntType)
    (discr : Gen.Discriminator) (sz : Size) (al : Align) (d : Int) (var : Gen.Variant)
    (hp : evalPlace m place = .ok ((rp, .Enum variants dty discr sz al), m))
    (hvar : mapGet variants d = some var)
    (hmatch : Ep1DiscrMatchesTags BM var.tagger.entries discr d)
    (hset : evalStatement m (.SetDiscriminant place d) = .ok m1) :
    ∃ m2, evalValue m1 (.GetDiscriminant place) = .ok ((.Int d, .Int dty), m2) ∧
      m2.mem.memory = m1.mem.memory := by
  rw [← evalPlaceM_bm_eq] at hp
  rw [← evalStatementM_bm_eq] at hset
  suffices h : ∃ m2, evalValueM (M := BM) m1 (.GetDiscriminant place) = .ok ((.Int d, .Int dty), m2) ∧
      m2.mem.memory = m1.mem.memory by
    obtain ⟨m2, h1, h2⟩ := h
    rw [evalValueM_bm_eq] at h1
    exact ⟨m2, h1, h2⟩
  simp only [evalStatementM, evalSetDiscriminantM] at hset
  rw [hp] at hset
  dsimp only [bind, Except.bind] at hset
  have hal : rp.aligned = true := by
    cases h : rp.aligned
    · simp [h, ub] at hset
    · rfl
  simp only [hal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hvar] at hset
  obtain ⟨hf1, hs1, hreadable⟩ := ep1_encodeDiscriminantM_fold_bm rp.ptr.thin_pointer var.tagger.entries m m1 hset
  have hp1 : evalPlaceM (M := BM) m1 place = .ok ((rp, .Enum variants dty discr sz al), m1) := by
    rw [evalPlaceM_bm_eq] at hp ⊢
    rw [(ep1_evalPlaceM_chain_same_shape place hc).2 m m1 hf1 hs1, hp]
  obtain ⟨m2, hdd, hmem2⟩ :=
    ep1_decodeDiscriminantM_of_matches_bm m1 rp.ptr.thin_pointer var.tagger.entries hreadable hmatch m1 rfl
  refine ⟨m2, ?_, hmem2⟩
  rw [(ep1_evalValueM_getDiscriminant_complete_spec (M := BM)).1 m1 m1 place rp variants dty discr sz al hp1 hal]
  unfold ep1GetDiscriminantCore
  dsimp only
  rw [hdd]; rfl

/-! #### Universal `Assign place (ValueExpr.Variant d dataExpr enumTy) → GetDiscriminant place` (MachTB & Mach, NO `hp1`!) -/

private theorem ep1_encodeVariantM_eq_of_mapGet {M : Type} [Gen.Memory M]
    (vs : List (Int × Gen.Variant)) (d : Int) (var : Gen.Variant) (v : Gen.Value M)
    (hvar : mapGet ⟨vs⟩ d = some var) :
    Type.encodeVariantM (M := M) vs d v =
      (do
        let bytes ← Type.encodeM var.ty v
        encodeDiscriminantM (M := M)
          (fun bytes offset valueBytes => writeSubsliceAtIndex bytes offset.bytes valueBytes)
          var.tagger bytes) := by
  induction vs with
  | nil => simp [mapGet] at hvar
  | cons hd tl ih =>
    rcases hd with ⟨d0, ⟨ty0, tg0⟩⟩
    unfold mapGet at hvar
    dsimp only at hvar
    unfold Type.encodeVariantM
    by_cases heq : d0 = d
    · simp only [List.find?, heq, decide_true, Option.map_some, Option.some.injEq, ↓reduceIte] at hvar ⊢
      subst hvar; rfl
    · simp only [List.find?, heq, decide_false, ↓reduceIte] at hvar ⊢
      exact ih hvar

private theorem ep1_encodeDiscriminantM_bytes_recover {M : Type} [Gen.Memory M] :
    ∀ (tags : List (Gen.Offset × (Gen.IntType × Int)))
      (initBs outBs : List (Gen.AbstractByte (Gen.Memory.Provenance M))),
      encodeDiscriminantM (M := M)
        (fun bytes offset valueBytes => writeSubsliceAtIndex bytes offset.bytes valueBytes)
        ⟨tags⟩ initBs = .ok outBs →
      outBs.length = initBs.length ∧
      (∀ off ty tagVal pre suf bs,
        tags = pre ++ (off, (ty, tagVal)) :: suf →
        Type.encodeIntM (M := M) ty (.Int tagVal) = .ok bs →
        (∀ t ∈ suf, off.bytes + ty.size.bytes ≤ t.1.bytes ∨ t.1.bytes + t.2.1.size.bytes ≤ off.bytes) →
        off.bytes + ty.size.bytes ≤ outBs.length ∧
        subsliceWithLength outBs (off.bytes : Int) (ty.size.bytes : Int) = .ok bs)
  | [], initBs, outBs, h => by
    unfold encodeDiscriminantM at h
    obtain rfl := ep1_pure_ok h
    refine ⟨rfl, fun _ _ _ pre _ _ hEq => ?_⟩
    cases pre <;> simp at hEq
  | (off0, (ty0, val0)) :: rest, initBs, outBs, h => by
    unfold encodeDiscriminantM at h
    simp only [List.foldlM_cons] at h
    obtain ⟨midBs, hstep0, hrest⟩ := ep1_bind_ok h
    obtain ⟨bs0, henc0, hws0⟩ := ep1_bind_ok hstep0
    obtain ⟨hlen0, hsub0⟩ := ep1_writeSubsliceAtIndex_subslice_recover hws0
    have hrest' : encodeDiscriminantM (M := M)
        (fun bytes offset valueBytes => writeSubsliceAtIndex bytes offset.bytes valueBytes)
        ⟨rest⟩ midBs = .ok outBs := hrest
    obtain ⟨hlenR, hrecR⟩ := ep1_encodeDiscriminantM_bytes_recover rest midBs outBs hrest'
    refine ⟨hlenR.trans hlen0, ?_⟩
    intro off ty tagVal pre suf bs hEq henc hdisj
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hEq
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hEq
      subst h1; subst h2; subst h3; subst h4
      rw [henc0] at henc; cases henc
      have htagLen : bs0.length = ty0.size.bytes := ep1_encodeIntM_length henc0
      have hfit0 : off0.bytes + ty0.size.bytes ≤ midBs.length := by
        unfold writeSubsliceAtIndex at hws0
        split at hws0
        · rename_i hc; rw [hlen0, ← htagLen]; omega
        · simp [specPanic] at hws0
      have hsub0' : subsliceWithLength midBs (off0.bytes : Int) (ty0.size.bytes : Int) = .ok bs0 := by
        rw [← htagLen]; exact hsub0
      have hcarry : ∀ (xs : List (Gen.Offset × (Gen.IntType × Int)))
          (cur fin : List (Gen.AbstractByte (Gen.Memory.Provenance M))),
          encodeDiscriminantM (M := M)
            (fun bytes offset valueBytes => writeSubsliceAtIndex bytes offset.bytes valueBytes)
            ⟨xs⟩ cur = .ok fin →
          (∀ t ∈ xs, off0.bytes + ty0.size.bytes ≤ t.1.bytes ∨ t.1.bytes + t.2.1.size.bytes ≤ off0.bytes) →
          subsliceWithLength cur (off0.bytes : Int) (ty0.size.bytes : Int) = .ok bs0 →
          subsliceWithLength fin (off0.bytes : Int) (ty0.size.bytes : Int) = .ok bs0 := by
        intro xs
        induction xs with
        | nil =>
          intro cur fin hcur _ hsub
          unfold encodeDiscriminantM at hcur
          obtain rfl := ep1_pure_ok hcur; exact hsub
        | cons t ts ih =>
          intro cur fin hcur hdj hsub
          unfold encodeDiscriminantM at hcur
          simp only [List.foldlM_cons] at hcur
          obtain ⟨nxt, hst, hts⟩ := ep1_bind_ok hcur
          obtain ⟨bsT, hencT, hwsT⟩ := ep1_bind_ok hst
          have hlenT : bsT.length = t.2.1.size.bytes := ep1_encodeIntM_length hencT
          have hdjT : t.1.bytes + bsT.length ≤ off0.bytes ∨ off0.bytes + ty0.size.bytes ≤ t.1.bytes := by
            rw [hlenT]
            rcases hdj t (List.mem_cons_self ..) with h1 | h2
            · exact Or.inr h1
            · exact Or.inl h2
          exact ih nxt fin hts (fun x hx => hdj x (List.mem_cons_of_mem _ hx))
            (by rw [ep1_writeSubsliceAtIndex_disjoint_preserves hwsT hdjT]; exact hsub)
      exact ⟨by omega, hcarry rest midBs outBs hrest' hdisj hsub0'⟩
    | cons hd tl =>
      simp only [List.cons_append, List.cons.injEq] at hEq
      exact hrecR off ty tagVal tl suf bs hEq.2 henc hdisj

private theorem ep1_evalValueM_variant_inv {M : Type} [Gen.Memory M] [MemoryOps M]
    {m mMid : Gen.Machine M} {d : Int} {dataExpr : Gen.ValueExpr} {enumTy : Gen.Type}
    {v : Gen.Value M} {vTy : Gen.Type}
    (h : evalValueM m (.Variant d dataExpr enumTy) = .ok ((v, vTy), mMid)) :
    ∃ dv, v = .Variant d dv := by
  unfold evalValueM at h
  obtain ⟨⟨⟨dv, _⟩, _⟩, _, hRet⟩ := ep1_bind_ok h
  obtain ⟨hvt, _⟩ := Prod.mk.inj (ep1_pure_ok hRet)
  exact ⟨dv, (Prod.mk.inj hvt).1.symm⟩

private theorem ep1_encodeM_enum_variant {M : Type} [Gen.Memory M]
    (variants : Map Int Gen.Variant) (dty : Gen.IntType) (discr : Gen.Discriminator)
    (sz : Size) (al : Align) (d : Int) (dv : Gen.Value M) :
    Type.encodeM (.Enum variants dty discr sz al) (.Variant d dv) =
      Type.encodeVariantM variants.entries d dv := by
  simp only [Type.encodeM]

private theorem ep1_store_enum_tag_readable_tb
    (mMid m1 : MachTB) (basePtr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (enumBytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (tbm1 : Gen.TreeBorrowsMemory Gen.x86_64)
    (htbStore : TreeBorrowsMemory.store mMid.mem.memory basePtr enumBytes ⟨1⟩ = .ok tbm1)
    (hmemEq : m1.mem.memory = tbm1)
    (off : Gen.Offset) (ty : Gen.IntType) (bs : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (hoffHi : (off.bytes : Int) < (2 : Int) ^ 63)
    (haddrLo : 0 ≤ basePtr.addr + (off.bytes : Int))
    (haddrHi : basePtr.addr + (off.bytes : Int) < (2 : Int) ^ 64)
    (hfit : off.bytes + ty.size.bytes ≤ enumBytes.length)
    (hsubEnum : subsliceWithLength enumBytes (off.bytes : Int) (ty.size.bytes : Int) = .ok bs)
    (htagLen : bs.length = ty.size.bytes) :
    ep1TagReadableTB m1 basePtr off ty bs := by
  unfold TreeBorrowsMemory.store at htbStore
  obtain ⟨bm1, hbmStore, htbRet⟩ := ep1_bind_ok htbStore
  obtain rfl := ep1_pure_ok htbRet
  have hm1Mem : m1.mem.memory.mem = bm1 := by rw [hmemEq]
  unfold BasicMemory.store at hbmStore
  simp only [ep1_align_one_is_aligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hbmStore
  obtain ⟨chk0, hchk0, hbmStore⟩ := ep1_bind_ok hbmStore
  cases chk0 with
  | none =>
    obtain rfl := ep1_pure_ok hbmStore
    have hlen0 : enumBytes.length = 0 := by
      unfold BasicMemory.check_ptr at hchk0
      split at hchk0
      · assumption
      · cases hpr : basePtr.provenance with
        | none => simp [hpr, ub] at hchk0
        | some ip =>
          simp only [hpr] at hchk0
          obtain ⟨_, _, hchk0⟩ := ep1_bind_ok hchk0
          split at hchk0
          · simp [ub] at hchk0
          · split at hchk0
            · simp [ub] at hchk0
            · cases ep1_pure_ok hchk0
    have hoff0 : off.bytes = 0 := by omega
    have hty0 : ty.size.bytes = 0 := by omega
    have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs0
    have hpoi : ptrOffsetInboundsM m1 basePtr (off.bytes : Int) =
        .ok { basePtr with addr := basePtr.addr + (off.bytes : Int) } := by
      have hsd : ConcurrentMemory.signed_dereferenceable m1.mem basePtr (off.bytes : Int) = .ok () := by
        change TreeBorrowsMemory.signed_dereferenceable m1.mem.memory basePtr (off.bytes : Int) = .ok ()
        unfold TreeBorrowsMemory.signed_dereferenceable TreeBorrowsMemory.dereferenceable
        simp [hoff0, BasicMemory.check_ptr, pure, Except.pure]
      exact ep1_ptrOffsetInboundsM_ok m1 basePtr (off.bytes : Int) hsd
        (ep1_inBounds_nonneg_signed off.bytes hoffHi) (ep1_inBounds_unsigned _ haddrLo haddrHi)
    have hchkTag : BasicMemory.check_ptr m1.mem.memory.mem
        { basePtr with addr := basePtr.addr + (off.bytes : Int) } ty.size = .ok none := by
      unfold BasicMemory.check_ptr; simp [hty0, pure, Except.pure]
    exact ⟨_, hpoi, (fun _ _ _ _ hc _ => by rw [hchkTag] at hc; cases hc), (fun _ => rfl), ⟨none, hchkTag⟩⟩
  | some trip =>
    rcases trip with ⟨id, path, baseOff⟩
    obtain ⟨alloc, hidx0, hbmStore⟩ := ep1_bind_ok hbmStore
    obtain ⟨extra', hextra, hbmStore⟩ := ep1_bind_ok hbmStore
    obtain ⟨root', hnodeW, hretE⟩ := ep1_bind_ok hextra
    obtain rfl := ep1_pure_ok hretE
    obtain ⟨data', hws, hbmStore⟩ := ep1_bind_ok hbmStore
    obtain ⟨allocs', hset', hbmRet⟩ := ep1_bind_ok hbmStore
    obtain rfl := ep1_pure_ok hbmRet
    obtain ⟨hidNN, hidLt, _⟩ := ep1_listIndex_int_eq_getElem hidx0
    have hallocsEq : allocs' = mMid.mem.memory.mem.allocations.set id._0.toNat
        { alloc with data := data', extra := { root := root' } } := by
      unfold listSet at hset'
      split at hset'
      · exact (ep1_pure_ok hset').symm
      · simp [specPanic] at hset'
    subst hallocsEq
    have hidLt1 : id._0.toNat < (mMid.mem.memory.mem.allocations.set id._0.toNat
        { alloc with data := data', extra := { root := root' } }).length := by
      simpa [List.length_set] using hidLt
    have hchk0Info : basePtr.provenance = some (id, path) ∧
        alloc.live = true ∧
        (baseOff.bytes : Int) = basePtr.addr - alloc.addr ∧
        baseOff.bytes + enumBytes.length ≤ alloc.data.length := by
      unfold BasicMemory.check_ptr at hchk0
      split at hchk0
      · cases ep1_pure_ok hchk0
      · cases hpr : basePtr.provenance with
        | none => simp [hpr, ub] at hchk0
        | some ip =>
          rcases ip with ⟨id', path'⟩
          simp only [hpr] at hchk0
          obtain ⟨a', hidx', hchk0⟩ := ep1_bind_ok hchk0
          split at hchk0
          · simp [ub] at hchk0
          · rename_i hlive
            split at hchk0
            · simp [ub] at hchk0
            · rename_i hnotOob
              have hp := ep1_pure_ok hchk0
              simp only [Option.some.injEq, Prod.mk.injEq] at hp
              rcases hp with ⟨rfl, rfl, hoffEq⟩
              rw [hidx0] at hidx'; cases hidx'
              have hlv : alloc.live = true := by cases h : alloc.live <;> simp [h] at hlive ⊢
              have hnn : (0 : Int) ≤ (basePtr.addr : Int) - (alloc.addr : Int) :=
                Int.not_lt.mp (fun hlt => hnotOob (Or.inl hlt))
              have hle : (basePtr.addr : Int) - (alloc.addr : Int) + (enumBytes.length : Int) ≤
                  (alloc.data.length : Int) := Int.not_lt.mp (fun hgt => hnotOob (Or.inr hgt))
              have hbEq : (baseOff.bytes : Int) = (basePtr.addr : Int) - (alloc.addr : Int) := by
                cases hoffEq; exact Int.toNat_of_nonneg hnn
              rw [← hbEq] at hle
              exact ⟨rfl, hlv, hbEq, Int.ofNat_le.mp (by simpa [Int.natCast_add] using hle)⟩
    obtain ⟨hprov, hlive, hbaseEq, hbaseFit⟩ := hchk0Info
    have hlenData : data'.length = alloc.data.length := writeSubsliceAtIndex_length hws
    have hidx1 : listIndex (mMid.mem.memory.mem.allocations.set id._0.toNat
        { alloc with data := data', extra := { root := root' } }) id._0 "self.allocations[id.0]" =
        .ok { alloc with data := data', extra := { root := root' } } := by
      rw [ep1_listIndex_int_of_getElem _ hidNN hidLt1, List.getElem_set_self]
    let tagPtr : Gen.ThinPointer Gen.TreeBorrowsProvenance :=
      { basePtr with addr := basePtr.addr + (off.bytes : Int) }
    have hpoi : ptrOffsetInboundsM m1 basePtr (off.bytes : Int) = .ok tagPtr := by
      have hsd : ConcurrentMemory.signed_dereferenceable m1.mem basePtr (off.bytes : Int) = .ok () := by
        change TreeBorrowsMemory.signed_dereferenceable m1.mem.memory basePtr (off.bytes : Int) = .ok ()
        unfold TreeBorrowsMemory.signed_dereferenceable TreeBorrowsMemory.dereferenceable
        by_cases hpos : (off.bytes : Int) > 0
        · simp only [hpos, Int.toNat_natCast, ↓reduceIte]
          have hchkOff : BasicMemory.check_ptr m1.mem.memory.mem basePtr ⟨off.bytes⟩ =
              .ok (some (id, path, baseOff)) := by
            rw [hm1Mem]; unfold BasicMemory.check_ptr
            have hnz : off.bytes ≠ 0 := by omega
            simp only [hnz, ↓reduceIte, hprov, hidx1, bind, Except.bind]
            simp only [hlive, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Allocation.size, hlenData]
            have hnoOob : ¬((basePtr.addr : Int) - (alloc.addr : Int) < 0 ∨
                (basePtr.addr : Int) - (alloc.addr : Int) + (off.bytes : Int) >
                (alloc.data.length : Int)) := by
              rw [← hbaseEq]; exact ep1_not_oob_int (by omega) (by omega)
            simp only [hnoOob, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq]
            refine ⟨trivial, trivial, ?_⟩
            cases baseOff; simp only [← hbaseEq, Int.toNat_natCast]
          simp only [hchkOff, bind, Except.bind, pure, Except.pure]
        · have hoff0 : off.bytes = 0 := by omega
          simp [hoff0, BasicMemory.check_ptr, pure, Except.pure]
      exact ep1_ptrOffsetInboundsM_ok m1 basePtr (off.bytes : Int) hsd
        (ep1_inBounds_nonneg_signed off.bytes hoffHi) (ep1_inBounds_unsigned _ haddrLo haddrHi)
    by_cases hty0 : ty.size.bytes = 0
    · have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hbs0
      have hchkTag : BasicMemory.check_ptr m1.mem.memory.mem tagPtr ty.size = .ok none := by
        unfold BasicMemory.check_ptr; simp [hty0, pure, Except.pure]
      exact ⟨tagPtr, hpoi, (fun _ _ _ _ hc _ => by rw [hchkTag] at hc; cases hc), (fun _ => rfl), ⟨none, hchkTag⟩⟩
    · have hchkTag : BasicMemory.check_ptr m1.mem.memory.mem tagPtr ty.size =
          .ok (some (id, path, ⟨baseOff.bytes + off.bytes⟩)) := by
        rw [hm1Mem]; unfold BasicMemory.check_ptr
        dsimp only [tagPtr]
        simp only [hty0, ↓reduceIte, hprov, hidx1, bind, Except.bind]
        simp only [hlive, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Allocation.size, hlenData]
        have hdiff : (basePtr.addr : Int) + (off.bytes : Int) - (alloc.addr : Int) =
            ((baseOff.bytes + off.bytes : Nat) : Int) := by
          rw [Int.natCast_add, hbaseEq, Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.add_right_comm]
        have hnoOob : ¬((basePtr.addr : Int) + (off.bytes : Int) - (alloc.addr : Int) < 0 ∨
            (basePtr.addr : Int) + (off.bytes : Int) - (alloc.addr : Int) + (ty.size.bytes : Int) >
            (alloc.data.length : Int)) := by
          rw [hdiff]; exact ep1_not_oob_int (by omega) (by omega)
        simp only [hnoOob, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq]
        refine ⟨trivial, trivial, ?_⟩
        simp only [hdiff, Int.toNat_natCast]
      refine ⟨tagPtr, hpoi, ?_, (fun hn => by rw [hchkTag] at hn; cases hn),
        ⟨some (id, path, ⟨baseOff.bytes + off.bytes⟩), hchkTag⟩⟩
      intro id' path' aOff' a' hchk' hidx'
      rw [hchkTag] at hchk'
      simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hchk'
      rcases hchk' with ⟨rfl, rfl, rfl⟩
      rw [hm1Mem] at hidx'
      rw [hidx1] at hidx'; cases hidx'
      have hdataRec : subsliceWithLength data' (baseOff.bytes : Int) (enumBytes.length : Int) = .ok enumBytes :=
        (ep1_writeSubsliceAtIndex_subslice_recover hws).2
      have hsubData : subsliceWithLength data' ((baseOff.bytes + off.bytes : Nat) : Int) (ty.size.bytes : Int) = .ok bs := by
        have h1 := ep1_subsliceWithLength_eq hdataRec
        have h2 := ep1_subsliceWithLength_eq hsubEnum
        rw [ep1_subsliceWithLength_of_le data' (by omega),
          ← ep1_drop_take_subslice data' (sz := enumBytes.length) (by omega), ← h1.2, ← h2.2]
      have hidemFull := ep1_node_access_write_establishes_readIdem alloc.extra.root root' (some path)
        baseOff.bytes enumBytes.length hnodeW
      have hidemSub : ep1NodeReadIdem (some path) (baseOff.bytes + off.bytes) ty.size.bytes root' :=
        ep1_nodeReadIdem_subrange baseOff.bytes enumBytes.length (baseOff.bytes + off.bytes) ty.size.bytes
          (by omega) (by omega) root' (some path) hidemFull
      exact ⟨hsubData, hidemSub⟩

/-- **Universal `Assign place (ValueExpr.Variant d dataExpr enumTy) → GetDiscriminant place` roundtrip
on `MachTB` (NO `hp1`, NO `m0`!):**
for **any** `Ep1PlaceChain place` (`Local`/`Field`/`Downcast`), **any** payload expression `dataExpr`
(even with `Load`/`AddrOf`/`GetDiscriminant` side effects), and **any** multi-tag variant matching
an arbitrary-depth `Discriminator` tree (`Ep1DiscrMatchesTags`), under the tight tag-offset address
bounds `haddr`, `Assign` followed by `GetDiscriminant` **unconditionally succeeds** returning
`(.Int d, .Int dty)` with `m2.mem.memory = m1.mem.memory` (every Tree Borrows permission unchanged,
since `Assign`'s full-enum `.Write` covers every tag sub-range). -/
theorem ep1_assign_variant_then_getDiscriminant_tb
    (m m1 : MachTB) (place : Gen.PlaceExpr) (hc : Ep1PlaceChain place)
    (rp : Gen.Place TBM) (variants : Map Int Gen.Variant) (dty : Gen.IntType)
    (discr : Gen.Discriminator) (sz : Size) (al : Align)
    (d : Int) (var : Gen.Variant) (dataExpr : Gen.ValueExpr) (enumTy : Gen.Type)
    (hp : evalPlaceM m place = .ok ((rp, .Enum variants dty discr sz al), m))
    (hvar : mapGet variants d = some var)
    (hmatch : Ep1DiscrMatchesTags TBM var.tagger.entries discr d)
    (haddr : ∀ t ∈ var.tagger.entries,
      (t.1.bytes : Int) < (2 : Int) ^ 63 ∧
      0 ≤ rp.ptr.thin_pointer.addr + (t.1.bytes : Int) ∧
      rp.ptr.thin_pointer.addr + (t.1.bytes : Int) < (2 : Int) ^ 64)
    (hassign : evalStatementM m (.Assign place (.Variant d dataExpr enumTy)) = .ok m1) :
    ∃ m2, evalValueM m1 (.GetDiscriminant place) = .ok ((.Int d, .Int dty), m2) ∧
      m2.mem.memory = m1.mem.memory := by
  simp only [evalStatementM] at hassign
  rw [hp] at hassign
  dsimp only [bind, Except.bind] at hassign
  obtain ⟨⟨⟨v, vTy⟩, mMid⟩, hv, hstoreSt⟩ := ep1_bind_ok hassign
  obtain ⟨hfMid, hsMid⟩ := ep1_evalValueM_preserves_shape_tb (.Variant d dataExpr enumTy) m mMid (v, vTy) hv
  obtain ⟨dv, rfl⟩ := ep1_evalValueM_variant_inv hv
  unfold placeStoreM at hstoreSt
  have hal : rp.aligned = true := by
    cases h : rp.aligned
    · simp [h, ub] at hstoreSt
    · rfl
  simp only [hal, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hstoreSt
  unfold typedStoreM at hstoreSt
  split at hstoreSt
  · obtain ⟨enumBytes, hencEnum, hstoreSt⟩ := ep1_bind_ok hstoreSt
    obtain ⟨cm1, hcmStore, hpRet⟩ := ep1_bind_ok hstoreSt
    have hm1Eq : m1 = { mMid with mem := cm1 } := (ep1_pure_ok hpRet).symm
    unfold ConcurrentMemory.store at hcmStore
    obtain ⟨tbm1, htbStore, hcmRet⟩ := ep1_bind_ok hcmStore
    have hcmMem : cm1.memory = tbm1 := by
      have h := (ep1_pure_ok hcmRet).symm; rw [h]
    have hm1Mem : m1.mem.memory = tbm1 := by rw [hm1Eq, hcmMem]
    have htbStore' : TreeBorrowsMemory.store mMid.mem.memory rp.ptr.thin_pointer enumBytes ⟨1⟩ = .ok tbm1 := htbStore
    have hshapeStore : ep1AllocShape tbm1.mem.allocations = ep1AllocShape mMid.mem.memory.mem.allocations := by
      unfold TreeBorrowsMemory.store at htbStore'
      obtain ⟨bm1, hbmStore, htbRet⟩ := ep1_bind_ok htbStore'
      have h := (ep1_pure_ok htbRet).symm
      rw [h]; exact ep1_BasicMemory_store_shape hbmStore
    have hf1 : ep1CurFrameViewM m1 = ep1CurFrameViewM m := by
      rw [hm1Eq]; exact hfMid
    have hs1 : ep1AllocShape m1.mem.memory.mem.allocations = ep1AllocShape m.mem.memory.mem.allocations := by
      rw [hm1Mem, hshapeStore, hsMid]
    have hp1 : evalPlaceM m1 place = .ok ((rp, .Enum variants dty discr sz al), m1) := by
      rw [(ep1_evalPlaceM_chain_same_shape place hc).1 m m1 hf1 hs1, hp]
    rw [ep1_encodeM_enum_variant, ep1_encodeVariantM_eq_of_mapGet variants.entries d var dv hvar] at hencEnum
    obtain ⟨varBytes, _, hencTags⟩ := ep1_bind_ok hencEnum
    obtain ⟨_, htagsRec⟩ := ep1_encodeDiscriminantM_bytes_recover var.tagger.entries varBytes enumBytes hencTags
    have hreadable : ∀ off ty tagVal pre suf bs,
        var.tagger.entries = pre ++ (off, (ty, tagVal)) :: suf →
        Type.encodeIntM (M := TBM) ty (.Int tagVal) = .ok bs →
        (∀ t ∈ suf, off.bytes + ty.size.bytes ≤ t.1.bytes ∨ t.1.bytes + t.2.1.size.bytes ≤ off.bytes) →
        ep1TagReadableTB m1 rp.ptr.thin_pointer off ty bs := by
      intro off ty tagVal pre suf bs hEq hencT hdisj
      have hmemT : (off, (ty, tagVal)) ∈ var.tagger.entries := by rw [hEq]; simp
      obtain ⟨hoffHi, haddrLo, haddrHi⟩ := haddr (off, (ty, tagVal)) hmemT
      dsimp only at hoffHi haddrLo haddrHi
      obtain ⟨hfit, hsubEnum⟩ := htagsRec off ty tagVal pre suf bs hEq hencT hdisj
      exact ep1_store_enum_tag_readable_tb mMid m1 rp.ptr.thin_pointer enumBytes tbm1
        htbStore hm1Mem off ty bs hoffHi haddrLo haddrHi hfit hsubEnum (ep1_encodeIntM_length hencT)
    obtain ⟨m2, hdd, hmem2⟩ :=
      ep1_decodeDiscriminantM_of_matches_tb m1 rp.ptr.thin_pointer var.tagger.entries hreadable hmatch m1 rfl
    refine ⟨m2, ?_, hmem2⟩
    rw [(ep1_evalValueM_getDiscriminant_complete_spec (M := TBM)).1 m1 m1 place rp variants dty discr sz al hp1 hal]
    unfold ep1GetDiscriminantCore
    dsimp only
    rw [hdd]; rfl
  · simp [specPanic] at hstoreSt

private theorem ep1_store_enum_tag_readable_bm
    (mMid m1 : Mach) (basePtr : Ptr)
    (enumBytes : List (Gen.AbstractByte (Gen.Provenance Unit)))
    (bm1 : BM)
    (hbmStore : BM.store mMid.mem.memory basePtr enumBytes ⟨1⟩ = .ok bm1)
    (hmemEq : m1.mem.memory = bm1)
    (off : Gen.Offset) (ty : Gen.IntType) (bs : List (Gen.AbstractByte (Gen.Provenance Unit)))
    (hoffHi : (off.bytes : Int) < (2 : Int) ^ 63)
    (haddrLo : 0 ≤ basePtr.addr + (off.bytes : Int))
    (haddrHi : basePtr.addr + (off.bytes : Int) < (2 : Int) ^ 64)
    (hfit : off.bytes + ty.size.bytes ≤ enumBytes.length)
    (hsubEnum : subsliceWithLength enumBytes (off.bytes : Int) (ty.size.bytes : Int) = .ok bs)
    (htagLen : bs.length = ty.size.bytes) :
    ep1TagReadableBM m1 basePtr off ty bs := by
  unfold BM.store at hbmStore
  simp only [ep1_align_one_is_aligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hbmStore
  obtain ⟨chk0, hchk0, hbmStore⟩ := ep1_bind_ok hbmStore
  cases chk0 with
  | none =>
    obtain rfl := ep1_pure_ok hbmStore
    have hlen0 : enumBytes.length = 0 := by
      unfold BM.check_ptr at hchk0
      split at hchk0
      · assumption
      · cases hpr : basePtr.provenance with
        | none => simp [hpr, ub] at hchk0
        | some ip =>
          simp only [hpr] at hchk0
          obtain ⟨_, _, hchk0⟩ := ep1_bind_ok hchk0
          split at hchk0
          · simp [ub] at hchk0
          · split at hchk0
            · simp [ub] at hchk0
            · cases ep1_pure_ok hchk0
    have hoff0 : off.bytes = 0 := by omega
    have hty0 : ty.size.bytes = 0 := by omega
    have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs0
    have hpoi : ptrOffsetInboundsM (M := BM) m1 basePtr (off.bytes : Int) =
        .ok { basePtr with addr := basePtr.addr + (off.bytes : Int) } := by
      have hsd : ConcurrentMemory.signed_dereferenceable (M := BM) m1.mem basePtr (off.bytes : Int) = .ok () := by
        change BM.signed_dereferenceable m1.mem.memory basePtr (off.bytes : Int) = .ok ()
        unfold BM.signed_dereferenceable BM.dereferenceable
        simp [hoff0, BM.check_ptr, pure, Except.pure]
      exact ep1_ptrOffsetInboundsM_ok (M := BM) m1 basePtr (off.bytes : Int) hsd
        (ep1_inBounds_nonneg_signed off.bytes hoffHi) (ep1_inBounds_unsigned _ haddrLo haddrHi)
    have hchkTag : BM.check_ptr m1.mem.memory
        { basePtr with addr := basePtr.addr + (off.bytes : Int) } ty.size = .ok none := by
      unfold BM.check_ptr; simp [hty0, pure, Except.pure]
    exact ⟨_, hpoi, (fun _ _ _ hc _ => by rw [hchkTag] at hc; cases hc), (fun _ => rfl), ⟨none, hchkTag⟩⟩
  | some trip =>
    rcases trip with ⟨id, pu, baseOff⟩
    cases pu
    obtain ⟨alloc, hidx0, hbmStore⟩ := ep1_bind_ok hbmStore
    obtain ⟨data', hws, hbmStore⟩ := ep1_bind_ok hbmStore
    obtain ⟨allocs', hset', hbmRet⟩ := ep1_bind_ok hbmStore
    obtain rfl := ep1_pure_ok hbmRet
    obtain ⟨hidNN, hidLt, _⟩ := ep1_listIndex_int_eq_getElem hidx0
    have hallocsEq : allocs' = mMid.mem.memory.allocations.set id._0.toNat { alloc with data := data' } := by
      unfold listSet at hset'
      split at hset'
      · exact (ep1_pure_ok hset').symm
      · simp [specPanic] at hset'
    subst hallocsEq
    have hidLt1 : id._0.toNat < (mMid.mem.memory.allocations.set id._0.toNat { alloc with data := data' }).length := by
      simpa [List.length_set] using hidLt
    have hchk0Info : basePtr.provenance = some (id, ()) ∧
        alloc.live = true ∧
        (baseOff.bytes : Int) = basePtr.addr - alloc.addr ∧
        baseOff.bytes + enumBytes.length ≤ alloc.data.length := by
      unfold BM.check_ptr at hchk0
      split at hchk0
      · cases ep1_pure_ok hchk0
      · cases hpr : basePtr.provenance with
        | none => simp [hpr, ub] at hchk0
        | some ip =>
          rcases ip with ⟨id', pu'⟩
          cases pu'
          simp only [hpr] at hchk0
          obtain ⟨a', hidx', hchk0⟩ := ep1_bind_ok hchk0
          split at hchk0
          · simp [ub] at hchk0
          · rename_i hlive
            split at hchk0
            · simp [ub] at hchk0
            · rename_i hnotOob
              have hp := ep1_pure_ok hchk0
              simp only [Option.some.injEq, Prod.mk.injEq] at hp
              rcases hp with ⟨rfl, _, hoffEq⟩
              rw [hidx0] at hidx'; cases hidx'
              have hlv : alloc.live = true := by cases h : alloc.live <;> simp [h] at hlive ⊢
              have hnn : (0 : Int) ≤ (basePtr.addr : Int) - (alloc.addr : Int) :=
                Int.not_lt.mp (fun hlt => hnotOob (Or.inl hlt))
              have hle : (basePtr.addr : Int) - (alloc.addr : Int) + (enumBytes.length : Int) ≤
                  (alloc.data.length : Int) := Int.not_lt.mp (fun hgt => hnotOob (Or.inr hgt))
              have hbEq : (baseOff.bytes : Int) = (basePtr.addr : Int) - (alloc.addr : Int) := by
                cases hoffEq; exact Int.toNat_of_nonneg hnn
              rw [← hbEq] at hle
              exact ⟨rfl, hlv, hbEq, Int.ofNat_le.mp (by simpa [Int.natCast_add] using hle)⟩
    obtain ⟨hprov, hlive, hbaseEq, hbaseFit⟩ := hchk0Info
    have hlenData : data'.length = alloc.data.length := writeSubsliceAtIndex_length hws
    have hidx1 : listIndex (mMid.mem.memory.allocations.set id._0.toNat { alloc with data := data' })
        id._0 "self.allocations[id.0]" = .ok { alloc with data := data' } := by
      rw [ep1_listIndex_int_of_getElem _ hidNN hidLt1, List.getElem_set_self]
    let tagPtr : Ptr :=
      { basePtr with addr := basePtr.addr + (off.bytes : Int) }
    have hpoi : ptrOffsetInboundsM (M := BM) m1 basePtr (off.bytes : Int) = .ok tagPtr := by
      have hsd : ConcurrentMemory.signed_dereferenceable (M := BM) m1.mem basePtr (off.bytes : Int) = .ok () := by
        change BM.signed_dereferenceable m1.mem.memory basePtr (off.bytes : Int) = .ok ()
        unfold BM.signed_dereferenceable BM.dereferenceable
        by_cases hpos : (off.bytes : Int) > 0
        · simp only [hpos, Int.toNat_natCast, ↓reduceIte]
          have hchkOff : BM.check_ptr m1.mem.memory basePtr ⟨off.bytes⟩ =
              .ok (some (id, (), baseOff)) := by
            rw [hmemEq]; unfold BM.check_ptr
            have hnz : off.bytes ≠ 0 := by omega
            simp only [hnz, ↓reduceIte, hprov, hidx1, bind, Except.bind]
            simp only [hlive, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Allocation.size, hlenData]
            have hnoOob : ¬((basePtr.addr : Int) - (alloc.addr : Int) < 0 ∨
                (basePtr.addr : Int) - (alloc.addr : Int) + (off.bytes : Int) >
                (alloc.data.length : Int)) := by
              rw [← hbaseEq]; exact ep1_not_oob_int (by omega) (by omega)
            simp only [hnoOob, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq]
            refine ⟨trivial, trivial, ?_⟩
            cases baseOff; simp only [← hbaseEq, Int.toNat_natCast]
          simp only [hchkOff, bind, Except.bind, pure, Except.pure]
        · have hoff0 : off.bytes = 0 := by omega
          simp [hoff0, BM.check_ptr, pure, Except.pure]
      exact ep1_ptrOffsetInboundsM_ok (M := BM) m1 basePtr (off.bytes : Int) hsd
        (ep1_inBounds_nonneg_signed off.bytes hoffHi) (ep1_inBounds_unsigned _ haddrLo haddrHi)
    by_cases hty0 : ty.size.bytes = 0
    · have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hbs0
      have hchkTag : BM.check_ptr m1.mem.memory tagPtr ty.size = .ok none := by
        unfold BM.check_ptr; simp [hty0, pure, Except.pure]
      exact ⟨tagPtr, hpoi, (fun _ _ _ hc _ => by rw [hchkTag] at hc; cases hc), (fun _ => rfl), ⟨none, hchkTag⟩⟩
    · have hchkTag : BM.check_ptr m1.mem.memory tagPtr ty.size =
          .ok (some (id, (), ⟨baseOff.bytes + off.bytes⟩)) := by
        rw [hmemEq]; unfold BM.check_ptr
        dsimp only [tagPtr]
        simp only [hty0, ↓reduceIte, hprov, hidx1, bind, Except.bind]
        simp only [hlive, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Allocation.size, hlenData]
        have hdiff : (basePtr.addr : Int) + (off.bytes : Int) - (alloc.addr : Int) =
            ((baseOff.bytes + off.bytes : Nat) : Int) := by
          rw [Int.natCast_add, hbaseEq, Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.add_right_comm]
        have hnoOob : ¬((basePtr.addr : Int) + (off.bytes : Int) - (alloc.addr : Int) < 0 ∨
            (basePtr.addr : Int) + (off.bytes : Int) - (alloc.addr : Int) + (ty.size.bytes : Int) >
            (alloc.data.length : Int)) := by
          rw [hdiff]; exact ep1_not_oob_int (by omega) (by omega)
        simp only [hnoOob, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq]
        refine ⟨trivial, trivial, ?_⟩
        simp only [hdiff, Int.toNat_natCast]
      refine ⟨tagPtr, hpoi, ?_, (fun hn => by rw [hchkTag] at hn; cases hn),
        ⟨some (id, (), ⟨baseOff.bytes + off.bytes⟩), hchkTag⟩⟩
      intro id' aOff' a' hchk' hidx'
      rw [hchkTag] at hchk'
      simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hchk'
      rcases hchk' with ⟨rfl, _, rfl⟩
      rw [hmemEq] at hidx'
      rw [hidx1] at hidx'; cases hidx'
      have hdataRec : subsliceWithLength data' (baseOff.bytes : Int) (enumBytes.length : Int) = .ok enumBytes :=
        (ep1_writeSubsliceAtIndex_subslice_recover hws).2
      have hsubData : subsliceWithLength data' ((baseOff.bytes + off.bytes : Nat) : Int) (ty.size.bytes : Int) = .ok bs := by
        have h1 := ep1_subsliceWithLength_eq hdataRec
        have h2 := ep1_subsliceWithLength_eq hsubEnum
        rw [ep1_subsliceWithLength_of_le data' (by omega),
          ← ep1_drop_take_subslice data' (sz := enumBytes.length) (by omega), ← h1.2, ← h2.2]
      exact hsubData

/-- **Universal `Assign place (ValueExpr.Variant d dataExpr enumTy) → GetDiscriminant place` roundtrip
on `Mach` (`BasicMemory`, NO `hp1`, NO `m0`!):**
`BasicMemory` counterpart to `ep1_assign_variant_then_getDiscriminant_tb`. -/
theorem ep1_assign_variant_then_getDiscriminant_bm
    (m m1 : Mach) (place : Gen.PlaceExpr) (hc : Ep1PlaceChain place)
    (rp : Gen.Place BM) (variants : Map Int Gen.Variant) (dty : Gen.IntType)
    (discr : Gen.Discriminator) (sz : Size) (al : Align)
    (d : Int) (var : Gen.Variant) (dataExpr : Gen.ValueExpr) (enumTy : Gen.Type)
    (hp : evalPlace m place = .ok ((rp, .Enum variants dty discr sz al), m))
    (hvar : mapGet variants d = some var)
    (hmatch : Ep1DiscrMatchesTags BM var.tagger.entries discr d)
    (haddr : ∀ t ∈ var.tagger.entries,
      (t.1.bytes : Int) < (2 : Int) ^ 63 ∧
      0 ≤ rp.ptr.thin_pointer.addr + (t.1.bytes : Int) ∧
      rp.ptr.thin_pointer.addr + (t.1.bytes : Int) < (2 : Int) ^ 64)
    (hassign : evalStatement m (.Assign place (.Variant d dataExpr enumTy)) = .ok m1) :
    ∃ m2, evalValue m1 (.GetDiscriminant place) = .ok ((.Int d, .Int dty), m2) ∧
      m2.mem.memory = m1.mem.memory := by
  rw [← evalPlaceM_bm_eq] at hp
  rw [← evalStatementM_bm_eq] at hassign
  suffices h : ∃ m2, evalValueM (M := BM) m1 (.GetDiscriminant place) = .ok ((.Int d, .Int dty), m2) ∧
      m2.mem.memory = m1.mem.memory by
    obtain ⟨m2, h1, h2⟩ := h
    rw [evalValueM_bm_eq] at h1
    exact ⟨m2, h1, h2⟩
  simp only [evalStatementM] at hassign
  rw [hp] at hassign
  dsimp only [bind, Except.bind] at hassign
  obtain ⟨⟨⟨v, vTy⟩, mMid⟩, hv, hstoreSt⟩ := ep1_bind_ok hassign
  obtain ⟨hfMid, hmemMid⟩ := ep1_evalValueM_preserves_shape_bm (.Variant d dataExpr enumTy) m mMid (v, vTy) hv
  obtain ⟨dv, rfl⟩ := ep1_evalValueM_variant_inv hv
  unfold placeStoreM at hstoreSt
  have hal : rp.aligned = true := by
    cases h : rp.aligned
    · simp [h, ub] at hstoreSt
    · rfl
  simp only [hal, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hstoreSt
  unfold typedStoreM at hstoreSt
  split at hstoreSt
  · obtain ⟨enumBytes, hencEnum, hstoreSt⟩ := ep1_bind_ok hstoreSt
    obtain ⟨cm1, hcmStore, hpRet⟩ := ep1_bind_ok hstoreSt
    have hm1Eq : m1 = { mMid with mem := cm1 } := (ep1_pure_ok hpRet).symm
    unfold ConcurrentMemory.store at hcmStore
    obtain ⟨bm1, hbmStore, hcmRet⟩ := ep1_bind_ok hcmStore
    have hcmMem : cm1.memory = bm1 := by
      have h := (ep1_pure_ok hcmRet).symm; rw [h]
    have hm1Mem : m1.mem.memory = bm1 := by rw [hm1Eq, hcmMem]
    have hbmStore' : BM.store mMid.mem.memory rp.ptr.thin_pointer enumBytes ⟨1⟩ = .ok bm1 := hbmStore
    have hshapeStore : ep1AllocShape bm1.allocations = ep1AllocShape mMid.mem.memory.allocations :=
      ep1_BM_store_shape hbmStore'
    have hf1 : ep1CurFrameViewM m1 = ep1CurFrameViewM m := by
      rw [hm1Eq]; exact hfMid
    have hsTotal : ep1AllocShape m1.mem.memory.allocations = ep1AllocShape m.mem.memory.allocations := by
      rw [hm1Mem, hshapeStore, hmemMid]
    have hp1 : evalPlaceM (M := BM) m1 place = .ok ((rp, .Enum variants dty discr sz al), m1) := by
      rw [evalPlaceM_bm_eq] at hp ⊢
      rw [(ep1_evalPlaceM_chain_same_shape place hc).2 m m1 hf1 hsTotal, hp]
    rw [ep1_encodeM_enum_variant, ep1_encodeVariantM_eq_of_mapGet variants.entries d var dv hvar] at hencEnum
    obtain ⟨varBytes, _, hencTags⟩ := ep1_bind_ok hencEnum
    obtain ⟨_, htagsRec⟩ := ep1_encodeDiscriminantM_bytes_recover var.tagger.entries varBytes enumBytes hencTags
    have hreadable : ∀ off ty tagVal pre suf bs,
        var.tagger.entries = pre ++ (off, (ty, tagVal)) :: suf →
        Type.encodeIntM (M := BM) ty (.Int tagVal) = .ok bs →
        (∀ t ∈ suf, off.bytes + ty.size.bytes ≤ t.1.bytes ∨ t.1.bytes + t.2.1.size.bytes ≤ off.bytes) →
        ep1TagReadableBM m1 rp.ptr.thin_pointer off ty bs := by
      intro off ty tagVal pre suf bs hEq hencT hdisj
      have hmemT : (off, (ty, tagVal)) ∈ var.tagger.entries := by rw [hEq]; simp
      obtain ⟨hoffHi, haddrLo, haddrHi⟩ := haddr (off, (ty, tagVal)) hmemT
      dsimp only at hoffHi haddrLo haddrHi
      obtain ⟨hfit, hsubEnum⟩ := htagsRec off ty tagVal pre suf bs hEq hencT hdisj
      exact ep1_store_enum_tag_readable_bm mMid m1 rp.ptr.thin_pointer enumBytes bm1
        hbmStore' hm1Mem off ty bs hoffHi haddrLo haddrHi hfit hsubEnum (ep1_encodeIntM_length hencT)
    obtain ⟨m2, hdd, hmem2⟩ :=
      ep1_decodeDiscriminantM_of_matches_bm m1 rp.ptr.thin_pointer var.tagger.entries hreadable hmatch m1 rfl
    refine ⟨m2, ?_, hmem2⟩
    rw [(ep1_evalValueM_getDiscriminant_complete_spec (M := BM)).1 m1 m1 place rp variants dty discr sz al hp1 hal]
    unfold ep1GetDiscriminantCore
    dsimp only
    rw [hdd]; rfl
  · simp [specPanic] at hstoreSt

/-! #### MiniRust representation-relation Galois law for `Type.Union` & sharp witnesses -/

/-- Exact transcription of MiniRust's `DefinedRelation for AbstractByte` (`spec/lang/representation.md`):
`Uninit ≤ _` and `Init b1 none ≤ Init b2 _` iff `b1 = b2`, and `Init b1 (some p1) ≤ Init b2 (some p2)`
iff `b1 = b2 ∧ p1 = p2`. -/
def ep1ByteLeDefined {P : Type} : Gen.AbstractByte P → Gen.AbstractByte P → Prop
  | .Uninit, _ => True
  | .Init b1 none, .Init b2 _ => b1 = b2
  | .Init b1 (some p1), .Init b2 (some p2) => b1 = b2 ∧ p1 = p2
  | _, _ => False

/-- Bytewise `DefinedRelation` on lists (`spec/lang/representation.md`). -/
def ep1BytesLeDefined {P : Type} (bs1 bs2 : List (Gen.AbstractByte P)) : Prop :=
  bs1.length = bs2.length ∧ ∀ (p : Nat), match bs1[p]?, bs2[p]? with
    | some b1, some b2 => ep1ByteLeDefined b1 b2
    | none, none => True
    | _, _ => False

private theorem ep1ByteLeDefined_refl {P : Type} (b : Gen.AbstractByte P) : ep1ByteLeDefined b b := by
  cases b with
  | Uninit => trivial
  | Init d p => cases p <;> simp [ep1ByteLeDefined]

/-- **MiniRust representation-relation Galois law (`encode(decode(bs)) ≤_defined bs`) and idempotence
(`decode(encode(decode(bs))) = decode(bs)`) for `Type::Union` across all `Memory` and ALL chunk layouts**
(empty, gapped, overlapping, or out-of-order): re-encoding any decoded union value preserves every
chunk-covered byte exactly, resets every uncovered padding byte to `Uninit` (hence strictly
`≤_defined bs`), and decodes back to the exact same value. -/
theorem ep1_union_decode_encode_galois_and_idempotent
    {M : Type} [Gen.Memory M] [MemoryOps M]
    (fields : List (Gen.Offset × Gen.Type)) (chunks : List (Gen.Offset × Size))
    (sz : Size) (al : Align)
    (bs : List (Gen.AbstractByte (Gen.Memory.Provenance M))) (v : Gen.Value M)
    (hdec : Type.decodeM (M := M) (.Union fields chunks sz al) bs = .ok (some v)) :
    bs.length = sz.bytes ∧
    ∃ bs',
      Type.encodeM (.Union fields chunks sz al) v = .ok bs' ∧
      bs'.length = sz.bytes ∧
      (∀ p, bs'[p]? = if ep1Covered chunks p then bs[p]? else if p < sz.bytes then some .Uninit else none) ∧
      ep1BytesLeDefined bs' bs ∧
      Type.decodeM (M := M) (.Union fields chunks sz al) bs' = .ok (some v) := by
  unfold Type.decodeM at hdec
  split at hdec
  · simp [specPanic] at hdec
  · rename_i hlenNe
    have hlen : bs.length = sz.bytes := by omega
    obtain ⟨chunkData, hmap, hret⟩ := ep1_bind_ok hdec
    have hvEq : Gen.Value.Union chunkData = v := Option.some.inj (ep1_pure_ok hret)
    subst hvEq
    obtain ⟨rfl, hrange⟩ := ep1_mapM_subslice_eq bs chunks chunkData hmap
    obtain ⟨out, hencChunks, houtLen, hout⟩ := ep1_encodeUnionChunksM_pointwise bs chunks
      (List.replicate sz.bytes .Uninit) (by simp [hlen]) hrange
    have houtSz : out.length = sz.bytes := houtLen.trans hlen
    have hpoint : ∀ p, out[p]? = if ep1Covered chunks p then bs[p]? else if p < sz.bytes then some .Uninit else none := by
      intro p
      rw [hout p]
      by_cases hc : ep1Covered chunks p = true
      · simp [hc]
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, List.getElem?_replicate]
    have hleDef : ep1BytesLeDefined out bs := by
      refine ⟨houtLen, fun p => ?_⟩
      rw [hpoint p]
      by_cases hp : p < sz.bytes
      · have hpBs : p < bs.length := hlen.symm ▸ hp
        rw [List.getElem?_eq_getElem hpBs]
        by_cases hc : ep1Covered chunks p = true
        · simp only [hc, ↓reduceIte]
          exact ep1ByteLeDefined_refl _
        · simp only [hc, Bool.false_eq_true, hp, ↓reduceIte, ep1ByteLeDefined]
      · have hpBs : ¬(p < bs.length) := hlen.symm ▸ hp
        rw [List.getElem?_eq_none (Nat.le_of_not_lt hpBs)]
        by_cases hc : ep1Covered chunks p = true <;> simp [hc, hp]
    refine ⟨hlen, out, ?_, houtSz, hpoint, hleDef, ?_⟩
    · unfold Type.encodeM
      simp only [List.length_map, ne_eq, not_true_eq_false, ↓reduceIte]
      exact hencChunks
    · unfold Type.decodeM
      simp only [houtSz, ne_eq, not_true_eq_false, ↓reduceIte]
      have hsame : ∀ c ∈ chunks, (out.drop c.1.bytes).take c.2.bytes =
          (bs.drop c.1.bytes).take c.2.bytes := by
        intro c hc
        apply List.ext_getElem?
        intro i
        simp only [List.getElem?_take, List.getElem?_drop]
        by_cases hi : i < c.2.bytes
        · simp only [hi, ↓reduceIte]
          rw [hout]
          have hcov : ep1Covered chunks (c.1.bytes + i) = true := by
            simp only [ep1Covered, List.any_eq_true, decide_eq_true_eq]
            exact ⟨c, hc, by omega, by omega⟩
          simp [hcov]
        · simp [hi]
      have key : ∀ cs : List (Gen.Offset × Size), (∀ c ∈ cs, c ∈ chunks) →
          cs.mapM (fun (x : Gen.Offset × Size) =>
            subsliceWithLength out (x.1.bytes : Int) (x.2.bytes : Int)) =
          .ok (cs.map (fun c => (bs.drop c.1.bytes).take c.2.bytes)) := by
        intro cs
        induction cs with
        | nil => intro _; rfl
        | cons c rest ih =>
          intro hsub
          have hc := hsub c (List.mem_cons_self ..)
          have hr := hrange c hc
          have hsl : subsliceWithLength out (c.1.bytes : Int) (c.2.bytes : Int) =
              .ok ((bs.drop c.1.bytes).take c.2.bytes) := by
            unfold subsliceWithLength
            have hcond : (0 : Int) ≤ (c.1.bytes : Int) ∧ (0 : Int) ≤ (c.2.bytes : Int) ∧
                (c.1.bytes : Int) + (c.2.bytes : Int) ≤ (out.length : Int) := by
              rw [houtLen]; omega
            simp only [hcond, and_self, ↓reduceIte, Int.toNat_natCast, pure, Except.pure, hsame c hc]
          simp only [List.mapM_cons, hsl, ih (fun c' hc' => hsub c' (List.mem_cons_of_mem _ hc')),
            List.map_cons, bind, Except.bind, pure, Except.pure]
      simp only [key chunks (fun _ h => h), bind, Except.bind, pure, Except.pure]

/-- **Sharp boundary + multi-tag end-to-end witness (`Mach` and `MachTB` + `MachTB.wfLive`):**
1. **Overlapping-chunk `checkValue`-valid non-roundtrip counterexample** (sharp boundary of B3's
   `ep1_evalValueM_union_decode_encode_roundtrip_any_chunks`): a manually constructed `Value.Union`
   whose overlapping chunks `[(0, 3), (1, 3)]` *disagree* on `[1..3)` passes `checkValue`/`checkValueM`,
   yet `decode (encode v) ≠ some v` (proving single-buffer provenance from `ValueExpr.Union` or
   `Type.decode` is strictly necessary when chunks overlap).
2. **2-tag, 2-level `Discriminator` enum** (tag 0 at offset 0, tag 1 at offset 1, `u32` payload at
   offset 4) executing BOTH `SetDiscriminant → GetDiscriminant` AND
   `Assign (.Variant ...) → GetDiscriminant → Load (.Downcast ...)` on `Mach` and `MachTB` with
   `m2.mem.memory = m1.mem.memory` and `MachTB.wfLive`. -/
theorem ep1_union_overlapping_checkValue_not_roundtrip_and_multitag_assign_witness :
    let overlapUnionTy : Gen.Type :=
      .Union [(⟨0⟩, .Int ep1U32)] [(⟨0⟩, ⟨3⟩), (⟨1⟩, ⟨3⟩)] ⟨4⟩ ⟨4⟩
    let disagreeValBM : Val :=
      .Union [[.Init 1 none, .Init 2 none, .Init 3 none],
              [.Init 9 none, .Init 8 none, .Init 7 none]]
    let disagreeValTB : Gen.Value TBM :=
      .Union [[.Init 1 none, .Init 2 none, .Init 3 none],
              [.Init 9 none, .Init 8 none, .Init 7 none]]
    let overwrittenValBM : Val :=
      .Union [[.Init 1 none, .Init 9 none, .Init 8 none],
              [.Init 9 none, .Init 8 none, .Init 7 none]]
    let overwrittenValTB : Gen.Value TBM :=
      .Union [[.Init 1 none, .Init 9 none, .Init 8 none],
              [.Init 9 none, .Init 8 none, .Init 7 none]]
    -- 2-tag 2-level enum: variant 0 has tags (0:u8=0), variant 1 has tags (0:u8=1, 1:u8=2) + u32 @ 4
    let var0Ty : Gen.Type := .Tuple [] ⟨⟨8⟩, ⟨4⟩, none⟩ none
    let var1Ty : Gen.Type := .Tuple [(⟨4⟩, .Int ep1U32)] ⟨⟨8⟩, ⟨4⟩, none⟩ none
    let var0 : Gen.Variant := ⟨var0Ty, ⟨[(⟨0⟩, (ep1U8, 0))]⟩⟩
    let var1 : Gen.Variant := ⟨var1Ty, ⟨[(⟨0⟩, (ep1U8, 1)), (⟨1⟩, (ep1U8, 2))]⟩⟩
    let discr2 : Gen.Discriminator :=
      .Branch ⟨0⟩ ep1U8 .Invalid ⟨[
        ((0, 1), .Known 0),
        ((1, 2), .Branch ⟨1⟩ ep1U8 .Invalid ⟨[((2, 3), .Known 1)]⟩)
      ]⟩
    let multiTagEnumTy : Gen.Type :=
      .Enum ⟨[(0, var0), (1, var1)]⟩ ep1U8 discr2 ⟨8⟩ ⟨4⟩
    let mBM := ep1MachBM
      [{ data := List.replicate 8 .Uninit, addr := 0x200, align := ⟨4⟩, kind := .Stack,
         live := true, extra := () }]
      [(⟨⟨0⟩⟩, ⟨0x200, some (⟨0⟩, ())⟩)]
      [(⟨⟨0⟩⟩, multiTagEnumTy)]
    let mTB := liftMachToTB mBM
    -- Part 1: overlapping checkValue-valid Union disagreement
    (checkValue disagreeValBM overlapUnionTy (some mBM) = .ok () ∧
     checkValueM disagreeValTB overlapUnionTy (some mTB) = .ok () ∧
     (Type.encode overlapUnionTy disagreeValBM >>= Type.decode overlapUnionTy) =
       .ok (some overwrittenValBM) ∧
     overwrittenValBM ≠ disagreeValBM ∧
     (Type.encodeM overlapUnionTy disagreeValTB >>= Type.decodeM (M := TBM) overlapUnionTy) =
       .ok (some overwrittenValTB) ∧
     overwrittenValTB ≠ disagreeValTB) ∧
    -- Part 2: 2-tag SetDiscriminant -> GetDiscriminant AND Assign (Variant) -> GetDiscriminant -> Load (Downcast)
    (∃ m1 m2,
      evalStatement mBM (.SetDiscriminant (.Local ⟨⟨0⟩⟩) 1) = .ok m1 ∧
      evalValue m1 (.GetDiscriminant (.Local ⟨⟨0⟩⟩)) = .ok ((.Int 1, .Int ep1U8), m2) ∧
      m2.mem.memory = m1.mem.memory) ∧
    (∃ t1 t2,
      evalStatementM mTB (.SetDiscriminant (.Local ⟨⟨0⟩⟩) 1) = .ok t1 ∧
      evalValueM t1 (.GetDiscriminant (.Local ⟨⟨0⟩⟩)) = .ok ((.Int 1, .Int ep1U8), t2) ∧
      t2.mem.memory = t1.mem.memory ∧ MachTB.wfLive t2) ∧
    (∃ m1 m2 m3,
      evalStatement mBM (.Assign (.Local ⟨⟨0⟩⟩)
        (.Variant 1 (.Tuple [.Constant (.Int 0xCAFEBABE) (.Int ep1U32)] var1Ty) multiTagEnumTy)) = .ok m1 ∧
      evalValue m1 (.GetDiscriminant (.Local ⟨⟨0⟩⟩)) = .ok ((.Int 1, .Int ep1U8), m2) ∧
      m2.mem.memory = m1.mem.memory ∧
      evalValue m2 (.Load (.Downcast (.Local ⟨⟨0⟩⟩) 1)) =
        .ok ((.Tuple [.Int 0xCAFEBABE], var1Ty), m3)) ∧
    (∃ t1 t2 t3,
      evalStatementM mTB (.Assign (.Local ⟨⟨0⟩⟩)
        (.Variant 1 (.Tuple [.Constant (.Int 0xCAFEBABE) (.Int ep1U32)] var1Ty) multiTagEnumTy)) = .ok t1 ∧
      evalValueM t1 (.GetDiscriminant (.Local ⟨⟨0⟩⟩)) = .ok ((.Int 1, .Int ep1U8), t2) ∧
      t2.mem.memory = t1.mem.memory ∧
      evalValueM t2 (.Load (.Downcast (.Local ⟨⟨0⟩⟩) 1)) =
        .ok ((.Tuple [.Int 0xCAFEBABE], var1Ty), t3) ∧
      MachTB.wfLive t3) := by
  intro overlapUnionTy disagreeValBM disagreeValTB overwrittenValBM overwrittenValTB
    var0Ty var1Ty var0 var1 discr2 multiTagEnumTy mBM mTB
  have hwf0 : MachTB.wfLive mTB := liftMachToTB_wfLive mBM
  have hpBM : evalPlace mBM (.Local ⟨⟨0⟩⟩) =
      .ok ((⟨⟨⟨0x200, some (⟨0⟩, ())⟩, none⟩, true⟩, multiTagEnumTy), mBM) := by ep1_kernel_rfl
  have hpTB : evalPlaceM mTB (.Local ⟨⟨0⟩⟩) =
      .ok ((⟨⟨⟨0x200, some (⟨0⟩, [])⟩, none⟩, true⟩, multiTagEnumTy), mTB) := by ep1_kernel_rfl
  have hmatchBM : Ep1DiscrMatchesTags BM var1.tagger.entries discr2 1 :=
    .Branch ⟨0⟩ ep1U8 .Invalid _ 1 1 [] [(⟨1⟩, (ep1U8, 2))] [.Init 1 none]
      rfl (by ep1_kernel_rfl) (by ep1_kernel_rfl)
      (by intro t ht; simp at ht; rcases ht with rfl; left; decide)
      (.Branch ⟨1⟩ ep1U8 .Invalid _ 2 1 [(⟨0⟩, (ep1U8, 1))] [] [.Init 2 none]
        rfl (by ep1_kernel_rfl) (by ep1_kernel_rfl)
        (by intro t ht; cases ht)
        (.Known 1))
  have hmatchTB : Ep1DiscrMatchesTags TBM var1.tagger.entries discr2 1 :=
    .Branch ⟨0⟩ ep1U8 .Invalid _ 1 1 [] [(⟨1⟩, (ep1U8, 2))] [.Init 1 none]
      rfl (by ep1_kernel_rfl) (by ep1_kernel_rfl)
      (by intro t ht; simp at ht; rcases ht with rfl; left; decide)
      (.Branch ⟨1⟩ ep1U8 .Invalid _ 2 1 [(⟨0⟩, (ep1U8, 1))] [] [.Init 2 none]
        rfl (by ep1_kernel_rfl) (by ep1_kernel_rfl)
        (by intro t ht; cases ht)
        (.Known 1))
  have haddr : ∀ t ∈ var1.tagger.entries,
      (t.1.bytes : Int) < (2 : Int) ^ 63 ∧
      0 ≤ (0x200 : Int) + (t.1.bytes : Int) ∧
      (0x200 : Int) + (t.1.bytes : Int) < (2 : Int) ^ 64 := by
    intro t ht
    simp only [var1, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> decide
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · ep1_kernel_rfl
  · intro h; simp [overwrittenValBM, disagreeValBM] at h
  · ep1_kernel_rfl
  · intro h; simp [overwrittenValTB, disagreeValTB] at h
  · -- Part 2a: Mach SetDiscriminant -> GetDiscriminant via universal multi-tag theorem
    have hset : (evalStatement mBM (.SetDiscriminant (.Local ⟨⟨0⟩⟩) 1)).isOk = true := by ep1_kernel_rfl
    have hEx : ∃ m1, evalStatement mBM (.SetDiscriminant (.Local ⟨⟨0⟩⟩) 1) = .ok m1 := by
      cases h : evalStatement mBM (.SetDiscriminant (.Local ⟨⟨0⟩⟩) 1) with
      | error e => simp [h, Except.isOk, Except.toBool] at hset
      | ok m1 => exact ⟨m1, rfl⟩
    obtain ⟨m1, hm1⟩ := hEx
    obtain ⟨m2, hm2, hmem2⟩ := ep1_setDiscriminant_multitag_then_getDiscriminant_bm
      mBM m1 (.Local ⟨⟨0⟩⟩) (.Local _) _ _ ep1U8 discr2 ⟨8⟩ ⟨4⟩ 1 var1 hpBM rfl hmatchBM hm1
    exact ⟨m1, m2, hm1, hm2, hmem2⟩
  · -- Part 2b: MachTB SetDiscriminant -> GetDiscriminant via universal multi-tag theorem
    have hset : (evalStatementM mTB (.SetDiscriminant (.Local ⟨⟨0⟩⟩) 1)).isOk = true := by ep1_kernel_rfl
    have hEx : ∃ t1, evalStatementM mTB (.SetDiscriminant (.Local ⟨⟨0⟩⟩) 1) = .ok t1 := by
      cases h : evalStatementM mTB (.SetDiscriminant (.Local ⟨⟨0⟩⟩) 1) with
      | error e => simp [h, Except.isOk, Except.toBool] at hset
      | ok t1 => exact ⟨t1, rfl⟩
    obtain ⟨t1, ht1⟩ := hEx
    obtain ⟨t2, ht2, hmem2⟩ := ep1_setDiscriminant_multitag_then_getDiscriminant_tb
      mTB t1 (.Local ⟨⟨0⟩⟩) (.Local _) _ _ ep1U8 discr2 ⟨8⟩ ⟨4⟩ 1 var1 hpTB rfl hmatchTB ht1
    have hwf1 : MachTB.wfLive t1 := evalStatementM_tb_wfLive hwf0 ht1
    have hwf2 : MachTB.wfLive t2 := evalValueM_tb_wfLive _ hwf1 ht2
    exact ⟨t1, t2, ht1, ht2, hmem2, hwf2⟩
  · -- Part 2c: Mach Assign (Variant) -> GetDiscriminant -> Load (Downcast)
    let srcExpr : Gen.ValueExpr :=
      .Variant 1 (.Tuple [.Constant (.Int 0xCAFEBABE) (.Int ep1U32)] var1Ty) multiTagEnumTy
    have hseq : (do
        let m1 ← evalStatement mBM (.Assign (.Local ⟨⟨0⟩⟩) srcExpr)
        let (_, m2) ← evalValue m1 (.GetDiscriminant (.Local ⟨⟨0⟩⟩))
        let (r3, _) ← evalValue m2 (.Load (.Downcast (.Local ⟨⟨0⟩⟩) 1))
        pure r3) = .ok (.Tuple [.Int 0xCAFEBABE], var1Ty) := by ep1_kernel_rfl
    obtain ⟨m1, hm1, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨m2, hm2, hmem2⟩ := ep1_assign_variant_then_getDiscriminant_bm
      mBM m1 (.Local ⟨⟨0⟩⟩) (.Local _) _ _ ep1U8 discr2 ⟨8⟩ ⟨4⟩ 1 var1 _ multiTagEnumTy hpBM rfl hmatchBM haddr hm1
    rw [hm2] at hseq
    dsimp only [bind, Except.bind] at hseq
    obtain ⟨⟨r3, m3⟩, hm3, hret⟩ := ep1_bind_ok hseq
    obtain rfl := ep1_pure_ok hret
    exact ⟨m1, m2, m3, hm1, hm2, hmem2, hm3⟩
  · -- Part 2d: MachTB Assign (Variant) -> GetDiscriminant -> Load (Downcast)
    let srcExpr : Gen.ValueExpr :=
      .Variant 1 (.Tuple [.Constant (.Int 0xCAFEBABE) (.Int ep1U32)] var1Ty) multiTagEnumTy
    have hseq : (do
        let t1 ← evalStatementM mTB (.Assign (.Local ⟨⟨0⟩⟩) srcExpr)
        let (_, t2) ← evalValueM t1 (.GetDiscriminant (.Local ⟨⟨0⟩⟩))
        let (r3, _) ← evalValueM t2 (.Load (.Downcast (.Local ⟨⟨0⟩⟩) 1))
        pure r3) = .ok (.Tuple [.Int 0xCAFEBABE], var1Ty) := by ep1_kernel_rfl
    obtain ⟨t1, ht1, hseq⟩ := ep1_bind_ok hseq
    obtain ⟨t2, ht2, hmem2⟩ := ep1_assign_variant_then_getDiscriminant_tb
      mTB t1 (.Local ⟨⟨0⟩⟩) (.Local _) _ _ ep1U8 discr2 ⟨8⟩ ⟨4⟩ 1 var1 _ multiTagEnumTy hpTB rfl hmatchTB haddr ht1
    rw [ht2] at hseq
    dsimp only [bind, Except.bind] at hseq
    obtain ⟨⟨r3, t3⟩, ht3, hret⟩ := ep1_bind_ok hseq
    obtain rfl := ep1_pure_ok hret
    have hwf1 : MachTB.wfLive t1 := evalStatementM_tb_wfLive hwf0 ht1
    have hwf2 : MachTB.wfLive t2 := evalValueM_tb_wfLive _ hwf1 ht2
    have hwf3 : MachTB.wfLive t3 := evalValueM_tb_wfLive _ hwf2 ht3
    exact ⟨t1, t2, t3, ht1, ht2, hmem2, ht3, hwf3⟩

#check_theorem_deps "[EP1-EXPR-AUDIT]"
  ep1_type_meta_kind_eq_layout_meta_kind
  ep1_evalUnOpM_computeSize_computeAlign_mach_indep
  ep1_evalUnOpM_meta_unops_spec
  ep1_evalPlaceM_downcast_spec_and_wfLive
  ep1_evalValueM_union_variant_getDiscriminant_spec_and_wfLive
  ep1_enum_variant_downcast_getDiscriminant_witness
  ep1_getDiscriminant_tree_borrows_read_access_witness
  ep1_union_construct_punning_and_errors_witness
  ep1_meta_unops_unsized_dst_and_errors_witness
  ep1_decodeDiscriminantChildrenM_eq_find_map
  ep1_decodeDiscriminantChildren_eq_find_map
  ep1_evalValueM_getDiscriminant_complete_spec
  ep1_evalValueM_union_complete_spec
  ep1_evalM_type_mismatch_panics_and_error_propagation
  ep1_evalUnOpM_getMetadata_complete_spec
  ep1_Type_layout_error_is_specPanic
  ep1_evalUnOpM_meta_unops_error_is_specPanic_or_unsupported
  ep1_getDiscriminant_nested_tags_access_log_and_dereferenceability_witness
  ep1_getDiscriminant_tree_borrows_nested_gap_byte_witness
  ep1_meta_unops_end_to_end_evalValue_witness
  ep1_variant_union_ill_formed_ast_specPanic_witness
  ep1_getDiscriminant_ordering_agrees_with_model_and_lowering
  ep1_downcast_variant_lookup_agrees_with_representation
  ep1_tb_permission_read_idempotent
  ep1_evalValueM_load_enum_implies_getDiscriminant_tb
  ep1_evalValue_load_enum_implies_getDiscriminant_bm
  ep1_evalValueM_union_produces_valid_value_and_roundtrip
  ep1_meta_unops_nonVTable_never_unsupported_and_vtable_layout_total
  ep1_evalUnOpM_getMetadata_then_computeSize_computeAlign
  ep1_misaligned_downcast_zst_slice_and_multitag_witness
  ep1_evalValueM_getDiscriminant_frame
  ep1_evalValue_getDiscriminant_readonly_bm
  ep1_evalValueM_getDiscriminant_preserves_bytes_tb
  ep1_evalM_downcast_variant_union_add_no_machine_effect
  ep1_evalValueM_variant_checkValue
  ep1_getDiscriminant_address_hypotheses_necessary_and_no_result_check_witness
  ep1_getDiscriminant_tb_success_implies_bm_success
  ep1_liftMachToTB_allocView
  ep1_getDiscriminant_local_lifted_tb_success_implies_bm_success
  ep1_tb_permission_write_then_read_idempotent
  ep1_setDiscriminant_then_getDiscriminant_tb
  ep1_setDiscriminant_then_getDiscriminant_bm
  ep1_evalPlaceM_liftMachToTB_exact
  ep1_getDiscriminant_liftMachToTB_iff
  ep1_evalPlaceM_downcast_field_tb_to_bm
  ep1_evalValueM_union_encode_total_and_disjoint_roundtrip
  ep1_union_gapped_chunks_and_setDiscr_downcast_field_witness
  ep1_evalValueM_union_decode_encode_roundtrip_any_chunks
  ep1_union_overlapping_chunks_roundtrip_witness
  ep1_evalPlaceM_chain_same_shape
  ep1_setDiscriminant_multitag_then_getDiscriminant_tb
  ep1_setDiscriminant_multitag_then_getDiscriminant_bm
  ep1_assign_variant_then_getDiscriminant_tb
  ep1_assign_variant_then_getDiscriminant_bm
  ep1_union_decode_encode_galois_and_idempotent
  ep1_union_overlapping_checkValue_not_roundtrip_and_multitag_assign_witness
  ep1_vtable_dyn_safe_ptr_and_unops_witness
  ep1_vtable_dyn_safe_ptr_ub_witness
  ep1_evalUnOpM_meta_unops_some_mach_error_is_specPanic
  ep1_vtable_error_precedence_and_corrupt_table_witness
  ep1_vtable_unsized_struct_tail_packed_and_overflow_witness
  ep1_vtable_dyn_tree_borrows_retag_protector_and_cells_witness
  ep1_vtable_zst_uninhabited_and_deref_witness
  ep1_vtable_constructWidePointer_boundary_and_decode_witness
  ep1_vtable_congr_mach_hypotheses_necessary_witness
  ep1_evalUnOpM_getMetadata_then_computeSize_computeAlign_dyn
  ep1_evalStatement_deinit_traitObject_spec
  ep1_evalStatementM_deinit_traitObject_spec
  ep1_vtable_deinit_traitObject_and_sized_view_witness
  ep1_evalPlace_deref_safe_traitObject_misaligned_specPanic
  ep1_evalPlaceM_deref_safe_traitObject_misaligned_specPanic
  ep1_cellsToFreezeMask_zero_dichotomy
  ep1_retag_ptr_traitObject_zst_noProv_cells_dichotomy

#assert_standard_axioms
  vtableFromPtrM_bm_eq
  vtableFromPtr_ok_iff_vtableLookup_ok
  vtableFromPtrM_ok_iff_vtableLookupM_ok
  vtableFromPtr_ub_of_not_mem
  vtableFromPtrM_ub_of_not_mem
  vtableFromPtr_eq_mapIndex_of_find
  vtableFromPtrM_eq_mapIndex_of_find
  checkPtrMetadata_none
  checkPtrMetadataM_none
  checkPtrMetadata_vtable_eq_checkPtr
  checkPtrMetadataM_vtable_eq_checkPtrM
  compute_size_and_align_traitObject
  compute_size_and_align_tuple_traitObject
  checkPtr_vtablePtr_eq
  checkPtrM_vtablePtr_eq
  checkPtr_vtablePtr_ok
  checkPtrM_vtablePtr_ok
  checkPtr_vtablePtr_invalid_ptr_ub
  checkPtrM_vtablePtr_invalid_ptr_ub
  checkPtr_vtablePtr_wrong_trait_ub
  checkPtrM_vtablePtr_wrong_trait_ub
  checkPtr_vtablePtr_outOfBounds_ub
  checkPtrM_vtablePtr_outOfBounds_ub
  checkPtr_vtablePtr_nonNone_meta_ub
  checkPtrM_vtablePtr_nonNone_meta_ub
  checkPtr_rawTraitObject_eq_vtablePtr
  checkPtrM_rawTraitObject_eq_vtablePtr
  checkPtr_traitObject_metadata_error
  checkPtrM_traitObject_metadata_error
  checkPtr_traitObject_eq_sized
  checkPtrM_traitObject_eq_sized
  checkPtr_traitObject_ok
  checkPtrM_traitObject_ok
  checkPtr_traitObject_unaligned_ub
  checkPtrM_traitObject_unaligned_ub
  checkPtr_traitObject_nonDereferenceable_ub
  checkPtrM_traitObject_nonDereferenceable_ub
  checkPtr_traitObject_null_ub
  checkPtrM_traitObject_null_ub
  checkPtr_traitObject_uninhabited_ub
  checkPtrM_traitObject_uninhabited_ub
  checkPtr_traitObject_zst_ok
  checkPtrM_traitObject_zst_tb_ok
  retag_ptr_traitObject_zst_noProv
  evalPlace_deref_safe_traitObject
  evalPlaceM_deref_safe_traitObject
  evalBinOp_constructWidePointer_unsupported
  evalBinOpM_constructWidePointer_unsupported
  evalValue_constructWidePointer_ok_operands_unsupported
  evalValueM_constructWidePointer_ok_operands_unsupported
  decode_vtablePointer_and_checkValue_dyn
  decode_vtablePointer_and_checkValueM_dyn
  checkPtr_congr_vtables
  checkValue_congr_vtables
  evalUnOp_congr_vtables
  checkPtrM_congr_mach
  checkValueM_congr_mach
  evalUnOpM_congr_mach
  checkPtr_tuple_traitObject_metadata_error
  checkPtrM_tuple_traitObject_metadata_error
  checkPtr_tuple_traitObject_eq_sized
  checkPtrM_tuple_traitObject_eq_sized
  checkPtr_tuple_traitObject_size_overflow_ub
  checkPtrM_tuple_traitObject_size_overflow_ub
  evalUnOp_tuple_traitObject_size_align
  evalUnOpM_tuple_traitObject_size_align
  getMetadataSanity
  checkValue_nonVTable_meta_ok_or_ub
  checkValueM_nonVTable_meta_ok_or_ub
  evalUnOp_getMetadata_eq_sanity
  evalUnOpM_getMetadata_eq_sanity
  evalUnOpM_getMetadata_nonVTable_ok_or_specPanic
  evalUnOp_vtableMethodLookup_eq_fnPointer
  evalUnOpM_vtableMethodLookup_eq_fnPointer
  ep1_evalUnOpM_meta_unops_some_mach_error_is_specPanic
  ep1_vtable_dyn_safe_ptr_and_unops_witness
  ep1_vtable_dyn_safe_ptr_ub_witness
  ep1_vtable_error_precedence_and_corrupt_table_witness
  ep1_vtable_unsized_struct_tail_packed_and_overflow_witness
  ep1_vtable_dyn_tree_borrows_retag_protector_and_cells_witness
  ep1_vtable_zst_uninhabited_and_deref_witness
  ep1_vtable_constructWidePointer_boundary_and_decode_witness
  ep1_vtable_congr_mach_hypotheses_necessary_witness
  ep1_evalUnOpM_getMetadata_then_computeSize_computeAlign_dyn
  ep1_evalStatement_deinit_traitObject_spec
  ep1_evalStatementM_deinit_traitObject_spec
  ep1_vtable_deinit_traitObject_and_sized_view_witness
  ep1_evalPlace_deref_safe_traitObject_misaligned_specPanic
  ep1_evalPlaceM_deref_safe_traitObject_misaligned_specPanic
  ep1_cellsToFreezeMask_zero_dichotomy
  ep1_retag_ptr_traitObject_zst_noProv_cells_dichotomy

/-- Verify that every newly added or modified executable `Interp` definition in
Episode 1 is strictly computable (`Classical.choice`-free, `sorryAx`-free, and
`Lean.ofReduceBool`-free). -/
elab "#assert_ep1_interp_no_choice" : command => do
  let targets : Array Lean.Name := #[
    ``MiniRustSpec.Interp.Type.meta_kind,
    ``MiniRustSpec.Interp.PointerMetaKind.ty,
    ``MiniRustSpec.Interp.evalUnOp,
    ``MiniRustSpec.Interp.evalUnOpM,
    ``MiniRustSpec.Interp.vtableFromPtr,
    ``MiniRustSpec.Interp.vtableFromPtrM,
    ``MiniRustSpec.Interp.checkPtrMetadata,
    ``MiniRustSpec.Interp.checkPtrMetadataM,
    ``MiniRustSpec.Interp.checkPtr,
    ``MiniRustSpec.Interp.checkPtrM,
    ``MiniRustSpec.Interp.evalPlace,
    ``MiniRustSpec.Interp.evalPlaceM,
    ``MiniRustSpec.Interp.evalValue,
    ``MiniRustSpec.Interp.evalValueM
  ]
  for c in targets do
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      unless a == ``propext || a == ``Quot.sound do
        throwError "[EP1-INTERP-COMPUTABLE] {c} depends on non-computable or non-standard axiom {a}"
  logInfo m!"[EP1-INTERP-COMPUTABLE] verified {targets.size} Interp defs are Classical.choice-free"

#assert_ep1_interp_no_choice

end Ep1ExprAndMetaUnOpAudit

/-- Exhaustively verify that every declaration across every imported
`MiniRustSpec.*` module in the environment — as well as every declaration
elaborated in `MiniRustSpec.Audit` itself (`env.constants.map₂`) — depends only
on Lean's standard axioms (`propext`, `Quot.sound`, `Classical.choice`). -/
elab "#assert_all_minirustspec_standard_axioms" : command => do
  let env ← getEnv
  let mut checked : Nat := 0
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if (`MiniRustSpec).isPrefixOf modName then
      let modData := env.header.moduleData[i]!
      for c in modData.constNames do
        let axs ← liftCoreM <| Lean.collectAxioms c
        for a in axs do
          unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
            throwError "{c} (in {modName}) depends on the non-standard axiom {a}"
        checked := checked + 1
  for (c, _) in env.constants.map₂.toList do
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} (in MiniRustSpec.Audit) depends on the non-standard axiom {a}"
    checked := checked + 1
  logInfo m!"MiniRustSpec.Audit: exhaustively verified standard axioms for {checked} declarations across all MiniRustSpec.* modules"

#assert_minirustspec_import_isolation

#assert_adt_control_audit_coverage

#assert_all_minirustspec_standard_axioms

end MiniRustSpec.Audit
