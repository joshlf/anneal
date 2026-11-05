<!--
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-->

# Reproduction Guide: FF-4.1 (`Anneal.SepLogicLenses`)

`theory/Anneal/SepLogicLenses.lean` proves separation-logic-guarded alias
erasure. When `&mut` parameters satisfy either whole-allocation ownership
`ATMB rp₁ c₁ a₁ ∗ ⋯ ∗ ATMB rpₖ cₖ aₖ ∗ R_frame` (`ATMB` is
`ActiveTypedMutBorrow`, i.e., `PointsTo ∗ BorrowToken .active`) or
sub-allocation field-granular ownership (`ActiveTypedFieldMutBorrow`, i.e.,
`FieldPointsTo ∗ BorrowToken .active` for sibling reborrows `&mut s.f` on a
shared struct allocation), dereference reads and writes, function-entry retags,
and the `I-10` Tree Borrows transitions they trigger reduce to pure updates of
the lens state `(a₁, …, aₖ)`. A lifting derivation over that state yields
fuel-free `MirWpConverges` on real memory (`mirWpConverges_of_sepLenses` and
`mirWpConverges_of_sepSubplaceLenses`), and from it
`StatefulVerificationResult` and `TotalVerificationResult`. No proof in the
module destructures the 12-field `Memory` record.

The module is imported by `theory/Anneal.lean` and registered in
`trusted/audit/check_trusted.py`.

## 1. Theorem inventory

### Section 1: lens algebra and separation-logic bridges

- `IndependentLenses` (with `IndependentLenses.symm`,
  `LawfulMutLens.of_sub_agree`, and `IndependentLenses.of_sub_agree`): two
  lenses whose write-backs preserve the validity domain, do not disturb each
  other's views, and commute, together with generic restriction lemmas that
  transfer lawfulness and independence from base lenses (`rawPtrMutLens`,
  `rawFieldMutLens`) to borrow-checked refinements whose write-backs agree on
  their invariant domains.
- `prodMutLens` and `prodMutLens_lawful`: the product of two lawful,
  independent lenses is lawful.
- `PairwiseIndependentLenses`: pairwise independence of a homogeneous lens
  list.
- `rawPtrMutLens`, `ValidRawPtrLens`, `rawPtrMutLens_lawful`,
  `ValidRawPtrLensPair`, and `rawPtrMutLens_independent_of_ne_alloc`: the
  borrow-agnostic byte-update base lens, from which both `memoryPtrMutLens` and
  `treeMemoryPtrMutLens` inherit their lens laws and pairwise independence via
  `LawfulMutLens.of_sub_agree` and `IndependentLenses.of_sub_agree`.
- `memoryPtrMutLens_lawful`, `memoryPtrMutLens_independent_of_ne_alloc`, and
  `sepConj_entails_independentLenses`: two separated active typed mutable
  borrows have distinct allocations and tags and lawful, independent
  `memoryPtrMutLens` lenses under the strict ancestor-free
  `ExclusiveActiveBorrow`.
- `I-10`-aware whole-allocation lenses: `stepTreeBorrowHierarchyAccess?`
  applies the trusted `I-10` transitions of `MirSemantics`
  (`freezeTreeBorrowsOnReadAtProj` on reads, `invalidateTreeBorrowsAtProj` on
  writes), and `treeMemoryPtrMutLens` uses it for write-backs.
  `treeMemoryPtrMutLens_lawful`, `treeMemoryPtrMutLens_independent_of_ne_alloc`,
  and `sepConj_entails_independentTreeLenses` prove the lens laws and pairwise
  independence under `TreeExclusiveBorrow`, where active parent tags stay in
  the borrow table. `stepTreeBorrowHierarchyAccess_read_eq_some_self_of_tree`
  and `stepTreeBorrowHierarchyAccess_write_eq_some_self_of_tree` show that both
  accesses leave such a table unchanged, and
  `treeMemoryPtrMutLens_writeBack_eq_memoryPtrMutLens_of_exclusive` shows that
  the two lenses agree under `ExclusiveActiveBorrow`.
- Sub-allocation aggregate field lenses (`rawFieldMutLens` and
  `treeFieldMemoryPtrMutLens`) and separation-logic bridge: `readFieldAt?`,
  `writeFieldAt?`, `rawFieldMutLens`, `ValidRawFieldLens`,
  `rawFieldMutLens_lawful`, `ValidRawFieldLensPair`, and
  `rawFieldMutLens_independent_of_ne_field` provide borrow-agnostic field
  lenses on variant-`0` aggregate allocations (`.aggregate 0 elems`).
  `TreeFieldExclusiveBorrow`,
  `freezeTreeBorrowsOnReadAtProj_eq_self_of_treeField`,
  `invalidateTreeBorrowsAtProj_eq_self_of_treeField`,
  `stepTreeBorrowHierarchyAccess_read_eq_some_self_of_treeField`,
  `stepTreeBorrowHierarchyAccess_write_eq_some_self_of_treeField`,
  `treeFieldMemoryPtrMutLens`, `ValidTreeFieldMutBorrowLens`,
  `treeFieldMemoryPtrMutLens_lawful`, `ValidTreeFieldMutBorrowLensPair`, and
  `treeFieldMemoryPtrMutLens_independent_of_ne_field` lift them to
  field-granular `I-10` reborrows (`&mut s.f` / `&mut s.g`, `f ≠ g`).
  `FieldPointsTo` (`localSepProp_fieldPointsTo`), `ActiveTypedFieldMutBorrow`
  (`localSepProp_activeTypedFieldMutBorrow`),
  `sepConj_entails_independentTreeFieldLenses`,
  `treeFieldMemoryPtrMutLens_writeBack_agreeOnFootprint`, and
  `treeFieldMemoryPtrMutLens_writeBack_supportedBy` derive field-disjointness
  (`f₁ ≠ f₂`), `ValidTreeFieldMutBorrowLensPair`, `IndependentLenses`,
  `LawfulMutLens (prodMutLens ...)`, and `SupportedBy` frame preservation
  directly from `sepConj`.

### Section 2: lifting rules and soundness

- Tree Borrows parent/child exclusivity (`I-10`): `TreeExclusiveBorrow`
  requires `rp`'s own entry to be an active whole-allocation borrow and every
  other entry on the allocation to be an active ancestor of `rp.tag`
  (`isBorrowDescendantOrSelf`) or disabled. `ExclusiveActiveBorrow.toTree`
  embeds the strict invariant. `freezeTreeBorrowsOnReadAtProj_eq_self_of_tree`,
  `invalidateTreeBorrowsAtProj_eq_self_of_tree`, and
  `hasProtectedTreeWriteConflict_eq_false_of_tree` show that reads and writes
  through `rp` leave such a table unchanged, and
  `isBorrowDescendantOrSelf_attachBorrowProtector` shows that function-entry
  retags preserve the hierarchy. For field-granular reborrows
  (`TreeFieldExclusiveBorrow`), `TreeFieldExclusiveBorrow.attachProtector`,
  `freezeTreeBorrowsOnReadAtProj_eq_self_of_treeField_prefix`,
  `invalidateTreeBorrowsAtProj_eq_self_of_treeField_prefix`, and
  `hasProtectedTreeWriteConflict_eq_false_of_treeField_prefix` prove the
  analogous hierarchy, protector, and sub-projection properties when sibling
  field borrows (`borrowEntryOverlapsWrite = false`) are simultaneously active
  and protected.
- Invariants: `SepLensStateInv` and `LensFramePreserved` (whole-allocation
  borrows in caller slots above the callee frame), generalized by
  `BorrowSubplace`, `BorrowSubplace.disjointOn`, `SepSubplaceLensStateInv`
  (`SepLensStateInv.toSubplace`), and `SubplaceLensFramePreserved` to arbitrary
  mixtures of root borrows and sibling field-granular reborrows on shared
  aggregate allocations.
- Judgments:
  - `LiftLensOperand`: locals, single-field projections, and constants.
  - `LiftDerefRead`: `copy`/`move` of `*p`.
  - `LiftDerefFieldRead`: `copy`/`move` of `((*p).fieldIdx)` against an
    aggregate pointee in the lens environment (`evalOperand_and_freeze_eq` and
    `evalOperand_eq_rawFieldLens_readView`).
  - `LiftLensOperandAny`: any of `LiftLensOperand`, `LiftDerefRead`, or
    `LiftDerefFieldRead`.
  - `LiftLensOperands`: lists of `LiftLensOperandAny` operands for multi-field
    aggregate construction (`evalOperands_eq` and `length_eq`).
  - `LiftLensRvalue`: `use`, `use_deref_field`, `copyForDeref`, any scalar
    `binaryOp` over pure, deref, or deref-field operands
    (`LiftLensRvalue.binaryOp_add` is the wrapping-`Add` instance),
    `unaryOp_not` (`UnOp.not` on scalars and booleans), `unaryOp_neg`
    (`UnOp.neg` two's-complement negation), `cast_intToInt`
    (`CastKind.intToInt` unsigned truncation/zero-extension and signed
    truncation/sign-extension), the empty tuple (`tuple_nil`), and non-empty
    tuple/ADT aggregates (`aggregate_tuple` and `aggregate_adt`).
  - `LiftRetag`, `LiftDerefWrite` (both root `*p = rv` via `.mk` and projected
    field `((*p).fieldIdx) = rv` via `.field`), `LiftPureAssign`,
    `LiftStorageLive`, `LiftStorageDead`, `LiftNop`, `LiftLensStmt`,
    `LiftLensStmts`.
  - `LiftLensBlock`: control flow through `return_`, `goto`, `assert` success
    edges, `switchInt` (an observable `.event` step), and `drop_local`
    (`TerminatorKind.drop` on root locals).
- Soundness:
  - Whole-allocation: `LiftLensStmt.evalStmt_step`,
    `mirWpConverges_of_liftLensStmts`, `mirWpConverges_return_of_lens`,
    `mirWpConverges_goto_of_lens`, `mirWpConverges_assert_of_lens`,
    `mirWpConverges_switchInt_of_lens`, `mirWpConverges_drop_of_lens`,
    `mirWpConverges_of_liftLensBlock`, `mirWpConverges_of_sepLenses`,
    `verifyStatefulMir_of_sepLenses`, and `verifyTotalMir_of_sepLenses`.
  - Sub-place / sibling field reborrows: `LiftLensStmt.evalStmt_step_subplace`,
    `mirWpConverges_of_liftLensStmts_subplace`,
    `mirWpConverges_of_liftLensBlock_subplace`,
    `mirWpConverges_of_sepSubplaceLenses`,
    `verifyStatefulMir_of_sepSubplaceLenses`, and
    `verifyTotalMir_of_sepSubplaceLenses`, plus the 1- and 2-field bridges
    `WfSingleFieldMutBorrow`, `sepSubplaceLensStateInv_of_sepConj_one_field`,
    `sepConj_activeTypedFieldMutBorrow_preserved_one`,
    `sepSubplaceLensStateInv_of_sepConj_two_fields`, and
    `sepConj_activeTypedFieldMutBorrow_preserved_two`.
- Alias erasure at the semantic level: `LiftDerefWrite.evalStmt_eq` and
  `LiftDerefWrite.evalStmt_field_eq` give the exact memory after a lifted root
  or projected-field deref write. `SepLensStateInv.treeLens_readView`,
  `LiftDerefRead.evalOperand_eq_treeLens_readView`, and
  `LiftDerefRead.evalOperand_eq_treeLens_readView_and_step` equate MIR deref
  reads to `treeMemoryPtrMutLens` views while leaving the `I-10` borrow table
  unchanged under `stepTreeBorrowHierarchyAccess? m rp false = some m`.
  `LiftDerefFieldRead.evalOperand_eq_rawFieldLens_readView` shows a projected
  deref field read returns
  `(rawFieldMutLens rp.allocId fieldIdx codec).readView m`, while
  `LiftDerefWrite.field_evalStmt_eq_rawFieldLens_writeBack` shows a projected
  deref field write `((*p).fieldIdx) = rv` steps to
  `m' = (rawFieldMutLens rp.allocId fieldIdx codec).writeBack a m`, satisfying
  `PutGet` and preserving every sibling field `fieldIdx₂ ≠ fieldIdx`.
  `LiftDerefWrite.evalStmt_eq_treeLens_writeBack`,
  `SepLensStateInv.validTreeMutBorrowLens`,
  `SepLensStateInv.validTreeMutBorrowLensPair`,
  `LiftDerefWrite.evalStmt_treeLens_putGet_and_frame`, and the sub-place
  counterpart `LiftDerefWrite.evalStmt_treeFieldLens_putGet_and_frame` connect
  MIR deref writes directly to Section 1 `PutGet` and `IndependentLenses` for
  both `treeMemoryPtrMutLens` and `treeFieldMemoryPtrMutLens`.
- Every lifted statement, statement list, and whole-CFG execution is lens-state
  passing: `LiftLensStmt.evalStmt_treeLens_views` and
  `LiftLensStmt.evalStmt_treeLens_views_and_frame` show that `evalStmt` steps
  to a memory whose `treeMemoryPtrMutLens` views are the post lens state while
  establishing `LensFramePreserved entries s.memory s'.memory`;
  `LiftRetag.evalStmt_treeLens_views` specializes this to Tree Borrows retags;
  and `LiftLensStmts.mirWpConverges_treeLens_views` and
  `mirWpConverges_of_sepLenses_treeLens_views` compose this state-passing
  invariant across multi-statement lists and whole-CFG `MirWpConverges`
  executions.
- General `List` / indexed composition:
  - `MutBorrowBinding`, `sepConjList`, and `sepConjBindings` (the `k`-ary,
    heterogeneous separating conjunction, right-nested like the binary form).
  - `sepConjBindings_split` and `sepConjBindings_intro`: decomposition into
    pairwise-disjoint bindings plus a disjoint frame, and the converse.
  - `sepConjBindings_pairwise_disjointFootprints` (pairwise
    `DisjointFootprints` of the binding footprints) and
    `sepConjBindings_targetLocal_pairwise_ne` (the borrow entries behind
    distinct bindings target distinct caller locals).
  - `sepLensStateInv_of_sepConjBindings` (`k`-lens entry),
    `sepConjBindings_preserved` (`k`-lens exit for non-aggregate codecs and any
    `LocalSepProp` frame), and `RootAllocSepProp` (`rootAllocSepProp_emp`,
    `rootAllocSepProp_borrowToken`, `rootAllocSepProp_pointsTo`,
    `rootAllocSepProp_activeTypedMutBorrow`, `rootAllocSepProp_sepConj`,
    `sepConjBindings_preserved_of_rootAlloc`, and
    `sepConj_activeTypedMutBorrow_preserved_one_of_rootAlloc` for aggregate
    pointees with root-addressed frames).
  - `ValidMutBorrowFamily`, `memoryPtrMutLens_lawful_family`,
    `memoryPtrMutLens_independent_family`,
    `sepConjBindings_entails_independentLensFamily` (lawful lenses at every
    index, independent lenses at every pair of distinct indices), and
    `sepConjBindings_entails_pairwiseIndependentLenses` (homogeneous
    `PairwiseIndependentLenses`).
  - `ValidTreeMutBorrowFamily`, `ValidMutBorrowFamily.toTree`,
    `treeMemoryPtrMutLens_lawful_family`,
    `treeMemoryPtrMutLens_independent_family`,
    `sepConjBindings_entails_independentTreeLensFamily`, and
    `sepConjBindings_entails_pairwiseIndependentTreeLenses` (`k`-ary `I-10`
    parent/child lens lawfulness and pairwise independence under
    `TreeExclusiveBorrow`).
  - `SupportedBy` frames:
    `treeMemoryPtrMutLens_writeBack_agreeOnFootprint_family`,
    `treeMemoryPtrMutLens_writeBack_supportedBy_family`,
    `memoryPtrMutLens_writeBack_agreeOnFootprint_family`,
    `memoryPtrMutLens_writeBack_supportedBy_family`,
    `agreeOnFootprint_of_lensFramePreserved`,
    `supportedBy_of_lensFramePreserved`,
    `verifyStatefulMir_of_sepLenses_supportedFrame`, `frameTotalClaim`, and
    `verifyTotalMir_of_sepLenses_supportedFrame`.
- Unary and binary instances, derived from the general bridges:
  `sepLensStateInv_of_sepConj_one`, `sepLensStateInv_of_sepConj_two`,
  `sepConj_activeTypedMutBorrow_preserved_one`,
  `sepConj_activeTypedMutBorrow_preserved_two`, and
  `pairwise_disjoint_of_sepConj_two_ne`.

### Section 3: concrete witnesses

Every pointer parameter is a reference (`RigidTy.ref .mut _`), and each witness
theorem is proved through `mirWpConverges_of_sepLenses` or
`mirWpConverges_of_sepSubplaceLenses` from a pure lifting derivation (`*_lift`).

| Body | MIR shape | Theorems |
| :--- | :--- | :--- |
| `add_assign` | `(*_1) = Add(copy (*_1), copy _2); _0 = const (); return` | `add_assign_mirWpConverges`, `add_assign_verified`, `add_assign_total` |
| `add_assign_checked` | bb0: `StorageLive(_3); _3 = AddWithOverflow(copy (*_1), copy _2); assert(!move (_3.1: bool)) -> bb1`; bb1: `(*_1) = move (_3.0: u32); StorageDead(_3); _0 = const (); return` | `add_assign_checked_mirWpConverges`, `add_assign_checked_verified`, `add_assign_checked_total` |
| `add_assign_retag` | `Retag([fn entry] _1)` followed by the `add_assign` body (both root `&mut u32` and field reborrow `&mut s.0`) | `add_assign_retag_mirWpConverges`, `add_assign_retag_verified`, `add_assign_retag_total`, `add_assign_retag_field_mirWpConverges`, `add_assign_retag_field_verified`, `add_assign_retag_field_total` |
| `swap_u32` | `StorageLive(_3); _3 = copy (*_1); (*_1) = copy (*_2); (*_2) = copy _3; _0 = const (); StorageDead(_3); return` (both distinct allocations and sibling field reborrows `&mut s.0`, `&mut s.1`) | `swap_u32_mirWpConverges`, `swap_u32_verified`, `swap_u32_total`, `swap_u32_sibling_fields_mirWpConverges`, `swap_u32_sibling_fields_verified`, `swap_u32_sibling_fields_total` |
| `max_assign_u32` | bb0: `StorageLive(_3); _3 = Lt(copy (*_1), copy _2); switchInt(move _3) -> [0: bb2, otherwise: bb1]`; bb1: `(*_1) = copy _2; goto -> bb2`; bb2: `StorageDead(_3); _0 = const (); return` | `max_assign_u32_mirWpConverges`, `max_assign_u32_verified`, `max_assign_u32_total` |
| `not_assign` | `(*_1) = Not(copy (*_1)); _0 = const (); return` | `not_assign_mirWpConverges`, `not_assign_verified`, `not_assign_total` |
| `widen_assign` (`x: &mut u64`) | `(*_1) = copy _2 as u64 (IntToInt); _0 = const (); return` | `widen_assign_mirWpConverges`, `widen_assign_verified`, `widen_assign_total` |
| `neg_assign_i32` (`x: &mut i32`) | `(*_1) = Neg(copy (*_1)); _0 = const (); return` | `neg_assign_i32_mirWpConverges`, `neg_assign_i32_verified`, `neg_assign_i32_total`, `i32NegBits_spec` |
| `drop_temp_assign` (hand-written) | bb0: `StorageLive(_3); _3 = copy _2; (*_1) = Add(copy (*_1), copy _3); drop(_3) -> bb1`; bb1: `StorageDead(_3); _0 = const (); return` | `drop_temp_assign_mirWpConverges`, `drop_temp_assign_verified`, `drop_temp_assign_total` |
| `swap_pair_u32` (`p: &mut (u32, u32)`) | `_2 = copy ((*_1).0); _3 = copy ((*_1).1); ((*_1).0) = move _3; ((*_1).1) = move _2; _0 = const (); return` | `swap_pair_u32_mirWpConverges`, `swap_pair_u32_verified`, `swap_pair_u32_total` |
| `swap_pair_tuple_rvalue` (`p: &mut (u32, u32)`) | `(*_1) = (copy ((*_1).1), copy ((*_1).0)); _0 = const (); return` | `swap_pair_tuple_rvalue_mirWpConverges`, `swap_pair_tuple_rvalue_verified`, `swap_pair_tuple_rvalue_total` |
| `step_fib_pair_adt` (`p: &mut PairU32`) | `StorageLive(_2); _2 = Add(copy ((*_1).0), copy ((*_1).1)); (*_1) = PairU32 { copy ((*_1).1), move _2 }; StorageDead(_2); _0 = const (); return` | `step_fib_pair_adt_mirWpConverges`, `step_fib_pair_adt_verified`, `step_fib_pair_adt_total` |

Non-vacuity: `add_assign_demo_pre` and `add_assign_demo_runs` instantiate the
`add_assign` precondition on a concrete memory whose borrow table is an `I-10`
reborrow chain (active parent tag `1`, active child tag `2` with
`parentTag := some 1`). The strict `ExclusiveActiveBorrow` rejects this table
(`addAssignDemoMem_not_strictExclusive`), whereas `ValidTreeMutBorrowLens`
accepts it (`validTreeMutBorrowLens_addAssignDemoMem` and
`treeMemoryPtrMutLens_putGet_addAssignDemoMem`). With
`R_frame := BorrowToken demoParentPtr .active`, the postcondition shows that
the parent stays active after the child's write. `swap_u32_demo_pre` and
`swap_u32_demo_runs` do the same for `swap_u32` on two distinct allocations,
and `swap_pair_u32_demo_pre` and `swap_pair_u32_demo_runs` do so for
`swap_pair_u32` on a 2-field tuple pointee under an `I-10` parent/child borrow
chain. Finally, `validTreeFieldMutBorrowLensPair_siblingFieldDemoMem`
instantiates a 3-tag `I-10` sibling field-reborrow hierarchy, and
`swap_u32_sibling_fields_demo_pre` / `swap_u32_sibling_fields_demo_runs` execute
`swap_u32(&mut s.0, &mut s.1)` end to end on `swapSiblingFieldsDemoMem` (a
4-tag hierarchy on caller slot `4` with active parent `&mut s` tag `1`, swapped
children `&mut s.0` tag `2` and `&mut s.1` tag `3`, and an untouched active
third sibling borrow `&mut s.2` tag `4` preserved inside `R_frame`).

## 2. Scope and known limitations

- `SepLensStateInv` tracks whole-allocation borrows (`targetProjection = []`),
  while `SepSubplaceLensStateInv` and `mirWpConverges_of_sepSubplaceLenses`
  generalize MIR execution to single-level field-granular reborrows
  (`targetProjection = [.field fieldIdx fieldTy]`, e.g., `&mut s.0`, `&mut s.1`)
  alongside root borrows. Multi-level nested borrow projections
  (`[.field f _, .field g _]`) and index/subslice borrow projections are not
  modeled in `BorrowSubplace`.
- `LiftLensBlock` covers acyclic paths through `return_`, `goto`, `assert`
  success edges, `switchInt` branches, and `drop` on root locals. Function
  calls, cyclic loops, and unwinding edges are not lifted.
- `LiftLensRvalue` lifts `use`, `use_deref_field`, `copyForDeref`, `binaryOp`,
  `unaryOp` (`.not`, `.neg`), `cast` (`.intToInt`), and tuple/ADT `aggregate`
  constructors (`.tuple` and `.adt defPath variantIdx activeField`, which
  `MirSemantics` evaluates uniformly to `.aggregate variantIdx vals` without
  inspecting `activeField`), while `&`/`&raw` borrow-creation and array-repeat
  rvalues are not lifted.
- Section 1 provides both `memoryPtrMutLens` (from `FunctionalTranslation`,
  whose `stepTreeBorrowAccess?` in `Anneal.UnsafeObligations` ignores the
  `I-10` hierarchy, so it is lawful only under `ExclusiveActiveBorrow`) and
  `treeMemoryPtrMutLens` (lawful under `TreeExclusiveBorrow`); their
  write-backs coincide whenever `ExclusiveActiveBorrow` holds, and both derive
  their lens laws and independence from `rawPtrMutLens` via
  `LawfulMutLens.of_sub_agree` and `IndependentLenses.of_sub_agree`.
- For non-aggregate codecs (`h_not_agg`), `sepConjBindings_preserved` preserves
  any `LocalSepProp` frame. For whole-allocation aggregate pointees
  (`.aggregate 0 elems`, whose `PointsTo` footprint at `(allocId, 0)` aliases
  sub-field cells `(allocId, k + 1)`), `sepConjBindings_preserved_of_rootAlloc`
  and `sepConj_activeTypedMutBorrow_preserved_one_of_rootAlloc` preserve any
  root-addressed frame (`RootAllocSepProp R_frame`). For field-granular borrows
  (`ActiveTypedFieldMutBorrow`), whenever field `0` is among the borrowed
  fields (such as `&mut s.0` or `(&mut s.0, &mut s.1)`), `(allocId, 0)` is
  already excluded from `R_frame`'s footprint by `sepConj`, so
  `sepConj_activeTypedFieldMutBorrow_preserved_one` and
  `sepConj_activeTypedFieldMutBorrow_preserved_two` preserve **any**
  `LocalSepProp R_frame` (including active parent `BorrowToken` and active
  sibling `ActiveTypedFieldMutBorrow` assertions on the same allocation).
- Anneal's `rustc` capture does not request retag statements;
  `add_assign_retag` models `-Zmir-emit-retag` output to exercise `LiftRetag`.
- `drop_temp_assign` is hand-written: rustc elaborates away `drop` of locals
  without drop glue such as `u32`, so it only exercises
  `LiftLensBlock.drop_local`.

## 3. Environment

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
cd /usr/local/google/Projects/anneal-workspace/anneal-wt-ff-4-1
```

## 4. Receipts

```bash
./ci/check_todo.sh
python3 trusted/audit/check_trusted.py --fast
(cd examples && anneal-lean-run --mode file --concurrency 2 -- \
  lake env lean ../theory/Anneal/SepLogicLenses.lean)
(cd examples && anneal-lean-run --mode build --concurrency 2 -- \
  lake build Anneal)
```

Expected: `check_todo.sh` exits `0`; `check_trusted.py --fast` prints `PASS`
with `axioms=['propext', 'Classical.choice', 'Quot.sound']`; the single-file
check prints nothing and exits `0`; `lake build Anneal` ends with
`Build completed successfully`.

## 5. Kernel axiom audit

After `lake build Anneal`, print the axioms of the headline theorems:

```bash
cat > /tmp/ff_4_1_axioms.lean <<'EOF'
import Anneal.SepLogicLenses
open Anneal.SepLogicLenses
#print axioms mirWpConverges_of_sepLenses
#print axioms mirWpConverges_of_sepLenses_treeLens_views
#print axioms mirWpConverges_of_liftLensBlock
#print axioms mirWpConverges_of_sepSubplaceLenses
#print axioms verifyStatefulMir_of_sepSubplaceLenses
#print axioms verifyTotalMir_of_sepSubplaceLenses
#print axioms verifyStatefulMir_of_sepLenses_supportedFrame
#print axioms verifyTotalMir_of_sepLenses_supportedFrame
#print axioms sepLensStateInv_of_sepConjBindings
#print axioms sepConjBindings_preserved
#print axioms sepConjBindings_preserved_of_rootAlloc
#print axioms sepConjBindings_entails_independentLensFamily
#print axioms sepConjBindings_entails_pairwiseIndependentLenses
#print axioms sepConjBindings_entails_independentTreeLensFamily
#print axioms sepConjBindings_entails_pairwiseIndependentTreeLenses
#print axioms treeMemoryPtrMutLens_writeBack_supportedBy_family
#print axioms rawFieldMutLens_lawful
#print axioms rawFieldMutLens_independent_of_ne_field
#print axioms treeFieldMemoryPtrMutLens_lawful
#print axioms treeFieldMemoryPtrMutLens_independent_of_ne_field
#print axioms sepConj_entails_independentTreeFieldLenses
#print axioms treeFieldMemoryPtrMutLens_writeBack_supportedBy
#print axioms sepSubplaceLensStateInv_of_sepConj_one_field
#print axioms sepConj_activeTypedFieldMutBorrow_preserved_one
#print axioms sepSubplaceLensStateInv_of_sepConj_two_fields
#print axioms sepConj_activeTypedFieldMutBorrow_preserved_two
#print axioms add_assign_verified
#print axioms add_assign_total
#print axioms add_assign_checked_verified
#print axioms add_assign_retag_mirWpConverges
#print axioms add_assign_retag_verified
#print axioms add_assign_retag_total
#print axioms add_assign_retag_field_verified
#print axioms add_assign_retag_field_total
#print axioms swap_u32_verified
#print axioms swap_u32_total
#print axioms swap_u32_sibling_fields_verified
#print axioms swap_u32_sibling_fields_total
#print axioms max_assign_u32_verified
#print axioms max_assign_u32_total
#print axioms not_assign_verified
#print axioms not_assign_total
#print axioms widen_assign_verified
#print axioms widen_assign_total
#print axioms neg_assign_i32_verified
#print axioms neg_assign_i32_total
#print axioms drop_temp_assign_verified
#print axioms drop_temp_assign_total
#print axioms swap_pair_u32_verified
#print axioms swap_pair_u32_total
#print axioms swap_pair_tuple_rvalue_verified
#print axioms swap_pair_tuple_rvalue_total
#print axioms step_fib_pair_adt_verified
#print axioms step_fib_pair_adt_total
#print axioms LiftLensStmt.evalStmt_treeLens_views
#print axioms LiftLensStmt.evalStmt_treeLens_views_and_frame
#print axioms LiftLensStmts.mirWpConverges_treeLens_views
#print axioms LiftRetag.evalStmt_treeLens_views
#print axioms i32NegBits_spec
#print axioms LiftDerefWrite.evalStmt_eq_treeLens_writeBack
#print axioms LiftDerefWrite.evalStmt_treeLens_putGet_and_frame
#print axioms LiftDerefWrite.field_evalStmt_eq_rawFieldLens_writeBack
#print axioms LiftDerefWrite.evalStmt_treeFieldLens_putGet_and_frame
#print axioms LiftDerefRead.evalOperand_eq_treeLens_readView
#print axioms LiftDerefRead.evalOperand_eq_treeLens_readView_and_step
#print axioms LiftDerefFieldRead.evalOperand_eq_rawFieldLens_readView
#print axioms sepConjBindings_pairwise_disjointFootprints
#print axioms sepConjBindings_targetLocal_pairwise_ne
#print axioms add_assign_demo_runs
#print axioms treeMemoryPtrMutLens_putGet_addAssignDemoMem
#print axioms swap_u32_demo_runs
#print axioms swap_pair_u32_demo_runs
#print axioms validTreeFieldMutBorrowLensPair_siblingFieldDemoMem
#print axioms swap_u32_sibling_fields_demo_runs
EOF
(cd examples && anneal-lean-run --mode file --concurrency 2 -- \
  lake env lean /tmp/ff_4_1_axioms.lean)
rm -f /tmp/ff_4_1_axioms.lean
```

Expected: every line has the form
`'Anneal.SepLogicLenses.<name>' depends on axioms: [...]` and lists only
`propext`, `Classical.choice`, and `Quot.sound` (some list a subset). No line
mentions `sorryAx` or `Lean.ofReduceBool`.

## 6. Source hygiene

```bash
grep -nwE 'sorry|admit|native_decide|axiom' theory/Anneal/SepLogicLenses.lean
```

Expected: no output.

## 7. Pass log

| Pass | Agent | Model | Notes |
| :--- | :--- | :--- | :--- |
| A0 | `ff41a` | `gemini-launch-candidate-high` | Initial implementation. |
| B1 | `ff41b` | `opus-5.5-max` | `k`-ary composition, `I-10` parent/child exclusivity, multi-block lifting, deref operands in binary ops, checked and retagged witnesses, non-vacuity. |
| A1 | `ff41a` | `gemini-launch-candidate-high` | Closed Section 1 / Section 2 `I-10` exclusivity gap via `treeMemoryPtrMutLens` and `sepConjBindings_entails_independentTreeLensFamily`; added `LiftLensBlock.switchInt` and `drop_local`; added `LiftLensRvalue.unaryOp_not`, `unaryOp_neg`, and `cast_intToInt`; added `add_assign_retag_verified`/`total`, 3-block `max_assign_u32` (`switchInt`), and `treeMemoryPtrMutLens_putGet_addAssignDemoMem`. |
| B2 | `ff41b` | `opus-5.5-max` | MIR deref accesses proved equal to `treeMemoryPtrMutLens` reads and write-backs; `I-10` read freezing in `stepTreeBorrowHierarchyAccess?`; pairwise `DisjointFootprints` and distinct `targetLocal`s; `not_assign` and `widen_assign` witnesses exercising the unary and cast rules; documentation fixes. |
| A2 | `ff41a` | `gemini-launch-candidate-high` | Factored strict and tree `MutLens` proofs through `rawPtrMutLens`, `LawfulMutLens.of_sub_agree`, and `IndependentLenses.of_sub_agree`; added `SepLensStateInv.validTreeMutBorrowLens`/`Pair` and `LiftDerefWrite.evalStmt_treeLens_putGet_and_frame`; added `treeMemoryPtrMutLens_writeBack_agreeOnFootprint_family`/`supportedBy_family` and `verifyTotalMir_of_sepLenses_supportedFrame`; added `not_assign_total`, `widen_assign_total`, `neg_assign_i32` (`unaryOp_neg`), and `drop_temp_assign` (`drop_local`). |
| B3 | `ff41b` | `opus-5.5-max` | Every lifted statement proved to be lens-state passing on `treeMemoryPtrMutLens` views (`LiftLensStmt.evalStmt_treeLens_views`), retags proved to be the identity on lens views (`LiftRetag.evalStmt_treeLens_views`), `i32NegBits_spec`, corrected `drop_temp_assign` MIR shape and marked it hand-written, comment rewraps. |
| A3 | `ff41a` | `gemini-launch-candidate-high` | Added projected deref field reads/writes (`LiftDerefFieldRead`, `LiftDerefWrite.field`) and non-empty aggregate construction (`LiftLensOperands`, `LiftLensRvalue.aggregate_tuple`/`aggregate_adt`); added `RootAllocSepProp` and `sepConjBindings_preserved_of_rootAlloc` for aggregate pointees; added sub-allocation field lenses `rawFieldMutLens` and `treeFieldMemoryPtrMutLens` (`LawfulMutLens` and `IndependentLenses` for sibling field reborrows `&mut s.f` / `&mut s.g`); composed `evalStmt_treeLens_views` with `LensFramePreserved`, `LiftLensStmts`, and `mirWpConverges_of_sepLenses_treeLens_views`; added `swap_pair_u32` and 3-tag sibling field-reborrow non-vacuity witness `validTreeFieldMutBorrowLensPair_siblingFieldDemoMem`. |
| B4 | `ff41b` | `gemini-pro-coordinator` | Closed Section 1 / Section 2 field-granular `SepLogic` and MIR execution gaps via `FieldPointsTo`, `ActiveTypedFieldMutBorrow`, `sepConj_entails_independentTreeFieldLenses`, `treeFieldMemoryPtrMutLens_writeBack_supportedBy`, `SepSubplaceLensStateInv`, `LiftDerefWrite.evalStmt_treeFieldLens_putGet_and_frame`, `mirWpConverges_of_sepSubplaceLenses`, and `LiftDerefWrite.field_evalStmt_eq_rawFieldLens_writeBack`; executed `swap_u32(&mut s.0, &mut s.1)` and `add_assign_retag(&mut s.0, d)` on shared struct allocations (plus 4-tag non-vacuity witness `swap_u32_sibling_fields_demo_runs` preserving active parent `&mut s` and active third sibling `&mut s.2`); added `swap_pair_tuple_rvalue` (`aggregate_tuple`) and `step_fib_pair_adt` (`aggregate_adt`); fixed `aggregate_adt` scope note and 80-col wraps. |

Passes A0–A3 and B1–B3 ran on primary frontier pools
(`gemini-launch-candidate-high` and `opus-5.5-max`); before Pass B4,
`coordinator` switched `ff41b` to the Reserve Frontier Pool
`gemini-pro-coordinator` (`[diversity-reduced]`) after `opus-5.5-max` reached
1% quota.
