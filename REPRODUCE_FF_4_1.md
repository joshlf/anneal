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
erasure. When `&mut` parameters satisfy
`ATMB rp₁ c₁ a₁ ∗ ⋯ ∗ ATMB rpₖ cₖ aₖ ∗ R_frame` (`ATMB` is
`ActiveTypedMutBorrow`, that is `PointsTo ∗ BorrowToken .active`), dereference
reads and writes, function-entry retags, and the `I-10` Tree Borrows
transitions they trigger reduce to pure updates of the lens state
`(a₁, …, aₖ)`. A lifting derivation over that state yields fuel-free
`MirWpConverges` on real memory, and from it `StatefulVerificationResult` and
`TotalVerificationResult`. No proof in the module destructures the 12-field
`Memory` record.

The module is imported by `theory/Anneal.lean` and registered in
`trusted/audit/check_trusted.py`.

## 1. Theorem inventory

### Section 1: lens algebra and the binary bridge

- `IndependentLenses` (with `IndependentLenses.symm`): two lenses whose
  write-backs preserve the validity domain, do not disturb each other's views,
  and commute.
- `prodMutLens` and `prodMutLens_lawful`: the product of two lawful,
  independent lenses is lawful.
- `PairwiseIndependentLenses`: pairwise independence of a homogeneous lens
  list.
- `memoryPtrMutLens_lawful`, `memoryPtrMutLens_independent_of_ne_alloc`, and
  `sepConj_entails_independentLenses`: two separated active typed mutable
  borrows have distinct allocations and tags and lawful, independent
  `memoryPtrMutLens` lenses under the strict ancestor-free `ExclusiveActiveBorrow`.
- `stepTreeBorrowHierarchyAccess?`, `treeMemoryPtrMutLens`,
  `treeMemoryPtrMutLens_writeBack_eq_memoryPtrMutLens_of_exclusive`,
  `ValidTreeMutBorrowLens`, `ValidMutBorrowLens.toTree`,
  `treeMemoryPtrMutLens_lawful`, `treeMemoryPtrMutLens_independent_of_ne_alloc`,
  and `sepConj_entails_independentTreeLenses`: `I-10`-aware mutable borrow lens
  family whose `writeBack` uses `invalidateTreeBorrowsAtProj` (matching MIR
  execution in `PureMirExec.lean`), so PutGet, GetPut, PutPut, and pairwise
  independence hold under the `I-10` parent/child hierarchy invariant
  `TreeExclusiveBorrow` (where active parent tags remain in the borrow table)
  and agree identically with `memoryPtrMutLens` whenever `ExclusiveActiveBorrow`
  holds.

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
  retags preserve the hierarchy.
- Invariants: `SepLensStateInv` (lens entries live in caller slots above the
  callee frame, each with `TreeExclusiveBorrow`, pairwise distinct allocations
  and tags) and `LensFramePreserved` (caller slots and borrow tags outside the
  lens footprint are unchanged).
- Judgments:
  - `LiftLensOperand`: locals, single-field projections, and constants.
  - `LiftDerefRead`: `copy`/`move` of `*p`.
  - `LiftLensOperandAny`: either of the above.
  - `LiftLensRvalue`: `use`, `copyForDeref`, any scalar `binaryOp` over pure or
    deref operands (`LiftLensRvalue.binaryOp_add` is the wrapping-`Add`
    instance), `unaryOp_not` (`UnOp.not` on scalars and booleans),
    `unaryOp_neg` (`UnOp.neg` two's-complement negation), `cast_intToInt`
    (`CastKind.intToInt` unsigned truncation/zero-extension and signed
    truncation/sign-extension), and the empty tuple.
  - `LiftRetag`, `LiftDerefWrite`, `LiftPureAssign`, `LiftStorageLive`,
    `LiftStorageDead`, `LiftNop`, `LiftLensStmt`, `LiftLensStmts`.
  - `LiftLensBlock`: control flow through `return_`, `goto`, `assert` success
    edges, `switchInt` (`TerminatorKind.switchInt` via `MirWpConverges.step_emit`),
    and `drop_local` (`TerminatorKind.drop` on root locals).
- Soundness: `LiftLensStmt.evalStmt_step`, `mirWpConverges_of_liftLensStmts`,
  `mirWpConverges_return_of_lens`, `mirWpConverges_goto_of_lens`,
  `mirWpConverges_assert_of_lens`, `mirWpConverges_switchInt_of_lens`,
  `mirWpConverges_drop_of_lens`, `mirWpConverges_of_liftLensBlock`, and the
  top-level `mirWpConverges_of_sepLenses`, with the bridges
  `verifyStatefulMir_of_sepLenses` and `verifyTotalMir_of_sepLenses`.
- General `List` / indexed composition:
  - `MutBorrowBinding`, `sepConjList`, and `sepConjBindings` (the `k`-ary,
    heterogeneous separating conjunction, right-nested like the binary form).
  - `sepConjBindings_split` and `sepConjBindings_intro`: decomposition into
    pairwise-disjoint bindings plus a disjoint frame, and the converse.
  - `sepLensStateInv_of_sepConjBindings` (`k`-lens entry) and
    `sepConjBindings_preserved` (`k`-lens exit, for any `LocalSepProp`
    frame).
  - `ValidMutBorrowFamily`, `memoryPtrMutLens_lawful_family`,
    `memoryPtrMutLens_independent_family`,
    `sepConjBindings_entails_independentLensFamily` (lawful lenses at every
    index, independent lenses at every pair of distinct indices), and
    `sepConjBindings_entails_pairwiseIndependentLenses` (homogeneous
    `PairwiseIndependentLenses`).
  - `ValidTreeMutBorrowFamily`, `treeMemoryPtrMutLens_lawful_family`,
    `treeMemoryPtrMutLens_independent_family`,
    `sepConjBindings_entails_independentTreeLensFamily`, and
    `sepConjBindings_entails_pairwiseIndependentTreeLenses` (`k`-ary `I-10`
    parent/child lens lawfulness and pairwise independence under
    `TreeExclusiveBorrow`).
  - `SupportedBy` frames: `memoryPtrMutLens_writeBack_agreeOnFootprint_family`,
    `memoryPtrMutLens_writeBack_supportedBy_family`,
    `agreeOnFootprint_of_lensFramePreserved`,
    `supportedBy_of_lensFramePreserved`, and
    `verifyStatefulMir_of_sepLenses_supportedFrame`.
- Unary and binary instances, derived from the general bridges:
  `sepLensStateInv_of_sepConj_one`, `sepLensStateInv_of_sepConj_two`,
  `sepConj_activeTypedMutBorrow_preserved_one`,
  `sepConj_activeTypedMutBorrow_preserved_two`, and
  `pairwise_disjoint_of_sepConj_two_ne`.

### Section 3: concrete witnesses

All parameters are typed `&mut u32` (`RigidTy.ref .mut (.uint .u32)`), and each
witness theorem is proved by `mirWpConverges_of_sepLenses` from a lifting
derivation (`*_lift`).

| Body | MIR shape | Theorems |
| :--- | :--- | :--- |
| `add_assign` | `(*_1) = Add(copy (*_1), copy _2); _0 = const (); return` | `add_assign_mirWpConverges`, `add_assign_verified`, `add_assign_total` |
| `add_assign_checked` | bb0: `StorageLive(_3); _3 = AddWithOverflow(copy (*_1), copy _2); assert(!move (_3.1: bool)) -> bb1`; bb1: `(*_1) = move (_3.0: u32); StorageDead(_3); _0 = const (); return` | `add_assign_checked_mirWpConverges`, `add_assign_checked_verified`, `add_assign_checked_total` |
| `add_assign_retag` | `Retag([fn entry] _1)` followed by the `add_assign` body | `add_assign_retag_mirWpConverges`, `add_assign_retag_verified`, `add_assign_retag_total` |
| `swap_u32` | `StorageLive(_3); _3 = copy (*_1); (*_1) = copy (*_2); (*_2) = copy _3; _0 = const (); StorageDead(_3); return` | `swap_u32_mirWpConverges`, `swap_u32_verified`, `swap_u32_total` |
| `max_assign_u32` | bb0: `StorageLive(_3); _3 = Lt(copy (*_1), copy _2); switchInt(move _3) -> [0: bb2, otherwise: bb1]`; bb1: `(*_1) = copy _2; goto -> bb2`; bb2: `StorageDead(_3); _0 = const (); return` | `max_assign_u32_mirWpConverges`, `max_assign_u32_verified`, `max_assign_u32_total` |

Non-vacuity: `add_assign_demo_pre` and `add_assign_demo_runs` instantiate the
`add_assign` precondition on a concrete memory whose borrow table is an `I-10`
reborrow chain (active parent tag `1`, active child tag `2` with
`parentTag := some 1`). The strict `ExclusiveActiveBorrow` rejects this table
(`addAssignDemoMem_not_strictExclusive`), whereas `ValidTreeMutBorrowLens`
accepts it (`validTreeMutBorrowLens_addAssignDemoMem` and
`treeMemoryPtrMutLens_putGet_addAssignDemoMem`).
With `R_frame := BorrowToken demoParentPtr .active`, the postcondition shows
that the parent stays active after the child's write. `swap_u32_demo_pre` and
`swap_u32_demo_runs` do the same for `swap_u32` on two distinct allocations.

## 2. Scope and known limitations

- Lens entries are whole-allocation borrows at offset `0` with
  `targetProjection = []`; field-granular reborrows such as `&mut s.f` are not
  lifted.
- `LiftLensBlock` covers acyclic paths through `return_`, `goto`, `assert`
  success edges, `switchInt` branches, and `drop` on root locals. Function
  calls, cyclic loops, and unwinding edges are not lifted.
- `LiftLensRvalue` lifts `use`, `copyForDeref`, `binaryOp`, `unaryOp` (`.not`,
  `.neg`), `cast` (`.intToInt`), and empty `aggregate` tuples, but does not
  lift `&`/`&raw` borrow-creation rvalues or non-empty aggregate construction.
- Section 1 provides both `memoryPtrMutLens` (using `SymbolicEval`'s
  ancestor-oblivious `stepTreeBorrowAccess?`, lawful under
  `ExclusiveActiveBorrow`) and `treeMemoryPtrMutLens` (using `PureMirExec`'s
  `I-10`-aware `invalidateTreeBorrowsAtProj`, lawful under
  `TreeExclusiveBorrow`), with `treeMemoryPtrMutLens_writeBack_eq_memoryPtrMutLens_of_exclusive`
  proving that their write-backs coincide whenever `ExclusiveActiveBorrow`
  holds.
- Frames that own a sub-field cell `(allocId, k + 1)` of a tracked pointee are
  preserved only for non-aggregate codecs (`h_not_agg`).
- Anneal's `rustc` capture does not request retag statements;
  `add_assign_retag` models `-Zmir-emit-retag` output to exercise `LiftRetag`.

## 3. Environment

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
cd /usr/local/google/Projects/anneal-workspace/anneal-wt-ff-4-1
```

## 4. Receipts

```bash
./ci/check_todo.sh
python3 trusted/audit/check_trusted.py --fast
(cd examples && anneal-lean-run --mode file --concurrency 1 -- \
  lake env lean ../theory/Anneal/SepLogicLenses.lean)
(cd examples && anneal-lean-run --mode build --concurrency 1 -- \
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
#print axioms mirWpConverges_of_liftLensBlock
#print axioms verifyStatefulMir_of_sepLenses_supportedFrame
#print axioms sepLensStateInv_of_sepConjBindings
#print axioms sepConjBindings_preserved
#print axioms sepConjBindings_entails_independentLensFamily
#print axioms sepConjBindings_entails_pairwiseIndependentLenses
#print axioms sepConjBindings_entails_independentTreeLensFamily
#print axioms sepConjBindings_entails_pairwiseIndependentTreeLenses
#print axioms add_assign_verified
#print axioms add_assign_total
#print axioms add_assign_checked_verified
#print axioms add_assign_retag_mirWpConverges
#print axioms add_assign_retag_verified
#print axioms add_assign_retag_total
#print axioms swap_u32_verified
#print axioms swap_u32_total
#print axioms max_assign_u32_verified
#print axioms max_assign_u32_total
#print axioms add_assign_demo_runs
#print axioms treeMemoryPtrMutLens_putGet_addAssignDemoMem
#print axioms swap_u32_demo_runs
EOF
(cd examples && anneal-lean-run --mode file --concurrency 1 -- \
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

No pass so far ran under `[diversity-reduced]` or a fallback model.
