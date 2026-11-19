/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/
import Trusted.Correspondence
import Anneal.Mir.Correspondence.MoveDeinit

/-!
# Executable `D1`–`D9` canaries for `Trusted.Correspondence`

Part 7 of the correspondence development: kernel-`decide`d canaries on real
`V2026_06_01` `CapturedMir` bodies, each executed by `M_anneal` and by `M_ref`
on `encodeProg p` (`deinitMoves = true`) through `bothObs` (all 33 prototype
`D1`–`D9` canaries, statement for statement), plus concrete canaries on the live
`Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand ...
(deinitProjectedMoves := true)` for `D1` root moves, `D2` field moves, `D3`
union field moves, `D5` untyped and typed `Deref` moves, and `D9` element,
subslice and slice fat-pointer moves, each with its legacy
(`deinitProjectedMoves := false`) contrast.
-/

namespace Anneal.Mir.Correspondence

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Correspondence

set_option linter.constructorNameAsVariable false

/-! ## Part 7 — Executable `D1`–`D9` canaries on real `V2026_06_01` bodies -/

/-! ### `D1` — direct local move (PR #257 `D6` / `D9`) -/

theorem canary_D1_direct_move_ub :
    bothObs d1MoveThenRead = (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by decide

/-- Non-vacuity witness for `ProgWellFormed` and `RefProgWellFormed` on the
`D1` canary program. -/
theorem refProgWellFormed_d1_nonvacuous :
    ProgWellFormed d1MoveThenRead ∧ RefProgWellFormed (encodeProg d1MoveThenRead) := by
  have hwf : ProgWellFormed d1MoveThenRead := by
    refine ⟨by decide, ?_⟩
    intro b hb
    simp only [d1MoveThenRead, prog1, List.mem_singleton] at hb
    subst hb
    refine ⟨rfl, rfl, ?_⟩
    intro d hd
    simp only [mkBody, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with ⟨ty, rfl | rfl | rfl, rfl⟩ <;> exact ⟨(kU8, lay kU8), rfl⟩
  exact ⟨hwf, refProgWellFormed_encodeProg d1MoveThenRead hwf⟩

def d1ZstMove : V2026Prog := prog1 <| mkBody "d1z" 0 [tUnit, tUnit, tUnit]
  [blk [asg (loc 1) (.use cUnit), asg (loc 2) (.use (.move (loc 1))),
        asg (loc 0) (.use (.copy (loc 1)))] .return_]

theorem canary_D1_zst_unit_move_ok :
    bothObs d1ZstMove = (.returned (some 0) 0, .returned (some 0) 0) := by decide

/-! ### `D2` — partial field move -/

def d2Prog (reread : Bool) : V2026Prog := prog1 <| mkBody "d2" 0 [tU8, tPair, tU8]
  [blk [asg (loc 1) (.aggregate .tuple [cU8 1, cU8 2]),
        asg (loc 2) (.use (.move (fld 1 0 tU8))),
        asg (loc 0) (.use (.copy (fld 1 (if reread then 0 else 1) tU8)))] .return_]

theorem canary_D2_partial_field_move_sibling_ok :
    bothObs (d2Prog false) = (.returned (some 2) 1, .returned (some 2) 1) := by decide

theorem canary_D2_partial_field_move_reread_ub :
    bothObs (d2Prog true) = (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by decide

/-! ### `D3` — move then re-initialize -/

theorem canary_D3_move_then_reinit_ok :
    bothObs d3Prog = (.returned (some 99) 1, .returned (some 99) 1) := by decide

/-! ### `D4` — copy keeps the source; left-to-right binary operands (PR #257 `D7a`–`D7c`) -/

def d4Prog (rv : Rvalue) : V2026Prog := prog1 <| mkBody "d4" 0 [tU8, tU8, tU8]
  [blk [asg (loc 1) (.use (cU8 5)), asg (loc 2) (.use (.copy (loc 1))), asg (loc 0) rv] .return_]

theorem canary_D4_copy_keeps_source :
    bothObs (d4Prog (.use (.copy (loc 1)))) = (.returned (some 5) 1, .returned (some 5) 1) := by
  decide

theorem canary_D4_copy_then_move_ok :
    bothObs (d4Prog (.binaryOp .add (.copy (loc 1)) (.move (loc 1)))) =
      (.returned (some 10) 1, .returned (some 10) 1) := by decide

theorem canary_D4_move_then_copy_ub :
    bothObs (d4Prog (.binaryOp .add (.move (loc 1)) (.copy (loc 1)))) =
      (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by decide

theorem canary_D4_move_then_move_ub :
    bothObs (d4Prog (.binaryOp .add (.move (loc 1)) (.move (loc 1)))) =
      (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by decide

/-! ### `D5` — indirect move through `*ptr` with a sibling `.frozen` borrow -/

theorem canary_D5_indirect_move_delivers_value :
    bothObs (d5Prog (asg (loc 4) (.use (.move (drf 2)))) (.use (.copy (loc 4)))) =
      (.returned (some 5) 1, .returned (some 5) 1) := by decide

theorem canary_D5_indirect_move_reread_ub :
    bothObs (d5Prog (asg (loc 4) (.use (.move (drf 2)))) (.use (.copy (drf 2)))) =
      (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by decide

/-- After `move (*_2)` the sibling shared borrow `_3` is still `.frozen`: reading
`*_3` passes Tree Borrows and only fails on the moved (uninit) bytes. -/
theorem canary_D5_move_preserves_sibling_frozen :
    bothObs (d5Prog (asg (loc 4) (.use (.move (drf 2)))) (.use (.copy (drf 3)))) =
      (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by decide

/-- Contrast: `*_2 = 9` is a foreign write that disables `_3`. -/
theorem canary_D5_assign_disables_sibling_frozen :
    bothObs (d5Prog (asg (drf 2) (.use (cU8 9))) (.use (.copy (drf 3)))) =
      (.ub .treeBorrows, .ub .treeBorrows) := by decide

/-- Contrast: `Deinit(*_2)` is also a Tree Borrows write. -/
theorem canary_D5_deinit_disables_sibling_frozen :
    bothObs (d5Prog (stmt (.deinit (drf 2))) (.use (.copy (drf 3)))) =
      (.ub .treeBorrows, .ub .treeBorrows) := by decide

/-! ### `D6` — self-moves (PR #257 `D8`) -/

def d6Direct : V2026Prog := prog1 <| mkBody "d6a" 0 [tU8, tU8]
  [blk [asg (loc 1) (.use (cU8 5)), asg (loc 1) (.use (.move (loc 1))),
        asg (loc 0) (.use (.copy (loc 1)))] .return_]

def d6Indirect : V2026Prog := prog1 <| mkBody "d6b" 0 [tU8, tU8, tRaw]
  [blk [asg (loc 1) (.use (cU8 5)), asg (loc 2) (.rawPtr .mut (loc 1)),
        asg (drf 2) (.use (.move (drf 2))), asg (loc 0) (.use (.copy (loc 1)))] .return_]

def d6Swap : V2026Prog := prog1 <| mkBody "d6c" 0 [tU8, tPair]
  [blk [asg (loc 1) (.aggregate .tuple [cU8 1, cU8 2]),
        asg (loc 1) (.aggregate .tuple [.move (fld 1 1 tU8), .move (fld 1 0 tU8)]),
        asg (loc 0) (.use (.copy (fld 1 0 tU8)))] .return_]

theorem canary_D6_direct_self_move_ok :
    bothObs d6Direct = (.returned (some 5) 1, .returned (some 5) 1) := by decide

theorem canary_D6_indirect_self_move_ok :
    bothObs d6Indirect = (.returned (some 5) 1, .returned (some 5) 1) := by decide

theorem canary_D6_field_swap_self_aggregate_ok :
    bothObs d6Swap = (.returned (some 2) 1, .returned (some 2) 1) := by decide

/-- Self-referential raw pointer assignment `_1 = &raw mut _1; _0 = copy (*_1)`
where `_1` starts as `.imm`: `placeToMPlace` forces `_1` into `.mem 0` after
`resolveDest` returns `.imm 1`, so `execStmt` upgrades the destination to `.mem 0`
and writes the pointer into `heap[0]` (rather than demoting `_1` back to `.imm`
and leaving `heap[0]` uninitialized). -/
def d6SelfRawPtr : V2026Prog := prog1 <| mkBody "d6raw" 0 [tU8, tRaw]
  [blk [asg (loc 1) (.rawPtr .mut (loc 1)),
        asg (loc 0) (.use (.copy (drf 1)))] .return_]

theorem canary_D6_self_rawPtr_assign_deref_ok :
    bothObs d6SelfRawPtr = (.returned (some 0) 1, .returned (some 0) 1) := by decide

/-- Self-referential shared borrow assignment `_1 = &_1; _0 = copy (*_1)`:
`createRef` creates a `.frozen` borrow tag `1` on `alloc = 0`, and writing the
new reference into `_1` (upgraded to `.mem 0`) performs a Tree Borrows `.Write`
through the root tag that disables tag `1`, so dereferencing `*_1` faults with
`.ub .treeBorrows`. (This program and `d6SelfRawPtr` are ill-typed in rustc MIR,
so both canaries exercise only the byte-level machines; the outcome still
matches Miri, where the following `Retag(_1)` write disables the fresh tag.) -/
def d6SelfSharedRef : V2026Prog := prog1 <| mkBody "d6ref" 0 [tU8, tRef]
  [blk [asg (loc 1) (.ref .shared (loc 1)),
        asg (loc 0) (.use (.copy (drf 1)))] .return_]

theorem canary_D6_self_shared_ref_assign_tb_ub :
    bothObs d6SelfSharedRef = (.ub .treeBorrows, .ub .treeBorrows) := by decide

/-! ### `D7` — call-argument moves and `kani#5172` ordering -/

/-- `_1` is deinitialized in the caller before `callee` runs: the callee's
aliasing read through the raw pointer is UB. -/
theorem canary_D7_call_arg_move_deinit_before_callee :
    bothObs (d7Prog (.move (loc 1))) = (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by
  decide

theorem canary_D7_call_arg_copy_ok :
    bothObs (d7Prog (.copy (loc 1))) = (.returned (some 5) 1, .returned (some 5) 1) := by decide

/-- `kani#5172`: the uninitialized argument faults with UB *before* the
unresolved callee is reported `.unsupported`. -/
theorem canary_D7_uninit_arg_ub_before_unsupported :
    bothObs (d7Unresolved (.move (loc 1))) =
      (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by
  decide

theorem canary_D7_unresolved_callee_unsupported :
    bothObs (d7Unresolved (cU8 1)) = (.unsupported, .unsupported) := by decide

/-- `Call` destination `*_2` is resolved at call entry (before `move _2`
deinitializes `_2`), matching `Miri.Interpreter.Call.evalCallTerminator`. When
`callee` returns `42`, it writes through the pre-resolved `*_2` into `_1`, and
the caller returns `42`. -/
def d7DestCallee : CapturedMir := mkBody "callee" 1 [tU8, tRaw]
  [blk [asg (loc 0) (.use (cU8 42))] .return_]

def d7DestBeforeArgMove : V2026Prog := ⟨[mkBody "caller" 0 [tU8, tU8, tRaw]
  [blk [asg (loc 1) (.use (cU8 5)), asg (loc 2) (.rawPtr .mut (loc 1))]
     (.call (.constant ⟨tFnCallee, .zeroSized⟩) [.move (loc 2)] (drf 2) (some 1) .continue_),
   blk [asg (loc 0) (.use (.copy (loc 1)))] .return_], d7DestCallee], 0⟩

theorem canary_D7_call_dest_resolved_before_arg_move :
    bothObs d7DestBeforeArgMove = (.returned (some 42) 1, .returned (some 42) 1) := by
  decide

/-- An invalid `Call` destination (`*_2` where `_2` is uninitialized) faults
with `.ub .invalidPointer` at call entry *before* evaluating arguments or
reporting `.unsupported` on an unresolved callee. -/
def d7BadDestBeforeUnresolved : V2026Prog := prog1 <| mkBody "caller" 0 [tU8, tU8, tRaw]
  [blk [] (.call (.constant ⟨tFnUnresolved, .zeroSized⟩) [cU8 1] (drf 2) (some 1) .continue_),
   blk [] .return_]

theorem canary_D7_call_bad_dest_ub_before_unsupported :
    bothObs d7BadDestBeforeUnresolved = (.ub .invalidPointer, .ub .invalidPointer) := by
  decide

/-- Same-call `move _1` then `copy _1` faults in both machines. -/
theorem canary_D7_call_move_then_copy_arg_ub :
    bothObs d7MoveThenCopySameCallProg = (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by
  decide

/-! ### `D8` — unwind / cleanup paths -/

def d8Assert (cleanupRead : Nat) : V2026Prog := prog1 <| mkBody "d8" 0 [tU8, tBool, tU8]
  [blk [asg (loc 1) (.use (cBool false)), asg (loc 2) (.use (cU8 7))]
     (.assert (.move (loc 1)) true 1 (.cleanup 2)),
   blk [asg (loc 0) (.use (cU8 0))] .return_,
   blk [asg (loc 0) (.use (.copy (loc cleanupRead)))] .unwindResume true]

theorem canary_D8_assert_cleanup_moved_cond_ub :
    bothObs (d8Assert 1) = (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by decide

theorem canary_D8_assert_cleanup_unmoved_ok :
    bothObs (d8Assert 2) = (.panicked, .panicked) := by decide

def d8Panicky : CapturedMir := mkBody "panicky" 1 [tU8, tU8] [blk [] .unwindResume]

def d8Call (cleanupRead : Nat) : V2026Prog := ⟨[mkBody "caller" 0 [tU8, tU8, tU8]
  [blk [asg (loc 1) (.use (cU8 5)), asg (loc 2) (.use (cU8 6))]
     (.call (.constant ⟨tFnPanicky, .zeroSized⟩) [.move (loc 1)] (loc 0) (some 1) (.cleanup 2)),
   blk [] .return_,
   blk [asg (loc 0) (.use (.copy (loc cleanupRead)))] .unwindResume true], d8Panicky], 0⟩

theorem canary_D8_unwinding_call_moved_arg_ub :
    bothObs (d8Call 1) = (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by decide

theorem canary_D8_unwinding_call_unmoved_ok :
    bothObs (d8Call 2) = (.panicked, .panicked) := by decide

/-! ### `D9` — array element / `ConstantIndex` / `Subslice` moves -/

def d9Prog (s : Statement) (readIdx : Nat) : V2026Prog := prog1 <| mkBody "d9" 0
  [tU8, tArr4, tU8, tArr2]
  [blk [asg (loc 1) (.aggregate (.array tU8) [cU8 10, cU8 11, cU8 12, cU8 13]), s,
        asg (loc 0) (.use (.copy ⟨1, [.constantIndex readIdx 4 false]⟩))] .return_]

def d9MoveElem : Statement := asg (loc 2) (.use (.move ⟨1, [.constantIndex 1 4 false]⟩))
def d9MoveSub : Statement := asg (loc 3) (.use (.move ⟨1, [.subslice 1 3 false]⟩))

theorem canary_D9_elem_move_neighbors_ok :
    bothObs (d9Prog d9MoveElem 0) = (.returned (some 10) 1, .returned (some 10) 1) ∧
    bothObs (d9Prog d9MoveElem 3) = (.returned (some 13) 1, .returned (some 13) 1) := by
  decide

theorem canary_D9_elem_move_reread_ub :
    bothObs (d9Prog d9MoveElem 1) = (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by
  decide

theorem canary_D9_subslice_move_window :
    bothObs (d9Prog d9MoveSub 0) = (.returned (some 10) 1, .returned (some 10) 1) ∧
    bothObs (d9Prog d9MoveSub 3) = (.returned (some 13) 1, .returned (some 13) 1) ∧
    bothObs (d9Prog d9MoveSub 1) = (.ub .invalidUninitBytes, .ub .invalidUninitBytes) ∧
    bothObs (d9Prog d9MoveSub 2) = (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by
  decide

/-- `ConstantIndex` minimum-length check (`minLen > n` faults with `.ub .outOfBounds`),
valid `fromEnd = true` element move (`_1[-1]` = `_1[3] = 13`), and malformed
`fromEnd = true` `off = 0` / `off > minLen` failing closed with `.unsupported`
instead of `Nat`-underflowing to `_1[0]`. -/
def d9ConstIndexBoundsProg (proj : ProjectionElem) : V2026Prog := prog1 <| mkBody "d9ci" 0
  [tU8, tArr4]
  [blk [asg (loc 1) (.aggregate (.array tU8) [cU8 10, cU8 11, cU8 12, cU8 13]),
        asg (loc 0) (.use (.move ⟨1, [proj]⟩))] .return_]

theorem canary_D9_constIndex_minLen_and_fromEnd_bounds :
    bothObs (d9ConstIndexBoundsProg (.constantIndex 0 5 false)) =
      (.ub .outOfBounds, .ub .outOfBounds) ∧
    bothObs (d9ConstIndexBoundsProg (.constantIndex 1 4 true)) =
      (.returned (some 13) 1, .returned (some 13) 1) ∧
    bothObs (d9ConstIndexBoundsProg (.constantIndex 0 4 true)) =
      (.unsupported, .unsupported) ∧
    bothObs (d9ConstIndexBoundsProg (.constantIndex 5 4 true)) =
      (.unsupported, .unsupported) := by
  decide

/-- `Subslice` with `fromEnd = true` and `fromIdx + toIdx > n` (`_1[0..-5]` on
`[u8; 4]`) faults with `.ub .outOfBounds` rather than `Nat`-underflowing `4 - 5 = 0`
into an empty subslice. -/
def d9SubsliceFromEndOobProg : V2026Prog := prog1 <| mkBody "d9sub" 0
  [tU8, tArr4, { kind := .array (.uint .u8) 0, layoutIdx := 0 }]
  [blk [asg (loc 1) (.aggregate (.array tU8) [cU8 10, cU8 11, cU8 12, cU8 13]),
        asg (loc 2) (.use (.move ⟨1, [.subslice 0 5 true]⟩)),
        asg (loc 0) (.use (cU8 1))] .return_]

theorem canary_D9_subslice_fromEnd_underflow_ub :
    bothObs d9SubsliceFromEndOobProg = (.ub .outOfBounds, .ub .outOfBounds) := by
  decide

/-- Out-of-bounds `.field` on `FieldsShape.array`, sub-place escape via an
oversized `.field` (`fo + fty.size > mp.size` inside a larger allocation), and
excess `Rvalue.aggregate` operands all fail closed with `.unsupported` in both
`M_anneal` and `M_ref` (`Place.projectRuntimePlace` local bounds parity). -/
def d2SubplaceFieldOobProg (tailProj : ProjectionElem) : V2026Prog := prog1 <| mkBody "d2oob" 0
  [tU8, tArr4, tArr4]
  [blk [asg (loc 1) (.aggregate (.array tU8) [cU8 10, cU8 11, cU8 12, cU8 13]),
        asg (loc 0) (.use (.move ⟨1, [.subslice 0 2 false, tailProj]⟩))] .return_]

def d2OversizedSubplaceFieldProg : V2026Prog := prog1 <| mkBody "d2over" 0
  [tU8, tArr4, tArr4]
  [blk [asg (loc 1) (.aggregate (.array tU8) [cU8 10, cU8 11, cU8 12, cU8 13]),
        asg (loc 2) (.use (.move ⟨1, [.subslice 0 2 false, .field 0 tArr4]⟩)),
        asg (loc 0) (.use (cU8 1))] .return_]

def d2ExcessAggregateOperandsProg : V2026Prog := prog1 <| mkBody "d2agg" 0
  [tU8, tPair]
  [blk [asg (loc 1) (.aggregate .tuple [cU8 1, cU8 2, cU8 3]),
        asg (loc 0) (.use (.copy (fld 1 0 tU8)))] .return_]

theorem canary_D2_field_bounds_and_subplace_containment :
    bothObs (d2SubplaceFieldOobProg (.field 1 tU8)) =
      (.returned (some 11) 1, .returned (some 11) 1) ∧
    bothObs (d2SubplaceFieldOobProg (.field 2 tU8)) = (.unsupported, .unsupported) ∧
    bothObs d2OversizedSubplaceFieldProg = (.unsupported, .unsupported) ∧
    bothObs d2ExcessAggregateOperandsProg = (.unsupported, .unsupported) := by
  decide

/-- Real `CapturedMir` body over `union U { a: u8, b: u16 }` (`claimUnionLayouts`)
exercising `D3` partial union move, overlapping-field UB, re-initialization, and
`FieldsShape.union` field-count bounds through `bothObs` (`M_anneal` & `M_ref`). -/
def d3UnionProg (ss : List Statement) (retIsU16 : Bool := false) : V2026Prog :=
  let uTy : Ty := { kind := .adt "U" [], layoutIdx := 2 }
  let retTy : Ty := if retIsU16 then claimU16Ty else claimU8Ty
  ⟨[{ defPath := "d3union", phase := .runtimePostCleanup, role := .subject, argCount := 0
      localDecls := [⟨.mut, retTy, none⟩, ⟨.mut, uTy, none⟩, ⟨.mut, claimU8Ty, none⟩]
      basicBlocks := [blk ss .return_]
      fnAbi := ⟨[], ⟨claimU8Layout, .ignore⟩, .rust, true⟩
      layouts := claimUnionLayouts, allocations := [] }], 0⟩

theorem canary_D3_union_field_move_and_reinit_bothObs :
    let cU16_770 : Operand := .constant ⟨claimU16Ty, .scalar (.int ⟨770, 2⟩)⟩
    let cU8_9 : Operand := .constant ⟨claimU8Ty, .scalar (.int ⟨9, 1⟩)⟩
    bothObs (d3UnionProg
      [asg (fld 1 1 claimU16Ty) (.use cU16_770),
       asg (loc 0) (.use (.move (fld 1 0 claimU8Ty)))]) =
      (.returned (some 2) 1, .returned (some 2) 1) ∧
    bothObs (d3UnionProg
      [asg (fld 1 1 claimU16Ty) (.use cU16_770),
       asg (loc 2) (.use (.move (fld 1 0 claimU8Ty))),
       asg (loc 0) (.use (.copy (fld 1 0 claimU8Ty)))]) =
      (.ub .invalidUninitBytes, .ub .invalidUninitBytes) ∧
    bothObs (d3UnionProg
      [asg (fld 1 1 claimU16Ty) (.use cU16_770),
       asg (loc 2) (.use (.move (fld 1 0 claimU8Ty))),
       asg (loc 0) (.use (.copy (fld 1 1 claimU16Ty)))] true) =
      (.ub .invalidUninitBytes, .ub .invalidUninitBytes) ∧
    bothObs (d3UnionProg
      [asg (fld 1 1 claimU16Ty) (.use cU16_770),
       asg (loc 2) (.use (.move (fld 1 0 claimU8Ty))),
       asg (fld 1 0 claimU8Ty) (.use cU8_9),
       asg (loc 0) (.use (.copy (fld 1 1 claimU16Ty)))] true) =
      (.returned (some 777) 2, .returned (some 777) 2) ∧
    bothObs (d3UnionProg
      [asg (fld 1 1 claimU16Ty) (.use cU16_770),
       asg (loc 0) (.use (.copy (fld 1 2 claimU8Ty)))]) =
      (.unsupported, .unsupported) := by
  decide

/-! ## Live `Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand` canaries

Concrete runs of the Episode 1 consumer-side move deinitialization
(`deinitProjectedMoves := true`) on the live Trusted `evalOperand`, each with
its legacy (`deinitProjectedMoves := false`) contrast. -/

/-- `u8` field type (layout index irrelevant without local declarations). -/
def trustedU8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }

/-- Place helper. -/
def tpl (l : Local) (proj : List ProjectionElem) : Place := { local_ := l, projection := proj }

/-! ### `D1`: root moves -/

/-- `_1 : u8 = 5`. -/
def trustedD1Locals : List LocalSlot := [.uninit, .init (u8Value 5)]

theorem canary_trusted_D1_root_move :
    evalOperand trustedD1Locals (.move (tpl 1 [])) (deinitProjectedMoves := true) =
      .ok (u8Value 5) [.uninit, .uninit] := rfl

theorem canary_trusted_D1_root_reread_ub :
    evalOperand [.uninit, .uninit] (.copy (tpl 1 [])) (deinitProjectedMoves := true) = .ub := rfl

/-! ### `D2`: field moves -/

/-- `_1 : (u8, u8) = (2, 3)`. -/
def trustedD2Locals : List LocalSlot := [.uninit, .init (.aggregate 0 [u8Value 2, u8Value 3])]

/-- `_1` after `move _1.0`. -/
def trustedD2AfterMove : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [movedUninitValue, u8Value 3])]

/-- **`D2` field move** on the live `evalOperand`: moving `_1.0` returns `2` and
deinitializes `_1.0`; re-reading or re-moving `_1.0`, or reading the whole `_1`,
faults with `.ub`, while the sibling `_1.1 = 3` stays readable. -/
theorem canary_trusted_D2_field_move :
    evalOperand trustedD2Locals (.move (tpl 1 [.field 0 trustedU8Ty]))
        (deinitProjectedMoves := true) = .ok (u8Value 2) trustedD2AfterMove ∧
    evalOperand trustedD2AfterMove (.copy (tpl 1 [.field 0 trustedU8Ty]))
        (deinitProjectedMoves := true) = .ub ∧
    evalOperand trustedD2AfterMove (.move (tpl 1 [.field 0 trustedU8Ty]))
        (deinitProjectedMoves := true) = .ub ∧
    evalOperand trustedD2AfterMove (.copy (tpl 1 [])) (deinitProjectedMoves := true) = .ub ∧
    evalOperand trustedD2AfterMove (.copy (tpl 1 [.field 1 trustedU8Ty]))
        (deinitProjectedMoves := true) = .ok (u8Value 3) trustedD2AfterMove :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Contrast: the legacy semantics keeps a moved field readable. -/
theorem canary_trusted_D2_legacy_keeps_field :
    evalOperand trustedD2Locals (.move (tpl 1 [.field 0 trustedU8Ty])) =
      .ok (u8Value 2) trustedD2Locals ∧
    evalOperand trustedD2Locals (.copy (tpl 1 [.field 0 trustedU8Ty])) =
      .ok (u8Value 2) trustedD2Locals :=
  ⟨rfl, rfl⟩

/-! ### `D5`: Tree-Borrows-silent `move (*_2)` -/

/-- **`D5` `Deref` move** on the live `evalOperand`: `move (*_2)` delivers `5`
and deinitializes `_1`; the sibling `_3` keeps its `.frozen` tag (the borrow
table is unchanged), and reading `*_3` now faults on the uninitialized target,
whereas before the move the same read succeeds. -/
theorem canary_trusted_D5_deref_move :
    evalOperand d5TrustedLocals (.move (tpl 2 [.deref])) d5TrustedBorrows
        (deinitProjectedMoves := true) = .ok (u8Value 5) d5TrustedAfterMove ∧
    lookupBorrow d5TrustedBorrows 3 =
      .some { tag := 3, targetLocal := 1, targetProjection := [], perm := .frozen } ∧
    evalOperand d5TrustedLocals (.copy (tpl 3 [.deref])) d5TrustedBorrows
        (deinitProjectedMoves := true) = .ok (u8Value 5) d5TrustedLocals ∧
    evalOperand d5TrustedAfterMove (.copy (tpl 3 [.deref])) d5TrustedBorrows
        (deinitProjectedMoves := true) = .ub ∧
    evalOperand d5TrustedAfterMove (.copy (tpl 2 [.deref])) d5TrustedBorrows
        (deinitProjectedMoves := true) = .ub :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Contrast: a disabled tag faults even before the move (the `.ub` above is the
uninitialized target, not a Tree Borrows failure). -/
theorem canary_trusted_D5_disabled_contrast :
    evalOperand d5TrustedLocals (.copy (tpl 3 [.deref]))
      [{ tag := 2, targetLocal := 1, targetProjection := [], perm := .active },
       { tag := 3, targetLocal := 1, targetProjection := [], perm := .disabled }]
      (deinitProjectedMoves := true) = .ub := rfl

/-- Contrast: the legacy semantics does not deinitialize the `Deref` target. -/
theorem canary_trusted_D5_legacy_keeps_target :
    evalOperand d5TrustedLocals (.move (tpl 2 [.deref])) d5TrustedBorrows =
      .ok (u8Value 5) d5TrustedLocals := rfl

/-! ### `D9`: element and subslice moves -/

/-- `_1 : [u8; 4] = [10, 11, 12, 13]`, `_2 : usize = 1`. -/
def trustedD9Locals : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [u8Value 10, u8Value 11, u8Value 12, u8Value 13]),
    .init (.scalar { bits := 1, sizeBytes := 8 })]

def trustedD9AfterElem : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [u8Value 10, movedUninitValue, u8Value 12, u8Value 13]),
    .init (.scalar { bits := 1, sizeBytes := 8 })]

/-- **`D9` element move** on the live `evalOperand` (`ConstantIndex` and
`Index`): the moved element faults afterwards while its neighbours stay
readable. -/
theorem canary_trusted_D9_elem_move :
    evalOperand trustedD9Locals (.move (tpl 1 [.constantIndex 1 4 false]))
        (deinitProjectedMoves := true) = .ok (u8Value 11) trustedD9AfterElem ∧
    evalOperand trustedD9Locals (.move (tpl 1 [.index 2])) (deinitProjectedMoves := true) =
      .ok (u8Value 11) trustedD9AfterElem ∧
    evalOperand trustedD9AfterElem (.copy (tpl 1 [.constantIndex 0 4 false]))
        (deinitProjectedMoves := true) = .ok (u8Value 10) trustedD9AfterElem ∧
    evalOperand trustedD9AfterElem (.copy (tpl 1 [.constantIndex 3 4 false]))
        (deinitProjectedMoves := true) = .ok (u8Value 13) trustedD9AfterElem ∧
    evalOperand trustedD9AfterElem (.copy (tpl 1 [.constantIndex 1 4 false]))
        (deinitProjectedMoves := true) = .ub ∧
    evalOperand trustedD9AfterElem (.copy (tpl 1 [])) (deinitProjectedMoves := true) = .ub :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def trustedD9AfterSubslice : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [u8Value 10, movedUninitValue, movedUninitValue, u8Value 13]),
    .init (.scalar { bits := 1, sizeBytes := 8 })]

/-- **`D9` subslice move** on the live `evalOperand` (`from_end = false` and
`from_end = true`): exactly the moved window faults afterwards. -/
theorem canary_trusted_D9_subslice_move :
    evalOperand trustedD9Locals (.move (tpl 1 [.subslice 1 3 false]))
        (deinitProjectedMoves := true) =
      .ok (.aggregate 0 [u8Value 11, u8Value 12]) trustedD9AfterSubslice ∧
    evalOperand trustedD9Locals (.move (tpl 1 [.subslice 1 1 true]))
        (deinitProjectedMoves := true) =
      .ok (.aggregate 0 [u8Value 11, u8Value 12]) trustedD9AfterSubslice ∧
    evalOperand trustedD9AfterSubslice (.copy (tpl 1 [.constantIndex 0 4 false]))
        (deinitProjectedMoves := true) = .ok (u8Value 10) trustedD9AfterSubslice ∧
    evalOperand trustedD9AfterSubslice (.copy (tpl 1 [.constantIndex 3 4 false]))
        (deinitProjectedMoves := true) = .ok (u8Value 13) trustedD9AfterSubslice ∧
    evalOperand trustedD9AfterSubslice (.copy (tpl 1 [.constantIndex 1 4 false]))
        (deinitProjectedMoves := true) = .ub ∧
    evalOperand trustedD9AfterSubslice (.copy (tpl 1 [.constantIndex 2 4 false]))
        (deinitProjectedMoves := true) = .ub :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Contrast: the legacy semantics keeps moved elements readable. -/
theorem canary_trusted_D9_legacy_keeps_elems :
    evalOperand trustedD9Locals (.move (tpl 1 [.subslice 1 3 false])) =
      .ok (.aggregate 0 [u8Value 11, u8Value 12]) trustedD9Locals := rfl

/-- **`D3` union field move and re-initialization** on the live `evalOperand`
(`deinitUnionSubPlace`) with its legacy (`deinitProjectedMoves := false`)
contrast. -/
theorem canary_trusted_D3_union_field_move_and_reinit :
    evalOperand [.uninit, .init (.aggregate 0 [.unit, .scalar ⟨770, 2⟩])]
        (.move (tpl 1 [.field 0 claimU8Ty])) [] [] claimUnionLayouts [] claimUnionDecls [] true =
      .ok (u8Value 2) d3TrustedUnionAfterMove ∧
    evalOperand d3TrustedUnionAfterMove (.copy (tpl 1 [.field 0 claimU8Ty])) [] []
      claimUnionLayouts [] claimUnionDecls [] true = .ub ∧
    evalOperand d3TrustedUnionAfterMove (.copy (tpl 1 [.field 1 claimU16Ty])) [] []
      claimUnionLayouts [] claimUnionDecls [] true = .ub ∧
    evalOperand d3TrustedUnionAfterMove (.copy (tpl 1 [])) [] [] claimUnionLayouts []
      claimUnionDecls [] true =
      .ok (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨0, 0⟩, .scalar ⟨3, 1⟩]])
        d3TrustedUnionAfterMove ∧
    writePlaceValue d3TrustedUnionAfterMove [] (tpl 1 [.field 0 claimU8Ty]) (u8Value 9)
      claimUnionDecls claimUnionLayouts = .ok d3TrustedUnionAfterReinit ∧
    evalOperand d3TrustedUnionAfterReinit (.copy (tpl 1 [.field 1 claimU16Ty])) [] []
      claimUnionLayouts [] claimUnionDecls [] true = .ok (.scalar ⟨777, 2⟩) d3TrustedUnionAfterReinit ∧
    evalOperand [.uninit, .init (.aggregate 0 [.unit, .scalar ⟨770, 2⟩])]
        (.move (tpl 1 [.field 0 claimU8Ty])) [] [] claimUnionLayouts [] claimUnionDecls [] false =
      .ok (u8Value 2) [.uninit, .init (.aggregate 0 [.unit, .scalar ⟨770, 2⟩])] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`D5` typed thin-pointer `Deref` + field move** (`deinitTypedThinPtrDeref`
at a non-zero array-element byte offset) with its legacy contrast. -/
theorem canary_trusted_D5_typed_deref_field_of_array_elem_move :
    let initLocals : List LocalSlot :=
      [.uninit,
        .init (.aggregate 0 [.aggregate 0 [u8Value 1, u8Value 2],
          .aggregate 0 [u8Value 3, u8Value 4]]),
        .init (.ptr { allocId := 2, offsetBytes := 2 } 8),
        .init (.ptr { allocId := 3, offsetBytes := 2 } 8)]
    evalOperand initLocals (.move (tpl 2 [.deref, .field 0 claimU8Ty])) claimDerefBorrows []
      claimPairArrLayouts [] claimPairArrDecls [] true =
      .ok (u8Value 3) d5TrustedTypedDerefAfterMove ∧
    evalOperand d5TrustedTypedDerefAfterMove (.copy (tpl 2 [.deref, .field 1 claimU8Ty]))
      claimDerefBorrows [] claimPairArrLayouts [] claimPairArrDecls [] true =
      .ok (u8Value 4) d5TrustedTypedDerefAfterMove ∧
    evalOperand d5TrustedTypedDerefAfterMove (.copy (tpl 3 [.deref, .field 1 claimU8Ty]))
      claimDerefBorrows [] claimPairArrLayouts [] claimPairArrDecls [] true =
      .ok (u8Value 4) d5TrustedTypedDerefAfterMove ∧
    evalOperand d5TrustedTypedDerefAfterMove (.copy (tpl 2 [.deref, .field 0 claimU8Ty]))
      claimDerefBorrows [] claimPairArrLayouts [] claimPairArrDecls [] true = .ub ∧
    evalOperand initLocals (.move (tpl 2 [.deref, .field 0 claimU8Ty])) claimDerefBorrows []
      claimPairArrLayouts [] claimPairArrDecls [] false = .ok (u8Value 3) initLocals :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **`D9` slice fat-pointer `Deref` element and subslice moves**
(`deinitSliceFatPtrDeref`) with legacy contrast. -/
theorem canary_trusted_D9_slice_fat_ptr_elem_and_subslice_move :
    let initSliceLocals : List LocalSlot :=
      [.uninit,
        .init (.aggregate 0 [u8Value 10, u8Value 11, u8Value 12, u8Value 13]),
        .init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0 } 8,
          .scalar { bits := 4, sizeBytes := 8 }])]
    evalOperand initSliceLocals (.move (tpl 2 [.deref, .constantIndex 1 4 false]))
      claimDerefBorrows [] emptyLayoutTable [] [] [] true =
      .ok (u8Value 11) d9TrustedSliceAfterElem ∧
    evalOperand d9TrustedSliceAfterElem (.copy (tpl 2 [.deref, .constantIndex 1 4 false]))
      claimDerefBorrows [] emptyLayoutTable [] [] [] true = .ub ∧
    evalOperand d9TrustedSliceAfterElem (.copy (tpl 2 [.deref, .constantIndex 0 4 false]))
      claimDerefBorrows [] emptyLayoutTable [] [] [] true =
      .ok (u8Value 10) d9TrustedSliceAfterElem ∧
    evalOperand initSliceLocals (.move (tpl 2 [.deref, .subslice 1 3 false]))
      claimDerefBorrows [] emptyLayoutTable [] [] [] true =
      .ok (.aggregate 0 [u8Value 11, u8Value 12]) d9TrustedSliceAfterSub ∧
    evalOperand d9TrustedSliceAfterSub (.copy (tpl 1 [.constantIndex 1 4 false]))
      claimDerefBorrows [] emptyLayoutTable [] [] [] true = .ub ∧
    evalOperand initSliceLocals (.move (tpl 2 [.deref, .subslice 1 3 false]))
      claimDerefBorrows [] emptyLayoutTable [] [] [] false =
      .ok (.aggregate 0 [u8Value 11, u8Value 12]) initSliceLocals :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `evalOperands`: `move _1` followed by `copy _1` in one operand list faults. -/
theorem canary_trusted_evalOperands_move_then_copy_ub :
    evalOperands trustedD1Locals [.move (tpl 1 []), .copy (tpl 1 [])]
      (deinitProjectedMoves := true) = .ub := rfl

/-- **`D4` & `D6` multi-operand field evaluation on the live `evalOperands`**
(`deinitProjectedMoves := true` vs `false`):
1. `[copy _1.0, move _1.0]` succeeds with `[2, 2]` and deinitializes `_1.0`;
2. `[move _1.0, copy _1.0]`, `[move _1.0, move _1.0]`, and `[move _1.0, copy _1]`
   fault with `.ub` (whereas legacy `false` mode returns `[2, 2]` on
   `[move _1.0, copy _1.0]`);
3. `[move _1.0, copy _1.1]` succeeds with `[2, 3]`; and
4. `[move _1.1, move _1.0]` followed by `writePlaceValue` completes the `D6`
   self-aggregate field swap `_1 = (move _1.1, move _1.0)`. -/
theorem canary_trusted_evalOperands_D4_D6_field_order_and_swap :
    evalOperands trustedD2Locals
      [.copy (tpl 1 [.field 0 trustedU8Ty]), .move (tpl 1 [.field 0 trustedU8Ty])]
      (deinitProjectedMoves := true) = .ok [u8Value 2, u8Value 2] trustedD2AfterMove ∧
    evalOperands trustedD2Locals
      [.move (tpl 1 [.field 0 trustedU8Ty]), .copy (tpl 1 [.field 0 trustedU8Ty])]
      (deinitProjectedMoves := true) = .ub ∧
    evalOperands trustedD2Locals
      [.move (tpl 1 [.field 0 trustedU8Ty]), .move (tpl 1 [.field 0 trustedU8Ty])]
      (deinitProjectedMoves := true) = .ub ∧
    evalOperands trustedD2Locals
      [.move (tpl 1 [.field 0 trustedU8Ty]), .copy (tpl 1 [])]
      (deinitProjectedMoves := true) = .ub ∧
    evalOperands trustedD2Locals
      [.move (tpl 1 [.field 0 trustedU8Ty]), .copy (tpl 1 [.field 1 trustedU8Ty])]
      (deinitProjectedMoves := true) = .ok [u8Value 2, u8Value 3] trustedD2AfterMove ∧
    evalOperands trustedD2Locals
      [.move (tpl 1 [.field 0 trustedU8Ty]), .copy (tpl 1 [.field 0 trustedU8Ty])] =
        .ok [u8Value 2, u8Value 2] trustedD2Locals ∧
    evalOperands trustedD2Locals
      [.move (tpl 1 [.field 1 trustedU8Ty]), .move (tpl 1 [.field 0 trustedU8Ty])]
      (deinitProjectedMoves := true) =
        .ok [u8Value 3, u8Value 2]
          [.uninit, .init (.aggregate 0 [movedUninitValue, movedUninitValue])] ∧
    writePlaceValue
      [.uninit, .init (.aggregate 0 [movedUninitValue, movedUninitValue])]
      [] (tpl 1 []) (.aggregate 0 [u8Value 3, u8Value 2]) =
        .ok [.uninit, .init (.aggregate 0 [u8Value 3, u8Value 2])] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`D7` call-argument / multi-operand `Deref` evaluation on the live
`evalOperands` with a sibling `.frozen` borrow** (`_2 = &raw mut _1`,
`_3 = &_1` `.frozen`):
1. `[copy (*_2), move (*_2)]` and `[copy (*_3), move (*_2)]` return `[5, 5]` and
   deinitialize `_1`;
2. `[move (*_2), copy (*_2)]` and `[move (*_2), copy (*_3)]` fault with `.ub`
   while preserving the sibling `.frozen` borrow `_3` (whereas legacy `false`
   mode returns `[5, 5]`); and
3. on typed `*mut (u8, u8)` (`_2` at byte offset `2`) with sibling `&(u8, u8)`
   (`_3` `.frozen`), `[copy (*_2).0, move (*_2).0]` returns `[3, 3]`,
   `[move (*_2).0, copy (*_2).0]` and `[move (*_2).0, copy (*_3).0]` fault with
   `.ub`, and `[move (*_2).0, copy (*_3).1]` returns `[3, 4]`. -/
theorem canary_trusted_evalOperands_D7_deref_order_with_frozen_sibling :
    let initTyped : List LocalSlot :=
      [.uninit,
        .init (.aggregate 0 [.aggregate 0 [u8Value 1, u8Value 2],
          .aggregate 0 [u8Value 3, u8Value 4]]),
        .init (.ptr { allocId := 2, offsetBytes := 2 } 8),
        .init (.ptr { allocId := 3, offsetBytes := 2 } 8)]
    evalOperands d5TrustedLocals [.copy (tpl 2 [.deref]), .move (tpl 2 [.deref])]
      d5TrustedBorrows (deinitProjectedMoves := true) =
        .ok [u8Value 5, u8Value 5] d5TrustedAfterMove ∧
    evalOperands d5TrustedLocals [.copy (tpl 3 [.deref]), .move (tpl 2 [.deref])]
      d5TrustedBorrows (deinitProjectedMoves := true) =
        .ok [u8Value 5, u8Value 5] d5TrustedAfterMove ∧
    evalOperands d5TrustedLocals [.move (tpl 2 [.deref]), .copy (tpl 2 [.deref])]
      d5TrustedBorrows (deinitProjectedMoves := true) = .ub ∧
    evalOperands d5TrustedLocals [.move (tpl 2 [.deref]), .copy (tpl 3 [.deref])]
      d5TrustedBorrows (deinitProjectedMoves := true) = .ub ∧
    evalOperands d5TrustedLocals [.move (tpl 2 [.deref]), .copy (tpl 2 [.deref])]
      d5TrustedBorrows = .ok [u8Value 5, u8Value 5] d5TrustedLocals ∧
    evalOperands initTyped
      [.copy (tpl 2 [.deref, .field 0 claimU8Ty]), .move (tpl 2 [.deref, .field 0 claimU8Ty])]
      claimDerefBorrows [] claimPairArrLayouts [] claimPairArrDecls [] true =
        .ok [u8Value 3, u8Value 3] d5TrustedTypedDerefAfterMove ∧
    evalOperands initTyped
      [.move (tpl 2 [.deref, .field 0 claimU8Ty]), .copy (tpl 2 [.deref, .field 0 claimU8Ty])]
      claimDerefBorrows [] claimPairArrLayouts [] claimPairArrDecls [] true = .ub ∧
    evalOperands initTyped
      [.move (tpl 2 [.deref, .field 0 claimU8Ty]), .copy (tpl 3 [.deref, .field 0 claimU8Ty])]
      claimDerefBorrows [] claimPairArrLayouts [] claimPairArrDecls [] true = .ub ∧
    evalOperands initTyped
      [.move (tpl 2 [.deref, .field 0 claimU8Ty]), .copy (tpl 3 [.deref, .field 1 claimU8Ty])]
      claimDerefBorrows [] claimPairArrLayouts [] claimPairArrDecls [] true =
        .ok [u8Value 3, u8Value 4] d5TrustedTypedDerefAfterMove :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`D1`/`D3`/`D5` transparent-projection move, typed `Deref` sub-place
re-initialization, and sub-scalar vs union byte-window `Deref` canaries**:
1. `move (unwrap_unsafe!(_1))` marks `_1` with `movedUninitValue`, and
   `(*_2).0 = 9` via `writePlaceValue` re-initializes the moved-out field of
   `_1 : [(u8, u8); 2]`;
2. strict sub-scalar `move (*_3)` (`*mut u8` on non-union `_1 : u16`) fails
   closed with `.unsupported` rather than poisoning byte `1`; and
3. `move (*_2)` (`*mut u8` at byte `0` of `union U { a: u8, b: u16 }`)
   deinitializes byte `0` while keeping byte `1` (`copy (*_3)`) readable. -/
theorem canary_trusted_transparent_root_and_subscalar_deref_move :
    let u16Init : List LocalSlot :=
      [.uninit, .init (.scalar ⟨770, 2⟩),
       .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
       .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
       .init (.ptr { allocId := 3, offsetBytes := 1 } 8)]
    evalOperand [.uninit, .init (u8Value 5), .init (.ptr { allocId := 2, offsetBytes := 0 } 8)]
        (.move (tpl 1 [.unwrapUnsafeBinder claimU8Ty])) claimDerefBorrows []
        claimScalarDerefLayouts [] claimU8ScalarDerefDecls [] true =
      .ok (u8Value 5)
        [.uninit, .init movedUninitValue, .init (.ptr { allocId := 2, offsetBytes := 0 } 8)] ∧
    writePlaceValue d5TrustedTypedDerefAfterMove claimDerefBorrows
        (tpl 2 [.deref, .field 0 claimU8Ty]) (u8Value 9) claimPairArrDecls claimPairArrLayouts =
      .ok [.uninit,
           .init (.aggregate 0 [.aggregate 0 [u8Value 1, u8Value 2],
             .aggregate 0 [u8Value 9, u8Value 4]]),
           .init (.ptr { allocId := 2, offsetBytes := 2 } 8),
           .init (.ptr { allocId := 3, offsetBytes := 2 } 8)] ∧
    evalOperand u16Init (.move (tpl 3 [.deref])) claimDerefBorrows [] claimScalarDerefLayouts []
      claimU16ScalarDerefDecls [] true = .unsupported ∧
    evalOperand
        [.uninit, .init (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨0, 0⟩, .scalar ⟨3, 1⟩]]),
         .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
         .init (.ptr { allocId := 3, offsetBytes := 1 } 8)]
        (.copy (tpl 3 [.deref])) claimDerefBorrows [] claimUnionPtrLayouts [] claimUnionPtrDecls []
        true =
      .ok (u8Value 3)
        [.uninit, .init (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨0, 0⟩, .scalar ⟨3, 1⟩]]),
         .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
         .init (.ptr { allocId := 3, offsetBytes := 1 } 8)] :=
  ⟨rfl, rfl, rfl, rfl⟩

end Anneal.Mir.Correspondence
