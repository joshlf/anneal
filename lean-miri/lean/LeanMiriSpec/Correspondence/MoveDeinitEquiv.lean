/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Trusted.Rustc.V2026_06_01.MirSemantics.Places
import Miri.Interpreter.ExecutionMachine

/-!
# Consumer-side move deinitialization: patched `lean-miri` and Trusted `Places`

Kernel-checked theorems about the consumer-side runtime move deinitialization
added to the vendored `lean-miri` interpreter (`deinitMovedPlace`, ten files under
`lean-miri/vendor/Miri/Interpreter/`) and to Anneal's trusted MIR semantics
(`Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand ... (deinitProjectedMoves :=
true)`).

* **Part 1 (Trusted `Places`).** `deinitProjectedMoves = false` is definitionally
  the pre-extension `evalOperand`/`evalOperands` (verbatim `Legacy` copies);
  universal decomposition and root-move theorems; `D1`/`D2`/`D3`/`D5`/`D6`/`D9`
  canaries (root, zero-sized, field, re-initialization including typed `Deref`
  write-back and partial-then-full subslice re-initialization, self-aggregate
  field swap, Tree-Borrows-silent `Deref`, element and subslice moves, nested
  field-then-element, enum downcast, thin-pointer `Deref`+subslice, offset slice
  fat-pointer access after element `0` move, and union byte-window moves), each
  with its legacy contrast; the element stride is the pre-extension stride on
  marker-free lists (`inferElemListByteStride_eq_legacy`); and the `ep1-A2`
  canaries: `(*_ptr).field` through a thin pointer at a non-zero byte offset into
  an array element, exact `Deref` targets when distinct places hold equal values
  (`canary_D5_typed_deref_equal_values_exact_target`), strides skipping nested
  moved-out leaves, fail-closed moves out of non-zero-sized global allocations
  (and no-op moves of zero-sized ones), a partial byte-window move out of
  overlapping union fields (`canary_D3_union_partial_byte_window_move`), and the
  `ep1-B3` multi-level projection (`_1.0.1`, `(_1[i]).0`, `(*_p).0[1..3]`,
  `((*_fatPtr)[1]).0`) and transparent `.opaqueCast` / `.unwrapUnsafeBinder`
  theorems (`deinitMovedSubPlace_opaqueCast_prefix`,
  `deinitMovedSubPlace_unwrapUnsafeBinder_prefix`,
  `canary_B3_chained_projections_move_and_reinit`,
  `canary_B3_transparent_opaqueCast_and_unwrapUnsafeBinder_moves`).
* **Part 2 (`lean-miri`, `deinitMovedPlace = false`).** `Cast.cast` and
  `Call.evalFnCallArgumentAt`/`evalCalleeAndArgs`/`passArgument`/
  `evalCallTerminator`/`evalTailCallTerminator` are the unchanged source (the
  consumer-side `…Moving` variants are separate definitions); the patched
  `LocalAccess.evalOperand`/`evalOperandImmediate`,
  `OperandMachine.evalOperand`/`evalOperandAt`, `PlaceMachine.readImmediate`,
  `Place.copyRuntimePlaceNoValidate` and `Cast.castMoving` equal the source with
  the flag off or the latch disarmed (verbatim `src…` copies of the base-commit
  bodies and of their private helpers), and the executor's place dictionaries
  have a disarmed latch.
* **Part 3 (`lean-miri`, `deinitMovedPlace = true`).** Tree-Borrows-silent and
  race-silent deinitialization hooks (contrasted with the source write hook,
  which performs a Tree Borrows `.Write`), the read-then-deinit decomposition of
  `PlaceMachine.readImmediate`, operand-latch behavior of
  `OperandMachine.evalOperand` (including projected immediate moves
  `operandMachine_evalOperand_move_projected_immediate`), step-boundary latch
  clearing; universal call
  theorems: every consumer-side argument is an `FnArg.Copy` (one theorem per
  branch of `Call.evalFnCallArgumentMoving`), on which `passArgument` and
  `allocateVarargs` never run `protectArgument`
  (`call_passArgument_copy_protect_irrelevant`,
  `call_allocateVarargs_protect_irrelevant`), and argument snapshots run under
  `RetagMode.None` (`call_materializeArgument_indirect_eq`); concrete runs of the
  real `Call.evalCalleeAndArgsMoving` showing that a moved immediate argument is
  deinitialized, that `f(move _1, copy _1)` and `(move _1)(copy _1)` fault, and
  that `call unresolved(move _uninit)` faults before callee resolution
  (kani#5172); concrete `D4` runs of the real `evalRvalueIntoPlace`
  (`copy _1 + move _1` succeeds, `move _1 + copy _1` and `move _1 + move _1`
  fault, for memory-backed, immediate and projected-immediate locals); the event
  order of the real `Cast.castMoving` (read, then deinitialize, then write; latch
  hand-off to transmute and unsizing copies); `CopyNonOverlapping` FIFO latch
  reordering (`prependLastPendingMoveDeinit`, including `count == 0`), `Repeat`
  (`length == 0` and `length > 0`) and `Aggregate` move deinitialization;
  `RustCall` tuple argument unpacking and `FnInstance.Virtual` receiver dispatch
  through `Call.evalCallTerminatorMoving`; `D8` `Assert` and unwinding `Call`
  cleanup (`canary_D8_assert_cleanup_moved_cond_ub`,
  `canary_D8_unwinding_call_moved_arg_ub`, `canary_D8_unwinding_call_unmoved_ok`),
  tail-call (`evalTailCallTerminatorMoving` / `initFnTailCallMoving`: caller
  deinitialization before `popRaw`/`cleanup` and temporary cleanup on both normal
  completion and error, `canary_tailCallMoving_deinit_before_pop_and_temp_cleanup`),
  and `Drop` (`call_initDropInPlaceCall_static_eq`,
  `canary_dropInPlace_preserves_initialized_and_detects_moved`);
  operand reads `PlaceMachine.readImmediate (← OperandMachine.evalOperandAt …)`
  of moved places (`operandRead_move_indirect`,
  `discriminantRead_move_immediate_root`); the `SwitchInt` terminator of the
  assembled `ExecutionMachine.stepHooks` faults with a faulting discriminant read
  and branches from the post-read state (`stepHooks_switchInt_discriminant_error`,
  `stepHooks_switchInt_otherwise`), with a concrete `SwitchInt` run through the
  real `ControlFlow.evalTerminator` (`canary_switchInt_move_deinit`); `UnaryOp`
  (including `PtrMetadata` of a wide pointer) reads and deinitializes its whole
  operand before the operator runs (`evalRvalueIntoPlace_unaryOp`,
  `rvalueHooks_unaryOp_move_indirect`); and `D7` call destinations are resolved
  before argument moves (`call_evalCallTerminatorMoving_dest_before_args`,
  `canary_D7_call_dest_resolved_before_arg_move`,
  `canary_D7_call_dest_overlaps_moved_arg`).
* **Part 4.** Root, indirect, call-argument `Deref` (including projected
  `(*_p).restProj`), and projected sub-place move simulations between
  `lean-miri` (`deinitMovedPlace = true`) and Trusted `evalOperand
  (deinitProjectedMoves := true)`, together with concrete kernel-checked
  non-vacuity witnesses (`witness_root_move_simulation`,
  `witness_projected_subplace_move_simulation`,
  `witness_d7_call_arg_move_deref_projected_sibling_frozen_simulation`).
* **Part 5.** An environment audit: no declaration depends on `sorryAx`,
  `Lean.ofReduceBool` or `Lean.trustCompiler`, and the proofs use only `propext`
  and `Quot.sound` (`Classical.choice` reaches statements only through the
  vendored `lean-miri` machine definitions they mention).

## Known limitations

* **Niche-encoded enums (`lean-miri`, `deinitMovedPlace = true`).** Moving an enum
  payload (`move (_1 as Some).0`) deinitializes the payload bytes, including the
  bytes that carry a niche-encoded tag (for example the pointer of
  `Option<Box<T>>`), so the `discriminant(_1)` read that drop elaboration emits
  after such a partial move faults on valid Rust. The Trusted semantics keeps the
  variant index outside the payload and its `Rvalue.discriminant` reads with the
  default `false` (`canary_D2_enum_downcast_discriminant_after_move`), so the two
  semantics disagree on this program shape; Part 4 relates root moves only.
* **Error paths (`lean-miri`).** When a later argument of
  `Call.evalCalleeAndArgsMoving` faults, the snapshots of the earlier arguments are
  not deallocated and earlier moved arguments stay deinitialized; every such fault
  is terminal for the machine.
* **Unsizing (`lean-miri`).** `Cast.castMoving` deinitializes the moved fields of an
  unsized struct source, not its padding bytes.
* **Moved-out leaves have no byte width (Trusted).** Untyped (`localDecls = []`)
  byte-offset inference reads sizes off runtime values; element strides skip
  moved-out leaves (`inferElemListByteStride`), but other untyped offset
  resolutions over a container holding a moved-out leaf (for example a thin
  pointer resolved element-wise past a moved element) fault conservatively.
* **Reinterpreting `Deref` moves (Trusted).** A typed thin-pointer move whose read
  decodes the pointee bytes instead of reaching a structural sub-place (a
  pointer cast into the middle of an aggregate followed by a projection, or a
  whole `[u8; 2]` pointee inside a `[u8; 4]`) fails closed with `.unsupported`.
-/

namespace LeanMiriSpec.Correspondence.MoveDeinitEquivTactic

open Lean Elab Tactic in
/-- `unfold_named "<full name>"` unfolds the constant whose full name renders as
the given string. It is used only to unfold `private` source helpers (which
cannot be named from another module) when relating a patched definition to its
verbatim source copy in Part 2. -/
elab "unfold_named " n:str : tactic => do
  let env ← getEnv
  let target := n.getString
  let parsed := (target.splitOn ".").foldl (init := Name.anonymous) fun acc part =>
    match part.toNat? with
    | some k => Name.mkNum acc k
    | none => Name.mkStr acc part
  if env.contains parsed then
    evalTactic (← `(tactic| unfold $(mkIdent parsed):ident))
  else
    let mut found := false
    for (name, _) in env.constants.map₁.toList do
      if name.toString == target then
        found := true
        evalTactic (← `(tactic| unfold $(mkIdent name):ident))
    unless found do throwError "constant {target} not found"

end LeanMiriSpec.Correspondence.MoveDeinitEquivTactic

namespace LeanMiriSpec.Correspondence.MoveDeinitEquiv

section TrustedPart

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## Part 1: Trusted `Places.evalOperand (deinitProjectedMoves := …)` -/

section Legacy

/-- Verbatim copy of `Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand` before the
`deinitProjectedMoves` extension (base commit `b91fc2aa`), used only to state the
backward-compatibility theorem `evalOperand_deinitProjectedMoves_false_eq_legacy`. -/
def legacyEvalOperand
    (locals : List LocalSlot)
    (op : Operand)
    (borrows : List BorrowEntry := .nil)
    (globals : List CapturedAllocation := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (callerLocals : List LocalSlot := .nil)
    (localDecls : List LocalDecl := .nil)
    (callStack : List SavedCallerFrame := .nil) :
    PlaceReadResult :=
  match op with
  | .constant c =>
    match c.val with
    | .indirect allocId offset =>
      match lookupGlobalAlloc globals allocId with
      | .some _ =>
        match evalConstValue (.indirect allocId offset) c.ty globals layouts with
        | .some v => .ok v locals
        | .none => .ub
      | .none => .unsupported
    | .unevaluated _ => .unsupported
    | cv =>
      match evalConstValue cv c.ty globals layouts with
      | .some v => .ok v locals
      | .none => .unsupported
  | .copy p =>
    match p.projection with
    | .deref :: restProj =>
      match localDecls with
      | .nil =>
        match get? locals p.local_ with
        | .some (.init (.ptr ptrVal sz)) =>
          match lookupBorrow borrows ptrVal.tag with
          | .some entry =>
            match entry.perm with
            | .disabled => .ub
            | _ =>
              match
                needsThinPtrElemResolution entry.targetProjection ptrVal.offsetBytes
              with
              | false =>
                match activeFrameSlot? locals callStack entry.targetFrameDepth entry.targetLocal with
                | .some (.init targetRootVal) =>
                  let fullProj :=
                    match entry.targetProjection with
                    | .nil => restProj
                    | ph :: pt => ph :: appendProjections pt restProj
                  match readProjectedValue locals targetRootVal fullProj with
                  | .ok fieldVal => .ok fieldVal locals
                  | .ub => .ub
                  | .unsupported => .unsupported
                | .some _ => .ub
                | .none =>
                  match foreignFrameSlot? callStack callerLocals entry.targetFrameDepth entry.targetLocal with
                  | .some (.init targetRootVal) =>
                    let fullProj :=
                      match entry.targetProjection with
                      | .nil => restProj
                      | ph :: pt => ph :: appendProjections pt restProj
                    match readProjectedValue locals targetRootVal fullProj with
                    | .ok fieldVal => .ok fieldVal locals
                    | .ub => .ub
                    | .unsupported => .unsupported
                  | _ => .ub
              | true =>
                match activeFrameSlot? locals callStack entry.targetFrameDepth entry.targetLocal with
                | .some (.init targetRootVal) =>
                  match
                    resolveStackThinPtrTargetProj?
                      locals
                      targetRootVal
                      entry
                      ptrVal
                      restProj
                  with
                  | .none => .ub
                  | .some fullProj =>
                    match readProjectedValue locals targetRootVal fullProj with
                    | .ok fieldVal => .ok fieldVal locals
                    | .ub => .ub
                    | .unsupported => .unsupported
                | .some _ => .ub
                | .none =>
                  match foreignFrameSlot? callStack callerLocals entry.targetFrameDepth entry.targetLocal with
                  | .some (.init targetRootVal) =>
                    match
                      resolveStackThinPtrTargetProj?
                        locals
                        targetRootVal
                        entry
                        ptrVal
                        restProj
                    with
                    | .none => .ub
                    | .some fullProj =>
                      match readProjectedValue locals targetRootVal fullProj with
                      | .ok fieldVal => .ok fieldVal locals
                      | .ub => .ub
                      | .unsupported => .unsupported
                  | _ => .ub
          | .none =>
            match lookupGlobalAlloc globals ptrVal.allocId with
            | .some alloc =>
              evalGlobalDerefRead
                locals
                alloc
                ptrVal.offsetBytes
                sz
                restProj
                layouts
                .none
            | .none => .ub
        | .some (.init (.aggregate 0 (.ptr ptrVal ptrSz :: .scalar lenSc :: .nil))) =>
          evalSliceFatPtrDerefRead
            locals
            ptrVal
            ptrSz
            lenSc
            restProj
            borrows
            globals
            layouts
            callerLocals
            .none
            (callStack := callStack)
        | _ => .ub
      | _ :: _ =>
        let pointeeTyOpt :=
          placeTyResolved localDecls layouts { local_ := p.local_, projection := .deref :: .nil }
        let accessedTyOpt := placeTyResolved localDecls layouts p
        match get? locals p.local_ with
        | .some (.init (.ptr ptrVal sz)) =>
          match lookupBorrow borrows ptrVal.tag with
          | .some entry =>
            match entry.perm with
            | .disabled => .ub
            | _ =>
              match activeFrameSlot? locals callStack entry.targetFrameDepth entry.targetLocal with
              | .some (.init targetRootVal) =>
                evalStackThinPtrTypedDerefRead
                  locals
                  targetRootVal
                  entry
                  ptrVal
                  restProj
                  localDecls
                  layouts
                  pointeeTyOpt
                  accessedTyOpt
                  (placeTyResolved
                    localDecls
                    layouts
                    { local_ := entry.targetLocal, projection := entry.targetProjection })
              | .some _ => .ub
              | .none =>
                match foreignFrameSlot? callStack callerLocals entry.targetFrameDepth entry.targetLocal with
                | .some (.init targetRootVal) =>
                  let runTypedForeignRead : PlaceReadResult :=
                    let (targetDecls, targetLayouts) :=
                      foreignFrameDeclsAndLayouts
                        callStack
                        layouts
                        entry.targetFrameDepth
                        entry.targetLocal
                    evalStackThinPtrTypedDerefRead
                      locals
                      targetRootVal
                      entry
                      ptrVal
                      restProj
                      localDecls
                      layouts
                      pointeeTyOpt
                      accessedTyOpt
                      (placeTyResolved
                        targetDecls
                        targetLayouts
                        { local_ := entry.targetLocal, projection := entry.targetProjection })
                      targetDecls
                      targetLayouts
                  match
                    foreignFrameTarget?
                      callStack
                      callerLocals
                      entry.targetFrameDepth
                      entry.targetLocal
                  with
                  | .some (.savedFrame _ _) => runTypedForeignRead
                  | _ =>
                    match
                      needsThinPtrElemResolution entry.targetProjection ptrVal.offsetBytes
                    with
                    | false =>
                      let fullProj :=
                        match entry.targetProjection with
                        | .nil => restProj
                        | ph :: pt => ph :: appendProjections pt restProj
                      match readProjectedValue locals targetRootVal fullProj with
                      | .ok fieldVal => .ok fieldVal locals
                      | .ub => .ub
                      | .unsupported => .unsupported
                    | true => runTypedForeignRead
                | _ => .ub
          | .none =>
            let globalAlignTyOpt : Option Ty :=
              match pointeeTyOpt, restProj with
              | .some pt, _ => .some pt
              | .none, .nil => accessedTyOpt
              | .none, _ :: _ => .none
            match checkDerefAlign localDecls layouts globalAlignTyOpt ptrVal.offsetBytes with
            | false => .ub
            | true =>
              match lookupGlobalAlloc globals ptrVal.allocId with
              | .some alloc =>
                match
                  checkGlobalAllocAlign
                    localDecls
                    layouts
                    globalAlignTyOpt
                    alloc
                    ptrVal.offsetBytes
                with
                | false => .ub
                | true =>
                  match
                    evalGlobalDerefRead
                      locals
                      alloc
                      ptrVal.offsetBytes
                      sz
                      restProj
                      layouts
                      pointeeTyOpt
                  with
                  | .ok fieldVal locals' =>
                    match validateValueForTy? layouts accessedTyOpt fieldVal with
                    | true => .ok fieldVal locals'
                    | false => .ub
                  | .ub => .ub
                  | .unsupported => .unsupported
              | .none => .ub
        | .some (.init (.aggregate 0 (.ptr ptrVal ptrSz :: .scalar lenSc :: .nil))) =>
          evalSliceFatPtrDerefRead
            locals
            ptrVal
            ptrSz
            lenSc
            restProj
            borrows
            globals
            layouts
            callerLocals
            pointeeTyOpt
            localDecls
            accessedTyOpt
            (callStack := callStack)
        | _ => .ub
    | .nil =>
      match get? locals p.local_ with
      | .some (.init rootVal) =>
        match readProjectedValue locals rootVal .nil with
        | .ok fieldVal => .ok fieldVal locals
        | .ub => .ub
        | .unsupported => .unsupported
      | .some .uninit => .ub
      | .some .dead => .ub
      | .none => .ub
    | proj :: rest =>
      match get? locals p.local_ with
      | .some (.init rootVal) =>
        match placeTouchesUnion localDecls layouts p with
        | false =>
          match readProjectedValue locals rootVal (proj :: rest) with
          | .ok fieldVal => .ok fieldVal locals
          | .ub => .ub
          | .unsupported => .unsupported
        | true =>
          match readProjectedForLocal locals localDecls layouts p.local_ rootVal (proj :: rest) with
          | .ok fieldVal =>
            match validateValueForTy? layouts (placeTyResolved localDecls layouts p) fieldVal with
            | true => .ok fieldVal locals
            | false => .ub
          | .ub => .ub
          | .unsupported => .unsupported
      | .some .uninit => .ub
      | .some .dead => .ub
      | .none => .ub
  | .move p =>
    match p.projection with
    | .nil =>
      match get? locals p.local_ with
      | .some (.init v) =>
        match set? locals p.local_ .uninit with
        | .some locals' => .ok v locals'
        | .none => .ub
      | .some .uninit => .ub
      | .some .dead => .ub
      | .none => .ub
    | .deref :: restProj =>
      match localDecls with
      | .nil =>
        match get? locals p.local_ with
        | .some (.init (.ptr ptrVal sz)) =>
          match lookupBorrow borrows ptrVal.tag with
          | .some entry =>
            match entry.perm with
            | .disabled => .ub
            | _ =>
              match
                needsThinPtrElemResolution entry.targetProjection ptrVal.offsetBytes
              with
              | false =>
                match activeFrameSlot? locals callStack entry.targetFrameDepth entry.targetLocal with
                | .some (.init targetRootVal) =>
                  let fullProj :=
                    match entry.targetProjection with
                    | .nil => restProj
                    | ph :: pt => ph :: appendProjections pt restProj
                  match readProjectedValue locals targetRootVal fullProj with
                  | .ok fieldVal => .ok fieldVal locals
                  | .ub => .ub
                  | .unsupported => .unsupported
                | .some _ => .ub
                | .none =>
                  match foreignFrameSlot? callStack callerLocals entry.targetFrameDepth entry.targetLocal with
                  | .some (.init targetRootVal) =>
                    let fullProj :=
                      match entry.targetProjection with
                      | .nil => restProj
                      | ph :: pt => ph :: appendProjections pt restProj
                    match readProjectedValue locals targetRootVal fullProj with
                    | .ok fieldVal => .ok fieldVal locals
                    | .ub => .ub
                    | .unsupported => .unsupported
                  | _ => .ub
              | true =>
                match activeFrameSlot? locals callStack entry.targetFrameDepth entry.targetLocal with
                | .some (.init targetRootVal) =>
                  match
                    resolveStackThinPtrTargetProj?
                      locals
                      targetRootVal
                      entry
                      ptrVal
                      restProj
                  with
                  | .none => .ub
                  | .some fullProj =>
                    match readProjectedValue locals targetRootVal fullProj with
                    | .ok fieldVal => .ok fieldVal locals
                    | .ub => .ub
                    | .unsupported => .unsupported
                | .some _ => .ub
                | .none =>
                  match foreignFrameSlot? callStack callerLocals entry.targetFrameDepth entry.targetLocal with
                  | .some (.init targetRootVal) =>
                    match
                      resolveStackThinPtrTargetProj?
                        locals
                        targetRootVal
                        entry
                        ptrVal
                        restProj
                    with
                    | .none => .ub
                    | .some fullProj =>
                      match readProjectedValue locals targetRootVal fullProj with
                      | .ok fieldVal => .ok fieldVal locals
                      | .ub => .ub
                      | .unsupported => .unsupported
                  | _ => .ub
          | .none =>
            match lookupGlobalAlloc globals ptrVal.allocId with
            | .some alloc =>
              evalGlobalDerefRead
                locals
                alloc
                ptrVal.offsetBytes
                sz
                restProj
                layouts
                .none
            | .none => .ub
        | .some (.init (.aggregate 0 (.ptr ptrVal ptrSz :: .scalar lenSc :: .nil))) =>
          evalSliceFatPtrDerefRead
            locals
            ptrVal
            ptrSz
            lenSc
            restProj
            borrows
            globals
            layouts
            callerLocals
            .none
            (callStack := callStack)
        | _ => .ub
      | _ :: _ =>
        let pointeeTyOpt :=
          placeTyResolved localDecls layouts { local_ := p.local_, projection := .deref :: .nil }
        let accessedTyOpt := placeTyResolved localDecls layouts p
        match get? locals p.local_ with
        | .some (.init (.ptr ptrVal sz)) =>
          match lookupBorrow borrows ptrVal.tag with
          | .some entry =>
            match entry.perm with
            | .disabled => .ub
            | _ =>
              match activeFrameSlot? locals callStack entry.targetFrameDepth entry.targetLocal with
              | .some (.init targetRootVal) =>
                evalStackThinPtrTypedDerefRead
                  locals
                  targetRootVal
                  entry
                  ptrVal
                  restProj
                  localDecls
                  layouts
                  pointeeTyOpt
                  accessedTyOpt
                  (placeTyResolved
                    localDecls
                    layouts
                    { local_ := entry.targetLocal, projection := entry.targetProjection })
              | .some _ => .ub
              | .none =>
                match foreignFrameSlot? callStack callerLocals entry.targetFrameDepth entry.targetLocal with
                | .some (.init targetRootVal) =>
                  let runTypedForeignRead : PlaceReadResult :=
                    let (targetDecls, targetLayouts) :=
                      foreignFrameDeclsAndLayouts
                        callStack
                        layouts
                        entry.targetFrameDepth
                        entry.targetLocal
                    evalStackThinPtrTypedDerefRead
                      locals
                      targetRootVal
                      entry
                      ptrVal
                      restProj
                      localDecls
                      layouts
                      pointeeTyOpt
                      accessedTyOpt
                      (placeTyResolved
                        targetDecls
                        targetLayouts
                        { local_ := entry.targetLocal, projection := entry.targetProjection })
                      targetDecls
                      targetLayouts
                  match
                    foreignFrameTarget?
                      callStack
                      callerLocals
                      entry.targetFrameDepth
                      entry.targetLocal
                  with
                  | .some (.savedFrame _ _) => runTypedForeignRead
                  | _ =>
                    match
                      needsThinPtrElemResolution entry.targetProjection ptrVal.offsetBytes
                    with
                    | false =>
                      let fullProj :=
                        match entry.targetProjection with
                        | .nil => restProj
                        | ph :: pt => ph :: appendProjections pt restProj
                      match readProjectedValue locals targetRootVal fullProj with
                      | .ok fieldVal => .ok fieldVal locals
                      | .ub => .ub
                      | .unsupported => .unsupported
                    | true => runTypedForeignRead
                | _ => .ub
          | .none =>
            let globalAlignTyOpt : Option Ty :=
              match pointeeTyOpt, restProj with
              | .some pt, _ => .some pt
              | .none, .nil => accessedTyOpt
              | .none, _ :: _ => .none
            match checkDerefAlign localDecls layouts globalAlignTyOpt ptrVal.offsetBytes with
            | false => .ub
            | true =>
              match lookupGlobalAlloc globals ptrVal.allocId with
              | .some alloc =>
                match
                  checkGlobalAllocAlign
                    localDecls
                    layouts
                    globalAlignTyOpt
                    alloc
                    ptrVal.offsetBytes
                with
                | false => .ub
                | true =>
                  match
                    evalGlobalDerefRead
                      locals
                      alloc
                      ptrVal.offsetBytes
                      sz
                      restProj
                      layouts
                      pointeeTyOpt
                  with
                  | .ok fieldVal locals' =>
                    match validateValueForTy? layouts accessedTyOpt fieldVal with
                    | true => .ok fieldVal locals'
                    | false => .ub
                  | .ub => .ub
                  | .unsupported => .unsupported
              | .none => .ub
        | .some (.init (.aggregate 0 (.ptr ptrVal ptrSz :: .scalar lenSc :: .nil))) =>
          evalSliceFatPtrDerefRead
            locals
            ptrVal
            ptrSz
            lenSc
            restProj
            borrows
            globals
            layouts
            callerLocals
            pointeeTyOpt
            localDecls
            accessedTyOpt
            (callStack := callStack)
        | _ => .ub
    | proj :: rest =>
      match get? locals p.local_ with
      | .some (.init rootVal) =>
        match placeTouchesUnion localDecls layouts p with
        | false =>
          match readProjectedValue locals rootVal (proj :: rest) with
          | .ok fieldVal => .ok fieldVal locals
          | .ub => .ub
          | .unsupported => .unsupported
        | true =>
          match readProjectedForLocal locals localDecls layouts p.local_ rootVal (proj :: rest) with
          | .ok fieldVal =>
            match validateValueForTy? layouts (placeTyResolved localDecls layouts p) fieldVal with
            | true => .ok fieldVal locals
            | false => .ub
          | .ub => .ub
          | .unsupported => .unsupported
      | .some .uninit => .ub
      | .some .dead => .ub
      | .none => .ub

/-- Verbatim copy of `Trusted.Rustc.V2026_06_01.MirSemantics.evalOperands` before the
`deinitProjectedMoves` extension (base commit `b91fc2aa`). -/
def legacyEvalOperands
    (locals : List LocalSlot)
    (ops : List Operand)
    (borrows : List BorrowEntry := .nil)
    (globals : List CapturedAllocation := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (callerLocals : List LocalSlot := .nil)
    (localDecls : List LocalDecl := .nil)
    (callStack : List SavedCallerFrame := .nil) :
    OperandsEvalResult :=
  match ops with
  | .nil => .ok .nil locals
  | op :: rest =>
    match legacyEvalOperand locals op borrows globals layouts callerLocals localDecls callStack with
    | .ok v locals₁ =>
      match legacyEvalOperands locals₁ rest borrows globals layouts callerLocals localDecls callStack with
      | .ok vs locals₂ => .ok (v :: vs) locals₂
      | .ub => .ub
      | .unsupported => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported

/-- Verbatim copy of `Trusted.Rustc.V2026_06_01.MirSemantics.inferElemListByteStride`
before the `deinitProjectedMoves` extension (base commit `b91fc2aa`). -/
def legacyInferElemListByteStride : List Value → Nat
  | .scalar sc :: _ => sc.sizeBytes
  | .ptr _ sz :: _ => sz
  | .unit :: _ => 0
  | .aggregate 0 fields :: _ =>
    match inferValueByteSizeAux 8 (.aggregate 0 fields) with
    | .some sz => sz
    | .none => 1
  | _ => 1

end Legacy

section TrustedPlaces

/-- **Backward compatibility (`rfl`).** With `deinitProjectedMoves = false`
(the default), the extended `evalOperand` is definitionally the pre-extension
`evalOperand`, for every operand and context. -/
theorem evalOperand_deinitProjectedMoves_false_eq_legacy
    (locals : List LocalSlot) (op : Operand) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame) :
    evalOperand locals op borrows globals layouts callerLocals localDecls callStack false =
      legacyEvalOperand locals op borrows globals layouts callerLocals localDecls callStack := by
  cases op <;> rfl

/-- The default argument is `false`: existing callers are unaffected. -/
theorem evalOperand_deinitProjectedMoves_default
    (locals : List LocalSlot) (op : Operand) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame) :
    evalOperand locals op borrows globals layouts callerLocals localDecls callStack =
      legacyEvalOperand locals op borrows globals layouts callerLocals localDecls callStack :=
  evalOperand_deinitProjectedMoves_false_eq_legacy locals op borrows globals layouts callerLocals
    localDecls callStack

/-- **Backward compatibility of `evalOperands`.** -/
theorem evalOperands_deinitProjectedMoves_false_eq_legacy
    (ops : List Operand) :
    ∀ (locals : List LocalSlot) (borrows : List BorrowEntry)
      (globals : List CapturedAllocation) (layouts : LayoutTable)
      (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
      (callStack : List SavedCallerFrame),
      evalOperands locals ops borrows globals layouts callerLocals localDecls callStack false =
        legacyEvalOperands locals ops borrows globals layouts callerLocals localDecls callStack := by
  induction ops with
  | nil => intros; rfl
  | cons op rest ih =>
    intro locals borrows globals layouts callerLocals localDecls callStack
    simp only [evalOperands, legacyEvalOperands]
    rw [evalOperand_deinitProjectedMoves_false_eq_legacy]
    cases legacyEvalOperand locals op borrows globals layouts callerLocals localDecls callStack with
    | ok v locals₁ =>
      dsimp only
      rw [ih]
      cases legacyEvalOperands locals₁ rest borrows globals layouts callerLocals localDecls callStack <;>
        rfl
    | ub => rfl
    | unsupported => rfl

/-- `evalCopyPlaceRead` is the `Operand.copy` read of `evalOperand`. -/
theorem evalCopyPlaceRead_eq_copy
    (locals : List LocalSlot) (p : Place) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame) :
    evalCopyPlaceRead locals p borrows globals layouts callerLocals localDecls callStack =
      evalOperand locals (.copy p) borrows globals layouts callerLocals localDecls callStack := rfl

/-- **Copy reads in `deinitProjectedMoves` mode**: the legacy copy read, faulting
on any value that contains a moved-out leaf. -/
theorem evalOperand_copy_deinit
    (locals : List LocalSlot) (p : Place) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame) :
    evalOperand locals (.copy p) borrows globals layouts callerLocals localDecls callStack true =
      guardMovedUninitRead
        (evalOperand locals (.copy p) borrows globals layouts callerLocals localDecls callStack) :=
  rfl

/-- **Moves in `deinitProjectedMoves` mode**: the legacy copy read, followed by
`evalMoveOperandDeinit`. In particular the borrow table is only read. -/
theorem evalOperand_move_deinit
    (locals : List LocalSlot) (p : Place) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame) :
    evalOperand locals (.move p) borrows globals layouts callerLocals localDecls callStack true =
      evalMoveOperandDeinit p borrows globals layouts callerLocals localDecls callStack
        (evalOperand locals (.copy p) borrows globals layouts callerLocals localDecls callStack) :=
  rfl

/-- Constants are unaffected by `deinitProjectedMoves`. -/
theorem evalOperand_constant_deinit
    (locals : List LocalSlot) (c : ConstOperand) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame) :
    evalOperand locals (.constant c) borrows globals layouts callerLocals localDecls callStack true =
      evalOperand locals (.constant c) borrows globals layouts callerLocals localDecls callStack :=
  rfl

/-- Any read in `deinitProjectedMoves` mode faults on a value containing a
moved-out leaf. -/
theorem evalOperand_copy_deinit_movedUninit_ub
    (locals : List LocalSlot) (p : Place) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame) (v : Value) (locals' : List LocalSlot)
    (hread : evalOperand locals (.copy p) borrows globals layouts callerLocals localDecls
      callStack = .ok v locals')
    (hmoved : valueContainsMovedUninit v = true) :
    evalOperand locals (.copy p) borrows globals layouts callerLocals localDecls callStack true =
      .ub := by
  rw [evalOperand_copy_deinit, hread]
  simp only [guardMovedUninitRead, hmoved]

/-- A move in `deinitProjectedMoves` mode of a value containing a moved-out leaf
faults. -/
theorem evalOperand_move_deinit_movedUninit_ub
    (locals : List LocalSlot) (p : Place) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame) (v : Value) (locals' : List LocalSlot)
    (hread : evalOperand locals (.copy p) borrows globals layouts callerLocals localDecls
      callStack = .ok v locals')
    (hmoved : valueContainsMovedUninit v = true) :
    evalOperand locals (.move p) borrows globals layouts callerLocals localDecls callStack true =
      .ub := by
  rw [evalOperand_move_deinit, hread]
  simp only [evalMoveOperandDeinit, hmoved]

/-- The moved-out marker is flagged; `.unit` and every empty aggregate are not. -/
theorem movedUninit_flags :
    valueContainsMovedUninit movedUninitValue = true ∧
    valueContainsMovedUninit .unit = false ∧
    (∀ k, valueContainsMovedUninit (.aggregate k .nil) = false) ∧
    valueContainsMovedUninit (.scalar { bits := 0, sizeBytes := 0 }) = false :=
  ⟨rfl, rfl, fun _ => rfl, rfl⟩

/-- A successful slot read makes the point update succeed, and the updated
slot is read back. -/
theorem get?_set?_isSome {α : Type} (xs : List α) (i : Nat) (x y : α)
    (h : get? xs i = .some x) :
    ∃ ys, set? xs i y = .some ys ∧ get? ys i = .some y := by
  have hlt : i < xs.length := by
    simp only [get?] at h
    exact (List.getElem?_eq_some_iff.mp h).1
  refine ⟨xs.set i y, ?_, ?_⟩
  · simp only [set?, hlt, ite_true]
  · simp only [get?, List.getElem?_set_self hlt]

/-- **`D1` root move (universal).** Moving an initialized, non-zero-sized root
local returns its value and leaves the slot `.uninit`. -/
theorem evalOperand_move_root_deinit
    (locals : List LocalSlot) (l : Local) (v : Value) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame)
    (hget : get? locals l = .some (.init v))
    (hmoved : valueContainsMovedUninit v = false)
    (hzst : moveValueIsZeroSized localDecls layouts
      (placeTyResolved localDecls layouts { local_ := l, projection := .nil }) v = false) :
    ∃ locals', get? locals' l = .some .uninit ∧
      evalOperand locals (.move { local_ := l, projection := .nil }) borrows globals layouts
        callerLocals localDecls callStack true = .ok v locals' := by
  obtain ⟨ys, hset, hget'⟩ := get?_set?_isSome locals l (.init v) .uninit hget
  refine ⟨ys, hget', ?_⟩
  rw [evalOperand_move_deinit]
  simp only [evalOperand, hget, readProjectedValue, evalMoveOperandDeinit, hmoved, hzst,
    deinitMovedSubPlace, hset]

/-- **`D1` zero-sized root move (universal).** Moving a zero-sized value leaves
the source initialized. -/
theorem evalOperand_move_root_zst
    (locals : List LocalSlot) (l : Local) (v : Value) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame)
    (hget : get? locals l = .some (.init v))
    (hmoved : valueContainsMovedUninit v = false)
    (hzst : moveValueIsZeroSized localDecls layouts
      (placeTyResolved localDecls layouts { local_ := l, projection := .nil }) v = true) :
    evalOperand locals (.move { local_ := l, projection := .nil }) borrows globals layouts
      callerLocals localDecls callStack true = .ok v locals := by
  rw [evalOperand_move_deinit]
  simp only [evalOperand, hget, readProjectedValue, evalMoveOperandDeinit, hmoved, hzst]

/-- **`D1` re-read after a root move (universal).** -/
theorem evalOperand_read_uninit_root_ub
    (locals : List LocalSlot) (l : Local) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame) (deinit : Bool)
    (hget : get? locals l = .some .uninit) :
    evalOperand locals (.copy { local_ := l, projection := .nil }) borrows globals layouts
      callerLocals localDecls callStack deinit = .ub ∧
    evalOperand locals (.move { local_ := l, projection := .nil }) borrows globals layouts
      callerLocals localDecls callStack deinit = .ub := by
  cases deinit <;>
    simp only [evalOperand, evalCopyPlaceRead, hget, guardMovedUninitRead, evalMoveOperandDeinit,
      and_self]

/-- **Backward compatibility of the element stride.** On element lists without
a moved-out leaf (every list the statement semantics, which never passes
`deinitProjectedMoves := true`, produces) `inferElemListByteStride`, which skips
elements holding moved-out leaves, is the pre-extension stride. -/
theorem inferElemListByteStride_eq_legacy (elems : List Value)
    (h : valueListContainsMovedUninit elems = false) :
    inferElemListByteStride elems = legacyInferElemListByteStride elems := by
  cases elems with
  | nil => rfl
  | cons v rest =>
    have hv : valueContainsMovedUninit v = false := by
      cases hc : valueContainsMovedUninit v
      · rfl
      · simp only [valueListContainsMovedUninit, hc] at h
        exact absurd h (by decide)
    rcases v with _ | ⟨bits, _ | n⟩ | ⟨p, sz⟩ | ⟨_ | k, fields⟩
    · rfl
    · have hbits : Nat.beq bits 1 = false := hv
      simp only [inferElemListByteStride, legacyInferElemListByteStride, hbits]
    · rfl
    · rfl
    · have hfields : valueListContainsMovedUninit fields = false := hv
      show (match valueListContainsMovedUninit fields with
        | true => inferElemListByteStride rest
        | false =>
          match inferValueByteSizeAux 8 (.aggregate 0 fields) with
          | .some sz => sz
          | .none => 1) = _
      rw [hfields]
      rfl
    · rfl

/-- Leading `.opaqueCast` is transparent to `lastStructuralProjection?`. -/
theorem lastStructuralProjection?_opaqueCast_prefix (ty : Ty) (proj : List ProjectionElem) :
    lastStructuralProjection? (.opaqueCast ty :: proj) = lastStructuralProjection? proj := by
  simp only [lastStructuralProjection?]
  cases lastStructuralProjection? proj <;> rfl

/-- Leading `.unwrapUnsafeBinder` is transparent to `lastStructuralProjection?`. -/
theorem lastStructuralProjection?_unwrapUnsafeBinder_prefix (ty : Ty) (proj : List ProjectionElem) :
    lastStructuralProjection? (.unwrapUnsafeBinder ty :: proj) = lastStructuralProjection? proj := by
  simp only [lastStructuralProjection?]
  cases lastStructuralProjection? proj <;> rfl

/-- Leading `.opaqueCast` is transparent to `movedMarkerValue`. -/
theorem movedMarkerValue_opaqueCast_prefix (ty : Ty) (proj : List ProjectionElem) (v : Value) :
    movedMarkerValue (.opaqueCast ty :: proj) v = movedMarkerValue proj v := by
  simp only [movedMarkerValue, lastStructuralProjection?_opaqueCast_prefix]

/-- Leading `.unwrapUnsafeBinder` is transparent to `movedMarkerValue`. -/
theorem movedMarkerValue_unwrapUnsafeBinder_prefix (ty : Ty) (proj : List ProjectionElem)
    (v : Value) :
    movedMarkerValue (.unwrapUnsafeBinder ty :: proj) v = movedMarkerValue proj v := by
  simp only [movedMarkerValue, lastStructuralProjection?_unwrapUnsafeBinder_prefix]

/-- Leading `.opaqueCast` on a non-empty, union-free, deref-free projection
chain is transparent to `deinitMovedSubPlace`. -/
theorem deinitMovedSubPlace_opaqueCast_prefix
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (loc : Local) (rootVal fieldVal : Value) (ty : Ty)
    (head : ProjectionElem) (tail : List ProjectionElem)
    (hnoDeref : projHasDeref (head :: tail) = false)
    (hnoUnion₁ : placeTouchesUnion localDecls layouts
      { local_ := loc, projection := .opaqueCast ty :: head :: tail } = false)
    (hnoUnion₂ : placeTouchesUnion localDecls layouts
      { local_ := loc, projection := head :: tail } = false) :
    deinitMovedSubPlace locals localDecls layouts loc rootVal
        (.opaqueCast ty :: head :: tail) fieldVal =
      deinitMovedSubPlace locals localDecls layouts loc rootVal (head :: tail) fieldVal := by
  have hnoDeref' : projHasDeref (.opaqueCast ty :: head :: tail) = false := hnoDeref
  simp only [deinitMovedSubPlace, hnoDeref, hnoDeref', hnoUnion₁, hnoUnion₂,
    movedMarkerValue_opaqueCast_prefix, writeProjectedValue]

/-- Leading `.unwrapUnsafeBinder` on a non-empty, union-free, deref-free
projection chain is transparent to `deinitMovedSubPlace`. -/
theorem deinitMovedSubPlace_unwrapUnsafeBinder_prefix
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (loc : Local) (rootVal fieldVal : Value) (ty : Ty)
    (head : ProjectionElem) (tail : List ProjectionElem)
    (hnoDeref : projHasDeref (head :: tail) = false)
    (hnoUnion₁ : placeTouchesUnion localDecls layouts
      { local_ := loc, projection := .unwrapUnsafeBinder ty :: head :: tail } = false)
    (hnoUnion₂ : placeTouchesUnion localDecls layouts
      { local_ := loc, projection := head :: tail } = false) :
    deinitMovedSubPlace locals localDecls layouts loc rootVal
        (.unwrapUnsafeBinder ty :: head :: tail) fieldVal =
      deinitMovedSubPlace locals localDecls layouts loc rootVal (head :: tail) fieldVal := by
  have hnoDeref' : projHasDeref (.unwrapUnsafeBinder ty :: head :: tail) = false := hnoDeref
  simp only [deinitMovedSubPlace, hnoDeref, hnoDeref', hnoUnion₁, hnoUnion₂,
    movedMarkerValue_unwrapUnsafeBinder_prefix, writeProjectedValue]

end TrustedPlaces

/-! ### Concrete `D1`–`D9` canaries on the real Trusted `evalOperand` -/

section TrustedCanaries

/-- `u8` field type (layout index irrelevant without local declarations). -/
def u8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }

/-- A `u8` scalar value. -/
def sc8 (n : Nat) : Value := .scalar { bits := n, sizeBytes := 1 }

/-- Place helper. -/
def pl (l : Local) (proj : List ProjectionElem) : Place := { local_ := l, projection := proj }

/-! #### `D1`: root moves -/

/-- `_1 : u8 = 5`. -/
def d1Locals : List LocalSlot := [.uninit, .init (sc8 5)]

theorem canary_D1_root_move :
    evalOperand d1Locals (.move (pl 1 [])) (deinitProjectedMoves := true) =
      .ok (sc8 5) [.uninit, .uninit] := rfl

theorem canary_D1_root_reread_ub :
    evalOperand [.uninit, .uninit] (.copy (pl 1 [])) (deinitProjectedMoves := true) = .ub := rfl

/-- `_1 : () = ()`: a zero-sized move leaves the source initialized. -/
theorem canary_D1_zst_move_ok :
    evalOperand [.uninit, .init .unit] (.move (pl 1 [])) (deinitProjectedMoves := true) =
      .ok .unit [.uninit, .init .unit] := rfl

theorem canary_D1_zst_reread_ok :
    evalOperand [.uninit, .init .unit] (.copy (pl 1 [])) (deinitProjectedMoves := true) =
      .ok .unit [.uninit, .init .unit] := rfl

/-! #### `D2`/`D3`: field moves and re-initialization -/

/-- `_1 : (u8, u8) = (2, 3)`. -/
def d2Locals : List LocalSlot := [.uninit, .init (.aggregate 0 [sc8 2, sc8 3])]

/-- `_1` after `move _1.0`. -/
def d2AfterMove : List LocalSlot := [.uninit, .init (.aggregate 0 [movedUninitValue, sc8 3])]

theorem canary_D2_field_move :
    evalOperand d2Locals (.move (pl 1 [.field 0 u8Ty])) (deinitProjectedMoves := true) =
      .ok (sc8 2) d2AfterMove := rfl

theorem canary_D2_reread_field_ub :
    evalOperand d2AfterMove (.copy (pl 1 [.field 0 u8Ty])) (deinitProjectedMoves := true) =
      .ub := rfl

theorem canary_D2_remove_field_ub :
    evalOperand d2AfterMove (.move (pl 1 [.field 0 u8Ty])) (deinitProjectedMoves := true) =
      .ub := rfl

theorem canary_D2_reread_whole_ub :
    evalOperand d2AfterMove (.copy (pl 1 [])) (deinitProjectedMoves := true) = .ub := rfl

theorem canary_D2_move_whole_ub :
    evalOperand d2AfterMove (.move (pl 1 [])) (deinitProjectedMoves := true) = .ub := rfl

theorem canary_D2_sibling_ok :
    evalOperand d2AfterMove (.copy (pl 1 [.field 1 u8Ty])) (deinitProjectedMoves := true) =
      .ok (sc8 3) d2AfterMove := rfl

/-- Contrast: the legacy semantics keeps a moved field readable. -/
theorem canary_D2_legacy_keeps_field :
    evalOperand d2Locals (.move (pl 1 [.field 0 u8Ty])) = .ok (sc8 2) d2Locals ∧
    evalOperand d2Locals (.copy (pl 1 [.field 0 u8Ty])) = .ok (sc8 2) d2Locals := ⟨rfl, rfl⟩

/-- `_1.0 = 9` after the move. -/
def d3AfterWrite : List LocalSlot := [.uninit, .init (.aggregate 0 [sc8 9, sc8 3])]

theorem canary_D3_reinit_write :
    writePlaceValue d2AfterMove [] (pl 1 [.field 0 u8Ty]) (sc8 9) = .ok d3AfterWrite := rfl

theorem canary_D3_reinit_reread_ok :
    evalOperand d3AfterWrite (.copy (pl 1 [.field 0 u8Ty])) (deinitProjectedMoves := true) =
      .ok (sc8 9) d3AfterWrite ∧
    evalOperand d3AfterWrite (.copy (pl 1 [])) (deinitProjectedMoves := true) =
      .ok (.aggregate 0 [sc8 9, sc8 3]) d3AfterWrite := ⟨rfl, rfl⟩

/-- Re-initializing the whole local also clears the moved-out state. -/
theorem canary_D3_root_reinit_ok :
    writePlaceValue d2AfterMove [] (pl 1 []) (.aggregate 0 [sc8 7, sc8 8]) =
      .ok [.uninit, .init (.aggregate 0 [sc8 7, sc8 8])] := rfl

/-- `u8` and `()` types for ZST sub-field canaries. -/
def unitTy : Ty := { kind := .tuple .nil, layoutIdx := 0 }

/-- `_1 : (u8, ()) = (7, ())`. -/
def d2ZstTupleLocals : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [sc8 7, .unit])]

def d2ZstTupleAfterMove0 : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [movedUninitValue, .unit])]

/-- **`D2` with a ZST sibling field.** Moving `_1.0` (`u8`) out of `_1 : (u8, ())`
deinitializes `_1.0` (so reading `_1.0` or `_1` faults with `.ub`), while
reading the zero-sized sibling `_1.1` (`()`) still succeeds. -/
theorem canary_D2_zst_subfield_after_nonzst_move :
    evalOperand d2ZstTupleLocals (.move (pl 1 [.field 0 u8Ty]))
      (deinitProjectedMoves := true) = .ok (sc8 7) d2ZstTupleAfterMove0 ∧
    evalOperand d2ZstTupleAfterMove0 (.copy (pl 1 [.field 1 unitTy]))
      (deinitProjectedMoves := true) = .ok .unit d2ZstTupleAfterMove0 ∧
    evalOperand d2ZstTupleAfterMove0 (.copy (pl 1 [.field 0 u8Ty]))
      (deinitProjectedMoves := true) = .ub ∧
    evalOperand d2ZstTupleAfterMove0 (.copy (pl 1 []))
      (deinitProjectedMoves := true) = .ub := ⟨rfl, rfl, rfl, rfl⟩

/-- **`D2` moving a ZST sub-field.** Moving `_1.1` (`()`) out of `_1 : (u8, ())`
leaves `_1` (`(7, ())`) and `_1.0` (`7`) completely valid and initialized. -/
theorem canary_D2_move_zst_subfield_preserves_parent :
    evalOperand d2ZstTupleLocals (.move (pl 1 [.field 1 unitTy]))
      (deinitProjectedMoves := true) = .ok .unit d2ZstTupleLocals ∧
    evalOperand d2ZstTupleLocals (.copy (pl 1 []))
      (deinitProjectedMoves := true) = .ok (.aggregate 0 [sc8 7, .unit]) d2ZstTupleLocals ∧
    evalOperand d2ZstTupleLocals (.copy (pl 1 [.field 0 u8Ty]))
      (deinitProjectedMoves := true) = .ok (sc8 7) d2ZstTupleLocals := ⟨rfl, rfl, rfl⟩

/-- `_1 : ((u8, u8), u8) = ((10, 11), 12)`. -/
def tupU8U8Ty : Ty := { kind := .tuple [.uint .u8, .uint .u8], layoutIdx := 0 }

def d3NestedLocals : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [.aggregate 0 [sc8 10, sc8 11], sc8 12])]

def d3NestedAfterMove0 : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [.aggregate 0 [movedUninitValue, movedUninitValue], sc8 12])]

def d3NestedAfterPartialReinit : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [.aggregate 0 [movedUninitValue, sc8 99], sc8 12])]

def d3NestedAfterFullReinit : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [.aggregate 0 [sc8 88, sc8 99], sc8 12])]

/-- **`D3` nested aggregate move and field-by-field re-initialization.** Moving
`_1.0` out of `_1 : ((u8, u8), u8)` preserves the aggregate spine of `_1.0` with
moved-out leaves, so `_1.0.1 = 99` and `_1.0.0 = 88` can re-initialize `_1.0`
field-by-field. -/
theorem canary_D3_nested_aggregate_move_and_partial_reinit :
    evalOperand d3NestedLocals (.move (pl 1 [.field 0 tupU8U8Ty]))
      (deinitProjectedMoves := true) =
      .ok (.aggregate 0 [sc8 10, sc8 11]) d3NestedAfterMove0 ∧
    writePlaceValue d3NestedAfterMove0 [] (pl 1 [.field 0 tupU8U8Ty, .field 1 u8Ty]) (sc8 99) =
      .ok d3NestedAfterPartialReinit ∧
    evalOperand d3NestedAfterPartialReinit (.copy (pl 1 [.field 0 tupU8U8Ty, .field 1 u8Ty]))
      (deinitProjectedMoves := true) = .ok (sc8 99) d3NestedAfterPartialReinit ∧
    evalOperand d3NestedAfterPartialReinit (.copy (pl 1 [.field 0 tupU8U8Ty]))
      (deinitProjectedMoves := true) = .ub ∧
    writePlaceValue d3NestedAfterPartialReinit []
      (pl 1 [.field 0 tupU8U8Ty, .field 0 u8Ty]) (sc8 88) = .ok d3NestedAfterFullReinit ∧
    evalOperand d3NestedAfterFullReinit (.copy (pl 1 []))
      (deinitProjectedMoves := true) =
      .ok (.aggregate 0 [.aggregate 0 [sc8 88, sc8 99], sc8 12]) d3NestedAfterFullReinit :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! #### `D5`: Tree-Borrows-silent `move (*_2)` -/

/-- `_1 : u8 = 5; _2 = &raw mut _1` (tag `2`, active); `_3 = &_1` (tag `3`, frozen). -/
def d5Locals : List LocalSlot :=
  [.uninit, .init (sc8 5),
    .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
    .init (.ptr { allocId := 3, offsetBytes := 0 } 8)]

/-- Borrow table of `d5Locals`. -/
def d5Borrows : List BorrowEntry :=
  [{ tag := 2, targetLocal := 1, targetProjection := [], perm := .active },
   { tag := 3, targetLocal := 1, targetProjection := [], perm := .frozen }]

/-- After `move (*_2)`: `_1` is deinitialized; nothing else changes. -/
def d5AfterMove : List LocalSlot :=
  [.uninit, .uninit,
    .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
    .init (.ptr { allocId := 3, offsetBytes := 0 } 8)]

theorem canary_D5_deref_move_delivers_value :
    evalOperand d5Locals (.move (pl 2 [.deref])) d5Borrows (deinitProjectedMoves := true) =
      .ok (sc8 5) d5AfterMove := rfl

/-- The sibling shared borrow `_3` is still `Frozen` (a move never writes the
borrow table), and reading through it now faults on the uninitialized target,
whereas before the move the same read succeeds. -/
theorem canary_D5_sibling_frozen_reads_uninit :
    lookupBorrow d5Borrows 3 =
      .some { tag := 3, targetLocal := 1, targetProjection := [], perm := .frozen } ∧
    evalOperand d5Locals (.copy (pl 3 [.deref])) d5Borrows (deinitProjectedMoves := true) =
      .ok (sc8 5) d5Locals ∧
    evalOperand d5AfterMove (.copy (pl 3 [.deref])) d5Borrows (deinitProjectedMoves := true) =
      .ub ∧
    evalOperand d5AfterMove (.copy (pl 2 [.deref])) d5Borrows (deinitProjectedMoves := true) =
      .ub := ⟨rfl, rfl, rfl, rfl⟩

/-- Contrast: a disabled tag faults even before the move (the `.ub` above is the
uninitialized target, not a Tree Borrows failure). -/
theorem canary_D5_disabled_contrast :
    evalOperand d5Locals (.copy (pl 3 [.deref]))
      [{ tag := 2, targetLocal := 1, targetProjection := [], perm := .active },
       { tag := 3, targetLocal := 1, targetProjection := [], perm := .disabled }]
      (deinitProjectedMoves := true) = .ub := rfl

/-- Contrast: the legacy semantics does not deinitialize the `Deref` target. -/
theorem canary_D5_legacy_keeps_target :
    evalOperand d5Locals (.move (pl 2 [.deref])) d5Borrows = .ok (sc8 5) d5Locals := rfl

/-- Typed local declarations for `_1 : (u8, u8)` and `_2 : *mut u8` pointing at
byte offset `1` of `_1` (`_1.1`), with `_3 : &u8` frozen borrow on `_1.1`. -/
def d5TypedTupleLayouts : LayoutTable :=
  { emptyLayoutTable with
    entries :=
      [{ size := ⟨1⟩, align := ⟨1⟩, backendRepr := .memory, fields := .primitive,
         variants := .single 0, isUninhabited := false, fieldLayouts := [] },
       { size := ⟨2⟩, align := ⟨1⟩, backendRepr := .memory,
         fields := .arbitrary [⟨0⟩, ⟨1⟩] [0, 1], variants := .single 0,
         isUninhabited := false, fieldLayouts := [0, 0] }] }

def d5TypedTupleDecls : List LocalDecl :=
  [{ mutability := .mut, ty := u8Ty, debugName := .none },
   { mutability := .mut, ty := { kind := .tuple [.uint .u8, .uint .u8], layoutIdx := 1 },
     debugName := .none },
   { mutability := .mut, ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 },
     debugName := .none },
   { mutability := .not, ty := { kind := .ref .not (.uint .u8), layoutIdx := 0 },
     debugName := .none }]

def d5TypedTupleLocals : List LocalSlot :=
  [.uninit,
   .init (.aggregate 0 [sc8 2, sc8 3]),
   .init (.ptr { allocId := 2, offsetBytes := 1 } 8),
   .init (.ptr { allocId := 3, offsetBytes := 1 } 8)]

def d5TypedTupleAfterMove : List LocalSlot :=
  [.uninit,
   .init (.aggregate 0 [sc8 2, movedUninitValue]),
   .init (.ptr { allocId := 2, offsetBytes := 1 } 8),
   .init (.ptr { allocId := 3, offsetBytes := 1 } 8)]

/-- **`D5` typed byte-offset `Deref` move into a tuple (`localDecls ≠ .nil`).**
When `_2 : *mut u8` points at byte offset `1` of `_1 : (u8, u8) = (2, 3)`,
`move (*_2)` delivers `3`, deinitializes `_1.1` while keeping `_1.0 = 2`
readable, and leaves the sibling `.frozen` borrow `_3` intact. -/
theorem canary_D5_typed_field_offset_deref_move :
    evalOperand d5TypedTupleLocals (.move (pl 2 [.deref])) d5Borrows []
      d5TypedTupleLayouts [] d5TypedTupleDecls [] true =
      .ok (sc8 3) d5TypedTupleAfterMove ∧
    evalOperand d5TypedTupleAfterMove (.copy (pl 1 [.field 0 u8Ty])) d5Borrows []
      d5TypedTupleLayouts [] d5TypedTupleDecls [] true =
      .ok (sc8 2) d5TypedTupleAfterMove ∧
    evalOperand d5TypedTupleAfterMove (.copy (pl 3 [.deref])) d5Borrows []
      d5TypedTupleLayouts [] d5TypedTupleDecls [] true = .ub := ⟨rfl, rfl, rfl⟩

/-- Typed local declarations for `_1 : u16 = 0x0302` and `_2 : *mut u8` pointing
at byte offset `1` inside `_1`. -/
def d5TypedScalarDecls : List LocalDecl :=
  [{ mutability := .mut, ty := u8Ty, debugName := .none },
   { mutability := .mut, ty := { kind := .uint .u16, layoutIdx := 0 }, debugName := .none },
   { mutability := .mut, ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 },
     debugName := .none }]

def d5TypedScalarLocals : List LocalSlot :=
  [.uninit,
   .init (.scalar { bits := 770, sizeBytes := 2 }),
   .init (.ptr { allocId := 2, offsetBytes := 1 } 8)]

def d5TypedScalarAfterMove : List LocalSlot :=
  [.uninit,
   .init movedUninitValue,
   .init (.ptr { allocId := 2, offsetBytes := 1 } 8)]

/-- **`D5` typed intra-scalar byte-window `Deref` move (`localDecls ≠ .nil`).**
Moving a `u8` at byte offset `1` out of `_1 : u16 = 0x0302` (`770`) delivers the
high byte `3` and marks `_1` as moved-out so subsequent reads of `_1` or `*_2`
fault with `.ub`. -/
theorem canary_D5_typed_scalar_byte_window_deref_move :
    evalOperand d5TypedScalarLocals (.move (pl 2 [.deref])) d5Borrows []
      emptyLayoutTable [] d5TypedScalarDecls [] true =
      .ok (sc8 3) d5TypedScalarAfterMove ∧
    evalOperand d5TypedScalarAfterMove (.copy (pl 1 [])) d5Borrows []
      emptyLayoutTable [] d5TypedScalarDecls [] true = .ub ∧
    evalOperand d5TypedScalarAfterMove (.copy (pl 2 [.deref])) d5Borrows []
      emptyLayoutTable [] d5TypedScalarDecls [] true = .ub := ⟨rfl, rfl, rfl⟩

/-! #### `D9`: element and subslice moves -/

/-- `_1 : [u8; 4] = [10, 11, 12, 13]`, `_2 : usize = 1`. -/
def d9Locals : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [sc8 10, sc8 11, sc8 12, sc8 13]),
    .init (.scalar { bits := 1, sizeBytes := 8 })]

def d9AfterElem : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [sc8 10, movedUninitValue, sc8 12, sc8 13]),
    .init (.scalar { bits := 1, sizeBytes := 8 })]

theorem canary_D9_constIndex_move :
    evalOperand d9Locals (.move (pl 1 [.constantIndex 1 4 false]))
      (deinitProjectedMoves := true) = .ok (sc8 11) d9AfterElem := rfl

theorem canary_D9_index_move :
    evalOperand d9Locals (.move (pl 1 [.index 2])) (deinitProjectedMoves := true) =
      .ok (sc8 11) d9AfterElem := rfl

theorem canary_D9_elem_neighbors_ok :
    evalOperand d9AfterElem (.copy (pl 1 [.constantIndex 0 4 false]))
      (deinitProjectedMoves := true) = .ok (sc8 10) d9AfterElem ∧
    evalOperand d9AfterElem (.copy (pl 1 [.constantIndex 3 4 false]))
      (deinitProjectedMoves := true) = .ok (sc8 13) d9AfterElem ∧
    evalOperand d9AfterElem (.copy (pl 1 [.constantIndex 1 4 false]))
      (deinitProjectedMoves := true) = .ub ∧
    evalOperand d9AfterElem (.copy (pl 1 [])) (deinitProjectedMoves := true) = .ub :=
  ⟨rfl, rfl, rfl, rfl⟩

def d9AfterSubslice : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [sc8 10, movedUninitValue, movedUninitValue, sc8 13]),
    .init (.scalar { bits := 1, sizeBytes := 8 })]

theorem canary_D9_subslice_move :
    evalOperand d9Locals (.move (pl 1 [.subslice 1 3 false])) (deinitProjectedMoves := true) =
      .ok (.aggregate 0 [sc8 11, sc8 12]) d9AfterSubslice := rfl

theorem canary_D9_subslice_window :
    evalOperand d9AfterSubslice (.copy (pl 1 [.constantIndex 0 4 false]))
      (deinitProjectedMoves := true) = .ok (sc8 10) d9AfterSubslice ∧
    evalOperand d9AfterSubslice (.copy (pl 1 [.constantIndex 3 4 false]))
      (deinitProjectedMoves := true) = .ok (sc8 13) d9AfterSubslice ∧
    evalOperand d9AfterSubslice (.copy (pl 1 [.constantIndex 1 4 false]))
      (deinitProjectedMoves := true) = .ub ∧
    evalOperand d9AfterSubslice (.copy (pl 1 [.constantIndex 2 4 false]))
      (deinitProjectedMoves := true) = .ub := ⟨rfl, rfl, rfl, rfl⟩

/-- `from_end` subslices (`_1[1..len-1]`) deinitialize the same window. -/
theorem canary_D9_subslice_fromEnd_move :
    evalOperand d9Locals (.move (pl 1 [.subslice 1 1 true])) (deinitProjectedMoves := true) =
      .ok (.aggregate 0 [sc8 11, sc8 12]) d9AfterSubslice := rfl

/-- Contrast: the legacy semantics keeps moved elements readable. -/
theorem canary_D9_legacy_keeps_elems :
    evalOperand d9Locals (.move (pl 1 [.subslice 1 3 false])) =
      .ok (.aggregate 0 [sc8 11, sc8 12]) d9Locals := rfl

/-! #### `evalOperands`: `move _1` followed by `copy _1` in one operand list -/

theorem canary_evalOperands_move_then_copy_ub :
    evalOperands d1Locals [.move (pl 1 []), .copy (pl 1 [])] (deinitProjectedMoves := true) =
      .ub := rfl

/-- **`D4` on the Trusted side.** `[copy _1, move _1]` delivers `5` twice and then
deinitializes `_1` (the copy is read before the move), whereas `[move _1, move _1]`
faults on the second operand: the operand-list counterpart of the `lean-miri`
`D4` runs of the real `evalRvalueIntoPlace` (`canary_D4_mem_binaryOp`). -/
theorem canary_evalOperands_D4_copy_then_move_ok_move_then_move_ub :
    evalOperands d1Locals [.copy (pl 1 []), .move (pl 1 [])] (deinitProjectedMoves := true) =
      .ok [sc8 5, sc8 5] [.uninit, .uninit] ∧
    evalOperands d1Locals [.move (pl 1 []), .move (pl 1 [])] (deinitProjectedMoves := true) =
      .ub := ⟨rfl, rfl⟩

theorem canary_evalOperands_field_move_then_sibling_ok :
    evalOperands d2Locals [.move (pl 1 [.field 0 u8Ty]), .copy (pl 1 [.field 1 u8Ty])]
      (deinitProjectedMoves := true) = .ok [sc8 2, sc8 3] d2AfterMove := rfl

theorem canary_evalOperands_field_move_then_whole_ub :
    evalOperands d2Locals [.move (pl 1 [.field 0 u8Ty]), .copy (pl 1 [])]
      (deinitProjectedMoves := true) = .ub := rfl

/-- **`D6` field swap via `evalOperands ... (deinitProjectedMoves := true)`.**
Evaluating `[move _1.1, move _1.0]` on `_1 = (2, 3)` yields `[3, 2]` and marks
both fields moved-out; writing `(3, 2)` back to `_1` completes the swap. -/
theorem canary_D6_evalOperands_field_swap :
    evalOperands d2Locals [.move (pl 1 [.field 1 u8Ty]), .move (pl 1 [.field 0 u8Ty])]
      (deinitProjectedMoves := true) =
      .ok [sc8 3, sc8 2]
        [.uninit, .init (.aggregate 0 [movedUninitValue, movedUninitValue])] ∧
    writePlaceValue
      [.uninit, .init (.aggregate 0 [movedUninitValue, movedUninitValue])]
      [] (pl 1 []) (.aggregate 0 [sc8 3, sc8 2]) =
      .ok [.uninit, .init (.aggregate 0 [sc8 3, sc8 2])] := ⟨rfl, rfl⟩

/-- **`D6` self-aggregate field swap (`_1 = (move _1.1, move _1.0)`) and same-list
move/copy combinations on the real `Places.evalOperands`.**
1. First `.move _1.1` reads `3` and marks `_1.1` uninit while leaving `_1.0 = 2`
   intact; second `.move _1.0` reads `2` and marks `_1.0` uninit; writing
   `.aggregate 0 [sc8 3, sc8 2]` to `_1` re-initializes `_1` so reading `_1`,
   `_1.0`, and `_1.1` in `deinitProjectedMoves` mode returns `(3, 2)`, `3`, and
   `2`.
2. In a single `evalOperands` list: `[.move _1, .copy _1]` faults with `.ub`,
   `[.copy _1, .move _1]` succeeds (`D4`), `[.move _1.0, .copy _1.0]` faults with
   `.ub`, and `[.move _1.0, .copy _1.1]` succeeds. -/
theorem canary_D6_field_swap_self_aggregate_ok :
    evalOperand d2Locals (.move (pl 1 [.field 1 u8Ty])) (deinitProjectedMoves := true) =
      .ok (sc8 3) [.uninit, .init (.aggregate 0 [sc8 2, movedUninitValue])] ∧
    evalOperand [.uninit, .init (.aggregate 0 [sc8 2, movedUninitValue])]
      (.move (pl 1 [.field 0 u8Ty])) (deinitProjectedMoves := true) =
      .ok (sc8 2) [.uninit, .init (.aggregate 0 [movedUninitValue, movedUninitValue])] ∧
    evalOperands d2Locals [.move (pl 1 [.field 1 u8Ty]), .move (pl 1 [.field 0 u8Ty])]
      (deinitProjectedMoves := true) =
      .ok [sc8 3, sc8 2]
        [.uninit, .init (.aggregate 0 [movedUninitValue, movedUninitValue])] ∧
    writePlaceValue
      [.uninit, .init (.aggregate 0 [movedUninitValue, movedUninitValue])]
      [] (pl 1 []) (.aggregate 0 [sc8 3, sc8 2]) =
      .ok [.uninit, .init (.aggregate 0 [sc8 3, sc8 2])] ∧
    evalOperand [.uninit, .init (.aggregate 0 [sc8 3, sc8 2])] (.copy (pl 1 []))
      (deinitProjectedMoves := true) =
      .ok (.aggregate 0 [sc8 3, sc8 2]) [.uninit, .init (.aggregate 0 [sc8 3, sc8 2])] ∧
    evalOperand [.uninit, .init (.aggregate 0 [sc8 3, sc8 2])] (.copy (pl 1 [.field 0 u8Ty]))
      (deinitProjectedMoves := true) =
      .ok (sc8 3) [.uninit, .init (.aggregate 0 [sc8 3, sc8 2])] ∧
    evalOperand [.uninit, .init (.aggregate 0 [sc8 3, sc8 2])] (.copy (pl 1 [.field 1 u8Ty]))
      (deinitProjectedMoves := true) =
      .ok (sc8 2) [.uninit, .init (.aggregate 0 [sc8 3, sc8 2])] ∧
    evalOperands d1Locals [.move (pl 1 []), .copy (pl 1 [])] (deinitProjectedMoves := true) = .ub ∧
    evalOperands d1Locals [.copy (pl 1 []), .move (pl 1 [])] (deinitProjectedMoves := true) =
      .ok [sc8 5, sc8 5] [.uninit, .uninit] ∧
    evalOperands d2Locals [.move (pl 1 [.field 0 u8Ty]), .copy (pl 1 [.field 0 u8Ty])]
      (deinitProjectedMoves := true) = .ub ∧
    evalOperands d2Locals [.move (pl 1 [.field 0 u8Ty]), .copy (pl 1 [.field 1 u8Ty])]
      (deinitProjectedMoves := true) = .ok [sc8 2, sc8 3] d2AfterMove :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `d5TypedTupleAfterMove` after re-initializing `_1.1 = 99`. -/
def d5TypedTupleAfterReinit : List LocalSlot :=
  [.uninit,
   .init (.aggregate 0 [sc8 2, sc8 99]),
   .init (.ptr { allocId := 2, offsetBytes := 1 } 8),
   .init (.ptr { allocId := 3, offsetBytes := 1 } 8)]

/-- **`D3` write-back / re-initialization completeness (projected field write,
root assignment, and typed pointer dereference write `*_2 = 99`).** After moving
`_1.1` out of `_1 : (u8, u8) = (2, 3)` (`d5TypedTupleAfterMove`), re-initializing
via `_1.1 = 99`, `_1 = (2, 99)`, or `*_2 = 99` (where `_2 : *mut u8` points at
byte offset `1` of `_1`) all succeed and produce `d5TypedTupleAfterReinit`, where
`valueContainsMovedUninit` is `false` on both `_1` and `_1.1` and subsequent
reads of `_1`, `_1.1`, `*_2`, and `*_3` all succeed. -/
theorem canary_D3_typed_deref_reinit_after_field_move :
    writePlaceValue d5TypedTupleAfterMove d5Borrows (pl 1 [.field 1 u8Ty]) (sc8 99)
      d5TypedTupleDecls d5TypedTupleLayouts = .ok d5TypedTupleAfterReinit ∧
    writePlaceValue d5TypedTupleAfterMove d5Borrows (pl 1 []) (.aggregate 0 [sc8 2, sc8 99])
      d5TypedTupleDecls d5TypedTupleLayouts = .ok d5TypedTupleAfterReinit ∧
    writePlaceValue d5TypedTupleAfterMove d5Borrows (pl 2 [.deref]) (sc8 99)
      d5TypedTupleDecls d5TypedTupleLayouts = .ok d5TypedTupleAfterReinit ∧
    valueContainsMovedUninit (.aggregate 0 [sc8 2, sc8 99]) = false ∧
    valueContainsMovedUninit (sc8 99) = false ∧
    evalOperand d5TypedTupleAfterReinit (.copy (pl 1 [])) d5Borrows []
      d5TypedTupleLayouts [] d5TypedTupleDecls [] true =
      .ok (.aggregate 0 [sc8 2, sc8 99]) d5TypedTupleAfterReinit ∧
    evalOperand d5TypedTupleAfterReinit (.copy (pl 1 [.field 1 u8Ty])) d5Borrows []
      d5TypedTupleLayouts [] d5TypedTupleDecls [] true =
      .ok (sc8 99) d5TypedTupleAfterReinit ∧
    evalOperand d5TypedTupleAfterReinit (.copy (pl 2 [.deref])) d5Borrows []
      d5TypedTupleLayouts [] d5TypedTupleDecls [] true =
      .ok (sc8 99) d5TypedTupleAfterReinit ∧
    evalOperand d5TypedTupleAfterReinit (.copy (pl 3 [.deref])) d5Borrows []
      d5TypedTupleLayouts [] d5TypedTupleDecls [] true =
      .ok (sc8 99) d5TypedTupleAfterReinit :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `d9AfterSubslice` after re-initializing only `_1[1] = 50` (`_1[2]` still moved-out). -/
def d9AfterHalfReinit : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [sc8 10, sc8 50, movedUninitValue, sc8 13]),
    .init (.scalar { bits := 1, sizeBytes := 8 })]

/-- `d9AfterSubslice` after completing re-initialization with `_1[2] = 60`. -/
def d9AfterFullReinit : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [sc8 10, sc8 50, sc8 60, sc8 13]),
    .init (.scalar { bits := 1, sizeBytes := 8 })]

/-- **`D3`/`D9` partial-then-full subslice re-initialization.** After
`move _1[1..3]` on `_1 : [u8; 4] = [10, 11, 12, 13]` (`d9AfterSubslice`):
1. Writing `_1[1] = 50` re-initializes only element `1`: reading `_1[1]` now
   succeeds with `50` (and `_1[0] = 10`, `_1[3] = 13`), while reading `_1[2]`,
   the subslice `_1[1..3]`, or the whole array `_1` still faults with `.ub`.
2. Writing `_1[2] = 60` (or assigning `_1[1..3] = [50, 60]` directly) completes
   re-initialization so `_1[2]`, `_1[1..3]`, and `_1` are all readable again. -/
theorem canary_D3_subslice_partial_then_full_reinit :
    writePlaceValue d9AfterSubslice [] (pl 1 [.constantIndex 1 4 false]) (sc8 50) =
      .ok d9AfterHalfReinit ∧
    evalOperand d9AfterHalfReinit (.copy (pl 1 [.constantIndex 1 4 false]))
      (deinitProjectedMoves := true) = .ok (sc8 50) d9AfterHalfReinit ∧
    evalOperand d9AfterHalfReinit (.copy (pl 1 [.constantIndex 0 4 false]))
      (deinitProjectedMoves := true) = .ok (sc8 10) d9AfterHalfReinit ∧
    evalOperand d9AfterHalfReinit (.copy (pl 1 [.constantIndex 3 4 false]))
      (deinitProjectedMoves := true) = .ok (sc8 13) d9AfterHalfReinit ∧
    evalOperand d9AfterHalfReinit (.copy (pl 1 [.constantIndex 2 4 false]))
      (deinitProjectedMoves := true) = .ub ∧
    evalOperand d9AfterHalfReinit (.copy (pl 1 [.subslice 1 3 false]))
      (deinitProjectedMoves := true) = .ub ∧
    evalOperand d9AfterHalfReinit (.copy (pl 1 []))
      (deinitProjectedMoves := true) = .ub ∧
    writePlaceValue d9AfterHalfReinit [] (pl 1 [.constantIndex 2 4 false]) (sc8 60) =
      .ok d9AfterFullReinit ∧
    writePlaceValue d9AfterSubslice [] (pl 1 [.subslice 1 3 false])
      (.aggregate 0 [sc8 50, sc8 60]) = .ok d9AfterFullReinit ∧
    valueContainsMovedUninit (.aggregate 0 [sc8 10, sc8 50, sc8 60, sc8 13]) = false ∧
    evalOperand d9AfterFullReinit (.copy (pl 1 [.constantIndex 2 4 false]))
      (deinitProjectedMoves := true) = .ok (sc8 60) d9AfterFullReinit ∧
    evalOperand d9AfterFullReinit (.copy (pl 1 [.subslice 1 3 false]))
      (deinitProjectedMoves := true) =
      .ok (.aggregate 0 [sc8 50, sc8 60]) d9AfterFullReinit ∧
    evalOperand d9AfterFullReinit (.copy (pl 1 []))
      (deinitProjectedMoves := true) =
      .ok (.aggregate 0 [sc8 10, sc8 50, sc8 60, sc8 13]) d9AfterFullReinit :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `_1 : [u8; 4] = [10, 11, 12, 13]` and `_2 : *mut [u8]` slice fat pointer
(`.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0 } 8, .scalar { bits := 4, sizeBytes := 8 }]`). -/
def d9SliceFatPtrLocals : List LocalSlot :=
  [.uninit,
   .init (.aggregate 0 [sc8 10, sc8 11, sc8 12, sc8 13]),
   .init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0 } 8,
     .scalar { bits := 4, sizeBytes := 8 }])]

def d9SliceFatPtrAfterElem : List LocalSlot :=
  [.uninit,
   .init (.aggregate 0 [sc8 10, movedUninitValue, sc8 12, sc8 13]),
   .init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0 } 8,
     .scalar { bits := 4, sizeBytes := 8 }])]

def d9SliceFatPtrAfterSubslice : List LocalSlot :=
  [.uninit,
   .init (.aggregate 0 [sc8 10, movedUninitValue, movedUninitValue, sc8 13]),
   .init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0 } 8,
     .scalar { bits := 4, sizeBytes := 8 }])]

/-- **`D9` slice fat-pointer element move (`move (*_2)[1]`).** Deinitializes
`_1[1]` while preserving `_1[0] = 10`, `_1[2] = 12`, `_1[3] = 13` and sibling
frozen borrows. -/
theorem canary_D9_slice_fat_ptr_elem_move :
    evalOperand d9SliceFatPtrLocals (.move (pl 2 [.deref, .constantIndex 1 4 false]))
      d5Borrows (deinitProjectedMoves := true) =
      .ok (sc8 11) d9SliceFatPtrAfterElem ∧
    evalOperand d9SliceFatPtrAfterElem (.copy (pl 2 [.deref, .constantIndex 0 4 false]))
      d5Borrows (deinitProjectedMoves := true) = .ok (sc8 10) d9SliceFatPtrAfterElem ∧
    evalOperand d9SliceFatPtrAfterElem (.copy (pl 2 [.deref, .constantIndex 2 4 false]))
      d5Borrows (deinitProjectedMoves := true) = .ok (sc8 12) d9SliceFatPtrAfterElem ∧
    evalOperand d9SliceFatPtrAfterElem (.copy (pl 2 [.deref, .constantIndex 3 4 false]))
      d5Borrows (deinitProjectedMoves := true) = .ok (sc8 13) d9SliceFatPtrAfterElem ∧
    evalOperand d9SliceFatPtrAfterElem (.copy (pl 2 [.deref, .constantIndex 1 4 false]))
      d5Borrows (deinitProjectedMoves := true) = .ub := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **`D9` slice fat-pointer subslice move (`move (*_2)[1..3]`) & index stability.**
Moving the 2-element window `(*_2)[1..3]` replaces `[11, 12]` element-wise with
`[movedUninitValue, movedUninitValue]` (keeping the 4-element array length
invariant), so `_1[0] = 10` and `_1[3] = 13` remain at their exact indices while
`_1[1]` and `_1[2]` fault with `.ub`. -/
theorem canary_D9_slice_fat_ptr_subslice_move :
    evalOperand d9SliceFatPtrLocals (.move (pl 2 [.deref, .subslice 1 3 false]))
      d5Borrows (deinitProjectedMoves := true) =
      .ok (.aggregate 0 [sc8 11, sc8 12]) d9SliceFatPtrAfterSubslice ∧
    evalOperand d9SliceFatPtrAfterSubslice (.copy (pl 1 [.constantIndex 0 4 false]))
      d5Borrows (deinitProjectedMoves := true) = .ok (sc8 10) d9SliceFatPtrAfterSubslice ∧
    evalOperand d9SliceFatPtrAfterSubslice (.copy (pl 1 [.constantIndex 1 4 false]))
      d5Borrows (deinitProjectedMoves := true) = .ub ∧
    evalOperand d9SliceFatPtrAfterSubslice (.copy (pl 1 [.constantIndex 2 4 false]))
      d5Borrows (deinitProjectedMoves := true) = .ub ∧
    evalOperand d9SliceFatPtrAfterSubslice (.copy (pl 1 [.constantIndex 3 4 false]))
      d5Borrows (deinitProjectedMoves := true) = .ok (sc8 13) d9SliceFatPtrAfterSubslice :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `_1 : [u8; 4] = [movedUninitValue, 11, 12, 13]` (after `move _1[0]`) and
`_2 : *mut [u8]` slice fat pointer at `offsetBytes = 1`, `len = 2` (`&mut _1[1..3]`). -/
def d9OffsetSliceAfterElem0Move : List LocalSlot :=
  [.uninit,
   .init (.aggregate 0 [movedUninitValue, sc8 11, sc8 12, sc8 13]),
   .init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 1 } 8,
     .scalar { bits := 2, sizeBytes := 8 }])]

/-- **`D9` offset slice fat-pointer access after element `0` was moved.** Even
when `_1[0]` holds `movedUninitValue` (`sizeBytes = 0`), `inferElemListByteStride`
skips the moved-out sentinel and infers the `1`-byte element stride from the
remaining elements, so a slice fat pointer at `offsetBytes = 1, len = 2`
(`_1[1..3]`) still reads `(*_2)[0] = 11` and re-initializes `(*_2)[0] = 77`. -/
theorem canary_D9_slice_fat_ptr_offset_after_elem0_move :
    inferElemListByteStride [movedUninitValue, sc8 11, sc8 12, sc8 13] = 1 ∧
    evalOperand d9OffsetSliceAfterElem0Move (.copy (pl 2 [.deref, .constantIndex 0 2 false]))
      d5Borrows (deinitProjectedMoves := true) =
      .ok (sc8 11) d9OffsetSliceAfterElem0Move ∧
    writePlaceValue d9OffsetSliceAfterElem0Move d5Borrows
      (pl 2 [.deref, .constantIndex 0 2 false]) (sc8 77) =
      .ok [.uninit,
           .init (.aggregate 0 [movedUninitValue, sc8 77, sc8 12, sc8 13]),
           .init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 1 } 8,
             .scalar { bits := 2, sizeBytes := 8 }])] :=
  ⟨rfl, rfl, rfl⟩

/-! #### `ep1-A1`: nested, downcast, thin-pointer subslice and union moves -/

/-- `[u8; 3]` field annotation. -/
def arr3Ty : Ty := { kind := .array (.uint .u8) 3, layoutIdx := 0 }

/-- `_1 : ([u8; 3], u8) = ([1, 2, 3], 4)`. -/
def dNestLocals : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [.aggregate 0 [sc8 1, sc8 2, sc8 3], sc8 4])]

/-- `_1` after `move _1.0[1]`. -/
def dNestAfterMove : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [.aggregate 0 [sc8 1, movedUninitValue, sc8 3], sc8 4])]

/-- `_1` after `_1.0[1] = 9`. -/
def dNestReinit : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [.aggregate 0 [sc8 1, sc8 9, sc8 3], sc8 4])]

/-- **`D2`/`D3` nested field-then-element move `move _1.0[1]`.** Only the moved
element of the array field is marked; its array neighbours and the sibling field
stay readable, the enclosing array field and `_1` fault, and writing the element
back re-initializes the whole local. -/
theorem canary_D2_nested_field_elem_move :
    evalOperand dNestLocals (.move (pl 1 [.field 0 arr3Ty, .constantIndex 1 3 false]))
      (deinitProjectedMoves := true) = .ok (sc8 2) dNestAfterMove ∧
    evalOperand dNestAfterMove (.copy (pl 1 [.field 0 arr3Ty, .constantIndex 0 3 false]))
      (deinitProjectedMoves := true) = .ok (sc8 1) dNestAfterMove ∧
    evalOperand dNestAfterMove (.copy (pl 1 [.field 0 arr3Ty, .constantIndex 2 3 false]))
      (deinitProjectedMoves := true) = .ok (sc8 3) dNestAfterMove ∧
    evalOperand dNestAfterMove (.copy (pl 1 [.field 1 u8Ty]))
      (deinitProjectedMoves := true) = .ok (sc8 4) dNestAfterMove ∧
    evalOperand dNestAfterMove (.copy (pl 1 [.field 0 arr3Ty, .constantIndex 1 3 false]))
      (deinitProjectedMoves := true) = .ub ∧
    evalOperand dNestAfterMove (.copy (pl 1 [.field 0 arr3Ty]))
      (deinitProjectedMoves := true) = .ub ∧
    evalOperand dNestAfterMove (.copy (pl 1 [])) (deinitProjectedMoves := true) = .ub ∧
    writePlaceValue dNestAfterMove [] (pl 1 [.field 0 arr3Ty, .constantIndex 1 3 false]) (sc8 9) =
      .ok dNestReinit ∧
    evalOperand dNestReinit (.copy (pl 1 [])) (deinitProjectedMoves := true) =
      .ok (.aggregate 0 [.aggregate 0 [sc8 1, sc8 9, sc8 3], sc8 4]) dNestReinit :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `_1 : Option<u8> = Some(5)` (variant `1`). -/
def dEnumLocals : List LocalSlot := [.uninit, .init (.aggregate 1 [sc8 5])]

/-- `_1` after `move (_1 as Some).0`. -/
def dEnumAfterMove : List LocalSlot := [.uninit, .init (.aggregate 1 [movedUninitValue])]

/-- **`D2` enum downcast field move `move (_1 as Some).0`.** The payload is marked
inside the variant (the variant index is kept), so re-reading the payload or the
whole enum faults, writing the payload re-initializes it, and the legacy
semantics keeps the payload. A discriminant read through this mode's
`Operand.copy` of the whole enum also faults (unlike the statement semantics'
`Rvalue.discriminant`, which reads with the default `false`:
`canary_D2_enum_downcast_discriminant_after_move`). -/
theorem canary_D2_enum_downcast_field_move :
    evalOperand dEnumLocals (.move (pl 1 [.downcast (.some "Some") 1, .field 0 u8Ty]))
      (deinitProjectedMoves := true) = .ok (sc8 5) dEnumAfterMove ∧
    evalOperand dEnumAfterMove (.copy (pl 1 [.downcast (.some "Some") 1, .field 0 u8Ty]))
      (deinitProjectedMoves := true) = .ub ∧
    evalOperand dEnumAfterMove (.copy (pl 1 [])) (deinitProjectedMoves := true) = .ub ∧
    writePlaceValue dEnumAfterMove [] (pl 1 [.downcast (.some "Some") 1, .field 0 u8Ty]) (sc8 7) =
      .ok [.uninit, .init (.aggregate 1 [sc8 7])] ∧
    evalOperand dEnumLocals (.move (pl 1 [.downcast (.some "Some") 1, .field 0 u8Ty])) =
      .ok (sc8 5) dEnumLocals :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **`discriminant(_1)` after `move (_1 as Some).0`.** Drop elaboration reads the
discriminant of a partially moved enum (`open_drop_for_multivariant`). The
statement semantics' `Rvalue.discriminant` reads the place with the default
`deinitProjectedMoves := false`, so after a consumer-side payload move it still
returns the kept variant index `1`, exactly as before the move. That read is
marker-tolerant by design: a `false` read does not detect moved-out markers at
all, so the plain statement-level `Rvalue.use (copy (_1 as Some).0)` returns the
marker itself as a value. The statement semantics never creates markers (it never
passes `true`); a consumer that enables the flag must therefore enable it for
every operand read except this discriminant read. -/
theorem canary_D2_enum_downcast_discriminant_after_move :
    evalRvalue dEnumLocals (.discriminant (pl 1 [])) =
      .ok (.scalar ⟨1, 8⟩) dEnumLocals emptyMemory ∧
    evalRvalue dEnumAfterMove (.discriminant (pl 1 [])) =
      .ok (.scalar ⟨1, 8⟩) dEnumAfterMove emptyMemory ∧
    evalRvalue dEnumAfterMove (.use (.copy (pl 1 [.downcast (.some "Some") 1, .field 0 u8Ty]))) =
      .ok movedUninitValue dEnumAfterMove emptyMemory :=
  ⟨rfl, rfl, rfl⟩

/-- `_1 : [u8; 4] = [10, 11, 12, 13]` and the thin pointer `_2 = &raw mut _1`
(tag `2`, active). -/
def dThinLocals : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [sc8 10, sc8 11, sc8 12, sc8 13]),
    .init (.ptr { allocId := 2, offsetBytes := 0 } 8)]

/-- After `move (*_2)[1..3]`. -/
def dThinAfter : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [sc8 10, movedUninitValue, movedUninitValue, sc8 13]),
    .init (.ptr { allocId := 2, offsetBytes := 0 } 8)]

/-- **`D9` thin-pointer `Deref` + subslice move `move (*_2)[1..3]`.** The window
of the active-frame target `_1` is marked element-wise, keeping the array length
and the neighbours `_1[0]`/`_1[3]` readable through the pointer. -/
theorem canary_D9_thin_ptr_deref_subslice_move :
    evalOperand dThinLocals (.move (pl 2 [.deref, .subslice 1 3 false])) d5Borrows
      (deinitProjectedMoves := true) = .ok (.aggregate 0 [sc8 11, sc8 12]) dThinAfter ∧
    evalOperand dThinAfter (.copy (pl 2 [.deref, .constantIndex 0 4 false])) d5Borrows
      (deinitProjectedMoves := true) = .ok (sc8 10) dThinAfter ∧
    evalOperand dThinAfter (.copy (pl 2 [.deref, .constantIndex 3 4 false])) d5Borrows
      (deinitProjectedMoves := true) = .ok (sc8 13) dThinAfter ∧
    evalOperand dThinAfter (.copy (pl 2 [.deref, .constantIndex 1 4 false])) d5Borrows
      (deinitProjectedMoves := true) = .ub ∧
    evalOperand dThinAfter (.copy (pl 1 [])) d5Borrows (deinitProjectedMoves := true) = .ub :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `u8` layout of the union canary. -/
def d3UnionU8Layout : TypeLayout :=
  { size := { bytes := 1 }, align := { bytes := 1 },
    backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 255 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- `u16` layout of the union canary. -/
def d3UnionU16Layout : TypeLayout :=
  { size := { bytes := 2 }, align := { bytes := 2 },
    backendRepr := .scalar (.initialized (.int 16 false) { start := 0, end_ := 65535 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- `union U { a: u8, b: u16 }`: two bytes, both fields at offset `0`. -/
def d3UnionULayout : TypeLayout :=
  { size := { bytes := 2 }, align := { bytes := 2 }, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false, fieldLayouts := [0, 1] }

def d3UnionLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [d3UnionU8Layout, d3UnionU16Layout, d3UnionULayout] }

def d3UnionU8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }
def d3UnionU16Ty : Ty := { kind := .uint .u16, layoutIdx := 1 }

/-- `_0 : u8`, `_1 : U`. -/
def d3UnionDecls : List LocalDecl :=
  [{ mutability := .mut, ty := d3UnionU8Ty, debugName := none },
   { mutability := .mut, ty := { kind := .adt "U" [], layoutIdx := 2 }, debugName := none }]

/-- `_1 = U { b: 0x0302 }` (the value of the `U { b: const 0x0302_u16 }` aggregate). -/
def d3UnionLocals : List LocalSlot := [.uninit, .init (.aggregate 0 [.unit, .scalar ⟨770, 2⟩])]

/-- `_1` after `move _1.a`: byte `0` uninitialized, byte `1 = 0x03` kept (raw
overlay). -/
def d3UnionAfterMoveA : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨0, 0⟩, .scalar ⟨3, 1⟩]])]

/-- `_1` after `_1.a = 9`. -/
def d3UnionAfterReinit : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [sc8 9, .unit, .aggregate 0 [sc8 9, sc8 3]])]

/-- **`D3` union field move and re-initialization.** Moving `_1.a` (`u8`) out of
`_1 = U { b: 0x0302 }` delivers the low byte `2` and deinitializes exactly byte
`0`: re-reading `_1.a` or the overlapping `_1.b` faults, while the whole union
(which may hold uninitialized bytes) is still readable — its raw uninitialized
byte is not the moved-out marker. Writing `_1.a = 9` re-initializes byte `0`, so
`_1.b` reads `0x0309`; the legacy semantics keeps the union intact. -/
theorem canary_D3_union_field_move_and_reinit :
    evalOperand d3UnionLocals (.move (pl 1 [.field 0 d3UnionU8Ty])) [] [] d3UnionLayouts []
      d3UnionDecls [] true = .ok (sc8 2) d3UnionAfterMoveA ∧
    evalOperand d3UnionAfterMoveA (.copy (pl 1 [.field 0 d3UnionU8Ty])) [] [] d3UnionLayouts []
      d3UnionDecls [] true = .ub ∧
    evalOperand d3UnionAfterMoveA (.copy (pl 1 [.field 1 d3UnionU16Ty])) [] [] d3UnionLayouts []
      d3UnionDecls [] true = .ub ∧
    evalOperand d3UnionAfterMoveA (.copy (pl 1 [])) [] [] d3UnionLayouts [] d3UnionDecls [] true =
      .ok (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨0, 0⟩, .scalar ⟨3, 1⟩]])
        d3UnionAfterMoveA ∧
    writePlaceValue d3UnionAfterMoveA [] (pl 1 [.field 0 d3UnionU8Ty]) (sc8 9) d3UnionDecls
      d3UnionLayouts = .ok d3UnionAfterReinit ∧
    evalOperand d3UnionAfterReinit (.copy (pl 1 [.field 1 d3UnionU16Ty])) [] [] d3UnionLayouts []
      d3UnionDecls [] true = .ok (.scalar ⟨777, 2⟩) d3UnionAfterReinit ∧
    evalOperand d3UnionLocals (.move (pl 1 [.field 0 d3UnionU8Ty])) [] [] d3UnionLayouts []
      d3UnionDecls [] = .ok (sc8 2) d3UnionLocals :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! #### `ep1-A2`: exact `Deref` targets, strides, global pointees and union byte windows -/

/-- One-byte primitive layout. -/
def a2U8Layout : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false, fieldLayouts := [] }

/-- `(u8, u8)` layout (fields at offsets `0` and `1`). -/
def a2PairLayout : TypeLayout :=
  { size := ⟨2⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .arbitrary [⟨0⟩, ⟨1⟩] [0, 1], variants := .single 0, isUninhabited := false,
    fieldLayouts := [0, 0] }

/-- `[(u8, u8); 2]` layout (stride `2`). -/
def a2PairArrLayout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .array ⟨2⟩ 2, variants := .single 0, isUninhabited := false, fieldLayouts := [1] }

/-- A thin-pointer layout. -/
def a2PtrLayout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false, fieldLayouts := [] }

/-- Layouts of the array-of-pairs canaries. -/
def a2PairArrLayouts : LayoutTable :=
  { emptyLayoutTable with entries := [a2U8Layout, a2PairLayout, a2PairArrLayout, a2PtrLayout] }

/-- `(u8, u8)`. -/
def a2PairTy : Ty := { kind := .tuple [.uint .u8, .uint .u8], layoutIdx := 1 }

/-- `_1 : [(u8, u8); 2]`, `_2 : *mut (u8, u8)`, `_3 : &(u8, u8)`. -/
def a2PairArrDecls : List LocalDecl :=
  [{ mutability := .mut, ty := u8Ty, debugName := .none },
   { mutability := .mut, ty := { kind := .array (.tuple [.uint .u8, .uint .u8]) 2, layoutIdx := 2 },
     debugName := .none },
   { mutability := .mut, ty := { kind := .rawPtr .mut (.tuple [.uint .u8, .uint .u8]), layoutIdx := 3 },
     debugName := .none },
   { mutability := .not, ty := { kind := .ref .not (.tuple [.uint .u8, .uint .u8]), layoutIdx := 3 },
     debugName := .none }]

/-- `_1 = [(1, 2), (3, 4)]`; `_2 = &raw mut _1[1]` (tag `2`, active) and
`_3 = &_1[1]` (tag `3`, frozen), both at byte offset `2` of `_1`. -/
def a2PairArrLocals : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [.aggregate 0 [sc8 1, sc8 2], .aggregate 0 [sc8 3, sc8 4]]),
    .init (.ptr { allocId := 2, offsetBytes := 2 } 8), .init (.ptr { allocId := 3, offsetBytes := 2 } 8)]

/-- After `move (*_2).0`: only `_1[1].0` is moved out. -/
def a2PairArrAfterMove : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [.aggregate 0 [sc8 1, sc8 2], .aggregate 0 [movedUninitValue, sc8 4]]),
    .init (.ptr { allocId := 2, offsetBytes := 2 } 8), .init (.ptr { allocId := 3, offsetBytes := 2 } 8)]

/-- Typed `deinitProjectedMoves` evaluation over the array-of-pairs canary. -/
def a2EvalPairArr (locals : List LocalSlot) (op : Operand) : PlaceReadResult :=
  evalOperand locals op d5Borrows [] a2PairArrLayouts [] a2PairArrDecls [] true

/-- **`(*_ptr).field` through a thin pointer at a non-zero byte offset into an
array element (`ep1-A2`).** With `_2 : *mut (u8, u8)` pointing at `_1[1]` (byte
offset `2`), `move (*_2).0` delivers `3` and deinitializes exactly `_1[1].0`: the
sibling field `(*_2).1` stays readable through `_2` and through the frozen shared
borrow `_3`, the sibling element `_1[0] = (1, 2)` is untouched, while `(*_2).0`,
`*_3`, `_1[1]` and `_1` fault; the typed write `(*_2).0 = 9` re-initializes it. -/
theorem canary_D5_typed_deref_field_of_array_elem_move :
    a2EvalPairArr a2PairArrLocals (.move (pl 2 [.deref, .field 0 u8Ty])) =
      .ok (sc8 3) a2PairArrAfterMove ∧
    a2EvalPairArr a2PairArrAfterMove (.copy (pl 2 [.deref, .field 1 u8Ty])) =
      .ok (sc8 4) a2PairArrAfterMove ∧
    a2EvalPairArr a2PairArrAfterMove (.copy (pl 3 [.deref, .field 1 u8Ty])) =
      .ok (sc8 4) a2PairArrAfterMove ∧
    a2EvalPairArr a2PairArrAfterMove (.copy (pl 1 [.constantIndex 0 2 false])) =
      .ok (.aggregate 0 [sc8 1, sc8 2]) a2PairArrAfterMove ∧
    a2EvalPairArr a2PairArrAfterMove (.copy (pl 2 [.deref, .field 0 u8Ty])) = .ub ∧
    a2EvalPairArr a2PairArrAfterMove (.copy (pl 3 [.deref])) = .ub ∧
    a2EvalPairArr a2PairArrAfterMove (.copy (pl 1 [.constantIndex 1 2 false])) = .ub ∧
    a2EvalPairArr a2PairArrAfterMove (.copy (pl 1 [])) = .ub ∧
    writePlaceValue a2PairArrAfterMove d5Borrows (pl 2 [.deref, .field 0 u8Ty]) (sc8 9)
        a2PairArrDecls a2PairArrLayouts =
      .ok [.uninit, .init (.aggregate 0 [.aggregate 0 [sc8 1, sc8 2], .aggregate 0 [sc8 9, sc8 4]]),
        .init (.ptr { allocId := 2, offsetBytes := 2 } 8),
        .init (.ptr { allocId := 3, offsetBytes := 2 } 8)] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `[u8; 4]` layout (stride `1`). -/
def a2U8x4Layout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .array ⟨1⟩ 4, variants := .single 0, isUninhabited := false, fieldLayouts := [0] }

/-- `[u8; 2]` layout (stride `1`). -/
def a2U8x2Layout : TypeLayout :=
  { size := ⟨2⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .array ⟨1⟩ 2, variants := .single 0, isUninhabited := false, fieldLayouts := [0] }

/-- Layouts of the equal-values canary. -/
def a2EqLayouts : LayoutTable :=
  { emptyLayoutTable with entries := [a2U8Layout, a2U8x4Layout, a2PtrLayout, a2U8x2Layout] }

/-- `_1 : [u8; 4]`, `_2 : *mut [u8; 2]`. -/
def a2EqDecls : List LocalDecl :=
  [{ mutability := .mut, ty := u8Ty, debugName := .none },
   { mutability := .mut, ty := { kind := .array (.uint .u8) 4, layoutIdx := 1 }, debugName := .none },
   { mutability := .mut, ty := { kind := .rawPtr .mut (.array (.uint .u8) 2), layoutIdx := 2 },
     debugName := .none }]

/-- `_1 = [7, 7, 7, 7]` and `_2 = &raw mut _1[2] as *mut [u8; 2]` (tag `2`, byte
offset `2`). -/
def a2EqLocals : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [sc8 7, sc8 7, sc8 7, sc8 7]),
    .init (.ptr { allocId := 2, offsetBytes := 2 } 8)]

/-- Typed `deinitProjectedMoves` evaluation over the equal-values canary. -/
def a2EvalEq (locals : List LocalSlot) (op : Operand) : PlaceReadResult :=
  evalOperand locals op d5Borrows [] a2EqLayouts [] a2EqDecls [] true

/-- `(u8, u8, u8, u8)` layout. -/
def a2QuadLayout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .arbitrary [⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩] [0, 1, 2, 3], variants := .single 0,
    isUninhabited := false, fieldLayouts := [0, 0, 0, 0] }

/-- `_1 : (u8, u8, u8, u8)`, `_2 : *mut (u8, u8)`. -/
def a2QuadDecls : List LocalDecl :=
  [{ mutability := .mut, ty := u8Ty, debugName := .none },
   { mutability := .mut,
     ty := { kind := .tuple [.uint .u8, .uint .u8, .uint .u8, .uint .u8], layoutIdx := 2 },
     debugName := .none },
   { mutability := .mut, ty := { kind := .rawPtr .mut (.tuple [.uint .u8, .uint .u8]), layoutIdx := 3 },
     debugName := .none }]

/-- `_1 = (7, 7, 7, 7)` and `_2 = &raw mut _1.2 as *mut (u8, u8)` (byte offset `2`). -/
def a2QuadLocals : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [sc8 7, sc8 7, sc8 7, sc8 7]),
    .init (.ptr { allocId := 2, offsetBytes := 2 } 8)]

/-- **A `Deref` move deinitializes the place the read accessed, never another
place holding an equal value (`ep1-A2` regression).** With `_1 = [7, 7, 7, 7]` and
`_2 = &raw mut _1[2] as *mut [u8; 2]`, `move (*_2)[1]` reads `_1[3]` and
deinitializes exactly `_1[3]` (`move (*_2)[0]` exactly `_1[2]`), leaving `_1[1]`
readable; resolving the target by value equality had deinitialized `_1[1]` (resp.
`_1[0]`) and left the moved `_1[3]` initialized. A pointer cast into the middle of
a tuple whose typed read decodes the pointee bytes (`(*_2).1` with
`_2 = &raw mut _1.2 as *mut (u8, u8)`) has no structural target: the move fails
closed instead of deinitializing the equal-valued `_1.1`. -/
theorem canary_D5_typed_deref_equal_values_exact_target :
    a2EvalEq a2EqLocals (.move (pl 2 [.deref, .constantIndex 1 2 false])) =
      .ok (sc8 7) [.uninit, .init (.aggregate 0 [sc8 7, sc8 7, sc8 7, movedUninitValue]),
        .init (.ptr { allocId := 2, offsetBytes := 2 } 8)] ∧
    a2EvalEq a2EqLocals (.move (pl 2 [.deref, .constantIndex 0 2 false])) =
      .ok (sc8 7) [.uninit, .init (.aggregate 0 [sc8 7, sc8 7, movedUninitValue, sc8 7]),
        .init (.ptr { allocId := 2, offsetBytes := 2 } 8)] ∧
    a2EvalEq [.uninit, .init (.aggregate 0 [sc8 7, sc8 7, sc8 7, movedUninitValue]),
        .init (.ptr { allocId := 2, offsetBytes := 2 } 8)] (.copy (pl 1 [.constantIndex 1 4 false])) =
      .ok (sc8 7) [.uninit, .init (.aggregate 0 [sc8 7, sc8 7, sc8 7, movedUninitValue]),
        .init (.ptr { allocId := 2, offsetBytes := 2 } 8)] ∧
    a2EvalEq [.uninit, .init (.aggregate 0 [sc8 7, sc8 7, sc8 7, movedUninitValue]),
        .init (.ptr { allocId := 2, offsetBytes := 2 } 8)]
        (.copy (pl 2 [.deref, .constantIndex 1 2 false])) = .ub ∧
    evalOperand a2QuadLocals (.copy (pl 2 [.deref, .field 1 u8Ty])) d5Borrows []
      { emptyLayoutTable with entries := [a2U8Layout, a2PairLayout, a2QuadLayout, a2PtrLayout] } []
      a2QuadDecls [] true = .ok (sc8 7) a2QuadLocals ∧
    evalOperand a2QuadLocals (.move (pl 2 [.deref, .field 1 u8Ty])) d5Borrows []
      { emptyLayoutTable with entries := [a2U8Layout, a2PairLayout, a2QuadLayout, a2PtrLayout] } []
      a2QuadDecls [] true = .unsupported :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `_1 = [(1, 2), (3, 4)]` and the slice fat pointer `_2 = &raw mut _1[1..]`
(`len = 1`, byte offset `2`, tag `2`). -/
def a2StrideLocals : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [.aggregate 0 [sc8 1, sc8 2], .aggregate 0 [sc8 3, sc8 4]]),
    .init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 2 } 8,
      .scalar { bits := 1, sizeBytes := 8 }])]

/-- After `move _1[0].0`. -/
def a2StrideAfterMove : List LocalSlot :=
  [.uninit,
    .init (.aggregate 0 [.aggregate 0 [movedUninitValue, sc8 2], .aggregate 0 [sc8 3, sc8 4]]),
    .init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 2 } 8,
      .scalar { bits := 1, sizeBytes := 8 }])]

/-- **Element strides skip nested moved-out leaves (`ep1-A2` regression of the
`ep1-B2` stride fix).** After `move _1[0].0` on `_1 = [(1, 2), (3, 4)]`, the first
element holds a moved-out leaf of no byte width, so its inferred size (`1`) is
not the element stride; `inferElemListByteStride` infers the stride `2` from the
first element without a moved-out leaf, so the slice fat pointer `_2 = &_1[1..]`
at byte offset `2` still reads `(*_2)[0].1 = 4`, moves it, and writes it (the
`ep1-B2` stride faulted on all three because only a moved scalar element was
skipped). -/
theorem canary_D9_slice_stride_skips_nested_moved_leaf :
    inferElemListByteStride
      [.aggregate 0 [movedUninitValue, sc8 2], .aggregate 0 [sc8 3, sc8 4]] = 2 ∧
    evalOperand a2StrideLocals (.move (pl 1 [.constantIndex 0 2 false, .field 0 u8Ty]))
      (deinitProjectedMoves := true) = .ok (sc8 1) a2StrideAfterMove ∧
    evalOperand a2StrideAfterMove (.copy (pl 2 [.deref, .constantIndex 0 1 false, .field 1 u8Ty]))
      d5Borrows (deinitProjectedMoves := true) = .ok (sc8 4) a2StrideAfterMove ∧
    evalOperand a2StrideAfterMove (.move (pl 2 [.deref, .constantIndex 0 1 false, .field 1 u8Ty]))
      d5Borrows (deinitProjectedMoves := true) =
      .ok (sc8 4) [.uninit,
        .init (.aggregate 0 [.aggregate 0 [movedUninitValue, sc8 2],
          .aggregate 0 [sc8 3, movedUninitValue]]),
        .init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 2 } 8,
          .scalar { bits := 1, sizeBytes := 8 }])] ∧
    writePlaceValue a2StrideAfterMove d5Borrows
        (pl 2 [.deref, .constantIndex 0 1 false, .field 1 u8Ty]) (sc8 9) =
      .ok [.uninit,
        .init (.aggregate 0 [.aggregate 0 [movedUninitValue, sc8 2], .aggregate 0 [sc8 3, sc8 9]]),
        .init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 2 } 8,
          .scalar { bits := 1, sizeBytes := 8 }])] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- An immutable 4-byte global holding `0x11223344` (little-endian). -/
def a2GlobalU32 : CapturedAllocation :=
  { allocId := 7, bytes := [some 0x44, some 0x33, some 0x22, some 0x11], relocations := [],
    align := ⟨4⟩, mutability := .not }

/-- An immutable zero-sized global. -/
def a2GlobalZst : CapturedAllocation :=
  { allocId := 8, bytes := [], relocations := [], align := ⟨1⟩, mutability := .not }

/-- `_1 = &GLOBAL_U32` and `_2 = &GLOBAL_ZST`: pointers with no borrow-table entry. -/
def a2GlobalLocals : List LocalSlot :=
  [.uninit, .init (.ptr { allocId := 7, offsetBytes := 0 } 4),
    .init (.ptr { allocId := 8, offsetBytes := 0 } 0)]

/-- `_1 : &u32`, `_2 : &()`. -/
def a2GlobalDecls : List LocalDecl :=
  [{ mutability := .mut, ty := u8Ty, debugName := .none },
   { mutability := .mut, ty := { kind := .ref .not (.uint .u32), layoutIdx := 0 }, debugName := .none },
   { mutability := .mut, ty := { kind := .ref .not (.tuple []), layoutIdx := 0 }, debugName := .none }]

/-- **Moves out of global allocations fail closed (`ep1-A2`).** `*_1` (a
non-zero-sized immutable global, no borrow-table entry) reads `0x11223344`, but
`move (*_1)` with `deinitProjectedMoves := true` is `.unsupported`, untyped and
typed alike: it never succeeds as a silent copy that leaves the moved bytes
initialized (the legacy semantics, which never deinitializes, does return the
value). Moving the zero-sized global `*_2` moves no bytes and succeeds without
changing any local. -/
theorem canary_global_deref_move_fails_closed :
    evalOperand a2GlobalLocals (.copy (pl 1 [.deref])) [] [a2GlobalU32, a2GlobalZst]
      (deinitProjectedMoves := true) = .ok (.scalar ⟨0x11223344, 4⟩) a2GlobalLocals ∧
    evalOperand a2GlobalLocals (.move (pl 1 [.deref])) [] [a2GlobalU32, a2GlobalZst]
      (deinitProjectedMoves := true) = .unsupported ∧
    evalOperand a2GlobalLocals (.move (pl 1 [.deref])) [] [a2GlobalU32, a2GlobalZst]
      emptyLayoutTable [] a2GlobalDecls [] true = .unsupported ∧
    evalOperand a2GlobalLocals (.move (pl 1 [.deref])) [] [a2GlobalU32, a2GlobalZst] =
      .ok (.scalar ⟨0x11223344, 4⟩) a2GlobalLocals ∧
    evalOperand a2GlobalLocals (.move (pl 2 [.deref])) [] [a2GlobalU32, a2GlobalZst]
      (deinitProjectedMoves := true) = .ok .unit a2GlobalLocals ∧
    evalOperand a2GlobalLocals (.move (pl 2 [.deref])) [] [a2GlobalU32, a2GlobalZst]
      emptyLayoutTable [] a2GlobalDecls [] true = .ok .unit a2GlobalLocals :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `u16` layout of the overlapping-union canary. -/
def a2U16Layout : TypeLayout :=
  { size := { bytes := 2 }, align := { bytes := 2 },
    backendRepr := .scalar (.initialized (.int 16 false) { start := 0, end_ := 65535 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- `u32` layout of the overlapping-union canary. -/
def a2U32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 },
    backendRepr := .scalar (.initialized (.int 32 false) { start := 0, end_ := 4294967295 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- `(u16, u16)` layout (fields at offsets `0` and `2`). -/
def a2U16PairLayout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 2 }, backendRepr := .memory,
    fields := .arbitrary [⟨0⟩, ⟨2⟩] [0, 1], variants := .single 0, isUninhabited := false,
    fieldLayouts := [0, 0] }

/-- `union W { f0: u32, f1: (u16, u16) }`: four bytes, both fields at offset `0`. -/
def a2UnionWLayout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false, fieldLayouts := [1, 2] }

def a2UnionLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [a2U16Layout, a2U32Layout, a2U16PairLayout, a2UnionWLayout] }

def a2U16Ty : Ty := { kind := .uint .u16, layoutIdx := 0 }
def a2U32Ty : Ty := { kind := .uint .u32, layoutIdx := 1 }
def a2U16PairTy : Ty := { kind := .tuple [.uint .u16, .uint .u16], layoutIdx := 2 }

/-- `_0 : u16`, `_1 : W`. -/
def a2UnionDecls : List LocalDecl :=
  [{ mutability := .mut, ty := a2U16Ty, debugName := none },
   { mutability := .mut, ty := { kind := .adt "W" [], layoutIdx := 3 }, debugName := none }]

/-- `_1 = W { f0: 0x11223344 }`. -/
def a2UnionLocals : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [.scalar ⟨0x11223344, 4⟩, .unit])]

/-- `_1` after `move _1.f1.0`: bytes `[0, 2)` uninitialized, bytes `[2, 4)` kept
(`0x22`, `0x11`, raw overlay). -/
def a2UnionAfterMove : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [.unit, .unit,
    .aggregate 0 [.scalar ⟨0, 0⟩, .scalar ⟨0, 0⟩, .scalar ⟨0x22, 1⟩, .scalar ⟨0x11, 1⟩]])]

/-- `_1` after re-initializing `_1.f1.0 = 0x5566`. -/
def a2UnionAfterReinit : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [.unit, .aggregate 0 [.scalar ⟨0x5566, 2⟩, .scalar ⟨0x1122, 2⟩]])]

/-- Typed `deinitProjectedMoves` evaluation over the overlapping-union canary. -/
def a2EvalUnion (locals : List LocalSlot) (op : Operand) : PlaceReadResult :=
  evalOperand locals op [] [] a2UnionLayouts [] a2UnionDecls [] true

/-- **Partial byte-window move out of overlapping union fields (`ep1-A2`).** For
`_1 = W { f0: 0x11223344 }` with `f1 : (u16, u16)` overlapping `f0`,
`move _1.f1.0` delivers the low half `0x3344` and deinitializes exactly bytes
`[0, 2)`: `_1.f1.1` still reads `0x1122` (bytes `[2, 4)`), while `_1.f1.0`, the
overlapping `_1.f0` and the pair `_1.f1` fault; the whole union (which may hold
uninitialized bytes) reads as its raw byte image. Re-initializing `_1.f1.0 =
0x5566` makes `_1.f0` read `0x11225566`; moving the high half `_1.f1.1` instead
deinitializes bytes `[2, 4)` only; the legacy semantics keeps the union intact. -/
theorem canary_D3_union_partial_byte_window_move :
    a2EvalUnion a2UnionLocals (.move (pl 1 [.field 1 a2U16PairTy, .field 0 a2U16Ty])) =
      .ok (.scalar ⟨0x3344, 2⟩) a2UnionAfterMove ∧
    a2EvalUnion a2UnionAfterMove (.copy (pl 1 [.field 1 a2U16PairTy, .field 1 a2U16Ty])) =
      .ok (.scalar ⟨0x1122, 2⟩) a2UnionAfterMove ∧
    a2EvalUnion a2UnionAfterMove (.copy (pl 1 [.field 1 a2U16PairTy, .field 0 a2U16Ty])) = .ub ∧
    a2EvalUnion a2UnionAfterMove (.copy (pl 1 [.field 0 a2U32Ty])) = .ub ∧
    a2EvalUnion a2UnionAfterMove (.copy (pl 1 [.field 1 a2U16PairTy])) = .ub ∧
    a2EvalUnion a2UnionAfterMove (.copy (pl 1 [])) =
      .ok (.aggregate 0 [.unit, .unit,
        .aggregate 0 [.scalar ⟨0, 0⟩, .scalar ⟨0, 0⟩, .scalar ⟨0x22, 1⟩, .scalar ⟨0x11, 1⟩]])
        a2UnionAfterMove ∧
    writePlaceValue a2UnionAfterMove [] (pl 1 [.field 1 a2U16PairTy, .field 0 a2U16Ty])
        (.scalar ⟨0x5566, 2⟩) a2UnionDecls a2UnionLayouts = .ok a2UnionAfterReinit ∧
    a2EvalUnion a2UnionAfterReinit (.copy (pl 1 [.field 0 a2U32Ty])) =
      .ok (.scalar ⟨0x11225566, 4⟩) a2UnionAfterReinit ∧
    a2EvalUnion a2UnionLocals (.move (pl 1 [.field 1 a2U16PairTy, .field 1 a2U16Ty])) =
      .ok (.scalar ⟨0x1122, 2⟩) [.uninit, .init (.aggregate 0 [.unit, .unit,
        .aggregate 0 [.scalar ⟨0x44, 1⟩, .scalar ⟨0x33, 1⟩, .scalar ⟨0, 0⟩, .scalar ⟨0, 0⟩]])] ∧
    evalOperand a2UnionLocals (.move (pl 1 [.field 1 a2U16PairTy, .field 0 a2U16Ty])) [] []
      a2UnionLayouts [] a2UnionDecls [] = .ok (.scalar ⟨0x3344, 2⟩) a2UnionLocals :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! #### `ep1-B3`: chained projections (`_1.0.1`, `(_1[i]).0`, `(*_p).0[1..3]`, `((*_fatPtr)[1]).0`) and transparent `.opaqueCast` / `.unwrapUnsafeBinder` -/

/-- `[u8; 4]` and `[u8; 2]` type annotations. -/
def b3Arr4Ty : Ty := { kind := .array (.uint .u8) 4, layoutIdx := 0 }
def b3Arr2Ty : Ty := { kind := .array (.uint .u8) 2, layoutIdx := 0 }
def b3SliceU8Ty : Ty := { kind := .slice (.uint .u8), layoutIdx := 0 }

/-- `_1 : [(u8, u8); 2] = [(10, 11), (20, 21)]`, `_2 : usize = 1` (dynamic index),
`_3 : *mut [(u8, u8)]` slice fat pointer (`allocId = 2`, `offsetBytes = 0`, `len = 2`). -/
def b3IdxFatLocals : List LocalSlot :=
  [.uninit,
   .init (.aggregate 0 [.aggregate 0 [sc8 10, sc8 11], .aggregate 0 [sc8 20, sc8 21]]),
   .init (.scalar { bits := 1, sizeBytes := 8 }),
   .init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0 } 8,
     .scalar { bits := 2, sizeBytes := 8 }])]

def b3IdxFatAfterMove : List LocalSlot :=
  [.uninit,
   .init (.aggregate 0 [.aggregate 0 [sc8 10, sc8 11], .aggregate 0 [movedUninitValue, sc8 21]]),
   .init (.scalar { bits := 1, sizeBytes := 8 }),
   .init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0 } 8,
     .scalar { bits := 2, sizeBytes := 8 }])]

/-- `_1 : ([u8; 4], u8) = ([10, 11, 12, 13], 40)`, `_2 = &raw mut _1` (tag `2`),
`_3 = &_1` (tag `3`, frozen). -/
def b3PtrFieldSubLocals : List LocalSlot :=
  [.uninit,
   .init (.aggregate 0 [.aggregate 0 [sc8 10, sc8 11, sc8 12, sc8 13], sc8 40]),
   .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
   .init (.ptr { allocId := 3, offsetBytes := 0 } 8)]

def b3PtrFieldSubAfterMove : List LocalSlot :=
  [.uninit,
   .init (.aggregate 0 [.aggregate 0 [sc8 10, movedUninitValue, movedUninitValue, sc8 13], sc8 40]),
   .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
   .init (.ptr { allocId := 3, offsetBytes := 0 } 8)]

/-- **Chained multi-level projections (`ep1-B3`): `move _1.0.1`, `move (_1[i]).0`,
`move (*_p).0[1..3]`, and `move ((*_fatPtr)[1]).0`.**
1. `move _1.0.1` on `d3NestedLocals` (`((10, 11), 12)`) delivers `11` and marks
   only `_1.0.1` moved-out while `_1.0.0 = 10` and `_1.1 = 12` remain readable.
2. `move (_1[_2]).0` (`[.index 2, .field 0 u8Ty]` with `_2 = 1`) on
   `b3IdxFatLocals` delivers `20` and marks only `_1[1].0` moved-out (`_1[1].1 = 21`
   and `_1[0] = (10, 11)` stay readable); `writePlaceValue` at `(_1[_2]).0`
   re-initializes it.
3. `move (*_2).0[1..3]` (`[.deref, .field 0 b3Arr4Ty, .subslice 1 3 false]`) on
   `b3PtrFieldSubLocals` with active + frozen borrows `d5Borrows` delivers
   `[11, 12]` and marks `_1.0[1]` and `_1.0[2]` element-wise while keeping
   `(*_3).0[0] = 10`, `(*_3).0[3] = 13`, and `(*_3).1 = 40` readable through the
   sibling frozen borrow `_3`.
4. `move ((*_3)[1]).0` (`[.deref, .constantIndex 1 2 false, .field 0 u8Ty]`) on
   `b3IdxFatLocals` with `d5Borrows` delivers `20` and deinitializes `_1[1].0`
   while keeping `((*_3)[1]).1 = 21` and `(*_3)[0] = (10, 11)` readable. -/
theorem canary_B3_chained_projections_move_and_reinit :
    evalOperand d3NestedLocals (.move (pl 1 [.field 0 tupU8U8Ty, .field 1 u8Ty]))
      (deinitProjectedMoves := true) =
      .ok (sc8 11) [.uninit, .init (.aggregate 0 [.aggregate 0 [sc8 10, movedUninitValue], sc8 12])] ∧
    evalOperand [.uninit, .init (.aggregate 0 [.aggregate 0 [sc8 10, movedUninitValue], sc8 12])]
      (.copy (pl 1 [.field 0 tupU8U8Ty, .field 0 u8Ty])) (deinitProjectedMoves := true) =
      .ok (sc8 10) [.uninit, .init (.aggregate 0 [.aggregate 0 [sc8 10, movedUninitValue], sc8 12])] ∧
    evalOperand [.uninit, .init (.aggregate 0 [.aggregate 0 [sc8 10, movedUninitValue], sc8 12])]
      (.copy (pl 1 [.field 0 tupU8U8Ty])) (deinitProjectedMoves := true) = .ub ∧
    evalOperand b3IdxFatLocals (.move (pl 1 [.index 2, .field 0 u8Ty])) d5Borrows
      (deinitProjectedMoves := true) = .ok (sc8 20) b3IdxFatAfterMove ∧
    evalOperand b3IdxFatAfterMove (.copy (pl 1 [.index 2, .field 1 u8Ty])) d5Borrows
      (deinitProjectedMoves := true) = .ok (sc8 21) b3IdxFatAfterMove ∧
    evalOperand b3IdxFatAfterMove (.copy (pl 1 [.constantIndex 0 2 false])) d5Borrows
      (deinitProjectedMoves := true) =
      .ok (.aggregate 0 [sc8 10, sc8 11]) b3IdxFatAfterMove ∧
    evalOperand b3IdxFatAfterMove (.copy (pl 1 [.index 2, .field 0 u8Ty])) d5Borrows
      (deinitProjectedMoves := true) = .ub ∧
    writePlaceValue b3IdxFatAfterMove d5Borrows (pl 1 [.index 2, .field 0 u8Ty]) (sc8 20) =
      .ok b3IdxFatLocals ∧
    evalOperand b3PtrFieldSubLocals
      (.move (pl 2 [.deref, .field 0 b3Arr4Ty, .subslice 1 3 false])) d5Borrows
      (deinitProjectedMoves := true) =
      .ok (.aggregate 0 [sc8 11, sc8 12]) b3PtrFieldSubAfterMove ∧
    evalOperand b3PtrFieldSubAfterMove
      (.copy (pl 3 [.deref, .field 0 b3Arr4Ty, .constantIndex 0 4 false])) d5Borrows
      (deinitProjectedMoves := true) = .ok (sc8 10) b3PtrFieldSubAfterMove ∧
    evalOperand b3PtrFieldSubAfterMove
      (.copy (pl 3 [.deref, .field 0 b3Arr4Ty, .constantIndex 3 4 false])) d5Borrows
      (deinitProjectedMoves := true) = .ok (sc8 13) b3PtrFieldSubAfterMove ∧
    evalOperand b3PtrFieldSubAfterMove
      (.copy (pl 3 [.deref, .field 1 u8Ty])) d5Borrows
      (deinitProjectedMoves := true) = .ok (sc8 40) b3PtrFieldSubAfterMove ∧
    evalOperand b3PtrFieldSubAfterMove
      (.copy (pl 3 [.deref, .field 0 b3Arr4Ty, .constantIndex 1 4 false])) d5Borrows
      (deinitProjectedMoves := true) = .ub ∧
    evalOperand b3IdxFatLocals
      (.move (pl 3 [.deref, .constantIndex 1 2 false, .field 0 u8Ty])) d5Borrows
      (deinitProjectedMoves := true) = .ok (sc8 20) b3IdxFatAfterMove ∧
    evalOperand b3IdxFatAfterMove
      (.copy (pl 3 [.deref, .constantIndex 1 2 false, .field 1 u8Ty])) d5Borrows
      (deinitProjectedMoves := true) = .ok (sc8 21) b3IdxFatAfterMove ∧
    evalOperand b3IdxFatAfterMove
      (.copy (pl 3 [.deref, .constantIndex 1 2 false, .field 0 u8Ty])) d5Borrows
      (deinitProjectedMoves := true) = .ub :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Transparent `.opaqueCast` and `.unwrapUnsafeBinder` projections wrapping
`.field`, `.subslice`, and `.deref` (`ep1-B3`).**
1. Prefix and suffix `.opaqueCast` / `.unwrapUnsafeBinder` around `.field 0 u8Ty`
   produce the exact same deinitialized state `d2AfterMove` as `.field 0 u8Ty`,
   and re-reading through either transparent wrapper faults with `.ub` while the
   sibling `.field 1` stays readable.
2. Prefix and suffix `.opaqueCast` / `.unwrapUnsafeBinder` around `.subslice 1 3 false`
   produce the exact same element-wise deinitialized array `d9AfterSubslice`
   (preserving the 4-element array length because `lastStructuralProjection?`
   skips trailing transparent projections).
3. `.opaqueCast` / `.unwrapUnsafeBinder` on `(*_2)` (thin pointer and slice fat
   pointer) deinitializes the active-frame target just like an unwrapped `Deref`. -/
theorem canary_B3_transparent_opaqueCast_and_unwrapUnsafeBinder_moves :
    evalOperand d2Locals (.move (pl 1 [.opaqueCast tupU8U8Ty, .field 0 u8Ty])) d5Borrows
      (deinitProjectedMoves := true) = .ok (sc8 2) d2AfterMove ∧
    evalOperand d2Locals (.move (pl 1 [.field 0 u8Ty, .opaqueCast u8Ty])) d5Borrows
      (deinitProjectedMoves := true) = .ok (sc8 2) d2AfterMove ∧
    evalOperand d2Locals (.move (pl 1 [.unwrapUnsafeBinder tupU8U8Ty, .field 0 u8Ty])) d5Borrows
      (deinitProjectedMoves := true) = .ok (sc8 2) d2AfterMove ∧
    evalOperand d2Locals (.move (pl 1 [.field 0 u8Ty, .unwrapUnsafeBinder u8Ty])) d5Borrows
      (deinitProjectedMoves := true) = .ok (sc8 2) d2AfterMove ∧
    evalOperand d2AfterMove (.copy (pl 1 [.field 0 u8Ty, .opaqueCast u8Ty])) d5Borrows
      (deinitProjectedMoves := true) = .ub ∧
    evalOperand d2AfterMove (.copy (pl 1 [.unwrapUnsafeBinder tupU8U8Ty, .field 1 u8Ty])) d5Borrows
      (deinitProjectedMoves := true) = .ok (sc8 3) d2AfterMove ∧
    evalOperand d9Locals (.move (pl 1 [.opaqueCast b3Arr4Ty, .subslice 1 3 false])) d5Borrows
      (deinitProjectedMoves := true) = .ok (.aggregate 0 [sc8 11, sc8 12]) d9AfterSubslice ∧
    evalOperand d9Locals (.move (pl 1 [.subslice 1 3 false, .opaqueCast b3Arr2Ty])) d5Borrows
      (deinitProjectedMoves := true) = .ok (.aggregate 0 [sc8 11, sc8 12]) d9AfterSubslice ∧
    evalOperand d9Locals (.move (pl 1 [.unwrapUnsafeBinder b3Arr4Ty, .subslice 1 3 false])) d5Borrows
      (deinitProjectedMoves := true) = .ok (.aggregate 0 [sc8 11, sc8 12]) d9AfterSubslice ∧
    evalOperand d9Locals (.move (pl 1 [.subslice 1 3 false, .unwrapUnsafeBinder b3Arr2Ty])) d5Borrows
      (deinitProjectedMoves := true) = .ok (.aggregate 0 [sc8 11, sc8 12]) d9AfterSubslice ∧
    evalOperand d5TypedTupleLocals (.move (pl 2 [.deref, .opaqueCast u8Ty])) d5Borrows []
      d5TypedTupleLayouts [] d5TypedTupleDecls [] true =
      .ok (sc8 3) d5TypedTupleAfterMove ∧
    evalOperand d9SliceFatPtrLocals (.move (pl 2 [.deref, .opaqueCast b3SliceU8Ty])) d5Borrows
      (deinitProjectedMoves := true) =
      .ok (.aggregate 0 [sc8 10, sc8 11, sc8 12, sc8 13])
        [.uninit,
         .init (.aggregate 0 [movedUninitValue, movedUninitValue, movedUninitValue, movedUninitValue]),
         .init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0 } 8,
           .scalar { bits := 4, sizeBytes := 8 }])] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end TrustedCanaries

end TrustedPart

/-! ## Part 2: patched `lean-miri` with `deinitMovedPlace = false`

The source entry points `Cast.cast`, `Call.evalFnCallArgumentAt`,
`Call.evalCalleeAndArgs`, `Call.passArgument`, `Call.evalCallTerminator` and
`Call.evalTailCallTerminator` are unchanged; the consumer-side behavior lives in
the separate `Cast.castMoving`, `Call.evalFnCallArgumentMoving`,
`Call.evalCalleeAndArgsMoving`, `Call.evalCallTerminatorMoving` and
`Call.evalTailCallTerminatorMoving`, which `ExecutionMachine.stepHooks` selects
only when `deinitMovedPlace = true`. The remaining patched entry points
(`LocalAccess.evalOperand`/`evalOperandImmediate`,
`OperandMachine.evalOperand`/`evalOperandAt`, `PlaceMachine.readImmediate`,
`Place.copyRuntimePlaceNoValidate`) reduce to the source when the flag is off or
the latch is disarmed.

Where a source body calls a `private` helper (`placeLift`,
`PlaceMachine.commit`/`finish`, `Call.require`, the `Cast` lifts), the statement
uses a public verbatim copy of that helper (`src…` below), and the source body
itself is restated verbatim (`srcCopyRuntimePlaceNoValidate`, `srcReadImmediate`,
`srcCast`, `srcEvalCalleeAndArgs`, `srcPassArgument`, `srcEvalCallTerminator`,
`srcEvalTailCallTerminator`), so each theorem is an exact source identity. -/

section SourceCopies

open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

/-! ### `Place.lean` -/

section PlaceCopies

variable {P S C E A : Type}

/-- Verbatim copy of the private source helper `Miri.Interpreter.placeLift`. -/
def srcPlaceLift (value : Except StepError A) : PlaceM S A :=
  match value with | .ok value => pure value | .error error => throw error

/-- Verbatim copy of the unpatched source `copyRuntimePlaceNoValidate`
(`copy_op_no_validate`), base commit `b91fc2aa`. -/
def srcCopyRuntimePlaceNoValidate (h : PlaceHooks P S C E) (copy : PlaceCopyHooks P S C)
    (choice : C) (source : OpTy P) (dest : RuntimePlace P) (allowTransmute : Bool) : PlaceM S Unit := do
  let compatible ← srcPlaceLift (copy.compatible source.layout dest.layout)
  if !compatible && !allowTransmute then throw (.invalidProgram "copy type mismatch")
  let padding ← srcPlaceLift (copy.hasPadding source.layout)
  let value ← if padding then pure (match source.op with
      | .immediate value => ImmediateOrPlace.immediate ⟨value, localMemoryLayout source.layout⟩
      | .indirect mplace => .place ⟨mplace, localMemoryLayout source.layout⟩)
    else copy.readRaw choice source
  match value with
  | .immediate value =>
    if !source.layout.layout.isSized || !dest.layout.layout.isSized then
      throw (.invalidProgram "copy immediate is unsized")
    if source.layout.layout.size != dest.layout.layout.size then
      throw (.invalidProgram "copy immediate size mismatch")
    if compatible then writePlaceImmediateNoValidate h choice value.value dest
    else
      let memory ← forceAllocation h choice dest
      h.writeMemoryNoValidate choice value.value ⟨memory.mplace, source.layout⟩
  | .place memory =>
    let target ← forceAllocation h choice dest
    copy.memoryCopy choice ⟨memory.mplace, source.layout⟩ target

end PlaceCopies

/-! ### `PlaceMachine.lean` -/

section PlaceMachineCopies

variable {K User A : Type}

/-- Verbatim copy of the private source helper `PlaceMachine.commit`. -/
def srcCommit (config : PlaceMachine.AccessConfig K User)
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (hooks : PlaceMachine.AccessState K User)
    (touched : Option (AllocationAccessRef Provenance Miri.TreeBorrows.BorrowTree)) :
    PlaceMachine.M K User Unit :=
  modify fun state => { state with machine := config.retainTouched {hooks.machine with memory} touched }

/-- Verbatim copy of the private source helper `PlaceMachine.finish`. -/
def srcFinish (config : PlaceMachine.AccessConfig K User) (hooks : PlaceMachine.AccessState K User)
    (outcome : Except MemoryOperandError A) : PlaceMachine.M K User A := do
  match outcome with
  | .ok value => return value
  | .error error => throw (hooks.pendingError.getD (config.memoryError error))

/-- Verbatim copy of the unpatched source `PlaceMachine.readImmediate`. -/
def srcReadImmediate [DecidableEq K] (config : PlaceMachine.AccessConfig K User)
    (operand : OpTy Provenance) : PlaceMachine.M K User (RvalueImmTy Provenance) := do
  let state ← get
  let result := Miri.Interpreter.readImmediate state.machine.memory ⟨state.machine, none⟩ operand.op
    (localMemoryLayout operand.layout) config.runtime config.ghostMode config.globalKind
    config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout
  srcCommit config result.memory result.hooks result.touched
  let value ← srcFinish config result.hooks result.outcome
  return ⟨value.value, operand.layout⟩

end PlaceMachineCopies

/-! ### `Cast.lean` -/

section CastCopies

variable {P S C V A : Type}

/-- Verbatim copy of the private source helper `Cast.invalid`. -/
def srcInvalid (message : String) : RvalueM S A := throw (.invalidProgram message)

/-- Verbatim copy of the private source helper `Cast.liftResult`. -/
def srcLiftResult (result : Except StepError A) : RvalueM S A :=
  match result with | .ok value => pure value | .error error => throw error

/-- Verbatim copy of the private source helper `Cast.scalarOf`. -/
def srcScalarOf (value : RvalueImmTy P) : RvalueM S (Memory.Scalar P) :=
  srcLiftResult (value.imm.toScalar |>.mapError ScalarOps.immediateError)

/-- Verbatim copy of the private source helper `Cast.readPointer`. -/
def srcReadPointer [PointerProvenance P] (h : CastHooks P S C V) (choice : C)
    (op : OpTy P) : RvalueM S (Pointer (Option P)) := do
  let value ← h.readImmediate choice op
  let scalar ← srcScalarOf value
  srcLiftResult (scalar.toPointer h.target |>.mapError ScalarOps.scalarError)

/-- Verbatim copy of the private source helper `Cast.transmuteImmediate`. -/
def srcTransmuteImmediate (h : CastHooks P S C V) (value : RvalueImmTy P)
    (target : TyAndLayout TyId) : RvalueM S (RvalueImmTy P) := do
  if !value.layout.layout.isSized || !target.layout.isSized || value.layout.layout.size != target.layout.size then
    srcInvalid "immediate transmute requires equally sized layouts"
  srcLiftResult (h.validateImmediateABI value.imm value.layout.layout)
  let forget := target.layout.isUninhabited || target.layout.isZst ||
    (match target.layout.backendRepr, target.layout.variants, target.layout.fields with
     | .Memory, .Single _, .Arbitrary fields _ => fields.isEmpty | _, _, _ => false)
  let value := if forget then Immediate.uninit else value.imm
  srcLiftResult (h.validateImmediateABI value target.layout)
  pure ⟨value, target⟩

/-- Verbatim copy of the unpatched source `Cast.cast`, base commit `b91fc2aa`. -/
def srcCast [PointerProvenance P] (h : CastHooks P S C V) (choice : C) (fuel : Nat)
    (source : OpTy P) (kind : CastKind) (castTy : TyId) (dest : V) : RvalueM S Unit := do
  let destLayout := h.destLayout dest
  let target ← if castTy == destLayout.ty then pure destLayout else h.layoutOf choice castTy
  let skipValidity := match kind with
    | .Transmute | .Subtype | .BoxDerefTransmute | .PointerCoercion .Unsize _ => true | _ => false
  unless skipValidity do
    if ← h.enforceValidity choice source.layout then
      match ← h.typeInfo choice source.layout.ty with
      | .rawPointer _ =>
        if (match source.layout.layout.backendRepr with | .ScalarPair => true | _ => false) then h.derefPointer choice source
      | .fnPointer => h.checkFunctionPointer choice (← srcReadPointer h choice source)
      | .closure _ _ upvars => if upvars != 0 then srcInvalid "capturing closure in pointer cast"
      | .integer _ | .floating _ | .boolean | .character | .fnDefinition _ _ => pure ()
      | _ => srcInvalid "unexpected input type in non-transmute/unsize cast"
  match kind with
  | .PointerCoercion .Unsize _ =>
    Cast.unsizeInto h choice fuel source target dest
    if ← h.enforceValidity choice destLayout then
      let recursive ← h.enforceValidityRecursively choice destLayout
      h.validatePlace choice dest recursive true
  | .PointerExposeProvenance =>
    let value ← h.readImmediate choice source
    let result ← Cast.pointerExposeProvenance h choice value target
    h.writeImmediate choice result.imm dest
  | .PointerWithExposedProvenance =>
    let value ← h.readImmediate choice source
    let result ← Cast.pointerWithExposedProvenance h choice value target
    h.writeImmediate choice result.imm dest
  | .IntToInt | .IntToFloat =>
    let value ← h.readImmediate choice source
    let sourceKind ← h.typeInfo choice value.layout.ty
    match sourceKind with
    | .integer _ | .boolean | .character => pure ()
    | _ => srcInvalid "IntToInt/IntToFloat source type is not integer-like"
    match ← h.typeInfo choice target.ty with
    | .integer _ | .floating _ | .character => pure ()
    | _ => srcInvalid "IntToInt/IntToFloat destination type is not integer/float/char"
    let result ← Cast.castFromIntLike h choice (← srcScalarOf value) value.layout target
    h.writeImmediate choice result.imm dest
  | .FloatToFloat | .FloatToInt =>
    let value ← h.readImmediate choice source
    let .floating _ ← h.typeInfo choice value.layout.ty | srcInvalid "float cast source type is not float"
    -- Source converts the input float payload before matching destination kind.
    let bits ← FloatOps.readBits h.floatOps choice value
    let scalar ← match ← h.typeInfo choice target.ty with
      | .floating format => do
        let converted ← srcLiftResult (bits.convert format |>.mapError fun e => .invalidProgram s!"{repr e}")
        let converted ← FloatOps.adjustNaN h.floatOps choice converted [bits]
        if target.layout.size != format.size then srcInvalid "float cast target size mismatch"
        srcLiftResult (Memory.Scalar.fromUInt converted.bits format.size |>.mapError ScalarOps.scalarError)
      | .integer integerKind => do
        let width ← srcLiftResult (target.layout.size.bitsNat |>.mapError fun e => .invalidProgram (toString e))
        let integer ← srcLiftResult (bits.toInteger width integerKind.signed |>.mapError fun e => .invalidProgram s!"{repr e}")
        if integerKind.signed then
          srcLiftResult (Memory.Scalar.fromInt integer target.layout.size |>.mapError ScalarOps.scalarError)
        else srcLiftResult (Memory.Scalar.fromUInt (BitVec.ofInt 128 integer) target.layout.size |>.mapError ScalarOps.scalarError)
      | _ => srcInvalid "invalid float cast destination"
    h.writeImmediate choice (.scalar scalar) dest
  | .FnPtrToPtr | .PtrToPtr =>
    let value ← h.readImmediate choice source
    let result ← Cast.ptrToPtr h choice value target
    h.writeImmediate choice result.imm dest
  | .PointerCoercion .MutToConstPointer _ | .PointerCoercion .ArrayToPointer _ =>
    srcInvalid "borrowck-only pointer coercion in runtime MIR"
  | .PointerCoercion (.ReifyFnPointer _) _ =>
    h.ensureMonomorphic choice source.layout.ty
    let .fnDefinition definition args ← h.typeInfo choice source.layout.ty | srcInvalid "reify fn pointer on non-function definition"
    h.requireNoBoundVars choice args
    let some fnInstance ← h.resolveFunction choice definition args | srcInvalid "TooGeneric"
    h.writePointer choice (← h.functionPointer choice fnInstance) dest
  | .PointerCoercion .UnsafeFnPointer _ =>
    let value ← h.readImmediate choice source
    let .fnPointer ← h.typeInfo choice castTy | srcInvalid "unsafe fn pointer target is not fn pointer"
    h.writeImmediate choice value.imm dest
  | .PointerCoercion (.ClosureFnPointer _) _ =>
    h.ensureMonomorphic choice source.layout.ty
    let .closure definition args _ ← h.typeInfo choice source.layout.ty | srcInvalid "closure fn pointer on non-closure"
    let fnInstance ← h.resolveClosureFnOnce choice definition args
    h.writePointer choice (← h.functionPointer choice fnInstance) dest
  | .Transmute | .Subtype | .BoxDerefTransmute =>
    if !source.layout.layout.isSized || !destLayout.layout.isSized then srcInvalid "transmute requires sized types"
    if castTy != destLayout.ty then srcInvalid "transmute target type differs from destination"
    if source.layout.layout.size != destLayout.layout.size then throw (.undefinedBehavior "transmute size mismatch")
    if kind == .BoxDerefTransmute then
      let pointer ← h.readImmediate choice source
      let some pointee ← h.builtinDeref choice castTy true
        | srcInvalid "BoxDerefTransmute target is not dereferenceable"
      let box ← h.boxLayout choice pointee
      let pointer ← srcTransmuteImmediate h pointer box
      h.derefPointer choice ⟨.immediate pointer.imm, pointer.layout⟩
    h.copyAllowTransmute choice source dest

end CastCopies

/-! ### `Call.lean` -/

section CallCopies

variable {P S C E Other Extern FnABI ArgABI : Type}

/-- Verbatim copy of the private source helper `Call.require`. -/
def srcRequire (condition : Bool) (message : String) : CallM S Unit :=
  unless condition do throw (.invalidProgram message)

/-- Verbatim copy of the unpatched source `Call.evalCalleeAndArgs`
(`eval_callee_and_args`), base commit `b91fc2aa`. -/
def srcEvalCalleeAndArgs (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C)
    (func : MIR.Operand) (args : Array SpannedOperand) (dest : Place) :
    CallM S (EvaluatedCall P Other Extern FnABI) := do
  let func ← h.evalOperandAt choice (OperandPath.instruction "function") func
  let disjoint := Call.moveDefinitelyDisjoint args dest
  let mut evaluated := #[]
  for index in [:args.size] do
    let some arg := args[index]? | throw (.invalidProgram "missing source call argument")
    evaluated := evaluated.push (← Call.evalFnCallArgumentAt h choice arg.operand disjoint (OperandPath.argument index))
  let (inputCount, externAbi) ← h.functionSignature choice func.layout
  srcRequire (inputCount ≤ evaluated.size) "call has fewer args than normalized signature"
  let extra := (evaluated.extract inputCount evaluated.size).map fun arg => arg.layout.ty
  match ← h.functionKind func.layout.ty with
  | .FnPtr =>
    let fnPtr ← h.readPointer choice func
    let fnVal ← h.getPtrFn choice fnPtr
    let abi ← h.fnAbiOfFnPtr choice func.layout extra
    return ⟨fnVal, evaluated, externAbi, some abi, false⟩
  | .FnDef definition args =>
    let fnInstance ← h.resolve choice definition args
    let abi ← match fnInstance.kind with
      | .LlvmIntrinsic _ => pure none
      | .Intrinsic definition =>
        pure (some (← h.fnAbiOfInstance choice ⟨.Item definition, fnInstance.args⟩ extra))
      | _ => pure (some (← h.fnAbiOfInstance choice fnInstance extra))
    return ⟨.Instance fnInstance, evaluated, externAbi, abi, ← h.requiresCallerLocation fnInstance⟩
  | .invalid => throw (.invalidProgram "invalid callee type")

/-- Verbatim copy of the unpatched source `Call.passArgument`. -/
def srcPassArgument (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C)
    (caller : FnArg P) (callerAbi calleeAbi : ArgABI)
    (calleeIndex : Nat) (dest : Place) (calleeTy : TyId) (alreadyLive : Bool) : CallM S Unit := do
  srcRequire (calleeTy == (h.argLayout calleeAbi).ty) "callee type does not match ABI"
  srcRequire (caller.layout.layout == (h.argLayout callerAbi).layout) "caller layout does not match ABI"
  unless ← h.checkArgumentCompat choice callerAbi calleeAbi do
    throw (.undefinedBehavior s!"AbiMismatchArgument {calleeIndex}")
  let copied := caller.copyFnArg
  if !alreadyLive then
    srcRequire dest.projection.isEmpty "nonlocal destination in storage_live_dyn"
    srcRequire (!copied.metadata.hasMeta || copied.layout.ty == calleeTy) "argument metadata type mismatch"
    h.storageLiveDyn choice dest.localId copied.metadata
  let dest ← h.evalPlace choice dest false
  h.copyAllowTransmute choice copied dest
  if let .InPlace place := caller then h.protectArgument choice place

/-- Verbatim copy of the unpatched source `Call.evalCallTerminator`. -/
def srcEvalCallTerminator (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C)
    (budget : Nat) (terminator : Terminator) : CallM S Unit := do
  match terminator.kind with
  | .Call func args dest target unwind _ _ =>
    let oldIndex ← h.frameIndex
    let oldLoc := (← h.getFrame).location
    let destPlace ← h.evalPlace choice dest false
    let evaluated ← Call.evalCalleeAndArgs h choice func args dest
    Call.initFnCall h choice budget ⟨evaluated.callee, evaluated.callerAbi, evaluated.fnAbi, evaluated.args,
      evaluated.withCallerLocation, destPlace, target,
      if evaluated.fnAbi.any h.abiCanUnwind then unwind else .Unreachable⟩
    if target.isSome then
      if (← h.frameIndex) == oldIndex then
        if (← h.getFrame).location == oldLoc then
          throw (.invalidProgram "evaluating this call made no progress")
  | _ => throw (.invalidProgram "call hook received a non-Call terminator")

/-- Verbatim copy of the unpatched source `Call.evalTailCallTerminator`. -/
def srcEvalTailCallTerminator (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C)
    (budget : Nat) (terminator : Terminator) : CallM S Unit := do
  match terminator.kind with
  | .TailCall func args _ =>
    let oldIndex ← h.frameIndex
    let evaluated ← Call.evalCalleeAndArgs h choice func args ⟨0, #[]⟩
    Call.initFnTailCall h choice budget evaluated
    srcRequire ((← h.frameIndex) == oldIndex) "evaluating this tail call pushed a new stack frame"
  | _ => throw (.invalidProgram "tailCall hook received a non-TailCall terminator")

end CallCopies

end SourceCopies

section MiriFlagOff

open Miri.ABI Miri.Memory Miri.Interpreter

/-- `LocalAccess.evalOperand` with `deinitMovedPlace = false` is the unpatched
`Copy`/`Move`-sharing dispatch. -/
theorem localAccess_evalOperand_off {Prov Extra State : Type}
    (hooks : LocalAccessHooks Prov Extra State) (frame : Frame Prov LocalLayout Extra)
    (state : State) (operand : Miri.MIR.Operand) (known : Option LocalLayout)
    (hoff : hooks.deinitMovedPlace = false) :
    Miri.Interpreter.evalOperand hooks frame state operand known =
      match operand with
      | .Copy place | .Move place => Miri.Interpreter.evalPlaceToOp hooks frame state place known
      | .RuntimeChecks check => hooks.runtimeChecks frame state check
      | .Constant constant => hooks.constant frame state constant known := by
  cases operand <;> simp only [Miri.Interpreter.evalOperand, hoff, Bool.false_eq_true, ↓reduceIte]

/-- `LocalAccess.evalOperandImmediate` with `deinitMovedPlace = false` is the
unpatched read: no deinitialization write. -/
theorem localAccess_evalOperandImmediate_off {Prov Extra MemExtra Kind HookState ProvExtra : Type}
    [DecidableEq Kind] [DecidableEq Prov] [PointerProvenance Prov]
    (context : LocalReadContext Prov MemExtra Kind HookState ProvExtra)
    (hooks : LocalAccessHooks Prov Extra (LocalReadState Prov MemExtra Kind HookState))
    (frame : Frame Prov LocalLayout Extra) (state : LocalReadState Prov MemExtra Kind HookState)
    (operand : Miri.MIR.Operand) (known : Option LocalLayout)
    (hoff : hooks.deinitMovedPlace = false) :
    evalOperandImmediate context hooks frame state operand known =
      let evaluated := Miri.Interpreter.evalOperand hooks frame state operand known
      match evaluated.outcome with
      | .error e => ⟨evaluated.frame, evaluated.state, .error e⟩
      | .ok op =>
        let read := readTypedImmediate context evaluated.state.memory evaluated.state.hooks op
        ⟨evaluated.frame, ⟨read.memory, read.hooks, read.touched⟩,
          read.outcome.mapError LocalAccessError.memory⟩ := by
  simp only [evalOperandImmediate, hoff, Bool.false_eq_true, ↓reduceIte]
  rfl

variable {K User C : Type}

/-- `OperandMachine.evalOperand` with `deinitMovedPlace = false` is the unpatched
source dispatch (`Copy` and `Move` share `evalPlaceToOp`; no latch access). -/
theorem operandMachine_evalOperand_off (h : OperandMachine.Hooks K User C) (c : C)
    (operand : Miri.MIR.Operand) (known : Option LocalLayout)
    (hoff : h.deinitMovedPlace = false) :
    OperandMachine.evalOperand h c operand known =
      (match operand with
      | .Copy place | .Move place => OperandMachine.evalPlaceToOp h c place known
      | .Constant value => h.constant c value known
      | .RuntimeChecks checks => do
        let value ← h.runtimeChecks c checks
        let layout ← h.boolLayout c
        return ⟨.immediate (.scalar (.fromBool value)), layout⟩) := by
  cases operand <;> simp only [OperandMachine.evalOperand, hoff, Bool.false_eq_true, ↓reduceIte]

/-- `OperandMachine.evalOperandAt` with `deinitMovedPlace = false` is the
unpatched source dispatch. -/
theorem operandMachine_evalOperandAt_off (h : OperandMachine.Hooks K User C) (c : C)
    (path : OperandPath) (operand : Miri.MIR.Operand) (known : Option LocalLayout)
    (hoff : h.deinitMovedPlace = false) :
    OperandMachine.evalOperandAt h c path operand known =
      match operand with
      | .Constant value => h.constantAt c (path.push (.field "constant")) value known
      | _ => OperandMachine.evalOperand h c operand known := by
  cases operand <;> simp only [OperandMachine.evalOperandAt, hoff, Bool.false_eq_true, ↓reduceIte]

/-- `PlaceMachine.readImmediate` with `deinitMovedPlace = false` is the unpatched
source typed read: no latch access and no write. -/
theorem placeMachine_readImmediate_off [DecidableEq K] (config : PlaceMachine.AccessConfig K User)
    (operand : OpTy Provenance) (hoff : config.deinitMovedPlace = false) :
    PlaceMachine.readImmediate config operand = srcReadImmediate config operand := by
  simp only [PlaceMachine.readImmediate, hoff, Bool.false_eq_true, ↓reduceIte]
  unfold_named "_private.Miri.Interpreter.PlaceMachine.0.Miri.Interpreter.PlaceMachine.commit"
  unfold_named "_private.Miri.Interpreter.PlaceMachine.0.Miri.Interpreter.PlaceMachine.finish"
  unfold srcReadImmediate srcCommit srcFinish
  rfl

/-- `Place.copyRuntimePlaceNoValidate` with a disarmed latch is the unpatched
source `copy_op_no_validate`: no deinitialization and no overlap query. -/
theorem place_copyRuntimePlaceNoValidate_off {P S E : Type} (h : PlaceHooks P S C E)
    (copy : PlaceCopyHooks P S C) (choice : C) (source : OpTy P) (dest : RuntimePlace P)
    (allowTransmute : Bool) (htake : h.takePendingMoveDeinit = pure false) :
    copyRuntimePlaceNoValidate h copy choice source dest allowTransmute =
      srcCopyRuntimePlaceNoValidate h copy choice source dest allowTransmute := by
  unfold copyRuntimePlaceNoValidate srcCopyRuntimePlaceNoValidate srcPlaceLift
  unfold_named "_private.Miri.Interpreter.Place.0.Miri.Interpreter.placeLift"
  simp only [htake, pure_bind, Bool.false_eq_true, ↓reduceIte, bind_pure_unit]
  rfl

/-- The `PlaceMachine` place dictionary's latch is `pure false` (no state access)
when `deinitMovedPlace = false`. -/
theorem placeMachine_placeHooks_take_off [DecidableEq K]
    (access : PlaceMachine.AccessConfig K User) (allocation : PlaceMachine.AllocationConfig K User)
    (compiler : PlaceMachine.CompilerHooks K User C) (hoff : access.deinitMovedPlace = false) :
    (PlaceMachine.placeHooks access allocation compiler).takePendingMoveDeinit = pure false := by
  show PlaceMachine.takeLastMoveDeinit access.deinitMovedPlace = pure false
  rw [hoff]
  rfl

/-- `Cast.cast` is the unpatched source cast, verbatim (the patch adds the
separate consumer-side `Cast.castMoving`, selected by `ExecutionMachine` only
when `deinitMovedPlace = true`). -/
theorem cast_eq_src {P S V : Type} [PointerProvenance P] (h : CastHooks P S C V)
    (choice : C) (fuel : Nat) (source : OpTy P) (kind : Miri.MIR.CastKind) (castTy : Miri.MIR.TyId)
    (dest : V) :
    Cast.cast h choice fuel source kind castTy dest = srcCast h choice fuel source kind castTy dest := by
  unfold Cast.cast srcCast
  unfold_named "_private.Miri.Interpreter.Cast.0.Miri.Interpreter.Cast.readPointer"
  unfold_named "_private.Miri.Interpreter.Cast.0.Miri.Interpreter.Cast.transmuteImmediate"
  unfold_named "_private.Miri.Interpreter.Cast.0.Miri.Interpreter.Cast.scalarOf"
  unfold_named "_private.Miri.Interpreter.Cast.0.Miri.Interpreter.Cast.liftResult"
  unfold_named "_private.Miri.Interpreter.Cast.0.Miri.Interpreter.Cast.invalid"
  unfold srcReadPointer srcTransmuteImmediate srcScalarOf srcLiftResult srcInvalid
  rfl

/-- The consumer-side `Cast.castMoving` with a disarmed latch hook is the source
cast: the deinitialization hook is never invoked and the latch hand-off is a
no-op. -/
theorem castMoving_off {P S V : Type} [PointerProvenance P] (h : CastHooks P S C V)
    (choice : C) (fuel : Nat) (source : OpTy P) (kind : Miri.MIR.CastKind) (castTy : Miri.MIR.TyId)
    (dest : V) (htake : h.takePendingMoveDeinit = pure false)
    (hrestore : h.restorePendingMoveDeinit false = pure ()) :
    Cast.castMoving h choice fuel source kind castTy dest =
      srcCast h choice fuel source kind castTy dest := by
  unfold Cast.castMoving srcCast
  unfold_named "_private.Miri.Interpreter.Cast.0.Miri.Interpreter.Cast.readPointer"
  unfold_named "_private.Miri.Interpreter.Cast.0.Miri.Interpreter.Cast.transmuteImmediate"
  unfold_named "_private.Miri.Interpreter.Cast.0.Miri.Interpreter.Cast.scalarOf"
  unfold_named "_private.Miri.Interpreter.Cast.0.Miri.Interpreter.Cast.liftResult"
  unfold_named "_private.Miri.Interpreter.Cast.0.Miri.Interpreter.Cast.invalid"
  unfold srcReadPointer srcTransmuteImmediate srcScalarOf srcLiftResult srcInvalid
  simp only [htake, hrestore, pure_bind, Bool.false_eq_true, ↓reduceIte]
  rfl

variable {P S E Other Extern FnABI ArgABI : Type}

/-- `Call.evalFnCallArgumentAt` is the unpatched source argument evaluation (lazy
`Copy` handles, `InPlace` moves) for every hook dictionary; the consumer-side
argument evaluation is the separate `Call.evalFnCallArgumentMoving`. -/
theorem call_evalFnCallArgumentAt_eq_src (h : CallHooks P S C E Other Extern FnABI ArgABI)
    (choice : C) (operand : Miri.MIR.Operand) (disjoint : Bool) (path : OperandPath) :
    Call.evalFnCallArgumentAt h choice operand disjoint path = (do
      match operand with
      | .Copy _ | .Constant _ | .RuntimeChecks _ => return .Copy (← h.evalOperandAt choice path operand)
      | .Move place =>
        let place ← h.evalPlace choice place true
        if disjoint then
          let op ← h.placeToOp choice place
          match op.op with
          | .indirect mplace => return .InPlace ⟨mplace, op.layout⟩
          | .immediate _ => return .Copy op
        else return .InPlace (← h.forceAllocation choice place)) := by
  cases operand <;> rfl

/-- `Call.evalCalleeAndArgs` is the unpatched source `eval_callee_and_args`; the
consumer-side evaluation is the separate `Call.evalCalleeAndArgsMoving`. -/
theorem call_evalCalleeAndArgs_eq_src (h : CallHooks P S C E Other Extern FnABI ArgABI)
    (choice : C) (func : Miri.MIR.Operand) (args : Array Miri.MIR.SpannedOperand)
    (dest : Miri.MIR.Place) :
    Call.evalCalleeAndArgs h choice func args dest = srcEvalCalleeAndArgs h choice func args dest := by
  unfold Call.evalCalleeAndArgs srcEvalCalleeAndArgs srcRequire
  unfold_named "_private.Miri.Interpreter.Call.0.Miri.Interpreter.Call.require"
  rfl

/-- `Call.passArgument` is the unpatched source `pass_argument` (an in-place
argument is protected). The consumer-side call path passes no argument in
place. -/
theorem call_passArgument_eq_src (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C)
    (caller : FnArg P) (callerAbi calleeAbi : ArgABI) (calleeIndex : Nat) (dest : Miri.MIR.Place)
    (calleeTy : Miri.MIR.TyId) (alreadyLive : Bool) :
    Call.passArgument h choice caller callerAbi calleeAbi calleeIndex dest calleeTy alreadyLive =
      srcPassArgument h choice caller callerAbi calleeAbi calleeIndex dest calleeTy alreadyLive := by
  unfold Call.passArgument srcPassArgument srcRequire
  unfold_named "_private.Miri.Interpreter.Call.0.Miri.Interpreter.Call.require"
  rfl

/-- `Call.evalCallTerminator` is the unpatched source call terminator; the
consumer-side terminator is the separate `Call.evalCallTerminatorMoving`. -/
theorem call_evalCallTerminator_eq_src (h : CallHooks P S C E Other Extern FnABI ArgABI)
    (choice : C) (budget : Nat) (terminator : Miri.MIR.Terminator) :
    Call.evalCallTerminator h choice budget terminator =
      srcEvalCallTerminator h choice budget terminator := by
  unfold Call.evalCallTerminator srcEvalCallTerminator
  rfl

/-- `Call.evalTailCallTerminator` is the unpatched source tail-call terminator;
the consumer-side terminator is the separate `Call.evalTailCallTerminatorMoving`. -/
theorem call_evalTailCallTerminator_eq_src (h : CallHooks P S C E Other Extern FnABI ArgABI)
    (choice : C) (budget : Nat) (terminator : Miri.MIR.Terminator) :
    Call.evalTailCallTerminator h choice budget terminator =
      srcEvalTailCallTerminator h choice budget terminator := by
  unfold Call.evalTailCallTerminator srcEvalTailCallTerminator srcRequire
  unfold_named "_private.Miri.Interpreter.Call.0.Miri.Interpreter.Call.require"
  rfl

end MiriFlagOff

section MiriFlagOffMachine

open Miri.ABI Miri.Memory Miri.Interpreter

variable {K U C O X Host : Type}

/-- The executor's place dictionary (`ExecutionMachine.projectionHooks`, used by
copies, casts and `Repeat`) has a disarmed latch when both consumer-side flags
are off, so `place_copyRuntimePlaceNoValidate_off` and `castMoving_off` apply. -/
theorem executionMachine_projectionHooks_take_off [DecidableEq K]
    (h : ExecutionMachine.Config K U C O X Host) (hoff : h.deinitMovedPlace = false)
    (hoff' : h.access.deinitMovedPlace = false) :
    (ExecutionMachine.projectionHooks h).place.takePendingMoveDeinit = pure false := by
  show PlaceMachine.takeLastMoveDeinit (h.deinitMovedPlace || h.access.deinitMovedPlace) = pure false
  rw [hoff, hoff']
  rfl

end MiriFlagOffMachine

/-! ## Part 3: patched `lean-miri` with `deinitMovedPlace = true` -/

section MiriFlagOn

open Miri.ABI Miri.Memory Miri.Interpreter

/-! ### Tree-Borrows-silent and race-silent deinitialization hooks -/

/-- The deinitialization hooks perform no allocation-access effect. -/
theorem tbSilentAccessHooks_beforeAllocationAccess {Prov MemExtra Kind HookState ProvExtra : Type}
    (hooks : AllocationAccessHooks Prov MemExtra Kind HookState ProvExtra) (state : HookState)
    (id : AllocId) :
    (tbSilentAccessHooks hooks).beforeAllocationAccess state id = ⟨state, .ok ()⟩ := rfl

/-- The deinitialization hooks perform no read access: the allocation extra (the
Tree Borrows tree) and the hook state are returned unchanged. -/
theorem tbSilentAccessHooks_beforeMemoryRead {Prov MemExtra Kind HookState ProvExtra : Type}
    (hooks : AllocationAccessHooks Prov MemExtra Kind HookState ProvExtra) (state : HookState)
    (extra : MemExtra) (ptr : Pointer (Option Prov)) (id : AllocId) (prov : ProvExtra)
    (range : AllocRange) :
    (tbSilentAccessHooks hooks).beforeMemoryRead state extra ptr id prov range =
      ⟨state, extra, .ok ()⟩ := rfl

/-- The deinitialization hooks perform no write access: the allocation extra (the
Tree Borrows tree) and the hook state (data-race clocks, weak memory) are
returned unchanged, so no sibling `Frozen` tag can be disabled by a move. -/
theorem tbSilentAccessHooks_beforeMemoryWrite {Prov MemExtra Kind HookState ProvExtra : Type}
    (hooks : AllocationAccessHooks Prov MemExtra Kind HookState ProvExtra) (state : HookState)
    (extra : MemExtra) (ptr : Pointer (Option Prov)) (id : AllocId) (prov : ProvExtra)
    (range : AllocRange) :
    (tbSilentAccessHooks hooks).beforeMemoryWrite state extra ptr id prov range =
      ⟨state, extra, .ok ()⟩ := rfl

/-- The deinitialization hooks resolve pointers exactly like the source hooks. -/
theorem tbSilentAccessHooks_resolvePointer {Prov MemExtra Kind HookState ProvExtra : Type}
    (hooks : AllocationAccessHooks Prov MemExtra Kind HookState ProvExtra) :
    (tbSilentAccessHooks hooks).resolvePointer = hooks.resolvePointer := rfl

variable {K User C : Type}

/-- `PlaceMachine.rawAccessHooks` are the silent version of the source hooks. -/
theorem placeMachine_rawAccessHooks_eq (config : PlaceMachine.AccessConfig K User) :
    PlaceMachine.rawAccessHooks config = tbSilentAccessHooks (PlaceMachine.accessHooks config) := rfl

/-- `PlaceMachine.writeMemoryRawUninit` is the source `uninit` writer
`writeImmediateToMplaceNoValidate` over the silent hooks (no Tree Borrows
`.Write`, no race write), committing only the written memory. -/
theorem placeMachine_writeMemoryRawUninit_eq [DecidableEq K]
    (config : PlaceMachine.AccessConfig K User) (place : MPlaceTy Provenance) :
    PlaceMachine.writeMemoryRawUninit config place = (do
      let state ← get
      let result := writeImmediateToMplaceNoValidate state.machine.memory ⟨state.machine, none⟩ .uninit
        ⟨place.mplace, localMemoryLayout place.layout⟩ config.runtime config.ghostMode config.globalKind
        config.globalHooks (tbSilentAccessHooks (PlaceMachine.accessHooks config)) config.dynamicLayout
        (fun _ => false)
      modify fun s => { s with machine := { result.hooks.machine with memory := result.memory } }
      srcFinish config result.hooks result.outcome) := by
  unfold PlaceMachine.writeMemoryRawUninit srcFinish
  unfold_named "_private.Miri.Interpreter.PlaceMachine.0.Miri.Interpreter.PlaceMachine.finish"
  rfl

/-- **Contrast (Finding 1).** The source write hook used by
`PlaceMachine.writeMemory` (and hence by the `d9b41b58b`/`dda03e8b`
deinitialization paths) performs a Tree Borrows `.Write` over the accessed range
whenever borrow tracking is enabled: the returned allocation extra is the tree
after `performBorrowAccessRange … .Write`, whatever the access status. The
consumer-side deinitialization hooks return the tree unchanged
(`tbSilentAccessHooks_beforeMemoryWrite`). -/
theorem placeMachine_accessHooks_write_performs_treeBorrows_write
    (config : PlaceMachine.AccessConfig K User) (state : PlaceMachine.AccessState K User)
    (tree : Miri.TreeBorrows.BorrowTree) (ptr : Pointer (Option Provenance)) (id : AllocId)
    (prov : ProvenanceExtra) (range : AllocRange) (tracker : MachineHooks.BorrowState)
    (hdiag : config.diagnostic true id range state.machine = .ok () state.machine)
    (hrace : MachineHooks.memoryRaceAccess state.machine id range (some .Write) .Read =
      (state.machine, .ok ()))
    (hweak : config.weakMemoryWrite id range state.machine = .ok () state.machine)
    (htracker : state.machine.borrowTracker = some tracker) :
    ((PlaceMachine.accessHooks config).beforeMemoryWrite state tree ptr id prov range).extra =
      (tree.performBorrowAccessRange prov range.start range.size .Write
        tracker.global.protectedTags .VisitChildrenOfAccessed).tree := by
  show (PlaceMachine.memoryAccess config true state tree id prov range).extra = _
  unfold PlaceMachine.memoryAccess
  unfold_named "_private.Miri.Interpreter.PlaceMachine.0.Miri.Interpreter.PlaceMachine.bridge"
  simp only [Id.run, hdiag, hrace, hweak, htracker, ↓reduceIte]
  split <;> rfl

end MiriFlagOn

/-! ### The move read is the copy read plus a silent deinitialization -/

section ReadDecomposition

open Miri.ABI Miri.Memory Miri.Interpreter

variable {K User C : Type}

/-- **Read-then-deinitialize decomposition.** With `deinitMovedPlace = true`,
`PlaceMachine.readImmediate` consumes this operand's latch record, performs
*exactly* the unpatched source read `srcReadImmediate` (with its Tree Borrows and
race read accesses; `placeMachine_readImmediate_off`), and then — for a moved
indirect operand only — deinitializes the source with `writeMemoryRawUninit`,
whose hooks perform no Tree Borrows or race access
(`placeMachine_writeMemoryRawUninit_eq`, `tbSilentAccessHooks_beforeMemoryWrite`).
Hence the borrow-tracker effect of a moved read equals that of the copy read. -/
theorem placeMachine_readImmediate_moving [DecidableEq K]
    (config : PlaceMachine.AccessConfig K User) (operand : OpTy Provenance)
    (hon : config.deinitMovedPlace = true) :
    PlaceMachine.readImmediate config operand = (do
      let state ← get
      let (machine', shouldDeinit) :=
        match operand.op with
        | .indirect mplace => MachineHooks.takePendingMoveDeinitFor state.machine (some mplace)
        | .immediate _ => MachineHooks.takePendingMoveDeinitFor state.machine none
      set { state with machine := machine' }
      let value ← srcReadImmediate config operand
      if shouldDeinit then
        if let .indirect mplace := operand.op then
          PlaceMachine.writeMemoryRawUninit config ⟨mplace, operand.layout⟩
      return value) := by
  simp only [PlaceMachine.readImmediate, hon, ↓reduceIte, PlaceMachine.readImmediateMoving]
  unfold_named "_private.Miri.Interpreter.PlaceMachine.0.Miri.Interpreter.PlaceMachine.commit"
  unfold_named "_private.Miri.Interpreter.PlaceMachine.0.Miri.Interpreter.PlaceMachine.finish"
  unfold srcReadImmediate srcCommit srcFinish
  simp only [bind_assoc, pure_bind]
  rfl

/-- The latch queue installed by `withPendingMoves`. -/
theorem pendingMoveDeinits_withPendingMoves (m : MachineHooks.MachineState K User) (flag : Bool)
    (queue : Array (MemPlace Provenance × Bool)) :
    (m.withPendingMoves flag queue).pendingMoveDeinits = queue := rfl

/-- The latch flag installed by `withPendingMoves`. -/
theorem pendingMoveDeinit_withPendingMoves (m : MachineHooks.MachineState K User) (flag : Bool)
    (queue : Array (MemPlace Provenance × Bool)) :
    (m.withPendingMoves flag queue).pendingMoveDeinit = flag := rfl

/-- An immediate operand never requests deinitialization (it only disarms the flag). -/
theorem takePendingMoveDeinitFor_immediate (m : MachineHooks.MachineState K User) :
    MachineHooks.takePendingMoveDeinitFor m none = (MachineHooks.clearPendingMoveDeinitFlag m, false) :=
  rfl

/-- The front record for the read place is consumed (and the flag disarmed); it
requests deinitialization exactly when it is a move record. In particular a copy
record (`isMove = false`) never deinitializes. -/
theorem takePendingMoveDeinitFor_front (m : MachineHooks.MachineState K User)
    (mplace : MemPlace Provenance) (isMove flag : Bool) (rest : List (MemPlace Provenance × Bool)) :
    MachineHooks.takePendingMoveDeinitFor (m.withPendingMoves flag ⟨(mplace, isMove) :: rest⟩)
        (some mplace) =
      ((m.withPendingMoves flag ⟨(mplace, isMove) :: rest⟩).withPendingMoves false
        ((⟨(mplace, isMove) :: rest⟩ : Array (MemPlace Provenance × Bool)).eraseIdxIfInBounds 0),
        isMove) := by
  simp [MachineHooks.takePendingMoveDeinitFor, pendingMoveDeinits_withPendingMoves]

/-- With an empty queue no indirect read deinitializes. -/
theorem takePendingMoveDeinitFor_empty (m : MachineHooks.MachineState K User)
    (mplace : MemPlace Provenance) (flag : Bool) :
    (MachineHooks.takePendingMoveDeinitFor (m.withPendingMoves flag #[]) (some mplace)).2 = false := by
  simp [MachineHooks.takePendingMoveDeinitFor, pendingMoveDeinits_withPendingMoves]

end ReadDecomposition

/-! ### Operand latch behavior of `OperandMachine.evalOperand` -/

section OperandLatch

open Miri.ABI Miri.Memory Miri.Interpreter

variable {K User C : Type}

/-- **Indirect move.** With `deinitMovedPlace = true`, `Move` of a place that
evaluates to memory queues `(mplace, true)` for the consuming read/copy/cast. -/
theorem operandMachine_evalOperand_move_indirect (h : OperandMachine.Hooks K User C) (c : C)
    (place : Miri.MIR.Place) (known : Option LocalLayout) (s s₁ : MachineHooks.State K User)
    (mplace : MemPlace Provenance) (layout : LocalLayout) (hon : h.deinitMovedPlace = true)
    (heval : OperandMachine.evalPlaceToOp h c place known
      { s with machine := MachineHooks.clearPendingMoveDeinitFlag s.machine } =
        .ok ⟨.indirect mplace, layout⟩ s₁) :
    OperandMachine.evalOperand h c (.Move place) known s =
      .ok ⟨.indirect mplace, layout⟩
        { s₁ with machine := MachineHooks.recordPendingMoveDeinit s₁.machine mplace true } := by
  simp only [OperandMachine.evalOperand, hon, ↓reduceIte]
  show (OperandMachine.evalOperandMoving h c (.Move place) known) s = _
  simp only [OperandMachine.evalOperandMoving, OperandMachine.updateMoveLatch, bind, EStateM.bind,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, heval]
  rfl

/-- **Indirect copy.** With `deinitMovedPlace = true`, `Copy` of a memory place
queues the non-move record `(mplace, false)`, which never deinitializes. -/
theorem operandMachine_evalOperand_copy_indirect (h : OperandMachine.Hooks K User C) (c : C)
    (place : Miri.MIR.Place) (known : Option LocalLayout) (s s₁ : MachineHooks.State K User)
    (mplace : MemPlace Provenance) (layout : LocalLayout) (hon : h.deinitMovedPlace = true)
    (heval : OperandMachine.evalPlaceToOp h c place known
      { s with machine := MachineHooks.clearPendingMoveDeinitFlag s.machine } =
        .ok ⟨.indirect mplace, layout⟩ s₁) :
    OperandMachine.evalOperand h c (.Copy place) known s =
      .ok ⟨.indirect mplace, layout⟩
        { s₁ with machine := MachineHooks.recordPendingMoveDeinit s₁.machine mplace false } := by
  simp only [OperandMachine.evalOperand, hon, ↓reduceIte]
  show (OperandMachine.evalOperandMoving h c (.Copy place) known) s = _
  simp only [OperandMachine.evalOperandMoving, OperandMachine.updateMoveLatch, bind, EStateM.bind,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, heval]
  rfl

/-- The empty projection list is empty (`Place.projection.isEmpty` on a root place). -/
theorem array_isEmpty_empty {α : Type} : (#[] : Array α).isEmpty = true := rfl

/-- **Unprojected immediate move.** With `deinitMovedPlace = true`, `Move _l` of a
non-zero-sized immediate local returns the read value, replaces the local with
`.live (.immediate .uninit)` in the current frame, and disarms the latch flag. -/
theorem operandMachine_evalOperand_move_immediate_root (h : OperandMachine.Hooks K User C)
    (c : C) (l : Miri.MIR.LocalId) (known : Option LocalLayout) (s s₁ s₂ : MachineHooks.State K User)
    (v : Immediate Provenance) (layout : LocalLayout)
    (frame frame' : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (hon : h.deinitMovedPlace = true)
    (heval : OperandMachine.evalPlaceToOp h c ⟨l, #[]⟩ known
      { s with machine := MachineHooks.clearPendingMoveDeinitFlag s.machine } =
        .ok ⟨.immediate v, layout⟩ s₁)
    (hzst : layout.layout.isZst = false)
    (hcur : MachineHooks.currentFrame s₁ = .ok frame s₁)
    (hrep : frame.replaceLocalValue l (.live (.immediate .uninit)) = .ok frame')
    (hset : MachineHooks.setCurrentFrame frame' s₁ = .ok () s₂) :
    OperandMachine.evalOperand h c (.Move ⟨l, #[]⟩) known s =
      .ok ⟨.immediate v, layout⟩
        { s₂ with machine := MachineHooks.clearPendingMoveDeinitFlag s₂.machine } := by
  simp only [OperandMachine.evalOperand, hon, ↓reduceIte]
  show (OperandMachine.evalOperandMoving h c (.Move ⟨l, #[]⟩) known) s = _
  simp only [OperandMachine.evalOperandMoving, OperandMachine.updateMoveLatch, bind, EStateM.bind,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, heval]
  unfold_named "_private.Miri.Interpreter.OperandMachine.0.Miri.Interpreter.OperandMachine.stack"
  unfold_named "_private.Miri.Interpreter.OperandMachine.0.Miri.Interpreter.OperandMachine.lift"
  simp only [array_isEmpty_empty, hzst, Bool.false_eq_true, ↓reduceIte, EStateM.bind, hcur, hrep,
    Except.mapError, pure, EStateM.pure, hset, EStateM.modifyGet]

/-- **Projected immediate move, universal.** With `deinitMovedPlace = true`,
`Move place` on a non-empty projection (`place.projection.isEmpty = false`) of a
non-zero-sized immediate local materializes the base local (`localToPlace` +
`forceAllocation`), re-evaluates `place` to `.indirect mplace`, and queues
`(mplace, true)` in `pendingMoveDeinits`. -/
theorem operandMachine_evalOperand_move_projected_immediate (h : OperandMachine.Hooks K User C)
    (c : C) (place : Miri.MIR.Place) (known : Option LocalLayout)
    (s s₁ s₂ s₃ s₄ : MachineHooks.State K User)
    (v : Immediate Provenance) (layout layout' : LocalLayout)
    (basePlace : RuntimePlace Provenance) (forced : MPlaceTy Provenance)
    (mplace : MemPlace Provenance)
    (hon : h.deinitMovedPlace = true)
    (hproj : place.projection.isEmpty = false)
    (hzst : layout.layout.isZst = false)
    (heval₁ : OperandMachine.evalPlaceToOp h c place known
      { s with machine := MachineHooks.clearPendingMoveDeinitFlag s.machine } =
        .ok ⟨.immediate v, layout⟩ s₁)
    (hloc : localToPlace h.projection.place c place.localId s₁ = .ok basePlace s₂)
    (hforce : forceAllocation h.projection.place c basePlace s₂ = .ok forced s₃)
    (heval₂ : OperandMachine.evalPlaceToOp h c place known s₃ =
      .ok ⟨.indirect mplace, layout'⟩ s₄) :
    OperandMachine.evalOperand h c (.Move place) known s =
      .ok ⟨.indirect mplace, layout'⟩
        { s₄ with machine := MachineHooks.recordPendingMoveDeinit s₄.machine mplace true } := by
  simp only [OperandMachine.evalOperand, hon, ↓reduceIte]
  show (OperandMachine.evalOperandMoving h c (.Move place) known) s = _
  simp only [OperandMachine.evalOperandMoving, OperandMachine.updateMoveLatch, bind, EStateM.bind,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, heval₁, hproj, hzst,
    Bool.false_eq_true, ↓reduceIte, hloc, hforce, heval₂]
  rfl

end OperandLatch

/-! ### Operand reads: `evalOperandAt` followed by `readImmediate`

`ExecutionMachine.stepHooks` reads the `SwitchInt` discriminant and the `Assert`
condition, and `evalRvalueIntoPlace` reads `UnaryOp`/`BinaryOp` operands, as
`PlaceMachine.readImmediate (← OperandMachine.evalOperandAt …)`. -/

section OperandReads

open Miri.ABI Miri.Memory Miri.Interpreter

variable {K User C : Type}

/-- **Non-`count` operand paths.** With `deinitMovedPlace = true`,
`OperandMachine.evalOperandAt` on every path other than `CopyNonOverlapping`'s
`count` (in particular the `SwitchInt` discriminant, the `Assert` condition and
rvalue operands) evaluates a moved place exactly as `OperandMachine.evalOperand`. -/
theorem operandMachine_evalOperandAt_move_eq_evalOperand (h : OperandMachine.Hooks K User C) (c : C)
    (path : OperandPath) (place : Miri.MIR.Place) (known : Option LocalLayout)
    (hon : h.deinitMovedPlace = true)
    (hpath : (path == OperandPath.instruction "count") = false) :
    OperandMachine.evalOperandAt h c path (.Move place) known =
      OperandMachine.evalOperand h c (.Move place) known := by
  simp only [OperandMachine.evalOperandAt, OperandMachine.evalOperand, hon, ↓reduceIte,
    OperandMachine.evalOperandAtMoving, hpath, Bool.false_eq_true, bind_pure]

/-- **Operand read of a moved memory place (`SwitchInt` discriminant, `Assert`
condition, `UnaryOp`/`BinaryOp` operands), universal.** With
`deinitMovedPlace = true` on both dictionaries, `move place` of a memory place
queues `(mplace, true)` (`OperandMachine.evalOperandAt` on a non-`count` path is
`OperandMachine.evalOperand`), and
`PlaceMachine.readImmediate` consumes the record, performs the unchanged source
read, and deinitializes the whole moved place `⟨mplace, layout⟩` with the
Tree-Borrows-silent `writeMemoryRawUninit`: the state the read returns, from
which `ExecutionMachine.stepHooks` branches (`stepHooks_switchInt_otherwise`), has
the moved place deinitialized. -/
theorem operandRead_move_indirect [DecidableEq K]
    (opHooks : OperandMachine.Hooks K User C) (config : PlaceMachine.AccessConfig K User)
    (c : C) (path : OperandPath) (place : Miri.MIR.Place) (known : Option LocalLayout)
    (s s₁ s₂ s₃ : MachineHooks.State K User) (mplace : MemPlace Provenance) (layout : LocalLayout)
    (val : RvalueImmTy Provenance)
    (hopOn : opHooks.deinitMovedPlace = true) (hcfgOn : config.deinitMovedPlace = true)
    (hpath : (path == OperandPath.instruction "count") = false)
    (hqueueEmpty : s₁.machine.pendingMoveDeinits = #[])
    (hevalPlace : OperandMachine.evalPlaceToOp opHooks c place known
      { s with machine := MachineHooks.clearPendingMoveDeinitFlag s.machine } =
        .ok ⟨.indirect mplace, layout⟩ s₁)
    (hreadMiri : srcReadImmediate config ⟨.indirect mplace, layout⟩
      { s₁ with
        machine :=
          MachineHooks.MachineState.withPendingMoves
            (MachineHooks.MachineState.withPendingMoves s₁.machine true #[(mplace, true)])
            false
            ((#[(mplace, true)] : Array (MemPlace Provenance × Bool)).eraseIdxIfInBounds 0) } =
        .ok val s₂)
    (hdeinitMiri : PlaceMachine.writeMemoryRawUninit config ⟨mplace, layout⟩ s₂ = .ok () s₃) :
    (do
      let op ← OperandMachine.evalOperandAt opHooks c path (.Move place) known
      PlaceMachine.readImmediate config op) s = .ok val s₃ := by
  rw [operandMachine_evalOperandAt_move_eq_evalOperand opHooks c path place known hopOn hpath]
  have hop := operandMachine_evalOperand_move_indirect opHooks c place known s s₁ mplace layout
    hopOn hevalPlace
  simp only [bind, EStateM.bind, hop]
  rw [placeMachine_readImmediate_moving config ⟨.indirect mplace, layout⟩ hcfgOn]
  simp only [MachineHooks.recordPendingMoveDeinit, hqueueEmpty, Array.push_empty]
  have htake := takePendingMoveDeinitFor_front s₁.machine mplace true true []
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, set,
    MonadStateOf.set, EStateM.set, htake, ↓reduceIte, hreadMiri, hdeinitMiri, pure,
    EStateM.pure]

/-- **`SwitchInt` discriminant read of a moved unprojected immediate local,
universal.** The local is replaced by `.live (.immediate .uninit)` at evaluation
(`operandMachine_evalOperand_move_immediate_root`), before the read, which then
reads the returned immediate without any memory deinitialization
(`takePendingMoveDeinitFor_immediate`). -/
theorem discriminantRead_move_immediate_root [DecidableEq K]
    (opHooks : OperandMachine.Hooks K User C) (config : PlaceMachine.AccessConfig K User)
    (c : C) (path : OperandPath) (l : Miri.MIR.LocalId)
    (s s₁ s₂ : MachineHooks.State K User) (v : Immediate Provenance) (layout : LocalLayout)
    (frame frame' : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (hopOn : opHooks.deinitMovedPlace = true)
    (hpath : (path == OperandPath.instruction "count") = false)
    (heval : OperandMachine.evalPlaceToOp opHooks c ⟨l, #[]⟩ none
      { s with machine := MachineHooks.clearPendingMoveDeinitFlag s.machine } =
        .ok ⟨.immediate v, layout⟩ s₁)
    (hzst : layout.layout.isZst = false)
    (hcur : MachineHooks.currentFrame s₁ = .ok frame s₁)
    (hrep : frame.replaceLocalValue l (.live (.immediate .uninit)) = .ok frame')
    (hset : MachineHooks.setCurrentFrame frame' s₁ = .ok () s₂) :
    (do
      let op ← OperandMachine.evalOperandAt opHooks c path (.Move ⟨l, #[]⟩) none
      PlaceMachine.readImmediate config op) s =
      PlaceMachine.readImmediate config ⟨.immediate v, layout⟩
        { s₂ with machine := MachineHooks.clearPendingMoveDeinitFlag s₂.machine } := by
  rw [operandMachine_evalOperandAt_move_eq_evalOperand opHooks c path ⟨l, #[]⟩ none hopOn hpath]
  have hop := operandMachine_evalOperand_move_immediate_root opHooks c l none s s₁ s₂ v layout
    frame frame' hopOn heval hzst hcur hrep hset
  simp only [bind, EStateM.bind, hop]

end OperandReads

/-! ### Step boundaries -/

section StepLatch

open Miri.ABI Miri.Memory Miri.Interpreter

variable {K U C O X Host : Type}

/-- **`step_clears_pendingMoveDeinit`.** Every `ExecutionMachine.step` leaves the
consumer-side latch disarmed, whatever the configuration and outcome. -/
theorem step_clears_pendingMoveDeinit [DecidableEq K]
    (h : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits) (c : C)
    (state : MachineHooks.State K U) :
    (ExecutionMachine.step h limits c state).1.machine.pendingMoveDeinit = false ∧
    (ExecutionMachine.step h limits c state).1.machine.pendingMoveDeinits = #[] := by
  simp only [ExecutionMachine.step]
  constructor <;> rfl

/-- **Entry clearing.** A step never observes a latch armed before it began. -/
theorem step_ignores_entry_latch [DecidableEq K]
    (h : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits) (c : C)
    (state : MachineHooks.State K U) :
    ExecutionMachine.step h limits c state =
      ExecutionMachine.step h limits c
        { state with machine := MachineHooks.clearPendingMoveDeinits state.machine } := rfl

end StepLatch

/-! ### `SwitchInt` in the assembled executor -/

section SwitchIntWiring

open Miri.ABI Miri.Memory Miri.Interpreter

variable {K U C O X Host : Type}

/-- The `SwitchInt` discriminant read of `ExecutionMachine.stepHooks`. -/
def stepSwitchDiscriminantRead [DecidableEq K] (h : ExecutionMachine.Config K U C O X Host)
    (limits : ExecutionMachine.Limits) (c : C) (discr : Miri.MIR.Operand) :
    MachineHooks.M K U (RvalueImmTy Provenance) := do
  let op ← OperandMachine.evalOperandAt
    (ExecutionMachine.operandHooks (ExecutionMachine.withValidation h limits)) c
    (OperandPath.instruction "discriminant") discr none
  PlaceMachine.readImmediate (ExecutionMachine.withValidation h limits).access op

/-- **A faulting discriminant read faults the `SwitchInt` terminator of the
assembled executor, universal.** `ExecutionMachine.stepHooks` evaluates the
discriminant with the consumer-side `OperandMachine.evalOperandAt` and reads it with
`PlaceMachine.readImmediate` (`stepSwitchDiscriminantRead`), whatever the
configuration: a discriminant read that faults — for example re-reading a place
deinitialized by an earlier move — faults the terminator with the read's state,
and no branch is taken. -/
theorem stepHooks_switchInt_discriminant_error [DecidableEq K]
    (h : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits) (c : C)
    (src : Miri.MIR.SourceInfo) (discr : Miri.MIR.Operand) (targets : Miri.MIR.SwitchTargets)
    (state state' : MachineHooks.State K U) (e : StepError)
    (hread : stepSwitchDiscriminantRead h limits c discr state = .error e state') :
    (ExecutionMachine.stepHooks h limits).terminator c ⟨src, .SwitchInt discr targets⟩ state =
      (state', .error e) := by
  have hrun : MachineHooks.run (stepSwitchDiscriminantRead h limits c discr) state =
      (state', .error e) := by
    simp only [MachineHooks.run, Call.run, hread]
  unfold stepSwitchDiscriminantRead at hrun
  unfold ExecutionMachine.stepHooks
  dsimp only
  split <;> (simp only [ControlFlow.evalTerminator]; rw [hrun]; rfl)

/-- **The `SwitchInt` branch of the assembled executor is taken from the state
after the discriminant read, universal.** When the discriminant read
(`stepSwitchDiscriminantRead`) succeeds with state `state'` — for `move place`, the
state in which `place` is deinitialized (`operandRead_move_indirect`,
`discriminantRead_move_immediate_root`) — a `SwitchInt` without matching cases
jumps to `otherwise` in exactly that state. -/
theorem stepHooks_switchInt_otherwise [DecidableEq K]
    (h : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits) (c : C)
    (src : Miri.MIR.SourceInfo) (discr : Miri.MIR.Operand) (targets : Miri.MIR.SwitchTargets)
    (state state' : MachineHooks.State K U) (v : RvalueImmTy Provenance)
    (hread : stepSwitchDiscriminantRead h limits c discr state = .ok v state')
    (hcases : targets.cases = #[]) :
    (ExecutionMachine.stepHooks h limits).terminator c ⟨src, .SwitchInt discr targets⟩ state =
      ControlFlow.goToBlock targets.otherwise state' := by
  have hrun : MachineHooks.run (stepSwitchDiscriminantRead h limits c discr) state =
      (state', .ok v) := by
    simp only [MachineHooks.run, Call.run, hread]
  unfold stepSwitchDiscriminantRead at hrun
  unfold ExecutionMachine.stepHooks
  dsimp only
  split <;> (simp only [ControlFlow.evalTerminator]; rw [hrun]; simp only [hcases]; rfl)

end SwitchIntWiring

/-! ### Call arguments: consumption, deinitialization and pre-resolution validation -/

section CallArgs

open Miri.ABI Miri.Memory Miri.Interpreter

variable {P S C E Other Extern FnABI ArgABI : Type}

/-- **Moved immediate call argument (`d7Imm`, Finding 11a), universal.** With
`deinitMovedPlace = true`, `move _l` of a non-zero-sized immediate local is
validated at its type (with retagging disabled, `RetagMode.None`), then the
caller's local is replaced by `.live (.immediate .uninit)` (`setFrame`), and the
read value is passed by copy. -/
theorem call_evalFnCallArgumentMoving_move_immediate
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C) (l : Miri.MIR.LocalId)
    (path : OperandPath) (s s₁ s₂ s₃ s₄ s₅ : S) (rplace : RuntimeStackPlace P)
    (v : Immediate P) (layout : LocalLayout) (frame frame' : Frame P LocalLayout E)
    (hplace : h.evalPlace choice ⟨l, #[]⟩ true s = .ok rplace s₁)
    (hop : h.placeToOp choice rplace s₁ = .ok ⟨.immediate v, layout⟩ s₂)
    (hsized : layout.layout.isSized = true) (hzst : layout.layout.isZst = false)
    (hval : h.withRetagMode choice .None
      (h.validateOperandBeforeCall choice ⟨.immediate v, layout⟩) s₂ = .ok () s₃)
    (hget : h.getFrame s₃ = .ok frame s₄)
    (hrep : frame.replaceLocalValue l (.live (.immediate .uninit)) = .ok frame')
    (hset : h.setFrame frame' s₄ = .ok () s₅) :
    Call.evalFnCallArgumentMoving h choice (.Move ⟨l, #[]⟩) path s =
      .ok (.Copy ⟨.immediate v, layout⟩, none) s₅ := by
  simp only [Call.evalFnCallArgumentMoving, bind, EStateM.bind, hplace, hop, hsized, hval,
    hzst, Bool.not_true, Bool.false_eq_true, ↓reduceIte, array_isEmpty_empty]
  simp only [EStateM.bind, hget, hrep, hset]
  rfl

/-- **Moved memory-backed call argument, universal.** With `deinitMovedPlace =
true`, `move p` of a memory place is copied (validating, with retagging disabled)
into a fresh temporary, then the source is deinitialized with the silent
`deinitInPlaceArgument`, and the temporary is passed by copy: no argument is passed
in place, so no protected `uninit` write can occur. -/
theorem call_evalFnCallArgumentMoving_move_indirect
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C) (place : Miri.MIR.Place)
    (path : OperandPath) (s s₁ s₂ s₃ s₄ s₅ : S) (rplace : RuntimeStackPlace P)
    (mplace : MemPlace P) (layout : LocalLayout) (tmp : MPlaceTy P)
    (hplace : h.evalPlace choice place true s = .ok rplace s₁)
    (hop : h.placeToOp choice rplace s₁ = .ok ⟨.indirect mplace, layout⟩ s₂)
    (hsized : layout.layout.isSized = true)
    (halloc : h.allocateStack choice layout s₂ = .ok tmp s₃)
    (hcopy : h.withRetagMode choice .None
      (h.copyToMemory choice ⟨.indirect mplace, layout⟩ tmp) s₃ = .ok () s₄)
    (hdeinit : h.deinitInPlaceArgument choice ⟨mplace, layout⟩ s₄ = .ok () s₅) :
    Call.evalFnCallArgumentMoving h choice (.Move place) path s =
      .ok (.Copy ⟨.indirect tmp.mplace, tmp.layout⟩, some tmp.mplace.ptr) s₅ := by
  simp only [Call.evalFnCallArgumentMoving, bind, EStateM.bind, hplace, hop, hsized,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, halloc, hcopy, hdeinit]
  rfl

/-- A failing pre-resolution validation of a moved immediate argument aborts
before the caller's local is touched. -/
theorem call_evalFnCallArgumentMoving_move_immediate_invalid
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C) (l : Miri.MIR.LocalId)
    (path : OperandPath) (s s₁ s₂ s₃ : S) (rplace : RuntimeStackPlace P)
    (v : Immediate P) (layout : LocalLayout) (err : StepError)
    (hplace : h.evalPlace choice ⟨l, #[]⟩ true s = .ok rplace s₁)
    (hop : h.placeToOp choice rplace s₁ = .ok ⟨.immediate v, layout⟩ s₂)
    (hsized : layout.layout.isSized = true)
    (hval : h.withRetagMode choice .None
      (h.validateOperandBeforeCall choice ⟨.immediate v, layout⟩) s₂ = .error err s₃) :
    Call.evalFnCallArgumentMoving h choice (.Move ⟨l, #[]⟩) path s = .error err s₃ := by
  simp only [Call.evalFnCallArgumentMoving, bind, EStateM.bind, hplace, hop, hsized, hval,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- **Moved zero-sized immediate call argument (root or projected), universal.**
Moving a zero-sized immediate place (`layout.layout.isZst = true`, whether
unprojected or projected such as `_1.1 : ()`) validates the operand and returns
`(.Copy op, none)` without forcing stack allocation or mutating the caller
frame. -/
theorem call_evalFnCallArgumentMoving_move_zst
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C) (place : Miri.MIR.Place)
    (path : OperandPath) (s s₁ s₂ s₃ : S) (rplace : RuntimeStackPlace P)
    (v : Immediate P) (layout : LocalLayout)
    (hplace : h.evalPlace choice place true s = .ok rplace s₁)
    (hop : h.placeToOp choice rplace s₁ = .ok ⟨.immediate v, layout⟩ s₂)
    (hsized : layout.layout.isSized = true) (hzst : layout.layout.isZst = true)
    (hval : h.withRetagMode choice .None
      (h.validateOperandBeforeCall choice ⟨.immediate v, layout⟩) s₂ = .ok () s₃) :
    Call.evalFnCallArgumentMoving h choice (.Move place) path s =
      .ok (.Copy ⟨.immediate v, layout⟩, none) s₃ := by
  simp only [Call.evalFnCallArgumentMoving, bind, EStateM.bind, hplace, hop, hsized, hval,
    hzst, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure]

/-- **Retag-free argument snapshots (`ep1-A1`), universal.** The consumer-side
temporary copy of an indirect argument, and the pre-resolution validation of an
immediate one, run under `RetagMode.None`. Between statements the ambient retag
mode is `Default`, and the validating copy (`copyRuntimePlace` → `validatePlace`
with `resetProvenanceAndPadding = true`) retags every reference it validates in
the current mode, so without this scope the snapshot would add a `Default` retag
(a fresh child tag plus its retag access) on top of the callee's `FnEntry` retag
of `passArgument`; with it the `FnEntry` retag remains the only one, exactly as in
the source call path. -/
theorem call_materializeArgument_indirect_eq
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C) (mplace : MemPlace P)
    (layout : LocalLayout) (hsized : layout.layout.isSized = true) :
    Call.materializeArgument h choice ⟨.indirect mplace, layout⟩ = (do
      let tmp ← h.allocateStack choice layout
      h.withRetagMode choice .None (h.copyToMemory choice ⟨.indirect mplace, layout⟩ tmp)
      return (.Copy ⟨.indirect tmp.mplace, tmp.layout⟩, some tmp.mplace.ptr)) := by
  simp only [Call.materializeArgument, hsized, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- The immediate counterpart of `call_materializeArgument_indirect_eq`. -/
theorem call_materializeArgument_immediate_eq
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C) (v : Immediate P)
    (layout : LocalLayout) :
    Call.materializeArgument h choice ⟨.immediate v, layout⟩ = (do
      h.withRetagMode choice .None (h.validateOperandBeforeCall choice ⟨.immediate v, layout⟩)
      return (.Copy ⟨.immediate v, layout⟩, none)) := rfl

/-- `RetagMode.None` creates no new permission: the `newPermission` query of the
retag driver (`TypedRetag.retagPtrValue`) returns `none` immediately, so a retag
in that mode leaves the pointer and the borrow tree unchanged. -/
theorem typedRetag_newPermission_none {K User : Type} (h : TypedRetag.Hooks K User)
    (pointee : Miri.MIR.TyId) (kind : Miri.TreeBorrows.RetagPolicy.ReferenceKind) :
    TypedRetag.newPermission h pointee kind .None = pure none := rfl

/-- **Moved projected immediate call argument, universal.** With
`deinitMovedPlace = true`, `move _l.f` of a non-zero-sized field of an immediate
local is validated (with retagging disabled), the local is then materialized
(`forceAllocation`) and exactly the moved bytes are deinitialized with the silent
`deinitInPlaceArgument`, and the validated value is passed by copy. Together with
`call_evalFnCallArgumentMoving_move_immediate`/`_move_indirect`/`_move_zst` (the
other `Move` branches) and `call_materializeArgument_immediate_eq`/`_indirect_eq`
(the `Copy`/`Constant`/`RuntimeChecks` branch), every successful consumer-side
argument is an `FnArg.Copy`: `FnArg.InPlace` never reaches `passArgument`. -/
theorem call_evalFnCallArgumentMoving_move_projected_immediate
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C) (place : Miri.MIR.Place)
    (path : OperandPath) (s s₁ s₂ s₃ s₄ s₅ : S) (rplace : RuntimeStackPlace P)
    (v : Immediate P) (layout : LocalLayout) (moved : MPlaceTy P)
    (hplace : h.evalPlace choice place true s = .ok rplace s₁)
    (hop : h.placeToOp choice rplace s₁ = .ok ⟨.immediate v, layout⟩ s₂)
    (hsized : layout.layout.isSized = true) (hzst : layout.layout.isZst = false)
    (hproj : place.projection.isEmpty = false)
    (hval : h.withRetagMode choice .None
      (h.validateOperandBeforeCall choice ⟨.immediate v, layout⟩) s₂ = .ok () s₃)
    (hforce : h.forceAllocation choice rplace s₃ = .ok moved s₄)
    (hdeinit : h.deinitInPlaceArgument choice moved s₄ = .ok () s₅) :
    Call.evalFnCallArgumentMoving h choice (.Move place) path s =
      .ok (.Copy ⟨.immediate v, layout⟩, none) s₅ := by
  simp only [Call.evalFnCallArgumentMoving, bind, EStateM.bind, hplace, hop, hsized, hval,
    hzst, hproj, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only [hforce, hdeinit]
  rfl

/-- **No protector on a copied argument, universal.** `Call.passArgument` on an
`FnArg.Copy` argument never runs `protectArgument` (the hook that retags an
in-place argument with a protector and writes `uninit` through it, a foreign Tree
Borrows `.Write` that would disable sibling `Frozen` borrows): replacing the hook
by any other leaves `passArgument` unchanged. Since every consumer-side argument
is an `FnArg.Copy` (`call_evalFnCallArgumentMoving_move_projected_immediate`), no
consumer-side moved argument is ever protected or deinitialized through a
protected tag. -/
theorem call_passArgument_copy_protect_irrelevant
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (protect : C → MPlaceTy P → CallM S Unit)
    (choice : C) (op : OpTy P) (callerAbi calleeAbi : ArgABI) (calleeIndex : Nat)
    (dest : Miri.MIR.Place) (calleeTy : Miri.MIR.TyId) (alreadyLive : Bool) :
    Call.passArgument { h with protectArgument := protect } choice (.Copy op) callerAbi calleeAbi
        calleeIndex dest calleeTy alreadyLive =
      Call.passArgument h choice (.Copy op) callerAbi calleeAbi calleeIndex dest calleeTy
        alreadyLive :=
  rfl

/-- **Memory-path overlapping move rejected with UB (`Finding 4`), universal.**
When `h.takePendingMoveDeinit` returns `true` on a padded/memory-path copy whose
source and destination overlap (`h.moveCopyOverlaps = true`),
`Place.copyRuntimePlaceNoValidate` rejects the copy with
`.undefinedBehavior "copy_nonoverlapping called on overlapping ranges"` before
`copy.memoryCopy` or `h.deinitMemoryRaw` runs. -/
theorem place_copyRuntimePlaceNoValidate_overlapping_move_ub
    (h : PlaceHooks P S C E) (copy : PlaceCopyHooks P S C) (choice : C)
    (mplace : MemPlace P) (srcLayout : LocalLayout) (dest : RuntimePlace P)
    (allowTransmute : Bool) (s s₁ s₂ s₃ : S) (target : MPlaceTy P)
    (hcompat : copy.compatible srcLayout dest.layout = .ok true)
    (hpad : copy.hasPadding srcLayout = .ok true)
    (htake : h.takePendingMoveDeinit s = .ok true s₁)
    (hforce : forceAllocation h choice dest s₁ = .ok target s₂)
    (hoverlap : h.moveCopyOverlaps choice ⟨mplace, srcLayout⟩ target s₂ = .ok true s₃) :
    copyRuntimePlaceNoValidate h copy choice ⟨.indirect mplace, srcLayout⟩ dest allowTransmute s =
      .error (.undefinedBehavior "copy_nonoverlapping called on overlapping ranges") s₃ := by
  unfold copyRuntimePlaceNoValidate
  unfold_named "_private.Miri.Interpreter.Place.0.Miri.Interpreter.placeLift"
  simp only [bind, EStateM.bind, pure, EStateM.pure, hcompat, hpad, htake, hforce, hoverlap,
    Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

end CallArgs

/-! ### Concrete runs of the real `Call.evalCalleeAndArgsMoving` and `Call.evalCalleeAndArgs`

A small hook dictionary over a byte-cell memory (`ToyCallState.mem`) drives the
real consumer-side `Call.evalCalleeAndArgsMoving` (used by
`Call.evalCallTerminatorMoving`/`evalTailCallTerminatorMoving`, which
`ExecutionMachine.stepHooks` selects when `deinitMovedPlace = true`) and, for
contrast, the unchanged source `Call.evalCalleeAndArgs` over the same hooks. The
validating copy (`copyToMemory`) faults on an uninitialized cell,
`deinitInPlaceArgument` clears a cell, and `resolve` records that it ran and then
fails as unresolved, as for an unresolved callee. -/

section CallToy

open Miri.ABI Miri.Memory Miri.Interpreter

/-- Toy machine state: memory cells (`none` = uninitialized), a flag recording
whether callee resolution ran, and the next temporary cell. -/
structure ToyCallState where
  mem : List (Option Nat)
  resolved : Bool
  nextTmp : Nat

/-- A one-byte, memory-represented, sized layout. -/
def toyByteLayout : LayoutData :=
  { fields := .Primitive, variants := .Single 0, backendRepr := .Memory (sized := true),
    largestNiche := none, uninhabited := false, align := ⟨Align.ONE⟩, size := ⟨1⟩,
    maxReprAlign := none, unadjustedAbiAlign := Align.ONE, reprC := false, randomizationSeed := 0 }

/-- A zero-byte (`isZst = true`) function-definition layout. -/
def toyZstLayout : LayoutData :=
  { toyByteLayout with size := ⟨0⟩ }

/-- `u8`-like local layout. -/
def toyU8 : LocalLayout := ⟨0, toyByteLayout⟩

/-- Zero-sized `FnDef` layout. -/
def toyFnLayout : LocalLayout := ⟨0, toyZstLayout⟩

/-- Memory place of cell `n`. -/
def toyMPlace (n : Nat) : MemPlace Unit := ⟨⟨⟨n.toUInt64⟩, none⟩, .none, none⟩

/-- Cell of a MIR place: `localId + fieldIdx` when projected by `.Field fieldIdx _`,
or `localId` when unprojected. -/
def toyPlaceCell (place : Miri.MIR.Place) : Nat :=
  place.localId +
    match (place.projection[0]? : Option Miri.MIR.ProjectionElem) with
    | some (Miri.MIR.ProjectionElem.Field idx _) => idx
    | _ => 0

/-- Cell of a memory place. -/
def toyCell (m : MemPlace Unit) : Nat := m.ptr.offset.bytes.toNat

/-- Read a cell. -/
def toyRead (s : ToyCallState) (n : Nat) : Option Nat := (s.mem[n]?).join

/-- Validating copy: faults on an uninitialized source cell (`invalidUninitBytes`). -/
def toyCopy (op : OpTy Unit) (dst : MPlaceTy Unit) : CallM ToyCallState Unit := do
  let s ← get
  match op.op with
  | .indirect m =>
    match toyRead s (toyCell m) with
    | some v => set { s with mem := s.mem.set (toyCell dst.mplace) (some v) }
    | none => throw (.undefinedBehavior "invalidUninitBytes")
  | .immediate .uninit => throw (.undefinedBehavior "invalidUninitBytes")
  | .immediate _ => set { s with mem := s.mem.set (toyCell dst.mplace) (some 0) }

/-- The toy call hooks; `deinitMovedPlace` selects the patched or source mode. -/
def toyCallHooks (deinit : Bool) :
    CallHooks Unit ToyCallState Unit Unit Unit Unit Unit Unit where
  debugAssertions := false
  getFrame := throw (.unsupported "toy: frame")
  setFrame := fun _ => throw (.unsupported "toy: frame")
  frameIndex := pure 0
  evalOperand := fun _ op =>
    match op with
    | .Copy ⟨0, _⟩ => pure ⟨.immediate .uninit, toyFnLayout⟩
    | .Copy place | .Move place => pure ⟨.indirect (toyMPlace (toyPlaceCell place)), toyU8⟩
    | _ => pure ⟨.immediate .uninit, toyU8⟩
  evalPlace := fun _ place _ => pure (.memory ⟨toyMPlace (toyPlaceCell place), toyU8⟩)
  placeToOp := fun _ rp =>
    match rp with
    | .memory m => pure ⟨.indirect m.mplace, m.layout⟩
    | _ => throw (.unsupported "toy: local place")
  forceAllocation := fun _ rp =>
    match rp with
    | .memory m => pure m
    | _ => throw (.unsupported "toy: local place")
  functionSignature := fun _ _ => pure (0, ())
  functionKind := fun _ => pure (.FnDef 7 #[])
  readPointer := fun _ _ => throw (.unsupported "toy")
  getPtrFn := fun _ _ => throw (.unsupported "toy")
  resolve := fun _ _ _ => do
    modify fun s => { s with resolved := true }
    throw (.unsupported "unresolved callee")
  fnAbiOfFnPtr := fun _ _ _ => throw (.unsupported "toy")
  fnAbiOfInstance := fun _ _ _ => throw (.unsupported "toy")
  requiresCallerLocation := fun _ => pure false
  callerLocation := throw (.unsupported "toy")
  abiCanUnwind := fun _ => false
  abiVariadic := fun _ => false
  abiFixedCount := fun _ => 0
  abiArgs := fun _ => #[]
  abiReturn := fun _ => ()
  sameConvention := fun _ _ => true
  isRustCall := fun _ => false
  rustAbi := ()
  argLayout := fun _ => toyU8
  argIsIgnore := fun _ => false
  isOneZst := fun _ => false
  checkArgumentCompat := fun _ _ _ => pure true
  checkTargetFeatures := fun _ _ => pure ()
  tupleFields := fun _ => pure #[]
  projectFnArg := fun _ _ _ => throw (.unsupported "toy")
  localLayout := fun _ _ => pure toyU8
  localSpan := fun _ _ => pure ⟨0⟩
  storageLiveDyn := fun _ _ _ => pure ()
  copyAllowTransmute := fun _ _ _ => throw (.unsupported "toy")
  protectArgument := fun _ _ => throw (.unsupported "toy")
  withRetagMode := fun _ _ action => action
  nonCapturingClosure := fun _ _ _ => pure false
  allocateStack := fun _ layout => do
    let s ← get
    set { s with nextTmp := s.nextTmp + 1 }
    pure ⟨toyMPlace s.nextTmp, layout⟩
  copyToMemory := fun _ op dst => toyCopy op dst
  vaListPtr := fun _ _ => throw (.unsupported "toy")
  writeZeroBytes := fun _ _ _ => throw (.unsupported "toy")
  vaListKeyField := fun _ _ => throw (.unsupported "toy")
  writePointerToMemory := fun _ _ _ => throw (.unsupported "toy")
  pushRaw := fun _ _ _ _ _ => throw (.unsupported "toy")
  pushDone := fun _ => throw (.unsupported "toy")
  popRaw := fun _ => throw (.unsupported "toy")
  cleanup := fun _ _ _ => throw (.unsupported "toy")
  afterFrameInit := fun _ => pure ()
  callExtra := fun _ _ _ _ _ _ _ => throw (.unsupported "toy")
  callIntrinsic := fun _ _ _ _ _ _ => throw (.unsupported "toy")
  callLlvmIntrinsic := fun _ _ _ _ _ => throw (.unsupported "toy")
  findMirOrEvalFn := fun _ _ _ _ _ _ _ => throw (.unsupported "toy")
  resolveVirtual := fun _ _ _ _ _ _ => throw (.unsupported "toy")
  isDynamic := fun _ => pure false
  unpackDynForDrop := fun _ _ => throw (.unsupported "toy")
  resolveDropGlue := fun _ _ => throw (.unsupported "toy")
  mplaceToMutRef := fun _ _ => throw (.unsupported "toy")
  fakeUnitReturn := fun _ => throw (.unsupported "toy")
  deinitMovedPlace := deinit
  deinitInPlaceArgument := fun _ m => modify fun s => { s with mem := s.mem.set (toyCell m.mplace) none }
  validateOperandBeforeCall := fun _ op =>
    if op.layout.layout.isZst then pure () else
    match op.op with
    | .immediate .uninit => throw (.undefinedBehavior "invalidUninitBytes")
    | _ => pure ()
  deallocateStack := fun _ _ => pure ()

/-- `_1 = 5` (cell 1), `_2` uninitialized (cell 2); temporaries from cell 4. -/
def toyInit : ToyCallState := { mem := [none, some 5, none, none, none, none, none], resolved := false, nextTmp := 4 }

def toySpan : Miri.MIR.SpanRef := ⟨0⟩
def toyFn : Miri.MIR.Operand := .Copy ⟨0, #[]⟩
def toyDest : Miri.MIR.Place := ⟨0, #[]⟩

/-- **Same-call `f(move _1, copy _1)` (Finding 11b).** The consumer-side
`Call.evalCalleeAndArgsMoving` consumes `move _1` (copying `5` into temporary cell 4
and deinitializing `_1`) before evaluating `copy _1`, whose validating copy
faults with undefined behavior — before callee resolution (`resolved = false`). -/
theorem canary_call_move_then_copy_ub :
    Call.evalCalleeAndArgsMoving (toyCallHooks true) () toyFn
        #[⟨toySpan, .Move ⟨1, #[]⟩⟩, ⟨toySpan, .Copy ⟨1, #[]⟩⟩] toyInit =
      .error (.undefinedBehavior "invalidUninitBytes")
        { mem := [none, none, none, none, some 5, none, none], resolved := false, nextTmp := 6 } := by
  with_unfolding_all rfl

/-- **Same-call `f(copy _1, move _1)` (valid).** Evaluating `copy _1` first
snapshots `5` into temporary cell 4 before `move _1` copies `5` into temporary
cell 5 and deinitializes `_1`, so both arguments receive `5` and callee
resolution is reached. -/
theorem canary_call_copy_then_move_same_call_ok :
    Call.evalCalleeAndArgsMoving (toyCallHooks true) () toyFn
        #[⟨toySpan, .Copy ⟨1, #[]⟩⟩, ⟨toySpan, .Move ⟨1, #[]⟩⟩] toyInit =
      .error (.unsupported "unresolved callee")
        { mem := [none, none, none, none, some 5, some 5, none], resolved := true, nextTmp := 6 } := by
  with_unfolding_all rfl

/-- **`call (move _uninit_fn)(move _1)` (`kani#5172` on `func`).** When the
callee operand `func` itself is `Operand.Move` (or `Operand.Copy`) of an
uninitialized local (`_2`), `Call.evalCalleeAndArgsMoving` faults on `func`
before evaluating `args` (so `_1 = 5` is NOT deinitialized) and before
`resolve` runs (`resolved = false`). -/
theorem canary_call_uninit_func_ub_before_args_and_resolve :
    Call.evalCalleeAndArgsMoving (toyCallHooks true) () (.Move ⟨2, #[]⟩)
        #[⟨toySpan, .Move ⟨1, #[]⟩⟩] toyInit =
      .error (.undefinedBehavior "invalidUninitBytes")
        { mem := [none, some 5, none, none, none, none, none], resolved := false, nextTmp := 5 } ∧
    Call.evalCalleeAndArgsMoving (toyCallHooks true) () (.Copy ⟨2, #[]⟩)
        #[⟨toySpan, .Move ⟨1, #[]⟩⟩] toyInit =
      .error (.undefinedBehavior "invalidUninitBytes")
        { mem := [none, some 5, none, none, none, none, none], resolved := false, nextTmp := 5 } :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl⟩

/-- **`(copy _1)(move _1)` when `_1` is memory-backed.** `Call.evalCalleeAndArgsMoving`
snapshots `func = copy _1` into temporary cell 4 before `args[0] = move _1`
copies `_1` into temporary cell 5 and deinitializes `_1`. -/
theorem canary_call_copy_func_then_move_func_arg_ok :
    Call.evalCalleeAndArgsMoving (toyCallHooks true) () (.Copy ⟨1, #[]⟩)
        #[⟨toySpan, .Move ⟨1, #[]⟩⟩] toyInit =
      .error (.unsupported "unresolved callee")
        { mem := [none, none, none, none, some 5, some 5, none], resolved := true, nextTmp := 6 } := by
  with_unfolding_all rfl

/-- **`(move _1)(copy _1)` when `_1` is memory-backed (`ep1-A1`).** The callee
operand is consumed first: `move _1` snapshots `5` into temporary cell 4 and
deinitializes `_1` *before* any argument is evaluated, so the argument
`copy _1` faults with `invalidUninitBytes` — before callee resolution
(`resolved = false`). Contrast `canary_call_copy_func_then_move_func_arg_ok`. -/
theorem canary_call_move_func_then_copy_func_arg_ub :
    Call.evalCalleeAndArgsMoving (toyCallHooks true) () (.Move ⟨1, #[]⟩)
        #[⟨toySpan, .Copy ⟨1, #[]⟩⟩] toyInit =
      .error (.undefinedBehavior "invalidUninitBytes")
        { mem := [none, none, none, none, some 5, none, none], resolved := false, nextTmp := 6 } := by
  with_unfolding_all rfl

/-- `_1 = (2, 3)` stored at cells 1 (`_1.0`) and 2 (`_1.1`). -/
def toyPairInit : ToyCallState :=
  { mem := [none, some 2, some 3, none, none, none, none], resolved := false, nextTmp := 4 }

/-- **Projected call arguments `f(move _1.0, copy _1.1)` (valid) vs
`f(move _1.0, copy _1.0)` (UB).** Moving `_1.0` deinitializes only cell 1, so
a sibling `copy _1.1` in the same call reads `3` and reaches `resolve`, whereas
`copy _1.0` faults with `invalidUninitBytes` before `resolve`. -/
theorem canary_call_projected_move_sibling_ok_vs_same_field_ub :
    Call.evalCalleeAndArgsMoving (toyCallHooks true) () toyFn
        #[⟨toySpan, .Move ⟨1, #[.Field 0 0]⟩⟩, ⟨toySpan, .Copy ⟨1, #[.Field 1 0]⟩⟩] toyPairInit =
      .error (.unsupported "unresolved callee")
        { mem := [none, none, some 3, none, some 2, some 3, none], resolved := true, nextTmp := 6 } ∧
    Call.evalCalleeAndArgsMoving (toyCallHooks true) () toyFn
        #[⟨toySpan, .Move ⟨1, #[.Field 0 0]⟩⟩, ⟨toySpan, .Copy ⟨1, #[.Field 0 0]⟩⟩] toyPairInit =
      .error (.undefinedBehavior "invalidUninitBytes")
        { mem := [none, none, some 3, none, some 2, none, none], resolved := false, nextTmp := 6 } :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl⟩

/-- **`call unresolved(move _uninit)` (kani#5172, Finding 11c).** The consumer-side
`Call.evalCalleeAndArgsMoving` faults with undefined behavior on the uninitialized
argument before `resolve` runs. -/
theorem canary_call_uninit_arg_ub_before_resolve :
    Call.evalCalleeAndArgsMoving (toyCallHooks true) () toyFn
        #[⟨toySpan, .Move ⟨2, #[]⟩⟩] toyInit =
      .error (.undefinedBehavior "invalidUninitBytes")
        { mem := [none, some 5, none, none, none, none, none], resolved := false, nextTmp := 5 } := by
  with_unfolding_all rfl

/-- `call unresolved(copy _uninit)` also faults before resolution. -/
theorem canary_call_uninit_copy_arg_ub_before_resolve :
    Call.evalCalleeAndArgsMoving (toyCallHooks true) () toyFn
        #[⟨toySpan, .Copy ⟨2, #[]⟩⟩] toyInit =
      .error (.undefinedBehavior "invalidUninitBytes")
        { mem := [none, some 5, none, none, none, none, none], resolved := false, nextTmp := 5 } := by
  with_unfolding_all rfl

/-- Contrast: with an initialized argument resolution does run (and fails as
unresolved); the moved argument's cell `_1` has been deinitialized and its value
was passed through temporary cell 4. -/
theorem canary_call_valid_move_reaches_resolve :
    Call.evalCalleeAndArgsMoving (toyCallHooks true) () toyFn
        #[⟨toySpan, .Move ⟨1, #[]⟩⟩] toyInit =
      .error (.unsupported "unresolved callee")
        { mem := [none, none, none, none, some 5, none, none], resolved := true, nextTmp := 5 } := by
  with_unfolding_all rfl

/-- Contrast (source order): the unchanged source `Call.evalCalleeAndArgs`, over
the same hooks, lets `f(move _1, copy _1)` reach callee resolution — the use after
move is not detected first — and never deinitializes `_1`. -/
theorem canary_call_move_then_copy_source_order :
    Call.evalCalleeAndArgs (toyCallHooks true) () toyFn
        #[⟨toySpan, .Move ⟨1, #[]⟩⟩, ⟨toySpan, .Copy ⟨1, #[]⟩⟩] toyDest toyInit =
      .error (.unsupported "unresolved callee")
        { mem := [none, some 5, none, none, none, none, none], resolved := true, nextTmp := 4 } := by
  with_unfolding_all rfl

/-- Contrast (source order): for `call unresolved(move _uninit)` the source
`Call.evalCalleeAndArgs` reports the unresolved callee instead of the undefined
behavior. -/
theorem canary_call_uninit_arg_source_order :
    Call.evalCalleeAndArgs (toyCallHooks true) () toyFn
        #[⟨toySpan, .Move ⟨2, #[]⟩⟩] toyDest toyInit =
      .error (.unsupported "unresolved callee")
        { mem := [none, some 5, none, none, none, none, none], resolved := true, nextTmp := 4 } := by
  with_unfolding_all rfl

end CallToy

/-! ### `D4`: multi-operand `BinaryOp` through the real `evalRvalueIntoPlace`

The real dispatcher `evalRvalueIntoPlace` (pinned `step.rs`) evaluates *and
reads* the left operand before it evaluates the right one
(`evalRvalueIntoPlace_binaryOp`). With the consumer-side latch, a moved indirect
operand is queued by `OperandMachine.evalOperand`
(`operandMachine_evalOperand_move_indirect`) and deinitialized by its own read
(`placeMachine_readImmediate_moving`, `takePendingMoveDeinitFor_front`), while a
moved unprojected immediate local is deinitialized at evaluation
(`operandMachine_evalOperand_move_immediate_root`), and a moved projected
immediate local is first materialized (`forceAllocation`) and then queued. A
small hook dictionary implementing exactly these transitions over memory cells,
immediate locals and the latch queue drives the real `evalRvalueIntoPlace`:
`copy _1 + move _1` succeeds with both operands reading `5` (and `_1`
deinitialized afterwards), while `move _1 + copy _1` and `move _1 + move _1` fault
on the second read — for memory-backed, immediate and projected-immediate
(`_1.0` of a scalar pair) locals alike. The toy carries an immediate operand's
value in its layout's type id (`toyImmOp`). -/

section BinaryOpToy

open Miri.ABI Miri.Memory Miri.Interpreter

variable {P S C : Type}

/-- A public copy of the private `assertRvalueLayout` of `Rvalue.lean`. -/
def rvalueLayoutCheck (actual expected : TyAndLayout Miri.MIR.TyId) : RvalueM S Unit :=
  if actual == expected then pure () else throw (.invalidProgram "rvalue result layout mismatch")

/-- The part of the `BinaryOp` arm of `evalRvalueIntoPlace` after both operands
have been read. -/
def binaryOpTail {V : Type} (h : RvalueHooks P S C V) (choice : C) (operator : Miri.MIR.BinOp)
    (layout : TyAndLayout Miri.MIR.TyId) (dest : V) (left right : RvalueImmTy P) :
    RvalueM S Unit := do
  let result ← h.binaryOp choice operator left right
  rvalueLayoutCheck result.layout layout
  h.writeImmediate choice result.imm dest

/-- **Operand order of `BinaryOp`, universal.** `evalRvalueIntoPlace` reads the
left operand (`readImmediate`, which consumes its latch record) before it
evaluates the right operand: there is never more than one pending operand record
in a binary operation. -/
theorem evalRvalueIntoPlace_binaryOp {V : Type} (h : RvalueHooks P S C V) (choice : C)
    (operator : Miri.MIR.BinOp) (l r : Miri.MIR.Operand) (place : Miri.MIR.Place) :
    evalRvalueIntoPlace h choice (.BinaryOp operator l r) place = (do
      let dest ← h.evalPlace choice place true
      let layout := h.placeLayout dest
      let left ← h.evalOperandAt choice (OperandPath.rvalue "left") l
        (if operator.leftHomogeneous then some layout else none)
      let left ← h.readImmediate choice left
      let right ← h.evalOperandAt choice (OperandPath.rvalue "right") r
        (if operator.rightHomogeneous then some left.layout else none)
      let right ← h.readImmediate choice right
      binaryOpTail h choice operator layout dest left right) := by
  unfold evalRvalueIntoPlace binaryOpTail rvalueLayoutCheck
  unfold_named "_private.Miri.Interpreter.Rvalue.0.Miri.Interpreter.assertRvalueLayout"
  rfl

/-- Representation of a local in the `D4` toy. -/
inductive ToySlot where
  /-- Memory-backed: the value of `_l.i` lives in memory cell `l + i`. -/
  | mem
  /-- Immediate scalar local (`none` = uninitialized). -/
  | imm (v : Option Nat)
  /-- Immediate scalar-pair local. -/
  | immPair (a b : Option Nat)

/-- Toy rvalue state: locals, memory cells (`none` = uninitialized), the latch
queue of `(cell, isMove)` records, the values read so far, and whether the
destination was written. -/
structure ToyRvState where
  slots : List ToySlot
  cells : List (Option Nat)
  queue : List (Nat × Bool)
  reads : List Nat
  written : Bool

/-- An immediate operand carrying `v` (in its layout's type id) or `uninit`. -/
def toyImmOp : Option Nat → OpTy Unit
  | some v => ⟨.immediate (.scalar (Scalar.fromBool true)), ⟨v, toyByteLayout⟩⟩
  | none => ⟨.immediate .uninit, toyU8⟩

/-- The field index of a toy place, if projected. -/
def toyField (place : Miri.MIR.Place) : Option Nat :=
  match (place.projection[0]? : Option Miri.MIR.ProjectionElem) with
  | some (Miri.MIR.ProjectionElem.Field idx _) => some idx
  | _ => none

/-- The memory operand of a toy place. -/
def toyMemOperand (place : Miri.MIR.Place) : OpTy Unit :=
  ⟨.indirect (toyMPlace (toyPlaceCell place)), toyU8⟩

/-- `OperandMachine.evalOperandMoving` over the toy state: `Copy`/`Move` of a
memory place queues `(cell, false/true)`; `Copy` of an immediate (field) is a
value snapshot; `Move` of an unprojected immediate local deinitializes it at once;
`Move` of a field of an immediate pair materializes the pair (`forceAllocation`)
and queues the moved field. -/
def toyRvEval (operand : Miri.MIR.Operand) : RvalueM ToyRvState (OpTy Unit) := do
  let s ← get
  match operand with
  | .Copy place =>
    match s.slots[place.localId]?, toyField place with
    | some (.imm v), none => pure (toyImmOp v)
    | some (.immPair a _), some 0 => pure (toyImmOp a)
    | some (.immPair _ b), some 1 => pure (toyImmOp b)
    | some .mem, _ =>
      set { s with queue := s.queue ++ [(toyPlaceCell place, false)] }
      pure (toyMemOperand place)
    | _, _ => throw (.unsupported "toy operand")
  | .Move place =>
    match s.slots[place.localId]?, toyField place with
    | some (.imm v), none =>
      set { s with slots := s.slots.set place.localId (.imm none) }
      pure (toyImmOp v)
    | some (.immPair a b), some _ =>
      set { s with
        slots := s.slots.set place.localId .mem
        cells := (s.cells.set place.localId a).set (place.localId + 1) b
        queue := s.queue ++ [(toyPlaceCell place, true)] }
      pure (toyMemOperand place)
    | some .mem, _ =>
      set { s with queue := s.queue ++ [(toyPlaceCell place, true)] }
      pure (toyMemOperand place)
    | _, _ => throw (.unsupported "toy operand")
  | _ => throw (.unsupported "toy operand")

/-- `MachineHooks.takePendingMoveDeinitFor` over the toy queue: consume the
earliest record of the read cell (the front one in every run below). -/
def toyTake : List (Nat × Bool) → Nat → List (Nat × Bool) × Bool
  | [], _ => ([], false)
  | (c, mv) :: rest, n =>
    if c == n then (rest, mv) else
      let (rest', mv') := toyTake rest n
      ((c, mv) :: rest', mv')

/-- `PlaceMachine.readImmediateMoving` over the toy state: an uninitialized
immediate faults; a memory read consumes its record, faults on an uninitialized
cell, and deinitializes the cell after the read exactly when the record is a move. -/
def toyRvRead (op : OpTy Unit) : RvalueM ToyRvState (RvalueImmTy Unit) := do
  let s ← get
  match op.op with
  | .immediate .uninit => throw (.undefinedBehavior "invalidUninitBytes")
  | .immediate imm =>
    set { s with reads := s.reads ++ [op.layout.ty] }
    pure ⟨imm, toyU8⟩
  | .indirect m =>
    let n := toyCell m
    let (queue, isMove) := toyTake s.queue n
    match (s.cells[n]?).join with
    | none =>
      set { s with queue }
      throw (.undefinedBehavior "invalidUninitBytes")
    | some v =>
      set { s with queue, reads := s.reads ++ [v],
                   cells := if isMove then s.cells.set n none else s.cells }
      pure ⟨.scalar (Scalar.fromBool true), toyU8⟩

/-- The toy rvalue hooks. -/
def toyRvHooks : RvalueHooks Unit ToyRvState Unit Unit where
  placeLayout := fun _ => toyU8
  evalPlace := fun _ _ _ => pure ()
  evalOperand := fun _ op _ => toyRvEval op
  evalOperandAt := fun _ _ op _ => toyRvEval op
  evalPlaceToOp := fun _ _ _ => throw (.unsupported "toy")
  readImmediate := fun _ op => toyRvRead op
  writeImmediate := fun _ _ _ => modify fun s => { s with written := true }
  writePointer := fun _ _ _ => throw (.unsupported "toy")
  threadLocalPointer := fun _ _ => throw (.unsupported "toy")
  withRetagMode := fun _ _ action => action
  copyOp := fun _ _ _ => throw (.unsupported "toy")
  copyOpAllowTransmute := fun _ _ _ => throw (.unsupported "toy")
  binaryOp := fun _ _ _ _ => pure ⟨.scalar (Scalar.fromBool true), toyU8⟩
  unaryOp := fun _ _ _ => throw (.unsupported "toy")
  writeAggregate := fun _ _ _ _ => throw (.unsupported "toy")
  writeRepeat := fun _ _ _ => throw (.unsupported "toy")
  forceAllocation := fun _ _ => throw (.unsupported "toy")
  toRef := fun _ _ => throw (.unsupported "toy")
  enforceValidity := fun _ _ => pure false
  retagPtrValue := fun _ _ _ => pure none
  placeBaseRaw := fun _ _ => pure false
  normalize := fun _ ty => pure ty
  cast := fun _ _ _ _ _ => throw (.unsupported "toy")
  readDiscriminant := fun _ _ => throw (.unsupported "toy")
  discriminantForVariant := fun _ _ _ => throw (.unsupported "toy")

/-- `_1 = 5`, memory-backed (cell 1). -/
def d4Mem : ToyRvState :=
  { slots := [.mem, .mem, .mem], cells := [none, some 5, none], queue := [], reads := [],
    written := false }

/-- `_1 = 5`, an immediate local. -/
def d4Imm : ToyRvState :=
  { slots := [.mem, .imm (some 5), .mem], cells := [none, none, none], queue := [], reads := [],
    written := false }

/-- `_1 = (5, 6)`, an immediate scalar pair. -/
def d4Pair : ToyRvState :=
  { slots := [.mem, .immPair (some 5) (some 6), .mem], cells := [none, none, none], queue := [],
    reads := [], written := false }

def d4P1 : Miri.MIR.Place := ⟨1, #[]⟩
def d4P10 : Miri.MIR.Place := ⟨1, #[.Field 0 0]⟩
def d4P11 : Miri.MIR.Place := ⟨1, #[.Field 1 0]⟩
def d4Add (l r : Miri.MIR.Operand) : Miri.MIR.Rvalue := .BinaryOp .Add l r
def d4Dest : Miri.MIR.Place := ⟨0, #[]⟩

/-- **`D4`, memory-backed `_1`.** `_0 = Add(copy _1, move _1)` reads `5` twice and
leaves `_1` deinitialized; `Add(move _1, copy _1)` and `Add(move _1, move _1)`
fault on the second read; `Add(copy _1, copy _1)` leaves `_1` intact. -/
theorem canary_D4_mem_binaryOp :
    evalRvalueIntoPlace toyRvHooks () (d4Add (.Copy d4P1) (.Move d4P1)) d4Dest d4Mem =
      .ok () { d4Mem with cells := [none, none, none], reads := [5, 5], written := true } ∧
    evalRvalueIntoPlace toyRvHooks () (d4Add (.Move d4P1) (.Copy d4P1)) d4Dest d4Mem =
      .error (.undefinedBehavior "invalidUninitBytes")
        { d4Mem with cells := [none, none, none], reads := [5] } ∧
    evalRvalueIntoPlace toyRvHooks () (d4Add (.Move d4P1) (.Move d4P1)) d4Dest d4Mem =
      .error (.undefinedBehavior "invalidUninitBytes")
        { d4Mem with cells := [none, none, none], reads := [5] } ∧
    evalRvalueIntoPlace toyRvHooks () (d4Add (.Copy d4P1) (.Copy d4P1)) d4Dest d4Mem =
      .ok () { d4Mem with reads := [5, 5], written := true } :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl,
   by with_unfolding_all rfl⟩

/-- **`D4`, immediate `_1`.** The moved immediate local is deinitialized at
evaluation, so `Add(copy _1, move _1)` reads `5` twice, whereas
`Add(move _1, copy _1)` reads the `uninit` immediate and faults. -/
theorem canary_D4_imm_binaryOp :
    evalRvalueIntoPlace toyRvHooks () (d4Add (.Copy d4P1) (.Move d4P1)) d4Dest d4Imm =
      .ok () { d4Imm with slots := [.mem, .imm none, .mem], reads := [5, 5], written := true } ∧
    evalRvalueIntoPlace toyRvHooks () (d4Add (.Move d4P1) (.Copy d4P1)) d4Dest d4Imm =
      .error (.undefinedBehavior "invalidUninitBytes")
        { d4Imm with slots := [.mem, .imm none, .mem], reads := [5] } ∧
    evalRvalueIntoPlace toyRvHooks () (d4Add (.Move d4P1) (.Move d4P1)) d4Dest d4Imm =
      .error (.undefinedBehavior "invalidUninitBytes")
        { d4Imm with slots := [.mem, .imm none, .mem], reads := [5] } :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩

/-- **`D4`, projected field of an immediate pair `_1 = (5, 6)`.** The copy of
`_1.0` evaluated first is a value snapshot taken before `move _1.0` materializes
`_1`, so `Add(copy _1.0, move _1.0)` reads `5` twice and leaves only `_1.0`
deinitialized (`_1.1 = 6` survives in cell 2); `Add(move _1.0, copy _1.0)` faults,
and `Add(move _1.0, copy _1.1)` reads the sibling `6`. -/
theorem canary_D4_pair_field_binaryOp :
    evalRvalueIntoPlace toyRvHooks () (d4Add (.Copy d4P10) (.Move d4P10)) d4Dest d4Pair =
      .ok () { d4Pair with slots := [.mem, .mem, .mem], cells := [none, none, some 6],
                           reads := [5, 5], written := true } ∧
    evalRvalueIntoPlace toyRvHooks () (d4Add (.Move d4P10) (.Copy d4P10)) d4Dest d4Pair =
      .error (.undefinedBehavior "invalidUninitBytes")
        { d4Pair with slots := [.mem, .mem, .mem], cells := [none, none, some 6], reads := [5] } ∧
    evalRvalueIntoPlace toyRvHooks () (d4Add (.Move d4P10) (.Copy d4P11)) d4Dest d4Pair =
      .ok () { d4Pair with slots := [.mem, .mem, .mem], cells := [none, none, some 6],
                           reads := [5, 6], written := true } :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩

end BinaryOpToy

/-! ### `UnaryOp` (including `PtrMetadata`) reads its whole operand before the operator -/

section UnaryOpA2

open Miri.ABI Miri.Memory Miri.Interpreter

variable {P S C : Type}

/-- The part of the `UnaryOp` arm of `evalRvalueIntoPlace` after its operand has
been read. -/
def unaryOpTail {V : Type} (h : RvalueHooks P S C V) (choice : C) (operator : Miri.MIR.UnOp)
    (layout : TyAndLayout Miri.MIR.TyId) (dest : V) (val : RvalueImmTy P) : RvalueM S Unit := do
  let result ← h.unaryOp choice operator val
  rvalueLayoutCheck result.layout layout
  h.writeImmediate choice result.imm dest

/-- **Operand order of `UnaryOp` (including `PtrMetadata`), universal.**
`evalRvalueIntoPlace` evaluates the operand and reads it *whole* with
`readImmediate` (which consumes its move record and, for a moved memory place,
deinitializes the entire operand layout) before the unary operator runs on the
read immediate: `PtrMetadata(move p)` of a wide pointer deinitializes both
halves of `p`, never only its metadata. -/
theorem evalRvalueIntoPlace_unaryOp {V : Type} (h : RvalueHooks P S C V) (choice : C)
    (operator : Miri.MIR.UnOp) (operand : Miri.MIR.Operand) (place : Miri.MIR.Place) :
    evalRvalueIntoPlace h choice (.UnaryOp operator operand) place = (do
      let dest ← h.evalPlace choice place true
      let layout := h.placeLayout dest
      let val ← h.evalOperandAt choice (OperandPath.rvalue "operand") operand
        (if operator.homogeneous then some layout else none)
      let val ← h.readImmediate choice val
      unaryOpTail h choice operator layout dest val) := by
  unfold evalRvalueIntoPlace unaryOpTail rvalueLayoutCheck
  unfold_named "_private.Miri.Interpreter.Rvalue.0.Miri.Interpreter.assertRvalueLayout"
  rfl

end UnaryOpA2

section UnaryOpWiring

open Miri.ABI Miri.Memory Miri.Interpreter

/-- An `EStateM` bind whose first action succeeds continues from its result. -/
theorem estatem_bind_of_ok {ε σ α β : Type} (m : EStateM ε σ α) (f : α → EStateM ε σ β)
    (s s' : σ) (a : α) (h : m s = .ok a s') : (m >>= f) s = f a s' := by
  simp only [bind, EStateM.bind, h]

variable {K U C O X Host : Type}

/-- The executor's expression dictionary evaluates operands with the
consumer-side `OperandMachine.evalOperandAt`, reads them with
`PlaceMachine.readImmediate` over the validated access configuration, and applies
`ScalarOps.unary` (whose `PtrMetadata` arm reads no memory: it checks the read
immediate and extracts its metadata). -/
theorem rvalueHooks_operand_wiring [DecidableEq K] (h : ExecutionMachine.Config K U C O X Host)
    (limits : ExecutionMachine.Limits) :
    (ExecutionMachine.rvalueHooks h limits).evalOperandAt =
      OperandMachine.evalOperandAt
        (ExecutionMachine.operandHooks (ExecutionMachine.withValidation h limits)) ∧
    (ExecutionMachine.rvalueHooks h limits).readImmediate =
      (fun _ => PlaceMachine.readImmediate (ExecutionMachine.withValidation h limits).access) ∧
    (ExecutionMachine.rvalueHooks h limits).unaryOp =
      ScalarOps.unary (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation h limits)) ∧
    (ExecutionMachine.rvalueHooks h limits).placeLayout = RuntimePlace.layout :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- With the configuration flag on, both the operand dictionary and the
validated access configuration of the executor are in `deinitMovedPlace` mode. -/
theorem withValidation_deinit_flags [DecidableEq K] (h : ExecutionMachine.Config K U C O X Host)
    (limits : ExecutionMachine.Limits) (hon : h.deinitMovedPlace = true) :
    (ExecutionMachine.operandHooks
      (ExecutionMachine.withValidation h limits)).deinitMovedPlace = true ∧
    (ExecutionMachine.withValidation h limits).access.deinitMovedPlace = true := by
  simp [ExecutionMachine.operandHooks, ExecutionMachine.withValidation, hon]

/-- **`UnaryOp` (including `PtrMetadata`) of a moved memory place in the real
executor dictionary, universal.** With `deinitMovedPlace = true`, the assignment
`dest = UnaryOp(op, move place)` evaluates the destination, queues the moved
operand, reads it whole and deinitializes the *entire* moved place
`⟨mplace, layout⟩` (the layout of `place` itself, for a wide pointer both its data
pointer and its metadata) before the unary operator runs; the operator and the
destination write then start from the deinitialized state. -/
theorem rvalueHooks_unaryOp_move_indirect [DecidableEq K]
    (h : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits) (c : C)
    (operator : Miri.MIR.UnOp) (place destPlace : Miri.MIR.Place)
    (s s₀ s₁ s₂ s₃ : MachineHooks.State K U) (dest : ExecutionMachine.Value)
    (mplace : MemPlace Provenance) (layout : LocalLayout) (val : RvalueImmTy Provenance)
    (hon : h.deinitMovedPlace = true)
    (hdest : (ExecutionMachine.rvalueHooks h limits).evalPlace c destPlace true s = .ok dest s₀)
    (hqueueEmpty : s₁.machine.pendingMoveDeinits = #[])
    (hevalPlace : OperandMachine.evalPlaceToOp
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation h limits)) c place
      (if operator.homogeneous then some dest.layout else none)
      { s₀ with machine := MachineHooks.clearPendingMoveDeinitFlag s₀.machine } =
        .ok ⟨.indirect mplace, layout⟩ s₁)
    (hreadMiri : srcReadImmediate (ExecutionMachine.withValidation h limits).access
      ⟨.indirect mplace, layout⟩
      { s₁ with
        machine :=
          MachineHooks.MachineState.withPendingMoves
            (MachineHooks.MachineState.withPendingMoves s₁.machine true #[(mplace, true)])
            false
            ((#[(mplace, true)] : Array (MemPlace Provenance × Bool)).eraseIdxIfInBounds 0) } =
        .ok val s₂)
    (hdeinitMiri : PlaceMachine.writeMemoryRawUninit (ExecutionMachine.withValidation h limits).access
      ⟨mplace, layout⟩ s₂ = .ok () s₃) :
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks h limits) c (.UnaryOp operator (.Move place))
        destPlace s =
      unaryOpTail (ExecutionMachine.rvalueHooks h limits) c operator dest.layout dest val s₃ := by
  obtain ⟨hopOn, hcfgOn⟩ := withValidation_deinit_flags h limits hon
  obtain ⟨hEval, hRead, -, hLayout⟩ := rvalueHooks_operand_wiring h limits
  have hread := operandRead_move_indirect
    (ExecutionMachine.operandHooks (ExecutionMachine.withValidation h limits))
    (ExecutionMachine.withValidation h limits).access c (OperandPath.rvalue "operand") place
    (if operator.homogeneous then some dest.layout else none) s₀ s₁ s₂ s₃ mplace layout val
    hopOn hcfgOn rfl hqueueEmpty hevalPlace hreadMiri hdeinitMiri
  rw [evalRvalueIntoPlace_unaryOp, estatem_bind_of_ok _ _ s s₀ dest hdest, hEval, hRead, hLayout,
    ← bind_assoc, estatem_bind_of_ok _ _ s₀ s₃ val hread]

end UnaryOpWiring

/-! ### Consumer-side casts: the real `Cast.castMoving` event order

A logging hook dictionary drives the real `Cast.castMoving`. Its latch flag
models the pending move record of the cast's source operand
(`takePendingMoveDeinit` consumes it; `restorePendingMoveDeinit true` re-arms it,
as `ExecutionCast.hooks` does; the logging `copyAllowTransmute`/`copyNoValidate`
consume it, as `copyRuntimePlaceNoValidate` does). -/

section CastToy

open Miri.ABI Miri.Memory Miri.Interpreter

/-- `Unit` provenance for the cast toy (no allocation identities). -/
local instance toyPointerProvenance : PointerProvenance Unit := ⟨false, none, fun _ => none⟩

/-- Toy cast state: the latch flag and the event log. -/
structure ToyCastState where
  armed : Bool
  log : List String

/-- A two-field, memory-represented ADT layout. -/
def toyAdtLayout : LayoutData :=
  { toyByteLayout with fields := .Arbitrary #[⟨0⟩, ⟨1⟩] #[0, 1], size := ⟨2⟩ }

/-- Append an event. -/
def toyLog (e : String) : RvalueM ToyCastState Unit :=
  modify fun s => { s with log := s.log ++ [e] }

/-- Logging cast hooks. Type ids: `0` a raw pointer; `10`/`11` the source/target
ADT (`.adt 1`), whose field `0` keeps type `20` and whose field `1` changes from
`30` (`*const dyn`, pointee tail `40`) to `31` (pointee tail `41`), both tails the
same `dyn` (`.dynamic 3`). -/
def toyCastHooks : CastHooks Unit ToyCastState Unit Unit where
  target := ⟨.little, .w64⟩
  typeInfo := fun _ ty =>
    match ty with
    | 10 | 11 => pure (.adt 1)
    | 30 => pure (.rawPointer 40)
    | 31 => pure (.rawPointer 41)
    | 40 | 41 => pure (.dynamic 3)
    | _ => pure (.rawPointer 0)
  layoutOf := fun _ ty => pure (if ty == 11 then ⟨11, toyAdtLayout⟩ else toyU8)
  destLayout := fun _ => toyU8
  readImmediate := fun _ op => do
    toyLog "read"
    pure ⟨.scalar (Scalar.fromBool true), op.layout⟩
  writeImmediate := fun _ _ _ => toyLog "write"
  writePointer := fun _ _ _ => toyLog "writePointer"
  enforceValidity := fun _ _ => pure false
  enforceValidityRecursively := fun _ _ => pure false
  validatePlace := fun _ _ _ _ => toyLog "validate"
  derefPointer := fun _ _ => throw (.unsupported "toy")
  checkFunctionPointer := fun _ _ => throw (.unsupported "toy")
  exposeProvenance := fun _ _ => throw (.unsupported "toy")
  pointerFromExposedAddress := fun _ _ => throw (.unsupported "toy")
  usizeLayout := fun _ => throw (.unsupported "toy")
  floatOps :=
    { integerKindOf := fun _ _ => throw (.unsupported "toy")
      formatOf := fun _ _ => throw (.unsupported "toy")
      boolLayout := fun _ => throw (.unsupported "toy")
      floatNondeterministic := false
      chooseNaN := fun _ _ => throw (.unsupported "toy") }
  ensureMonomorphic := fun _ _ => pure ()
  requireNoBoundVars := fun _ _ => pure ()
  resolveFunction := fun _ _ _ => throw (.unsupported "toy")
  resolveClosureFnOnce := fun _ _ _ => throw (.unsupported "toy")
  functionPointer := fun _ _ => throw (.unsupported "toy")
  builtinDeref := fun _ _ _ => throw (.unsupported "toy")
  boxLayout := fun _ _ => throw (.unsupported "toy")
  validateImmediateABI := fun _ _ => .ok ()
  copyAllowTransmute := fun _ _ _ => do
    let s ← get
    set { s with armed := false,
                 log := s.log ++ [if s.armed then "copyAllowTransmute+deinit" else "copyAllowTransmute"] }
  copyNoValidate := fun _ _ _ _ => do
    let s ← get
    set { s with armed := false,
                 log := s.log ++ [if s.armed then "copyNoValidate+deinit" else "copyNoValidate"] }
  projectRead := fun _ op i => pure ⟨op.op, ⟨if i == 0 then 20 else 30, toyByteLayout⟩⟩
  projectWrite := fun _ _ _ => pure ()
  fieldLayout := fun _ _ i => pure ⟨if i == 0 then 20 else 31, toyByteLayout⟩
  lockstepTails := fun _ a b => pure (a, b)
  vtableType := fun _ _ _ => throw (.unsupported "toy")
  vtablePointer := fun _ _ _ => throw (.unsupported "toy")
  principal := fun _ _ => throw (.unsupported "toy")
  vtableEntries := fun _ _ _ => throw (.unsupported "toy")
  supertraitSlot := fun _ _ _ => throw (.unsupported "toy")
  eraseSelfTraitRef := fun _ _ => throw (.unsupported "toy")
  normalizePrincipal := fun _ _ => throw (.unsupported "toy")
  takePendingMoveDeinit := do
    let s ← get
    set { s with armed := false, log := s.log ++ ["take"] }
    pure s.armed
  restorePendingMoveDeinit := fun flag =>
    if flag then modify fun s => { s with armed := true, log := s.log ++ ["restore"] } else pure ()
  deinitSource := fun _ source =>
    match source.op with
    | .immediate _ => pure ()
    | .indirect _ => toyLog "deinit"

/-- A memory-backed pointer source operand. -/
def toyCastSrc : OpTy Unit := ⟨.indirect (toyMPlace 1), toyU8⟩

/-- A memory-backed ADT source operand (type id `10`). -/
def toyCastAdtSrc : OpTy Unit := ⟨.indirect (toyMPlace 1), ⟨10, toyAdtLayout⟩⟩

/-- **`PtrToPtr` of a moved source.** The latch is consumed first, the source is
read, then deinitialized, and only then is the destination written (so a
self-assignment `_1 = move _1 as *const T` keeps its value); with a disarmed
latch (a `copy` source) nothing is deinitialized. -/
theorem canary_castMoving_ptrToPtr :
    Cast.castMoving toyCastHooks () 4 toyCastSrc .PtrToPtr 0 () { armed := true, log := [] } =
      .ok () { armed := false, log := ["take", "read", "deinit", "write"] } ∧
    Cast.castMoving toyCastHooks () 4 toyCastSrc .PtrToPtr 0 () { armed := false, log := [] } =
      .ok () { armed := false, log := ["take", "read", "write"] } :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl⟩

/-- **`Transmute` of a moved source.** The latch is handed on to the consuming
`copyAllowTransmute` (`restore`), which therefore deinitializes the source. -/
theorem canary_castMoving_transmute :
    Cast.castMoving toyCastHooks () 4 toyCastSrc .Transmute 0 () { armed := true, log := [] } =
      .ok () { armed := false, log := ["take", "restore", "copyAllowTransmute+deinit"] } ∧
    Cast.castMoving toyCastHooks () 4 toyCastSrc .Transmute 0 () { armed := false, log := [] } =
      .ok () { armed := false, log := ["take", "copyAllowTransmute"] } :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl⟩

/-- **Unsizing an ADT whose second field is a moved `*const dyn` pointer.** The
unchanged field receives the latch (`restore`) and is copied-and-deinitialized
by `copyNoValidate`; the unsized pointer leaf is read, then deinitialized, then
written. With a disarmed latch (`copy` source) the source `unsizeInto` runs and
nothing is deinitialized. -/
theorem canary_castMoving_unsize_adt :
    Cast.castMoving toyCastHooks () 4 toyCastAdtSrc (.PointerCoercion .Unsize .AsCast) 11 ()
        { armed := true, log := [] } =
      .ok () { armed := false,
               log := ["take", "restore", "copyNoValidate+deinit", "read", "deinit", "write"] } ∧
    Cast.castMoving toyCastHooks () 4 toyCastAdtSrc (.PointerCoercion .Unsize .AsCast) 11 ()
        { armed := false, log := [] } =
      .ok () { armed := false, log := ["take", "copyNoValidate", "read", "write"] } :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl⟩

end CastToy

/-! ### `CopyNonOverlapping`, `Repeat`, `Aggregate`, `RustCall`/`Virtual` & `D8` Unwind Cleanup -/

section CopyNonOverlappingAndRepeatToy

open Miri.ABI Miri.Memory Miri.Interpreter

local instance toyPointerProvenanceCno : PointerProvenance Unit := ⟨false, none, fun _ => none⟩

/-- **`OperandMachine.evalOperandAt` on `CopyNonOverlapping`'s `count` path, universal.**
When `deinitMovedPlace = true` and `path = OperandPath.instruction "count"`,
evaluating `Operand.Move place` to `⟨.indirect mplace, layout⟩` records
`(mplace, true)` and then runs `MachineHooks.prependLastPendingMoveDeinit` so the
`count` entry moves to the front of `pendingMoveDeinits` (matching
`Intrinsics.copyWith`'s read order: `count`, then `src`, then `dst`). -/
theorem operandMachine_evalOperandAt_count_prepends_latch {K User C : Type}
    (h : OperandMachine.Hooks K User C) (c : C) (place : Miri.MIR.Place)
    (known : Option LocalLayout) (s s₁ : MachineHooks.State K User)
    (mplace : MemPlace Provenance) (layout : LocalLayout)
    (hon : h.deinitMovedPlace = true)
    (heval : OperandMachine.evalPlaceToOp h c place known
      { s with machine := MachineHooks.clearPendingMoveDeinitFlag s.machine } =
        .ok ⟨.indirect mplace, layout⟩ s₁) :
    OperandMachine.evalOperandAt h c (OperandPath.instruction "count") (.Move place) known s =
      .ok ⟨.indirect mplace, layout⟩
        { s₁ with
          machine :=
            MachineHooks.prependLastPendingMoveDeinit
              (MachineHooks.recordPendingMoveDeinit s₁.machine mplace true) } := by
  have hpath : (OperandPath.instruction "count" == OperandPath.instruction "count") = true := rfl
  simp only [OperandMachine.evalOperandAt, hon, ↓reduceIte, OperandMachine.evalOperandAtMoving,
    OperandMachine.evalOperandMoving, OperandMachine.updateMoveLatch, bind, EStateM.bind,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, heval, hpath, pure, EStateM.pure]

/-- Prepending the last queued entry moves `count` ahead of `src` and `dst`. -/
theorem prependLastPendingMoveDeinit_three {K User : Type}
    (m : MachineHooks.MachineState K User)
    (src dst cnt : MemPlace Provenance × Bool) (flag : Bool) :
    (MachineHooks.prependLastPendingMoveDeinit
      (m.withPendingMoves flag #[src, dst, cnt])).pendingMoveDeinits =
      #[cnt, src, dst] := rfl

/-- **Universal decomposition of `Intrinsics.evalNondivergingWith` on `CopyNonOverlapping`.**
`evalNondivergingWith` evaluates `src`, then `dst`, then `count` via
`evalOperandAt` (whose `count` path prepends `count`'s latch entry to the front
of `pendingMoveDeinits`, `operandMachine_evalOperandAt_count_prepends_latch`),
and then invokes `Intrinsics.copyWith` (which reads `count`, then `src`, then
`dst`). -/
theorem intrinsics_evalNondivergingWith_copyNonOverlapping_eq
    {P S C : Type} [PointerProvenance P] (h : MemoryIntrinsicHooks P S C)
    (evalOpAt : C → OperandPath → Miri.MIR.Operand → RvalueM S (OpTy P)) (choice : C)
    (args : Miri.MIR.CopyNonOverlapping) :
    Intrinsics.evalNondivergingWith h evalOpAt choice (.CopyNonOverlapping args) = (do
      let source ← evalOpAt choice (OperandPath.instruction "src") args.source
      let dest ← evalOpAt choice (OperandPath.instruction "dst") args.destination
      let count ← evalOpAt choice (OperandPath.instruction "count") args.count
      Intrinsics.copyWith h choice source dest count true) := by
  with_unfolding_all rfl

/-- `OperandMachine.evalOperandAtMoving` over `ToyRvState`: prepends the last
queued entry when `path == OperandPath.instruction "count"`. -/
def toyRvEvalAt (_ : Unit) (path : OperandPath) (operand : Miri.MIR.Operand) :
    RvalueM ToyRvState (OpTy Unit) := do
  let res ← toyRvEval operand
  if path == OperandPath.instruction "count" then
    if let .indirect _ := res.op then
      modify fun s =>
        match s.queue.getLast? with
        | none => s
        | some last => { s with queue := last :: s.queue.dropLast }
  return res

/-- Concrete `CopyNonOverlapping` runner matching
`intrinsics_evalNondivergingWith_copyNonOverlapping_eq` + `Intrinsics.copyWith`'s
read order (`count`, then `src`, then `dst`). -/
def toyEvalCopyNonOverlapping (args : Miri.MIR.CopyNonOverlapping) :
    RvalueM ToyRvState Unit := do
  let source ← toyRvEvalAt () (OperandPath.instruction "src") args.source
  let dest ← toyRvEvalAt () (OperandPath.instruction "dst") args.destination
  let count ← toyRvEvalAt () (OperandPath.instruction "count") args.count
  let _ ← toyRvRead count
  let _ ← toyRvRead source
  let _ ← toyRvRead dest
  modify fun s => { s with written := true }

/-- `_1 = 16` (`src`), `_2 = 32` (`dst`), `_3 = 0` (`count == 0`), all memory-backed. -/
def cnoZeroState : ToyRvState :=
  { slots := [.mem, .mem, .mem, .mem],
    cells := [none, some 16, some 32, some 0],
    queue := [], reads := [], written := false }

/-- **`CopyNonOverlapping` move deinitialization (including `count == 0`).**
1. `copy_nonoverlapping(move _1, copy _2, move _3)` with `_3 = 0`: `evalOperandAt`
   evaluates `src` (`_1`), `dst` (`_2`), `count` (`_3`) and moves `_3` to the
   front of the latch queue; `copyWith` then reads `count` (`0`), `src` (`16`),
   `dst` (`32`) in order, consuming all three FIFO entries and deinitializing
   both moved operands (`_3` and `_1`) while leaving `_2 = 32` intact — even
   when `count == 0`!
2. `copy_nonoverlapping(move _1, copy _1, copy _3)` faults with
   `invalidUninitBytes` when reading `dst` after `src = move _1` deinitialized
   `_1`.
3. `copy_nonoverlapping(copy _1, move _1, copy _3)` succeeds (`src` reads `16`
   without deinitializing `_1`, then `dst` reads `16` and deinitializes `_1`). -/
theorem canary_copyNonOverlapping_move_deinit :
    toyEvalCopyNonOverlapping ⟨.Move ⟨1, #[]⟩, .Copy ⟨2, #[]⟩, .Move ⟨3, #[]⟩⟩
        cnoZeroState =
      .ok () { cnoZeroState with
               cells := [none, none, some 32, none],
               queue := [], reads := [0, 16, 32], written := true } ∧
    toyEvalCopyNonOverlapping ⟨.Move ⟨1, #[]⟩, .Copy ⟨1, #[]⟩, .Copy ⟨3, #[]⟩⟩
        cnoZeroState =
      .error (.undefinedBehavior "invalidUninitBytes")
        { cnoZeroState with
          cells := [none, none, some 32, some 0],
          queue := [], reads := [0, 16], written := false } ∧
    toyEvalCopyNonOverlapping ⟨.Copy ⟨1, #[]⟩, .Move ⟨1, #[]⟩, .Copy ⟨3, #[]⟩⟩
        cnoZeroState =
      .ok () { cnoZeroState with
               cells := [none, none, some 32, some 0],
               queue := [], reads := [0, 16, 16], written := true } :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩

/-- `AggregateHooks` driving the real `Miri.Interpreter.writeAggregate` and the
consumer-side `writeRepeat` of `ExecutionMachine.rvalueHooks`. -/
def toyAggHooks (repeatLen : UInt64) : AggregateHooks Unit ToyRvState Unit Nat where
  target := ⟨.little, .w64⟩
  placeLayout := fun _ => toyU8
  evalOperand := fun _ op _ => toyRvEval op
  evalOperandAt := fun _ _ op _ => toyRvEval op
  readPointer := fun _ _ => throw (.unsupported "toy")
  readScalar := fun _ _ => throw (.unsupported "toy")
  projectDowncast := fun _ d _ => pure d
  projectField := fun _ d idx => pure (d + idx)
  copyOp := fun _ op dst => do
    let s ← get
    match op.op with
    | .indirect m =>
      let n := toyCell m
      let (queue, isMove) := toyTake s.queue n
      match (s.cells[n]?).join with
      | none =>
        set { s with queue }
        throw (.undefinedBehavior "invalidUninitBytes")
      | some v =>
        let cells := if isMove then s.cells.set n none else s.cells
        set { s with queue, reads := s.reads ++ [v], cells := cells.set dst (some v) }
    | _ => throw (.unsupported "toy")
  copyOpNoValidate := fun _ op dst _ => do
    let s ← get
    match op.op with
    | .indirect m =>
      let n := toyCell m
      let (queue, isMove) := toyTake s.queue n
      match (s.cells[n]?).join with
      | none =>
        set { s with queue }
        throw (.undefinedBehavior "invalidUninitBytes")
      | some v =>
        let cells := if isMove then s.cells.set n none else s.cells
        set { s with queue, reads := s.reads ++ [v], cells := cells.set dst (some v) }
    | _ => throw (.unsupported "toy")
  writeDiscriminant := fun _ _ _ => pure ()
  enforceValidity := fun _ _ => pure false
  validate := fun _ _ => pure ()
  forceAllocation := fun _ d => pure d
  length := fun _ _ => pure repeatLen
  getPlaceAllocMut := fun _ _ => pure ()
  projectIndex := fun _ d idx => pure (d + idx.toNat)
  placePointer := fun d => .ok ⟨⟨d.toUInt64⟩, none⟩
  wrappingOffset := fun p sz => .ok ⟨⟨(p.offset.bytes.toNat + sz.bytes.toNat).toUInt64⟩, none⟩
  memCopyRepeatedly := fun _ src dst _ _ _ => do
    let s ← get
    let v := (s.cells[src.offset.bytes.toNat]?).join
    let base := dst.offset.bytes.toNat
    let cells := (s.cells.set base v).set (base + 1) v
    set { s with cells, written := true }

/-- Consumer-side `writeRepeat` of `ExecutionMachine.rvalueHooks` over `toyAggHooks`. -/
def toyWriteRepeatMoving (repeatLen : UInt64) (operand : Miri.MIR.Operand) (dest : Nat) :
    RvalueM ToyRvState Unit := do
  let aggregate := toyAggHooks repeatLen
  let source ← aggregate.evalOperandAt () (OperandPath.rvalue "operand") operand none
  if !source.layout.layout.isSized then throw (.invalidProgram "repeat source is unsized")
  let dest ← aggregate.forceAllocation () dest
  let length ← aggregate.length () dest
  if length == 0 then
    aggregate.getPlaceAllocMut () dest
    let s ← get
    let (queue, isMove) :=
      match s.queue.getLast? with
      | some (_, mv) => (s.queue.dropLast, mv)
      | none => ([], false)
    if isMove then
      if let .indirect mplace := source.op then
        set { s with queue, cells := s.cells.set (toyCell mplace) none }
      else set { s with queue }
    else set { s with queue }
  else
    let first ← aggregate.projectIndex () dest 0
    aggregate.copyOp () source first
    let elemSize := (aggregate.placeLayout first).layout.size
    let .ok firstPtr := aggregate.placePointer first | throw (.invalidProgram "ptr")
    let .ok restPtr := aggregate.wrappingOffset firstPtr elemSize | throw (.invalidProgram "off")
    aggregate.memCopyRepeatedly () firstPtr restPtr elemSize 2 true

/-- `_1 = 5` at cell 1; destination array at cells 2..5. -/
def repeatInitState : ToyRvState :=
  { slots := [.mem, .mem], cells := [none, some 5, none, none, none],
    queue := [], reads := [], written := false }

/-- **`Rvalue.Repeat` move deinitialization for `count == 0` and `count == 3`.**
1. `Repeat (.Move _1) 0` (`length == 0`): consumes the move latch and
   deinitializes `_1` via TB-silent `deinitMemoryRaw` without reading or writing
   elements.
2. `Repeat (.Copy _1) 0` (`length == 0`): consumes the non-move latch (`false`),
   leaving `_1 = 5` initialized and the queue empty.
3. `Repeat (.Move _1) 3` (`length == 3`): `copyOp` copies `5` into `dest[0]`
   (cell 2) and deinitializes `_1` (cell 1), then `memCopyRepeatedly` replicates
   `dest[0]` into `dest[1]` and `dest[2]` (cells 3 and 4). -/
theorem canary_repeat_move_deinit_zero_and_nonzero :
    toyWriteRepeatMoving 0 (.Move ⟨1, #[]⟩) 2 repeatInitState =
      .ok () { repeatInitState with cells := [none, none, none, none, none], queue := [] } ∧
    toyWriteRepeatMoving 0 (.Copy ⟨1, #[]⟩) 2 repeatInitState =
      .ok () { repeatInitState with cells := [none, some 5, none, none, none], queue := [] } ∧
    toyWriteRepeatMoving 3 (.Move ⟨1, #[]⟩) 2 repeatInitState =
      .ok () { repeatInitState with
               cells := [none, none, some 5, some 5, some 5],
               queue := [], reads := [5], written := true } :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩

/-- `_1 = (2, 3)` at cells 1 and 2; destination tuple at cells 3 and 4. -/
def aggPairState : ToyRvState :=
  { slots := [.mem, .mem], cells := [none, some 2, some 3, none, none],
    queue := [], reads := [], written := false }

/-- **`Rvalue.Aggregate` move deinitialization through the real `writeAggregate`.**
1. `.Tuple #[.Move _1.1, .Move _1.0]` copies `3` into field `0` and deinitializes
   `_1.1`, then copies `2` into field `1` and deinitializes `_1.0`.
2. `.Tuple #[.Move _1.0, .Copy _1.0]` deinitializes `_1.0` on field `0` and
   faults with `invalidUninitBytes` on field `1`. -/
theorem canary_aggregate_move_deinit :
    writeAggregate (toyAggHooks 0) () .Tuple
        #[.Move ⟨1, #[.Field 1 0]⟩, .Move ⟨1, #[.Field 0 0]⟩] 3 aggPairState =
      .ok () { aggPairState with
               cells := [none, none, none, some 3, some 2],
               queue := [], reads := [3, 2] } ∧
    writeAggregate (toyAggHooks 0) () .Tuple
        #[.Move ⟨1, #[.Field 0 0]⟩, .Copy ⟨1, #[.Field 0 0]⟩] 3 aggPairState =
      .error (.undefinedBehavior "invalidUninitBytes")
        { aggPairState with
          cells := [none, none, some 3, some 2, none],
          queue := [], reads := [2] } :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl⟩

end CopyNonOverlappingAndRepeatToy

section CallUnpackVirtualAndUnwindD8

open Miri.ABI Miri.Memory Miri.Interpreter

/-- **`Call.allocateVarargs` on consumer-side `FnArg.Copy` arguments, universal.**
Since `Call.evalFnCallArgumentMoving` produces only `FnArg.Copy` arguments,
`Call.allocateVarargs` is independent of `protectArgument`. -/
theorem call_allocateVarargs_protect_irrelevant
    {P S C E Other Extern FnABI ArgABI : Type}
    (h : CallHooks P S C E Other Extern FnABI ArgABI)
    (protect : C → MPlaceTy P → CallM S Unit)
    (choice : C) (args : Array (FnArg P × ArgABI)) (calleeAbis : Array ArgABI) :
    Call.allocateVarargs { h with protectArgument := protect } choice args calleeAbis =
      Call.allocateVarargs h choice args calleeAbis := rfl

/-- Extended call/unwind state for end-to-end `RustCall` tuple unpacking,
`FnInstance.Virtual` receiver dispatch, and `D8` unwinding call / `Assert`
cleanup. -/
structure ToyD8State where
  callerCells : List (Option Nat)
  calleeCells : List (Option Nat)
  temps : List Nat
  freedTemps : List Nat
  inCallee : Bool
  block : Miri.MIR.BasicBlockId
  unwinding : Bool
  panicCalled : Bool

/-- Read a cell from `callerCells`. -/
def d8ReadCaller (l : Nat) : EStateM StepError ToyD8State Nat := do
  let s ← get
  match (s.callerCells[l]?).join with
  | some v => pure v
  | none => throw (.undefinedBehavior "invalidUninitBytes")

/-- Minimal MIR body with two blocks (`0` normal, `1` cleanup). -/
def d8DummyBlock (isCleanup : Bool) : Miri.MIR.BasicBlock :=
  { statements := #[],
    terminator := ⟨⟨⟨0⟩, 0⟩, .Return⟩,
    cleanup := isCleanup }

def d8DummyBody (argCount : Nat) (spread : Option Nat := none) : Miri.Interpreter.LoadedBody :=
  { identity := .ofCanonicalIndex 0,
    body :=
      { phase := .Runtime .PostCleanup,
        basicBlocks := #[d8DummyBlock false, d8DummyBlock true],
        locals := #[0, 0, 0, 0],
        argumentCount := argCount,
        spreadArgument := spread } }

def d8Frame (blk : Nat) (unw : Bool) (argCount : Nat := 1) :
    Frame Unit LocalLayout Unit :=
  { bodyIdentity := .ofCanonicalIndex 0,
    functionInstance := ⟨.Item 1, #[]⟩,
    body := (d8DummyBody argCount).body,
    returnPlace := .frameLocal 0 0 none toyU8 (.ofAllocationToken 0),
    returnContinuation := .goto (some 0) (.Cleanup 1),
    location := if unw then .unwinding ⟨0⟩ else .mir ⟨blk, 0⟩,
    locals := #[],
    localsIdentity := .ofAllocationToken 0,
    trackCallerArg := none,
    vaList := #[],
    extra := () }

/-- Call hooks supporting `RustCall` tuple unpacking (`defId = 10`) and
`FnInstance.Virtual` dispatch (`defId = 20`) into `initStackFrame`. -/
def d8CallHooks (isRustCallMode : Bool) (isVirtualMode : Bool) :
    CallHooks Unit ToyD8State Unit Unit Unit Unit Unit Unit where
  debugAssertions := false
  getFrame := do
    let s ← get
    pure (d8Frame s.block s.unwinding (if isRustCallMode then 1 else 2))
  setFrame := fun f => modify fun s =>
    match f.location with
    | .unwinding _ => { s with unwinding := true }
    | .mir loc => { s with block := loc.block, unwinding := false }
  frameIndex := do
    let s ← get
    pure (if s.inCallee then 1 else 0)
  evalOperand := fun _ op =>
    match op with
    | .Copy ⟨0, _⟩ => pure ⟨.immediate .uninit, toyFnLayout⟩
    | .Copy p | .Move p => pure ⟨.indirect (toyMPlace p.localId), toyU8⟩
    | _ => pure ⟨.immediate .uninit, toyU8⟩
  evalPlace := fun _ p _ => pure (.memory ⟨toyMPlace p.localId, toyU8⟩)
  placeToOp := fun _ rp =>
    match rp with
    | .memory m => pure ⟨.indirect m.mplace, m.layout⟩
    | _ => throw (.unsupported "d8")
  forceAllocation := fun _ rp =>
    match rp with
    | .memory m => pure m
    | _ => throw (.unsupported "d8")
  functionSignature := fun _ _ => pure (if isRustCallMode then 1 else 2, ())
  functionKind := fun _ => pure (.FnDef (if isVirtualMode then 20 else 10) #[])
  readPointer := fun _ _ => throw (.unsupported "d8")
  getPtrFn := fun _ _ => throw (.unsupported "d8")
  resolve := fun _ defId _ =>
    if defId == 20 then pure ⟨.Virtual 20 0, #[]⟩
    else pure ⟨.Item defId, #[]⟩
  fnAbiOfFnPtr := fun _ _ _ => pure ()
  fnAbiOfInstance := fun _ _ _ => pure ()
  requiresCallerLocation := fun _ => pure false
  callerLocation := pure ⟨0⟩
  abiCanUnwind := fun _ => true
  abiVariadic := fun _ => false
  abiFixedCount := fun _ => 0
  abiArgs := fun _ => if isRustCallMode then #[(), ()] else #[(), ()]
  abiReturn := fun _ => ()
  sameConvention := fun _ _ => true
  isRustCall := fun _ => isRustCallMode
  rustAbi := ()
  argLayout := fun _ => toyU8
  argIsIgnore := fun _ => false
  isOneZst := fun _ => false
  checkArgumentCompat := fun _ _ _ => pure true
  checkTargetFeatures := fun _ _ => pure ()
  tupleFields := fun _ => pure #[0, 0]
  projectFnArg := fun _ arg idx =>
    match arg with
    | .Copy op =>
      match op.op with
      | .indirect m => pure (.Copy ⟨.indirect (toyMPlace (toyCell m + idx)), toyU8⟩)
      | _ => pure (.Copy op)
    | .InPlace _ => throw (.invalidProgram "expected FnArg.Copy")
  localLayout := fun _ _ => pure toyU8
  localSpan := fun _ _ => pure ⟨0⟩
  storageLiveDyn := fun _ _ _ => pure ()
  copyAllowTransmute := fun _ src dst => do
    let s ← get
    match src.op, dst with
    | .indirect m, .memory d =>
      let cellIdx := toyCell m
      let v ← match (s.callerCells[cellIdx]?).join with
        | some v => pure v
        | none => throw (.undefinedBehavior "invalidUninitBytes")
      set { s with calleeCells := s.calleeCells.set (toyCell d.mplace) (some v) }
    | .immediate _, .memory d =>
      set { s with calleeCells := s.calleeCells.set (toyCell d.mplace) (some 99) }
    | _, _ => throw (.unsupported "d8 copyAllowTransmute")
  protectArgument := fun _ m =>
    if toyCell m.mplace == 0 then pure ()
    else throw (.invalidProgram "protectArgument must not run on FnArg.Copy")
  withRetagMode := fun _ _ action => action
  nonCapturingClosure := fun _ _ _ => pure false
  allocateStack := fun _ layout => do
    let s ← get
    let tmpCell := 4 + s.temps.length * 2
    set { s with temps := s.temps ++ [tmpCell] }
    pure ⟨toyMPlace tmpCell, layout⟩
  copyToMemory := fun _ src dst => do
    let s ← get
    match src.op with
    | .indirect m =>
      let c := toyCell m
      let d := toyCell dst.mplace
      if isRustCallMode then
        match (s.callerCells[c]?).join, (s.callerCells[c + 1]?).join with
        | some v0, some v1 =>
          set { s with callerCells := (s.callerCells.set d (some v0)).set (d + 1) (some v1) }
        | _, _ => throw (.undefinedBehavior "invalidUninitBytes")
      else
        match (s.callerCells[c]?).join with
        | some v => set { s with callerCells := s.callerCells.set d (some v) }
        | none => throw (.undefinedBehavior "invalidUninitBytes")
    | _ => throw (.unsupported "d8 copyToMemory")
  vaListPtr := fun _ _ => throw (.unsupported "d8")
  writeZeroBytes := fun _ _ _ => throw (.unsupported "d8")
  vaListKeyField := fun _ _ => throw (.unsupported "d8")
  writePointerToMemory := fun _ _ _ => throw (.unsupported "d8")
  pushRaw := fun _ _ _ _ _ => modify fun s => { s with inCallee := true, unwinding := true }
  pushDone := fun _ => modify fun s => { s with unwinding := false }
  popRaw := fun _ => do
    let s ← get
    set { s with inCallee := false }
    pure (d8Frame s.block s.unwinding)
  cleanup := fun _ _ _ => pure .normal
  afterFrameInit := fun _ => pure ()
  callExtra := fun _ _ _ _ _ _ _ => throw (.unsupported "d8")
  callIntrinsic := fun _ _ _ _ _ _ => throw (.unsupported "d8")
  callLlvmIntrinsic := fun _ _ _ _ _ => throw (.unsupported "d8")
  findMirOrEvalFn := fun _ _ _ args _ _ _ => do
    let copyArgToCallee (arg : FnArg Unit) (calleeSlot : Nat) : CallM ToyD8State Unit := do
      let s ← get
      match arg.copyFnArg.op with
      | .indirect m =>
        match (s.callerCells[toyCell m]?).join with
        | some v => set { s with calleeCells := s.calleeCells.set calleeSlot (some v) }
        | none => throw (.undefinedBehavior "invalidUninitBytes")
      | .immediate _ =>
        set { s with calleeCells := s.calleeCells.set calleeSlot (some 99) }
    if isRustCallMode then
      let some tupleArg := args[0]? | throw (.invalidProgram "missing RustCall tuple")
      let .Copy op := tupleArg | throw (.invalidProgram "expected FnArg.Copy")
      let .indirect m := op.op | throw (.invalidProgram "expected indirect tuple")
      copyArgToCallee (.Copy ⟨.indirect (toyMPlace (toyCell m)), toyU8⟩) 1
      copyArgToCallee (.Copy ⟨.indirect (toyMPlace (toyCell m + 1)), toyU8⟩) 2
    else
      let some arg0 := args[0]? | throw (.invalidProgram "missing arg 0")
      let some arg1 := args[1]? | throw (.invalidProgram "missing arg 1")
      copyArgToCallee arg0 1
      copyArgToCallee arg1 2
    modify fun s => { s with inCallee := true }
    pure none
  resolveVirtual := fun _ _ _ _ abi args => do
    let thinReceiver : FnArg Unit := .Copy ⟨.immediate (.scalar (Scalar.fromBool true)), toyU8⟩
    pure (⟨.Item 10, #[]⟩, abi, args.set! 0 thinReceiver)
  isDynamic := fun _ => pure false
  unpackDynForDrop := fun _ _ => throw (.unsupported "d8")
  resolveDropGlue := fun _ _ => throw (.unsupported "d8")
  mplaceToMutRef := fun _ _ => throw (.unsupported "d8")
  fakeUnitReturn := fun _ => throw (.unsupported "d8")
  deinitMovedPlace := true
  deinitInPlaceArgument := fun _ m => modify fun s =>
    let c := toyCell m.mplace
    if isRustCallMode then
      { s with callerCells := (s.callerCells.set c none).set (c + 1) none }
    else
      { s with callerCells := s.callerCells.set c none }
  validateOperandBeforeCall := fun _ _ => pure ()
  deallocateStack := fun _ ptr => modify fun s =>
    { s with freedTemps := s.freedTemps ++ [ptr.offset.bytes.toNat] }

/-- Initial state for `RustCall` (`_1 = (2, 3)` at caller cells 1 and 2) and
`Virtual` (`_1 = 2`, `_2 = 3`). -/
def d8InitState : ToyD8State :=
  { callerCells := [none, some 2, some 3, none, none, none, none, none],
    calleeCells := [none, none, none, none],
    temps := [], freedTemps := [], inCallee := false, block := 0,
    unwinding := false, panicCalled := false }

/-- **`RustCall` tuple argument unpacking and `FnInstance.Virtual` receiver
dispatch through the real `Call.evalCallTerminatorMoving`.**
1. In `RustCall` mode (`call f(move _1)` where `_1 = (2, 3)` at caller cells 1
   and 2): `evalFnCallArgumentMoving` snapshots the whole tuple into temporary
   cells `(4, 5)` and deinitializes BOTH caller fields (`callerCells[1] = none`,
   `callerCells[2] = none`) without invoking `protectArgument`; `initFnCallStep`
   unpacks the snapshot via `projectFnArg` into two `FnArg.Copy` arguments that
   `initStackFrame` copies into callee locals `_1 = 2` and `_2 = 3`; and
   `deallocateTempArgs` frees temporary `4`.
2. In `Virtual` mode (`call Trait::method(move _1, move _2)`): both `_1` and
   `_2` are snapshotted into temporaries `4` and `6` and deinitialized in the
   caller (`callerCells[1] = none`, `callerCells[2] = none`); `resolveVirtual`
   replaces `args[0]` with the thin receiver pointer (`99`) while `args[1]` stays
   `3`; and `deallocateTempArgs` still frees both original temporary allocations
   `[4, 6]`. -/
theorem canary_call_rustCall_tuple_move_unpack_and_virtual :
    Call.evalCallTerminatorMoving (d8CallHooks true false) () 1
        ⟨⟨⟨0⟩, 0⟩, .Call toyFn #[⟨toySpan, .Move ⟨1, #[]⟩⟩] toyDest (some 0) (.Cleanup 1) .Normal ⟨0⟩⟩
        d8InitState =
      .ok ()
        { callerCells := [none, none, none, none, some 2, some 3, none, none],
          calleeCells := [none, some 2, some 3, none],
          temps := [4], freedTemps := [4], inCallee := true, block := 0,
          unwinding := false, panicCalled := false } ∧
    Call.evalCallTerminatorMoving (d8CallHooks false true) () 2
        ⟨⟨⟨0⟩, 0⟩, .Call toyFn #[⟨toySpan, .Move ⟨1, #[]⟩⟩, ⟨toySpan, .Move ⟨2, #[]⟩⟩]
          toyDest (some 0) (.Cleanup 1) .Normal ⟨0⟩⟩
        d8InitState =
      .ok ()
        { callerCells := [none, none, none, none, some 2, none, some 3, none],
          calleeCells := [none, some 99, some 3, none],
          temps := [4, 6], freedTemps := [4, 6], inCallee := true, block := 0,
          unwinding := false, panicCalled := false } :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl⟩

/-- `ControlFlow.ControlHooks` over `StepState Unit LocalLayout Unit ToyD8State`
for `D8` unwinding call and `Assert` cleanup runs. -/
def d8ControlHooks :
    ControlHooks Unit LocalLayout Unit ToyD8State Unit Unit where
  bodySpan := fun _ => .ok ⟨0⟩
  returnOperand := fun _ state => (state, .ok ())
  popFrame := fun _ state =>
    let popped := d8Frame 1 true
    let callerFrame := d8Frame 0 false
    ({ stack := ⟨#[callerFrame]⟩, machine := { state.machine with inCallee := false } }, .ok popped)
  copyReturn := fun _ _ _ state =>
    ({ state with machine := { state.machine with callerCells := state.machine.callerCells.set 0 (some 77) } },
     .ok ())
  cleanupFrame := fun _ _ _ state => (state, .ok .normal)
  unwindTerminate := fun _ _ state => (state, .ok ())

/-- `ControlFlow.TerminatorHooks` driving the real `ControlFlow.evalTerminator`
on `TerminatorKind.Assert` and `TerminatorKind.Call` / `TerminatorKind.UnwindResume`. -/
def d8TerminatorHooks :
    TerminatorHooks Unit LocalLayout Unit ToyD8State Unit Unit Bool where
  toControlHooks := d8ControlHooks
  evalDiscriminant := fun _ _ state => (state, .ok false)
  compareSwitchCase := fun _ _ _ state => (state, .ok false)
  call := fun _ term state =>
    match Call.evalCallTerminatorMoving (d8CallHooks false false) () 1 term state.machine with
    | .ok () m' =>
      let calleeFrame := d8Frame 1 true
      ({ stack := ⟨#[d8Frame 0 false, calleeFrame]⟩, machine := m' }, .ok ())
    | .error e m' => ({ state with machine := m' }, .error e)
  tailCall := fun _ _ state => (state, .error (.unsupported "d8"))
  drop := fun _ _ _ _ state => (state, .error (.unsupported "d8"))
  ignoreOptionalOverflowChecks := fun _ => false
  readAssertCondition := fun _ op state =>
    match op with
    | .Move p =>
      match (state.machine.callerCells[p.localId]?).join with
      | some v =>
        let m' := { state.machine with callerCells := state.machine.callerCells.set p.localId none }
        ({ state with machine := m' }, .ok (v != 0))
      | none => (state, .error (.undefinedBehavior "invalidUninitBytes"))
    | .Copy p =>
      match (state.machine.callerCells[p.localId]?).join with
      | some v => (state, .ok (v != 0))
      | none => (state, .error (.undefinedBehavior "invalidUninitBytes"))
    | _ => (state, .error (.unsupported "d8"))
  assertPanic := fun _ _ unwind state =>
    let state' := { state with machine := { state.machine with panicCalled := true } }
    ControlFlow.unwindToBlock d8ControlHooks () unwind state'

/-- Initial `StepState` for `D8` runs: caller frame at block `0`, `_1 = 0` (`false`),
`_2 = 1` (`true`). -/
def d8StepInit : StepState Unit LocalLayout Unit ToyD8State :=
  { stack := ⟨#[d8Frame 0 false]⟩,
    machine :=
      { callerCells := [none, some 0, some 1, none, none, none, none, none],
        calleeCells := [none, none, none, none],
        temps := [], freedTemps := [], inCallee := false, block := 0,
        unwinding := false, panicCalled := false } }

/-- Expected `StepState` after `TerminatorKind.Assert (.Move ⟨1, #[]⟩) true ... (.Cleanup 1)`
panics and unwinds to cleanup block `1`. -/
def d8AfterAssertState : StepState Unit LocalLayout Unit ToyD8State :=
  { stack := ⟨#[d8Frame 1 false]⟩,
    machine :=
      { callerCells := [none, none, some 1, none, none, none, none, none],
        calleeCells := [none, none, none, none],
        temps := [], freedTemps := [], inCallee := false, block := 0,
        unwinding := false, panicCalled := true } }

/-- Expected `StepState` right after `Call.evalCallTerminatorMoving` enters the
callee frame with `_1` moved and `_2` copied. -/
def d8AfterCallState : StepState Unit LocalLayout Unit ToyD8State :=
  { stack := ⟨#[d8Frame 0 false, d8Frame 1 true]⟩,
    machine :=
      { callerCells := [none, none, some 1, none, some 0, none, some 1, none],
        calleeCells := [none, some 0, some 1, none],
        temps := [4, 6], freedTemps := [4, 6], inCallee := true, block := 0,
        unwinding := false, panicCalled := false } }

/-- Expected `StepState` after `TerminatorKind.UnwindResume` pops the panicking
callee frame and unwinds the caller frame to cleanup block `1`. -/
def d8AfterUnwindState : StepState Unit LocalLayout Unit ToyD8State :=
  { stack := ⟨#[d8Frame 1 false]⟩,
    machine :=
      { callerCells := [none, none, some 1, none, some 0, none, some 1, none],
        calleeCells := [none, some 0, some 1, none],
        temps := [4, 6], freedTemps := [4, 6], inCallee := false, block := 0,
        unwinding := false, panicCalled := false } }

/-- **`D8` `Assert` cleanup after a moved condition (`canary_D8_assert_cleanup_moved_cond_ub`).**
When `TerminatorKind.Assert (.Move ⟨1, #[]⟩) true msg 0 (.Cleanup 1)` runs on
`_1 = false` (`0`) and `_2 = true` (`1`):
1. `ControlFlow.evalTerminator` reads and deinitializes `_1` via
   `readAssertCondition`, then invokes `assertPanic` and jumps to cleanup block
   `1` (`.mir ⟨1, 0⟩`);
2. In cleanup block `1`, reading the moved condition local `_1` faults with
   `.undefinedBehavior "invalidUninitBytes"`, whereas reading the unmoved local
   `_2` succeeds (`1`). -/
theorem canary_D8_assert_cleanup_moved_cond_ub :
    ControlFlow.evalTerminator d8TerminatorHooks ()
        ⟨⟨⟨0⟩, 0⟩, .Assert (.Move ⟨1, #[]⟩) true .NullPointerDereference 0 (.Cleanup 1)⟩
        d8StepInit =
      (d8AfterAssertState, .ok ()) ∧
    d8AfterAssertState.machine.panicCalled = true ∧
    (d8AfterAssertState.stack.currentFrame?.map (·.location)) = some (.mir ⟨1, 0⟩) ∧
    d8ReadCaller 1 d8AfterAssertState.machine =
      .error (.undefinedBehavior "invalidUninitBytes") d8AfterAssertState.machine ∧
    d8ReadCaller 2 d8AfterAssertState.machine = .ok 1 d8AfterAssertState.machine :=
  ⟨by with_unfolding_all rfl, rfl, by with_unfolding_all rfl, rfl, rfl⟩

/-- **`D8` unwinding `Call` cleanup (`canary_D8_unwinding_call_moved_arg_ub` and
`canary_D8_unwinding_call_unmoved_ok`).**
Run `TerminatorKind.Call func #[⟨span, .Move ⟨1, #[]⟩⟩, ⟨span, .Copy ⟨2, #[]⟩⟩]
dest (some 0) (.Cleanup 1)` through `ControlFlow.evalTerminator` (which calls
`Call.evalCallTerminatorMoving`), followed by `TerminatorKind.UnwindResume` in
the panicking callee (`ControlFlow.returnFromCurrentFrame ... true`):
1. `evalCallTerminatorMoving` snapshots both arguments, deinitializes the moved
   caller local `_1` while leaving the copied caller local `_2` intact, pushes
   the callee frame, and frees the argument snapshots;
2. `UnwindResume` pops the callee frame without writing `dest` (`callerCells[0] = none`)
   and unwinds the caller frame to cleanup block `1` (`.mir ⟨1, 0⟩`);
3. In cleanup block `1`, reading the moved argument local `_1` faults with
   `.undefinedBehavior "invalidUninitBytes"` (`canary_D8_unwinding_call_moved_arg_ub`),
   while reading the unmoved local `_2` succeeds (`canary_D8_unwinding_call_unmoved_ok`). -/
theorem canary_D8_unwinding_call_moved_arg_ub :
    ControlFlow.evalTerminator d8TerminatorHooks ()
        ⟨⟨⟨0⟩, 0⟩, .Call toyFn #[⟨toySpan, .Move ⟨1, #[]⟩⟩, ⟨toySpan, .Copy ⟨2, #[]⟩⟩]
          toyDest (some 0) (.Cleanup 1) .Normal ⟨0⟩⟩
        d8StepInit =
      (d8AfterCallState, .ok ()) ∧
    ControlFlow.evalTerminator d8TerminatorHooks ()
        ⟨⟨⟨0⟩, 0⟩, .UnwindResume⟩
        d8AfterCallState =
      (d8AfterUnwindState, .ok ()) ∧
    (d8AfterUnwindState.stack.currentFrame?.map (·.location)) = some (.mir ⟨1, 0⟩) ∧
    d8AfterUnwindState.machine.callerCells[0]? = some none ∧
    d8ReadCaller 1 d8AfterUnwindState.machine =
      .error (.undefinedBehavior "invalidUninitBytes") d8AfterUnwindState.machine :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl, rfl, rfl⟩

/-- Companion to `canary_D8_unwinding_call_moved_arg_ub`: unmoved caller locals
remain initialized and readable in the caller's cleanup block after an unwinding
call. -/
theorem canary_D8_unwinding_call_unmoved_ok :
    d8ReadCaller 2 d8AfterUnwindState.machine = .ok 1 d8AfterUnwindState.machine :=
  rfl

/-- **Consumer-side tail-call terminator (`evalTailCallTerminatorMoving`),
universal.** Evaluates callee and arguments with `evalCalleeAndArgsMoving`,
dispatches through `initFnTailCallMoving`, and checks that `frameIndex` did not
grow. -/
theorem call_evalTailCallTerminatorMoving_eq
    {P S C E Other Extern FnABI ArgABI : Type}
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C) (budget : Nat)
    (src : Miri.MIR.SourceInfo) (func : Miri.MIR.Operand) (args : Array Miri.MIR.SpannedOperand)
    (fnSpan : Miri.MIR.SpanRef) :
    Call.evalTailCallTerminatorMoving h choice budget ⟨src, .TailCall func args fnSpan⟩ = (do
      let oldIndex ← h.frameIndex
      let (evaluated, temps) ← Call.evalCalleeAndArgsMoving h choice func args
      Call.initFnTailCallMoving h choice budget evaluated temps
      srcRequire ((← h.frameIndex) == oldIndex)
        "evaluating this tail call pushed a new stack frame") := by
  unfold Call.evalTailCallTerminatorMoving srcRequire
  unfold_named "_private.Miri.Interpreter.Call.0.Miri.Interpreter.Call.require"
  rfl

/-- Call hooks for `initFnTailCallMoving`, `evalTailCallTerminatorMoving`, and
`initDropInPlaceCall`: `popRaw` fails if caller cell `1` was not yet
deinitialized when `requireCaller1UninitOnPop = true`, proving that argument
materialization and caller deinitialization run BEFORE `popRaw` and `cleanup`;
`cleanupAction` controls the `ReturnAction` returned by `cleanup`. -/
def b3TailDropHooks (requireCaller1UninitOnPop : Bool)
    (rootOfStack : Bool := false) (cleanupAction : ReturnAction := .normal) :
    CallHooks Unit ToyD8State Unit Unit Unit Unit Unit Unit :=
  { d8CallHooks false false with
    frameIndex := pure 0
    popRaw := fun _ => do
      let s ← get
      if requireCaller1UninitOnPop && (s.callerCells[1]?).join.isSome then
        throw (.invalidProgram "popRaw ran before caller arg 1 was deinitialized")
      set { s with inCallee := false }
      let base := d8Frame s.block s.unwinding
      pure (if rootOfStack then { base with returnContinuation := .stop true } else base)
    cleanup := fun _ _ _ => pure cleanupAction
    resolveDropGlue := fun _ _ => pure ⟨.Item 10, #[]⟩
    mplaceToMutRef := fun _ m => pure ⟨.indirect m.mplace, m.layout⟩
    fakeUnitReturn := fun _ => pure (.memory ⟨toyMPlace 0, toyFnLayout⟩)
    findMirOrEvalFn := fun _ _ _ args _ _ _ => do
      let copyArgToCallee (arg : FnArg Unit) (calleeSlot : Nat) : CallM ToyD8State Unit := do
        let s ← get
        match arg.copyFnArg.op with
        | .indirect m =>
          match (s.callerCells[toyCell m]?).join with
          | some v => set { s with calleeCells := s.calleeCells.set calleeSlot (some v) }
          | none => throw (.undefinedBehavior "invalidUninitBytes")
        | .immediate _ =>
          set { s with calleeCells := s.calleeCells.set calleeSlot (some 99) }
      match args.size with
      | 1 =>
        let some arg0 := args[0]? | throw (.invalidProgram "missing arg 0")
        copyArgToCallee arg0 1
      | _ =>
        let some arg0 := args[0]? | throw (.invalidProgram "missing arg 0")
        let some arg1 := args[1]? | throw (.invalidProgram "missing arg 1")
        copyArgToCallee arg0 1
        copyArgToCallee arg1 2
      pure none }

private theorem b3TailDropHooks_frameIndex
    (rootOfStack : Bool := false) (cleanupAction : ReturnAction := .normal) :
    (b3TailDropHooks true rootOfStack cleanupAction).frameIndex = pure 0 := rfl

private theorem tailCallMoving_evalCalleeAndArgs
    (rootOfStack : Bool := false) (cleanupAction : ReturnAction := .normal) :
    Call.evalCalleeAndArgsMoving (b3TailDropHooks true rootOfStack cleanupAction) () toyFn
        #[⟨toySpan, .Move ⟨1, #[]⟩⟩, ⟨toySpan, .Copy ⟨2, #[]⟩⟩] d8InitState =
      .ok (⟨.Instance ⟨.Item 10, #[]⟩,
            #[.Copy ⟨.indirect (toyMPlace 4), toyU8⟩, .Copy ⟨.indirect (toyMPlace 6), toyU8⟩],
            (), some (), false⟩,
           #[⟨⟨4⟩, none⟩, ⟨⟨6⟩, none⟩])
        { d8InitState with
          callerCells := [none, none, some 3, none, some 2, none, some 3, none],
          temps := [4, 6] } := by
  with_unfolding_all rfl

private theorem tailCallMoving_case_normal :
    Call.evalTailCallTerminatorMoving (b3TailDropHooks true) () 1
        ⟨⟨⟨0⟩, 0⟩, .TailCall toyFn #[⟨toySpan, .Move ⟨1, #[]⟩⟩, ⟨toySpan, .Copy ⟨2, #[]⟩⟩] ⟨0⟩⟩
        d8InitState =
      .ok ()
        { callerCells := [none, none, some 3, none, some 2, none, some 3, none],
          calleeCells := [none, some 2, some 3, none],
          temps := [4, 6], freedTemps := [4, 6], inCallee := false, block := 0,
          unwinding := false, panicCalled := false } := by
  rw [call_evalTailCallTerminatorMoving_eq]
  simp only [b3TailDropHooks_frameIndex, bind, EStateM.bind, pure, EStateM.pure,
    tailCallMoving_evalCalleeAndArgs]
  with_unfolding_all rfl

private theorem tailCallMoving_case_inPlace :
    Call.initFnTailCallMoving (b3TailDropHooks true) () 1
        ⟨.Instance ⟨.Item 10, #[]⟩,
         #[.InPlace ⟨toyMPlace 1, toyU8⟩, .Copy ⟨.indirect (toyMPlace 6), toyU8⟩],
         (), some (), false⟩
        #[⟨⟨6⟩, none⟩]
        { d8InitState with
          callerCells := [none, some 2, some 3, none, none, none, some 3, none],
          temps := [6] } =
      .ok ()
        { callerCells := [none, none, some 3, none, none, none, some 3, none].set 6 (some 2),
          calleeCells := [none, some 2, some 2, none],
          temps := [6, 6], freedTemps := [6, 6], inCallee := false, block := 0,
          unwinding := false, panicCalled := false } := by
  with_unfolding_all rfl

private theorem tailCallMoving_case_rootStop :
    Call.evalTailCallTerminatorMoving (b3TailDropHooks true true) () 1
        ⟨⟨⟨0⟩, 0⟩, .TailCall toyFn #[⟨toySpan, .Move ⟨1, #[]⟩⟩, ⟨toySpan, .Copy ⟨2, #[]⟩⟩] ⟨0⟩⟩
        d8InitState =
      .error (.invalidProgram "cannot tailcall as root of stack")
        { callerCells := [none, none, some 3, none, some 2, none, some 3, none],
          calleeCells := [none, none, none, none],
          temps := [4, 6], freedTemps := [4, 6], inCallee := false, block := 0,
          unwinding := false, panicCalled := false } := by
  rw [call_evalTailCallTerminatorMoving_eq]
  simp only [b3TailDropHooks_frameIndex, bind, EStateM.bind, pure, EStateM.pure,
    tailCallMoving_evalCalleeAndArgs]
  with_unfolding_all rfl

private theorem tailCallMoving_case_cleanupErr :
    Call.evalTailCallTerminatorMoving (b3TailDropHooks true false .noJump) () 1
        ⟨⟨⟨0⟩, 0⟩, .TailCall toyFn #[⟨toySpan, .Move ⟨1, #[]⟩⟩, ⟨toySpan, .Copy ⟨2, #[]⟩⟩] ⟨0⟩⟩
        d8InitState =
      .error (.invalidProgram "tailcall cleanup must return Normal")
        { callerCells := [none, none, some 3, none, some 2, none, some 3, none],
          calleeCells := [none, some 2, some 3, none],
          temps := [4, 6], freedTemps := [4, 6], inCallee := false, block := 0,
          unwinding := false, panicCalled := false } := by
  rw [call_evalTailCallTerminatorMoving_eq]
  simp only [b3TailDropHooks_frameIndex, bind, EStateM.bind, pure, EStateM.pure,
    tailCallMoving_evalCalleeAndArgs]
  with_unfolding_all rfl

/-- **`evalTailCallTerminatorMoving` & `initFnTailCallMoving` (`ep1-B3`):
caller places are materialized/deinitialized BEFORE `popRaw`/`cleanup`, and
`allTemps` are deallocated on both normal dispatch AND error.**
1. Normal `tailcall f(move _1, copy _2)` via `evalTailCallTerminatorMoving`:
   `_1 = 2` and `_2 = 3` are snapshotted into temporaries `[4, 6]` and `_1` is
   deinitialized (`callerCells[1] = none`) BEFORE `popRaw` runs (checked by
   `requireCaller1UninitOnPop = true`), the tail-callee receives `[2, 3]`, and
   both temporaries `[4, 6]` are freed (`freedTemps = [4, 6]`).
2. Direct `initFnTailCallMoving` with an `.InPlace` argument at cell `1`:
   materializes cell `1` into temporary `4` and deinitializes `callerCells[1]`
   before `popRaw` runs, copies `[2, 3]` into the tail-callee, and frees `[4, 6]`.
3. Error during `initFnTailCallMoving` (root-of-stack `.stop` continuation or
   non-`.normal` `cleanup` return): the `catch` handler still frees all temporary
   allocations (`freedTemps = [4, 6]`) before propagating the error. -/
theorem canary_tailCallMoving_deinit_before_pop_and_temp_cleanup :
    Call.evalTailCallTerminatorMoving (b3TailDropHooks true) () 1
        ⟨⟨⟨0⟩, 0⟩, .TailCall toyFn #[⟨toySpan, .Move ⟨1, #[]⟩⟩, ⟨toySpan, .Copy ⟨2, #[]⟩⟩] ⟨0⟩⟩
        d8InitState =
      .ok ()
        { callerCells := [none, none, some 3, none, some 2, none, some 3, none],
          calleeCells := [none, some 2, some 3, none],
          temps := [4, 6], freedTemps := [4, 6], inCallee := false, block := 0,
          unwinding := false, panicCalled := false } ∧
    Call.initFnTailCallMoving (b3TailDropHooks true) () 1
        ⟨.Instance ⟨.Item 10, #[]⟩,
         #[.InPlace ⟨toyMPlace 1, toyU8⟩, .Copy ⟨.indirect (toyMPlace 6), toyU8⟩],
         (), some (), false⟩
        #[⟨⟨6⟩, none⟩]
        { d8InitState with
          callerCells := [none, some 2, some 3, none, none, none, some 3, none],
          temps := [6] } =
      .ok ()
        { callerCells := [none, none, some 3, none, none, none, some 3, none].set 6 (some 2),
          calleeCells := [none, some 2, some 2, none],
          temps := [6, 6], freedTemps := [6, 6], inCallee := false, block := 0,
          unwinding := false, panicCalled := false } ∧
    Call.evalTailCallTerminatorMoving (b3TailDropHooks true true) () 1
        ⟨⟨⟨0⟩, 0⟩, .TailCall toyFn #[⟨toySpan, .Move ⟨1, #[]⟩⟩, ⟨toySpan, .Copy ⟨2, #[]⟩⟩] ⟨0⟩⟩
        d8InitState =
      .error (.invalidProgram "cannot tailcall as root of stack")
        { callerCells := [none, none, some 3, none, some 2, none, some 3, none],
          calleeCells := [none, none, none, none],
          temps := [4, 6], freedTemps := [4, 6], inCallee := false, block := 0,
          unwinding := false, panicCalled := false } ∧
    Call.evalTailCallTerminatorMoving (b3TailDropHooks true false .noJump) () 1
        ⟨⟨⟨0⟩, 0⟩, .TailCall toyFn #[⟨toySpan, .Move ⟨1, #[]⟩⟩, ⟨toySpan, .Copy ⟨2, #[]⟩⟩] ⟨0⟩⟩
        d8InitState =
      .error (.invalidProgram "tailcall cleanup must return Normal")
        { callerCells := [none, none, some 3, none, some 2, none, some 3, none],
          calleeCells := [none, some 2, some 3, none],
          temps := [4, 6], freedTemps := [4, 6], inCallee := false, block := 0,
          unwinding := false, panicCalled := false } :=
  ⟨tailCallMoving_case_normal, tailCallMoving_case_inPlace,
   tailCallMoving_case_rootStop, tailCallMoving_case_cleanupErr⟩

/-- **`Call.initDropInPlaceCall` on a static (non-`dyn`) type, universal.**
Forces allocation of the dropped place, resolves drop glue, builds `&mut T` via
`mplaceToMutRef`, and invokes `initFnCall` with `#[.Copy arg]` (never `.InPlace`
and never arming `pendingMoveDeinit`). -/
theorem call_initDropInPlaceCall_static_eq
    {P S C E Other Extern FnABI ArgABI : Type}
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C) (budget : Nat)
    (place : RuntimeStackPlace P) (originalInstance : CallInstance)
    (target : Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction)
    (hdbg : h.debugAssertions = false)
    (hstatic : ∀ ty, h.isDynamic ty = pure false) :
    Call.initDropInPlaceCall h choice budget place originalInstance target unwind = (do
      let place ← h.forceAllocation choice place
      let fnInstance ← h.resolveDropGlue choice place.layout.ty
      let abi ← h.fnAbiOfInstance choice fnInstance #[]
      let arg ← h.mplaceToMutRef choice place
      let ret ← h.fakeUnitReturn choice
      Call.initFnCall h choice budget ⟨.Instance fnInstance, h.rustAbi, some abi, #[.Copy arg],
        false, ret, some target, unwind⟩) := by
  simp only [Call.initDropInPlaceCall, hdbg, hstatic, bind, pure, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- **`Call.initDropInPlaceCall` (`ep1-B3`): dropping an initialized place keeps
its bytes initialized for the drop glue, whereas dropping a moved-out place
faults when the drop glue reads it.** -/
theorem canary_dropInPlace_preserves_initialized_and_detects_moved :
    Call.initDropInPlaceCall (b3TailDropHooks false) () 1
        (.memory ⟨toyMPlace 1, toyU8⟩) ⟨.Item 10, #[]⟩ 0 (.Cleanup 1) d8InitState =
      .ok ()
        { d8InitState with calleeCells := [none, some 2, none, none] } ∧
    Call.initDropInPlaceCall (b3TailDropHooks false) () 1
        (.memory ⟨toyMPlace 1, toyU8⟩) ⟨.Item 10, #[]⟩ 0 (.Cleanup 1)
        { d8InitState with callerCells := d8InitState.callerCells.set 1 none } =
      .error (.undefinedBehavior "invalidUninitBytes")
        { d8InitState with callerCells := d8InitState.callerCells.set 1 none } :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl⟩

end CallUnpackVirtualAndUnwindD8

/-! ### `SwitchInt` move deinitialization through the real `ControlFlow.evalTerminator` -/

section SwitchIntToy

open Miri.ABI Miri.Memory Miri.Interpreter

/-- Control hooks of the `SwitchInt` toy: a `SwitchInt` only jumps
(`ControlFlow.goToBlock`), so every frame transition fails. -/
def swControlHooks : ControlHooks Unit LocalLayout Unit ToyRvState Unit Unit where
  bodySpan := fun _ => .ok ⟨0⟩
  returnOperand := fun _ state => (state, .error (.unsupported "sw"))
  popFrame := fun _ state => (state, .error (.unsupported "sw"))
  copyReturn := fun _ _ _ state => (state, .error (.unsupported "sw"))
  cleanupFrame := fun _ _ _ state => (state, .error (.unsupported "sw"))
  unwindTerminate := fun _ _ state => (state, .error (.unsupported "sw"))

/-- `ControlFlow.TerminatorHooks` whose `SwitchInt` discriminant read composes the
`D4` toy's consumer-side operand evaluation and typed read (`toyRvEval`, then
`toyRvRead`: a moved memory place is queued and deinitialized by its own read, a
moved immediate local is deinitialized at evaluation), exactly as
`ExecutionMachine.stepHooks` composes `OperandMachine.evalOperandAt` and
`PlaceMachine.readImmediate` (`stepSwitchDiscriminantRead`); a case matches when it
equals the value read. -/
def swTerminatorHooks :
    TerminatorHooks Unit LocalLayout Unit ToyRvState Unit Unit (RvalueImmTy Unit) where
  toControlHooks := swControlHooks
  evalDiscriminant := fun _ op state =>
    match (do let o ← toyRvEval op; toyRvRead o) state.machine with
    | .ok v m => ({ state with machine := m }, .ok v)
    | .error e m => ({ state with machine := m }, .error e)
  compareSwitchCase := fun _ _ bits state =>
    (state, .ok (state.machine.reads.getLast? == some bits))
  call := fun _ _ state => (state, .error (.unsupported "sw"))
  tailCall := fun _ _ state => (state, .error (.unsupported "sw"))
  drop := fun _ _ _ _ state => (state, .error (.unsupported "sw"))
  ignoreOptionalOverflowChecks := fun _ => false
  readAssertCondition := fun _ _ state => (state, .error (.unsupported "sw"))
  assertPanic := fun _ _ _ state => (state, .error (.unsupported "sw"))

/-- The single-frame step state of the `SwitchInt` toy at block `blk`. -/
def swState (blk : Nat) (m : ToyRvState) : StepState Unit LocalLayout Unit ToyRvState :=
  { stack := ⟨#[d8Frame blk false]⟩, machine := m }

/-- `switchInt(op) -> [1: bb1, otherwise: bb0]`. -/
def swTerm (op : Miri.MIR.Operand) : Miri.MIR.Terminator :=
  ⟨⟨⟨0⟩, 0⟩, .SwitchInt op ⟨#[.Case 1 1], 0⟩⟩

/-- `_1 = v`, memory-backed (cell 1). -/
def swMem (v : Nat) : ToyRvState :=
  { slots := [.mem, .mem], cells := [none, some v], queue := [], reads := [], written := false }

/-- `_1 = 1`, an immediate local. -/
def swImm : ToyRvState :=
  { slots := [.mem, .imm (some 1)], cells := [none, none], queue := [], reads := [], written := false }

/-- **Concrete `SwitchInt` move deinitialization through the real
`ControlFlow.evalTerminator` (`ep1-A2`).** For
`switchInt(move _1) -> [1: bb1, otherwise: bb0]`:
1. memory-backed `_1 = 1`: the discriminant read consumes the move record,
   deinitializes `_1` and only then branches to `bb1`; with `_1 = 5` it branches
   to `bb0`, again with `_1` deinitialized;
2. an immediate local `_1 = 1` is deinitialized at evaluation and the branch to
   `bb1` is taken;
3. a later `switchInt(copy _1)` in the target block faults on the moved local,
   whereas `switchInt(copy _1)` leaves `_1` initialized. -/
theorem canary_switchInt_move_deinit :
    ControlFlow.evalTerminator swTerminatorHooks () (swTerm (.Move ⟨1, #[]⟩)) (swState 0 (swMem 1)) =
      (swState 1 { swMem 1 with cells := [none, none], reads := [1] }, .ok ()) ∧
    ControlFlow.evalTerminator swTerminatorHooks () (swTerm (.Move ⟨1, #[]⟩)) (swState 0 (swMem 5)) =
      (swState 0 { swMem 5 with cells := [none, none], reads := [5] }, .ok ()) ∧
    ControlFlow.evalTerminator swTerminatorHooks () (swTerm (.Move ⟨1, #[]⟩)) (swState 0 swImm) =
      (swState 1 { swImm with slots := [.mem, .imm none], reads := [1] }, .ok ()) ∧
    ControlFlow.evalTerminator swTerminatorHooks () (swTerm (.Copy ⟨1, #[]⟩))
        (swState 1 { swMem 1 with cells := [none, none], reads := [1] }) =
      (swState 1 { swMem 1 with cells := [none, none], reads := [1] },
        .error (.undefinedBehavior "invalidUninitBytes")) ∧
    ControlFlow.evalTerminator swTerminatorHooks () (swTerm (.Copy ⟨1, #[]⟩)) (swState 0 (swMem 1)) =
      (swState 1 { swMem 1 with reads := [1] }, .ok ()) :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl,
   by with_unfolding_all rfl, by with_unfolding_all rfl⟩

end SwitchIntToy

/-! ### `D7`: call destinations overlapping moved arguments -/

section CallDestA2

open Miri.ABI Miri.Memory Miri.Interpreter

/-- **Destination before arguments, universal.** The consumer-side call
terminator evaluates the destination place before it evaluates (and moves) the
callee and the arguments, exactly as the source `evalCallTerminator`. -/
theorem call_evalCallTerminatorMoving_dest_before_args
    {P S C E Other Extern FnABI ArgABI : Type}
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C) (budget : Nat)
    (src : Miri.MIR.SourceInfo) (func : Miri.MIR.Operand) (args : Array Miri.MIR.SpannedOperand)
    (dest : Miri.MIR.Place) (target : Option Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction)
    (callSource : Miri.MIR.CallSource) (fnSpan : Miri.MIR.SpanRef) :
    Call.evalCallTerminatorMoving h choice budget
        ⟨src, .Call func args dest target unwind callSource fnSpan⟩ = (do
      let oldIndex ← h.frameIndex
      let oldLoc := (← h.getFrame).location
      let destPlace ← h.evalPlace choice dest false
      let (evaluated, temps) ← Call.evalCalleeAndArgsMoving h choice func args
      Call.initFnCall h choice budget ⟨evaluated.callee, evaluated.callerAbi, evaluated.fnAbi,
        evaluated.args, evaluated.withCallerLocation, destPlace, target,
        if evaluated.fnAbi.any h.abiCanUnwind then unwind else .Unreachable⟩
      Call.deallocateTempArgs h choice temps
      if target.isSome then
        if (← h.frameIndex) == oldIndex then
          if (← h.getFrame).location == oldLoc then
            throw (.invalidProgram "evaluating this call made no progress")) := rfl

/-- Toy call state for destination/argument overlap: caller memory cells (`none`
= uninitialized; a pointer local holds the cell it points to), the argument
values the callee received, the return place recorded at call entry, the
temporaries, and whether the callee frame is active. -/
structure ToyD7State where
  cells : List (Option Nat)
  calleeArgs : List Nat
  ret : Option (RuntimeStackPlace Unit)
  temps : List Nat
  freed : List Nat
  inCallee : Bool

/-- The cell read of the `D7` toy. -/
def d7Read (s : ToyD7State) (n : Nat) : Option Nat := (s.cells[n]?).join

/-- Call hooks of the `D7` toy: `evalPlace` of `*_l` loads the pointer held by
`_l` (faulting when `_l` is uninitialized); `findMirOrEvalFn` records the return
place and the argument values handed to the callee. -/
def d7CallHooks : CallHooks Unit ToyD7State Unit Unit Unit Unit Unit Unit where
  debugAssertions := false
  getFrame := pure (d8Frame 0 false)
  setFrame := fun _ => pure ()
  frameIndex := do pure (if (← get).inCallee then 1 else 0)
  evalOperand := fun _ op =>
    match op with
    | .Copy ⟨0, _⟩ => pure ⟨.immediate .uninit, toyFnLayout⟩
    | .Copy p | .Move p => pure ⟨.indirect (toyMPlace p.localId), toyU8⟩
    | _ => throw (.unsupported "d7")
  evalPlace := fun _ p _ => do
    let s ← get
    match (p.projection[0]? : Option Miri.MIR.ProjectionElem) with
    | some .Deref =>
      match d7Read s p.localId with
      | some target => pure (.memory ⟨toyMPlace target, toyU8⟩)
      | none => throw (.undefinedBehavior "invalidUninitBytes")
    | _ => pure (.memory ⟨toyMPlace p.localId, toyU8⟩)
  placeToOp := fun _ rp =>
    match rp with
    | .memory m => pure ⟨.indirect m.mplace, m.layout⟩
    | _ => throw (.unsupported "d7")
  forceAllocation := fun _ rp =>
    match rp with
    | .memory m => pure m
    | _ => throw (.unsupported "d7")
  functionSignature := fun _ _ => pure (1, ())
  functionKind := fun _ => pure (.FnDef 10 #[])
  readPointer := fun _ _ => throw (.unsupported "d7")
  getPtrFn := fun _ _ => throw (.unsupported "d7")
  resolve := fun _ defId _ => pure ⟨.Item defId, #[]⟩
  fnAbiOfFnPtr := fun _ _ _ => pure ()
  fnAbiOfInstance := fun _ _ _ => pure ()
  requiresCallerLocation := fun _ => pure false
  callerLocation := pure ⟨0⟩
  abiCanUnwind := fun _ => true
  abiVariadic := fun _ => false
  abiFixedCount := fun _ => 0
  abiArgs := fun _ => #[()]
  abiReturn := fun _ => ()
  sameConvention := fun _ _ => true
  isRustCall := fun _ => false
  rustAbi := ()
  argLayout := fun _ => toyU8
  argIsIgnore := fun _ => false
  isOneZst := fun _ => false
  checkArgumentCompat := fun _ _ _ => pure true
  checkTargetFeatures := fun _ _ => pure ()
  tupleFields := fun _ => pure #[]
  projectFnArg := fun _ _ _ => throw (.unsupported "d7")
  localLayout := fun _ _ => pure toyU8
  localSpan := fun _ _ => pure ⟨0⟩
  storageLiveDyn := fun _ _ _ => pure ()
  copyAllowTransmute := fun _ _ _ => throw (.unsupported "d7")
  protectArgument := fun _ _ => throw (.invalidProgram "protectArgument must not run on FnArg.Copy")
  withRetagMode := fun _ _ action => action
  nonCapturingClosure := fun _ _ _ => pure false
  allocateStack := fun _ layout => do
    let s ← get
    let cell := 6 + s.temps.length
    set { s with temps := s.temps ++ [cell] }
    pure ⟨toyMPlace cell, layout⟩
  copyToMemory := fun _ src dst => do
    let s ← get
    match src.op with
    | .indirect m =>
      match d7Read s (toyCell m) with
      | some v => set { s with cells := s.cells.set (toyCell dst.mplace) (some v) }
      | none => throw (.undefinedBehavior "invalidUninitBytes")
    | _ => throw (.unsupported "d7")
  vaListPtr := fun _ _ => throw (.unsupported "d7")
  writeZeroBytes := fun _ _ _ => throw (.unsupported "d7")
  vaListKeyField := fun _ _ => throw (.unsupported "d7")
  writePointerToMemory := fun _ _ _ => throw (.unsupported "d7")
  pushRaw := fun _ _ _ _ _ => throw (.unsupported "d7")
  pushDone := fun _ => throw (.unsupported "d7")
  popRaw := fun _ => throw (.unsupported "d7")
  cleanup := fun _ _ _ => throw (.unsupported "d7")
  afterFrameInit := fun _ => pure ()
  callExtra := fun _ _ _ _ _ _ _ => throw (.unsupported "d7")
  callIntrinsic := fun _ _ _ _ _ _ => throw (.unsupported "d7")
  callLlvmIntrinsic := fun _ _ _ _ _ => throw (.unsupported "d7")
  findMirOrEvalFn := fun _ _ _ args destination _ _ => do
    let s ← get
    let argVals := args.toList.filterMap fun arg =>
      match arg.copyFnArg.op with
      | .indirect m => d7Read s (toyCell m)
      | .immediate _ => none
    set { s with ret := some destination, calleeArgs := argVals, inCallee := true }
    pure none
  resolveVirtual := fun _ _ _ _ _ _ => throw (.unsupported "d7")
  isDynamic := fun _ => pure false
  unpackDynForDrop := fun _ _ => throw (.unsupported "d7")
  resolveDropGlue := fun _ _ => throw (.unsupported "d7")
  mplaceToMutRef := fun _ _ => throw (.unsupported "d7")
  fakeUnitReturn := fun _ => throw (.unsupported "d7")
  deinitMovedPlace := true
  deinitInPlaceArgument := fun _ m => modify fun s =>
    { s with cells := s.cells.set (toyCell m.mplace) none }
  validateOperandBeforeCall := fun _ _ => pure ()
  deallocateStack := fun _ ptr => modify fun s =>
    { s with freed := s.freed ++ [ptr.offset.bytes.toNat] }

/-- `call callee(move _2) -> [return: bb1, unwind: bb1]` writing `dest`. -/
def d7Call (dest : Miri.MIR.Place) (arg : Nat) : Miri.MIR.Terminator :=
  ⟨⟨⟨0⟩, 0⟩, .Call toyFn #[⟨toySpan, .Move ⟨arg, #[]⟩⟩] dest (some 1) (.Cleanup 1) .Normal ⟨0⟩⟩

/-- `_2 = &raw mut _5` (cell 2 holds `5`), `_5 = 42`. -/
def d7DerefInit : ToyD7State :=
  { cells := [none, none, some 5, none, none, some 42, none, none],
    calleeArgs := [], ret := none, temps := [], freed := [], inCallee := false }

/-- After `*_2 = callee(move _2)` entered the callee. -/
def d7DerefAfter : ToyD7State :=
  { cells := [none, none, none, none, none, some 42, some 5, none],
    calleeArgs := [5], ret := some (.memory ⟨toyMPlace 5, toyU8⟩), temps := [6], freed := [6],
    inCallee := true }

/-- **`*_2 = callee(move _2)`: the destination is resolved before the moved
argument is deinitialized (`canary_D7_call_dest_resolved_before_arg_move`).** The
real `Call.evalCallTerminatorMoving` resolves `*_2` through the pointer held by
`_2` (return place: cell `5`) first, then snapshots `move _2` for the callee
(which receives the pointer `5`) and deinitializes `_2`. Resolving the
destination after the move would load the deinitialized pointer and fault. -/
theorem canary_D7_call_dest_resolved_before_arg_move :
    Call.evalCallTerminatorMoving d7CallHooks () 1 (d7Call ⟨2, #[.Deref]⟩ 2) d7DerefInit =
      .ok () d7DerefAfter ∧
    d7DerefAfter.ret = some (.memory ⟨toyMPlace 5, toyU8⟩) ∧
    d7Read d7DerefAfter 2 = none ∧
    d7CallHooks.evalPlace () ⟨2, #[.Deref]⟩ false d7DerefAfter =
      .error (.undefinedBehavior "invalidUninitBytes") d7DerefAfter :=
  ⟨by with_unfolding_all rfl, rfl, rfl, by with_unfolding_all rfl⟩

/-- Control hooks of the `D7` toy: `popFrame` pops the callee frame and
`copyReturn` stores the returned value `77` into the popped frame's return
place. -/
def d7ControlHooks : ControlHooks Unit LocalLayout Unit ToyD7State Unit Unit where
  bodySpan := fun _ => .ok ⟨0⟩
  returnOperand := fun _ state => (state, .ok ())
  popFrame := fun _ state =>
    match state.stack.currentFrame? with
    | some frame =>
      ({ stack := ⟨state.stack.frames.pop⟩, machine := { state.machine with inCallee := false } },
        .ok frame)
    | none => (state, .error (.stack .emptyStack))
  copyReturn := fun _ _ rp state =>
    match rp with
    | .memory m =>
      ({ state with machine :=
          { state.machine with cells := state.machine.cells.set (toyCell m.mplace) (some 77) } },
        .ok ())
    | _ => (state, .error (.unsupported "d7"))
  cleanupFrame := fun _ _ _ state => (state, .ok .normal)
  unwindTerminate := fun _ _ state => (state, .error (.unsupported "d7"))

/-- `ControlFlow.TerminatorHooks` of the `D7` toy (only `Return` is used). -/
def d7TerminatorHooks : TerminatorHooks Unit LocalLayout Unit ToyD7State Unit Unit Bool where
  toControlHooks := d7ControlHooks
  evalDiscriminant := fun _ _ state => (state, .error (.unsupported "d7"))
  compareSwitchCase := fun _ _ _ state => (state, .error (.unsupported "d7"))
  call := fun _ _ state => (state, .error (.unsupported "d7"))
  tailCall := fun _ _ state => (state, .error (.unsupported "d7"))
  drop := fun _ _ _ _ state => (state, .error (.unsupported "d7"))
  ignoreOptionalOverflowChecks := fun _ => false
  readAssertCondition := fun _ _ state => (state, .error (.unsupported "d7"))
  assertPanic := fun _ _ _ state => (state, .error (.unsupported "d7"))

/-- The callee frame pushed for return place `rp`, returning to `bb1`. -/
def d7CalleeFrame (rp : RuntimeStackPlace Unit) : Frame Unit LocalLayout Unit :=
  { d8Frame 0 false with returnPlace := rp, returnContinuation := .goto (some 1) (.Cleanup 1) }

/-- `_1 = 7`. -/
def d7RootInit : ToyD7State :=
  { cells := [none, some 7, none, none, none, none, none, none],
    calleeArgs := [], ret := none, temps := [], freed := [], inCallee := false }

/-- After `_1 = callee(move _1)` entered the callee. -/
def d7RootAfter : ToyD7State :=
  { cells := [none, none, none, none, none, none, some 7, none],
    calleeArgs := [7], ret := some (.memory ⟨toyMPlace 1, toyU8⟩), temps := [6], freed := [6],
    inCallee := true }

/-- **`_1 = callee(move _1)`: the moved argument is deinitialized at call entry
and the return value lands in `_1` (`canary_D7_call_dest_overlaps_moved_arg`).**
The real `Call.evalCallTerminatorMoving` resolves the destination `_1`, snapshots
`move _1` (the callee receives `7`) and deinitializes `_1` before the callee
runs, so `_1` is uninitialized during the call; on `Return` the real
`ControlFlow.evalTerminator` pops the callee frame, writes the returned value
into the recorded return place `_1` and resumes the caller at `bb1`. -/
theorem canary_D7_call_dest_overlaps_moved_arg :
    Call.evalCallTerminatorMoving d7CallHooks () 1 (d7Call ⟨1, #[]⟩ 1) d7RootInit =
      .ok () d7RootAfter ∧
    d7Read d7RootAfter 1 = none ∧
    ControlFlow.evalTerminator d7TerminatorHooks () ⟨⟨⟨0⟩, 0⟩, .Return⟩
        { stack := ⟨#[d8Frame 0 false,
            d7CalleeFrame (d7RootAfter.ret.getD (.memory ⟨toyMPlace 0, toyU8⟩))]⟩,
          machine := d7RootAfter } =
      ({ stack := ⟨#[d8Frame 1 false]⟩,
         machine := { d7RootAfter with
           cells := [none, some 77, none, none, none, none, some 7, none], inCallee := false } },
        .ok ()) :=
  ⟨by with_unfolding_all rfl, rfl, by with_unfolding_all rfl⟩

end CallDestA2

/-! ## Part 4: root-move simulation between `lean-miri` and Trusted `Places` -/

section RootMoveSimulation

open Miri.ABI Miri.Memory Miri.Interpreter

/-- A successful `replaceLocalValue` installs the new value at that local. -/
theorem frame_replaceLocalValue_get {Prov Layout Extra : Type}
    (frame frame' : Frame Prov Layout Extra) (l : Miri.MIR.LocalId) (v : LocalValue Prov)
    (h : frame.replaceLocalValue l v = .ok frame') :
    (frame'.locals[l]?).map (·.value) = some v := by
  unfold Frame.replaceLocalValue at h
  split at h
  · rename_i hlt
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [hlt]
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- Slot correspondence for an unprojected local: Trusted `.uninit` is a moved
immediate `.live (.immediate .uninit)`, and an initialized Trusted value is a live
immediate related by `rel`. -/
inductive RootSlotRel {Prov : Type} (rel : Trusted.Rustc.V2026_06_01.MirSemantics.Value →
    Immediate Prov → Prop) :
    Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot → LocalValue Prov → Prop where
  | uninit : RootSlotRel rel .uninit (.live (.immediate .uninit))
  | init {v imm} : rel v imm → RootSlotRel rel (.init v) (.live (.immediate imm))

/-- **Root-move simulation.** Run `Move _l` on a related pair of states: in
`lean-miri` through `LocalAccess.evalOperand` with `deinitMovedPlace = true` (the
local holds a non-zero-sized immediate), and in Trusted through
`evalOperand (deinitProjectedMoves := true)`. Both return related values, and the
moved local is related afterwards: Trusted `.uninit` ↔ `lean-miri`
`.live (.immediate .uninit)`. -/
theorem root_move_simulation {Prov Extra State : Type}
    (rel : Trusted.Rustc.V2026_06_01.MirSemantics.Value → Immediate Prov → Prop)
    (hooks : LocalAccessHooks Prov Extra State) (frame frame₁ frame₂ : Frame Prov LocalLayout Extra)
    (state state₁ : State) (l : Nat) (known : Option LocalLayout) (imm : Immediate Prov)
    (layout : LocalLayout)
    (locals : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot)
    (v : Trusted.Rustc.V2026_06_01.MirSemantics.Value)
    (borrows : List Trusted.Rustc.V2026_06_01.MirSemantics.BorrowEntry)
    (globals : List Trusted.Rustc.V2026_06_01.MirAst.CapturedAllocation)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (callerLocals : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot)
    (localDecls : List Trusted.Rustc.V2026_06_01.MirAst.LocalDecl)
    (callStack : List Trusted.Rustc.V2026_06_01.MirSemantics.SavedCallerFrame)
    (hon : hooks.deinitMovedPlace = true)
    (hread : Miri.Interpreter.evalPlaceToOp hooks frame state ⟨l, #[]⟩ known =
      ⟨frame₁, state₁, .ok ⟨.immediate imm, layout⟩⟩)
    (hzst : layout.layout.isZst = false)
    (hrep : frame₁.replaceLocalValue l (.live (.immediate .uninit)) = .ok frame₂)
    (hget : Trusted.Sequence.get? locals l = .some (.init v))
    (hrel : rel v imm)
    (hmoved : Trusted.Rustc.V2026_06_01.MirSemantics.valueContainsMovedUninit v = false)
    (htzst : Trusted.Rustc.V2026_06_01.MirSemantics.moveValueIsZeroSized localDecls layouts
      (Trusted.Rustc.V2026_06_01.MirSemantics.placeTyResolved localDecls layouts
        { local_ := l, projection := .nil }) v = false) :
    Miri.Interpreter.evalOperand hooks frame state (.Move ⟨l, #[]⟩) known =
        ⟨frame₂, state₁, .ok ⟨.immediate imm, layout⟩⟩ ∧
      ∃ locals',
        Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand locals
            (.move { local_ := l, projection := .nil }) borrows globals layouts callerLocals
            localDecls callStack true = .ok v locals' ∧
        rel v imm ∧
        ∃ lv, (frame₂.locals[l]?).map (·.value) = some lv ∧
          ∃ slot, Trusted.Sequence.get? locals' l = some slot ∧ RootSlotRel rel slot lv := by
  refine ⟨?_, ?_⟩
  · simp only [Miri.Interpreter.evalOperand, hon, ↓reduceIte, Miri.Interpreter.evalOperandMoving,
      hread, hzst, Bool.false_eq_true, Array.isEmpty, hrep]
    rfl
  · obtain ⟨locals', hgetu, heval⟩ :=
      evalOperand_move_root_deinit locals l v borrows globals layouts callerLocals localDecls
        callStack hget hmoved htzst
    exact ⟨locals', heval, hrel, _, frame_replaceLocalValue_get frame₁ frame₂ l _ hrep, _, hgetu,
      .uninit⟩

/-- **Indirect / memory-backed & `Deref` move simulation (`D5` & projected memory
moves).** Run `Move` of an indirect (`MemPlace`) place in `lean-miri` through
`OperandMachine.evalOperand` followed by `PlaceMachine.readImmediate` with
`deinitMovedPlace = true`, and in Trusted through
`evalOperand (deinitProjectedMoves := true)` on `tPlace`:
1. `OperandMachine.evalOperand` evaluates `mPlace` to `⟨.indirect mplace, layout⟩`
   and queues `(mplace, true)` at the front of `pendingMoveDeinits`;
2. `PlaceMachine.readImmediate` consumes `(mplace, true)` (disarming the latch),
   runs the exact source read `srcReadImmediate` (whose Tree Borrows effect on
   every allocation's `BorrowTree` equals the `Copy` read), and then deinitializes
   `mplace` via `PlaceMachine.writeMemoryRawUninit` (`tbSilentAccessHooks`, zero
   Tree Borrows or race writes);
3. `Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand ... (.move tPlace) ... true`
   runs `evalCopyPlaceRead` followed by `evalMoveOperandDeinit`, returning the
   related value `v` (`rel v val.imm`, a hypothesis restated for convenience) and
   the deinitialized `locals'`. Trusted `evalOperand` takes the borrow table as an
   input only (its `PlaceReadResult` carries no borrow table), so a move can never
   update a `.frozen` entry; the last conjunct merely records that every `.frozen`
   entry is still looked up as `.frozen`. -/
theorem indirect_move_simulation {K User C : Type} [DecidableEq K]
    (rel : Trusted.Rustc.V2026_06_01.MirSemantics.Value → Immediate Provenance → Prop)
    (opHooks : OperandMachine.Hooks K User C) (config : PlaceMachine.AccessConfig K User)
    (c : C) (mPlace : Miri.MIR.Place) (known : Option LocalLayout)
    (s s₁ s₂ s₃ : MachineHooks.State K User)
    (mplace : MemPlace Provenance) (layout : LocalLayout) (val : RvalueImmTy Provenance)
    (locals locals₀ locals₁ : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot)
    (tPlace : Trusted.Rustc.V2026_06_01.MirAst.Place)
    (v : Trusted.Rustc.V2026_06_01.MirSemantics.Value)
    (borrows : List Trusted.Rustc.V2026_06_01.MirSemantics.BorrowEntry)
    (globals : List Trusted.Rustc.V2026_06_01.MirAst.CapturedAllocation)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (callerLocals : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot)
    (localDecls : List Trusted.Rustc.V2026_06_01.MirAst.LocalDecl)
    (callStack : List Trusted.Rustc.V2026_06_01.MirSemantics.SavedCallerFrame)
    (hopOn : opHooks.deinitMovedPlace = true)
    (hcfgOn : config.deinitMovedPlace = true)
    (hqueueEmpty : s₁.machine.pendingMoveDeinits = #[])
    (hevalPlace : OperandMachine.evalPlaceToOp opHooks c mPlace known
      { s with machine := MachineHooks.clearPendingMoveDeinitFlag s.machine } =
        .ok ⟨.indirect mplace, layout⟩ s₁)
    (hreadMiri : srcReadImmediate config ⟨.indirect mplace, layout⟩
      { s₁ with
        machine :=
          MachineHooks.MachineState.withPendingMoves
            (MachineHooks.MachineState.withPendingMoves s₁.machine true #[(mplace, true)])
            false
            ((#[(mplace, true)] : Array (MemPlace Provenance × Bool)).eraseIdxIfInBounds 0) } =
        .ok val s₂)
    (hdeinitMiri : PlaceMachine.writeMemoryRawUninit config ⟨mplace, layout⟩ s₂ = .ok () s₃)
    (hcopyT : Trusted.Rustc.V2026_06_01.MirSemantics.evalCopyPlaceRead locals tPlace borrows
      globals layouts callerLocals localDecls callStack = .ok v locals₀)
    (hdeinitT : Trusted.Rustc.V2026_06_01.MirSemantics.evalMoveOperandDeinit tPlace borrows
      globals layouts callerLocals localDecls callStack (.ok v locals₀) = .ok v locals₁)
    (hrel : rel v val.imm) :
    (do
      let op ← OperandMachine.evalOperand opHooks c (.Move mPlace) known
      PlaceMachine.readImmediate config op) s = .ok val s₃ ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand locals (.move tPlace) borrows globals
      layouts callerLocals localDecls callStack true = .ok v locals₁ ∧
    rel v val.imm ∧
    (∀ tag entry,
      Trusted.Rustc.V2026_06_01.MirSemantics.lookupBorrow borrows tag = .some entry →
      entry.perm = .frozen →
      Trusted.Rustc.V2026_06_01.MirSemantics.lookupBorrow borrows tag =
        .some { entry with perm := .frozen }) := by
  refine ⟨?_, ?_, hrel, fun _ entry hlookup hperm => by rw [hlookup]; cases entry; cases hperm; rfl⟩
  · have hop := operandMachine_evalOperand_move_indirect opHooks c mPlace known s s₁ mplace layout
      hopOn hevalPlace
    simp only [bind, EStateM.bind, hop]
    rw [placeMachine_readImmediate_moving config ⟨.indirect mplace, layout⟩ hcfgOn]
    simp only [MachineHooks.recordPendingMoveDeinit, hqueueEmpty, Array.push_empty]
    have htake := takePendingMoveDeinitFor_front s₁.machine mplace true true []
    simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, set,
      MonadStateOf.set, EStateM.set, htake, ↓reduceIte, hreadMiri, hdeinitMiri, pure,
      EStateM.pure]
  · rw [evalOperand_move_deinit, ← evalCopyPlaceRead_eq_copy, hcopyT, hdeinitT]

/-- **Call-argument `Deref` move simulation over arbitrary trailing projections
and borrow tables (`ep1-B3`).** Moving `(*_p).restProj` as a call argument in
`lean-miri` via `Call.evalFnCallArgumentMoving` (`deinitMovedPlace = true`) and
in Trusted via `evalOperand ... (.move { local_ := pLocal, projection := .deref ::
tRestProj }) borrows ... true` both deliver the pointee sub-value and
deinitialize the target through the borrow-tracker-silent deinitializer, while
every `.frozen` sibling borrow in `borrows` stays `.frozen` and `passArgument`
is independent of `protectArgument`. -/
theorem d7_call_arg_move_deref_projected_sibling_frozen_simulation
    {P S C E Other Extern FnABI ArgABI : Type}
    (rel : Trusted.Rustc.V2026_06_01.MirSemantics.Value → MemPlace P → Prop)
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C)
    (pLocal : Nat) (mRestProj : List Miri.MIR.ProjectionElem)
    (tRestProj : List Trusted.Rustc.V2026_06_01.MirAst.ProjectionElem)
    (locals locals' : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot)
    (borrows : List Trusted.Rustc.V2026_06_01.MirSemantics.BorrowEntry)
    (globals : List Trusted.Rustc.V2026_06_01.MirAst.CapturedAllocation)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (callerLocals : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot)
    (localDecls : List Trusted.Rustc.V2026_06_01.MirAst.LocalDecl)
    (callStack : List Trusted.Rustc.V2026_06_01.MirSemantics.SavedCallerFrame)
    (v : Trusted.Rustc.V2026_06_01.MirSemantics.Value)
    (path : OperandPath) (s s₁ s₂ s₃ s₄ s₅ : S) (rplace : RuntimeStackPlace P)
    (mplace : MemPlace P) (layout : LocalLayout) (tmp : MPlaceTy P)
    (hplace : h.evalPlace choice ⟨pLocal, ⟨.Deref :: mRestProj⟩⟩ true s = .ok rplace s₁)
    (hop : h.placeToOp choice rplace s₁ = .ok ⟨.indirect mplace, layout⟩ s₂)
    (hsized : layout.layout.isSized = true)
    (halloc : h.allocateStack choice layout s₂ = .ok tmp s₃)
    (hcopy : h.withRetagMode choice .None
      (h.copyToMemory choice ⟨.indirect mplace, layout⟩ tmp) s₃ = .ok () s₄)
    (hdeinit : h.deinitInPlaceArgument choice ⟨mplace, layout⟩ s₄ = .ok () s₅)
    (htrusted : Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand locals
      (.move { local_ := pLocal, projection := .deref :: tRestProj })
      borrows globals layouts callerLocals localDecls callStack true = .ok v locals')
    (hrel : rel v tmp.mplace) :
    Call.evalFnCallArgumentMoving h choice (.Move ⟨pLocal, ⟨.Deref :: mRestProj⟩⟩) path s =
      .ok (.Copy ⟨.indirect tmp.mplace, tmp.layout⟩, some tmp.mplace.ptr) s₅ ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand locals
      (.move { local_ := pLocal, projection := .deref :: tRestProj })
      borrows globals layouts callerLocals localDecls callStack true = .ok v locals' ∧
    rel v tmp.mplace ∧
    (∀ tag entry,
      Trusted.Rustc.V2026_06_01.MirSemantics.lookupBorrow borrows tag = .some entry →
      entry.perm = .frozen →
      Trusted.Rustc.V2026_06_01.MirSemantics.lookupBorrow borrows tag =
        .some { entry with perm := .frozen }) ∧
    (∀ (protect : C → MPlaceTy P → CallM S Unit) (callerAbi calleeAbi : ArgABI)
        (calleeIndex : Nat) (dest : Miri.MIR.Place) (calleeTy : Miri.MIR.TyId) (live : Bool),
      Call.passArgument { h with protectArgument := protect } choice
          (.Copy ⟨.indirect tmp.mplace, tmp.layout⟩) callerAbi calleeAbi calleeIndex dest calleeTy
          live =
        Call.passArgument h choice (.Copy ⟨.indirect tmp.mplace, tmp.layout⟩) callerAbi calleeAbi
          calleeIndex dest calleeTy live) :=
  ⟨call_evalFnCallArgumentMoving_move_indirect h choice ⟨pLocal, ⟨.Deref :: mRestProj⟩⟩
    path s s₁ s₂ s₃ s₄ s₅ rplace mplace layout tmp hplace hop hsized halloc hcopy hdeinit,
   htrusted, hrel,
   fun _ entry hlookup hperm => by rw [hlookup]; cases entry; cases hperm; rfl,
   fun protect callerAbi calleeAbi calleeIndex dest calleeTy live =>
     call_passArgument_copy_protect_irrelevant h protect choice _ callerAbi calleeAbi calleeIndex
       dest calleeTy live⟩

/-- **Call-argument `Deref` move simulation (`d7MoveDerefSiblingFrozen`,
Finding 11).** Specialization of
`d7_call_arg_move_deref_projected_sibling_frozen_simulation` to `(*_2)` on
`d5Locals`/`d5Borrows`. -/
theorem d7_call_arg_move_deref_sibling_frozen_simulation
    {P S C E Other Extern FnABI ArgABI : Type}
    (rel : Trusted.Rustc.V2026_06_01.MirSemantics.Value → MemPlace P → Prop)
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C)
    (path : OperandPath) (s s₁ s₂ s₃ s₄ s₅ : S) (rplace : RuntimeStackPlace P)
    (mplace : MemPlace P) (layout : LocalLayout) (tmp : MPlaceTy P)
    (hplace : h.evalPlace choice ⟨2, #[.Deref]⟩ true s = .ok rplace s₁)
    (hop : h.placeToOp choice rplace s₁ = .ok ⟨.indirect mplace, layout⟩ s₂)
    (hsized : layout.layout.isSized = true)
    (halloc : h.allocateStack choice layout s₂ = .ok tmp s₃)
    (hcopy : h.withRetagMode choice .None
      (h.copyToMemory choice ⟨.indirect mplace, layout⟩ tmp) s₃ = .ok () s₄)
    (hdeinit : h.deinitInPlaceArgument choice ⟨mplace, layout⟩ s₄ = .ok () s₅)
    (hrel : rel (sc8 5) tmp.mplace) :
    Call.evalFnCallArgumentMoving h choice (.Move ⟨2, #[.Deref]⟩) path s =
      .ok (.Copy ⟨.indirect tmp.mplace, tmp.layout⟩, some tmp.mplace.ptr) s₅ ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand d5Locals
      (.move (pl 2 [.deref])) d5Borrows (deinitProjectedMoves := true) =
      .ok (sc8 5) d5AfterMove ∧
    rel (sc8 5) tmp.mplace ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.lookupBorrow d5Borrows 3 =
      .some { tag := 3, targetLocal := 1, targetProjection := [], perm := .frozen } ∧
    (∀ (protect : C → MPlaceTy P → CallM S Unit) (callerAbi calleeAbi : ArgABI)
        (calleeIndex : Nat) (dest : Miri.MIR.Place) (calleeTy : Miri.MIR.TyId) (live : Bool),
      Call.passArgument { h with protectArgument := protect } choice
          (.Copy ⟨.indirect tmp.mplace, tmp.layout⟩) callerAbi calleeAbi calleeIndex dest calleeTy
          live =
        Call.passArgument h choice (.Copy ⟨.indirect tmp.mplace, tmp.layout⟩) callerAbi calleeAbi
          calleeIndex dest calleeTy live) :=
  ⟨call_evalFnCallArgumentMoving_move_indirect h choice ⟨2, #[.Deref]⟩ path s s₁ s₂ s₃ s₄ s₅
    rplace mplace layout tmp hplace hop hsized halloc hcopy hdeinit,
   canary_D5_deref_move_delivers_value, hrel, rfl,
   fun protect callerAbi calleeAbi calleeIndex dest calleeTy live =>
     call_passArgument_copy_protect_irrelevant h protect choice _ callerAbi calleeAbi calleeIndex
       dest calleeTy live⟩

/-- **Projected sub-place move simulation (`D2` / `D9`).** Moving a non-empty
projected sub-place `⟨l, proj⟩` in `lean-miri` via `LocalAccess.evalOperand`
(`deinitMovedPlace = true`, which materializes an immediate base local via
`forceLocalAllocation` and re-projects to `.indirect mplace`) and in Trusted via
`evalOperand (deinitProjectedMoves := true)` returns related sub-values,
overwrites the moved sub-place in Trusted with `movedMarkerValue` while keeping
sibling fields intact, and leaves the `lean-miri` operand at `.indirect mplace`
ready for `tbSilentAccessHooks` deinitialization. -/
theorem projected_subplace_move_simulation {Prov Extra State : Type}
    (rel : Trusted.Rustc.V2026_06_01.MirSemantics.Value → MemPlace Prov → Prop)
    (hooks : LocalAccessHooks Prov Extra State)
    (frame frame₁ frame₂ frame₃ : Frame Prov LocalLayout Extra)
    (state state₁ state₂ state₃ : State)
    (l : Nat) (projHead : Miri.MIR.ProjectionElem) (projTail : List Miri.MIR.ProjectionElem)
    (known : Option LocalLayout) (imm : Immediate Prov) (mplace wholeMplace : MemPlace Prov)
    (layout : LocalLayout)
    (locals : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot)
    (tHead : Trusted.Rustc.V2026_06_01.MirAst.ProjectionElem)
    (tTail : List Trusted.Rustc.V2026_06_01.MirAst.ProjectionElem)
    (rootVal rootVal' fieldVal : Trusted.Rustc.V2026_06_01.MirSemantics.Value)
    (borrows : List Trusted.Rustc.V2026_06_01.MirSemantics.BorrowEntry)
    (globals : List Trusted.Rustc.V2026_06_01.MirAst.CapturedAllocation)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (callerLocals : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot)
    (localDecls : List Trusted.Rustc.V2026_06_01.MirAst.LocalDecl)
    (callStack : List Trusted.Rustc.V2026_06_01.MirSemantics.SavedCallerFrame)
    (hon : hooks.deinitMovedPlace = true)
    (hzst : layout.layout.isZst = false)
    (hread₁ : Miri.Interpreter.evalPlaceToOp hooks frame state ⟨l, ⟨projHead :: projTail⟩⟩ known =
      ⟨frame₁, state₁, .ok ⟨.immediate imm, layout⟩⟩)
    (hforce : hooks.forceLocalAllocation frame₁ state₁ l = ⟨frame₂, state₂, .ok ()⟩)
    (hgetInd : frame₂.getLocalOperand l = .ok (.indirect wholeMplace))
    (hread₂ : Miri.Interpreter.evalPlaceToOp hooks frame₂ state₂ ⟨l, ⟨projHead :: projTail⟩⟩ known =
      ⟨frame₃, state₃, .ok ⟨.indirect mplace, layout⟩⟩)
    (hgetT : Trusted.Sequence.get? locals l = .some (.init rootVal))
    (hnoDeref : Trusted.Rustc.V2026_06_01.MirSemantics.projHasDeref (tHead :: tTail) = false)
    (hnoUnion : Trusted.Rustc.V2026_06_01.MirSemantics.placeTouchesUnion localDecls layouts
      { local_ := l, projection := tHead :: tTail } = false)
    (hprojRead : Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue locals rootVal
      (tHead :: tTail) = .ok fieldVal)
    (hmoved : Trusted.Rustc.V2026_06_01.MirSemantics.valueContainsMovedUninit fieldVal = false)
    (htzst : Trusted.Rustc.V2026_06_01.MirSemantics.moveValueIsZeroSized localDecls layouts
      (Trusted.Rustc.V2026_06_01.MirSemantics.placeTyResolved localDecls layouts
        { local_ := l, projection := tHead :: tTail }) fieldVal = false)
    (hprojWrite : Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue locals rootVal
      (tHead :: tTail)
      (Trusted.Rustc.V2026_06_01.MirSemantics.movedMarkerValue (tHead :: tTail) fieldVal) =
        .ok rootVal')
    (hrel : rel fieldVal mplace) :
    Miri.Interpreter.evalOperand hooks frame state (.Move ⟨l, ⟨projHead :: projTail⟩⟩) known =
      ⟨frame₃, state₃, .ok ⟨.indirect mplace, layout⟩⟩ ∧
    ∃ locals',
      Trusted.Sequence.get? locals' l = .some (.init rootVal') ∧
      Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand locals
        (.move { local_ := l, projection := tHead :: tTail }) borrows globals layouts
        callerLocals localDecls callStack true = .ok fieldVal locals' ∧
      rel fieldVal mplace := by
  refine ⟨?_, ?_⟩
  · have hne : (⟨projHead :: projTail⟩ : Array Miri.MIR.ProjectionElem).isEmpty = false := rfl
    simp only [Miri.Interpreter.evalOperand, hon, ↓reduceIte, Miri.Interpreter.evalOperandMoving,
      hread₁, hne, hzst, Bool.false_eq_true, hforce, hgetInd, hread₂]
  · obtain ⟨locals', hset, hget'⟩ := get?_set?_isSome locals l (.init rootVal) (.init rootVal') hgetT
    refine ⟨locals', hget', ?_, hrel⟩
    rw [evalOperand_move_deinit]
    cases hhead : tHead
    · simp only [hhead, Trusted.Rustc.V2026_06_01.MirSemantics.projHasDeref] at hnoDeref
      contradiction
    all_goals
      simp only [hhead] at hnoDeref hnoUnion hprojRead htzst hprojWrite ⊢
      simp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand, hgetT, hnoUnion, hprojRead,
        Trusted.Rustc.V2026_06_01.MirSemantics.evalMoveOperandDeinit, hmoved, htzst,
        Trusted.Rustc.V2026_06_01.MirSemantics.deinitMovedSubPlace, hnoDeref, hprojWrite, hset]

/-- Minimal `LocalAccessHooks` for concrete Part 4 simulation non-vacuity
witnesses: local `1` starts as an immediate `u8`, and `forceLocalAllocation`
materializes local `1` to `toyMPlace 10` (with `.Field idx _` projecting to
`toyMPlace (10 + idx)`). -/
def b3SimLocalHooks : LocalAccessHooks Unit Unit Unit where
  layout := fun frame state _ _ => ⟨frame, state, .ok toyU8⟩
  validationInProgress := fun _ => false
  afterLocalRead := fun frame state _ => ⟨frame, state, .ok ()⟩
  project := fun frame state op elem =>
    match op.op, elem with
    | .immediate imm, .Field _ _ => ⟨frame, state, .ok ⟨.immediate imm, toyU8⟩⟩
    | .indirect m, .Field idx _ =>
      ⟨frame, state, .ok ⟨.indirect (toyMPlace (toyCell m + idx)), toyU8⟩⟩
    | _, _ => ⟨frame, state, .ok op⟩
  checkPlaceType := fun frame state _ _ => ⟨frame, state, .ok ()⟩
  runtimeChecks := fun frame state _ =>
    ⟨frame, state, .ok ⟨.immediate (.scalar (Scalar.fromBool true)), toyU8⟩⟩
  constant := fun frame state _ _ => ⟨frame, state, .ok ⟨.immediate .uninit, toyU8⟩⟩
  deinitMovedPlace := true
  forceLocalAllocation := fun frame state localId =>
    match frame.replaceLocalValue localId (.live (.indirect (toyMPlace 10))) with
    | .ok frame' => ⟨frame', state, .ok ()⟩
    | .error e => ⟨frame, state, .error (.stack e)⟩

/-- Initial 2-local `Frame` for Part 4 non-vacuity witnesses: `_0` uninitialized,
`_1` live immediate scalar `true`. -/
def b3SimFrameInit : Frame Unit LocalLayout Unit :=
  { d8Frame 0 false with
    locals := #[⟨.live (.immediate .uninit), some toyU8⟩,
                ⟨.live (.immediate (.scalar (Scalar.fromBool true))), some toyU8⟩] }

/-- Expected frame after `Move _1` deinitializes root local `_1`. -/
def b3SimFrameAfterRootMove : Frame Unit LocalLayout Unit :=
  { d8Frame 0 false with
    locals := #[⟨.live (.immediate .uninit), some toyU8⟩,
                ⟨.live (.immediate .uninit), some toyU8⟩] }

/-- Expected frame after `Move _1.0` materializes `_1` to `toyMPlace 10`. -/
def b3SimFrameAfterForce : Frame Unit LocalLayout Unit :=
  { d8Frame 0 false with
    locals := #[⟨.live (.immediate .uninit), some toyU8⟩,
                ⟨.live (.indirect (toyMPlace 10)), some toyU8⟩] }

/-- **Non-vacuity witness for `root_move_simulation` (`ep1-B3`)** with non-empty
`d5Borrows`. -/
theorem witness_root_move_simulation :
    Miri.Interpreter.evalOperand b3SimLocalHooks b3SimFrameInit () (.Move ⟨1, #[]⟩) none =
      ⟨b3SimFrameAfterRootMove, (),
       .ok ⟨.immediate (.scalar (Scalar.fromBool true)), toyU8⟩⟩ ∧
    ∃ locals',
      Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand d1Locals
          (.move { local_ := 1, projection := .nil }) d5Borrows []
          Trusted.Rustc.V2026_06_01.MirSemantics.emptyLayoutTable [] [] [] true =
        .ok (sc8 5) locals' ∧
      True ∧
      ∃ lv, (b3SimFrameAfterRootMove.locals[1]?).map (·.value) = some lv ∧
        ∃ slot, Trusted.Sequence.get? locals' 1 = some slot ∧
          RootSlotRel (fun _ _ => True) slot lv :=
  root_move_simulation (fun _ _ => True) b3SimLocalHooks
    b3SimFrameInit b3SimFrameInit b3SimFrameAfterRootMove () () 1 none
    (.scalar (Scalar.fromBool true)) toyU8 d1Locals (sc8 5) d5Borrows []
    Trusted.Rustc.V2026_06_01.MirSemantics.emptyLayoutTable [] [] [] rfl rfl rfl rfl rfl trivial rfl rfl

/-- **Non-vacuity witness for `projected_subplace_move_simulation` (`ep1-B3`)**
over a non-empty projection `_1.0` and non-empty borrow table `d5Borrows`. -/
theorem witness_projected_subplace_move_simulation :
    Miri.Interpreter.evalOperand b3SimLocalHooks b3SimFrameInit ()
        (.Move ⟨1, #[.Field 0 0]⟩) none =
      ⟨b3SimFrameAfterForce, (), .ok ⟨.indirect (toyMPlace 10), toyU8⟩⟩ ∧
    ∃ locals',
      Trusted.Sequence.get? locals' 1 =
        .some (.init (.aggregate 0 [Trusted.Rustc.V2026_06_01.MirSemantics.movedUninitValue, sc8 3])) ∧
      Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand d2Locals
        (.move { local_ := 1, projection := [.field 0 u8Ty] }) d5Borrows []
        Trusted.Rustc.V2026_06_01.MirSemantics.emptyLayoutTable [] [] [] true =
        .ok (sc8 2) locals' ∧
      True :=
  projected_subplace_move_simulation (fun _ _ => True) b3SimLocalHooks
    b3SimFrameInit b3SimFrameInit b3SimFrameAfterForce b3SimFrameAfterForce
    () () () () 1 (.Field 0 0) [] none (.scalar (Scalar.fromBool true))
    (toyMPlace 10) (toyMPlace 10) toyU8 d2Locals (.field 0 u8Ty) []
    (.aggregate 0 [sc8 2, sc8 3])
    (.aggregate 0 [Trusted.Rustc.V2026_06_01.MirSemantics.movedUninitValue, sc8 3])
    (sc8 2) d5Borrows [] Trusted.Rustc.V2026_06_01.MirSemantics.emptyLayoutTable [] [] []
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl trivial

/-- Initial state for `(*_2).0` call-argument move: cell `2` holds `3` (`_1[1].0`),
temporaries start at cell `4`. -/
def b3D7Init : ToyCallState :=
  { mem := [none, none, some 3, none, none, none, none], resolved := false, nextTmp := 4 }

/-- Post-state after `Call.evalFnCallArgumentMoving` moves `(*_2).0` into
temporary cell `4` and deinitializes cell `2`. -/
def b3D7After : ToyCallState :=
  { mem := [none, none, none, none, some 3, none, none], resolved := false, nextTmp := 5 }

/-- **Non-vacuity witness for
`d7_call_arg_move_deref_projected_sibling_frozen_simulation` (`ep1-B3`)** over a
non-empty trailing projection `(*_2).0` (`[.deref, .field 0 u8Ty]`) on
`a2PairArrLocals` with active + frozen `d5Borrows`. -/
theorem witness_d7_call_arg_move_deref_projected_sibling_frozen_simulation :
    Call.evalFnCallArgumentMoving (toyCallHooks true) ()
        (.Move ⟨2, #[.Deref, .Field 0 0]⟩) #[] b3D7Init =
      .ok (.Copy ⟨.indirect (toyMPlace 4), toyU8⟩, some ⟨⟨4⟩, none⟩) b3D7After ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand a2PairArrLocals
      (.move { local_ := 2, projection := [.deref, .field 0 u8Ty] })
      d5Borrows [] a2PairArrLayouts [] a2PairArrDecls [] true =
      .ok (sc8 3) a2PairArrAfterMove ∧
    True ∧
    (∀ tag entry,
      Trusted.Rustc.V2026_06_01.MirSemantics.lookupBorrow d5Borrows tag = .some entry →
      entry.perm = .frozen →
      Trusted.Rustc.V2026_06_01.MirSemantics.lookupBorrow d5Borrows tag =
        .some { entry with perm := .frozen }) ∧
    (∀ (protect : Unit → MPlaceTy Unit → CallM ToyCallState Unit) (callerAbi calleeAbi : Unit)
        (calleeIndex : Nat) (dest : Miri.MIR.Place) (calleeTy : Miri.MIR.TyId) (live : Bool),
      Call.passArgument { toyCallHooks true with protectArgument := protect } ()
          (.Copy ⟨.indirect (toyMPlace 4), toyU8⟩) callerAbi calleeAbi calleeIndex dest calleeTy
          live =
        Call.passArgument (toyCallHooks true) () (.Copy ⟨.indirect (toyMPlace 4), toyU8⟩)
          callerAbi calleeAbi calleeIndex dest calleeTy live) :=
  d7_call_arg_move_deref_projected_sibling_frozen_simulation (fun _ _ => True)
    (toyCallHooks true) () 2 [.Field 0 0] [.field 0 u8Ty]
    a2PairArrLocals a2PairArrAfterMove d5Borrows [] a2PairArrLayouts [] a2PairArrDecls []
    (sc8 3) #[] b3D7Init b3D7Init b3D7Init
    { mem := [none, none, some 3, none, none, none, none], resolved := false, nextTmp := 5 }
    { mem := [none, none, some 3, none, some 3, none, none], resolved := false, nextTmp := 5 }
    b3D7After (.memory ⟨toyMPlace 2, toyU8⟩) (toyMPlace 2) toyU8 ⟨toyMPlace 4, toyU8⟩
    rfl rfl rfl rfl rfl rfl rfl trivial

end RootMoveSimulation

end LeanMiriSpec.Correspondence.MoveDeinitEquiv

/-! ## Part 5: axiom audit

`Classical.choice` is a dependency of the vendored `lean-miri` machine
definitions themselves (for example `MachineHooks.State`, and hence
`OperandMachine.evalOperand`, `PlaceMachine.readImmediate` and
`ExecutionMachine.step`), so every statement about them inherits it through
`collectAxioms`. The audit therefore checks two things:

1. the full axiom closure of every declaration of this module contains no
   `sorryAx`, no `Lean.ofReduceBool` (`native_decide`) and no
   `Lean.trustCompiler`, and nothing beyond `propext`, `Quot.sound` and the
   inherited `Classical.choice`;
2. the *proof* closure — following theorem values (and this module's own
   definitions) but not the definitions of the vendored interpreter or of
   Trusted — uses only `propext` and `Quot.sound`: no proof here introduces
   classical reasoning. -/

namespace LeanMiriSpec.Correspondence.MoveDeinitEquivAudit

open Lean Elab Command in
/-- Run the two-part axiom audit described above over every declaration of
`LeanMiriSpec.Correspondence.MoveDeinitEquiv`. -/
elab "#assert_move_deinit_equiv_axioms" : command => do
  let env ← getEnv
  let ns := `LeanMiriSpec.Correspondence.MoveDeinitEquiv
  let names : Array Name := env.constants.map₂.foldl (init := #[]) fun acc n _ =>
    if ns.isPrefixOf n then acc.push n else acc
  if names.size < 100 then
    throwError "MoveDeinitEquiv axiom audit found only {names.size} declarations"
  let mut inherited : Nat := 0
  for n in names do
    let axs ← liftCoreM <| Lean.collectAxioms n
    for a in axs do
      if a == ``sorryAx || a == `Lean.ofReduceBool || a == `Lean.trustCompiler then
        throwError "{n} depends on the forbidden axiom {a}"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{n} depends on the unexpected axiom {a}"
    if axs.contains ``Classical.choice then inherited := inherited + 1
  let mut visited : NameSet := {}
  let mut todo : Array Name := names
  let mut proofAxioms : NameSet := {}
  while !todo.isEmpty do
    let k := todo.back!
    todo := todo.pop
    unless visited.contains k do
      visited := visited.insert k
      match env.find? k with
      | some (.axiomInfo _) => proofAxioms := proofAxioms.insert k
      | some (.thmInfo v) => todo := todo ++ v.value.getUsedConstants
      | some (.defnInfo v) =>
        if ns.isPrefixOf k then todo := todo ++ v.value.getUsedConstants
      | _ => pure ()
  for a in proofAxioms do
    unless a == ``propext || a == ``Quot.sound do
      throwError "a proof of this module depends on the axiom {a}"
  logInfo m!"MoveDeinitEquiv axiom audit: {names.size} declarations, no sorryAx / \
    Lean.ofReduceBool / Lean.trustCompiler; proofs use only propext and Quot.sound \
    ({visited.size} constants on the proof closure); {inherited} statements inherit \
    Classical.choice from the vendored lean-miri definitions"

#assert_move_deinit_equiv_axioms

end LeanMiriSpec.Correspondence.MoveDeinitEquivAudit
