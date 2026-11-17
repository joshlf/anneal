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
  universal decomposition and root-move theorems; `D1`/`D2`/`D3`/`D5`/`D9`
  canaries (root, zero-sized, field, re-initialization, Tree-Borrows-silent
  `Deref`, element and subslice moves), each with its legacy contrast.
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
  `OperandMachine.evalOperand`, step-boundary latch clearing, and concrete runs of
  the real `Call.evalCalleeAndArgsMoving` showing that a moved immediate argument is
  deinitialized, that `f(move _1, copy _1)` faults, and that
  `call unresolved(move _uninit)` faults before callee resolution (kani#5172).
* **Part 4.** A root-move simulation between `LocalAccess.evalOperand`
  (`deinitMovedPlace = true`) and `evalOperand (deinitProjectedMoves := true)`.
* **Part 5.** An environment audit: no declaration depends on `sorryAx`,
  `Lean.ofReduceBool` or `Lean.trustCompiler`, and the proofs use only `propext`
  and `Quot.sound` (`Classical.choice` reaches statements only through the
  vendored `lean-miri` machine definitions they mention).
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
      evalMoveOperandDeinit p borrows layouts localDecls callStack
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

end OperandLatch

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

/-! ### Call arguments: consumption, deinitialization and pre-resolution validation -/

section CallArgs

open Miri.ABI Miri.Memory Miri.Interpreter

variable {P S C E Other Extern FnABI ArgABI : Type}

/-- **Moved immediate call argument (`d7Imm`, Finding 11a), universal.** With
`deinitMovedPlace = true`, `move _l` of a non-zero-sized immediate local is
validated at its type, then the caller's local is replaced by
`.live (.immediate .uninit)` (`setFrame`), and the read value is passed by copy. -/
theorem call_evalFnCallArgumentMoving_move_immediate
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C) (l : Miri.MIR.LocalId)
    (path : OperandPath) (s s₁ s₂ s₃ s₄ s₅ : S) (rplace : RuntimeStackPlace P)
    (v : Immediate P) (layout : LocalLayout) (frame frame' : Frame P LocalLayout E)
    (hplace : h.evalPlace choice ⟨l, #[]⟩ true s = .ok rplace s₁)
    (hop : h.placeToOp choice rplace s₁ = .ok ⟨.immediate v, layout⟩ s₂)
    (hsized : layout.layout.isSized = true) (hzst : layout.layout.isZst = false)
    (hval : h.validateOperandBeforeCall choice ⟨.immediate v, layout⟩ s₂ = .ok () s₃)
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
true`, `move p` of a memory place is copied (validating) into a fresh temporary,
then the source is deinitialized with the silent `deinitInPlaceArgument`, and the
temporary is passed by copy: no argument is passed in place, so no protected
`uninit` write can occur. -/
theorem call_evalFnCallArgumentMoving_move_indirect
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C) (place : Miri.MIR.Place)
    (path : OperandPath) (s s₁ s₂ s₃ s₄ s₅ : S) (rplace : RuntimeStackPlace P)
    (mplace : MemPlace P) (layout : LocalLayout) (tmp : MPlaceTy P)
    (hplace : h.evalPlace choice place true s = .ok rplace s₁)
    (hop : h.placeToOp choice rplace s₁ = .ok ⟨.indirect mplace, layout⟩ s₂)
    (hsized : layout.layout.isSized = true)
    (halloc : h.allocateStack choice layout s₂ = .ok tmp s₃)
    (hcopy : h.copyToMemory choice ⟨.indirect mplace, layout⟩ tmp s₃ = .ok () s₄)
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
    (hval : h.validateOperandBeforeCall choice ⟨.immediate v, layout⟩ s₂ = .error err s₃) :
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
    (hval : h.validateOperandBeforeCall choice ⟨.immediate v, layout⟩ s₂ = .ok () s₃) :
    Call.evalFnCallArgumentMoving h choice (.Move place) path s =
      .ok (.Copy ⟨.immediate v, layout⟩, none) s₃ := by
  simp only [Call.evalFnCallArgumentMoving, bind, EStateM.bind, hplace, hop, hsized, hval,
    hzst, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure]

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
   runs `evalCopyPlaceRead` (leaving `borrows` and every `.frozen` tag unchanged)
   followed by `evalMoveOperandDeinit`, returning the related value `v` (`rel v
   val.imm`) and the deinitialized `locals'`. -/
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
      layouts localDecls callStack (.ok v locals₀) = .ok v locals₁)
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

/-- **Call-argument `Deref` move simulation (`d7MoveDerefSiblingFrozen`,
Finding 11).** Moving `(*_2)` as a call argument in `lean-miri` via
`Call.evalFnCallArgumentMoving` (`deinitMovedPlace = true`) and in Trusted via
`evalOperand d5Locals (.move (pl 2 [.deref])) d5Borrows (deinitProjectedMoves :=
true)` both deliver the pointee value, deinitialize `_1` through the
borrow-tracker-silent deinitializer (`deinitInPlaceArgument` /
`PlaceMachine.writeMemoryRawUninit`, never calling `protectArgument`), and
preserve the sibling `.frozen` borrow `_3` in `d5Borrows`. -/
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
    (hcopy : h.copyToMemory choice ⟨.indirect mplace, layout⟩ tmp s₃ = .ok () s₄)
    (hdeinit : h.deinitInPlaceArgument choice ⟨mplace, layout⟩ s₄ = .ok () s₅)
    (hrel : rel (sc8 5) tmp.mplace) :
    Call.evalFnCallArgumentMoving h choice (.Move ⟨2, #[.Deref]⟩) path s =
      .ok (.Copy ⟨.indirect tmp.mplace, tmp.layout⟩, some tmp.mplace.ptr) s₅ ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand d5Locals
      (.move (pl 2 [.deref])) d5Borrows (deinitProjectedMoves := true) =
      .ok (sc8 5) d5AfterMove ∧
    rel (sc8 5) tmp.mplace ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.lookupBorrow d5Borrows 3 =
      .some { tag := 3, targetLocal := 1, targetProjection := [], perm := .frozen } :=
  ⟨call_evalFnCallArgumentMoving_move_indirect h choice ⟨2, #[.Deref]⟩ path s s₁ s₂ s₃ s₄ s₅
    rplace mplace layout tmp hplace hop hsized halloc hcopy hdeinit,
   canary_D5_deref_move_delivers_value, hrel, rfl⟩

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
