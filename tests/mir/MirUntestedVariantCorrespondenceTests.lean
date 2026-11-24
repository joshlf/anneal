/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted
import Anneal.MirFuelFree
import Correspondence.V2026_06_01.L3_PlacesAndBasicMem
import Correspondence.V2026_06_01.L5_ControlAndCalls
import MiniRustSpec.Correspondence.Translate
import Lean.Elab.Command

/-!
# Correspondence of the last three `supported_untested` `Trusted.MirAst` variants

This file closes `StatementKind.constEvalCounter`, `TerminatorKind.tailCall`, and
`ProjectionElem.opaqueCast` — and pins `NonDivergingIntrinsic.copyNonOverlapping` through
element sub-place pointers (section 4) — against three references:

* **Trusted** — `Trusted.Rustc.V2026_06_01.MirSemantics` (`evalStmt`, `evalTerminator`,
  `stepMirFn`, `readProjectedValue`, …): universal (`∀`) characterizations of every
  success, external, and fail-closed (`.ub`) branch.
* **MiniRust** — the mechanically extracted `MiniRust.Snapshots.S2026_05_Matched.Generated.Ops`
  (`mrAdvanceStmtPc`, `MrStackFrame.jump_to_block`, `mrStepDispatchIsTerminator`,
  `mrFindCalleeById`) and the `MiniRustSpec` `minimize` transcription
  (`translateStatement`, `translateTerminator`, `translatePlace`, `borrowProjSteps`).
  Upstream `minimize` has **no** lowering for any of the three variants
  (`span_bug!` on `ConstEvalCounter`, `TailCall`, and `OpaqueCast`; anchored below), so
  the `MiniRustSpec` correspondence is *fail-closed*: the translation returns `none`, the
  fragment check rejects the construct, and no `MiniRustSpec` simulation is ever claimed
  for a body that contains one.
* **LeanMiri** — `lean-miri` is only in `examples/lakefile.toml`, so the exact step
  functions of `lean-miri/vendor/Miri/Interpreter/{Step,Call,ExecutionMachine,Projection,
  PlaceDynamic}.lean` that these variants reach are transcribed in `LeanMiri` below, one
  `@source-anchor` per transcribed source line; `scripts/audit_mir_coverage_matrix.py
  --check` re-reads every anchor from the vendored sources and checks the vendored files
  against their pinned SHA-256 (`lean-miri/UPSTREAM_PIN.json`,
  `minirust/minirust.lock.toml`), so the transcription cannot drift or be faked.

Semantic subtleties made explicit (never papered over):

* `constEvalCounter` is a pure program-counter step in all three references (Trusted
  `advanceStmt s s.frame.locals`, MiniRust `mrAdvanceStmtPc`, Miri's empty
  `incrementConstEvalCounter` hook followed by `Step.step`'s location increment); it is
  observationally identical to `nop` and never masks a later fault.
* `tailCall` replaces the active frame without pushing (`enterTailCalleeFrame`); the
  callee inherits the tail-caller's return continuation, so a return (or an external
  callee's `MirCallAns.returned`) lands directly in the caller's caller. Miri's
  `initFnTailCall` pops the frame and re-pushes the callee with the popped frame's
  `ReturnContinuation`, so the LeanMiri stack *shape* is preserved in lockstep — except at
  a whole-program root frame (`ReturnContinuation.stop`), where Miri raises
  `invalidProgram "cannot tailcall as root of stack"` while Trusted (whose root frame is the
  *modularly* verified function, i.e. a frame with an external `goto` continuation) steps.
  Direct-call arity and per-argument ABI are checked by Miri (UB, first failing parameter
  first) but not by Trusted (rustc's MIR type checker rules out ill-typed `FnDef` calls);
  indirect calls are checked by both. Miri's other `initStackFrame` checks are transcribed
  in source order through the `LeanMiri.CallChecks` oracle (`#[track_caller]`, calling
  convention, C-variadic ×2, target features, arguments, return ABI, `cleanup`); the
  calling-convention verdict is tied to Trusted's reified `FnPtrEntry` ABI by instantiating
  the oracle with the same `callConvEq` datum (`tailCall_abi_mismatch_corresponds`). For a
  callee whose ABI cannot unwind Miri forces the inherited unwind action to `Unreachable`,
  and so does Trusted: `enterTailCalleeFrame` narrows the saved caller's `returnUnwind`
  (`narrowCallStackForTailCallee`) and, for a tail call made by the modular root, lowers
  `Memory.rootUnwindCeiling`, so the stack shapes stay related for every inherited action
  and an unwind out of the non-unwinding callee is UB in both references at every depth
  (`tailCall_leanMiri_nounwind_callee_simulation`; the former divergence
  `DIV-LM-TAILCALL-NOUNWIND-UNWIND` is resolved).
  Both references tear the replaced tail-caller frame down: Miri's tail call *cleans up* the
  popped frame, deallocating its memory-backed locals, and Trusted's tail call — like its
  `return_` — rejects a teardown that would deallocate a protected local
  (`hasFrameDeallocProtectorConflict`, UB) and otherwise disables and marks dead every borrow
  of the frame's locals (`disableFrameBorrows` over the frame-depth-aware borrow table,
  `targetFrameDepth` / `allocDead`) before entering the callee. A raw pointer to a tail-caller
  local passed to the callee is therefore dangling in both, and dereferencing it is UB in both
  (`tailCall_leanMiri_cleanup_frees_caller_locals`,
  `tailCall_witness_dangling_caller_local_simulation`): the former Trusted soundness gap
  `DIV-TR-TAILCALL-DANGLING-CALLER-LOCAL` (an un-namespaced `targetLocal` that silently read
  the callee's same-index local) is resolved. Unwinding out of a callee that *can* unwind
  cannot observe the teardown (the catching caller disables every frame above it), so it is
  exactly the tail-caller's own unwind (`tailCall_trusted_unwind_through`). At a modular root
  Trusted addresses the external caller's memory as depth-`0` slots above the root's own
  locals; a root tail call into a callee with *more* locals now relocates every live
  caller-owned referent past the callee's frame (`relocateRootCallerReferents`), so a
  dereference of a pointer into the caller's memory still reads the caller's value, as in
  Miri, whose tail call leaves the caller's allocation live
  (`tailCall_witness_root_caller_referent_simulation`; the former Trusted soundness gap
  `DIV-TR-TAILCALL-ROOT-CALLER-REFERENT-SHADOW` is resolved). The one remaining modeling
  difference is the modular root itself: an unwind out of an *unwinding* root tail-callee
  escapes to Trusted's external caller (`.halted .panic`), whereas Miri's one-frame stack
  rejects it (`tailCall_leanMiri_modular_root_unwind`, `MODEL-LM-TAILCALL-MODULAR-ROOT`).
* `opaqueCast` is value-transparent and type-switching in Trusted (`readProjectedValue`,
  `writeProjectedValue`, `projectionsOverlap` ignore it; `resolveProjectedTy` and the
  union-aware readers retype to the cast type), whereas both Miri projection paths throw
  ("OpaqueCast after borrowck") — never a UB verdict — because rustc's MIR validator
  forbids `OpaqueCast` at `MirPhase::Runtime` (post-`PostAnalysisNormalize`), the phase of
  every captured body; the coverage matrix records `opaqueCast` as `supported_and_tested`
  (phase boundary). Trusted agrees with the opaque-cast-erased program up to the type
  switch: on an initialized local through any non-deref tail (`(_l as T).e.r` vs `_l.e.r`:
  reads, writes, protected writes, `.assign`; `placeMention` unconditionally), and — since
  the root dispatch looks through leading casts (`stripLeadingOpaqueCast`) — at a bare
  `(_l as T)` place and on an *uninitialized* local as well: `move`, `Deinit`,
  `SetDiscriminant`, and every assignment through the cast (including `(_l as T).f = v` into
  an uninitialized local) step like the erased place
  (`opaqueCast_trusted_root_dispatch_simulation`; the former latent divergence
  `DIV-TR-OPAQUECAST-ROOT-DISPATCH` is resolved).
* `copyNonOverlapping` between pointers to array *elements* (`&raw const src[i]`,
  `&raw mut dst[j]`) copies `count` elements in Trusted (`resolveCopySubplaceMulti`; formerly
  a single element whatever `count` was) or fails closed: a dead or missing root, a
  misaligned pointer, and a window that leaves its array or overlaps the other are UB, as in
  Miri, whose `copyWith` checks the total size, both alignments, and then `memCopy`
  (`copyNonOverlapping_leanMiri_check_order`). Two differences are explicit: a byte window
  that Trusted cannot re-encode is `.unsupported` (never a silent value), and a `count = 0`
  copy steps in Trusted without the alignment check that Miri performs "including for
  zero-length copies" (pre-existing; certified in `LeanMiriSpec`).

The final `run_cmd` is a kernel audit: every declaration of this namespace is free of
`sorryAx`, `Lean.ofReduceBool`, and `unsafe`, and every manifest theorem below exists and
mentions its variant constructor (non-vacuity).
-/

/-
Coverage manifest (checked by `scripts/audit_mir_coverage_matrix.py --check` and by the
final `run_cmd`):
-/
-- @mir-variant-coverage StatementKind.constEvalCounter trusted=constEvalCounter_trusted_step_universal,constEvalCounter_stepMirFn_universal,constEvalCounter_nop_statement_equiv minirust=constEvalCounter_minirust_ops_corresponds,constEvalCounter_minirustSpec_fail_closed leanmiri=constEvalCounter_leanMiri_lockstep,constEvalCounter_leanMiri_nop_equiv positive=constEvalCounter_witness_runs,constEvalCounter_leanMiri_witness negative=constEvalCounter_witness_ub_not_masked,constEvalCounter_witness_minirustSpec_rejects
-- @mir-variant-coverage TerminatorKind.tailCall trusted=tailCall_trusted_direct_enters_without_push,tailCall_trusted_vs_call_depth,tailCall_trusted_return_through,tailCall_trusted_external,tailCall_trusted_external_resume_is_return,tailCall_trusted_fail_closed_universal,tailCall_trusted_non_function_value_ub,tailCall_trusted_unwind_through,tailCall_trusted_direct_and_unsupported_fail_closed,tailCall_trusted_return_through_fail_closed minirust=tailCall_minirust_corresponds leanmiri=tailCall_leanMiri_shape_lockstep,tailCall_leanMiri_root_stop_diverges,tailCall_leanMiri_arity_ub,tailCall_leanMiri_ret_abi_and_cleanup_universal,tailCall_leanMiri_arg_abi_universal,tailCall_leanMiri_checks_classification,tailCall_leanMiri_nounwind_callee_simulation,tailCall_leanMiri_unwind_verdicts,tailCall_leanMiri_modular_root_unwind,tailCall_leanMiri_cleanup_frees_caller_locals,tailCall_abi_mismatch_corresponds,tailCall_leanMiri_calling_conv_ub_corresponds,tailCall_leanMiri_call_pushes positive=tailCall_leanMiri_witness,tailCall_witness_nested_runs,tailCall_witness_root_runs,tailCall_witness_external,tailCall_witness_indirect_and_zst,tailCall_witness_root_referent_copy negative=tailCall_witness_ub_cases,tailCall_witness_direct_arity_divergence,tailCall_leanMiri_witness_arg_abi,tailCall_leanMiri_witness_checks,tailCall_leanMiri_witness_unwind,tailCall_witness_dangling_caller_local_simulation,tailCall_witness_root_caller_referent_simulation
-- @mir-variant-coverage ProjectionElem.opaqueCast trusted=opaqueCast_trusted_traversal_universal,opaqueCast_trusted_retype_universal,opaqueCast_trusted_overlap_universal,opaqueCast_trusted_place_read_universal,opaqueCast_trusted_placeTy_and_helpers_universal,opaqueCast_trusted_write_and_borrow_universal,opaqueCast_trusted_place_rw_with_decls,opaqueCast_trusted_stmt_placeMention_and_deinit_universal,opaqueCast_trusted_root_dispatch_simulation minirust=opaqueCast_minirust_corresponds leanmiri=opaqueCast_leanMiri_phase_boundary positive=opaqueCast_witness_read_write,opaqueCast_witness_projected_move,opaqueCast_witness_place_rw_with_decls,opaqueCast_witness_root_dispatch negative=opaqueCast_witness_ub_not_masked,opaqueCast_witness_references_reject,opaqueCast_witness_type_switch
-- @mir-variant-coverage NonDivergingIntrinsic.copyNonOverlapping trusted=copyNonOverlapping_trusted_subplace_resolution_universal,copyNonOverlapping_trusted_elem_window_universal,copyNonOverlapping_trusted_byte_subplace_universal minirust=copyNonOverlapping_minirustSpec_fail_closed leanmiri=copyNonOverlapping_leanMiri_check_order positive=copyNonOverlapping_witness_elem_subplace_copies,copyNonOverlapping_witness_caller_referents_and_byte_pun negative=copyNonOverlapping_witness_ub_canaries,copyNonOverlapping_witness_resolution_canaries

/-
Source anchors (each is re-read verbatim from the pinned vendored file):
-/
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Step.lean#| .ConstEvalCounter => hooks.incrementConstEvalCounter choice state
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Step.lean#| .FakeRead .. | .AscribeUserType .. | .Coverage .. | .Nop
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Step.lean#| .BackwardIncompatibleDropHint .. => (state, .ok ())
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Step.lean#if oldIndex != newIndex then
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Step.lean#let next := { currentLoc with statementIndex := currentLoc.statementIndex + 1 }
-- @source-anchor lean-miri/vendor/Miri/Interpreter/ExecutionMachine.lean#incrementConstEvalCounter := fun _ state => (state,.ok ())
-- @source-anchor lean-miri/vendor/Miri/Interpreter/ExecutionMachine.lean#tailCall := fun c terminator => MachineHooks.run (Call.evalTailCallTerminator calls c limits.callDispatch terminator)
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#unless h.sameConvention callerFnAbi calleeFnAbi do
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#throw (.undefinedBehavior "caller/callee calling convention mismatch")
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#throw (.undefinedBehavior "caller/callee #[track_caller] mismatch")
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#throw (.undefinedBehavior "CVariadicMismatch")
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#throw (.undefinedBehavior "CVariadicFixedCountMismatch")
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#h.checkTargetFeatures choice fnInstance
-- @source-anchor lean-miri/vendor/Miri/Interpreter/ExecutionCallLeaves.lean#let message := "calling a function that requires unavailable target features: " ++
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#| .goto ret _ => .goto ret .Unreachable
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#if (request.callerFnAbi.any (fun abi => !h.abiCanUnwind abi)) then .Unreachable else request.unwind }
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#let args := evaluated.args.map fun arg => FnArg.Copy arg.copyFnArg
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#let frame ← h.popRaw choice
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#let (ret, unwind) ← match frame.returnContinuation with
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#| .goto ret unwind => pure (ret, unwind)
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#| .stop _ => throw (.invalidProgram "cannot tailcall as root of stack")
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#evaluated.withCallerLocation, frame.returnPlace, ret, unwind⟩
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#let action ← h.cleanup choice false frame
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#require (action == .normal) "tailcall cleanup must return Normal"
-- @source-anchor lean-miri/vendor/Miri/Interpreter/CallMachine.lean#| .goto .. => true | .stop cleanup => cleanup
-- @source-anchor lean-miri/vendor/Miri/Interpreter/CallMachine.lean#if !cleanup then return .noCleanup
-- @source-anchor lean-miri/vendor/Miri/Interpreter/CallMachine.lean#for slot in frame.locals do
-- @source-anchor lean-miri/vendor/Miri/Interpreter/CallMachine.lean#if let .live (.indirect place) := slot.value then h.storage.deallocateStack place.ptr
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#require ((← h.frameIndex) == oldIndex) "evaluating this tail call pushed a new stack frame"
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#| none => throw (.undefinedBehavior "calling a function with fewer arguments than it requires")
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#throw (.undefinedBehavior "calling a function with more arguments than it expected")
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#throw (.undefinedBehavior s!"AbiMismatchArgument {calleeIndex}")
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#throw (.undefinedBehavior "AbiMismatchReturn")
-- @source-anchor lean-miri/vendor/Miri/Interpreter/ControlFlow.lean#| .UnwindResume => return returnFromCurrentFrame hooks.toControlHooks choice true state
-- @source-anchor lean-miri/vendor/Miri/Interpreter/ControlFlow.lean#return (state, .error (.invalidProgram "return/unwind cleanup assertion failed"))
-- @source-anchor lean-miri/vendor/Miri/Interpreter/ControlFlow.lean#if unwinding && state.stack.frames.size == 1 then
-- @source-anchor lean-miri/vendor/Miri/Interpreter/ControlFlow.lean#return (state, .error (.undefinedBehavior "unwinding past the topmost stack frame"))
-- @source-anchor lean-miri/vendor/Miri/Interpreter/ControlFlow.lean#if unwinding then return unwindToBlock hooks choice unwind state
-- @source-anchor lean-miri/vendor/Miri/Interpreter/ControlFlow.lean#| .Cleanup block => return goToBlock block state
-- @source-anchor lean-miri/vendor/Miri/Interpreter/ControlFlow.lean#return (state, .error (.undefinedBehavior "unwinding past a frame that does not allow unwinding"))
-- @source-anchor lean-miri/vendor/Miri/Interpreter/ControlFlow.lean#| .Terminate reason => return hooks.unwindTerminate choice reason state
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Projection.lean#| .OpaqueCast _ => throw (.invariant "OpaqueCast after borrowck")
-- @source-anchor lean-miri/vendor/Miri/Interpreter/PlaceDynamic.lean#| .OpaqueCast _ => throw (.invalidProgram "OpaqueCast after borrowck")
-- @source-anchor minirust/vendor/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/bb.rs#| rs::StatementKind::ConstEvalCounter
-- @source-anchor minirust/vendor/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/bb.rs#| rs::TerminatorKind::TailCall { .. }
-- @source-anchor minirust/vendor/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/rvalue.rs#| smir::ProjectionElem::OpaqueCast(_) => {
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Intrinsics.lean#let some size := IntegerOps.computeSizeInBytes layout.layout.size count h.maxSizeOfVal
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Intrinsics.lean#| ub "overflow computing total size of copy"
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Intrinsics.lean#h.checkAlign choice source layout.layout.align.abi
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Intrinsics.lean#h.checkAlign choice dest layout.layout.align.abi
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Intrinsics.lean#h.memCopy choice source dest size nonoverlapping
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Intrinsics.lean#copyWith h choice source dest count true
-- @source-anchor minirust/vendor/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/bb.rs#rs::NonDivergingIntrinsic::CopyNonOverlapping(_) =>

namespace Anneal.MirUntestedVariantCorrespondenceTests

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRust.Snapshots.S2026_05_Matched.Generated.Ops
open Correspondence.V2026_06_01.L5_ControlAndCalls (toMrStackFrame)

/-! ## 0. `LeanMiri`: transcription of the vendored Miri step functions

Payload types the three variants never inspect (bodies, places, unwind actions, machine
state, interpreter choices) are kept abstract, so every theorem about the model holds for
*every* instantiation, in particular the concrete `lean-miri` one. Miri's frame `Array`
(active frame last) is a `List` with the active frame last. -/

namespace LeanMiri

/-- `Miri.Interpreter.ReturnContinuation` (`Interpreter/Stack.lean`): `goto ret unwind`
resumes the caller at block `ret` (`none` for a diverging call); `stop` marks a frame
without a caller (the whole-program root, e.g. the `start` frame). -/
inductive ReturnContinuation (U : Type) where
  | goto (ret : Option Nat) (unwind : U)
  | stop (cleanup : Bool)

/-- `Miri.MIR.Location`. -/
structure Location where
  block : Nat
  statementIndex : Nat
  deriving DecidableEq

/-- `Miri.Interpreter.FrameLocation`. -/
inductive FrameLocation where
  | mir (location : Location)
  | unwinding
  deriving DecidableEq

/-- The fields of `Miri.Interpreter.Frame` that `Step.step` and `Call.initFnTailCall` read
or write. -/
structure Frame (B P U : Type) where
  body : B
  returnContinuation : ReturnContinuation U
  returnPlace : P
  location : FrameLocation

/-- `Miri.Interpreter.StepState` (frames, active frame last; machine state). -/
structure StepState (B P U M : Type) where
  frames : List (Frame B P U)
  machine : M

/-- The `Miri.Interpreter.StepError` constructors reachable from the transcribed code. -/
inductive StepError where
  | undefinedBehavior (reason : String)
  | invalidProgram (reason : String)
  | invariant (reason : String)
  | frameIndexChanged (before after : Nat)
  | expectedMirLocation
  | emptyStack
  deriving DecidableEq

/-- `Miri.Interpreter.StepResult`. -/
abbrev StepResult (S A : Type) := S × Except StepError A

/-- `Miri.MIR.StatementKind` (constructor-for-constructor; payloads kept abstract). -/
inductive StatementKind (Pl Rv : Type) where
  | Assign (destination : Pl) (value : Rv)
  | FakeRead (place : Pl)
  | SetDiscriminant (place : Pl) (variant : Nat)
  | StorageLive (localId : Nat)
  | StorageDead (localId : Nat)
  | PlaceMention (place : Pl)
  | AscribeUserType (place : Pl)
  | Coverage
  | Intrinsic
  | ConstEvalCounter
  | Nop
  | BackwardIncompatibleDropHint (place : Pl)

/-- The statement hooks of `Miri.Interpreter.StepHooks`. -/
structure StepHooks (C S PV Pl Rv : Type) where
  assign : C → Pl → Rv → S → StepResult S Unit
  evalPlace : C → Pl → Bool → S → StepResult S PV
  writeDiscriminant : C → Nat → PV → S → StepResult S Unit
  storageLive : C → Nat → S → StepResult S Unit
  storageDead : C → Nat → S → StepResult S Unit
  intrinsic : C → S → StepResult S Unit
  incrementConstEvalCounter : C → S → StepResult S Unit

/-- `Step.evalStatement` (`Interpreter/Step.lean:61-78`), arm for arm. -/
def evalStatement {C S PV Pl Rv : Type} (hooks : StepHooks C S PV Pl Rv) (choice : C)
    (stmt : StatementKind Pl Rv) (state : S) : StepResult S Unit :=
  match stmt with
  | .Assign place value => hooks.assign choice place value state
  | .SetDiscriminant place variant =>
    match hooks.evalPlace choice place false state with
    | (state, .error error) => (state, .error error)
    | (state, .ok place) => hooks.writeDiscriminant choice variant place state
  | .StorageLive localId => hooks.storageLive choice localId state
  | .StorageDead localId => hooks.storageDead choice localId state
  | .Intrinsic => hooks.intrinsic choice state
  | .PlaceMention place =>
    match hooks.evalPlace choice place false state with
    | (state, result) => (state, result.map fun _ => ())
  | .ConstEvalCounter => hooks.incrementConstEvalCounter choice state
  | .FakeRead _ | .AscribeUserType _ | .Coverage | .Nop | .BackwardIncompatibleDropHint _ =>
    (state, .ok ())

/-- `ExecutionMachine.stepHooks.incrementConstEvalCounter`
(`Interpreter/ExecutionMachine.lean:360`, "Pinned Miri inherits rustc's empty counter
hook"). -/
def executionIncrementConstEvalCounter {C S : Type} : C → S → StepResult S Unit :=
  fun _ state => (state, .ok ())

/-- The location increment of `Step.step` (`Interpreter/Step.lean:109`). -/
def advanceLoc (loc : Location) : Location :=
  { loc with statementIndex := loc.statementIndex + 1 }

/-- The statement branch of `Step.step` (`Interpreter/Step.lean:95-115`) once
`block.statements[loc.statementIndex]? = some stmt`: evaluate the statement, reject a
callback that changed the frame index, then advance the *current* frame's location. -/
def stepStatement {B P U M C PV Pl Rv : Type}
    (hooks : StepHooks C (StepState B P U M) PV Pl Rv) (choice : C)
    (stmt : StatementKind Pl Rv) (state : StepState B P U M) :
    StepResult (StepState B P U M) Bool :=
  let oldIndex := state.frames.length - 1
  match evalStatement hooks choice stmt state with
  | (state, .error error) => (state, .error error)
  | (state, .ok ()) =>
    let newIndex := state.frames.length - 1
    if oldIndex != newIndex then (state, .error (.frameIndexChanged oldIndex newIndex))
    else
      match state.frames.getLast? with
      | none => (state, .error .emptyStack)
      | some current =>
        match current.location with
        | .unwinding => (state, .error .expectedMirLocation)
        | .mir currentLoc =>
          ({ state with
              frames := state.frames.set newIndex
                { current with location := .mir (advanceLoc currentLoc) } }, .ok true)

/-- The argument-passing loop of `initStackFrame` (`Interpreter/Call.lean:321-343`) over the
callee parameters `i, i+1, …` (`k` of them), in order: a missing caller argument is UB
"fewer arguments", and an ABI-incompatible one (`passArgument`, `Call.lean:213-214`) is UB
`AbiMismatchArgument i`; the first failing parameter decides. -/
def passArgsError (argAbiCompat : Nat → Bool) (argCount : Nat) : Nat → Nat → Option StepError
  | _, 0 => none
  | i, k + 1 =>
    if argCount ≤ i then
      some (.undefinedBehavior "calling a function with fewer arguments than it requires")
    else if !argAbiCompat i then some (.undefinedBehavior s!"AbiMismatchArgument {i}")
    else passArgsError argAbiCompat argCount (i + 1) k

/-- The outcomes of every check `initFnCallStep` / `initStackFrame` perform for a tail
call's callee (`Interpreter/Call.lean:241-358`, `Call.lean:362-364`), each an oracle over the
instantiated interpreter; the defaults describe a well-formed same-ABI call. -/
structure CallChecks (U : Type) where
  /-- `requiresLocation == withCallerLocation` (`Call.lean:245-247`). -/
  trackCallerMatch : Bool := true
  /-- `h.sameConvention callerFnAbi calleeFnAbi` (`Call.lean:254-255`). -/
  sameConvention : Bool := true
  /-- `h.abiVariadic callerFnAbi == h.abiVariadic calleeFnAbi` (`Call.lean:256-257`). -/
  variadicMatch : Bool := true
  /-- No C-variadic fixed-count mismatch (`Call.lean:258-259`). -/
  variadicFixedMatch : Bool := true
  /-- `h.checkTargetFeatures` finds every required target feature (`Call.lean:260`; otherwise
  UB "calling a function that requires unavailable target features", an abort on wasm-like
  targets, `ExecutionCallLeaves.lean`). -/
  targetFeaturesOk : Bool := true
  /-- `some ur` when the call-site ABI (`Call.lean:364`) or the callee ABI (`Call.lean:261-264`)
  cannot unwind: the inherited continuation's unwind action is replaced by `Unreachable` (`ur`). -/
  nounwindAs : Option U := none
  /-- Per-parameter ABI compatibility (`passArgument`, `Call.lean:213-214`). -/
  argAbiCompat : Nat → Bool := fun _ => true
  /-- Return-ABI compatibility (`Call.lean:345-346`). -/
  retAbiCompat : Bool := true
  /-- `cleanup` of the popped frame returns `.normal` (`Call.lean:445-446`). -/
  cleanupNormal : Bool := true

/-- `Call.initFnTailCall` (`Interpreter/Call.lean:436-446`) with the effect of the
`initFnCall` → `initFnCallStep` → `initStackFrame` push it performs: pop the active frame
(`popRaw`), reject a root frame (`ReturnContinuation.stop`), run every `initStackFrame`
check in source order (`#[track_caller]`, calling convention, C-variadic, target features,
the per-parameter loop, return ABI, surplus arguments), push the callee with the popped
frame's return place and continuation (its unwind action forced to `Unreachable` for a
non-unwinding ABI), and require `cleanup` to return `.normal`. -/
def initFnTailCall {B P U M : Type} (callee : B) (calleeArgCount argCount : Nat)
    (state : StepState B P U M) (ck : CallChecks U := {}) :
    Except StepError (StepState B P U M) :=
  match state.frames.getLast? with
  | none => .error .emptyStack
  | some frame =>
    match frame.returnContinuation with
    | .stop _ => .error (.invalidProgram "cannot tailcall as root of stack")
    | .goto ret unwind =>
      if !ck.trackCallerMatch then
        .error (.undefinedBehavior "caller/callee #[track_caller] mismatch")
      else if !ck.sameConvention then
        .error (.undefinedBehavior "caller/callee calling convention mismatch")
      else if !ck.variadicMatch then .error (.undefinedBehavior "CVariadicMismatch")
      else if !ck.variadicFixedMatch then .error (.undefinedBehavior "CVariadicFixedCountMismatch")
      else if !ck.targetFeaturesOk then
        .error (.undefinedBehavior "calling a function that requires unavailable target features")
      else
      match passArgsError ck.argAbiCompat argCount 0 calleeArgCount with
      | some e => .error e
      | none =>
      if !ck.retAbiCompat then
        .error (.undefinedBehavior "AbiMismatchReturn")
      else if calleeArgCount < argCount then
        .error (.undefinedBehavior "calling a function with more arguments than it expected")
      else if !ck.cleanupNormal then
        .error (.invalidProgram "tailcall cleanup must return Normal")
      else
        .ok { state with
          frames := state.frames.dropLast ++
            [{ body := callee, returnContinuation := .goto ret (ck.nounwindAs.getD unwind),
               returnPlace := frame.returnPlace, location := .mir ⟨0, 0⟩ }] }

/-- `Call.evalTailCallTerminator` (`Interpreter/Call.lean:464-471`): the tail call must
leave the frame index unchanged. -/
def evalTailCallTerminator {B P U M : Type} (callee : B) (calleeArgCount argCount : Nat)
    (state : StepState B P U M) (ck : CallChecks U := {}) :
    Except StepError (StepState B P U M) :=
  let oldIndex := state.frames.length - 1
  match initFnTailCall callee calleeArgCount argCount state ck with
  | .error e => .error e
  | .ok state' =>
    if state'.frames.length - 1 == oldIndex then .ok state'
    else .error (.invalidProgram "evaluating this tail call pushed a new stack frame")

/-- The stack effect of `Call.evalCallTerminator` / `initStackFrame` for a returning call
(`.goto target unwind`): push the callee above the caller. -/
def evalCallPush {B P U M : Type} (callee : B) (dest : P) (target : Option Nat) (unwind : U)
    (state : StepState B P U M) : StepState B P U M :=
  { state with
    frames := state.frames ++
      [{ body := callee, returnContinuation := .goto target unwind, returnPlace := dest,
         location := .mir ⟨0, 0⟩ }] }

/-- `Projection.project` (`Interpreter/Projection.lean:252`) on `OpaqueCast`. -/
def projectOpaqueCast {T A : Type} (_ty : T) : Except StepError A :=
  .error (.invariant "OpaqueCast after borrowck")

/-- `PlaceDynamic.project` (`Interpreter/PlaceDynamic.lean:150`) on `OpaqueCast`. -/
def placeProjectOpaqueCast {T A : Type} (_ty : T) : Except StepError A :=
  .error (.invalidProgram "OpaqueCast after borrowck")

/-- Verdict of `ControlFlow.unwindToBlock` (`Interpreter/ControlFlow.lean:42-60`) for the
caller of the popped frame. -/
inductive UnwindVerdict where
  /-- `.Cleanup block => goToBlock block`: the caller resumes at its cleanup block. -/
  | cleanup (bb : Nat)
  /-- `.Continue`: the caller's location becomes `.unwinding span`, so it keeps unwinding. -/
  | continueUnwinding
  /-- `.Terminate reason => hooks.unwindTerminate`: the unwind becomes an abort. -/
  | terminate
  deriving DecidableEq

/-- `ControlFlow.unwindToBlock` (`Interpreter/ControlFlow.lean:42-60`) over the shared
`UnwindAction` vocabulary (`Cleanup` / `Unreachable` / `Continue` / `Terminate`). -/
def unwindToBlock : UnwindAction → Except StepError UnwindVerdict
  | .cleanup bb => .ok (.cleanup bb)
  | .unreachable =>
    .error (.undefinedBehavior "unwinding past a frame that does not allow unwinding")
  | .continue_ => .ok .continueUnwinding
  | .terminate => .ok .terminate

/-- `UnwindResume` (`ControlFlow.evalTerminator`) =
`returnFromCurrentFrame … (unwinding := true)` (`Interpreter/ControlFlow.lean:64-112`):
the active frame must be in a cleanup block (`isCleanup`; rustc's validator only places
`UnwindResume` there); unwinding out of the only frame is UB; then, with the return-operand,
pop, and cleanup hooks succeeding (`.normal`), the popped frame's `goto _ unwind`
continuation is resolved by `unwindToBlock` (a `stop` continuation cannot be unwound). -/
def unwindResume {B P M : Type} (state : StepState B P UnwindAction M)
    (isCleanup : Bool := true) : Except StepError UnwindVerdict :=
  match state.frames.getLast? with
  | none => .error .emptyStack
  | some frame =>
    if !isCleanup then
      .error (.invalidProgram "return/unwind cleanup assertion failed")
    else if state.frames.length == 1 then
      .error (.undefinedBehavior "unwinding past the topmost stack frame")
    else
      match frame.returnContinuation with
      | .goto _ unwind => unwindToBlock unwind
      | .stop _ => .error (.invalidProgram "Stop continuation requires normal root return")

/-- `CallMachine.cleanup` (`Interpreter/CallMachine.lean:75-86`), run by `initFnTailCall` on
the popped tail-caller frame (`h.cleanup choice false frame`): a frame is cleaned up iff its
continuation is `goto` (or `stop true`), and cleaning it up deallocates every live
memory-backed local (`deallocateStack`) before the machine's `afterPop`. -/
def cleanupDeallocatesLocals {U : Type} : ReturnContinuation U → Bool
  | .goto .. => true
  | .stop cleanup => cleanup

/-- Whether a Miri error is a UB verdict. -/
def StepError.isUB : StepError → Bool
  | .undefinedBehavior _ => true
  | _ => false

/-- The `Miri.Interpreter.MemoryIntrinsicHooks` leaves that `Intrinsics.copyWith` runs once the
count and the two pointers are read, each an oracle over the instantiated interpreter. -/
structure CopyHooks (Ptr : Type) where
  /-- `IntegerOps.computeSizeInBytes layout.layout.size count h.maxSizeOfVal`: the total byte
  size of `count` elements of the pointee size, `none` on overflow. -/
  totalSize : Nat → Nat → Option Nat
  /-- `h.checkAlign choice ptr layout.layout.align.abi`: `none` when the pointer is aligned for
  the pointee, the raised error otherwise. -/
  checkAlign : Ptr → Nat → Option StepError
  /-- `h.memCopy choice source dest size nonoverlapping`: `none` when the copy succeeds, the
  raised error (out-of-bounds, overlapping ranges, dangling, …) otherwise. -/
  memCopy : Ptr → Ptr → Nat → Bool → Option StepError

/-- `Intrinsics.copyWith` (`Interpreter/Intrinsics.lean:143-157`) after the operand reads: the
total size (UB on overflow), then the alignment check of the source and of the destination —
"including for zero-length copies" — and only then the memory copy. -/
def copyWith {Ptr : Type} (h : CopyHooks Ptr) (elemSize elemAlign : Nat) (source dest : Ptr)
    (count : Nat) (nonoverlapping : Bool) : Except StepError Unit :=
  match h.totalSize elemSize count with
  | none => .error (.undefinedBehavior "overflow computing total size of copy")
  | some size =>
    match h.checkAlign source elemAlign with
    | some e => .error e
    | none =>
      match h.checkAlign dest elemAlign with
      | some e => .error e
      | none =>
        match h.memCopy source dest size nonoverlapping with
        | some e => .error e
        | none => .ok ()

/-- `Intrinsics.evalNondivergingWith` on `CopyNonOverlapping`
(`Interpreter/Intrinsics.lean:571-575`): `copyWith … true` — the two ranges must not overlap. -/
def evalCopyNonOverlapping {Ptr : Type} (h : CopyHooks Ptr) (elemSize elemAlign : Nat)
    (source dest : Ptr) (count : Nat) : Except StepError Unit :=
  copyWith h elemSize elemAlign source dest count true

end LeanMiri

/-! ### Concrete MIR builders and a small-step runner -/

def tyU32 : Ty := { kind := .uint .u32, layoutIdx := 0 }

def tyU8 : Ty := { kind := .uint .u8, layoutIdx := 0 }

def u32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .primitive, variants := .single 0, isUninhabited := false, fieldLayouts := [] }

def wFnAbi : FnAbi :=
  { args := [], ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := false }

def wLayouts : LayoutTable := { pointerBits := 64, isLittleEndian := true, entries := [] }

/-- A `Runtime(PostCleanup)` body with the given locals and blocks. -/
def mkBody (dp : DefPath) (argCount : Nat) (decls : List LocalDecl)
    (bbs : List BasicBlockData) : CapturedMir :=
  { defPath := dp, argCount, localDecls := decls, basicBlocks := bbs,
    phase := .runtimePostCleanup, role := .subject, fnAbi := wFnAbi, layouts := wLayouts,
    allocations := [] }

def u32Decl (name : String) : LocalDecl := { mutability := .mut, ty := tyU32, debugName := some name }

def cU32 (v : Nat) : Operand := .constant { ty := tyU32, val := .scalar (.int ⟨v, 4⟩) }

def cU8 (v : Nat) : Operand := .constant { ty := tyU8, val := .scalar (.int ⟨v, 1⟩) }

def lc (i : Nat) : Place := { local_ := i, projection := [] }

def st (k : StatementKind) : Statement := { kind := k, span := "w" }

def assignU32 (dst v : Nat) : Statement := st (.assign (lc dst) (.use (cU32 v)))

def assignMove (dst src : Nat) : Statement := st (.assign (lc dst) (.use (.move (lc src))))

def blk (stmts : List Statement) (t : TerminatorKind) : BasicBlockData :=
  { statements := stmts, terminator := { kind := t, span := "w" }, isCleanup := false }

/-- One coalgebra step on `MirExecState`: observations are resolved, faults become
`.faulted`, and a pending external call yields `none`. -/
def execStep (body : CapturedMir) (s : MirExecState) : Option MirExecState :=
  match stepMirState body s with
  | .ret out => some (.halted out)
  | .tau s' => some s'
  | .vis (.inl (.fail k)) _ => some (.faulted k)
  | .vis (.inr (.inl _)) k => some (k PUnit.unit)
  | .vis (.inr (.inr _)) _ => none

/-- `n` coalgebra steps. -/
def execN (body : CapturedMir) : Nat → MirExecState → Option MirExecState
  | 0, s => some s
  | n + 1, s => (execStep body s).bind (execN body n)

/-- The returned value of a normal outcome. -/
def retVal? : Option MirOutcome → Option Value
  | some (.normal (v, _)) => some v
  | _ => none

/-- The returned value of a halted state. -/
def haltedVal? : Option MirExecState → Option Value
  | some (.halted (.normal (v, _))) => some v
  | _ => none

/-- Whether a state is a UB fault. -/
def isUbFault : Option MirExecState → Bool
  | some (.faulted .ub) => true
  | _ => false

/-- Call-stack depth of a running state. -/
def depth? : Option MirExecState → Option Nat
  | some (.running s) => some s.memory.callStack.length
  | _ => none

private theorem mapM_none_of_mem {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (x : α), x ∈ xs → f x = none → xs.mapM f = none
  | [], _, h, _ => absurd h List.not_mem_nil
  | y :: ys, x, h, hx => by
    rcases List.mem_cons.mp h with rfl | h'
    · simp [List.mapM_cons, hx]
    · cases hy : f y with
      | none => simp [List.mapM_cons, hy]
      | some b => simp [List.mapM_cons, hy, mapM_none_of_mem f ys x h' hx]

/-- A body that contains a statement rejected by `MiniRustSpec`'s fragment check is not in
the `MiniRustSpec` fragment (so `step_correspondence` is never claimed for it). -/
private theorem inFragment_false_of_stmt {body : CapturedMir} {bb : BasicBlockData}
    (hbb : bb ∈ body.basicBlocks) {s : Statement} (hs : s ∈ bb.statements)
    (hbad : MiniRustSpec.Correspondence.statementOk body.localDecls s body.layouts = false) :
    MiniRustSpec.Correspondence.inFragment body = false := by
  cases h : MiniRustSpec.Correspondence.inFragment body with
  | false => rfl
  | true =>
    exfalso
    simp only [MiniRustSpec.Correspondence.inFragment, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hbbs⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
    obtain ⟨⟨_, hst⟩, _⟩ := hbbs bb hbb
    rw [hst s hs] at hbad
    exact Bool.noConfusion hbad

/-! ## 1. `StatementKind.constEvalCounter` -/

section ConstEvalCounter

/-- **Trusted (universal).** For every state, span, and body context, `.constEvalCounter`
is a pure program-counter step: it advances `stmtIdx` by one and leaves the block, the
locals, and the whole `Memory` untouched — the same transition as `.nop`. -/
theorem constEvalCounter_trusted_step_universal
    (s : MachineState) (span span' : String) (localDecls localDecls' : List LocalDecl)
    (layouts layouts' : LayoutTable) :
    evalStmt s ⟨.constEvalCounter, span⟩ localDecls layouts =
        MirStepNode.step { s with frame := { s.frame with stmtIdx := s.frame.stmtIdx + 1 } } ∧
      evalStmt s ⟨.constEvalCounter, span⟩ localDecls layouts =
        evalStmt s ⟨.nop, span'⟩ localDecls' layouts' ∧
      (advanceStmt s s.frame.locals).frame.locals = s.frame.locals ∧
      (advanceStmt s s.frame.locals).frame.blockIdx = s.frame.blockIdx ∧
      (advanceStmt s s.frame.locals).frame.stmtIdx = s.frame.stmtIdx + 1 ∧
      (advanceStmt s s.frame.locals).memory = s.memory :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Trusted machine step (universal).** Whenever the active body (root or callee) is at a
`.constEvalCounter` statement, `stepMirFn` / `stepMirState` take exactly the silent
program-counter step, in both runtime phases. -/
theorem constEvalCounter_stepMirFn_universal
    (body : CapturedMir) (s : MachineState) (bb : BasicBlockData) (span : String)
    (hphase : (s.memory.activeCallee.getD body).phase = .runtimePostCleanup ∨
      (s.memory.activeCallee.getD body).phase = .runtimeOptimized)
    (hbb : get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx = some bb)
    (hst : get? bb.statements s.frame.stmtIdx = some ⟨.constEvalCounter, span⟩) :
    stepMirFn body s = .tau (.running (advanceStmt s s.frame.locals)) ∧
      stepMirState body (.running s) = .tau (.running (advanceStmt s s.frame.locals)) := by
  have h : stepMirFn body s = .tau (.running (advanceStmt s s.frame.locals)) := by
    rcases hphase with hp | hp <;>
      simp only [stepMirFn, hp, hbb, hst] <;> rfl
  exact ⟨h, h⟩

/-- Replace a `.constEvalCounter` statement by `.nop` (indices are preserved). -/
def counterToNop (s : Statement) : Statement :=
  match s.kind with
  | .constEvalCounter => { s with kind := .nop }
  | _ => s

/-- Replace every `.constEvalCounter` statement of a body by `.nop`. -/
def nopifyBody (b : CapturedMir) : CapturedMir :=
  { b with basicBlocks := b.basicBlocks.map fun bb =>
      { bb with statements := bb.statements.map counterToNop } }

/-- **Trusted observational equivalence (universal).** Every statement evaluates identically
after replacing counters by `nop`, and on every root-frame statement step the
counter-erased body steps exactly like the original. -/
theorem constEvalCounter_nop_statement_equiv :
    (∀ (s : MachineState) (stm : Statement) (ld : List LocalDecl) (ly : LayoutTable),
      evalStmt s (counterToNop stm) ld ly = evalStmt s stm ld ly) ∧
    (∀ (body : CapturedMir) (s : MachineState) (bb : BasicBlockData) (stm : Statement),
      s.memory.activeCallee = none →
      get? body.basicBlocks s.frame.blockIdx = some bb →
      get? bb.statements s.frame.stmtIdx = some stm →
      stepMirFn (nopifyBody body) s = stepMirFn body s) := by
  have hstmt : ∀ (s : MachineState) (stm : Statement) (ld : List LocalDecl) (ly : LayoutTable),
      evalStmt s (counterToNop stm) ld ly = evalStmt s stm ld ly := by
    intro s stm ld ly
    obtain ⟨kind, span⟩ := stm
    cases kind <;> rfl
  refine ⟨hstmt, ?_⟩
  intro body s bb stm hroot hbb hst
  have hbb' : get? (nopifyBody body).basicBlocks s.frame.blockIdx =
      some { bb with statements := bb.statements.map counterToNop } := by
    simp only [nopifyBody, get?, List.getElem?_map] at hbb ⊢
    rw [hbb]; rfl
  have hst' : get? (bb.statements.map counterToNop) s.frame.stmtIdx = some (counterToNop stm) := by
    simp only [get?, List.getElem?_map] at hst ⊢
    rw [hst]; rfl
  simp only [stepMirFn, hroot, Option.getD_none, hbb', hst', hbb, hst, hstmt]
  rfl

/-- **MiniRust `Generated.Ops` (universal).** The counter step is MiniRust's
`mrAdvanceStmtPc` program-counter increment on the generated `MrStackFrame`, and the
following dispatch (statement vs. terminator) agrees with `mrStepDispatchIsTerminator`. -/
theorem constEvalCounter_minirust_ops_corresponds
    (s : MachineState) (span : String) (bb : BasicBlockData) :
    evalStmt s ⟨.constEvalCounter, span⟩ = MirStepNode.step (advanceStmt s s.frame.locals) ∧
      (advanceStmt s s.frame.locals).frame.stmtIdx = mrAdvanceStmtPc s.frame.stmtIdx ∧
      toMrStackFrame (advanceStmt s s.frame.locals).frame =
        { toMrStackFrame s.frame with stmtIdx := mrAdvanceStmtPc s.frame.stmtIdx } ∧
      ((advanceStmt s s.frame.locals).frame.stmtIdx == length bb.statements) =
        mrStepDispatchIsTerminator (mrAdvanceStmtPc s.frame.stmtIdx) (length bb.statements) :=
  ⟨(Correspondence.V2026_06_01.L5_ControlAndCalls.mir_evalStmt_nop_coverage_constEvalCounter
      s span).2.2.1,
    (Correspondence.V2026_06_01.L5_ControlAndCalls.mir_advanceStmt_corresponds
      s s.frame.locals s.memory).1,
    (Correspondence.V2026_06_01.L5_ControlAndCalls.mir_advanceStmt_corresponds
      s s.frame.locals s.memory).2.2.2.2, rfl⟩

/-- **MiniRustSpec (universal, fail-closed).** MiniRust has no `ConstEvalCounter`
statement and upstream `minimize` aborts on it (`span_bug!`, anchored above). The
`MiniRustSpec` transcription mirrors that exactly: the statement does not translate, the
fragment check rejects it, every block containing it fails to translate, and every body
containing it lies outside the `MiniRustSpec` fragment. -/
theorem constEvalCounter_minirustSpec_fail_closed
    (decls : List LocalDecl) (layouts : LayoutTable) (span : String) :
    MiniRustSpec.Correspondence.translateStatement decls ⟨.constEvalCounter, span⟩ layouts = none ∧
      MiniRustSpec.Correspondence.statementOk decls ⟨.constEvalCounter, span⟩ layouts = false ∧
      (∀ (bb : BasicBlockData) (s : Statement), s ∈ bb.statements → s.kind = .constEvalCounter →
        MiniRustSpec.Correspondence.translateBlock layouts decls bb = none) ∧
      (∀ (body : CapturedMir) (bb : BasicBlockData) (s : Statement), bb ∈ body.basicBlocks →
        s ∈ bb.statements → s.kind = .constEvalCounter →
        MiniRustSpec.Correspondence.inFragment body = false) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro bb s hs hk
    have hnone : bb.statements.mapM
        (fun x => MiniRustSpec.Correspondence.translateStatement decls x layouts) = none :=
      mapM_none_of_mem _ bb.statements s hs (by
        simp [MiniRustSpec.Correspondence.translateStatement, hk])
    simp [MiniRustSpec.Correspondence.translateBlock, hnone]
  · intro body bb s hbb hs hk
    exact inFragment_false_of_stmt hbb hs (by simp [MiniRustSpec.Correspondence.statementOk, hk])

/-- Trusted ↔ LeanMiri program-counter relation for the active frame. -/
def PcRel {B P U M : Type} (s : MachineState) (m : LeanMiri.StepState B P U M) : Prop :=
  ∃ f, m.frames.getLast? = some f ∧
    f.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩

/-- The non-program-counter part of the LeanMiri frames. -/
def eraseLocs {B P U : Type} (fs : List (LeanMiri.Frame B P U)) : List (LeanMiri.Frame B P U) :=
  fs.map fun f => { f with location := .unwinding }

/-- Lockstep relation, parametric in *any* relation `D` between the Trusted data (locals,
memory) and the LeanMiri non-program-counter data (machine, location-erased frames). -/
def LockstepRel {B P U M : Type}
    (D : List LocalSlot → Memory → M → List (LeanMiri.Frame B P U) → Prop)
    (s : MachineState) (m : LeanMiri.StepState B P U M) : Prop :=
  PcRel s m ∧ D s.frame.locals s.memory m.machine (eraseLocs m.frames)

private theorem getLast?_set_last {α : Type} {l : List α} {f : α} (h : l.getLast? = some f)
    (x : α) : (l.set (l.length - 1) x).getLast? = some x := by
  obtain ⟨init, rfl⟩ := List.getLast?_eq_some_iff.mp h
  simp

private theorem eraseLocs_set_last {B P U : Type} {l : List (LeanMiri.Frame B P U)}
    {f : LeanMiri.Frame B P U} (h : l.getLast? = some f) (loc : LeanMiri.FrameLocation) :
    eraseLocs (l.set (l.length - 1) { f with location := loc }) = eraseLocs l := by
  obtain ⟨init, rfl⟩ := List.getLast?_eq_some_iff.mp h
  simp [eraseLocs]

/-- **LeanMiri lockstep (universal).** For every LeanMiri instantiation whose counter hook
is the pinned `ExecutionMachine` one, every interpreter choice, and *every* data relation
`D`: if the Trusted state and the LeanMiri state agree on the active program counter and
are `D`-related, then one `.constEvalCounter` step on each side (`evalStmt` /
`Step.step`'s statement branch) succeeds and the successors are again related — both
sides advance the statement index by exactly one and change nothing else (the machine
and the location-erased frames are untouched, so `D` is preserved for free). -/
theorem constEvalCounter_leanMiri_lockstep {B P U M C PV Pl Rv : Type}
    (hooks : LeanMiri.StepHooks C (LeanMiri.StepState B P U M) PV Pl Rv)
    (hhook : hooks.incrementConstEvalCounter = LeanMiri.executionIncrementConstEvalCounter)
    (choice : C) (D : List LocalSlot → Memory → M → List (LeanMiri.Frame B P U) → Prop)
    (s : MachineState) (m : LeanMiri.StepState B P U M) (span : String)
    (ld : List LocalDecl) (ly : LayoutTable) (hrel : LockstepRel D s m) :
    ∃ m', LeanMiri.stepStatement hooks choice .ConstEvalCounter m = (m', .ok true) ∧
      evalStmt s ⟨.constEvalCounter, span⟩ ld ly = MirStepNode.step (advanceStmt s s.frame.locals) ∧
      LockstepRel D (advanceStmt s s.frame.locals) m' ∧
      m'.machine = m.machine ∧ m'.frames.length = m.frames.length := by
  obtain ⟨⟨f, hlast, hloc⟩, hD⟩ := hrel
  let f' : LeanMiri.Frame B P U :=
    { f with location := .mir (LeanMiri.advanceLoc ⟨s.frame.blockIdx, s.frame.stmtIdx⟩) }
  refine ⟨{ m with frames := m.frames.set (m.frames.length - 1) f' },
    ?_, rfl, ⟨⟨_, getLast?_set_last hlast _, rfl⟩, ?_⟩, rfl, by simp⟩
  · simp only [LeanMiri.stepStatement, LeanMiri.evalStatement, hhook,
      LeanMiri.executionIncrementConstEvalCounter, bne_self_eq_false, hlast, hloc]
    rfl
  · show D s.frame.locals s.memory m.machine (eraseLocs (m.frames.set (m.frames.length - 1) _))
    rw [eraseLocs_set_last hlast]
    exact hD

/-- **LeanMiri nop equivalence (universal).** With the pinned empty counter hook, the
LeanMiri step on `ConstEvalCounter` is the step on `Nop` — the Miri counterpart of the
Trusted `.constEvalCounter = .nop` equation. -/
theorem constEvalCounter_leanMiri_nop_equiv {B P U M C PV Pl Rv : Type}
    (hooks : LeanMiri.StepHooks C (LeanMiri.StepState B P U M) PV Pl Rv)
    (hhook : hooks.incrementConstEvalCounter = LeanMiri.executionIncrementConstEvalCounter)
    (choice : C) (m : LeanMiri.StepState B P U M) :
    LeanMiri.stepStatement hooks choice .ConstEvalCounter m =
      LeanMiri.stepStatement hooks choice .Nop m ∧
    LeanMiri.evalStatement hooks choice .ConstEvalCounter m = (m, .ok ()) := by
  refine ⟨?_, ?_⟩ <;>
    simp only [LeanMiri.stepStatement, LeanMiri.evalStatement, hhook,
      LeanMiri.executionIncrementConstEvalCounter]

/-! ### Concrete witnesses -/

/-- `fn counter() -> u32 { ConstEvalCounter; _0 = 42; ConstEvalCounter; return }`. -/
def counterBody : CapturedMir :=
  mkBody "w::counter" 0 [u32Decl "_0"]
    [blk [st .constEvalCounter, assignU32 0 42, st .constEvalCounter] .return_]

/-- The same function without counters. -/
def plainBody : CapturedMir :=
  mkBody "w::plain" 0 [u32Decl "_0"] [blk [assignU32 0 42] .return_]

/-- `fn bad() -> u32 { ConstEvalCounter; return }`: `_0` is never written. -/
def counterUbBody : CapturedMir :=
  mkBody "w::counter_ub" 0 [u32Decl "_0"] [blk [st .constEvalCounter] .return_]

/-- **Positive witness.** The counter body returns `42` like the counter-free body, with
the identical final outcome; each counter costs exactly one silent step (the counter body
needs two more steps), and the first step is the pure program-counter advance. -/
theorem constEvalCounter_witness_runs :
    retVal? (Anneal.MirFuelFree.runMirExecBounded 4 counterBody
        (.running (initMachineState counterBody []))) = some (.scalar ⟨42, 4⟩) ∧
      Anneal.MirFuelFree.runMirExecBounded 4 counterBody
          (.running (initMachineState counterBody [])) =
        Anneal.MirFuelFree.runMirExecBounded 2 plainBody
          (.running (initMachineState plainBody [])) ∧
      Anneal.MirFuelFree.runMirExecBounded 3 counterBody
          (.running (initMachineState counterBody [])) = none ∧
      execN counterBody 1 (.running (initMachineState counterBody [])) =
        some (.running (advanceStmt (initMachineState counterBody [])
          (initMachineState counterBody []).frame.locals)) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Negative witness.** A counter never initializes anything: after the counter step,
`return` with an uninitialized `_0` faults with UB — exactly as without the counter. -/
theorem constEvalCounter_witness_ub_not_masked :
    isUbFault (execN counterUbBody 2 (.running (initMachineState counterUbBody []))) = true ∧
      stepMirState counterUbBody
          (.running (advanceStmt (initMachineState counterUbBody [])
            (initMachineState counterUbBody []).frame.locals)) =
        MirStepNode.fail .ub :=
  ⟨rfl, rfl⟩

/-- **Negative witness (MiniRustSpec).** The counter-free body is in the `MiniRustSpec`
fragment, while the counter body is rejected (fail-closed), and its block does not
translate. -/
theorem constEvalCounter_witness_minirustSpec_rejects :
    MiniRustSpec.Correspondence.inFragment plainBody = true ∧
      MiniRustSpec.Correspondence.inFragment counterBody = false ∧
      MiniRustSpec.Correspondence.translateBlock counterBody.layouts counterBody.localDecls
        (blk [st .constEvalCounter, assignU32 0 42, st .constEvalCounter] .return_) = none := by
  refine ⟨by decide, ?_, ?_⟩
  · exact (constEvalCounter_minirustSpec_fail_closed counterBody.localDecls counterBody.layouts
      "w").2.2.2 counterBody _ (st .constEvalCounter) (List.mem_singleton_self _)
      (List.mem_cons_self) rfl
  · exact (constEvalCounter_minirustSpec_fail_closed counterBody.localDecls counterBody.layouts
      "w").2.2.1 _ (st .constEvalCounter) List.mem_cons_self rfl

/-- **LeanMiri witness.** A concrete LeanMiri state at `bb2[3]` (a root frame with a `stop`
continuation, machine state `7`) steps over `ConstEvalCounter` to `bb2[4]`, machine and
continuation untouched, exactly like the Trusted state at `bb2[3]`. -/
theorem constEvalCounter_leanMiri_witness :
    let hooks : LeanMiri.StepHooks Unit (LeanMiri.StepState Unit Unit Unit Nat) Unit Unit Unit :=
      { assign := fun _ _ _ s => (s, .ok ()), evalPlace := fun _ _ _ s => (s, .ok ()),
        writeDiscriminant := fun _ _ _ s => (s, .ok ()), storageLive := fun _ _ s => (s, .ok ()),
        storageDead := fun _ _ s => (s, .ok ()), intrinsic := fun _ s => (s, .ok ()),
        incrementConstEvalCounter := LeanMiri.executionIncrementConstEvalCounter }
    let fr : LeanMiri.Frame Unit Unit Unit :=
      { body := (), returnContinuation := .stop false, returnPlace := (),
        location := .mir ⟨2, 3⟩ }
    let s : MachineState := { frame := { blockIdx := 2, stmtIdx := 3, locals := [] }, memory := {} }
    LeanMiri.stepStatement hooks () .ConstEvalCounter ⟨[fr], 7⟩ =
        (⟨[{ fr with location := .mir ⟨2, 4⟩ }], 7⟩, .ok true) ∧
      PcRel (advanceStmt s s.frame.locals)
        (⟨[{ fr with location := .mir ⟨2, 4⟩ }], 7⟩ : LeanMiri.StepState Unit Unit Unit Nat) :=
  ⟨rfl, ⟨_, rfl, rfl⟩⟩

end ConstEvalCounter

/-! ## 2. `TerminatorKind.tailCall` -/

section TailCall

/-- Trusted's frame teardown of the active frame (run by `TerminatorKind.return_`, and by a
tail call before `enterTailCalleeFrame` replaces the frame): every borrow of one of its locals
— depth `length s.memory.callStack`, local index `< length s.frame.locals` — is disabled and
marked dead (`disableFrameBorrows`); every other memory component is unchanged. -/
def frameTeardownMem (s : MachineState) : Memory :=
  { s.memory with
    borrows := disableFrameBorrows s.memory.borrows (length s.memory.callStack)
      (length s.frame.locals) }

/-- The protector guard of Trusted's frame teardown (`hasFrameDeallocProtectorConflict`):
`true` iff deallocating a local of the active frame would remove a tag that an active
function-entry protector protects and whose permission prevents deallocation — `return_` and
a tail call are then UB instead of tearing the frame down. -/
def frameDeallocConflict (s : MachineState) : Bool :=
  hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
    (length s.memory.callStack) (length s.frame.locals)

/-- The memory in which Trusted resumes the saved `caller` once it has been popped off the
call stack — by `return_` (after the frame teardown) or by `unwindFromCallStack`. -/
def popCallerMem (mem : Memory) (caller : SavedCallerFrame) (rest : List SavedCallerFrame) :
    Memory :=
  { mem with callStack := rest, activeCallee := some caller.callerBody,
             activeProtectors := restoreCallerProtectors caller }

/-- The memory in which Trusted enters an in-table tail callee (`tailCalleeEntryMemory`): the
frame teardown and then — only at a modular root (`s.memory.callStack = []`), whose
caller-owned referents are addressed as depth-`0` slots past the root's own locals — the
relocation of the live caller-owned referents past the callee's frame
(`relocateRootCallerReferents`). -/
def tailEntryMem (s : MachineState) (calleeBody : CapturedMir) (argVals : List Value) : Memory :=
  tailCalleeEntryMemory s.memory.callStack (frameTeardownMem s) (length s.frame.locals)
    (length (initLocals calleeBody argVals))

/-- The saved caller a tail callee returns into: the tail-caller's own saved caller, whose
unwind action a callee that cannot unwind narrows to `unreachable`
(`narrowCallStackForTailCallee`). Every other field is the tail-caller's. -/
def narrowCaller (caller : SavedCallerFrame) (canUnwind : Bool) : SavedCallerFrame :=
  match canUnwind with
  | true => caller
  | false => { caller with returnUnwind := .unreachable }

private theorem narrow_nil (b : Bool) : narrowCallStackForTailCallee [] b = [] := by
  cases b <;> rfl

private theorem narrow_cons (caller : SavedCallerFrame) (rest : List SavedCallerFrame)
    (b : Bool) :
    narrowCallStackForTailCallee (caller :: rest) b = narrowCaller caller b :: rest := by
  cases b <;> rfl

private theorem narrow_length (cs : List SavedCallerFrame) (b : Bool) :
    (narrowCallStackForTailCallee cs b).length = cs.length := by
  cases b <;> cases cs <;> rfl

/-- Relocating the root's caller-owned referents changes only the borrow table and
`callerLocals`. -/
private theorem relocate_preserves (mem : Memory) (nOld nNew : Nat) :
    (relocateRootCallerReferents mem nOld nNew).callStack = mem.callStack ∧
      (relocateRootCallerReferents mem nOld nNew).rootUnwindCeiling = mem.rootUnwindCeiling ∧
      (relocateRootCallerReferents mem nOld nNew).activeProtectors = mem.activeProtectors := by
  unfold relocateRootCallerReferents
  cases Nat.blt nOld nNew <;> cases hasAnyRootCallerReferent mem.borrows nOld <;>
    exact ⟨rfl, rfl, rfl⟩

private theorem tailEntryMem_of_nil (s : MachineState) (calleeBody : CapturedMir)
    (argVals : List Value) (hnil : s.memory.callStack = []) :
    tailEntryMem s calleeBody argVals =
      relocateRootCallerReferents (frameTeardownMem s) (length s.frame.locals)
        (length (initLocals calleeBody argVals)) := by
  simp only [tailEntryMem, hnil, tailCalleeEntryMemory_nil]

private theorem tailEntryMem_of_cons (s : MachineState) (calleeBody : CapturedMir)
    (argVals : List Value) {caller : SavedCallerFrame} {rest : List SavedCallerFrame}
    (hcs : s.memory.callStack = caller :: rest) :
    tailEntryMem s calleeBody argVals = frameTeardownMem s := by
  simp only [tailEntryMem, hcs, tailCalleeEntryMemory_cons]

private theorem tailEntryMem_callStack (s : MachineState) (calleeBody : CapturedMir)
    (argVals : List Value) :
    (tailEntryMem s calleeBody argVals).callStack = s.memory.callStack := by
  cases hcs : s.memory.callStack with
  | nil =>
    rw [tailEntryMem_of_nil s calleeBody argVals hcs]
    exact (relocate_preserves _ _ _).1.trans hcs
  | cons caller rest =>
    rw [tailEntryMem_of_cons s calleeBody argVals hcs]
    exact hcs

/-- The call stack on entry to a tail callee: the tail-caller's, with the inherited caller
frame's unwind action narrowed for a callee that cannot unwind. -/
private theorem enterTail_callStack (mem : Memory) (calleeBody : CapturedMir)
    (argVals : List Value) :
    (enterTailCalleeFrame mem calleeBody argVals).memory.callStack =
      narrowCallStackForTailCallee mem.callStack calleeBody.fnAbi.canUnwind :=
  rfl

/-- The callee operand of a tail call, as `resolveCallTarget` evaluates it in the tail-caller's
body (`evalOperandWithBodyCast`: the erased `evalOperand`, except that a moved place starting
with an opaque cast is evaluated against the body's declarations). -/
def evalTailFunc (s : MachineState) (callerBody : CapturedMir) (func : Operand) :
    PlaceReadResult :=
  evalOperandWithBodyCast s.frame.locals func s.memory.borrows s.memory.globals
    callerBody.layouts s.memory.callerLocals callerBody.localDecls s.memory.callStack

/-- The arguments of a tail call, evaluated in the tail-caller's body from the locals `l` left
by the callee operand (`evalOperandsWithBodyCast`). -/
def evalTailArgs (s : MachineState) (callerBody : CapturedMir) (l : List LocalSlot)
    (argOps : List Operand) : OperandsEvalResult :=
  evalOperandsWithBodyCast l argOps s.memory.borrows s.memory.globals callerBody.layouts
    s.memory.callerLocals callerBody.localDecls s.memory.callStack

private theorem evalTailFunc_fold (s : MachineState) (callerBody : CapturedMir)
    (func : Operand) :
    evalOperandWithBodyCast s.frame.locals func s.memory.borrows s.memory.globals
        callerBody.layouts s.memory.callerLocals callerBody.localDecls s.memory.callStack =
      evalTailFunc s callerBody func :=
  rfl

private theorem evalTailArgs_fold (s : MachineState) (callerBody : CapturedMir)
    (l : List LocalSlot) (argOps : List Operand) :
    evalOperandsWithBodyCast l argOps s.memory.borrows s.memory.globals callerBody.layouts
        s.memory.callerLocals callerBody.localDecls s.memory.callStack =
      evalTailArgs s callerBody l argOps :=
  rfl

/-- `return_` from a frame holding `retVal` in `_0`, in the vocabulary above: the teardown's
protector guard, the teardown, then the root halt or the write of the caller's destination in
the popped caller's memory. -/
private theorem evalTerminator_return_eq (st : MachineState) (retVal : Value) (span : String)
    (cb : Option CapturedMir) (h0 : get? st.frame.locals 0 = some (.init retVal)) :
    evalTerminator st ⟨.return_, span⟩ cb =
      match frameDeallocConflict st with
      | true => MirStepNode.fail .ub
      | false =>
        match st.memory.callStack with
        | [] =>
          match valueContainsUninit retVal with
          | true => MirStepNode.fail .ub
          | false => MirStepNode.retNormal retVal (frameTeardownMem st)
        | caller :: rest =>
          match caller.isDiverging with
          | true => MirStepNode.fail .ub
          | false =>
            match valueContainsUninit retVal with
            | true => MirStepNode.fail .ub
            | false =>
              match writeReturnDestination caller.frame.locals
                  (popCallerMem (frameTeardownMem st) caller rest) caller.destination retVal
                  caller.callerBody.localDecls caller.callerBody.layouts with
              | .ok upd mem' =>
                MirStepNode.step
                  { frame := { caller.frame with blockIdx := caller.returnTarget, stmtIdx := 0,
                                                 locals := upd }
                    memory := mem' }
              | .ub => MirStepNode.fail .ub
              | .unsupported => MirStepNode.unsupported := by
  unfold frameDeallocConflict
  simp only [evalTerminator, h0]
  rfl

/-- **Trusted direct in-table tail call (universal).** A direct `become f(args)` whose
callee has a linked body, once the arguments are evaluated (`evalOperandsWithBodyCast`: the
erased `evalOperands`, except that a moved place starting with an opaque cast is evaluated
against the body's declarations), runs the frame teardown's protector guard: if deallocating a
local of the tail-caller would remove a protected tag, the tail call is UB; otherwise it tears
the tail-caller's frame down (`frameTeardownMem`: every borrow of one of its locals is disabled
and marked dead), relocates the root's live caller-owned referents past the callee's frame
when the tail-caller is the modular root (`tailEntryMem`), and enters the callee at `bb0` with
the evaluated arguments, *replacing* the active frame: no `SavedCallerFrame` is pushed (the
depth is unchanged), the inherited caller frame only has its unwind action narrowed when the
callee cannot unwind (`narrowCallStackForTailCallee`), the moved-out argument locals of the
tail-caller are discarded with its frame, and under a saved caller every other `Memory`
component is untouched. -/
theorem tailCall_trusted_direct_enters_without_push
    (s : MachineState) (func : Operand) (argOps : List Operand) (span : String)
    (callerBody calleeBody : CapturedMir) (defPath : DefPath) (argVals : List Value)
    (locals' : List LocalSlot)
    (hfunc : extractCalleeDefPath? func = some defPath)
    (hargs : evalOperandsWithBodyCast s.frame.locals argOps s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals callerBody.localDecls s.memory.callStack =
        .ok argVals locals')
    (hfind : lookupCallee s.memory.callees callerBody.layouts defPath
      (extractCalleeTypeArgs func) s.memory.traitImpls = some calleeBody) :
    (frameDeallocConflict s = true →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) =
        MirStepNode.fail .ub) ∧
      (frameDeallocConflict s = false →
        evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) =
          MirStepNode.step
            (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals)) ∧
      (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
          ).memory.callStack =
        narrowCallStackForTailCallee s.memory.callStack calleeBody.fnAbi.canUnwind ∧
      (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
          ).memory.callStack.length = s.memory.callStack.length ∧
      (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
          ).memory.activeCallee = some calleeBody ∧
      (∀ (caller : SavedCallerFrame) (rest : List SavedCallerFrame),
        s.memory.callStack = caller :: rest →
        (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals).memory =
          { s.memory with
            borrows := disableFrameBorrows s.memory.borrows (length s.memory.callStack)
              (length s.frame.locals),
            callStack := narrowCaller caller calleeBody.fnAbi.canUnwind :: rest,
            activeCallee := some calleeBody }) ∧
      (s.memory.callStack = [] →
        tailEntryMem s calleeBody argVals =
          relocateRootCallerReferents (frameTeardownMem s) (length s.frame.locals)
            (length (initLocals calleeBody argVals))) ∧
      (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals).frame =
        { blockIdx := 0, stmtIdx := 0, locals := initLocals calleeBody argVals } := by
  have hstack := tailEntryMem_callStack s calleeBody argVals
  refine ⟨fun hc => ?_, fun hc => ?_, ?_, ?_, rfl, ?_, tailEntryMem_of_nil s calleeBody argVals,
    rfl⟩
  · simp only [frameDeallocConflict] at hc
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget, hfunc,
      hargs, hc]
  · simp only [frameDeallocConflict] at hc
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget, hfunc,
      hargs, hc, hfind, checkCalleeTargetCompatible_direct, frameTeardownMem, tailEntryMem]
  · rw [enterTail_callStack, hstack]
  · rw [enterTail_callStack, narrow_length, hstack]
  · intro caller rest hcs
    rw [tailEntryMem_of_cons s calleeBody argVals hcs]
    cases hb : calleeBody.fnAbi.canUnwind <;>
      simp only [enterTailCalleeFrame, frameTeardownMem, narrowCallStackForTailCallee,
        narrowCaller, hb, hcs]

/-- **Trusted tail call vs. call (universal contrast).** For the same callee and
arguments, a returning `call` pushes exactly one `SavedCallerFrame` (whose continuation is
`targetBb`) and keeps every borrow of the suspended caller, whereas `tailCall` leaves the
stack depth unchanged and tears the replaced frame down (`disableFrameBorrows`; at a modular
root the live caller-owned referents are then relocated, `tailEntryMem`); both enter the callee
in the same frame. -/
theorem tailCall_trusted_vs_call_depth
    (s : MachineState) (callerBody calleeBody : CapturedMir) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (argVals : List Value)
    (unwind : UnwindAction) :
    (pushCalleeFrame s callerBody locals' destination targetBb calleeBody argVals unwind
        ).memory.callStack.length = s.memory.callStack.length + 1 ∧
      (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
          ).memory.callStack.length = s.memory.callStack.length ∧
      (pushCalleeFrame s callerBody locals' destination targetBb calleeBody argVals unwind
        ).memory.borrows = s.memory.borrows ∧
      (∀ (caller : SavedCallerFrame) (rest : List SavedCallerFrame),
        s.memory.callStack = caller :: rest →
        (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
            ).memory.borrows =
          disableFrameBorrows s.memory.borrows (length s.memory.callStack)
            (length s.frame.locals)) ∧
      (frameTeardownMem s).borrows =
        disableFrameBorrows s.memory.borrows (length s.memory.callStack)
          (length s.frame.locals) ∧
      (pushCalleeFrame s callerBody locals' destination targetBb calleeBody argVals unwind).frame =
        (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals).frame := by
  refine ⟨by simp [pushCalleeFrame], ?_, rfl, ?_, rfl, rfl⟩
  · rw [enterTail_callStack, narrow_length, tailEntryMem_callStack]
  · intro caller rest hcs
    exact (congrArg (fun m => (enterTailCalleeFrame m calleeBody argVals).memory.borrows)
      (tailEntryMem_of_cons s calleeBody argVals hcs)).trans rfl

/-- A `return` of `retVal` into the saved caller `c` at the head of the call stack, in the
vocabulary of `evalTerminator_return_eq`. -/
private theorem return_into_caller (st : MachineState) (retVal : Value) (span : String)
    (cb : Option CapturedMir) (h0 : get? st.frame.locals 0 = some (.init retVal))
    (c : SavedCallerFrame) (rest : List SavedCallerFrame)
    (hcs : st.memory.callStack = c :: rest) :
    evalTerminator st ⟨.return_, span⟩ cb =
      match frameDeallocConflict st with
      | true => MirStepNode.fail .ub
      | false =>
        match c.isDiverging with
        | true => MirStepNode.fail .ub
        | false =>
          match valueContainsUninit retVal with
          | true => MirStepNode.fail .ub
          | false =>
            match writeReturnDestination c.frame.locals
                (popCallerMem (frameTeardownMem st) c rest) c.destination retVal
                c.callerBody.localDecls c.callerBody.layouts with
            | .ok upd mem' =>
              MirStepNode.step
                { frame := { c.frame with blockIdx := c.returnTarget, stmtIdx := 0,
                                          locals := upd }
                  memory := mem' }
            | .ub => MirStepNode.fail .ub
            | .unsupported => MirStepNode.unsupported := by
  rw [evalTerminator_return_eq st retVal span cb h0]
  simp only [hcs]

/-- **Trusted return-through (universal).** A `return` depends only on `_0`, on the number
of locals of the returning frame (the extent of its teardown), and on the memory — never on
the rest of the frame. Once the tail-callee (entered from any memory `mem`, in particular the
tail call's `tailEntryMem`, whose borrows into the replaced tail-caller frame are already
disabled) has produced `retVal`, its `return` runs the teardown's protector guard for its own
frame and, unless that is UB, tears its frame down too (`frameTeardownMem`) and then halts or
pops exactly as the tail-caller's own `return` of `retVal` would have: at the root it halts
with `retVal`; under a caller it pops the inherited saved caller `c` — the tail-caller's saved
caller, which a non-unwinding callee changed only in its unwind action (`narrowCaller`) —
writes `c.destination` (`writeReturnDestination`, in the popped caller's memory
`popCallerMem`) and resumes at `c.returnTarget` (the caller's caller of the original
tail-caller frame), restoring its protectors; into a diverging caller it is UB. -/
theorem tailCall_trusted_return_through
    (mem : Memory) (calleeBody : CapturedMir) (argVals : List Value) (f : StackFrame)
    (retVal : Value) (span : String) (cb : Option CapturedMir)
    (h0 : get? f.locals 0 = some (.init retVal)) :
    (∀ (f' : StackFrame) (span' : String) (cb' : Option CapturedMir),
        get? f'.locals 0 = some (.init retVal) → length f'.locals = length f.locals →
        evalTerminator ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩
            ⟨.return_, span⟩ cb =
          evalTerminator ⟨f', (enterTailCalleeFrame mem calleeBody argVals).memory⟩
            ⟨.return_, span'⟩ cb') ∧
      (frameDeallocConflict ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩ = false →
        mem.callStack = [] →
        valueContainsUninit retVal = false →
        evalTerminator ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩
            ⟨.return_, span⟩ cb =
          MirStepNode.retNormal retVal
            (frameTeardownMem ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩)) ∧
      (∀ (caller c : SavedCallerFrame) (rest : List SavedCallerFrame) (upd : List LocalSlot)
          (mem' : Memory),
        frameDeallocConflict ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩ = false →
        mem.callStack = caller :: rest →
        c = narrowCaller caller calleeBody.fnAbi.canUnwind →
        c.isDiverging = false →
        valueContainsUninit retVal = false →
        writeReturnDestination c.frame.locals
            (popCallerMem
              (frameTeardownMem ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩)
              c rest)
            c.destination retVal c.callerBody.localDecls c.callerBody.layouts =
          .ok upd mem' →
        evalTerminator ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩
            ⟨.return_, span⟩ cb =
          MirStepNode.step
            { frame := { c.frame with blockIdx := c.returnTarget, stmtIdx := 0, locals := upd }
              memory := mem' } ∧
        toMrStackFrame { c.frame with blockIdx := c.returnTarget, stmtIdx := 0, locals := upd } =
          MrStackFrame.jump_to_block (toMrStackFrame c.frame) c.returnTarget) ∧
      (∀ (caller : SavedCallerFrame) (b : Bool),
        (narrowCaller caller b).frame = caller.frame ∧
        (narrowCaller caller b).destination = caller.destination ∧
        (narrowCaller caller b).returnTarget = caller.returnTarget ∧
        (narrowCaller caller b).callerBody = caller.callerBody ∧
        (narrowCaller caller b).isDiverging = caller.isDiverging ∧
        restoreCallerProtectors (narrowCaller caller b) = restoreCallerProtectors caller ∧
        (narrowCaller caller b).returnUnwind =
          (match b with
           | true => caller.returnUnwind
           | false => .unreachable)) ∧
      (∀ (caller : SavedCallerFrame) (rest : List SavedCallerFrame),
        mem.callStack = caller :: rest → caller.isDiverging = true →
        evalTerminator ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩
            ⟨.return_, span⟩ cb = MirStepNode.fail .ub) ∧
      (valueContainsUninit retVal = true →
        evalTerminator ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩
            ⟨.return_, span⟩ cb = MirStepNode.fail .ub) := by
  have hcons : ∀ (caller : SavedCallerFrame) (rest : List SavedCallerFrame),
      mem.callStack = caller :: rest →
      (enterTailCalleeFrame mem calleeBody argVals).memory.callStack =
        narrowCaller caller calleeBody.fnAbi.canUnwind :: rest := by
    intro caller rest hcs
    rw [enterTail_callStack, hcs, narrow_cons]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f' span' cb' h0' hlen
    simp only [evalTerminator, h0, h0', hlen]
  · intro hc hnil hinit
    have hnil' : (enterTailCalleeFrame mem calleeBody argVals).memory.callStack = [] := by
      rw [enterTail_callStack, hnil, narrow_nil]
    rw [evalTerminator_return_eq _ retVal span cb h0, hc]
    simp only [hnil', hinit]
  · intro caller c rest upd mem' hc hcs hceq hdiv hinit hw
    subst hceq
    refine ⟨?_, rfl⟩
    rw [return_into_caller ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩ retVal span cb
      h0 _ rest (hcons caller rest hcs), hc]
    simp only [hdiv, hinit, hw]
  · intro caller b
    cases b <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro caller rest hcs hdiv
    have hdiv' : (narrowCaller caller calleeBody.fnAbi.canUnwind).isDiverging = true := by
      cases calleeBody.fnAbi.canUnwind <;> exact hdiv
    rw [return_into_caller ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩ retVal span cb
      h0 _ rest (hcons caller rest hcs)]
    split <;> simp only [hdiv']
  · intro huninit
    rw [evalTerminator_return_eq _ retVal span cb h0]
    cases frameDeallocConflict
        ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩ with
    | true => rfl
    | false =>
      cases (enterTailCalleeFrame mem calleeBody argVals).memory.callStack with
      | nil => simp only [huninit]
      | cons caller rest =>
        cases hdiv : caller.isDiverging <;> simp only [hdiv, huninit]

/-- **Trusted external tail call (universal).** A direct tail call to a callee without a
linked body runs the teardown's protector guard (UB on a conflict), tears the tail-caller's
frame down, and emits the external `MirCallReq` with the evaluated arguments and the
torn-down memory, resuming with `resumeExternalTailCallWithAbi`: the answer is resumed by
`resumeExternalTailCall` once the tail-caller's root unwind ceiling has been restored into the
answer memory (an external callee cannot raise it), and — a direct callee being a function
item, which may unwind (`externalTargetCanUnwind = some true`) — a panic of the callee unwinds
the caller stack, whereas a panic out of a callee whose ABI cannot unwind is UB. -/
theorem tailCall_trusted_external
    (s : MachineState) (func : Operand) (argOps : List Operand) (span : String)
    (callerBody : CapturedMir) (defPath : DefPath) (argVals : List Value)
    (locals' : List LocalSlot)
    (hfunc : extractCalleeDefPath? func = some defPath)
    (hargs : evalOperandsWithBodyCast s.frame.locals argOps s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals callerBody.localDecls s.memory.callStack =
        .ok argVals locals')
    (hnone : lookupCallee s.memory.callees callerBody.layouts defPath
      (extractCalleeTypeArgs func) s.memory.traitImpls = none) :
    (frameDeallocConflict s = true →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) =
        MirStepNode.fail .ub) ∧
      (frameDeallocConflict s = false →
        evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) =
          MirStepNode.extCall
            { defPath := defPath, typeArgs := extractCalleeTypeArgs func, args := argVals,
              memory := frameTeardownMem s }
            (resumeExternalTailCallWithAbi s.memory.rootUnwindCeiling (some true))) ∧
      (∀ (ceiling : Bool) (retVal : Value) (memAns : Memory),
        resumeExternalTailCallWithAbi ceiling (some true) (.returned retVal memAns) =
          resumeExternalTailCall
            (.returned retVal { memAns with rootUnwindCeiling := ceiling })) ∧
      (∀ (ceiling : Bool) (memAns : Memory),
        resumeExternalTailCallWithAbi ceiling (some true) (.panicked memAns) =
          resumeExternalTailCall (.panicked { memAns with rootUnwindCeiling := ceiling })) ∧
      (∀ (ceiling : Bool) (memAns : Memory),
        resumeExternalTailCallWithAbi ceiling (some false) (.panicked memAns) =
          .faulted .ub) ∧
      (∀ (ceiling : Bool) (extUnwind : Option Bool),
        resumeExternalTailCallWithAbi ceiling extUnwind .aborted = .halted .abort) := by
  refine ⟨fun hc => ?_, fun hc => ?_, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl⟩ <;>
    simp only [frameDeallocConflict] at hc <;>
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget, hfunc,
      hargs, hc, hnone, frameTeardownMem, externalTargetCanUnwind]

/-- The `MirExecState` a step node denotes (`tau`, `ret`, or a fault). -/
def nodeState : MirStepNode → Option MirExecState
  | .tau s => some s
  | .ret out => some (.halted out)
  | .vis (.inl (.fail k)) _ => some (.faulted k)
  | _ => none

/-- **Trusted external return-through (universal).** For every frame `f` holding `retVal` in
`_0` and every memory `memAfter`, a `return` from `f` is UB when the teardown of `f`'s locals
conflicts with an active protector, and is otherwise *exactly* the resumption of an external
tail-callee that returned `retVal` with the torn-down memory: the external callee, too,
returns straight into the caller's caller (halting at the root, UB into a diverging caller) —
its frame lives outside the machine, and the tail-caller's frame was torn down when the tail
call was issued (`tailCall_trusted_external`). Unwinding and aborting follow the caller stack
(`unwindFromCallStack`) and abort. -/
theorem tailCall_trusted_external_resume_is_return
    (retVal : Value) (memAfter : Memory) (f : StackFrame) (span : String)
    (cb : Option CapturedMir) (h0 : get? f.locals 0 = some (.init retVal)) :
    (frameDeallocConflict ⟨f, memAfter⟩ = true →
      nodeState (evalTerminator ⟨f, memAfter⟩ ⟨.return_, span⟩ cb) = some (.faulted .ub)) ∧
      (valueContainsUninit retVal = true →
        nodeState (evalTerminator ⟨f, memAfter⟩ ⟨.return_, span⟩ cb) = some (.faulted .ub)) ∧
      (frameDeallocConflict ⟨f, memAfter⟩ = false →
        valueContainsUninit retVal = false →
        some (resumeExternalTailCall (.returned retVal (frameTeardownMem ⟨f, memAfter⟩))) =
          nodeState (evalTerminator ⟨f, memAfter⟩ ⟨.return_, span⟩ cb)) ∧
      resumeExternalTailCall (.panicked memAfter) =
        unwindFromCallStack memAfter.callStack memAfter ∧
      resumeExternalTailCall .aborted = .halted .abort := by
  refine ⟨fun hc => ?_, fun huninit => ?_, fun hc hinit => ?_, rfl, rfl⟩
  · rw [evalTerminator_return_eq _ retVal span cb h0, hc]
    rfl
  · rw [evalTerminator_return_eq _ retVal span cb h0]
    cases frameDeallocConflict ⟨f, memAfter⟩ with
    | true => rfl
    | false =>
      cases memAfter.callStack with
      | nil => simp only [huninit]; rfl
      | cons caller rest =>
        cases hdiv : caller.isDiverging <;> simp only [hdiv, huninit] <;> rfl
  · rw [evalTerminator_return_eq _ retVal span cb h0, hc]
    have hcs : (frameTeardownMem ⟨f, memAfter⟩).callStack = memAfter.callStack := rfl
    simp only [resumeExternalTailCall, hcs, popCallerMem]
    rcases memAfter.callStack with _ | ⟨caller, rest⟩
    · simp only [hinit]; rfl
    · dsimp only
      cases caller.isDiverging
      · dsimp only
        simp only [hinit]
        split <;> rename_i heq <;> simp only [heq] <;> rfl
      · rfl

set_option linter.unusedSimpArgs false in
/-- **Trusted fail-closed tail calls (universal).** Every tail call whose callee or
arguments cannot be resolved faults with UB: a callee operand whose evaluation is UB or
yields a non-function value (a scalar, a non-unit aggregate, a pointer with a non-zero
offset, a pointer that is a stack borrow, an unregistered function pointer, or one whose
signature/arity/ABI is incompatible with the call site), a resolved callee whose linked
body is incompatible with the reified signature (`checkCalleeTargetCompatible`; UB as well
when the frame teardown's protector guard fires first), and an argument whose evaluation is
UB (e.g. moving a dead local). A zero-sized function-item operand (`.unit` of `FnDef` type)
resolves to its function, which the tail call enters after the frame teardown. -/
theorem tailCall_trusted_fail_closed_universal
    (s : MachineState) (func : Operand) (argOps : List Operand) (span : String)
    (callerBody : CapturedMir) (hnodirect : extractCalleeDefPath? func = none) :
    (evalTailFunc s callerBody func = .ub →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub) ∧
    (∀ (sc : ScalarInt) (l : List LocalSlot),
      evalTailFunc s callerBody func = .ok (.scalar sc) l →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub) ∧
    (∀ (vi : Nat) (v : Value) (vs : List Value) (l : List LocalSlot),
      evalTailFunc s callerBody func = .ok (.aggregate vi (v :: vs)) l →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub) ∧
    (∀ (p : ProvenancePtr) (sz : Nat) (l : List LocalSlot),
      evalTailFunc s callerBody func = .ok (.ptr p sz) l →
      (sz ≠ 8 ∨ p.offsetBytes ≠ 0 ∨ (lookupBorrow s.memory.borrows p.tag).isSome ∨
        lookupFnPtr s.memory.fnPtrs p.allocId = none) →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub) ∧
    (∀ (p : ProvenancePtr) (l : List LocalSlot) (fnEntry : FnPtrEntry),
      evalTailFunc s callerBody func = .ok (.ptr p 8) l →
      p.offsetBytes = 0 → lookupBorrow s.memory.borrows p.tag = none →
      lookupFnPtr s.memory.fnPtrs p.allocId = some fnEntry →
      fnEntryCompatibleWithCallSite fnEntry (length argOps)
          (operandTy callerBody.localDecls callerBody.layouts func) = false →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub) ∧
    (∀ (p : ProvenancePtr) (l : List LocalSlot) (fnEntry : FnPtrEntry) (argVals : List Value)
        (l' : List LocalSlot) (calleeBody : CapturedMir),
      evalTailFunc s callerBody func = .ok (.ptr p 8) l →
      p.offsetBytes = 0 → lookupBorrow s.memory.borrows p.tag = none →
      lookupFnPtr s.memory.fnPtrs p.allocId = some fnEntry →
      fnEntryCompatibleWithCallSite fnEntry (length argOps)
          (operandTy callerBody.localDecls callerBody.layouts func) = true →
      evalTailArgs s callerBody l argOps = .ok argVals l' →
      lookupCallee s.memory.callees callerBody.layouts fnEntry.defPath fnEntry.typeArgs
          s.memory.traitImpls = some calleeBody →
      checkCalleeTargetCompatible
          { defPath := fnEntry.defPath, typeArgs := fnEntry.typeArgs, fnSig := fnEntry.fnSig,
            isIndirect := true } calleeBody (length argVals) = false →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub) ∧
    (∀ (l : List LocalSlot) (dp : DefPath) (tys : List RigidTy),
      evalTailFunc s callerBody func = .ok .unit l →
      extractFnItemTarget? (operandTy callerBody.localDecls callerBody.layouts func) =
        some (dp, tys) →
      evalTailArgs s callerBody l argOps = .ub →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub) ∧
    (∀ (l : List LocalSlot) (dp : DefPath) (tys : List RigidTy) (argVals : List Value)
        (l' : List LocalSlot) (calleeBody : CapturedMir),
      evalTailFunc s callerBody func = .ok .unit l →
      extractFnItemTarget? (operandTy callerBody.localDecls callerBody.layouts func) =
        some (dp, tys) →
      evalTailArgs s callerBody l argOps = .ok argVals l' →
      lookupCallee s.memory.callees callerBody.layouts dp tys s.memory.traitImpls =
        some calleeBody →
      frameDeallocConflict s = false →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) =
        MirStepNode.step
          (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
      evalTailFunc_fold, evalTailArgs_fold, hnodirect, h]
  · intro sc l h
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
      evalTailFunc_fold, evalTailArgs_fold, hnodirect, h]
  · intro vi v vs l h
    cases vi <;>
      simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
        evalTailFunc_fold, evalTailArgs_fold, hnodirect, h]
  · intro p sz l h hbad
    rcases hbad with hsz' | hoff' | hbor' | hnone
    · have hb : Nat.beq sz 8 = false :=
        Bool.eq_false_iff.mpr (fun hh => hsz' (Nat.eq_of_beq_eq_true hh))
      simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
        evalTailFunc_fold, evalTailArgs_fold, hnodirect, h, hb, Bool.false_and]
    · have ho : Nat.beq p.offsetBytes 0 = false :=
        Bool.eq_false_iff.mpr (fun hh => hoff' (Nat.eq_of_beq_eq_true hh))
      simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
        evalTailFunc_fold, evalTailArgs_fold, hnodirect, h, ho, Bool.false_and, Bool.and_false]
    · obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hbor'
      simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
        evalTailFunc_fold, evalTailArgs_fold, hnodirect, h, he, Bool.and_false]
    · rcases Bool.eq_false_or_eq_true (Nat.beq sz 8) with hb | hb <;>
        rcases Bool.eq_false_or_eq_true (Nat.beq p.offsetBytes 0) with ho | ho <;>
        cases hl : lookupBorrow s.memory.borrows p.tag <;>
        simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
          evalTailFunc_fold, evalTailArgs_fold, hnodirect, h, hb, ho, hl, hnone, Bool.and_true,
          Bool.and_false]
  · intro p l fnEntry h hoff hbor hfn hcompat
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
      evalTailFunc_fold, evalTailArgs_fold, hnodirect, h, hoff, hbor, hfn, hcompat, Nat.beq_refl,
      Bool.and_self]
  · intro p l fnEntry argVals l' calleeBody h hoff hbor hfn hcompat hargs hfind hbody
    cases hc : hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
        (length s.memory.callStack) (length s.frame.locals) <;>
      simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
        evalTailFunc_fold, evalTailArgs_fold, hnodirect, h, hoff, hbor, hfn, hcompat, Nat.beq_refl,
        Bool.and_self, hargs, hc, hfind, hbody]
  · intro l dp tys h hfi hargs
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
      evalTailFunc_fold, evalTailArgs_fold, hnodirect, h, hfi, hargs]
  · intro l dp tys argVals l' calleeBody h hfi hargs hfind hc
    simp only [frameDeallocConflict] at hc
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
      evalTailFunc_fold, evalTailArgs_fold, hnodirect, h, hfi, hargs, hc, hfind,
      checkCalleeTargetCompatible_direct, frameTeardownMem, tailEntryMem]

set_option linter.unusedSimpArgs false in
/-- **Trusted non-function callees (universal).** Whatever a non-direct callee operand
evaluates to, if it is not a pointer and not a zero-sized value of function-item type
(`extractFnItemTarget? = none`), the tail call is UB — scalars, unit, and every aggregate
(including a zero-sized `.aggregate 0 []` of non-function type). -/
theorem tailCall_trusted_non_function_value_ub
    (s : MachineState) (func : Operand) (argOps : List Operand) (span : String)
    (callerBody : CapturedMir) (hnodirect : extractCalleeDefPath? func = none)
    (v : Value) (l : List LocalSlot)
    (h : evalTailFunc s callerBody func = .ok v l)
    (hnp : ∀ p sz, v ≠ .ptr p sz)
    (hfi : extractFnItemTarget? (operandTy callerBody.localDecls callerBody.layouts func) = none) :
    evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub := by
  cases v with
  | unit =>
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
      evalTailFunc_fold, evalTailArgs_fold, hnodirect, h, hfi]
  | uninit =>
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
      evalTailFunc_fold, evalTailArgs_fold, hnodirect, h]
  | scalar sc =>
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
      evalTailFunc_fold, evalTailArgs_fold, hnodirect, h]
  | ptr p sz => exact absurd rfl (hnp p sz)
  | aggregate vi fs =>
    cases vi <;> cases fs <;>
      simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
        evalTailFunc_fold, evalTailArgs_fold, hnodirect, h, hfi]

/-- `disableFramesAbove k` already disables every borrow of a frame deeper than `k`, so a
prior teardown of such a frame is invisible to it. -/
private theorem disableFramesAbove_disableFrameBorrows (d n k : Nat) (hk : k < d) :
    ∀ bs : List BorrowEntry,
      disableFramesAbove (disableFrameBorrows bs d n) k = disableFramesAbove bs k
  | [] => rfl
  | e :: rest => by
    have ih := disableFramesAbove_disableFrameBorrows d n k hk rest
    cases h : Bool.and (Nat.beq e.targetFrameDepth d) (Nat.blt e.targetLocal n) with
    | true =>
      have hd : e.targetFrameDepth = d := by
        simp only [Bool.and_eq_true] at h
        exact Nat.eq_of_beq_eq_true h.1
      have hkd : Nat.blt k e.targetFrameDepth = true := by
        rw [hd]
        exact Nat.blt_eq.mpr hk
      simp only [disableFrameBorrows, h, disableFramesAbove, hkd, ih]
    | false =>
      simp only [disableFrameBorrows, h, disableFramesAbove, ih]

/-- Unwinding from a call stack no deeper than `d` cannot observe a teardown of the frame at
depth `d` (nor the active body): every caller that catches the unwind disables the frames
above it. -/
private theorem unwindFromCallStack_teardown (d n : Nat) :
    ∀ (cs : List SavedCallerFrame) (mem : Memory) (ac : Option CapturedMir), cs.length ≤ d →
      unwindFromCallStack cs
          { mem with borrows := disableFrameBorrows mem.borrows d n, activeCallee := ac } =
        unwindFromCallStack cs mem
  | [], _, _, _ => rfl
  | caller :: rest, mem, ac, hlen => by
    have hlt : length rest < d := by
      simp only [List.length_cons] at hlen
      simp only [length]
      omega
    have ih := unwindFromCallStack_teardown d n rest (popCallerMem mem caller rest)
      (some caller.callerBody) (by simp only [List.length_cons] at hlen; omega)
    cases hu : caller.returnUnwind with
    | unreachable => simp only [unwindFromCallStack, hu]
    | terminate => simp only [unwindFromCallStack, hu]
    | continue_ =>
      simp only [unwindFromCallStack, hu]
      exact ih
    | cleanup bb =>
      simp only [unwindFromCallStack, hu, disableFramesAbove_disableFrameBorrows d n _ hlt]

/-- `UnwindResume` depends only on the memory: two frames whose memories unwind alike take the
same step. -/
private theorem unwindResume_congr (f f' : StackFrame) (mem mem' : Memory)
    (span span' : String) (cb cb' : Option CapturedMir)
    (h : unwindFromCallStack mem.callStack mem = unwindFromCallStack mem'.callStack mem') :
    evalTerminator ⟨f, mem⟩ ⟨.unwindResume, span⟩ cb =
      evalTerminator ⟨f', mem'⟩ ⟨.unwindResume, span'⟩ cb' := by
  simp only [evalTerminator, h]

/-- `UnwindResume` is UB whenever unwinding the call stack is. -/
private theorem unwindResume_ub (f : StackFrame) (mem : Memory) (span : String)
    (cb : Option CapturedMir)
    (h : unwindFromCallStack mem.callStack mem = .faulted .ub) :
    evalTerminator ⟨f, mem⟩ ⟨.unwindResume, span⟩ cb = MirStepNode.fail .ub := by
  simp only [evalTerminator, h]

/-- An unwind that reaches the root reads only the root unwind ceiling. -/
private theorem unwind_nil_eq (m m' : Memory)
    (h : m.rootUnwindCeiling = m'.rootUnwindCeiling) :
    unwindFromCallStack [] m = unwindFromCallStack [] m' := by
  simp only [unwindFromCallStack, h]

/-- Unwinding out of a tail-callee that **cannot unwind** is UB at every depth: under a
caller the inherited unwind action was narrowed to `unreachable`, and at the modular root the
root unwind ceiling was lowered. -/
private theorem unwind_enterTail_nounwind (mem : Memory) (calleeBody : CapturedMir)
    (argVals : List Value) (hb : calleeBody.fnAbi.canUnwind = false) :
    unwindFromCallStack (enterTailCalleeFrame mem calleeBody argVals).memory.callStack
        (enterTailCalleeFrame mem calleeBody argVals).memory = .faulted .ub := by
  cases hcs : mem.callStack with
  | nil =>
    simp only [enterTailCalleeFrame, narrowCallStackForTailCallee, hb, hcs, unwindFromCallStack]
  | cons caller rest =>
    simp only [enterTailCalleeFrame, narrowCallStackForTailCallee, hb, hcs, unwindFromCallStack]

/-- Unwinding out of a tail-callee that **can unwind** is the unwind of the tail-caller: the
call stack and the root unwind ceiling are inherited unchanged, the frame teardown is invisible
to every catching caller, and the root relocation touches neither. -/
private theorem unwind_enterTail_canUnwind (s : MachineState) (calleeBody : CapturedMir)
    (argVals : List Value) (hb : calleeBody.fnAbi.canUnwind = true) :
    unwindFromCallStack
        (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
          ).memory.callStack
        (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals).memory =
      unwindFromCallStack s.memory.callStack s.memory := by
  have key := unwindFromCallStack_teardown (length s.memory.callStack) (length s.frame.locals)
    s.memory.callStack s.memory (some calleeBody) (Nat.le_refl _)
  rw [enterTailCalleeFrame_of_canUnwind _ calleeBody argVals hb]
  by_cases hnil : s.memory.callStack = []
  · have hcs' : (tailEntryMem s calleeBody argVals).callStack = [] :=
      (tailEntryMem_callStack s calleeBody argVals).trans hnil
    have hceil : (tailEntryMem s calleeBody argVals).rootUnwindCeiling =
        s.memory.rootUnwindCeiling := by
      rw [tailEntryMem_of_nil s calleeBody argVals hnil]
      exact (relocate_preserves _ _ _).2.1
    show unwindFromCallStack (tailEntryMem s calleeBody argVals).callStack
        { tailEntryMem s calleeBody argVals with activeCallee := some calleeBody } =
      unwindFromCallStack s.memory.callStack s.memory
    rw [hcs', hnil]
    exact unwind_nil_eq _ _ hceil
  · obtain ⟨caller, rest, hcs⟩ := List.exists_cons_of_ne_nil hnil
    rw [tailEntryMem_of_cons s calleeBody argVals hcs]
    exact key

/-- **Trusted unwind-through (universal).** Unwinding (`UnwindResume`) out of the tail-callee
depends only on the memory. For a callee that **can unwind**, the tail call changed that memory
only in the active body, in the teardown of the replaced tail-caller frame, and (at a modular
root) in the relocation of the caller-owned referents — and unwinding observes none of them: a
caller that catches the unwind disables every frame above it (`disableFramesAbove`), the
tail-caller's included, and a root unwind reads only the root unwind ceiling. So it is
*exactly* the unwind the tail-caller would have performed: it pops into the caller's caller
with the original call's `returnUnwind` action. For a callee that **cannot unwind**
(`calleeBody.fnAbi.canUnwind = false`), entered from *any* memory, the unwind is UB at every
depth — the inherited unwind action was narrowed to `unreachable`
(`narrowCallStackForTailCallee`) and the root unwind ceiling lowered — exactly Miri's
"unwinding past a frame that does not allow unwinding". -/
theorem tailCall_trusted_unwind_through (s : MachineState) (calleeBody : CapturedMir)
    (argVals : List Value) (f f' : StackFrame) (span span' : String)
    (cb cb' : Option CapturedMir) :
    evalTerminator
        ⟨f, (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals).memory⟩
        ⟨.unwindResume, span⟩ cb =
      evalTerminator
        ⟨f', (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals).memory⟩
        ⟨.unwindResume, span'⟩ cb' ∧
    (calleeBody.fnAbi.canUnwind = true →
      evalTerminator
          ⟨f, (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
            ).memory⟩
          ⟨.unwindResume, span⟩ cb =
        evalTerminator s ⟨.unwindResume, span'⟩ cb' ∧
      evalTerminator
          ⟨f, (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
            ).memory⟩
          ⟨.unwindResume, span⟩ cb =
        match unwindFromCallStack s.memory.callStack s.memory with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) ∧
    (calleeBody.fnAbi.canUnwind = false →
      ∀ mem : Memory,
        evalTerminator ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩
          ⟨.unwindResume, span⟩ cb = MirStepNode.fail .ub) := by
  refine ⟨rfl, fun hb => ?_, fun hb mem => ?_⟩
  · have h2 : evalTerminator
          ⟨f, (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
            ).memory⟩
          ⟨.unwindResume, span⟩ cb =
        evalTerminator s ⟨.unwindResume, span'⟩ cb' :=
      unwindResume_congr f s.frame _ s.memory span span' cb cb'
        (unwind_enterTail_canUnwind s calleeBody argVals hb)
    exact ⟨h2, h2⟩
  · exact unwindResume_ub f _ span cb (unwind_enterTail_nounwind mem calleeBody argVals hb)

set_option linter.unusedSimpArgs false in
/-- **Trusted direct-call, `.unsupported`, and teardown-guard fail-closed paths
(universal).** Complementing `tailCall_trusted_fail_closed_universal` (which covered
non-direct `func`), a direct tail call (`extractCalleeDefPath? func = some defPath`) whose
argument evaluation is `.ub` or `.unsupported` fails closed with `MirStepNode.fail .ub` or
`MirStepNode.unsupported`; an indirect tail call whose callee operand evaluation is
`.unsupported` fails closed with `MirStepNode.unsupported`; an indirect tail call through a
valid function pointer whose argument evaluation is `.ub` or `.unsupported` fails closed; a
zero-sized `.aggregate 0 []` function-item callee resolves to its target just like `.unit`;
and for *every* callee operand, once the target resolves and the arguments evaluate, a frame
teardown that would deallocate a protected local of the tail-caller
(`frameDeallocConflict`) is UB — before the callee is looked up. -/
theorem tailCall_trusted_direct_and_unsupported_fail_closed
    (s : MachineState) (func : Operand) (argOps : List Operand) (span : String)
    (callerBody : CapturedMir) :
    (∀ defPath : DefPath, extractCalleeDefPath? func = some defPath →
      evalTailArgs s callerBody s.frame.locals argOps = .ub →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub) ∧
    (∀ defPath : DefPath, extractCalleeDefPath? func = some defPath →
      evalTailArgs s callerBody s.frame.locals argOps =
        .unsupported →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.unsupported) ∧
    (extractCalleeDefPath? func = none →
      evalTailFunc s callerBody func = .unsupported →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.unsupported) ∧
    (∀ (p : ProvenancePtr) (l : List LocalSlot) (fnEntry : FnPtrEntry),
      extractCalleeDefPath? func = none →
      evalTailFunc s callerBody func = .ok (.ptr p 8) l →
      p.offsetBytes = 0 → lookupBorrow s.memory.borrows p.tag = none →
      lookupFnPtr s.memory.fnPtrs p.allocId = some fnEntry →
      fnEntryCompatibleWithCallSite fnEntry (length argOps)
          (operandTy callerBody.localDecls callerBody.layouts func) = true →
      (evalTailArgs s callerBody l argOps = .ub →
        evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub) ∧
      (evalTailArgs s callerBody l argOps = .unsupported →
        evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) =
          MirStepNode.unsupported)) ∧
    (∀ (l : List LocalSlot) (dp : DefPath) (tys : List RigidTy) (argVals : List Value)
        (l' : List LocalSlot) (calleeBody : CapturedMir),
      extractCalleeDefPath? func = none →
      evalTailFunc s callerBody func = .ok (.aggregate 0 []) l →
      extractFnItemTarget? (operandTy callerBody.localDecls callerBody.layouts func) =
        some (dp, tys) →
      evalTailArgs s callerBody l argOps = .ok argVals l' →
      lookupCallee s.memory.callees callerBody.layouts dp tys s.memory.traitImpls =
        some calleeBody →
      frameDeallocConflict s = false →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) =
        MirStepNode.step
          (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals)) ∧
    (∀ (target : ResolvedCallTarget) (l : List LocalSlot) (argVals : List Value)
        (l' : List LocalSlot),
      resolveCallTarget s func (length argOps) callerBody.localDecls callerBody.layouts =
        .ok target l →
      evalTailArgs s callerBody l argOps = .ok argVals l' →
      frameDeallocConflict s = true →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) =
        MirStepNode.fail .ub) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro defPath hfunc hargs
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
      evalTailFunc_fold, evalTailArgs_fold, hfunc, hargs]
  · intro defPath hfunc hargs
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
      evalTailFunc_fold, evalTailArgs_fold, hfunc, hargs]
  · intro hnodirect hfunc
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
      evalTailFunc_fold, evalTailArgs_fold, hnodirect, hfunc]
  · intro p l fnEntry hnodirect h hoff hbor hfn hcompat
    refine ⟨?_, ?_⟩ <;> intro hargs <;>
      simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
        evalTailFunc_fold, evalTailArgs_fold, hnodirect, h, hoff, hbor, hfn, hcompat, Nat.beq_refl,
        Bool.and_self, hargs]
  · intro l dp tys argVals l' calleeBody hnodirect h hfi hargs hfind hc
    simp only [frameDeallocConflict] at hc
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
      evalTailFunc_fold, evalTailArgs_fold, hnodirect, h, hfi, hargs, hc, hfind,
      checkCalleeTargetCompatible_direct, frameTeardownMem, tailEntryMem]
  · intro target l argVals l' hres hargs hc
    simp only [frameDeallocConflict] at hc
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, evalTailArgs_fold, hres,
      hargs, hc]

/-- **Trusted return-through fail-closed paths (universal).** When the tail-callee (entered
from any memory `mem`) executes `.return_`, an uninitialized, dead, or missing `_0` slot faults
with `.ub`; with `_0` initialized to `retVal`, a teardown that would deallocate a protected
local of the tail-callee's frame (`frameDeallocConflict`) faults with `.ub`; and under a
non-diverging inherited caller `c` (the tail-caller's saved caller, `narrowCaller`), a
destination write (`writeReturnDestination` into the popped caller) that faults with `.ub` or
`.unsupported` fails closed — on the in-table return (after the tail-callee frame's teardown)
and on the return of *every* external tail-callee (`resumeExternalTailCall`, whose frame
teardown happened when the tail call was issued). -/
theorem tailCall_trusted_return_through_fail_closed
    (mem : Memory) (calleeBody : CapturedMir) (argVals : List Value) (f : StackFrame)
    (retVal : Value) (span : String) (cb : Option CapturedMir) :
    ((get? f.locals 0 = some .uninit ∨ get? f.locals 0 = some .dead ∨ get? f.locals 0 = none) →
      evalTerminator ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩
          ⟨.return_, span⟩ cb = MirStepNode.fail .ub) ∧
    (get? f.locals 0 = some (.init retVal) →
      frameDeallocConflict ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩ = true →
      evalTerminator ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩
          ⟨.return_, span⟩ cb = MirStepNode.fail .ub) ∧
    (∀ (caller c : SavedCallerFrame) (rest : List SavedCallerFrame),
      get? f.locals 0 = some (.init retVal) →
      mem.callStack = caller :: rest →
      c = narrowCaller caller calleeBody.fnAbi.canUnwind →
      c.isDiverging = false →
      writeReturnDestination c.frame.locals
          (popCallerMem
            (frameTeardownMem ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩)
            c rest)
          c.destination retVal c.callerBody.localDecls c.callerBody.layouts =
        .ub →
      evalTerminator ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩
          ⟨.return_, span⟩ cb = MirStepNode.fail .ub) ∧
    (∀ (caller c : SavedCallerFrame) (rest : List SavedCallerFrame),
      get? f.locals 0 = some (.init retVal) →
      frameDeallocConflict ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩ = false →
      mem.callStack = caller :: rest →
      c = narrowCaller caller calleeBody.fnAbi.canUnwind →
      c.isDiverging = false →
      valueContainsUninit retVal = false →
      writeReturnDestination c.frame.locals
          (popCallerMem
            (frameTeardownMem ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩)
            c rest)
          c.destination retVal c.callerBody.localDecls c.callerBody.layouts =
        .unsupported →
      evalTerminator ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩
          ⟨.return_, span⟩ cb = MirStepNode.unsupported) ∧
    (get? f.locals 0 = some (.init retVal) →
      valueContainsUninit retVal = true →
      evalTerminator ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩
          ⟨.return_, span⟩ cb = MirStepNode.fail .ub) ∧
    (∀ (memAfter : Memory) (caller : SavedCallerFrame) (rest : List SavedCallerFrame),
      memAfter.callStack = caller :: rest → caller.isDiverging = false →
      (writeReturnDestination caller.frame.locals (popCallerMem memAfter caller rest)
          caller.destination retVal caller.callerBody.localDecls caller.callerBody.layouts =
          .ub →
        resumeExternalTailCall (.returned retVal memAfter) = .faulted .ub) ∧
      (writeReturnDestination caller.frame.locals (popCallerMem memAfter caller rest)
          caller.destination retVal caller.callerBody.localDecls caller.callerBody.layouts =
          .unsupported →
        resumeExternalTailCall (.returned retVal memAfter) = .faulted .unsupported)) := by
  have hcons : ∀ (caller : SavedCallerFrame) (rest : List SavedCallerFrame),
      mem.callStack = caller :: rest →
      (enterTailCalleeFrame mem calleeBody argVals).memory.callStack =
        narrowCaller caller calleeBody.fnAbi.canUnwind :: rest := by
    intro caller rest hcs
    rw [enterTail_callStack, hcs, narrow_cons]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (h0 | h0 | h0) <;> simp only [evalTerminator, h0]
  · intro h0 hc
    rw [evalTerminator_return_eq _ retVal span cb h0, hc]
  · intro caller c rest h0 hcs hceq hdiv hw
    subst hceq
    rw [return_into_caller ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩ retVal span cb
      h0 _ rest (hcons caller rest hcs)]
    cases frameDeallocConflict
        ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩ with
    | true => rfl
    | false =>
      simp only [hdiv]
      cases valueContainsUninit retVal <;> simp only [hw]
  · intro caller c rest h0 hc hcs hceq hdiv hinit hw
    subst hceq
    rw [return_into_caller ⟨f, (enterTailCalleeFrame mem calleeBody argVals).memory⟩ retVal span cb
      h0 _ rest (hcons caller rest hcs), hc]
    simp only [hdiv, hinit, hw]
  · intro h0 huninit
    exact (tailCall_trusted_return_through mem calleeBody argVals f retVal span cb h0).2.2.2.2.2
      huninit
  · intro memAfter caller rest hcs hdiv
    simp only [popCallerMem]
    refine ⟨fun hw => ?_, fun hw => ?_⟩ <;>
      simp only [resumeExternalTailCall, hcs, hdiv, hw]

/-- A body whose block ends in a terminator rejected by `MiniRustSpec`'s fragment check is
not in the `MiniRustSpec` fragment. -/
private theorem inFragment_false_of_term {body : CapturedMir} {bb : BasicBlockData}
    (hbb : bb ∈ body.basicBlocks)
    (hbad : MiniRustSpec.Correspondence.terminatorOk body.layouts body.localDecls
      body.basicBlocks.length bb.terminator = false) :
    MiniRustSpec.Correspondence.inFragment body = false := by
  cases h : MiniRustSpec.Correspondence.inFragment body with
  | false => rfl
  | true =>
    exfalso
    simp only [MiniRustSpec.Correspondence.inFragment, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hbbs⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
    obtain ⟨_, ht⟩ := hbbs bb hbb
    rw [ht] at hbad
    exact Bool.noConfusion hbad

/-- **MiniRust (universal).** MiniRust has no tail calls and upstream `minimize` aborts on
`TerminatorKind::TailCall` (`span_bug!`, anchored above). The `MiniRustSpec`
transcription is fail-closed (no translation, fragment rejection for every block and
body ending in a tail call), while the `Generated.Ops` side pins the pieces a tail call
reuses: callee resolution is MiniRust's first-match `mrFindCalleeById`, and a return out of
the tail-callee resumes the caller's caller via `MrStackFrame.jump_to_block`
(`tailCall_trusted_return_through`). -/
theorem tailCall_minirust_corresponds (layouts : LayoutTable) (decls : List LocalDecl)
    (nblocks : Nat) (func : Operand) (argOps : List Operand) (span : String) :
    MiniRustSpec.Correspondence.translateTerminator layouts decls
        ⟨.tailCall func argOps, span⟩ = none ∧
      MiniRustSpec.Correspondence.terminatorOk layouts decls nblocks
        ⟨.tailCall func argOps, span⟩ = false ∧
      (∀ bb : BasicBlockData, bb.terminator.kind = .tailCall func argOps →
        MiniRustSpec.Correspondence.translateBlock layouts decls bb = none) ∧
      (∀ (body : CapturedMir) (bb : BasicBlockData), bb ∈ body.basicBlocks →
        bb.terminator.kind = .tailCall func argOps →
        MiniRustSpec.Correspondence.inFragment body = false) ∧
      (∀ (callee : CapturedMir) (rest : List CapturedMir),
        findCallee? (callee :: rest) callee.defPath = some callee ∧
        mrFindCalleeById ((callee.defPath, callee) :: rest.map fun b => (b.defPath, b))
          callee.defPath = some callee) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro bb hk
    have ht : MiniRustSpec.Correspondence.translateTerminator layouts decls bb.terminator =
        none := by
      simp [MiniRustSpec.Correspondence.translateTerminator, hk]
    simp only [MiniRustSpec.Correspondence.translateBlock, ht]
    cases bb.statements.mapM (fun x => MiniRustSpec.Correspondence.translateStatement decls x
      layouts) <;> rfl
  · intro body bb hbb hk
    exact inFragment_false_of_term hbb (by simp [MiniRustSpec.Correspondence.terminatorOk, hk])
  · intro callee rest
    exact ⟨(Correspondence.V2026_06_01.L5_ControlAndCalls.mir_findCallee_corresponds
        (callee :: rest) callee.defPath).2.1 callee rest rfl,
      (Correspondence.V2026_06_01.L5_ControlAndCalls.mir_findCallee_corresponds
        (callee :: rest) callee.defPath).2.2.1 callee _ rfl⟩

/-! ### LeanMiri stack-shape lockstep -/

/-- The LeanMiri return continuation of a Trusted saved caller frame: a returning call
resumes at `returnTarget`; a diverging call (`isDiverging`) has no return block. -/
def contOfCaller (caller : SavedCallerFrame) : LeanMiri.ReturnContinuation UnwindAction :=
  .goto (if caller.isDiverging then none else some caller.returnTarget) caller.returnUnwind

/-- **Stack-shape correspondence.** The LeanMiri frames (bottom … active) carry the return
continuations `rootCont :: reverse (callStack.map contOfCaller)`: frame `k` returns into the
saved caller recorded above it, and the bottom frame returns per `rootCont` (`stop` for a
whole-program root, `goto` for a modularly verified function with an external caller). -/
def StackShapeRel {B P M : Type} (rootCont : LeanMiri.ReturnContinuation UnwindAction)
    (cs : List SavedCallerFrame) (m : LeanMiri.StepState B P UnwindAction M) : Prop :=
  m.frames.map (·.returnContinuation) = rootCont :: (cs.map contOfCaller).reverse

/-- The return continuation of the active frame. -/
def activeCont (rootCont : LeanMiri.ReturnContinuation UnwindAction) :
    List SavedCallerFrame → LeanMiri.ReturnContinuation UnwindAction
  | [] => rootCont
  | caller :: _ => contOfCaller caller

/-- Miri's narrowing of an inherited return continuation for a tail callee whose ABI cannot
unwind (`Call.lean`: `| .goto ret _ => .goto ret .Unreachable`, anchored above); a callee that
can unwind inherits the continuation unchanged. -/
def narrowCont (canUnwind : Bool) :
    LeanMiri.ReturnContinuation UnwindAction → LeanMiri.ReturnContinuation UnwindAction
  | .goto ret u =>
    .goto ret
      (match canUnwind with
       | true => u
       | false => .unreachable)
  | .stop cleanup => .stop cleanup

/-- The `nounwindAs` oracle of a tail call into a callee with the given `canUnwind` ABI bit:
Miri replaces the inherited unwind action by `Unreachable` exactly when the callee cannot
unwind. -/
def nounwindOracle (canUnwind : Bool) : Option UnwindAction :=
  match canUnwind with
  | true => none
  | false => some .unreachable

/-- The root continuation after a tail call: a tail call made *by the root frame* (`cs = []`)
replaces the bottom LeanMiri frame, whose inherited continuation is narrowed like any other
(Trusted records that narrowing in `Memory.rootUnwindCeiling`); under a caller the bottom
frame is untouched. -/
def tailRootCont (rootCont : LeanMiri.ReturnContinuation UnwindAction)
    (cs : List SavedCallerFrame) (canUnwind : Bool) :
    LeanMiri.ReturnContinuation UnwindAction :=
  match cs with
  | [] => narrowCont canUnwind rootCont
  | _ :: _ => rootCont

private theorem contOfCaller_narrow (caller : SavedCallerFrame) (b : Bool) :
    contOfCaller (narrowCaller caller b) = narrowCont b (contOfCaller caller) := by
  cases b <;> rfl

private theorem passArgsError_all_ok (compat : Nat → Bool) (argCount : Nat) :
    ∀ (k i : Nat), i + k ≤ argCount → (∀ x, i ≤ x → x < i + k → compat x = true) →
      LeanMiri.passArgsError compat argCount i k = none
  | 0, _, _, _ => rfl
  | k + 1, i, hle, hc => by
    have hlt : ¬ argCount ≤ i := by omega
    have hci : compat i = true := hc i (Nat.le_refl i) (by omega)
    simp only [LeanMiri.passArgsError, hlt, ite_false, hci, Bool.not_true]
    exact passArgsError_all_ok compat argCount k (i + 1) (by omega)
      (fun x hx1 hx2 => hc x (by omega) (by omega))

private theorem passArgsError_fewer (argCount : Nat) :
    ∀ (k i : Nat), i ≤ argCount → argCount < i + k →
      LeanMiri.passArgsError (fun _ => true) argCount i k =
        some (.undefinedBehavior "calling a function with fewer arguments than it requires")
  | 0, _, h1, h2 => absurd h2 (by omega)
  | k + 1, i, h1, h2 => by
    by_cases heq : argCount ≤ i
    · simp only [LeanMiri.passArgsError, heq, ite_true]
    · simp only [LeanMiri.passArgsError, heq, ite_false, Bool.not_true]
      exact passArgsError_fewer argCount k (i + 1) (by omega) (by omega)

private theorem passArgsError_first_mismatch (compat : Nat → Bool) (argCount j : Nat)
    (hj : j < argCount) (hbad : compat j = false) :
    ∀ (k i : Nat), i ≤ j → j < i + k → (∀ x, i ≤ x → x < j → compat x = true) →
      LeanMiri.passArgsError compat argCount i k =
        some (.undefinedBehavior s!"AbiMismatchArgument {j}")
  | 0, _, h1, h2, _ => absurd h2 (by omega)
  | k + 1, i, h1, h2, hc => by
    have hlt : ¬ argCount ≤ i := by omega
    by_cases hij : i = j
    · subst hij
      simp only [LeanMiri.passArgsError, hlt, ite_false, hbad, Bool.not_false, ite_true]
    · have hci : compat i = true := hc i (Nat.le_refl i) (by omega)
      simp only [LeanMiri.passArgsError, hlt, ite_false, hci, Bool.not_true]
      exact passArgsError_first_mismatch compat argCount j hj hbad k (i + 1) (by omega) (by omega)
        (fun x hx1 hx2 => hc x (by omega) hx2)

private theorem shape_last {B P M : Type} {rootCont : LeanMiri.ReturnContinuation UnwindAction}
    {cs : List SavedCallerFrame} {m : LeanMiri.StepState B P UnwindAction M}
    (h : StackShapeRel rootCont cs m) :
    ∃ init last, m.frames = init ++ [last] ∧
      last.returnContinuation = activeCont rootCont cs ∧
      init.map (·.returnContinuation) ++ [activeCont rootCont cs] =
        rootCont :: (cs.map contOfCaller).reverse := by
  unfold StackShapeRel at h
  rcases List.eq_nil_or_concat m.frames with hnil | ⟨init, last, hfr⟩
  · rw [hnil] at h; exact absurd h (by simp)
  · rw [List.concat_eq_append] at hfr
    rw [hfr] at h
    have hlast : last.returnContinuation = activeCont rootCont cs := by
      have := congrArg List.getLast? h
      cases cs with
      | nil => simpa [activeCont] using this
      | cons c cs' => simpa [activeCont, List.getLast?_cons] using this
    refine ⟨init, last, hfr, hlast, ?_⟩
    rw [← hlast, ← h]
    simp

/-- The continuation list after a tail call: the replaced active frame carries the narrowed
inherited continuation, which is the continuation of Trusted's narrowed call stack — or, for
a tail call made by the root frame, the narrowed root continuation. -/
private theorem tail_shape {B P : Type} (rootCont : LeanMiri.ReturnContinuation UnwindAction)
    (cs : List SavedCallerFrame) (b : Bool)
    (init : List (LeanMiri.Frame B P UnwindAction)) (newF : LeanMiri.Frame B P UnwindAction)
    (hmap : init.map (·.returnContinuation) ++ [activeCont rootCont cs] =
      rootCont :: (cs.map contOfCaller).reverse)
    (hnew : newF.returnContinuation = narrowCont b (activeCont rootCont cs)) :
    (init ++ [newF]).map (·.returnContinuation) =
      tailRootCont rootCont cs b ::
        ((narrowCallStackForTailCallee cs b).map contOfCaller).reverse := by
  cases cs with
  | nil =>
    have hinit : init = [] := by
      have hl := congrArg List.length hmap
      cases init with
      | nil => rfl
      | cons a as => simp at hl
    subst hinit
    simp only [List.nil_append, List.map_cons, List.map_nil, hnew, narrow_nil, tailRootCont,
      activeCont, List.reverse_nil]
  | cons c cs' =>
    have hinit : init.map (·.returnContinuation) =
        rootCont :: (cs'.map contOfCaller).reverse := by
      have h := hmap
      simp only [activeCont, List.map_cons, List.reverse_cons] at h
      rw [← List.cons_append] at h
      exact List.append_cancel_right h
    rw [narrow_cons, List.map_append, hinit]
    simp only [tailRootCont, List.map_cons, List.map_nil, List.reverse_cons, hnew, activeCont,
      contOfCaller_narrow, List.cons_append]

/-- **LeanMiri tail-call lockstep (universal).** If the Trusted call stack and the LeanMiri
frames are shape-related and the active frame has a caller continuation (`goto`: a nested
frame, or a modular root with an external caller), then after the Trusted tail call (frame
teardown, root relocation, then `enterTailCalleeFrame`) and the transcribed
`Call.evalTailCallTerminator` (matching arity; the `nounwindAs` oracle instantiated with the
callee's own `fnAbi.canUnwind` bit, `nounwindOracle`), the states are again shape-related: the
depth is unchanged in both (no frame is pushed, the frame-index check passes), the machine is
untouched, and the new active LeanMiri frame runs the callee from `bb0[0]` with the inherited
continuation of the tail-caller, its unwind action narrowed to `Unreachable` exactly when the
callee cannot unwind (`narrowCont`) — which is the continuation of Trusted's narrowed saved
caller (`narrowCallStackForTailCallee`). The root continuation is the same unless the
tail-caller *is* the root frame, whose replaced bottom frame carries the narrowed root
continuation (`tailRootCont`; Trusted's `rootUnwindCeiling`). So the callee returns where the
tail-caller would have returned, and unwinds where Miri lets it unwind. -/
theorem tailCall_leanMiri_shape_lockstep {B P M : Type}
    (s : MachineState) (calleeBody : CapturedMir) (argVals : List Value)
    (rootCont : LeanMiri.ReturnContinuation UnwindAction)
    (m : LeanMiri.StepState B P UnwindAction M) (callee : B) (n : Nat)
    (hrel : StackShapeRel rootCont s.memory.callStack m)
    (hgoto : ∃ ret u, activeCont rootCont s.memory.callStack = .goto ret u) :
    ∃ m', LeanMiri.evalTailCallTerminator callee n n m
          { nounwindAs := nounwindOracle calleeBody.fnAbi.canUnwind } = .ok m' ∧
      StackShapeRel (tailRootCont rootCont s.memory.callStack calleeBody.fnAbi.canUnwind)
        (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
          ).memory.callStack m' ∧
      m'.frames.length = m.frames.length ∧ m'.machine = m.machine ∧
      (∃ f, m'.frames.getLast? = some f ∧ f.body = callee ∧ f.location = .mir ⟨0, 0⟩ ∧
        f.returnContinuation =
          narrowCont calleeBody.fnAbi.canUnwind (activeCont rootCont s.memory.callStack)) := by
  obtain ⟨ret, u, hact⟩ := hgoto
  obtain ⟨init, last, hfr, hlast, hmap⟩ := shape_last hrel
  let newF : LeanMiri.Frame B P UnwindAction :=
    { body := callee,
      returnContinuation := narrowCont calleeBody.fnAbi.canUnwind (.goto ret u),
      returnPlace := last.returnPlace, location := .mir ⟨0, 0⟩ }
  have hnew : newF.returnContinuation =
      narrowCont calleeBody.fnAbi.canUnwind (activeCont rootCont s.memory.callStack) :=
    (congrArg (narrowCont calleeBody.fnAbi.canUnwind) hact).symm
  refine ⟨{ m with frames := init ++ [newF] }, ?_, ?_, ?_, rfl,
    ⟨newF, by simp, rfl, rfl, hnew⟩⟩
  · rw [hact] at hlast
    have hpass : LeanMiri.passArgsError (fun _ => true) n 0 n = none :=
      passArgsError_all_ok _ n n 0 (by omega) (fun _ _ _ => rfl)
    simp only [LeanMiri.evalTailCallTerminator, LeanMiri.initFnTailCall, hfr,
      List.getLast?_concat, hlast, hpass, Nat.lt_irrefl, ite_false, List.dropLast_concat]
    cases hb : calleeBody.fnAbi.canUnwind <;> simp [newF, nounwindOracle, narrowCont, hb]
  · show (init ++ [newF]).map (·.returnContinuation) = _
    rw [enterTail_callStack, tailEntryMem_callStack]
    exact tail_shape rootCont s.memory.callStack _ init newF hmap hnew
  · simp [hfr]

/-- **LeanMiri whole-program-root divergence (universal).** At a Trusted root frame that is
shape-related to a LeanMiri `stop` frame (the whole-program root), Trusted's tail call
(when the frame teardown's protector guard passes) tears the root frame down and steps into
the callee, whereas the transcribed `Call.initFnTailCall` raises
`invalidProgram "cannot tailcall as root of stack"` (rustc's `bug!("can't tailcall as
root")`) — a non-UB rejection; the modular-root relation (`goto`) is covered by
`tailCall_leanMiri_shape_lockstep`. -/
theorem tailCall_leanMiri_root_stop_diverges {B P M : Type}
    (s : MachineState) (func : Operand) (argOps : List Operand) (span : String)
    (callerBody calleeBody : CapturedMir) (defPath : DefPath) (argVals : List Value)
    (locals' : List LocalSlot)
    (hfunc : extractCalleeDefPath? func = some defPath)
    (hargs : evalOperandsWithBodyCast s.frame.locals argOps s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals callerBody.localDecls s.memory.callStack =
        .ok argVals locals')
    (hfind : lookupCallee s.memory.callees callerBody.layouts defPath
      (extractCalleeTypeArgs func) s.memory.traitImpls = some calleeBody)
    (hprot : frameDeallocConflict s = false)
    (hroot : s.memory.callStack = []) (c : Bool)
    (m : LeanMiri.StepState B P UnwindAction M) (callee : B) (k n : Nat)
    (hrel : StackShapeRel (.stop c) s.memory.callStack m) :
    evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) =
        MirStepNode.step
          (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals) ∧
      LeanMiri.evalTailCallTerminator callee k n m =
        .error (.invalidProgram "cannot tailcall as root of stack") ∧
      (LeanMiri.StepError.invalidProgram "cannot tailcall as root of stack").isUB = false := by
  refine ⟨(tailCall_trusted_direct_enters_without_push s func argOps span callerBody calleeBody
    defPath argVals locals' hfunc hargs hfind).2.1 hprot, ?_, rfl⟩
  obtain ⟨init, last, hfr, hlast, _⟩ := shape_last hrel
  rw [hroot] at hlast
  simp only [activeCont] at hlast
  simp only [LeanMiri.evalTailCallTerminator, LeanMiri.initFnTailCall, hfr, List.getLast?_concat,
    hlast]

/-- **LeanMiri arity (universal).** With a caller continuation, a tail call whose argument
count differs from the callee's is UB in Miri (`initStackFrame`). -/
theorem tailCall_leanMiri_arity_ub {B P U M : Type} (m : LeanMiri.StepState B P U M)
    (callee : B) (k n : Nat) (hne : k ≠ n) (f : LeanMiri.Frame B P U) (ret : Option Nat)
    (u : U) (hlast : m.frames.getLast? = some f) (hgoto : f.returnContinuation = .goto ret u) :
    ∃ msg, LeanMiri.evalTailCallTerminator callee k n m = .error (.undefinedBehavior msg) := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨"calling a function with more arguments than it expected", ?_⟩
    have hpass : LeanMiri.passArgsError (fun _ => true) n 0 k = none :=
      passArgsError_all_ok _ n k 0 (by omega) (fun _ _ _ => rfl)
    simp [LeanMiri.evalTailCallTerminator, LeanMiri.initFnTailCall, hlast, hgoto, hpass, hlt]
  · refine ⟨"calling a function with fewer arguments than it requires", ?_⟩
    have hpass := passArgsError_fewer n k 0 (Nat.zero_le n) (by omega)
    simp [LeanMiri.evalTailCallTerminator, LeanMiri.initFnTailCall, hlast, hgoto, hpass]

/-- **LeanMiri return-ABI and cleanup checks (universal).** On a frame with a caller
continuation (`goto`) and matching argument count `n`, an incompatible return ABI
(`retAbiCompat = false`, `Call.lean:345-346`) faults with `.undefinedBehavior "AbiMismatchReturn"`,
whereas a frame cleanup that fails to return `.normal` (`cleanupNormal = false`,
`Call.lean:445-446`) raises `.invalidProgram "tailcall cleanup must return Normal"`
(`isUB = false`). -/
theorem tailCall_leanMiri_ret_abi_and_cleanup_universal {B P U M : Type}
    (m : LeanMiri.StepState B P U M) (callee : B) (n : Nat) (cleanupNormal : Bool)
    (f : LeanMiri.Frame B P U) (ret : Option Nat) (u : U)
    (hlast : m.frames.getLast? = some f) (hgoto : f.returnContinuation = .goto ret u) :
    LeanMiri.evalTailCallTerminator callee n n m
        { retAbiCompat := false, cleanupNormal := cleanupNormal } =
        .error (.undefinedBehavior "AbiMismatchReturn") ∧
      (LeanMiri.StepError.undefinedBehavior "AbiMismatchReturn").isUB = true ∧
      LeanMiri.evalTailCallTerminator callee n n m { cleanupNormal := false } =
        .error (.invalidProgram "tailcall cleanup must return Normal") ∧
      (LeanMiri.StepError.invalidProgram "tailcall cleanup must return Normal").isUB = false := by
  have hpass : LeanMiri.passArgsError (fun _ => true) n 0 n = none :=
    passArgsError_all_ok _ n n 0 (by omega) (fun _ _ _ => rfl)
  refine ⟨?_, rfl, ?_, rfl⟩ <;>
    simp [LeanMiri.evalTailCallTerminator, LeanMiri.initFnTailCall, hlast, hgoto, hpass,
      Nat.lt_irrefl]

/-- **LeanMiri per-argument ABI (universal).** On a frame with a caller continuation and a
matching argument count, the first ABI-incompatible callee parameter `j` (every earlier one
compatible) is UB `AbiMismatchArgument j` (`passArgument`, `Call.lean:213-214`), decided before
the return-ABI, surplus-argument, and cleanup checks; with every parameter compatible, the
per-argument loop never fails. Trusted performs the matching check only for indirect calls
(`fnEntryCompatibleWithCallSite` compares the reified input types with the call site's,
`checkCalleeTargetCompatible` with the callee's parameter declarations; see
`tailCall_trusted_fail_closed_universal` and the `extern "C"` witness); for direct `FnDef`
calls rustc's MIR type checker guarantees parameter-type agreement. -/
theorem tailCall_leanMiri_arg_abi_universal {B P U M : Type}
    (m : LeanMiri.StepState B P U M) (callee : B) (n : Nat) (compat : Nat → Bool) (j : Nat)
    (hj : j < n) (hpre : ∀ x, x < j → compat x = true) (hbad : compat j = false)
    (retAbiCompat cleanupNormal : Bool) (f : LeanMiri.Frame B P U) (ret : Option Nat) (u : U)
    (hlast : m.frames.getLast? = some f) (hgoto : f.returnContinuation = .goto ret u) :
    LeanMiri.evalTailCallTerminator callee n n m
        { retAbiCompat := retAbiCompat, cleanupNormal := cleanupNormal, argAbiCompat := compat } =
        .error (.undefinedBehavior s!"AbiMismatchArgument {j}") ∧
      (LeanMiri.StepError.undefinedBehavior s!"AbiMismatchArgument {j}").isUB = true ∧
      LeanMiri.passArgsError (fun _ => true) n 0 n = none := by
  have hfirst := passArgsError_first_mismatch compat n j hj hbad n 0 (Nat.zero_le j) (by omega)
    (fun x _ hx => hpre x hx)
  refine ⟨?_, rfl, passArgsError_all_ok _ n n 0 (by omega) (fun _ _ _ => rfl)⟩
  simp [LeanMiri.evalTailCallTerminator, LeanMiri.initFnTailCall, hlast, hgoto, hfirst]

/-- **LeanMiri calling-convention mismatch UB correspondence (universal).** In Miri
(`initStackFrame`, `Call.lean:254-255`), `unless h.sameConvention callerFnAbi calleeFnAbi`
raises UB `"caller/callee calling convention mismatch"` before the per-argument loop; in
Trusted (`resolveCallTarget` / `checkCalleeTargetCompatible`), an indirect tail call whose
reified `FnPtrEntry` or linked `calleeBody` has a mismatched calling convention also faults
with `MirStepNode.fail .ub`. -/
theorem tailCall_leanMiri_calling_conv_ub_corresponds {B P U M : Type}
    (m : LeanMiri.StepState B P U M) (callee : B) (k n : Nat)
    (retAbiCompat cleanupNormal : Bool) (argAbiCompat : Nat → Bool)
    (f : LeanMiri.Frame B P U) (ret : Option Nat) (u : U)
    (hlast : m.frames.getLast? = some f) (hgoto : f.returnContinuation = .goto ret u)
    (s : MachineState) (func : Operand) (argOps : List Operand) (span : String)
    (callerBody : CapturedMir) (hnodirect : extractCalleeDefPath? func = none)
    (p : ProvenancePtr) (l : List LocalSlot) (fnEntry : FnPtrEntry)
    (h : evalTailFunc s callerBody func = .ok (.ptr p 8) l)
    (hoff : p.offsetBytes = 0) (hbor : lookupBorrow s.memory.borrows p.tag = none)
    (hfn : lookupFnPtr s.memory.fnPtrs p.allocId = some fnEntry)
    (hcompat : fnEntryCompatibleWithCallSite fnEntry (length argOps)
        (operandTy callerBody.localDecls callerBody.layouts func) = false) :
    LeanMiri.evalTailCallTerminator callee k n m
        { retAbiCompat := retAbiCompat, cleanupNormal := cleanupNormal, argAbiCompat := argAbiCompat,
          sameConvention := false } =
        .error (.undefinedBehavior "caller/callee calling convention mismatch") ∧
      (LeanMiri.StepError.undefinedBehavior "caller/callee calling convention mismatch").isUB =
        true ∧
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub := by
  refine ⟨?_, rfl, (tailCall_trusted_fail_closed_universal s func argOps span callerBody
    hnodirect).2.2.2.2.1 p l fnEntry h hoff hbor hfn hcompat⟩
  simp [LeanMiri.evalTailCallTerminator, LeanMiri.initFnTailCall, hlast, hgoto]



/-- **LeanMiri check classification (universal).** On a frame with a caller continuation
and matching arity, every `initStackFrame` check that fails — all earlier ones passing —
produces exactly its source error, checked in source order (`#[track_caller]` before the
calling convention); all are UB verdicts except the internal `cleanup` failure. -/
theorem tailCall_leanMiri_checks_classification {B P U M : Type}
    (m : LeanMiri.StepState B P U M) (callee : B) (n : Nat) (f : LeanMiri.Frame B P U)
    (ret : Option Nat) (u : U) (hlast : m.frames.getLast? = some f)
    (hgoto : f.returnContinuation = .goto ret u) :
    LeanMiri.evalTailCallTerminator callee n n m { trackCallerMatch := false } =
        .error (.undefinedBehavior "caller/callee #[track_caller] mismatch") ∧
      LeanMiri.evalTailCallTerminator callee n n m { sameConvention := false } =
        .error (.undefinedBehavior "caller/callee calling convention mismatch") ∧
      LeanMiri.evalTailCallTerminator callee n n m { variadicMatch := false } =
        .error (.undefinedBehavior "CVariadicMismatch") ∧
      LeanMiri.evalTailCallTerminator callee n n m { variadicFixedMatch := false } =
        .error (.undefinedBehavior "CVariadicFixedCountMismatch") ∧
      LeanMiri.evalTailCallTerminator callee n n m { targetFeaturesOk := false } =
        .error (.undefinedBehavior
          "calling a function that requires unavailable target features") ∧
      LeanMiri.evalTailCallTerminator callee n n m { retAbiCompat := false } =
        .error (.undefinedBehavior "AbiMismatchReturn") ∧
      LeanMiri.evalTailCallTerminator callee n n m { cleanupNormal := false } =
        .error (.invalidProgram "tailcall cleanup must return Normal") ∧
      LeanMiri.evalTailCallTerminator callee n n m
          { trackCallerMatch := false, sameConvention := false } =
        .error (.undefinedBehavior "caller/callee #[track_caller] mismatch") := by
  have hpass : LeanMiri.passArgsError (fun _ => true) n 0 n = none :=
    passArgsError_all_ok _ n n 0 (by omega) (fun _ _ _ => rfl)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [LeanMiri.evalTailCallTerminator, LeanMiri.initFnTailCall, hlast, hgoto, hpass,
      Nat.lt_irrefl]

/-- **LeanMiri non-unwinding callee (universal; resolved correspondence
`DIV-LM-TAILCALL-NOUNWIND-UNWIND`).** When the callee's ABI cannot unwind
(`calleeBody.fnAbi.canUnwind = false`), Miri forces the inherited continuation's unwind action
to `Unreachable`, and so does Trusted's tail call: `enterTailCalleeFrame` narrows the saved
caller's `returnUnwind` to `.unreachable` (`narrowCallStackForTailCallee`) and, for a tail call
made by the modular root, lowers the root unwind ceiling. After the two steps the stack shapes
are related for **every** inherited action `u` (with the narrowed root continuation when the
tail-caller is the root, `tailRootCont`), and an unwind (`UnwindResume`) out of the
non-unwinding callee is UB in **both** references at every depth: Miri faults with "unwinding
past a frame that does not allow unwinding" under a nested caller and with "unwinding past
the topmost stack frame" on a one-frame stack, and Trusted faults with `MirStepNode.fail .ub`
— where it formerly stepped to the caller's cleanup block, aborted, or let the panic
escape. -/
theorem tailCall_leanMiri_nounwind_callee_simulation {B P M : Type}
    (s : MachineState) (calleeBody : CapturedMir) (argVals : List Value)
    (rootCont : LeanMiri.ReturnContinuation UnwindAction)
    (m : LeanMiri.StepState B P UnwindAction M) (callee : B) (n : Nat)
    (hnu : calleeBody.fnAbi.canUnwind = false)
    (hrel : StackShapeRel rootCont s.memory.callStack m) (ret : Option Nat) (u : UnwindAction)
    (hact : activeCont rootCont s.memory.callStack = .goto ret u) :
    ∃ m', LeanMiri.evalTailCallTerminator callee n n m { nounwindAs := some .unreachable } =
        .ok m' ∧
      (∃ f, m'.frames.getLast? = some f ∧ f.returnContinuation = .goto ret .unreachable) ∧
      StackShapeRel (tailRootCont rootCont s.memory.callStack false)
        (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
          ).memory.callStack m' ∧
      (∃ msg, LeanMiri.unwindResume m' = .error (.undefinedBehavior msg)) ∧
      (∀ (f : StackFrame) (span : String) (cb : Option CapturedMir),
        evalTerminator
            ⟨f, (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
              ).memory⟩
            ⟨.unwindResume, span⟩ cb = MirStepNode.fail .ub) ∧
      (∀ (caller : SavedCallerFrame) (rest : List SavedCallerFrame),
        s.memory.callStack = caller :: rest →
        (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
            ).memory.callStack =
          { caller with returnUnwind := .unreachable } :: rest ∧
        LeanMiri.unwindResume m' =
          .error (.undefinedBehavior "unwinding past a frame that does not allow unwinding")) ∧
      (s.memory.callStack = [] →
        (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
            ).memory.rootUnwindCeiling = false ∧
        LeanMiri.unwindResume m' =
          .error (.undefinedBehavior "unwinding past the topmost stack frame")) := by
  obtain ⟨init, last, hfr, hlast, hmap⟩ := shape_last hrel
  let newF : LeanMiri.Frame B P UnwindAction :=
    { body := callee, returnContinuation := .goto ret .unreachable,
      returnPlace := last.returnPlace, location := .mir ⟨0, 0⟩ }
  have hnew : newF.returnContinuation =
      narrowCont false (activeCont rootCont s.memory.callStack) :=
    (congrArg (narrowCont false) hact).symm
  have hpass : LeanMiri.passArgsError (fun _ => true) n 0 n = none :=
    passArgsError_all_ok _ n n 0 (by omega) (fun _ _ _ => rfl)
  have hshape : (init ++ [newF]).map (·.returnContinuation) =
      tailRootCont rootCont s.memory.callStack false ::
        ((narrowCallStackForTailCallee s.memory.callStack false).map contOfCaller).reverse :=
    tail_shape rootCont s.memory.callStack false init newF hmap hnew
  have hstack : (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
      ).memory.callStack = narrowCallStackForTailCallee s.memory.callStack false := by
    rw [enterTail_callStack, tailEntryMem_callStack, hnu]
  have hlenInit : init.length = s.memory.callStack.length := by
    have hl := congrArg List.length hmap
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil,
      List.length_reverse] at hl
    omega
  have hres1 : ∀ (caller : SavedCallerFrame) (rest : List SavedCallerFrame),
      s.memory.callStack = caller :: rest →
      LeanMiri.unwindResume
          ({ m with frames := init ++ [newF] } : LeanMiri.StepState B P UnwindAction M) =
        .error (.undefinedBehavior "unwinding past a frame that does not allow unwinding") := by
    intro caller rest hcs
    have hlen : init.length = rest.length + 1 := hlenInit.trans (congrArg List.length hcs)
    simp [LeanMiri.unwindResume, LeanMiri.unwindToBlock, hlen, newF]
  have hres0 : s.memory.callStack = [] →
      LeanMiri.unwindResume
          ({ m with frames := init ++ [newF] } : LeanMiri.StepState B P UnwindAction M) =
        .error (.undefinedBehavior "unwinding past the topmost stack frame") := by
    intro hnil
    have hinit : init = [] :=
      List.eq_nil_of_length_eq_zero (hlenInit.trans (congrArg List.length hnil))
    subst hinit
    simp [LeanMiri.unwindResume, newF]
  have hex : ∃ msg,
      LeanMiri.unwindResume
          ({ m with frames := init ++ [newF] } : LeanMiri.StepState B P UnwindAction M) =
        .error (.undefinedBehavior msg) := by
    cases hcs : s.memory.callStack with
    | nil => exact ⟨_, hres0 hcs⟩
    | cons caller rest => exact ⟨_, hres1 caller rest hcs⟩
  refine ⟨{ m with frames := init ++ [newF] }, ?_, ⟨newF, by simp, rfl⟩, ?_, hex,
    fun f span cb =>
      (tailCall_trusted_unwind_through s calleeBody argVals f f span span cb cb).2.2 hnu _,
    ?_, ?_⟩
  · rw [hact] at hlast
    simp only [LeanMiri.evalTailCallTerminator, LeanMiri.initFnTailCall, hfr,
      List.getLast?_concat, hlast, hpass, Nat.lt_irrefl, ite_false, List.dropLast_concat]
    simp [newF]
  · show (init ++ [newF]).map (·.returnContinuation) = _
    rw [hstack]
    exact hshape
  · intro caller rest hcs
    refine ⟨?_, hres1 caller rest hcs⟩
    simp only [hstack, hcs]
  · intro hnil
    refine ⟨?_, hres0 hnil⟩
    have hcs' : (tailEntryMem s calleeBody argVals).callStack = [] :=
      (tailEntryMem_callStack s calleeBody argVals).trans hnil
    simp only [enterTailCalleeFrame_rootUnwindCeiling, hcs', hnu, Bool.and_false]

/-- Typed statement pin of the resolved non-unwinding tail-callee correspondence
(`DIV-LM-TAILCALL-NOUNWIND-UNWIND`). -/
example : ∀ {B P M : Type} (s : MachineState) (calleeBody : CapturedMir)
    (argVals : List Value) (rootCont : LeanMiri.ReturnContinuation UnwindAction)
    (m : LeanMiri.StepState B P UnwindAction M) (callee : B) (n : Nat),
    calleeBody.fnAbi.canUnwind = false →
    StackShapeRel rootCont s.memory.callStack m →
    ∀ (ret : Option Nat) (u : UnwindAction),
    activeCont rootCont s.memory.callStack = .goto ret u →
    ∃ m', LeanMiri.evalTailCallTerminator callee n n m { nounwindAs := some .unreachable } =
        .ok m' ∧
      (∃ f, m'.frames.getLast? = some f ∧ f.returnContinuation = .goto ret .unreachable) ∧
      StackShapeRel (tailRootCont rootCont s.memory.callStack false)
        (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
          ).memory.callStack m' ∧
      (∃ msg, LeanMiri.unwindResume m' = .error (.undefinedBehavior msg)) ∧
      (∀ (f : StackFrame) (span : String) (cb : Option CapturedMir),
        evalTerminator
            ⟨f, (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
              ).memory⟩
            ⟨.unwindResume, span⟩ cb = MirStepNode.fail .ub) ∧
      (∀ (caller : SavedCallerFrame) (rest : List SavedCallerFrame),
        s.memory.callStack = caller :: rest →
        (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
            ).memory.callStack =
          { caller with returnUnwind := .unreachable } :: rest ∧
        LeanMiri.unwindResume m' =
          .error (.undefinedBehavior "unwinding past a frame that does not allow unwinding")) ∧
      (s.memory.callStack = [] →
        (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
            ).memory.rootUnwindCeiling = false ∧
        LeanMiri.unwindResume m' =
          .error (.undefinedBehavior "unwinding past the topmost stack frame")) :=
  @tailCall_leanMiri_nounwind_callee_simulation

/-- How `evalTerminator` reports the `MirExecState` reached by `unwindFromCallStack`. -/
def execNode : MirExecState → MirStepNode
  | .running st => MirStepNode.step st
  | .halted out => MirStepNode.retOutcome out
  | .faulted fk => MirStepNode.fail fk

/-- An external callee's panic resumes exactly like an in-table `UnwindResume` in the memory it
returns. -/
private theorem execNode_resumeExternalTailCall_panicked (mem : Memory) (f : StackFrame)
    (span : String) (cb : Option CapturedMir) :
    execNode (resumeExternalTailCall (.panicked mem)) =
      evalTerminator ⟨f, mem⟩ ⟨.unwindResume, span⟩ cb := by
  simp only [resumeExternalTailCall, evalTerminator]
  cases unwindFromCallStack mem.callStack mem <;> rfl

/-- **Unwinding out of a tail-callee (universal; lockstep).**
Under a nested caller (`s.memory.callStack = caller :: rest`, inherited action
`caller.returnUnwind`), Miri's `UnwindResume` out of the tail-callee (`returnFromCurrentFrame
… true` → `unwindToBlock`, transcribed as `LeanMiri.unwindResume`) resolves the callee frame's
continuation, while Trusted (`unwindFromCallStack` — for both in-table `UnwindResume` and
external `resumeExternalTailCall (.panicked …)`) resolves the inherited saved caller's
`returnUnwind`:
* unwinding callee (`calleeBody.fnAbi.canUnwind = true`): both resolve the *same* action
  (`unreachable` is UB, `terminate` aborts, `cleanup bb` resumes the caller at `bb` with every
  frame above it disabled, `continue_` keeps unwinding), exactly as the tail-caller's own
  unwind would (the tail call's frame teardown is subsumed by the catching caller's
  `disableFramesAbove`);
* non-unwinding callee (`canUnwind = false`, Miri oracle `nounwindAs := some .unreachable`):
  both are UB for **every** inherited action — Miri's forced `Unreachable` continuation and
  Trusted's narrowed `returnUnwind` (`tailCall_leanMiri_nounwind_callee_simulation`).
The modular-root case (`callStack = []`, a one-frame LeanMiri stack) is
`tailCall_leanMiri_modular_root_unwind`. -/
theorem tailCall_leanMiri_unwind_verdicts {B P M : Type}
    (s : MachineState) (calleeBody : CapturedMir) (argVals : List Value)
    (rootCont : LeanMiri.ReturnContinuation UnwindAction)
    (m : LeanMiri.StepState B P UnwindAction M) (callee : B) (n : Nat)
    (hrel : StackShapeRel rootCont s.memory.callStack m)
    (caller : SavedCallerFrame) (rest : List SavedCallerFrame)
    (hcs : s.memory.callStack = caller :: rest) (f : StackFrame) (span : String)
    (cb : Option CapturedMir) :
    (∃ m', LeanMiri.evalTailCallTerminator callee n n m = .ok m' ∧
      LeanMiri.unwindResume m' = LeanMiri.unwindToBlock caller.returnUnwind) ∧
    (∃ m', LeanMiri.evalTailCallTerminator callee n n m { nounwindAs := some .unreachable } =
        .ok m' ∧
      LeanMiri.unwindResume m' =
        .error (.undefinedBehavior "unwinding past a frame that does not allow unwinding")) ∧
    (calleeBody.fnAbi.canUnwind = true →
      evalTerminator
          ⟨f, (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
            ).memory⟩
          ⟨.unwindResume, span⟩ cb =
        (match caller.returnUnwind with
         | .unreachable => MirStepNode.fail .ub
         | .terminate => MirStepNode.retOutcome .abort
         | .cleanup bb =>
           MirStepNode.step
             { frame := { caller.frame with blockIdx := bb, stmtIdx := 0 },
               memory := { popCallerMem s.memory caller rest with
                           borrows := disableFramesAbove s.memory.borrows (length rest) } }
         | .continue_ =>
           execNode (unwindFromCallStack rest (popCallerMem s.memory caller rest)))) ∧
    (calleeBody.fnAbi.canUnwind = false →
      evalTerminator
          ⟨f, (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
            ).memory⟩
          ⟨.unwindResume, span⟩ cb = MirStepNode.fail .ub) ∧
    execNode (resumeExternalTailCall
        (.panicked
          (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals).memory)) =
      evalTerminator
        ⟨f, (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals).memory⟩
        ⟨.unwindResume, span⟩ cb := by
  obtain ⟨init, last, hfr, hlast, hmap⟩ := shape_last hrel
  have hact : activeCont rootCont s.memory.callStack =
      .goto (if caller.isDiverging then none else some caller.returnTarget)
        caller.returnUnwind := by
    rw [hcs]; rfl
  rw [hact] at hlast
  have hlen : init.length = rest.length + 1 := by
    have h := hrel
    unfold StackShapeRel at h
    have hl := congrArg List.length h
    simp [hfr, hcs] at hl
    omega
  have hpass : LeanMiri.passArgsError (fun _ => true) n 0 n = none :=
    passArgsError_all_ok _ n n 0 (by omega) (fun _ _ _ => rfl)
  have hres : ∀ (ur : UnwindAction),
      LeanMiri.unwindResume
          ({ m with frames := init ++
              [{ body := callee,
                 returnContinuation :=
                   .goto (if caller.isDiverging then none else some caller.returnTarget) ur,
                 returnPlace := last.returnPlace, location := .mir ⟨0, 0⟩ }] } :
            LeanMiri.StepState B P UnwindAction M) =
        LeanMiri.unwindToBlock ur := by
    intro ur
    simp [LeanMiri.unwindResume, hlen]
  refine ⟨⟨_, ?_, hres caller.returnUnwind⟩, ⟨_, ?_, hres .unreachable⟩, fun hb => ?_,
    fun hb =>
      (tailCall_trusted_unwind_through s calleeBody argVals f f span span cb cb).2.2 hb _,
    execNode_resumeExternalTailCall_panicked _ f span cb⟩
  · simp only [LeanMiri.evalTailCallTerminator, LeanMiri.initFnTailCall, hfr,
      List.getLast?_concat, hlast, hpass, Nat.lt_irrefl, ite_false, List.dropLast_concat]
    simp
  · simp only [LeanMiri.evalTailCallTerminator, LeanMiri.initFnTailCall, hfr,
      List.getLast?_concat, hlast, hpass, Nat.lt_irrefl, ite_false, List.dropLast_concat]
    simp
  · rw [((tailCall_trusted_unwind_through s calleeBody argVals f f span span cb cb).2.1 hb).1]
    cases hu : caller.returnUnwind <;>
      simp [evalTerminator, hcs, unwindFromCallStack, hu, execNode, popCallerMem] <;>
      rfl

/-- **Modular-root unwind (universal; lockstep for non-unwinding callees, documented modeling
divergence for unwinding ones).** At a modular root (`s.memory.callStack = []`, LeanMiri root
continuation `goto ret u`, hence a one-frame LeanMiri stack) the tail call keeps one frame, so
Miri's `returnFromCurrentFrame` rejects an unwind with UB "unwinding past the topmost stack
frame" (for unwinding and non-unwinding callees alike). Trusted agrees for a callee that
**cannot unwind**: the tail call lowered the root unwind ceiling, so the unwind is UB, both
in-table and through `resumeExternalTailCall`. For a callee that **can unwind** Trusted's
modular root lets the panic escape to its external caller (`.halted .panic`) as long as the
root unwind ceiling is still up — the modular-root modeling choice
`MODEL-LM-TAILCALL-MODULAR-ROOT` — and is UB once an earlier non-unwinding tail call lowered
it. -/
theorem tailCall_leanMiri_modular_root_unwind {B P M : Type}
    (s : MachineState) (calleeBody : CapturedMir) (argVals : List Value)
    (m : LeanMiri.StepState B P UnwindAction M) (callee : B) (n : Nat)
    (ret : Option Nat) (u : UnwindAction) (hnil : s.memory.callStack = [])
    (hrel : StackShapeRel (.goto ret u) s.memory.callStack m)
    (f : StackFrame) (span : String) (cb : Option CapturedMir) :
    (∃ m', LeanMiri.evalTailCallTerminator callee n n m = .ok m' ∧
      LeanMiri.unwindResume m' =
        .error (.undefinedBehavior "unwinding past the topmost stack frame")) ∧
    (∃ m', LeanMiri.evalTailCallTerminator callee n n m { nounwindAs := some .unreachable } =
        .ok m' ∧
      LeanMiri.unwindResume m' =
        .error (.undefinedBehavior "unwinding past the topmost stack frame")) ∧
    (calleeBody.fnAbi.canUnwind = false →
      evalTerminator
          ⟨f, (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
            ).memory⟩
          ⟨.unwindResume, span⟩ cb = MirStepNode.fail .ub ∧
      resumeExternalTailCall
          (.panicked
            (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
              ).memory) =
        .faulted .ub) ∧
    (calleeBody.fnAbi.canUnwind = true → s.memory.rootUnwindCeiling = true →
      evalTerminator
          ⟨f, (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
            ).memory⟩
          ⟨.unwindResume, span⟩ cb = MirStepNode.retOutcome .panic ∧
      resumeExternalTailCall
          (.panicked
            (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
              ).memory) =
        .halted .panic) ∧
    (calleeBody.fnAbi.canUnwind = true → s.memory.rootUnwindCeiling = false →
      evalTerminator
          ⟨f, (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
            ).memory⟩
          ⟨.unwindResume, span⟩ cb = MirStepNode.fail .ub ∧
      resumeExternalTailCall
          (.panicked
            (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
              ).memory) =
        .faulted .ub) := by
  have hpass : LeanMiri.passArgsError (fun _ => true) n 0 n = none :=
    passArgsError_all_ok _ n n 0 (by omega) (fun _ _ _ => rfl)
  obtain ⟨init0, last0, hfr0, hlast0, hmap0⟩ := shape_last hrel
  have hact0 : activeCont (.goto ret u) s.memory.callStack = .goto ret u := by
    rw [hnil]; rfl
  rw [hact0] at hlast0
  have hinit0 : init0 = [] := by
    unfold StackShapeRel at hrel
    have hl0 := congrArg List.length hrel
    simp [hfr0, hnil] at hl0
    exact hl0
  subst hinit0
  have hres0 : ∀ (ur : UnwindAction),
      LeanMiri.unwindResume
          ({ m with frames :=
              [{ body := callee, returnContinuation := .goto ret ur,
                 returnPlace := last0.returnPlace, location := .mir ⟨0, 0⟩ }] } :
            LeanMiri.StepState B P UnwindAction M) =
        .error (.undefinedBehavior "unwinding past the topmost stack frame") := by
    intro ur
    simp [LeanMiri.unwindResume]
  -- Trusted: the unwind out of the callee, in terms of the external-panic resumption.
  have hnode : ∀ r : MirExecState,
      resumeExternalTailCall
          (.panicked
            (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
              ).memory) = r →
      evalTerminator
          ⟨f, (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
            ).memory⟩
          ⟨.unwindResume, span⟩ cb = execNode r := by
    intro r hr
    exact (execNode_resumeExternalTailCall_panicked _ f span cb).symm.trans
      (congrArg execNode hr)
  have hrootT : s.memory.rootUnwindCeiling = true →
      unwindFromCallStack s.memory.callStack s.memory = .halted .panic := by
    intro hc
    simp only [hnil, unwindFromCallStack, hc]
  have hrootF : s.memory.rootUnwindCeiling = false →
      unwindFromCallStack s.memory.callStack s.memory = .faulted .ub := by
    intro hc
    simp only [hnil, unwindFromCallStack, hc]
  refine ⟨⟨_, ?_, hres0 u⟩, ⟨_, ?_, hres0 .unreachable⟩, fun hb => ?_, fun hb hc => ?_,
    fun hb hc => ?_⟩
  · simp only [LeanMiri.evalTailCallTerminator, LeanMiri.initFnTailCall, hfr0,
      List.nil_append, List.getLast?_singleton, hlast0, hpass, Nat.lt_irrefl, ite_false]
    simp
  · simp only [LeanMiri.evalTailCallTerminator, LeanMiri.initFnTailCall, hfr0,
      List.nil_append, List.getLast?_singleton, hlast0, hpass, Nat.lt_irrefl, ite_false]
    simp
  · have hext : resumeExternalTailCall
        (.panicked
          (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
            ).memory) = .faulted .ub :=
      unwind_enterTail_nounwind _ calleeBody argVals hb
    exact ⟨hnode _ hext, hext⟩
  · have hext : resumeExternalTailCall
        (.panicked
          (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
            ).memory) = .halted .panic :=
      (unwind_enterTail_canUnwind s calleeBody argVals hb).trans (hrootT hc)
    exact ⟨hnode _ hext, hext⟩
  · have hext : resumeExternalTailCall
        (.panicked
          (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
            ).memory) = .faulted .ub :=
      (unwind_enterTail_canUnwind s calleeBody argVals hb).trans (hrootF hc)
    exact ⟨hnode _ hext, hext⟩

/-- `disableFrameBorrows` disables and marks dead exactly the borrows of the torn-down frame's
locals and keeps every other borrow. -/
private theorem disableFrameBorrows_eq_map (d n : Nat) : ∀ bs : List BorrowEntry,
    disableFrameBorrows bs d n =
      bs.map (fun e =>
        if e.targetFrameDepth = d ∧ e.targetLocal < n then
          { e with perm := .disabled, allocDead := true }
        else e)
  | [] => rfl
  | e :: rest => by
    have ih := disableFrameBorrows_eq_map d n rest
    by_cases hc : e.targetFrameDepth = d ∧ e.targetLocal < n
    · have h1 : Nat.beq e.targetFrameDepth d = true := by
        rw [hc.1]
        exact Nat.beq_refl d
      have hb : Bool.and (Nat.beq e.targetFrameDepth d) (Nat.blt e.targetLocal n) = true := by
        rw [h1, Nat.blt_eq.mpr hc.2]
        rfl
      simp only [disableFrameBorrows, hb, ih, List.map_cons, ite_eq_left hc]
    · have hb : Bool.and (Nat.beq e.targetFrameDepth d) (Nat.blt e.targetLocal n) = false := by
        cases h : Bool.and (Nat.beq e.targetFrameDepth d) (Nat.blt e.targetLocal n) with
        | false => rfl
        | true =>
          simp only [Bool.and_eq_true] at h
          exact absurd ⟨Nat.eq_of_beq_eq_true h.1, Nat.blt_eq.mp h.2⟩ hc
      simp only [disableFrameBorrows, hb, ih, List.map_cons, ite_eq_right hc]

/-- Relocating the root's caller-owned referents only moves entries that name a slot past the
old root frame. -/
private theorem mem_shiftRootCallerReferentBorrows (nOld delta : Nat) :
    ∀ (bs : List BorrowEntry) (e : BorrowEntry),
      e ∈ shiftRootCallerReferentBorrows bs nOld delta → e ∈ bs ∨ nOld ≤ e.targetLocal
  | [], e, h => by
    simp only [shiftRootCallerReferentBorrows, List.not_mem_nil] at h
  | b :: rest, e, h => by
    cases hb : isRootCallerReferentBorrow nOld b with
    | true =>
      simp only [shiftRootCallerReferentBorrows, hb, List.mem_cons] at h
      rcases h with rfl | h
      · right
        have hle : Nat.ble nOld b.targetLocal = true := by
          simp only [isRootCallerReferentBorrow, Bool.and_eq_true] at hb
          exact hb.2.2
        exact Nat.le_trans (Nat.le_of_ble_eq_true hle) (Nat.le_add_right _ _)
      · rcases mem_shiftRootCallerReferentBorrows nOld delta rest e h with h' | h'
        · exact Or.inl (List.mem_cons_of_mem _ h')
        · exact Or.inr h'
    | false =>
      simp only [shiftRootCallerReferentBorrows, hb, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inl List.mem_cons_self
      · rcases mem_shiftRootCallerReferentBorrows nOld delta rest e h with h' | h'
        · exact Or.inl (List.mem_cons_of_mem _ h')
        · exact Or.inr h'

private theorem mem_relocate_borrows (mem : Memory) (nOld nNew : Nat) (e : BorrowEntry)
    (h : e ∈ (relocateRootCallerReferents mem nOld nNew).borrows) :
    e ∈ mem.borrows ∨ nOld ≤ e.targetLocal := by
  cases hw : Nat.blt nOld nNew with
  | false =>
    simp only [relocateRootCallerReferents, hw] at h
    exact Or.inl h
  | true =>
    cases hr : hasAnyRootCallerReferent mem.borrows nOld with
    | false =>
      simp only [relocateRootCallerReferents, hw, hr] at h
      exact Or.inl h
    | true =>
      simp only [relocateRootCallerReferents, hw, hr] at h
      exact mem_shiftRootCallerReferentBorrows nOld _ mem.borrows e h

/-- **Tail-caller cleanup (universal; resolved correspondence).** Whenever the transcribed
tail call succeeds, the popped tail-caller frame has a `goto` continuation (a `stop` root is
rejected), so Miri's `h.cleanup choice false frame` (`CallMachine.cleanup`) deallocates every
live memory-backed local of the tail-caller before the callee runs. Trusted's tail call tears
the same frame down before `enterTailCalleeFrame` replaces its locals by the callee's
(`initLocals`): the borrow table becomes `disableFrameBorrows` of the old one
(`frameTeardownMem`), which disables and marks dead (`allocDead`) *exactly* the borrows of the
popped frame's locals (depth `length s.memory.callStack`, local index
`< length s.frame.locals`) and keeps every other borrow; under a caller that is the callee's
entry borrow table, and at a modular root the relocation of the live caller-owned referents
(`tailEntryMem`) only moves entries that name a slot *past* the popped frame. So after the
tail call every borrow into the popped frame is disabled and dead, a pointer into it is
dangling, and dereferencing it is UB
(`tailCall_witness_dangling_caller_local_simulation`), like Miri's use-after-free. -/
theorem tailCall_leanMiri_cleanup_frees_caller_locals {B P U M : Type}
    (m m' : LeanMiri.StepState B P U M) (callee : B) (k n : Nat) (ck : LeanMiri.CallChecks U)
    (h : LeanMiri.evalTailCallTerminator callee k n m ck = .ok m')
    (s : MachineState) (calleeBody : CapturedMir) (argVals : List Value) :
    (∃ f, m.frames.getLast? = some f ∧
      LeanMiri.cleanupDeallocatesLocals f.returnContinuation = true) ∧
    (frameTeardownMem s).borrows =
      s.memory.borrows.map (fun e =>
        if e.targetFrameDepth = length s.memory.callStack ∧ e.targetLocal < length s.frame.locals
        then { e with perm := .disabled, allocDead := true }
        else e) ∧
    (∀ (caller : SavedCallerFrame) (rest : List SavedCallerFrame),
      s.memory.callStack = caller :: rest →
      (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
          ).memory.borrows =
        (frameTeardownMem s).borrows) ∧
    (∀ e ∈ (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
        ).memory.borrows,
      e.targetFrameDepth = length s.memory.callStack → e.targetLocal < length s.frame.locals →
      e.perm = .disabled ∧ e.allocDead = true) ∧
    (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals).frame.locals =
      initLocals calleeBody argVals := by
  have hmap := disableFrameBorrows_eq_map (length s.memory.callStack) (length s.frame.locals)
    s.memory.borrows
  refine ⟨?_, hmap, ?_, ?_, rfl⟩
  · unfold LeanMiri.evalTailCallTerminator LeanMiri.initFnTailCall at h
    cases hl : m.frames.getLast? with
    | none => simp [hl] at h
    | some f =>
      cases hc : f.returnContinuation with
      | stop c => simp [hl, hc] at h
      | goto ret u => exact ⟨f, rfl, by simp [LeanMiri.cleanupDeallocatesLocals, hc]⟩
  · intro caller rest hcs
    show (tailEntryMem s calleeBody argVals).borrows = _
    rw [tailEntryMem_of_cons s calleeBody argVals hcs]
  · intro e he hd hl
    have he' : e ∈ disableFrameBorrows s.memory.borrows (length s.memory.callStack)
        (length s.frame.locals) := by
      have he1 : e ∈ (tailEntryMem s calleeBody argVals).borrows := he
      by_cases hnil : s.memory.callStack = []
      · rw [tailEntryMem_of_nil s calleeBody argVals hnil] at he1
        rcases mem_relocate_borrows _ _ _ e he1 with h' | h'
        · exact h'
        · exact absurd hl (Nat.not_lt.mpr h')
      · obtain ⟨caller, rest, hcs⟩ := List.exists_cons_of_ne_nil hnil
        rw [tailEntryMem_of_cons s calleeBody argVals hcs] at he1
        exact he1
    rw [hmap] at he'
    obtain ⟨e0, _, rfl⟩ := List.mem_map.mp he'
    by_cases hc : e0.targetFrameDepth = length s.memory.callStack ∧
        e0.targetLocal < length s.frame.locals
    · rw [ite_eq_left hc]
      exact ⟨rfl, rfl⟩
    · rw [ite_eq_right hc] at hd hl
      exact absurd ⟨hd, hl⟩ hc

/-- Typed statement pin of the resolved cleanup correspondence. -/
example : ∀ {B P U M : Type} (m m' : LeanMiri.StepState B P U M) (callee : B) (k n : Nat)
    (ck : LeanMiri.CallChecks U),
    LeanMiri.evalTailCallTerminator callee k n m ck = .ok m' →
    ∀ (s : MachineState) (calleeBody : CapturedMir) (argVals : List Value),
    (∃ f, m.frames.getLast? = some f ∧
      LeanMiri.cleanupDeallocatesLocals f.returnContinuation = true) ∧
    (frameTeardownMem s).borrows =
      s.memory.borrows.map (fun e =>
        if e.targetFrameDepth = length s.memory.callStack ∧ e.targetLocal < length s.frame.locals
        then { e with perm := .disabled, allocDead := true }
        else e) ∧
    (∀ (caller : SavedCallerFrame) (rest : List SavedCallerFrame),
      s.memory.callStack = caller :: rest →
      (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
          ).memory.borrows =
        (frameTeardownMem s).borrows) ∧
    (∀ e ∈ (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
        ).memory.borrows,
      e.targetFrameDepth = length s.memory.callStack → e.targetLocal < length s.frame.locals →
      e.perm = .disabled ∧ e.allocDead = true) ∧
    (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals).frame.locals =
      initLocals calleeBody argVals :=
  @tailCall_leanMiri_cleanup_frees_caller_locals

/-- **ABI mismatch correspondence (universal).** For an indirect tail call through a
registered function pointer whose reified calling convention `sigAbi` differs from the
call site's `callerAbi`, Trusted faults with UB (`fnEntryCompatibleWithCallSite`), and the
LeanMiri step whose `sameConvention` oracle is instantiated with *the same comparison*
(`callConvEq callerAbi sigAbi`, Miri's `sameConvention callerFnAbi calleeFnAbi`) is UB with
"caller/callee calling convention mismatch" — the two verdicts come from one datum. -/
theorem tailCall_abi_mismatch_corresponds {B P M : Type}
    (s : MachineState) (func : Operand) (argOps : List Operand) (span : String)
    (callerBody : CapturedMir) (hnodirect : extractCalleeDefPath? func = none)
    (p : ProvenancePtr) (l : List LocalSlot) (fnEntry : FnPtrEntry)
    (h : evalTailFunc s callerBody func = .ok (.ptr p 8) l)
    (hoff : p.offsetBytes = 0) (hbor : lookupBorrow s.memory.borrows p.tag = none)
    (hfn : lookupFnPtr s.memory.fnPtrs p.allocId = some fnEntry)
    (callerIns : List RigidTy) (callerOut : RigidTy) (callerSafety : Safety)
    (callerAbi : CallConv) (li : Nat)
    (hty : operandTy callerBody.localDecls callerBody.layouts func =
      some { kind := .fnPtr callerIns callerOut callerSafety callerAbi, layoutIdx := li })
    (sigIns : List RigidTy) (sigOut : RigidTy) (sigSafety : Safety) (sigAbi : CallConv)
    (hsig : fnEntry.fnSig = some (.fnPtr sigIns sigOut sigSafety sigAbi))
    (hne : callConvEq callerAbi sigAbi = false)
    (m : LeanMiri.StepState B P UnwindAction M) (callee : B) (k n : Nat)
    (fr : LeanMiri.Frame B P UnwindAction) (ret : Option Nat) (u : UnwindAction)
    (hlast : m.frames.getLast? = some fr) (hgoto : fr.returnContinuation = .goto ret u) :
    evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub ∧
      LeanMiri.evalTailCallTerminator callee k n m
          { sameConvention := callConvEq callerAbi sigAbi } =
        .error (.undefinedBehavior "caller/callee calling convention mismatch") := by
  have hcompat : fnEntryCompatibleWithCallSite fnEntry (length argOps)
      (operandTy callerBody.localDecls callerBody.layouts func) = false := by
    rw [hty]
    simp [fnEntryCompatibleWithCallSite, hsig, hne]
  refine ⟨(tailCall_trusted_fail_closed_universal s func argOps span callerBody
    hnodirect).2.2.2.2.1 p l fnEntry h hoff hbor hfn hcompat, ?_⟩
  simp [LeanMiri.evalTailCallTerminator, LeanMiri.initFnTailCall, hlast, hgoto, hne]

/-- **LeanMiri call contrast (universal).** A returning Trusted `call` (`pushCalleeFrame`)
and the transcribed call push both grow the stack by one frame and stay shape-related —
the pushed continuation is the saved caller's `goto targetBb` — whereas a tail call
(frame teardown and `enterTailCalleeFrame` / `LeanMiri.evalTailCallTerminator`) preserves the
depth, so the returning call is strictly one frame deeper than the tail call on both
sides. -/
theorem tailCall_leanMiri_call_pushes {B P M : Type}
    (s : MachineState) (callerBody calleeBody : CapturedMir) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (argVals : List Value)
    (unwind : UnwindAction) (rootCont : LeanMiri.ReturnContinuation UnwindAction)
    (m : LeanMiri.StepState B P UnwindAction M) (callee : B) (dest : P) (n : Nat)
    (hrel : StackShapeRel rootCont s.memory.callStack m) :
    StackShapeRel rootCont
        (pushCalleeFrame s callerBody locals' destination targetBb calleeBody argVals unwind
          ).memory.callStack
        (LeanMiri.evalCallPush callee dest (some targetBb) unwind m) ∧
      (LeanMiri.evalCallPush callee dest (some targetBb) unwind m).frames.length =
        m.frames.length + 1 ∧
      (pushCalleeFrame s callerBody locals' destination targetBb calleeBody argVals unwind
          ).memory.callStack.length =
        (enterTailCalleeFrame (tailEntryMem s calleeBody argVals) calleeBody argVals
          ).memory.callStack.length +
          1 ∧
      (∀ (m' : LeanMiri.StepState B P UnwindAction M),
        LeanMiri.evalTailCallTerminator callee n n m = .ok m' →
        (LeanMiri.evalCallPush callee dest (some targetBb) unwind m).frames.length =
          m'.frames.length + 1) := by
  refine ⟨?_, by simp [LeanMiri.evalCallPush], ?_, ?_⟩
  · unfold StackShapeRel at hrel ⊢
    simp only [LeanMiri.evalCallPush, pushCalleeFrame, List.map_append, hrel, List.map_cons,
      List.reverse_cons, contOfCaller, List.map_nil]
    rfl
  · rw [enterTail_callStack, narrow_length, tailEntryMem_callStack]
    simp [pushCalleeFrame]
  · intro m' htc
    obtain ⟨init, last, hfr, _, _⟩ := shape_last hrel
    cases hcont : last.returnContinuation with
    | stop c =>
      simp [LeanMiri.evalTailCallTerminator, LeanMiri.initFnTailCall, hfr, hcont] at htc
    | goto ret u =>
      have hpass : LeanMiri.passArgsError (fun _ => true) n 0 n = none :=
        passArgsError_all_ok _ n n 0 (by omega) (fun _ _ _ => rfl)
      simp only [LeanMiri.evalTailCallTerminator, LeanMiri.initFnTailCall, hfr,
        List.getLast?_concat, hcont, hpass, Nat.lt_irrefl, ite_false, List.dropLast_concat] at htc
      simp at htc
      subst htc
      simp [LeanMiri.evalCallPush, hfr]

/-! ### Concrete witnesses -/

def fnItem (dp : String) : Operand :=
  .constant { ty := { kind := .fnDef dp [], layoutIdx := 0 }, val := .zeroSized }

/-- `fn g(a: u32) -> u32 { _0 = move _1; return }`. -/
def gBody : CapturedMir :=
  mkBody "w::g" 1 [u32Decl "_0", u32Decl "a"] [blk [assignMove 0 1] .return_]

/-- `fn f(x: u32) -> u32 { become g(move _1) }`. -/
def fBody : CapturedMir :=
  mkBody "w::f" 1 [u32Decl "_0", u32Decl "x"] [blk [] (.tailCall (fnItem "w::g") [.move (lc 1)])]

/-- `fn main() -> u32 { StorageLive(_1); _1 = f(5) -> bb1; bb1: _0 = move _1; return }`. -/
def mainBody : CapturedMir :=
  mkBody "w::main" 0 [u32Decl "_0", u32Decl "t"]
    [blk [st (.storageLive 1)] (.call (fnItem "w::f") [cU32 5] (lc 1) (some 1) .continue_),
     blk [assignMove 0 1] .return_]

def mainInit : MachineState := initMachineStateWithCallees mainBody [] [fBody, gBody]

/-- Non-tail variant `fn fc(x) -> u32 { StorageLive(_2); _2 = g(move _1) -> bb1; bb1: _0 = move _2;
return }` and its caller. -/
def fcBody : CapturedMir :=
  mkBody "w::fc" 1 [u32Decl "_0", u32Decl "x", u32Decl "t"]
    [blk [st (.storageLive 2)] (.call (fnItem "w::g") [.move (lc 1)] (lc 2) (some 1) .continue_),
     blk [assignMove 0 2] .return_]

def mainCBody : CapturedMir :=
  mkBody "w::mainc" 0 [u32Decl "_0", u32Decl "t"]
    [blk [st (.storageLive 1)] (.call (fnItem "w::fc") [cU32 5] (lc 1) (some 1) .continue_),
     blk [assignMove 0 1] .return_]

def mainCInit : MachineState := initMachineStateWithCallees mainCBody [] [fcBody, gBody]

/-- Root-of-stack LeanMiri continuation for the witnesses' conts projection. -/
def trustedConts? (rootCont : LeanMiri.ReturnContinuation UnwindAction) :
    Option MirExecState → Option (List (LeanMiri.ReturnContinuation UnwindAction))
  | some (.running s) => some (rootCont :: (s.memory.callStack.map contOfCaller).reverse)
  | _ => none

/-- **Positive witness (nested, in-table).** `main → f(5)`, `f` tail-calls `g`: the run
returns `5`; the stack is one frame deep after the call, *still* one frame deep after the
tail call (vs. two for the non-tail `fc`), and empty again after `g` returns straight into
`main`. The Trusted continuation stack is exactly the LeanMiri shape: `[stop, goto bb1
continue]` after the call and — `g`'s ABI cannot unwind — `[stop, goto bb1 unreachable]`
after the tail call (`tailCall_leanMiri_nounwind_callee_simulation`). -/
theorem tailCall_witness_nested_runs :
    retVal? (Anneal.MirFuelFree.runMirExecBounded 7 mainBody (.running mainInit)) =
        some (.scalar ⟨5, 4⟩) ∧
      depth? (execN mainBody 2 (.running mainInit)) = some 1 ∧
      depth? (execN mainBody 3 (.running mainInit)) = some 1 ∧
      depth? (execN mainBody 5 (.running mainInit)) = some 0 ∧
      depth? (execN mainCBody 4 (.running mainCInit)) = some 2 ∧
      retVal? (Anneal.MirFuelFree.runMirExecBounded 10 mainCBody (.running mainCInit)) =
        some (.scalar ⟨5, 4⟩) ∧
      trustedConts? (.stop false) (execN mainBody 2 (.running mainInit)) =
        some [.stop false, .goto (some 1) .continue_] ∧
      trustedConts? (.stop false) (execN mainBody 3 (.running mainInit)) =
        some [.stop false, .goto (some 1) .unreachable] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Positive witness (root, in-table).** `f(7)` as the root tail-calls `g`: the callee's
return halts the whole run with `7` (the modular-root reading). -/
theorem tailCall_witness_root_runs :
    retVal? (Anneal.MirFuelFree.runMirExecBounded 3 fBody
        (.running (initMachineStateWithCallees fBody [.scalar ⟨7, 4⟩] [gBody]))) =
      some (.scalar ⟨7, 4⟩) :=
  rfl

/-- `n` coalgebra steps answering every external call with `oracle`. -/
def execNWith (oracle : MirCallReq → MirCallAns) (body : CapturedMir) :
    Nat → MirExecState → Option MirExecState
  | 0, s => some s
  | n + 1, s =>
    match stepMirState body s with
    | .ret out => execNWith oracle body n (.halted out)
    | .tau s' => execNWith oracle body n s'
    | .vis (.inl (.fail k)) _ => some (.faulted k)
    | .vis (.inr (.inl _)) k => execNWith oracle body n (k PUnit.unit)
    | .vis (.inr (.inr (.call req))) k => execNWith oracle body n (k (oracle req))

/-- `fn fext(x: u32) -> u32 { become ext::h(move _1) }` (no linked body for `ext::h`). -/
def fExtBody : CapturedMir :=
  mkBody "w::fext" 1 [u32Decl "_0", u32Decl "x"]
    [blk [] (.tailCall (fnItem "ext::h") [.move (lc 1)])]

def mainExtBody : CapturedMir :=
  mkBody "w::mainext" 0 [u32Decl "_0", u32Decl "t"]
    [blk [st (.storageLive 1)] (.call (fnItem "w::fext") [cU32 5] (lc 1) (some 1) .continue_),
     blk [assignMove 0 1] .return_]

/-- **Positive witness (external).** At the root, the tail call to `ext::h` emits exactly
the external request `ext::h(7)` with the current memory, resumed by
`resumeExternalTailCallWithAbi` under the root's unwind ceiling (`true`) and the direct
callee's may-unwind ABI (`some true`); the external answer `9` halts the run with `9`; nested
under `main`, the external answer lands in `main`'s destination and `main` returns `9`. -/
theorem tailCall_witness_external :
    stepMirFn fExtBody (initMachineState fExtBody [.scalar ⟨7, 4⟩]) =
        MirStepNode.extCall
          { defPath := "ext::h", typeArgs := [], args := [.scalar ⟨7, 4⟩],
            memory := (initMachineState fExtBody [.scalar ⟨7, 4⟩]).memory }
          (resumeExternalTailCallWithAbi true (some true)) ∧
      resumeExternalTailCallWithAbi true (some true)
          (.returned (.scalar ⟨9, 4⟩) (initMachineState fExtBody [.scalar ⟨7, 4⟩]).memory) =
        .halted (.normal (.scalar ⟨9, 4⟩, (initMachineState fExtBody [.scalar ⟨7, 4⟩]).memory)) ∧
      haltedVal? (execNWith (fun req => .returned (.scalar ⟨9, 4⟩) req.memory) mainExtBody 6
          (.running (initMachineStateWithCallees mainExtBody [] [fExtBody]))) =
        some (.scalar ⟨9, 4⟩) :=
  ⟨rfl, rfl, rfl⟩

/-- A `fn(u32) -> u32` local. -/
def fnPtrDecl : LocalDecl :=
  { mutability := .mut, ty := { kind := .fnPtr [.uint .u32] (.uint .u32) .safe .rust, layoutIdx := 0 },
    debugName := some "fp" }

/-- `fn tc_ptr(fp: fn(u32) -> u32) -> u32 { become fp(3) }`. -/
def tcPtrBody : CapturedMir :=
  mkBody "w::tc_ptr" 1 [u32Decl "_0", fnPtrDecl] [blk [] (.tailCall (.copy (lc 1)) [cU32 3])]

/-- The same through a zero-argument call site (arity mismatch). -/
def tcPtrArityBody : CapturedMir :=
  mkBody "w::tc_ptr_arity" 1 [u32Decl "_0", fnPtrDecl] [blk [] (.tailCall (.copy (lc 1)) [])]

def gFnPtr : ProvenancePtr := ⟨fnPtrAllocBase, 0⟩

def gEntry (abi : CallConv) : FnPtrEntry :=
  { allocId := fnPtrAllocBase, defPath := "w::g", typeArgs := [],
    fnSig := some (.fnPtr [.uint .u32] (.uint .u32) .safe abi) }

/-- `g` with an intrinsic ABI (incompatible with a `fn` pointer call). -/
def gIntrinsicBody : CapturedMir := { gBody with fnAbi := { wFnAbi with conv := .rustIntrinsic } }

def ptrState (body : CapturedMir) (fnPtrs : List FnPtrEntry) (callees : List CapturedMir) :
    MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := initLocals body [.ptr gFnPtr 8] },
    memory := { callees := callees, fnPtrs := fnPtrs } }

/-- `fn tc_zst(f: FnDef(g)) -> u32 { become f(4) }` (a zero-sized function-item local). -/
def tcZstBody : CapturedMir :=
  mkBody "w::tc_zst" 1
    [u32Decl "_0", { mutability := .not, ty := { kind := .fnDef "w::g" [], layoutIdx := 0 },
                     debugName := some "f" }]
    [blk [] (.tailCall (.copy (lc 1)) [cU32 4])]

/-- **Positive witness (indirect and ZST).** A registered, signature-compatible function
pointer and a zero-sized function-item local both resolve and enter `g` without a push. -/
theorem tailCall_witness_indirect_and_zst :
    stepMirFn tcPtrBody (ptrState tcPtrBody [gEntry .rust] [gBody]) =
        MirStepNode.step
          (enterTailCalleeFrame (ptrState tcPtrBody [gEntry .rust] [gBody]).memory gBody
            [.scalar ⟨3, 4⟩]) ∧
      stepMirFn tcZstBody (initMachineStateWithCallees tcZstBody [.unit] [gBody]) =
        MirStepNode.step
          (enterTailCalleeFrame (initMachineStateWithCallees tcZstBody [.unit] [gBody]).memory
            gBody [.scalar ⟨4, 4⟩]) :=
  ⟨rfl, rfl⟩

/-- `fn tc_nonfn() -> u32 { become (0_u8)() }`. -/
def tcNonFnBody : CapturedMir :=
  mkBody "w::tc_nonfn" 0 [u32Decl "_0"] [blk [] (.tailCall (cU8 0) [])]

/-- `fn tc_dead() -> u32 { become g(move _1) }` with `_1` never made live. -/
def tcDeadBody : CapturedMir :=
  mkBody "w::tc_dead" 0 [u32Decl "_0", u32Decl "d"]
    [blk [] (.tailCall (fnItem "w::g") [.move (lc 1)])]

/-- `fn tc_uninit() -> u32 { StorageLive(_1); become g(copy _1) }` (`_1` live but uninit). -/
def tcUninitBody : CapturedMir :=
  mkBody "w::tc_uninit" 0 [u32Decl "_0", u32Decl "u"]
    [blk [st (.storageLive 1)] (.tailCall (fnItem "w::g") [.copy (lc 1)])]

/-- A diverging saved caller. -/
def divCaller : SavedCallerFrame :=
  { callerBody := mainBody, frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] },
    destination := lc 1, isDiverging := true }

/-- **Negative witnesses (fail-closed UB).** A non-function callee, an unregistered function
pointer, an arity-mismatched pointer call, an ABI-mismatched pointer (`extern "C"` entry at a
`fn` call site), a callee body with the intrinsic ABI, a dead (moved) argument, an external return into a
diverging caller, and an uninitialized (copied) argument are all UB. -/
theorem tailCall_witness_ub_cases :
    stepMirFn tcNonFnBody (initMachineState tcNonFnBody []) = MirStepNode.fail .ub ∧
      stepMirFn tcPtrBody (ptrState tcPtrBody [] [gBody]) = MirStepNode.fail .ub ∧
      stepMirFn tcPtrArityBody (ptrState tcPtrArityBody [gEntry .rust] [gBody]) =
        MirStepNode.fail .ub ∧
      stepMirFn tcPtrBody (ptrState tcPtrBody [gEntry .c] [gBody]) = MirStepNode.fail .ub ∧
      stepMirFn tcPtrBody (ptrState tcPtrBody [gEntry .rust] [gIntrinsicBody]) =
        MirStepNode.fail .ub ∧
      stepMirFn tcDeadBody (initMachineStateWithCallees tcDeadBody [] [gBody]) =
        MirStepNode.fail .ub ∧
      resumeExternalTailCall
          (.returned (.scalar ⟨1, 4⟩) { emptyMemory with callStack := [divCaller] }) =
        .faulted .ub ∧
      isUbFault (execN tcUninitBody 2
        (.running (initMachineStateWithCallees tcUninitBody [] [gBody]))) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `fn fshort() -> u32 { become g() }`: a direct call with fewer arguments than `g`
expects (ruled out by rustc's MIR type checker for `FnDef` callees). -/
def fShortBody : CapturedMir :=
  mkBody "w::fshort" 0 [u32Decl "_0"] [blk [] (.tailCall (fnItem "w::g") [])]

/-- **Documented divergence (direct arity).** Miri rejects the ill-arity direct tail call
at the call (UB), while Trusted enters `g` with a dead parameter and faults one step later,
when `g` reads it — both report UB, at different steps. -/
theorem tailCall_witness_direct_arity_divergence :
    execN fShortBody 1 (.running (initMachineStateWithCallees fShortBody [] [gBody])) =
        some (.running (enterTailCalleeFrame
          (initMachineStateWithCallees fShortBody [] [gBody]).memory gBody [])) ∧
      isUbFault (execN fShortBody 2
        (.running (initMachineStateWithCallees fShortBody [] [gBody]))) = true ∧
      LeanMiri.evalTailCallTerminator "w::g" 1 0
          (⟨[{ body := "w::fshort", returnContinuation := .goto (some 1) UnwindAction.continue_,
               returnPlace := (0 : Nat), location := .mir ⟨0, 0⟩ }], ()⟩ :
            LeanMiri.StepState String Nat UnwindAction Unit) =
        .error (.undefinedBehavior "calling a function with fewer arguments than it requires") :=
  ⟨rfl, rfl, rfl⟩

/-- `*mut u32`. -/
def tyPtrMutU32 : Ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 0 }

def ptrDecl (name : String) : LocalDecl :=
  { mutability := .mut, ty := tyPtrMutU32, debugName := some name }

/-- `fn gread(p: *mut u32, y: u32) -> u32 { _0 = copy (*p); return }`. -/
def gReadBody : CapturedMir :=
  mkBody "w::gread" 2 [u32Decl "_0", ptrDecl "p", u32Decl "y"]
    [blk [st (.assign (lc 0) (.use (.copy ⟨1, [.deref]⟩)))] .return_]

/-- `fn fdangle() -> u32 { let mut x = 42; let p = &raw mut x; become gread(p, 137) }`
(`_1 = p`, `_2 = x`): the tail-callee receives a raw pointer into the tail-caller's frame. -/
def fDangleBody : CapturedMir :=
  mkBody "w::fdangle" 0 [u32Decl "_0", ptrDecl "p", u32Decl "x"]
    [blk [st (.storageLive 1), st (.storageLive 2), assignU32 2 42,
          st (.assign (lc 1) (.rawPtr .mut (lc 2)))]
      (.tailCall (fnItem "w::gread") [.copy (lc 1), cU32 137])]

/-- Witness LeanMiri frames: `main` (whole-program root) below `f` (returning to `bb1`). -/
def lmFrame (b : String) (c : LeanMiri.ReturnContinuation UnwindAction) :
    LeanMiri.Frame String Nat UnwindAction :=
  { body := b, returnContinuation := c, returnPlace := 1, location := .mir ⟨0, 0⟩ }

/-- **LeanMiri witnesses.** Nested: the tail call replaces `f` by `g`, which inherits
`goto bb1` (depth 2 → 2); a call pushes instead (depth 2 → 3); a whole-program root
`stop` frame is rejected with `invalidProgram`; a modular root (`goto`) frame is replaced
like a nested one; an arity mismatch is UB. -/
theorem tailCall_leanMiri_witness :
    LeanMiri.evalTailCallTerminator "w::g" 1 1
        (⟨[lmFrame "w::main" (.stop false), lmFrame "w::f" (.goto (some 1) .continue_)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) =
      .ok ⟨[lmFrame "w::main" (.stop false), lmFrame "w::g" (.goto (some 1) .continue_)], ()⟩ ∧
    (LeanMiri.evalCallPush "w::g" 2 (some 1) .continue_
        (⟨[lmFrame "w::main" (.stop false), lmFrame "w::f" (.goto (some 1) .continue_)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit)).frames.length = 3 ∧
    LeanMiri.evalTailCallTerminator "w::g" 1 1
        (⟨[lmFrame "w::f" (.stop false)], ()⟩ : LeanMiri.StepState String Nat UnwindAction Unit) =
      .error (.invalidProgram "cannot tailcall as root of stack") ∧
    LeanMiri.evalTailCallTerminator "w::g" 1 1
        (⟨[lmFrame "w::f" (.goto (some 3) .continue_)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) =
      .ok ⟨[lmFrame "w::g" (.goto (some 3) .continue_)], ()⟩ ∧
    LeanMiri.evalTailCallTerminator "w::g" 2 1
        (⟨[lmFrame "w::f" (.goto (some 3) .continue_)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) =
      .error (.undefinedBehavior "calling a function with fewer arguments than it requires") :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **LeanMiri negative witness (per-argument ABI).** A 2-parameter tail call whose second
argument is ABI-incompatible is UB `AbiMismatchArgument 1`; with a short argument list the
missing-argument UB wins at its index, exactly as `initStackFrame` iterates. -/
theorem tailCall_leanMiri_witness_arg_abi :
    LeanMiri.evalTailCallTerminator "w::g" 2 2
        (⟨[lmFrame "w::f" (.goto (some 3) .continue_)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) { argAbiCompat := fun i => i != 1 } =
      .error (.undefinedBehavior "AbiMismatchArgument 1") ∧
    LeanMiri.evalTailCallTerminator "w::g" 2 1
        (⟨[lmFrame "w::f" (.goto (some 3) .continue_)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) { argAbiCompat := fun i => i != 1 } =
      .error (.undefinedBehavior "calling a function with fewer arguments than it requires") ∧
    LeanMiri.evalTailCallTerminator "w::g" 2 2
        (⟨[lmFrame "w::f" (.goto (some 3) .continue_)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) { argAbiCompat := fun i => i != 0 } =
      .error (.undefinedBehavior "AbiMismatchArgument 0") :=
  ⟨rfl, rfl, rfl⟩

/-- **LeanMiri witnesses (checks).** A `#[track_caller]` mismatch, missing target features,
and a non-unwinding callee on a concrete frame: the first two are UB; the third succeeds
with the inherited `goto bb3` continuation's unwind forced from `continue` to `unreachable`. -/
theorem tailCall_leanMiri_witness_checks :
    LeanMiri.evalTailCallTerminator "w::g" 1 1
        (⟨[lmFrame "w::f" (.goto (some 3) .continue_)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) { trackCallerMatch := false } =
      .error (.undefinedBehavior "caller/callee #[track_caller] mismatch") ∧
    LeanMiri.evalTailCallTerminator "w::g" 1 1
        (⟨[lmFrame "w::f" (.goto (some 3) .continue_)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) { targetFeaturesOk := false } =
      .error (.undefinedBehavior "calling a function that requires unavailable target features") ∧
    LeanMiri.evalTailCallTerminator "w::g" 1 1
        (⟨[lmFrame "w::f" (.goto (some 3) .continue_)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) { nounwindAs := some .unreachable } =
      .ok ⟨[lmFrame "w::g" (.goto (some 3) .unreachable)], ()⟩ :=
  ⟨rfl, rfl, rfl⟩

/-- `fn gunw() -> u32 { resume }` and `fn funw() -> u32 { become gunw() }`. -/
def gUnwindBody : CapturedMir := mkBody "w::gunw" 0 [u32Decl "_0"] [blk [] .unwindResume]

def fUnwindBody : CapturedMir :=
  mkBody "w::funw" 0 [u32Decl "_0"] [blk [] (.tailCall (fnItem "w::gunw") [])]

/-- `gunw` with an ABI that can unwind (the same `w::gunw` def path). -/
def gUnwindBodyU : CapturedMir :=
  { gUnwindBody with fnAbi := { wFnAbi with canUnwind := true } }

/-- `fn maincu() -> u32 { _0 = funw() -> normal bb1, unwind cleanup bb2 }`: nested caller with a
cleanup landing pad (`bb2`), catching an unwind from an unwinding tail-callee while a
non-unwinding tail-callee narrows the inherited action to `.unreachable` (UB). -/
def mainCatchUnwindBody : CapturedMir :=
  mkBody "w::maincu" 0 [u32Decl "_0"]
    [blk [] (.call (fnItem "w::funw") [] (lc 0) (some 1) (.cleanup 2)),
     blk [] .return_,
     { statements := [assignU32 0 99], terminator := { kind := .return_, span := "w" },
       isCleanup := true }]

/-- **LeanMiri witnesses (unwinding out of a tail-callee).** `main` (root) below `f`, which
returns into `bb1` and keeps unwinding (`continue_`). After `f` tail-calls a non-unwinding
`g`, an unwind out of `g` is UB ("unwinding past a frame that does not allow unwinding");
had `g` kept the inherited `continue_` it would keep unwinding into `main`, and a
`cleanup bb4` action resumes the caller at `bb4`; `UnwindResume` outside a cleanup block is
an invalid program; and at a 1-frame modular root
(`[lmFrame "w::funw" (.goto (some 3) .continue_)]`) Miri faults with UB "unwinding past the
topmost stack frame". Trusted's root tail call `funw → gunw` into the **non-unwinding** `gunw`
now faults with UB as well (the tail call lowered the root unwind ceiling), whereas into an
unwinding `gunw` it halts with `.halted .panic` (the modular-root modeling choice); under a
nested caller `maincu` with `.cleanup 2`, `funw → gunw` (non-unwinding) likewise faults with UB
instead of jumping to `bb2`, whereas `funw → gunwU` (unwinding) resumes `maincu`'s cleanup pad
`bb2`; an external tail-callee's panic resumes the same way: `.halted .panic` under a
may-unwind ABI and an intact ceiling, UB under a no-unwind ABI or a lowered ceiling. -/
theorem tailCall_leanMiri_witness_unwind :
    LeanMiri.evalTailCallTerminator "w::g" 1 1
        (⟨[lmFrame "w::main" (.stop false), lmFrame "w::f" (.goto (some 1) .continue_)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) { nounwindAs := some .unreachable } =
      .ok ⟨[lmFrame "w::main" (.stop false), lmFrame "w::g" (.goto (some 1) .unreachable)], ()⟩ ∧
    LeanMiri.unwindResume
        (⟨[lmFrame "w::main" (.stop false), lmFrame "w::g" (.goto (some 1) .unreachable)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) =
      .error (.undefinedBehavior "unwinding past a frame that does not allow unwinding") ∧
    LeanMiri.unwindResume
        (⟨[lmFrame "w::main" (.stop false), lmFrame "w::g" (.goto (some 1) .continue_)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) = .ok .continueUnwinding ∧
    LeanMiri.unwindResume
        (⟨[lmFrame "w::main" (.stop false), lmFrame "w::g" (.goto (some 1) (.cleanup 4))], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) = .ok (.cleanup 4) ∧
    LeanMiri.unwindResume
        (⟨[lmFrame "w::main" (.stop false), lmFrame "w::g" (.goto (some 1) .continue_)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) (isCleanup := false) =
      .error (.invalidProgram "return/unwind cleanup assertion failed") ∧
    LeanMiri.unwindResume
        (⟨[lmFrame "w::gunw" (.goto (some 3) .continue_)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) =
      .error (.undefinedBehavior "unwinding past the topmost stack frame") ∧
    execN fUnwindBody 2
        (.running (initMachineStateWithCallees fUnwindBody [] [gUnwindBody])) =
      some (.faulted .ub) ∧
    execN fUnwindBody 2
        (.running (initMachineStateWithCallees fUnwindBody [] [gUnwindBodyU])) =
      some (.halted .panic) ∧
    execN mainCatchUnwindBody 3
        (.running (initMachineStateWithCallees mainCatchUnwindBody [] [fUnwindBody, gUnwindBody])) =
      some (.faulted .ub) ∧
    haltedVal? (execN mainCatchUnwindBody 5
        (.running (initMachineStateWithCallees mainCatchUnwindBody []
          [fUnwindBody, gUnwindBodyU]))) =
      some (.scalar ⟨99, 4⟩) ∧
    resumeExternalTailCallWithAbi true (some true)
        (.panicked (initMachineState fExtBody [.scalar ⟨7, 4⟩]).memory) =
      .halted .panic ∧
    resumeExternalTailCallWithAbi true (some false)
        (.panicked (initMachineState fExtBody [.scalar ⟨7, 4⟩]).memory) =
      .faulted .ub ∧
    resumeExternalTailCallWithAbi false (some true)
        (.panicked (initMachineState fExtBody [.scalar ⟨7, 4⟩]).memory) =
      .faulted .ub :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The borrow table of a running state. -/
def borrowsOf? : Option MirExecState → Option (List BorrowEntry)
  | some (.running s) => some s.memory.borrows
  | _ => none

/-- The active body (`none` for the root body) and program counter of a running state. -/
def activeAt? : Option MirExecState → Option (Option DefPath × Nat × Nat)
  | some (.running s) =>
    some (s.memory.activeCallee.map (·.defPath), s.frame.blockIdx, s.frame.stmtIdx)
  | _ => none

/-- **Resolved correspondence (dangling tail-caller local; formerly the Trusted soundness gap
`DIV-TR-TAILCALL-DANGLING-CALLER-LOCAL`).** `fdangle` passes `p = &raw mut x` (borrow tag `1`
of its own local `_2 = x`) to the tail-callee `gread`, which reads `*p`. After `fdangle`'s
four statements `p`'s borrow is live (`unique`). Trusted's tail call now tears `fdangle`'s
frame down before entering `gread` (`tailCall_leanMiri_cleanup_frees_caller_locals`): after
it the stack is still empty (depth `0`), `gread` runs at `bb0[0]`, and `p`'s borrow is
`disabled` and `allocDead` — so `gread`'s first statement, the `*p` read, faults with UB
instead of silently reading `gread`'s own `_2 = 137`. Miri's tail call cleans up the popped
`goto` frame, deallocating its memory-backed locals — `x` included — so `*p` is a
use-after-free (UB) there too: both references reject the program at the same read. -/
theorem tailCall_witness_dangling_caller_local_simulation :
    borrowsOf? (execN fDangleBody 4
        (.running (initMachineStateWithCallees fDangleBody [] [gReadBody]))) =
      some [{ tag := 1, targetLocal := 2, targetProjection := [], perm := .unique }] ∧
    depth? (execN fDangleBody 5
        (.running (initMachineStateWithCallees fDangleBody [] [gReadBody]))) = some 0 ∧
    activeAt? (execN fDangleBody 5
        (.running (initMachineStateWithCallees fDangleBody [] [gReadBody]))) =
      some (some "w::gread", 0, 0) ∧
    borrowsOf? (execN fDangleBody 5
        (.running (initMachineStateWithCallees fDangleBody [] [gReadBody]))) =
      some [{ tag := 1, targetLocal := 2, targetProjection := [], perm := .disabled,
              allocDead := true }] ∧
    execN fDangleBody 6 (.running (initMachineStateWithCallees fDangleBody [] [gReadBody])) =
      some (.faulted .ub) ∧
    LeanMiri.evalTailCallTerminator "w::gread" 2 2
        (⟨[lmFrame "w::fdangle" (.goto (some 3) .continue_)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) =
      .ok ⟨[lmFrame "w::gread" (.goto (some 3) .continue_)], ()⟩ ∧
    LeanMiri.cleanupDeallocatesLocals
      (lmFrame "w::fdangle" (.goto (some 3) .continue_)).returnContinuation = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Typed statement pin of the dangling tail-caller-local resolution. -/
example :
    borrowsOf? (execN fDangleBody 4
        (.running (initMachineStateWithCallees fDangleBody [] [gReadBody]))) =
      some [{ tag := 1, targetLocal := 2, targetProjection := [], perm := .unique }] ∧
    depth? (execN fDangleBody 5
        (.running (initMachineStateWithCallees fDangleBody [] [gReadBody]))) = some 0 ∧
    activeAt? (execN fDangleBody 5
        (.running (initMachineStateWithCallees fDangleBody [] [gReadBody]))) =
      some (some "w::gread", 0, 0) ∧
    borrowsOf? (execN fDangleBody 5
        (.running (initMachineStateWithCallees fDangleBody [] [gReadBody]))) =
      some [{ tag := 1, targetLocal := 2, targetProjection := [], perm := .disabled,
              allocDead := true }] ∧
    execN fDangleBody 6 (.running (initMachineStateWithCallees fDangleBody [] [gReadBody])) =
      some (.faulted .ub) ∧
    LeanMiri.evalTailCallTerminator "w::gread" 2 2
        (⟨[lmFrame "w::fdangle" (.goto (some 3) .continue_)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) =
      .ok ⟨[lmFrame "w::gread" (.goto (some 3) .continue_)], ()⟩ ∧
    LeanMiri.cleanupDeallocatesLocals
      (lmFrame "w::fdangle" (.goto (some 3) .continue_)).returnContinuation = true :=
  tailCall_witness_dangling_caller_local_simulation

/-- `fn fcr(p: *mut u32) -> u32 { become gread(copy p, 137) }`: a modular root with two
locals that tail-calls the three-local `gread`. -/
def fCrBody : CapturedMir :=
  mkBody "w::fcr" 1 [u32Decl "_0", ptrDecl "p"]
    [blk [] (.tailCall (fnItem "w::gread") [.copy (lc 1), cU32 137])]

/-- `fn frd(p: *mut u32) -> u32 { _0 = copy (*p); return }`: the same read without a tail
call. -/
def fRdBody : CapturedMir :=
  mkBody "w::frd" 1 [u32Decl "_0", ptrDecl "p"]
    [blk [st (.assign (lc 0) (.use (.copy ⟨1, [.deref]⟩)))] .return_]

/-- The modular root's external caller owns `*p = 42`: Trusted addresses it as the
caller-owned referent slot `2` of depth `0` (`≥` the root's two locals), borrowed by tag `1`. -/
def crMem : Memory :=
  { callees := [gReadBody], callerLocals := [.uninit, .uninit, .init (.scalar ⟨42, 4⟩)],
    borrows := [{ tag := 1, targetLocal := 2, targetProjection := [], perm := .unique }],
    nextTag := 2 }

/-- The caller-owned referent slots (`callerLocals`) of a running state. -/
def callerLocalsOf? : Option MirExecState → Option (List LocalSlot)
  | some (.running s) => some s.memory.callerLocals
  | _ => none

/-- `fn gmid(p: *mut u32) -> u32 { become gread(copy p, 137) }` (two locals, tail-calling the
three-local `gread`). -/
def gMidBody : CapturedMir :=
  mkBody "w::gmid" 1 [u32Decl "_0", ptrDecl "p"]
    [blk [] (.tailCall (fnItem "w::gread") [.copy (lc 1), cU32 137])]

/-- `fn fdangle2() -> u32 { let mut x = 42; let p = &raw mut x; become gmid(p) }`
(`_1 = p`, `_2 = x`): the root's own local `x` dies with the first tail call; the second tail
call (`gmid → gread`) widens the root frame from two to three locals. -/
def fDangle2Body : CapturedMir :=
  mkBody "w::fdangle2" 0 [u32Decl "_0", ptrDecl "p", u32Decl "x"]
    [blk [st (.storageLive 1), st (.storageLive 2), assignU32 2 42,
          st (.assign (lc 1) (.rawPtr .mut (lc 2)))]
      (.tailCall (fnItem "w::gmid") [.copy (lc 1)])]

/-- `fn gfin(p: *mut u32, q: *mut u32) -> u32 { let c = 500; _0 = copy (*_readLocal); return }`
with seven locals (`_5 = c`). -/
def gFinBody (readLocal : Nat) : CapturedMir :=
  mkBody "w::gfin" 2
    [u32Decl "_0", ptrDecl "p", ptrDecl "q", u32Decl "a", u32Decl "b", u32Decl "c", u32Decl "d"]
    [blk [st (.storageLive 5), assignU32 5 500,
          st (.assign (lc 0) (.use (.copy ⟨readLocal, [.deref]⟩)))] .return_]

/-- `fn gmid2(p: *mut u32, q: *mut u32) -> u32 { become gfin(copy p, copy q) }` (three
locals). -/
def gMid2Body : CapturedMir :=
  mkBody "w::gmid2" 2 [u32Decl "_0", ptrDecl "p", ptrDecl "q"]
    [blk [] (.tailCall (fnItem "w::gfin") [.copy (lc 1), .copy (lc 2)])]

/-- `fn fmix(p: *mut u32) -> u32 { let mut x = 7; let q = &raw mut x; become gmid2(p, q) }`
with five locals (`_0`, `p`, `q`, a pad, `_4 = x`). -/
def fMixBody : CapturedMir :=
  mkBody "w::fmix" 1 [u32Decl "_0", ptrDecl "p", ptrDecl "q", u32Decl "pad", u32Decl "x"]
    [blk [st (.storageLive 2), st (.storageLive 3), st (.storageLive 4), assignU32 4 7,
          st (.assign (lc 2) (.rawPtr .mut (lc 4)))]
      (.tailCall (fnItem "w::gmid2") [.copy (lc 1), .copy (lc 2)])]

/-- The external caller of `fmix` owns `*p = 42` at the depth-`0` slot `5` (past `fmix`'s five
locals), borrowed by tag `1`; `gfin` reads through its local `readLocal`. -/
def mixMem (readLocal : Nat) : Memory :=
  { callees := [gMid2Body, gFinBody readLocal],
    callerLocals := [.uninit, .uninit, .uninit, .uninit, .uninit, .init (.scalar ⟨42, 4⟩)],
    borrows := [{ tag := 1, targetLocal := 5, targetProjection := [], perm := .unique }],
    nextTag := 2 }

/-- **Resolved correspondence (root tail call keeps a caller-owned referent live; formerly the
Trusted soundness gap `DIV-TR-TAILCALL-ROOT-CALLER-REFERENT-SHADOW`).** At a modular root,
Trusted addresses the external caller's memory as depth-`0` slots *above* the root's own
locals. A root tail call into a callee with *more* locals now relocates every **live**
caller-owned referent past the callee's frame (`relocateRootCallerReferents`: the borrow's
`targetLocal` and the `callerLocals` slots shift by the frame growth), so the callee's own
slots no longer shadow it: `frd(p)` reads the caller's `*p = 42`, and `fcr(p)`, which
tail-calls `gread(p, 137)`, now returns `42` too — after the tail call `p`'s borrow names slot
`3` (past `gread`'s three locals) and `callerLocals` is padded by one dead slot — where it
formerly read `gread`'s own `_2 = 137`. In Miri the tail call pops only `fcr`'s frame and the
caller's allocation stays live, so `*p` reads `42`: both references agree.

**Negative guard (`!entry.allocDead`).** Only *live* referents are relocated. A borrow of the
root's *own* local that an earlier tail call tore down (`fdangle2 → gmid`, dead borrow of slot
`2`) stays put — disabled and dead — when the next tail call (`gmid → gread`) widens the frame
past it, so `*p` is still UB. In the mixed chain `fmix → gmid2 → gfin`, the dead borrow of
`fmix`'s own `x` (slot `4`) stays at slot `4`, while the live caller-owned referent moves
`5 → 9` past `gfin`'s seven locals: reading through `p` yields the caller's `42` (not `gfin`'s
own `_5 = 500`), and reading through `q` is UB. -/
theorem tailCall_witness_root_caller_referent_simulation :
    haltedVal? (execN fRdBody 2
        (.running (Trusted.VerificationResult.initMachineStateWithMemory fRdBody
          [.ptr ⟨1, 0⟩ 8] crMem))) = some (.scalar ⟨42, 4⟩) ∧
    activeAt? (execN fCrBody 1
        (.running (Trusted.VerificationResult.initMachineStateWithMemory fCrBody
          [.ptr ⟨1, 0⟩ 8] crMem))) = some (some "w::gread", 0, 0) ∧
    borrowsOf? (execN fCrBody 1
        (.running (Trusted.VerificationResult.initMachineStateWithMemory fCrBody
          [.ptr ⟨1, 0⟩ 8] crMem))) =
      some [{ tag := 1, targetLocal := 3, targetProjection := [], perm := .unique }] ∧
    callerLocalsOf? (execN fCrBody 1
        (.running (Trusted.VerificationResult.initMachineStateWithMemory fCrBody
          [.ptr ⟨1, 0⟩ 8] crMem))) =
      some [.dead, .uninit, .uninit, .init (.scalar ⟨42, 4⟩)] ∧
    haltedVal? (execN fCrBody 3
        (.running (Trusted.VerificationResult.initMachineStateWithMemory fCrBody
          [.ptr ⟨1, 0⟩ 8] crMem))) = some (.scalar ⟨42, 4⟩) ∧
    LeanMiri.evalTailCallTerminator "w::gread" 2 2
        (⟨[lmFrame "w::fcr" (.goto (some 3) .continue_)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) { nounwindAs := some .unreachable } =
      .ok ⟨[lmFrame "w::gread" (.goto (some 3) .unreachable)], ()⟩ ∧
    activeAt? (execN fDangle2Body 6
        (.running (initMachineStateWithCallees fDangle2Body [] [gMidBody, gReadBody]))) =
      some (some "w::gread", 0, 0) ∧
    borrowsOf? (execN fDangle2Body 6
        (.running (initMachineStateWithCallees fDangle2Body [] [gMidBody, gReadBody]))) =
      some [{ tag := 1, targetLocal := 2, targetProjection := [], perm := .disabled,
              allocDead := true }] ∧
    execN fDangle2Body 7
        (.running (initMachineStateWithCallees fDangle2Body [] [gMidBody, gReadBody])) =
      some (.faulted .ub) ∧
    borrowsOf? (execN fMixBody 7
        (.running (Trusted.VerificationResult.initMachineStateWithMemory fMixBody
          [.ptr ⟨1, 0⟩ 8] (mixMem 1)))) =
      some [{ tag := 2, targetLocal := 4, targetProjection := [], perm := .disabled,
              allocDead := true },
            { tag := 1, targetLocal := 9, targetProjection := [], perm := .unique }] ∧
    haltedVal? (execN fMixBody 11
        (.running (Trusted.VerificationResult.initMachineStateWithMemory fMixBody
          [.ptr ⟨1, 0⟩ 8] (mixMem 1)))) = some (.scalar ⟨42, 4⟩) ∧
    execN fMixBody 10
        (.running (Trusted.VerificationResult.initMachineStateWithMemory fMixBody
          [.ptr ⟨1, 0⟩ 8] (mixMem 2))) =
      some (.faulted .ub) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Typed statement pin of the resolved root caller-referent correspondence
(`DIV-TR-TAILCALL-ROOT-CALLER-REFERENT-SHADOW`). -/
example :
    haltedVal? (execN fRdBody 2
        (.running (Trusted.VerificationResult.initMachineStateWithMemory fRdBody
          [.ptr ⟨1, 0⟩ 8] crMem))) = some (.scalar ⟨42, 4⟩) ∧
    activeAt? (execN fCrBody 1
        (.running (Trusted.VerificationResult.initMachineStateWithMemory fCrBody
          [.ptr ⟨1, 0⟩ 8] crMem))) = some (some "w::gread", 0, 0) ∧
    borrowsOf? (execN fCrBody 1
        (.running (Trusted.VerificationResult.initMachineStateWithMemory fCrBody
          [.ptr ⟨1, 0⟩ 8] crMem))) =
      some [{ tag := 1, targetLocal := 3, targetProjection := [], perm := .unique }] ∧
    callerLocalsOf? (execN fCrBody 1
        (.running (Trusted.VerificationResult.initMachineStateWithMemory fCrBody
          [.ptr ⟨1, 0⟩ 8] crMem))) =
      some [.dead, .uninit, .uninit, .init (.scalar ⟨42, 4⟩)] ∧
    haltedVal? (execN fCrBody 3
        (.running (Trusted.VerificationResult.initMachineStateWithMemory fCrBody
          [.ptr ⟨1, 0⟩ 8] crMem))) = some (.scalar ⟨42, 4⟩) ∧
    LeanMiri.evalTailCallTerminator "w::gread" 2 2
        (⟨[lmFrame "w::fcr" (.goto (some 3) .continue_)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) { nounwindAs := some .unreachable } =
      .ok ⟨[lmFrame "w::gread" (.goto (some 3) .unreachable)], ()⟩ ∧
    activeAt? (execN fDangle2Body 6
        (.running (initMachineStateWithCallees fDangle2Body [] [gMidBody, gReadBody]))) =
      some (some "w::gread", 0, 0) ∧
    borrowsOf? (execN fDangle2Body 6
        (.running (initMachineStateWithCallees fDangle2Body [] [gMidBody, gReadBody]))) =
      some [{ tag := 1, targetLocal := 2, targetProjection := [], perm := .disabled,
              allocDead := true }] ∧
    execN fDangle2Body 7
        (.running (initMachineStateWithCallees fDangle2Body [] [gMidBody, gReadBody])) =
      some (.faulted .ub) ∧
    borrowsOf? (execN fMixBody 7
        (.running (Trusted.VerificationResult.initMachineStateWithMemory fMixBody
          [.ptr ⟨1, 0⟩ 8] (mixMem 1)))) =
      some [{ tag := 2, targetLocal := 4, targetProjection := [], perm := .disabled,
              allocDead := true },
            { tag := 1, targetLocal := 9, targetProjection := [], perm := .unique }] ∧
    haltedVal? (execN fMixBody 11
        (.running (Trusted.VerificationResult.initMachineStateWithMemory fMixBody
          [.ptr ⟨1, 0⟩ 8] (mixMem 1)))) = some (.scalar ⟨42, 4⟩) ∧
    execN fMixBody 10
        (.running (Trusted.VerificationResult.initMachineStateWithMemory fMixBody
          [.ptr ⟨1, 0⟩ 8] (mixMem 2))) =
      some (.faulted .ub) :=
  tailCall_witness_root_caller_referent_simulation

end TailCall

/-! ## 3. `ProjectionElem.opaqueCast` -/

section OpaqueCast

/-- Erase every `.opaqueCast` projection, at any depth. -/
def eraseOpaqueCasts : List ProjectionElem → List ProjectionElem
  | [] => []
  | .opaqueCast _ :: rest => eraseOpaqueCasts rest
  | .deref :: rest => .deref :: eraseOpaqueCasts rest
  | .field i t :: rest => .field i t :: eraseOpaqueCasts rest
  | .index l :: rest => .index l :: eraseOpaqueCasts rest
  | .constantIndex o m e :: rest => .constantIndex o m e :: eraseOpaqueCasts rest
  | .subslice a b e :: rest => .subslice a b e :: eraseOpaqueCasts rest
  | .downcast n v :: rest => .downcast n v :: eraseOpaqueCasts rest
  | .unwrapUnsafeBinder t :: rest => .unwrapUnsafeBinder t :: eraseOpaqueCasts rest

set_option linter.unusedSimpArgs false in
private theorem readProjectedValue_erase (locals : List LocalSlot) :
    ∀ (p : List ProjectionElem) (v : Value),
      readProjectedValue locals v p = readProjectedValue locals v (eraseOpaqueCasts p)
  | [], _ => rfl
  | e :: rest, v => by
    have ih := readProjectedValue_erase locals rest
    cases e with
    | field f ty => cases f <;> cases v <;> simp only [readProjectedValue, eraseOpaqueCasts, ih]
    | index l =>
      cases v with
      | aggregate vi fs => cases vi <;> simp only [readProjectedValue, eraseOpaqueCasts, ih]
      | _ => simp only [readProjectedValue, eraseOpaqueCasts, ih]
    | constantIndex o m fe =>
      cases v with
      | aggregate vi fs =>
        cases vi
        · unfold readProjectedValue
          simp only [eraseOpaqueCasts, ih]
        · simp only [readProjectedValue, eraseOpaqueCasts]
      | _ => simp only [readProjectedValue, eraseOpaqueCasts]
    | subslice a b fe =>
      cases v with
      | aggregate vi fs => cases vi <;> simp only [readProjectedValue, eraseOpaqueCasts, ih]
      | _ => simp only [readProjectedValue, eraseOpaqueCasts, ih]
    | _ => cases v <;> simp only [readProjectedValue, eraseOpaqueCasts, ih]

set_option linter.unusedSimpArgs false in
private theorem writeProjectedValue_erase (locals : List LocalSlot) :
    ∀ (p : List ProjectionElem) (v nv : Value),
      writeProjectedValue locals v p nv = writeProjectedValue locals v (eraseOpaqueCasts p) nv
  | [], _, _ => rfl
  | e :: rest, v, nv => by
    have ih := writeProjectedValue_erase locals rest
    cases e with
    | field f ty => cases f <;> cases v <;> simp only [writeProjectedValue, eraseOpaqueCasts, ih]
    | index l =>
      cases v with
      | aggregate vi fs => cases vi <;> simp only [writeProjectedValue, eraseOpaqueCasts, ih]
      | _ => simp only [writeProjectedValue, eraseOpaqueCasts, ih]
    | constantIndex o m fe =>
      cases v with
      | aggregate vi fs =>
        cases vi
        · unfold writeProjectedValue
          simp only [eraseOpaqueCasts, ih]
        · simp only [writeProjectedValue, eraseOpaqueCasts]
      | _ => simp only [writeProjectedValue, eraseOpaqueCasts]
    | subslice a b fe =>
      cases v with
      | aggregate vi fs => cases vi <;> simp only [writeProjectedValue, eraseOpaqueCasts, ih]
      | _ => simp only [writeProjectedValue, eraseOpaqueCasts, ih]
    | _ => cases v <;> simp only [writeProjectedValue, eraseOpaqueCasts, ih]

/-- **Trusted value traversal (universal).** `.opaqueCast` is value-transparent for every
value, cast type, and projection tail — for reads and for writes — and erasing *all*
opaque casts, at any depth of a nested projection, never changes a read or a write
(success, UB, or unsupported). -/
theorem opaqueCast_trusted_traversal_universal (locals : List LocalSlot) (v nv : Value)
    (t : Ty) (rest : List ProjectionElem) :
    readProjectedValue locals v (.opaqueCast t :: rest) = readProjectedValue locals v rest ∧
      writeProjectedValue locals v (.opaqueCast t :: rest) nv =
        writeProjectedValue locals v rest nv ∧
      (∀ p : List ProjectionElem,
        readProjectedValue locals v p = readProjectedValue locals v (eraseOpaqueCasts p)) ∧
      (∀ p : List ProjectionElem,
        writeProjectedValue locals v p nv = writeProjectedValue locals v (eraseOpaqueCasts p) nv) := by
  refine ⟨?_, ?_, fun p => readProjectedValue_erase locals p v,
    fun p => writeProjectedValue_erase locals p v nv⟩ <;>
    cases v <;> rfl

/-- **Trusted typing (universal).** `.opaqueCast castTy` is *type-switching*: projected-type
resolution, the union-aware readers/writers, and the borrow-invalidation path truncation
(`truncateTyProjAtUnion`) all continue at the cast type (resolved through the local
declarations), independently of the base type — so erasure is value-sound but not
type-sound, and the union-aware paths see the revealed concrete type. -/
theorem opaqueCast_trusted_retype_universal (locals : List LocalSlot) (decls : List LocalDecl)
    (layouts : LayoutTable) (v nv : Value) (baseTy baseTy' t : Ty) (rest : List ProjectionElem) :
    resolveProjectedTy layouts baseTy (.opaqueCast t :: rest) = resolveProjectedTy layouts t rest ∧
      resolveProjectedTy layouts baseTy (.opaqueCast t :: rest) =
        resolveProjectedTy layouts baseTy' (.opaqueCast t :: rest) ∧
      readProjectedValueUnionAware locals decls layouts v baseTy (.opaqueCast t :: rest) =
        readProjectedValueUnionAware locals decls layouts v
          (resolveTyWithLocalDecls decls layouts t) rest ∧
      writeProjectedValueUnionAware locals decls layouts v baseTy (.opaqueCast t :: rest) nv =
        writeProjectedValueUnionAware locals decls layouts v
          (resolveTyWithLocalDecls decls layouts t) rest nv ∧
      truncateTyProjAtUnion decls layouts baseTy (.opaqueCast t :: rest) =
        .opaqueCast t ::
          truncateTyProjAtUnion decls layouts (resolveTyWithLocalDecls decls layouts t) rest := by
  refine ⟨rfl, rfl, ?_, ?_, rfl⟩
  · cases v with
    | uninit => simp only [readProjectedValueUnionAware]
    | _ => rfl
  · cases v <;> rfl

private theorem strip_erase : ∀ p : List ProjectionElem,
    stripTransparentProjections (eraseOpaqueCasts p) = stripTransparentProjections p
  | [] => rfl
  | e :: rest => by
    have ih := strip_erase rest
    cases e <;> simp only [eraseOpaqueCasts, stripTransparentProjections, ih]

/-- **Trusted aliasing (universal).** Sub-place overlap — and therefore every borrow
invalidation and protector conflict decided through `projectionsOverlap` — ignores opaque
casts on either side and at any depth: a write through `(_l as T).f` conflicts with
exactly the borrows that a write through `_l.f` conflicts with. -/
theorem opaqueCast_trusted_overlap_universal (t : Ty) (p q : List ProjectionElem) :
    stripTransparentProjections (.opaqueCast t :: p) = stripTransparentProjections p ∧
      projectionsOverlap (.opaqueCast t :: p) q = projectionsOverlap p q ∧
      projectionsOverlap q (.opaqueCast t :: p) = projectionsOverlap q p ∧
      stripTransparentProjections (eraseOpaqueCasts p) = stripTransparentProjections p ∧
      projectionsOverlap (eraseOpaqueCasts p) q = projectionsOverlap p q ∧
      projectionsOverlap q (eraseOpaqueCasts p) = projectionsOverlap q p := by
  refine ⟨rfl, rfl, rfl, strip_erase p, ?_, ?_⟩ <;>
    simp only [projectionsOverlap, strip_erase]

/-- **Trusted place reads (universal).** On a non-union place, `copy (_l as T).rest` reads
exactly what `copy _l.rest` reads (including the UB of an uninitialized or dead root),
whenever `rest` does not start with a dereference. An opaque cast directly *before* a
dereference is not traversed: the read fails closed with `.unsupported` (never a silent
value). -/
theorem opaqueCast_trusted_place_read_universal (locals : List LocalSlot) (l : Nat) (t : Ty)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (decls : List LocalDecl) :
    (∀ (e : ProjectionElem) (r : List ProjectionElem), (∀ r', e :: r ≠ .deref :: r') →
      placeTouchesUnion decls layouts ⟨l, .opaqueCast t :: e :: r⟩ = false →
      placeTouchesUnion decls layouts ⟨l, e :: r⟩ = false →
      evalOperand locals (.copy ⟨l, .opaqueCast t :: e :: r⟩) borrows globals layouts
          callerLocals decls =
        evalOperand locals (.copy ⟨l, e :: r⟩) borrows globals layouts callerLocals decls) ∧
    (placeTouchesUnion decls layouts ⟨l, [.opaqueCast t]⟩ = false →
      evalOperand locals (.copy ⟨l, [.opaqueCast t]⟩) borrows globals layouts callerLocals decls =
        evalOperand locals (.copy ⟨l, []⟩) borrows globals layouts callerLocals decls) ∧
    (∀ (v : Value) (r : List ProjectionElem), get? locals l = some (.init v) →
      placeTouchesUnion decls layouts ⟨l, .opaqueCast t :: .deref :: r⟩ = false →
      evalOperand locals (.copy ⟨l, .opaqueCast t :: .deref :: r⟩) borrows globals layouts
          callerLocals decls = .unsupported) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e r hnd hu hu'
    have hread : ∀ v, readProjectedValue locals v (.opaqueCast t :: e :: r) =
        readProjectedValue locals v (e :: r) := fun v =>
      (opaqueCast_trusted_traversal_universal locals v v t (e :: r)).1
    cases e with
    | deref => exact absurd rfl (hnd r)
    | _ =>
      simp only [evalOperand, hu, hu', hread]
  · intro hu
    have hread : ∀ v, readProjectedValue locals v [.opaqueCast t] =
        readProjectedValue locals v [] := fun v =>
      (opaqueCast_trusted_traversal_universal locals v v t []).1
    simp only [evalOperand, hu, hread]
  · intro v r hv hu
    have hread : readProjectedValue locals v (.opaqueCast t :: .deref :: r) = .unsupported := by
      rw [(opaqueCast_trusted_traversal_universal locals v v t (.deref :: r)).1]
      cases v <;> rfl
    simp only [evalOperand, hu, hv, hread]

/-- **Trusted place typing, offset, union, and shell helpers (universal).** `.opaqueCast t`
switches the static type in `placeTy`, `resolveProjectedTyResolved`, `placeTyResolved`,
`projectionChainByteOffset?` (also clearing `activeVariant`), `tyProjTouchesUnion`,
`checkStaticSubProjBounds`, and `wrapFullWidthInitChain?` to `t` (resolved through
`localDecls` / `layouts`); it is transparent in `isScalarCompatibleProj`,
`subsliceChainValidOnVal`, `splitLastDeref?`, `ensureNestedFieldShells`, and
`fieldShellChainPopulated`; and at the head of an assignment into an `.uninit` local,
`uninitFieldWriteShell?` looks through the leading opaque casts (`stripLeadingOpaqueCast`): a
cast chain followed by a field step materializes exactly the shell of the cast-erased field
write, at the declarations with the local retyped to the effective cast type
(`eraseLeadingOpaqueCastDecls`), while a pure cast chain has no field shell (`none`; the
statement is dispatched as a whole-local write,
`opaqueCast_trusted_root_dispatch_simulation`). -/
theorem opaqueCast_trusted_placeTy_and_helpers_universal
    (locals : List LocalSlot) (decls : List LocalDecl) (layouts : LayoutTable)
    (l : Nat) (decl : LocalDecl) (baseTy t : Ty) (v leafVal : Value)
    (curTyOpt : Option Ty) (curValOpt : Option Value) (activeVariant : Option VariantIdx)
    (accOff : Nat) (nextProj : ProjectionElem) (rest : List ProjectionElem)
    (hdecl : get? decls l = some decl) :
    placeTy decls layouts ⟨l, .opaqueCast t :: rest⟩ = resolveProjectedTy layouts t rest ∧
      resolveProjectedTyResolved decls layouts baseTy (.opaqueCast t :: rest) =
        resolveProjectedTyResolved decls layouts (resolveTyWithLocalDecls decls layouts t) rest ∧
      placeTyResolved decls layouts ⟨l, .opaqueCast t :: rest⟩ =
        resolveProjectedTyResolved decls layouts (resolveTyWithLocalDecls decls layouts t) rest ∧
      projectionChainByteOffset? layouts curTyOpt curValOpt activeVariant accOff decls
          (.opaqueCast t :: rest) =
        projectionChainByteOffset? layouts (some (resolveTyWithLocalDecls decls layouts t))
          curValOpt none accOff decls rest ∧
      tyProjTouchesUnion decls layouts baseTy (.opaqueCast t :: rest) =
        tyProjTouchesUnion decls layouts (resolveTyWithLocalDecls decls layouts t) rest ∧
      checkStaticSubProjBounds decls layouts baseTy (.opaqueCast t :: rest) =
        checkStaticSubProjBounds decls layouts (resolveTyWithLocalDecls decls layouts t) rest ∧
      wrapFullWidthInitChain? decls layouts baseTy (.opaqueCast t :: rest) leafVal =
        wrapFullWidthInitChain? decls layouts (resolveTyWithLocalDecls decls layouts t)
          rest leafVal ∧
      isScalarCompatibleProj (.opaqueCast t :: rest) = isScalarCompatibleProj rest ∧
      subsliceChainValidOnVal locals v (.opaqueCast t :: rest) =
        subsliceChainValidOnVal locals v rest ∧
      splitLastDeref? (.opaqueCast t :: rest) = splitLastDeref? rest ∧
      ensureNestedFieldShells v (.opaqueCast t :: nextProj :: rest) =
        ensureNestedFieldShells v (nextProj :: rest) ∧
      fieldShellChainPopulated v (.opaqueCast t :: nextProj :: rest) =
        fieldShellChainPopulated v (nextProj :: rest) ∧
      (∀ (i : FieldIdx) (ft : Ty) (fr : List ProjectionElem),
        stripLeadingOpaqueCast rest = .field i ft :: fr →
        uninitFieldWriteShell? decls layouts l (.opaqueCast t) rest =
          uninitFieldWriteShell?
            (eraseLeadingOpaqueCastDecls decls layouts l (.opaqueCast t :: rest)) layouts l
            (.field i ft) fr) ∧
      (stripLeadingOpaqueCast rest = [] →
        uninitFieldWriteShell? decls layouts l (.opaqueCast t) rest = none) := by
  refine ⟨?_, rfl, ?_, rfl, rfl, rfl, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · simp [placeTy, hdecl, resolveProjectedTy]
  · simp [placeTyResolved, hdecl, resolveProjectedTyResolved]
  · cases v <;> rfl
  · cases v <;> rfl
  · cases v <;> rfl
  · intro i ft fr hs
    simp only [uninitFieldWriteShell?, hs]
  · intro hs
    simp only [uninitFieldWriteShell?, hs]


set_option linter.unusedSimpArgs false in
/-- **Trusted `evalPlaceRead`, `writePlaceValue`, `evalPlaceWrite`, and
`resolveBorrowWriteLocalProj` (universal).** On non-union places with `e ≠ .deref`,
`evalPlaceRead`, `writePlaceValue`, and `evalPlaceWrite` (with any active protectors)
through `.opaqueCast t :: e :: r` agree with `e :: r` when `decls = []` (or when `placeTy` /
`placeTyResolved` agrees); a write through a pure cast chain
(`stripLeadingOpaqueCast r = []`) is the write of the whole local `_l` (so it initializes an
`.uninit` local, like its post-borrowck erasure); a write through a cast chain followed by a
non-deref projection into an `.uninit` or `.dead` local faults with `.ub`, and before a
`.deref` on an initialized non-union local fails closed with `.unsupported`;
and `resolveBorrowWriteLocalProj` preserves `.opaqueCast t` in
front of the resolved path on non-union or zero-sized places (so `stripTransparentProjections`
agrees with the cast-free path) while truncating at the enclosing union under `t` on
non-ZST union writes. -/
theorem opaqueCast_trusted_write_and_borrow_universal
    (locals : List LocalSlot) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (decls : List LocalDecl)
    (activeProtectors : List Nat) (l : Nat) (t : Ty) (val : Value) :
    (∀ (e : ProjectionElem) (r : List ProjectionElem), (∀ r', e :: r ≠ .deref :: r') →
      evalPlaceRead locals ⟨l, .opaqueCast t :: e :: r⟩ borrows globals layouts callerLocals [] =
        evalPlaceRead locals ⟨l, e :: r⟩ borrows globals layouts callerLocals [] ∧
      writePlaceValue locals borrows ⟨l, .opaqueCast t :: e :: r⟩ val [] layouts =
        writePlaceValue locals borrows ⟨l, e :: r⟩ val [] layouts ∧
      evalPlaceWrite locals borrows ⟨l, .opaqueCast t :: e :: r⟩ val activeProtectors [] layouts =
        evalPlaceWrite locals borrows ⟨l, e :: r⟩ val activeProtectors [] layouts) ∧
    (∀ (r : List ProjectionElem) (e : ProjectionElem) (r' : List ProjectionElem),
      stripLeadingOpaqueCast r = e :: r' → (∀ r'', e :: r' ≠ .deref :: r'') →
      (get? locals l = some .uninit ∨ get? locals l = some .dead ∨ get? locals l = none) →
      writePlaceValue locals borrows ⟨l, .opaqueCast t :: r⟩ val [] layouts = .ub) ∧
    (∀ (r : List ProjectionElem), stripLeadingOpaqueCast r = [] →
      writePlaceValue locals borrows ⟨l, .opaqueCast t :: r⟩ val [] layouts =
        writePlaceValue locals borrows ⟨l, []⟩ val [] layouts) ∧
    (∀ (v : Value) (r : List ProjectionElem), get? locals l = some (.init v) →
      writePlaceValue locals borrows ⟨l, .opaqueCast t :: .deref :: r⟩ val [] layouts =
        .unsupported) ∧
    (∀ (r : List ProjectionElem),
      placeTouchesUnion decls layouts ⟨l, .opaqueCast t :: r⟩ = false →
      placeTouchesUnion decls layouts ⟨l, r⟩ = false →
      resolveBorrowWriteLocalProj decls layouts locals l (.opaqueCast t :: r) =
        .opaqueCast t :: resolveBorrowWriteLocalProj decls layouts locals l r ∧
      stripTransparentProjections
          (resolveBorrowWriteLocalProj decls layouts locals l (.opaqueCast t :: r)) =
        stripTransparentProjections (resolveBorrowWriteLocalProj decls layouts locals l r)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e r hnd
    have hread : ∀ v, readProjectedValue locals v (.opaqueCast t :: e :: r) =
        readProjectedValue locals v (e :: r) := fun v =>
      (opaqueCast_trusted_traversal_universal locals v v t (e :: r)).1
    have hwrite : ∀ v, writeProjectedValue locals v (.opaqueCast t :: e :: r) val =
        writeProjectedValue locals v (e :: r) val := fun v =>
      (opaqueCast_trusted_traversal_universal locals v val t (e :: r)).2.1
    have hpty : ∀ p, placeTyResolved [] layouts p = none := fun _ => by
      simp [placeTyResolved, get?]
    have herase : ∀ q : List ProjectionElem,
        eraseLeadingOpaqueCastDecls [] layouts l q = [] := by
      intro q
      cases q with
      | nil => rfl
      | cons e' q' => cases e' <;> simp only [eraseLeadingOpaqueCastDecls, hpty]
    have hprot : ∀ (ps : List Nat) (q : List ProjectionElem),
        hasProtectedWriteConflict borrows ps l none (.opaqueCast t :: q) =
          hasProtectedWriteConflict borrows ps l none q := by
      intro ps q
      induction borrows with
      | nil => rfl
      | cons b bs ih =>
        simp only [hasProtectedWriteConflict, borrowEntryOverlapsWrite, projectionsOverlap,
          stripTransparentProjections, ih]
    have hres_er :
        (match resolveBorrowProjectionElems locals (.opaqueCast t :: e :: r) with
         | some rp => rp
         | none => .opaqueCast t :: e :: r) =
        .opaqueCast t ::
          (match resolveBorrowProjectionElems locals (e :: r) with
           | some rp => rp
           | none => e :: r) := by
      simp only [resolveBorrowProjectionElems]
      cases resolveBorrowProjectionElems locals (e :: r) <;> rfl
    have hwv :
        writePlaceValue locals borrows ⟨l, .opaqueCast t :: e :: r⟩ val [] layouts =
          writePlaceValue locals borrows ⟨l, e :: r⟩ val [] layouts := by
      cases e with
      | deref => exact absurd rfl (hnd r)
      | _ =>
        simp only [writePlaceValue, stripLeadingOpaqueCast, eraseLeadingOpaqueCastDecls, hpty,
          herase, writeProjectedForLocal, hwrite]
    refine ⟨?_, hwv, ?_⟩
    · cases e with
      | deref => exact absurd rfl (hnd r)
      | _ => simp only [evalPlaceRead, readProjectedForLocal, hpty, hread]
    · cases activeProtectors with
      | nil => exact hwv
      | cons ph pt =>
        cases e with
        | deref => exact absurd rfl (hnd r)
        | _ =>
          change
            (match hasProtectedWriteConflict borrows (ph :: pt) l none
                (match resolveBorrowProjectionElems locals (.opaqueCast t :: _ :: r) with
                 | some rp => rp
                 | none => .opaqueCast t :: _ :: r) with
             | true => PlaceWriteResult.ub
             | false =>
               writePlaceValue locals borrows ⟨l, .opaqueCast t :: _ :: r⟩ val [] layouts) =
            (match hasProtectedWriteConflict borrows (ph :: pt) l none
                (match resolveBorrowProjectionElems locals (_ :: r) with
                 | some rp => rp
                 | none => _ :: r) with
             | true => PlaceWriteResult.ub
             | false => writePlaceValue locals borrows ⟨l, _ :: r⟩ val [] layouts)
          rw [hres_er, hprot, hwv]
  · intro r e r' hs hnd hslot
    cases e with
    | deref => exact absurd rfl (hnd r')
    | _ => rcases hslot with h | h | h <;> simp only [writePlaceValue, hs, h]
  · intro r hs
    simp only [writePlaceValue, hs]
  · intro v r hv
    have hw : writeProjectedValue locals v (.opaqueCast t :: .deref :: r) val = .unsupported := by
      rw [(opaqueCast_trusted_traversal_universal locals v val t (.deref :: r)).2.1]
      cases v <;> rfl
    simp only [writePlaceValue, stripLeadingOpaqueCast, hv, writeProjectedForLocal, hw]
  · intro r hu1 hu2
    have hres :
        (match resolveBorrowProjectionElems locals (.opaqueCast t :: r) with
         | some rp => rp
         | none => .opaqueCast t :: r) =
        .opaqueCast t ::
          (match resolveBorrowProjectionElems locals r with
           | some rp => rp
           | none => r) := by
      simp only [resolveBorrowProjectionElems]
      cases resolveBorrowProjectionElems locals r <;> rfl
    have heq : resolveBorrowWriteLocalProj decls layouts locals l (.opaqueCast t :: r) =
        .opaqueCast t :: resolveBorrowWriteLocalProj decls layouts locals l r := by
      rw [resolveBorrowWriteLocalProj_of_not_union decls layouts locals l (.opaqueCast t :: r) hu1,
        resolveBorrowWriteLocalProj_of_not_union decls layouts locals l r hu2]
      exact hres
    exact ⟨heq, by rw [heq, stripTransparentProjections]⟩

set_option linter.unusedSimpArgs false in
/-- **Trusted place read/write and initialized `.assign` with declarations (universal).** For
any declaration table (the one `stepMirFn` passes) and any active-protector list, a read or
write (`evalPlaceRead`, `writePlaceValue`, `evalPlaceWrite`, and `evalStmt` on
`StatementKind.assign` into an initialized local `get? locals₁ l = some (.init rootVal)`)
through `(_l as T).e.r` (`e` not a dereference) agrees with the cast-free place `_l.e.r`
whenever neither place touches a union and the cast does not change the validation types
(`placeTyResolved` agrees; a write through a cast place is validated at its resolved type, so
when `e` is not itself a cast that type must also be the cast-free place's `placeTy`; e.g.
when `T` is the declared type or the next projection fixes the type) nor the local's declared
type (`eraseLeadingOpaqueCastDecls … = decls` for both places: the declarations with `_l`
retyped to the effective cast type, against which a projected write is evaluated; for a
cast-free `e` the second equation holds by definition). Pure cast chains — a *bare*
`(_l as T)` place, also on an *uninitialized* local — are dispatched as whole-local accesses:
`opaqueCast_trusted_root_dispatch_simulation`. -/
theorem opaqueCast_trusted_place_rw_with_decls
    (locals : List LocalSlot) (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot) (decls : List LocalDecl)
    (activeProtectors : List Nat)
    (l : Nat) (t : Ty) (e : ProjectionElem) (r : List ProjectionElem) (val : Value)
    (hnd : ∀ r', e :: r ≠ .deref :: r')
    (hu : placeTouchesUnion decls layouts ⟨l, .opaqueCast t :: e :: r⟩ = false)
    (hu' : placeTouchesUnion decls layouts ⟨l, e :: r⟩ = false)
    (htyW : (∀ (t' : Ty) (r' : List ProjectionElem), e :: r ≠ .opaqueCast t' :: r') →
      placeTyResolved decls layouts ⟨l, .opaqueCast t :: e :: r⟩ =
        placeTy decls layouts ⟨l, e :: r⟩)
    (htyR : placeTyResolved decls layouts ⟨l, .opaqueCast t :: e :: r⟩ =
      placeTyResolved decls layouts ⟨l, e :: r⟩)
    (herase : eraseLeadingOpaqueCastDecls decls layouts l (.opaqueCast t :: e :: r) = decls)
    (herase' : eraseLeadingOpaqueCastDecls decls layouts l (e :: r) = decls) :
    evalPlaceRead locals ⟨l, .opaqueCast t :: e :: r⟩ borrows globals layouts callerLocals decls =
        evalPlaceRead locals ⟨l, e :: r⟩ borrows globals layouts callerLocals decls ∧
      writePlaceValue locals borrows ⟨l, .opaqueCast t :: e :: r⟩ val decls layouts =
        writePlaceValue locals borrows ⟨l, e :: r⟩ val decls layouts ∧
      evalPlaceWrite locals borrows ⟨l, .opaqueCast t :: e :: r⟩ val activeProtectors decls
          layouts =
        evalPlaceWrite locals borrows ⟨l, e :: r⟩ val activeProtectors decls layouts ∧
      (∀ (s : MachineState) (rv : Rvalue) (span : String) (locals₁ : List LocalSlot)
          (mem₁ : Memory) (rootVal : Value),
        evalRvalue s.frame.locals rv s.memory decls layouts = .ok val locals₁ mem₁ →
        get? locals₁ l = some (.init rootVal) →
        (∀ baseTy, placeTy decls layouts ⟨l, []⟩ = some baseTy →
          resolveTyWithLocalDecls decls layouts t = baseTy) →
        evalStmt s ⟨.assign ⟨l, .opaqueCast t :: e :: r⟩ rv, span⟩ decls layouts =
          evalStmt s ⟨.assign ⟨l, e :: r⟩ rv, span⟩ decls layouts) := by
  have hread : ∀ v, readProjectedValue locals v (.opaqueCast t :: e :: r) =
      readProjectedValue locals v (e :: r) := fun v =>
    (opaqueCast_trusted_traversal_universal locals v v t (e :: r)).1
  have hwrite : ∀ (ls : List LocalSlot) (v : Value),
      writeProjectedValue ls v (.opaqueCast t :: e :: r) val =
        writeProjectedValue ls v (e :: r) val := fun ls v =>
    (opaqueCast_trusted_traversal_universal ls v val t (e :: r)).2.1
  have hprot : ∀ (bs : List BorrowEntry) (ps : List Nat) (q : List ProjectionElem) (d : Nat),
      hasProtectedWriteConflict bs ps l none (.opaqueCast t :: q) 0 0 d =
        hasProtectedWriteConflict bs ps l none q 0 0 d := by
    intro bs ps q d
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      simp only [hasProtectedWriteConflict, borrowEntryOverlapsWrite, projectionsOverlap,
        stripTransparentProjections, ih]
  have hinv : ∀ (bs : List BorrowEntry) (q : List ProjectionElem) (d : Nat),
      invalidateConflictingBorrowsAtProj bs l none (.opaqueCast t :: q) 0 0 d =
        invalidateConflictingBorrowsAtProj bs l none q 0 0 d := by
    intro bs q d
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      simp only [invalidateConflictingBorrowsAtProj, updateBorrowPermAtProj,
        borrowEntryOverlapsWrite, projectionsOverlap, stripTransparentProjections, ih]
  have hres_er : ∀ (ls : List LocalSlot),
      (match resolveBorrowProjectionElems ls (.opaqueCast t :: e :: r) with
       | some rp => rp
       | none => .opaqueCast t :: e :: r) =
      .opaqueCast t ::
        (match resolveBorrowProjectionElems ls (e :: r) with
         | some rp => rp
         | none => e :: r) := by
    intro ls
    simp only [resolveBorrowProjectionElems]
    cases resolveBorrowProjectionElems ls (e :: r) <;> rfl
  have hwfl : ∀ (ls : List LocalSlot) (v : Value),
      writeProjectedForLocal ls decls layouts l v (.opaqueCast t :: e :: r) val =
        writeProjectedForLocal ls decls layouts l v (e :: r) val := by
    intro ls v
    simp only [writeProjectedForLocal, hu, hu', hwrite]
  have hwv :
      writePlaceValue locals borrows ⟨l, .opaqueCast t :: e :: r⟩ val decls layouts =
        writePlaceValue locals borrows ⟨l, e :: r⟩ val decls layouts := by
    cases e with
    | deref => exact absurd rfl (hnd r)
    | opaqueCast t' =>
      cases hs : stripLeadingOpaqueCast r with
      | nil => cases decls <;> simp only [writePlaceValue, stripLeadingOpaqueCast, hs, htyR]
      | cons a b =>
        cases a <;> cases decls <;>
          simp only [writePlaceValue, stripLeadingOpaqueCast, hs, writeProjectedForLocal,
            herase, herase', hu, hu', htyR, hwrite]
    | _ =>
      have htyW' := htyW (fun _ _ h => by cases h)
      cases decls <;>
        simp only [writePlaceValue, stripLeadingOpaqueCast, writeProjectedForLocal, herase, hu,
          hu', htyW', hwrite]
  refine ⟨?_, hwv, ?_, ?_⟩
  · cases e with
    | deref => exact absurd rfl (hnd r)
    | _ =>
      simp only [evalPlaceRead, readProjectedForLocal, hu, hu', htyR, hread]
  · cases activeProtectors with
    | nil => exact hwv
    | cons ph pt =>
      cases e with
      | deref => exact absurd rfl (hnd r)
      | _ =>
        change
          (match hasProtectedWriteConflict borrows (ph :: pt) l none
              (match resolveBorrowProjectionElems locals (.opaqueCast t :: _ :: r) with
               | some rp => rp
               | none => .opaqueCast t :: _ :: r) with
           | true => PlaceWriteResult.ub
           | false =>
             writePlaceValue locals borrows ⟨l, .opaqueCast t :: _ :: r⟩ val decls layouts) =
          (match hasProtectedWriteConflict borrows (ph :: pt) l none
              (match resolveBorrowProjectionElems locals (_ :: r) with
               | some rp => rp
               | none => _ :: r) with
           | true => PlaceWriteResult.ub
           | false => writePlaceValue locals borrows ⟨l, _ :: r⟩ val decls layouts)
        rw [hres_er, hprot, hwv]
  · intro s rv span locals₁ mem₁ rootVal hrv hinit hroot
    have hens :
        ensureNestedFieldShells rootVal (.opaqueCast t :: e :: r) decls layouts
            (placeTy decls layouts { local_ := l, projection := [] }) =
          ensureNestedFieldShells rootVal (e :: r) decls layouts
            (placeTy decls layouts { local_ := l, projection := [] }) := by
      conv => lhs; unfold ensureNestedFieldShells
      cases hpt : placeTy decls layouts { local_ := l, projection := [] } with
      | none => rfl
      | some baseTy => simp only [hroot baseTy hpt]
    have hrlp : resolveBorrowWriteLocalProj decls layouts locals₁ l (.opaqueCast t :: e :: r) =
        .opaqueCast t :: resolveBorrowWriteLocalProj decls layouts locals₁ l (e :: r) := by
      rw [resolveBorrowWriteLocalProj_of_not_union decls layouts locals₁ l
            (.opaqueCast t :: e :: r) hu,
          resolveBorrowWriteLocalProj_of_not_union decls layouts locals₁ l (e :: r) hu']
      exact hres_er locals₁
    cases e with
    | deref => exact absurd rfl (hnd r)
    | opaqueCast t' =>
      cases hs : stripLeadingOpaqueCast r with
      | nil => simp only [evalStmt, stripLeadingOpaqueCast, hs]
      | cons a b =>
        simp only [evalStmt, stripLeadingOpaqueCast, hs, hrv, hinit, herase, herase', hens,
          hwfl, hrlp, hinv, hprot]
    | _ =>
      simp only [evalStmt, stripLeadingOpaqueCast, hrv, hinit, herase, herase', hens, hwfl,
        hrlp, hinv, hprot]

private theorem projectionHasDeref_erase : ∀ p : List ProjectionElem,
    projectionHasDeref (eraseOpaqueCasts p) = projectionHasDeref p
  | [] => rfl
  | e :: rest => by
    have ih := projectionHasDeref_erase rest
    cases e <;> simp only [eraseOpaqueCasts, projectionHasDeref, ih]

private theorem placeIndexLocalsInit_erase (locals : List LocalSlot) :
    ∀ p : List ProjectionElem,
      placeIndexLocalsInit locals (eraseOpaqueCasts p) = placeIndexLocalsInit locals p
  | [] => rfl
  | e :: rest => by
    have ih := placeIndexLocalsInit_erase locals rest
    cases e <;> simp only [eraseOpaqueCasts, placeIndexLocalsInit, ih]

/-- With no root type to validate against, no non-empty projected `Deinit` tail validates
below an uninitialized (sub-)value. -/
private theorem deinitTailOk_none_cons (locals : List LocalSlot) (decls : List LocalDecl)
    (layouts : LayoutTable) (e : ProjectionElem) (r : List ProjectionElem) :
    deinitTailOk locals decls layouts none (e :: r) = false := by
  cases e with
  | downcast n vi =>
    cases r with
    | nil => rfl
    | cons e' r' => cases e' <;> rfl
  | index i =>
    simp only [deinitTailOk]
    cases get? locals i with
    | none => rfl
    | some slot =>
      cases slot with
      | init v => cases v <;> rfl
      | _ => rfl
  | _ => rfl

set_option linter.unusedSimpArgs false in
/-- **Trusted `placeMention` and `deinit` statement semantics on `.opaqueCast` (universal).**
`StatementKind.placeMention` is completely invariant under erasing `.opaqueCast` at any
depth (even with `.deref` or `.index` projections). `StatementKind.deinit` looks through a
*pure* cast chain (`Deinit((_l as T))` is `Deinit(_l)`,
`opaqueCast_trusted_root_dispatch_simulation`); on a projected path
`.opaqueCast t :: rest` whose cast chain is followed by a projection it validates the tail
below the cast at the *cast* type:
* on an initialized root `get? s.frame.locals l = some (.init rootVal)`,
  `.deinit ⟨l, .opaqueCast t :: rest⟩` runs `deinitProjectedForLocal`, which fails closed
  with `.unsupported` when `rest` contains `.deref` or the place touches a union and
  otherwise (for `rootVal ≠ .uninit`) steps through `.opaqueCast t` at the cast type;
* on an `.uninit` root whose local has no declared type (`placeTy = none`, e.g.
  `decls = []`) and a cast chain followed by a projection
  (`stripLeadingOpaqueCast rest = e :: r'`), `deinitTailOk` returns `false`, so it fails
  closed with `.unsupported` if `rest` has a `.deref` and `.fail .ub` otherwise;
* on either kind of root, for *every* root value (including `Value.uninit`) and every
  declaration table, `Deinit((_l as T).e.r)` is exactly `Deinit(_l.e.r)` whenever neither
  place touches a union and the cast does not switch the root type (`T` resolves to the
  declared type of `_l`, or `_l` has none). The root-type hypothesis is necessary:
  `opaqueCast_witness_type_switch`. -/
theorem opaqueCast_trusted_stmt_placeMention_and_deinit_universal
    (s : MachineState) (decls : List LocalDecl) (layouts : LayoutTable)
    (l : Nat) (t : Ty) (span : String) (rootSlot : LocalSlot) :
    (∀ p : List ProjectionElem,
      placeMentionOperandsInit s.frame.locals rootSlot (eraseOpaqueCasts p) =
        placeMentionOperandsInit s.frame.locals rootSlot p ∧
      evalStmt s ⟨.placeMention ⟨l, p⟩, span⟩ decls layouts =
        evalStmt s ⟨.placeMention ⟨l, eraseOpaqueCasts p⟩, span⟩ decls layouts) ∧
    (∀ (rootVal : Value) (rest : List ProjectionElem),
      get? s.frame.locals l = some (.init rootVal) →
      (rootVal ≠ .uninit →
        deinitProjectedForLocal s.frame.locals decls layouts l rootVal (.opaqueCast t :: rest) =
          (match projListHasDeref rest with
           | true => .unsupported
           | false =>
             match placeTouchesUnion decls layouts ⟨l, .opaqueCast t :: rest⟩ with
             | true => .unsupported
             | false =>
               let nextTyOpt :=
                 match placeTy decls layouts ⟨l, []⟩ with
                 | .some _ => .some (resolveTyWithLocalDecls decls layouts t)
                 | .none => .none
               deinitProjectedValue s.frame.locals rootVal rest decls layouts nextTyOpt)) ∧
      (∀ (e : ProjectionElem) (r : List ProjectionElem),
        rest = e :: r →
        placeTouchesUnion decls layouts ⟨l, .opaqueCast t :: e :: r⟩ = false →
        placeTouchesUnion decls layouts ⟨l, e :: r⟩ = false →
        (∀ baseTy, placeTy decls layouts ⟨l, []⟩ = some baseTy →
          resolveTyWithLocalDecls decls layouts t = baseTy) →
        evalStmt s ⟨.deinit ⟨l, .opaqueCast t :: e :: r⟩, span⟩ decls layouts =
          evalStmt s ⟨.deinit ⟨l, e :: r⟩, span⟩ decls layouts)) ∧
    (∀ rest : List ProjectionElem,
      get? s.frame.locals l = some .uninit →
      (∀ (e : ProjectionElem) (r' : List ProjectionElem),
        stripLeadingOpaqueCast rest = e :: r' →
        placeTy decls layouts ⟨l, []⟩ = none →
        evalStmt s ⟨.deinit ⟨l, .opaqueCast t :: rest⟩, span⟩ decls layouts =
          match projectionHasDeref rest with
          | true => MirStepNode.unsupported
          | false => MirStepNode.fail .ub) ∧
      (∀ (e : ProjectionElem) (r : List ProjectionElem),
        rest = e :: r →
        placeTouchesUnion decls layouts ⟨l, .opaqueCast t :: e :: r⟩ = false →
        placeTouchesUnion decls layouts ⟨l, e :: r⟩ = false →
        (∀ baseTy, placeTy decls layouts ⟨l, []⟩ = some baseTy →
          resolveTyWithLocalDecls decls layouts t = baseTy) →
        evalStmt s ⟨.deinit ⟨l, .opaqueCast t :: e :: r⟩, span⟩ decls layouts =
          evalStmt s ⟨.deinit ⟨l, e :: r⟩, span⟩ decls layouts)) := by
  have hprot : ∀ (bs : List BorrowEntry) (ps : List Nat) (q : List ProjectionElem) (d : Nat),
      hasProtectedWriteConflict bs ps l none (.opaqueCast t :: q) 0 0 d =
        hasProtectedWriteConflict bs ps l none q 0 0 d := by
    intro bs ps q d
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      simp only [hasProtectedWriteConflict, borrowEntryOverlapsWrite, projectionsOverlap,
        stripTransparentProjections, ih]
  have hinv : ∀ (bs : List BorrowEntry) (q : List ProjectionElem) (d : Nat),
      invalidateConflictingBorrowsAtProj bs l none (.opaqueCast t :: q) 0 0 d =
        invalidateConflictingBorrowsAtProj bs l none q 0 0 d := by
    intro bs q d
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      simp only [invalidateConflictingBorrowsAtProj, updateBorrowPermAtProj,
        borrowEntryOverlapsWrite, projectionsOverlap, stripTransparentProjections, ih]
  have hrlp : ∀ (e : ProjectionElem) (r : List ProjectionElem),
      placeTouchesUnion decls layouts ⟨l, .opaqueCast t :: e :: r⟩ = false →
      placeTouchesUnion decls layouts ⟨l, e :: r⟩ = false →
      resolveBorrowWriteLocalProj decls layouts s.frame.locals l (.opaqueCast t :: e :: r) =
        .opaqueCast t :: resolveBorrowWriteLocalProj decls layouts s.frame.locals l (e :: r) := by
    intro e r hu hu'
    rw [resolveBorrowWriteLocalProj_of_not_union decls layouts s.frame.locals l
          (.opaqueCast t :: e :: r) hu,
        resolveBorrowWriteLocalProj_of_not_union decls layouts s.frame.locals l (e :: r) hu']
    simp only [resolveBorrowProjectionElems]
    cases resolveBorrowProjectionElems s.frame.locals (e :: r) <;> rfl
  have htail : ∀ (e : ProjectionElem) (r : List ProjectionElem),
      (∀ baseTy, placeTy decls layouts ⟨l, []⟩ = some baseTy →
        resolveTyWithLocalDecls decls layouts t = baseTy) →
      deinitTailOk s.frame.locals decls layouts (placeTy decls layouts ⟨l, []⟩)
          (.opaqueCast t :: e :: r) =
        deinitTailOk s.frame.locals decls layouts (placeTy decls layouts ⟨l, []⟩) (e :: r) := by
    intro e r hroot
    cases hpt : placeTy decls layouts { local_ := l, projection := [] } with
    | none => rw [deinitTailOk_none_cons s.frame.locals decls layouts e r]
    | some baseTy =>
      conv => lhs; unfold deinitTailOk
      simp only [hroot baseTy hpt]
  refine ⟨?_, ?_, ?_⟩
  · intro p
    have hm : ∀ slot, placeMentionOperandsInit s.frame.locals slot (eraseOpaqueCasts p) =
        placeMentionOperandsInit s.frame.locals slot p := by
      intro slot
      simp only [placeMentionOperandsInit, projectionHasDeref_erase, placeIndexLocalsInit_erase]
    refine ⟨hm rootSlot, ?_⟩
    simp only [evalStmt]
    cases get? s.frame.locals l with
    | none => rfl
    | some slot =>
      cases slot <;> simp only [hm]
  · intro rootVal rest hv
    refine ⟨?_, ?_⟩
    · intro hne
      simp only [deinitProjectedForLocal, projListHasDeref]
      cases projListHasDeref rest with
      | true => rfl
      | false =>
        cases placeTouchesUnion decls layouts ⟨l, .opaqueCast t :: rest⟩ with
        | true => rfl
        | false =>
          cases rootVal with
          | uninit => exact absurd rfl hne
          | aggregate vi _ => cases vi <;> rfl
          | _ => rfl
    · intro e r hrest hu hu' hroot
      subst hrest
      have hdp :
          deinitProjectedForLocal s.frame.locals decls layouts l rootVal (.opaqueCast t :: e :: r) =
            deinitProjectedForLocal s.frame.locals decls layouts l rootVal (e :: r) := by
        simp only [deinitProjectedForLocal, projListHasDeref, hu, hu']
        cases projListHasDeref (e :: r) with
        | true => rfl
        | false =>
          cases rootVal with
          | uninit =>
            simp only [deinitProjectedValue, htail e r hroot, projListHasDeref]
          | aggregate vi _ =>
            cases vi <;> {
              conv => lhs; unfold deinitProjectedValue
              cases hpt : placeTy decls layouts { local_ := l, projection := [] } with
              | none => rfl
              | some baseTy => simp only [hroot baseTy hpt]
            }
          | _ =>
            conv => lhs; unfold deinitProjectedValue
            cases hpt : placeTy decls layouts { local_ := l, projection := [] } with
            | none => rfl
            | some baseTy => simp only [hroot baseTy hpt]
      have hr := hrlp e r hu hu'
      cases e with
      | opaqueCast t' =>
        cases hs : stripLeadingOpaqueCast r with
        | nil => simp only [evalStmt, stripLeadingOpaqueCast, hs]
        | cons a b =>
          simp only [evalStmt, stripLeadingOpaqueCast, hs, hv, hdp, hr, hprot, hinv]
      | _ => simp only [evalStmt, stripLeadingOpaqueCast, hv, hdp, hr, hprot, hinv]
  · intro rest huninit
    refine ⟨?_, ?_⟩
    · intro e r' hs hpt
      simp only [evalStmt, stripLeadingOpaqueCast, hs, huninit, hpt, deinitTailOk,
        projectionHasDeref]
      cases projectionHasDeref rest <;> rfl
    · intro e r hrest hu hu' hroot
      subst hrest
      have ht := htail e r hroot
      have hr := hrlp e r hu hu'
      cases e with
      | opaqueCast t' =>
        cases hs : stripLeadingOpaqueCast r with
        | nil => simp only [evalStmt, stripLeadingOpaqueCast, hs]
        | cons a b =>
          simp only [evalStmt, stripLeadingOpaqueCast, hs, huninit, ht, hr, hprot, hinv,
            projectionHasDeref]
      | _ =>
        simp only [evalStmt, stripLeadingOpaqueCast, huninit, ht, hr, hprot, hinv,
          projectionHasDeref]

/-- **Trusted root dispatch through opaque casts (universal; resolved correspondence
`DIV-TR-OPAQUECAST-ROOT-DISPATCH`).** Trusted now dispatches on the projection list *modulo
its leading opaque casts* (`stripLeadingOpaqueCast`): a place whose projection is a pure cast
chain (`(_l as T)`, `((_l as T) as U)`, …; `stripLeadingOpaqueCast cs = []`) is the whole local
`_l`, exactly like its post-borrowck erasure, and a cast chain followed by a field step uses
the field shell of the cast-erased write. With no type switch involved, opaque-cast places no
longer differ observably from their erasure:
* `move (_l as T)` **is** `move _l`: it yields the value and de-initializes `_l` (formerly a
  projected move that kept `_l` initialized). With a declaration table the moved value is
  additionally validated at the cast type — the only remaining difference is that type switch
  (an invalid value at the cast type is UB);
* `writePlaceValue` (for both empty and non-empty declaration tables, validating against the cast
  type when declarations are supplied) and `evalStmt` on `StatementKind.assign ⟨l, .opaqueCast t :: cs⟩ rv`
  are the whole-local write / `_l = rv` — in particular they initialize an uninitialized `_l`
  (formerly UB);
* `Deinit((_l as T))` is `Deinit(_l)` and stores `LocalSlot.uninit` (formerly
  `LocalSlot.init Value.uninit`);
* `SetDiscriminant((_l as T), vIdx)` is `SetDiscriminant(_l, vIdx)` evaluated at the
  declarations with `_l` retyped to the effective cast type (`eraseLeadingOpaqueCastDecls`) —
  on initialized *and* uninitialized enum locals (formerly UB on an uninitialized one);
* `Drop((_l as T))`, `writeReturnDestination` (validated at the cast type when declarations are
  supplied), and `Rvalue.discriminant((_l as T))` (whenever the cast preserves `placeTyResolved`,
  in particular with empty declarations) likewise match the erased root local `_l`;
* an assignment `(_l as T).f.r = rv` into an uninitialized `_l` materializes
  (`uninitFieldWriteShell?`) exactly the aggregate shell of the cast-erased `_l.f.r = rv` at
  those declarations (formerly `none`, hence UB);
* fail-closed boundary: a cast chain directly before a dereference is still `.unsupported`,
  never a silent write.
Unreachable for captured bodies (`MirPhase::Runtime` forbids `OpaqueCast`,
`opaqueCast_leanMiri_phase_boundary`); concrete instances:
`opaqueCast_witness_projected_move`, `opaqueCast_witness_root_dispatch`. -/
theorem opaqueCast_trusted_root_dispatch_simulation
    (locals : List LocalSlot) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable) (callerLocals : List LocalSlot)
    (callStack : List SavedCallerFrame) (l : Nat) (t : Ty) (cs : List ProjectionElem)
    (val : Value)
    (hcs : stripLeadingOpaqueCast cs = []) :
    evalOperand locals (.move ⟨l, .opaqueCast t :: cs⟩) borrows globals layouts callerLocals []
        callStack =
      evalOperand locals (.move ⟨l, []⟩) borrows globals layouts callerLocals [] callStack ∧
    (∀ (decls : List LocalDecl) (v w : Value) (locals' : List LocalSlot),
      get? locals l = some (.init v) → readProjectedValue locals v [] = .ok w →
      set? locals l .uninit = some locals' →
      validateValueForTy? layouts (placeTyResolved decls layouts ⟨l, .opaqueCast t :: cs⟩) w =
        true →
      evalOperand locals (.move ⟨l, .opaqueCast t :: cs⟩) borrows globals layouts callerLocals
          decls callStack = .ok w locals' ∧
      evalOperand locals (.move ⟨l, []⟩) borrows globals layouts callerLocals decls callStack =
        .ok w locals') ∧
    (∀ (d : LocalDecl) (ds : List LocalDecl) (v w : Value),
      get? locals l = some (.init v) → readProjectedValue locals v [] = .ok w →
      validateValueForTy? layouts (placeTyResolved (d :: ds) layouts ⟨l, .opaqueCast t :: cs⟩)
          w = false →
      evalOperand locals (.move ⟨l, .opaqueCast t :: cs⟩) borrows globals layouts callerLocals
          (d :: ds) callStack = .ub) ∧
    writePlaceValue locals borrows ⟨l, .opaqueCast t :: cs⟩ val [] layouts callStack =
      writePlaceValue locals borrows ⟨l, []⟩ val [] layouts callStack ∧
    (∀ (d : LocalDecl) (ds : List LocalDecl),
      (validateValueForTy? layouts (placeTyResolved (d :: ds) layouts ⟨l, .opaqueCast t :: cs⟩)
          val = true →
        writePlaceValue locals borrows ⟨l, .opaqueCast t :: cs⟩ val (d :: ds) layouts callStack =
          writePlaceValue locals borrows ⟨l, []⟩ val [] layouts callStack) ∧
      (validateValueForTy? layouts (placeTyResolved (d :: ds) layouts ⟨l, .opaqueCast t :: cs⟩)
          val = false →
        writePlaceValue locals borrows ⟨l, .opaqueCast t :: cs⟩ val (d :: ds) layouts callStack =
          .ub)) ∧
    (∀ (s : MachineState) (decls : List LocalDecl) (rv : Rvalue) (span : String),
      evalStmt s ⟨.assign ⟨l, .opaqueCast t :: cs⟩ rv, span⟩ decls layouts =
        evalStmt s ⟨.assign ⟨l, []⟩ rv, span⟩ decls layouts) ∧
    (∀ (s : MachineState) (decls : List LocalDecl) (span : String),
      evalStmt s ⟨.deinit ⟨l, .opaqueCast t :: cs⟩, span⟩ decls layouts =
        evalStmt s ⟨.deinit ⟨l, []⟩, span⟩ decls layouts) ∧
    (∀ (s : MachineState) (decls : List LocalDecl) (vIdx : VariantIdx) (span : String),
      evalStmt s ⟨.setDiscriminant ⟨l, .opaqueCast t :: cs⟩ vIdx, span⟩ decls layouts =
        evalStmt s ⟨.setDiscriminant ⟨l, []⟩ vIdx, span⟩
          (eraseLeadingOpaqueCastDecls decls layouts l (.opaqueCast t :: cs)) layouts) ∧
    (∀ (s : MachineState) (target : BasicBlockIdx) (unwind : UnwindAction) (span : String)
        (cb : Option CapturedMir),
      evalTerminator s ⟨.drop ⟨l, .opaqueCast t :: cs⟩ target unwind, span⟩ cb =
        evalTerminator s ⟨.drop ⟨l, []⟩ target unwind, span⟩ cb) ∧
    (∀ (mem : Memory),
      writeReturnDestination locals mem ⟨l, .opaqueCast t :: cs⟩ val [] layouts =
        writeReturnDestination locals mem ⟨l, []⟩ val [] layouts ∧
      (∀ (d : LocalDecl) (ds : List LocalDecl),
        (validateValueForTy? layouts (placeTyResolved (d :: ds) layouts ⟨l, .opaqueCast t :: cs⟩)
            val = true →
          writeReturnDestination locals mem ⟨l, .opaqueCast t :: cs⟩ val (d :: ds) layouts =
            writeReturnDestination locals mem ⟨l, []⟩ val (d :: ds) layouts) ∧
        (validateValueForTy? layouts (placeTyResolved (d :: ds) layouts ⟨l, .opaqueCast t :: cs⟩)
            val = false →
          writeReturnDestination locals mem ⟨l, .opaqueCast t :: cs⟩ val (d :: ds) layouts =
            .ub))) ∧
    (∀ (mem : Memory) (decls : List LocalDecl),
      placeTyResolved decls layouts ⟨l, .opaqueCast t :: cs⟩ =
        placeTyResolved decls layouts ⟨l, []⟩ →
      evalRvalue locals (.discriminant ⟨l, .opaqueCast t :: cs⟩) mem decls layouts =
        evalRvalue locals (.discriminant ⟨l, []⟩) mem decls layouts) ∧
    (∀ (decls : List LocalDecl) (rest : List ProjectionElem) (i : FieldIdx) (ft : Ty)
        (fr : List ProjectionElem),
      stripLeadingOpaqueCast rest = .field i ft :: fr →
      uninitFieldWriteShell? decls layouts l (.opaqueCast t) rest =
        uninitFieldWriteShell?
          (eraseLeadingOpaqueCastDecls decls layouts l (.opaqueCast t :: rest)) layouts l
          (.field i ft) fr) ∧
    (∀ (rest r : List ProjectionElem), stripLeadingOpaqueCast rest = .deref :: r →
      writePlaceValue locals borrows ⟨l, .opaqueCast t :: rest⟩ val [] layouts callStack =
        .unsupported) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [evalOperand, hcs] <;> rfl
  · intro decls v w locals' hv hr hset hval
    refine ⟨?_, ?_⟩
    · cases decls <;> simp only [evalOperand, hcs, hv, hr, hset, hval]
    · simp only [evalOperand, hv, hr, hset]
  · intro d ds v w hv hr hval
    simp only [evalOperand, hcs, hv, hr, hval]
  · simp only [writePlaceValue, hcs] <;> rfl
  · intro d ds
    refine ⟨fun hv => ?_, fun hv => ?_⟩
    · simp only [writePlaceValue, hcs, hv]
    · simp only [writePlaceValue, hcs, hv]
  · intro s decls rv span
    simp only [evalStmt, stripLeadingOpaqueCast, hcs] <;> rfl
  · intro s decls span
    simp only [evalStmt, stripLeadingOpaqueCast, hcs] <;> rfl
  · intro s decls vIdx span
    simp only [evalStmt, stripLeadingOpaqueCast, hcs] <;> rfl
  · intro s target unwind span cb
    simp only [evalTerminator, stripLeadingOpaqueCast, hcs]
  · intro mem
    refine ⟨?_, fun d ds => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · simp only [writeReturnDestination, stripLeadingOpaqueCast, hcs]
    · simp only [writeReturnDestination, stripLeadingOpaqueCast, hcs, hv]
    · simp only [writeReturnDestination, stripLeadingOpaqueCast, hcs, hv]
  · intro mem decls hty
    simp only [evalRvalue, stripLeadingOpaqueCast, hcs]
    cases get? locals l with
    | none => rfl
    | some slot =>
      cases slot with
      | init v =>
        cases v with
        | uninit => rfl
        | aggregate vi fs => simp only [evalPlaceDiscriminant, hty]
        | _ => simp only [evalPlaceDiscriminant, hty]
      | _ => rfl
  · intro decls rest i ft fr hs
    simp only [uninitFieldWriteShell?, hs]
  · intro rest r hs
    simp only [writePlaceValue, hs]

/-- Typed statement pin of the resolved opaque-cast root-dispatch correspondence
(`DIV-TR-OPAQUECAST-ROOT-DISPATCH`). -/
example : ∀ (locals : List LocalSlot) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable) (callerLocals : List LocalSlot)
    (callStack : List SavedCallerFrame) (l : Nat) (t : Ty) (cs : List ProjectionElem)
    (val : Value),
    stripLeadingOpaqueCast cs = [] →
    evalOperand locals (.move ⟨l, .opaqueCast t :: cs⟩) borrows globals layouts callerLocals []
        callStack =
      evalOperand locals (.move ⟨l, []⟩) borrows globals layouts callerLocals [] callStack ∧
    (∀ (decls : List LocalDecl) (v w : Value) (locals' : List LocalSlot),
      get? locals l = some (.init v) → readProjectedValue locals v [] = .ok w →
      set? locals l .uninit = some locals' →
      validateValueForTy? layouts (placeTyResolved decls layouts ⟨l, .opaqueCast t :: cs⟩) w =
        true →
      evalOperand locals (.move ⟨l, .opaqueCast t :: cs⟩) borrows globals layouts callerLocals
          decls callStack = .ok w locals' ∧
      evalOperand locals (.move ⟨l, []⟩) borrows globals layouts callerLocals decls callStack =
        .ok w locals') ∧
    (∀ (d : LocalDecl) (ds : List LocalDecl) (v w : Value),
      get? locals l = some (.init v) → readProjectedValue locals v [] = .ok w →
      validateValueForTy? layouts (placeTyResolved (d :: ds) layouts ⟨l, .opaqueCast t :: cs⟩)
          w = false →
      evalOperand locals (.move ⟨l, .opaqueCast t :: cs⟩) borrows globals layouts callerLocals
          (d :: ds) callStack = .ub) ∧
    writePlaceValue locals borrows ⟨l, .opaqueCast t :: cs⟩ val [] layouts callStack =
      writePlaceValue locals borrows ⟨l, []⟩ val [] layouts callStack ∧
    (∀ (d : LocalDecl) (ds : List LocalDecl),
      (validateValueForTy? layouts (placeTyResolved (d :: ds) layouts ⟨l, .opaqueCast t :: cs⟩)
          val = true →
        writePlaceValue locals borrows ⟨l, .opaqueCast t :: cs⟩ val (d :: ds) layouts callStack =
          writePlaceValue locals borrows ⟨l, []⟩ val [] layouts callStack) ∧
      (validateValueForTy? layouts (placeTyResolved (d :: ds) layouts ⟨l, .opaqueCast t :: cs⟩)
          val = false →
        writePlaceValue locals borrows ⟨l, .opaqueCast t :: cs⟩ val (d :: ds) layouts callStack =
          .ub)) ∧
    (∀ (s : MachineState) (decls : List LocalDecl) (rv : Rvalue) (span : String),
      evalStmt s ⟨.assign ⟨l, .opaqueCast t :: cs⟩ rv, span⟩ decls layouts =
        evalStmt s ⟨.assign ⟨l, []⟩ rv, span⟩ decls layouts) ∧
    (∀ (s : MachineState) (decls : List LocalDecl) (span : String),
      evalStmt s ⟨.deinit ⟨l, .opaqueCast t :: cs⟩, span⟩ decls layouts =
        evalStmt s ⟨.deinit ⟨l, []⟩, span⟩ decls layouts) ∧
    (∀ (s : MachineState) (decls : List LocalDecl) (vIdx : VariantIdx) (span : String),
      evalStmt s ⟨.setDiscriminant ⟨l, .opaqueCast t :: cs⟩ vIdx, span⟩ decls layouts =
        evalStmt s ⟨.setDiscriminant ⟨l, []⟩ vIdx, span⟩
          (eraseLeadingOpaqueCastDecls decls layouts l (.opaqueCast t :: cs)) layouts) ∧
    (∀ (s : MachineState) (target : BasicBlockIdx) (unwind : UnwindAction) (span : String)
        (cb : Option CapturedMir),
      evalTerminator s ⟨.drop ⟨l, .opaqueCast t :: cs⟩ target unwind, span⟩ cb =
        evalTerminator s ⟨.drop ⟨l, []⟩ target unwind, span⟩ cb) ∧
    (∀ (mem : Memory),
      writeReturnDestination locals mem ⟨l, .opaqueCast t :: cs⟩ val [] layouts =
        writeReturnDestination locals mem ⟨l, []⟩ val [] layouts ∧
      (∀ (d : LocalDecl) (ds : List LocalDecl),
        (validateValueForTy? layouts (placeTyResolved (d :: ds) layouts ⟨l, .opaqueCast t :: cs⟩)
            val = true →
          writeReturnDestination locals mem ⟨l, .opaqueCast t :: cs⟩ val (d :: ds) layouts =
            writeReturnDestination locals mem ⟨l, []⟩ val (d :: ds) layouts) ∧
        (validateValueForTy? layouts (placeTyResolved (d :: ds) layouts ⟨l, .opaqueCast t :: cs⟩)
            val = false →
          writeReturnDestination locals mem ⟨l, .opaqueCast t :: cs⟩ val (d :: ds) layouts =
            .ub))) ∧
    (∀ (mem : Memory) (decls : List LocalDecl),
      placeTyResolved decls layouts ⟨l, .opaqueCast t :: cs⟩ =
        placeTyResolved decls layouts ⟨l, []⟩ →
      evalRvalue locals (.discriminant ⟨l, .opaqueCast t :: cs⟩) mem decls layouts =
        evalRvalue locals (.discriminant ⟨l, []⟩) mem decls layouts) ∧
    (∀ (decls : List LocalDecl) (rest : List ProjectionElem) (i : FieldIdx) (ft : Ty)
        (fr : List ProjectionElem),
      stripLeadingOpaqueCast rest = .field i ft :: fr →
      uninitFieldWriteShell? decls layouts l (.opaqueCast t) rest =
        uninitFieldWriteShell?
          (eraseLeadingOpaqueCastDecls decls layouts l (.opaqueCast t :: rest)) layouts l
          (.field i ft) fr) ∧
    (∀ (rest r : List ProjectionElem), stripLeadingOpaqueCast rest = .deref :: r →
      writePlaceValue locals borrows ⟨l, .opaqueCast t :: rest⟩ val [] layouts callStack =
        .unsupported) :=
  @opaqueCast_trusted_root_dispatch_simulation

private theorem borrowProjSteps_erase : ∀ p : List ProjectionElem,
    MiniRustSpec.Correspondence.borrowProjSteps (eraseOpaqueCasts p) =
      MiniRustSpec.Correspondence.borrowProjSteps p
  | [] => rfl
  | e :: rest => by
    have ih := borrowProjSteps_erase rest
    cases e <;> simp only [eraseOpaqueCasts, MiniRustSpec.Correspondence.borrowProjSteps, ih]

private theorem borrowProjSteps_strip : ∀ p : List ProjectionElem,
    MiniRustSpec.Correspondence.borrowProjSteps (stripTransparentProjections p) =
      MiniRustSpec.Correspondence.borrowProjSteps p
  | [] => rfl
  | e :: rest => by
    have ih := borrowProjSteps_strip rest
    cases e <;> simp only [stripTransparentProjections, MiniRustSpec.Correspondence.borrowProjSteps,
      ih]

/-- **MiniRust (universal).** MiniRust places have no opaque-cast projection and upstream
`minimize` aborts on `ProjectionElem::OpaqueCast` (`span_bug!`, anchored above): the
`MiniRustSpec` place translation fails closed (so no statement writing or reading through
an opaque cast enters the fragment), while the `MiniRustSpec` borrow-overlap abstraction
`borrowProjSteps` — the one its simulation proofs use — strips opaque casts exactly as the
Trusted `stripTransparentProjections` does. -/
theorem opaqueCast_minirust_corresponds (decls : List LocalDecl) (layouts : LayoutTable)
    (i : Nat) (t : Ty) (rest : List ProjectionElem) (rv : Rvalue) (span : String) :
    MiniRustSpec.Correspondence.translatePlace decls ⟨i, .opaqueCast t :: rest⟩ = none ∧
      MiniRustSpec.Correspondence.translateStatement decls
        ⟨.assign ⟨i, .opaqueCast t :: rest⟩ rv, span⟩ layouts = none ∧
      MiniRustSpec.Correspondence.borrowProjSteps (.opaqueCast t :: rest) =
        MiniRustSpec.Correspondence.borrowProjSteps rest ∧
      (∀ p, MiniRustSpec.Correspondence.borrowProjSteps (eraseOpaqueCasts p) =
        MiniRustSpec.Correspondence.borrowProjSteps p) ∧
      (∀ p, MiniRustSpec.Correspondence.borrowProjSteps (stripTransparentProjections p) =
        MiniRustSpec.Correspondence.borrowProjSteps p) := by
  refine ⟨rfl, ?_, rfl, borrowProjSteps_erase, borrowProjSteps_strip⟩
  simp [MiniRustSpec.Correspondence.translateStatement, MiniRustSpec.Correspondence.translatePlace]

/-- **LeanMiri phase boundary (universal).** Both vendored Miri projection paths reject an
`OpaqueCast` after borrowck — `Projection.project` with an invariant error and
`PlaceDynamic.project` with an invalid-program error — and neither is a UB verdict, for
every cast type and result type. Trusted instead agrees with the opaque-cast-erased
program (value semantics), so the two references never disagree on a UB verdict; rustc's
MIR validator excludes `OpaqueCast` from every runtime-phase body Anneal captures. -/
theorem opaqueCast_leanMiri_phase_boundary {T A : Type} (tid : T) (locals : List LocalSlot)
    (v : Value) (t : Ty) (rest : List ProjectionElem) :
    (LeanMiri.projectOpaqueCast tid : Except LeanMiri.StepError A) =
        .error (.invariant "OpaqueCast after borrowck") ∧
      (LeanMiri.placeProjectOpaqueCast tid : Except LeanMiri.StepError A) =
        .error (.invalidProgram "OpaqueCast after borrowck") ∧
      (∀ e, (LeanMiri.projectOpaqueCast tid : Except LeanMiri.StepError A) = .error e →
        e.isUB = false) ∧
      (∀ e, (LeanMiri.placeProjectOpaqueCast tid : Except LeanMiri.StepError A) = .error e →
        e.isUB = false) ∧
      readProjectedValue locals v (.opaqueCast t :: rest) =
        readProjectedValue locals v (eraseOpaqueCasts rest) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro e he; cases he; rfl
  · intro e he; cases he; rfl
  · rw [(opaqueCast_trusted_traversal_universal locals v v t rest).1]
    exact readProjectedValue_erase locals rest v

/-! ### Concrete witnesses -/

def tyPair : Ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 0 }

def pairDecl : LocalDecl := { mutability := .mut, ty := tyPair, debugName := some "p" }

def pairVal : Value := .aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩]

def ocLocals : List LocalSlot := [.uninit, .init pairVal]

/-- `p.f` and `(p as T).f`. -/
def plainField (f : Nat) : Place := ⟨1, [.field f tyU32]⟩

def ocField (f : Nat) : Place := ⟨1, [.opaqueCast tyPair, .field f tyU32]⟩

/-- Two live borrows of `p.0` (tag 5) and `p.1` (tag 6). -/
def ocBorrows : List BorrowEntry :=
  [{ tag := 5, targetLocal := 1, targetProjection := [.field 0 tyU32], perm := .unique },
   { tag := 6, targetLocal := 1, targetProjection := [.field 1 tyU32], perm := .unique }]

def ocState : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := ocLocals },
    memory := { borrows := ocBorrows, nextTag := 7 } }

/-- **Positive witness.** Reading `(p as T).1` yields `9` like `p.1`; the statement
`(p as T).0 = 42` produces exactly the successor state of `p.0 = 42` — the same written
value *and* the same borrow-table update (the `p.0` borrow is invalidated, the sibling
`p.1` borrow survives in both). -/
theorem opaqueCast_witness_read_write :
    evalOperand ocLocals (.copy (ocField 1)) = .ok (.scalar ⟨9, 4⟩) ocLocals ∧
      evalOperand ocLocals (.copy (ocField 1)) = evalOperand ocLocals (.copy (plainField 1)) ∧
      evalStmt ocState ⟨.assign (ocField 0) (.use (cU32 42)), "w"⟩ [u32Decl "_0", pairDecl]
          wLayouts =
        evalStmt ocState ⟨.assign (plainField 0) (.use (cU32 42)), "w"⟩ [u32Decl "_0", pairDecl]
          wLayouts ∧
      nodeState (evalStmt ocState ⟨.assign (ocField 0) (.use (cU32 42)), "w"⟩
          [u32Decl "_0", pairDecl] wLayouts) =
        some (.running
          { frame := { blockIdx := 0, stmtIdx := 1,
                       locals := [.uninit, .init (.aggregate 0 [.scalar ⟨42, 4⟩, .scalar ⟨9, 4⟩])] },
            memory := { borrows :=
              [{ tag := 5, targetLocal := 1, targetProjection := [.field 0 tyU32],
                 perm := .disabled },
               { tag := 6, targetLocal := 1, targetProjection := [.field 1 tyU32],
                 perm := .unique }], nextTag := 7 } }) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Positive witness (real declarations).** With the body's declaration table, reading
and writing `(p as (u32, u32)).1` agree with `p.1` (`opaqueCast_trusted_place_rw_with_decls`
instantiated: no union, same validation types). -/
theorem opaqueCast_witness_place_rw_with_decls :
    evalPlaceRead ocLocals (ocField 1) [] [] wLayouts [] [u32Decl "_0", pairDecl] =
        .ok (.scalar ⟨9, 4⟩) ocLocals ∧
      evalPlaceRead ocLocals (ocField 1) [] [] wLayouts [] [u32Decl "_0", pairDecl] =
        evalPlaceRead ocLocals (plainField 1) [] [] wLayouts [] [u32Decl "_0", pairDecl] ∧
      writePlaceValue ocLocals [] (ocField 1) (.scalar ⟨5, 4⟩) [u32Decl "_0", pairDecl] wLayouts =
        writePlaceValue ocLocals [] (plainField 1) (.scalar ⟨5, 4⟩) [u32Decl "_0", pairDecl]
          wLayouts ∧
      writePlaceValue ocLocals [] (ocField 1) (.scalar ⟨5, 4⟩) [u32Decl "_0", pairDecl] wLayouts =
        .ok [.uninit, .init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨5, 4⟩])] :=
  (opaqueCast_trusted_place_rw_with_decls ocLocals [] [] wLayouts [] [u32Decl "_0", pairDecl] [] 1
      tyPair (.field 1 tyU32) [] (.scalar ⟨5, 4⟩) (fun _ h => by cases h) rfl rfl
      (fun _ => rfl) rfl rfl rfl).elim
    fun hr hrest => ⟨rfl, hr, hrest.1, rfl⟩

def tyBool : Ty := { kind := .bool, layoutIdx := 0 }

def tyU8Arr2 : Ty := { kind := .array (.uint .u8) 2, layoutIdx := 0 }

def tyBoolArr2 : Ty := { kind := .array .bool 2, layoutIdx := 0 }

def u8Arr2Decl : LocalDecl := { mutability := .mut, ty := tyU8Arr2, debugName := some "arr" }

def u8Arr2Locals : List LocalSlot := [.uninit, .init (.aggregate 0 [.scalar ⟨2, 1⟩, .scalar ⟨0, 1⟩])]

/-- A borrow-free state whose `(u32, u32)` local `_1` holds `slot`. -/
def ocDeinitState (slot : LocalSlot) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, slot] },
    memory := { borrows := [], nextTag := 7 } }

/-- Concrete ADT layouts (`1`: 2-variant enum `{ None, Some(u32) }`; `2`: 2-field struct `Inner2`;
`3`: 3-field struct `Inner3`; `4`: `OuterA { inner: Inner2 }`; `5`: `OuterB { inner: Inner3 }`)
used to witness both non-degenerate `SetDiscriminant` behavior and necessity of the root-type
agreement hypothesis `hroot` in `opaqueCast_trusted_place_rw_with_decls` Clause 4. -/
def ocAdtLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ u32Layout,
        { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := .memory,
          fields := .arbitrary [{ bytes := 0 }] [0],
          variants := .multiple (.initialized (.int 8 false) ⟨0, 1⟩) 0
            [.arbitrary [] [], .arbitrary [{ bytes := 4 }] [0]],
          isUninhabited := false, fieldLayouts := [] },
        { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := .memory,
          fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }] [0, 1],
          variants := .single 0, isUninhabited := false, fieldLayouts := [0, 0] },
        { size := { bytes := 12 }, align := { bytes := 4 }, backendRepr := .memory,
          fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }, { bytes := 8 }] [0, 1, 2],
          variants := .single 0, isUninhabited := false, fieldLayouts := [0, 0, 0] },
        { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := .memory,
          fields := .arbitrary [{ bytes := 0 }] [0],
          variants := .single 0, isUninhabited := false, fieldLayouts := [2] },
        { size := { bytes := 12 }, align := { bytes := 4 }, backendRepr := .memory,
          fields := .arbitrary [{ bytes := 0 }] [0],
          variants := .single 0, isUninhabited := false, fieldLayouts := [3] } ] }

def tyOcEnum : Ty := { kind := .adt "w::OptU32" [], layoutIdx := 1 }

def tyOcInnerUnresolved : Ty := { kind := .adt "w::Inner" [], layoutIdx := 0 }

def tyOcOuterA : Ty := { kind := .adt "w::OuterA" [], layoutIdx := 4 }

def tyOcOuterB : Ty := { kind := .adt "w::OuterB" [], layoutIdx := 5 }

def ocEnumDecl : LocalDecl := { mutability := .mut, ty := tyOcEnum, debugName := some "e" }

def ocOuterADecl : LocalDecl := { mutability := .mut, ty := tyOcOuterA, debugName := some "o" }

def ocNestedPlainPlace : Place := ⟨1, [.field 0 tyOcInnerUnresolved, .field 0 tyU32]⟩

def ocNestedCastPlace : Place :=
  ⟨1, [.opaqueCast tyOcOuterB, .field 0 tyOcInnerUnresolved, .field 0 tyU32]⟩

def ocNestedState : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.aggregate 0 [.uninit])] },
    memory := { borrows := [], nextTag := 7 } }

/-- **Documented type switch (including `.ok` vs `.ub` runtime validity flip and `hroot`
necessity).** The opaque cast switches `placeTy` (write validation) and `placeTyResolved`
(read validation). When an array `[u8; 2]` local holding `[2_u8, 0_u8]` is indexed at `0`
(`e = .constantIndex 0 1 false`, which inherits its element type from the base type), the
cast-free read and write of `2_u8` succeed at `tyU8`, whereas pre-casting the base via
`.opaqueCast tyBoolArr2` switches the element type to `bool` (`tyBool`) so `validateValueForTy?`
rejects `2` and both `evalPlaceRead` and `writePlaceValue` fault with `.ub` — proving the
`htyW`/`htyR` agreement hypotheses of `opaqueCast_trusted_place_rw_with_decls` are necessary even
for non-empty `e :: r` tails. Likewise for `Deinit`, whose tail is validated at the cast type:
on a `(u32, u32)` local that is uninitialized (`LocalSlot.uninit`) or holds `Value.uninit`,
`Deinit((_1 as (u32, u32)).0)` steps exactly like `Deinit(_1.0)`, whereas
`Deinit((_1 as u32).0)` asks `u32` for a field and faults with UB although neither place
touches a union — the root-type agreement hypothesis of the `Deinit` erasure in
`opaqueCast_trusted_stmt_placeMention_and_deinit_universal` is necessary. Finally, for nested
struct initialization `(_1 as OuterB).0.0 = 42` vs `_1.0.0 = 42` on `_1 : OuterA` holding
`Aggregate 0 [.uninit]`, `placeTy`, `placeTyResolved` (both `some tyU32`), and
`placeTouchesUnion = false` all agree, yet `ensureNestedFieldShells` materializes a 3-field
inner shell under `OuterB` vs a 2-field inner shell under `OuterA` (`evalStmt` strictly
distinct) — proving the `hroot` hypothesis of `opaqueCast_trusted_place_rw_with_decls`
Clause 4 is strictly necessary. -/
theorem opaqueCast_witness_type_switch :
    placeTy [u32Decl "_0", pairDecl] wLayouts ⟨1, [.opaqueCast tyU8]⟩ = some tyU8 ∧
      placeTy [u32Decl "_0", pairDecl] wLayouts ⟨1, []⟩ = some tyPair ∧
      placeTy [u32Decl "_0", pairDecl] wLayouts ⟨1, [.opaqueCast tyU8]⟩ ≠
        placeTy [u32Decl "_0", pairDecl] wLayouts ⟨1, []⟩ ∧
      evalPlaceRead u8Arr2Locals ⟨1, [.constantIndex 0 1 false]⟩ [] [] wLayouts []
          [u32Decl "_0", u8Arr2Decl] =
        .ok (.scalar ⟨2, 1⟩) u8Arr2Locals ∧
      evalPlaceRead u8Arr2Locals ⟨1, [.opaqueCast tyBoolArr2, .constantIndex 0 1 false]⟩ [] []
          wLayouts [] [u32Decl "_0", u8Arr2Decl] =
        .ub ∧
      writePlaceValue u8Arr2Locals [] ⟨1, [.constantIndex 0 1 false]⟩ (.scalar ⟨2, 1⟩)
          [u32Decl "_0", u8Arr2Decl] wLayouts =
        .ok u8Arr2Locals ∧
      writePlaceValue u8Arr2Locals [] ⟨1, [.opaqueCast tyBoolArr2, .constantIndex 0 1 false]⟩
          (.scalar ⟨2, 1⟩) [u32Decl "_0", u8Arr2Decl] wLayouts =
        .ub ∧
      placeTouchesUnion [u32Decl "_0", pairDecl] wLayouts ⟨1, [.opaqueCast tyU32, .field 0 tyU32]⟩ =
        false ∧
      placeTouchesUnion [u32Decl "_0", pairDecl] wLayouts (plainField 0) = false ∧
      (∀ slot ∈ [LocalSlot.uninit, LocalSlot.init Value.uninit],
        evalStmt (ocDeinitState slot) ⟨.deinit (plainField 0), "w"⟩ [u32Decl "_0", pairDecl]
            wLayouts =
          MirStepNode.step (advanceStmt (ocDeinitState slot) [.uninit, slot]) ∧
        evalStmt (ocDeinitState slot) ⟨.deinit (ocField 0), "w"⟩ [u32Decl "_0", pairDecl]
            wLayouts =
          evalStmt (ocDeinitState slot) ⟨.deinit (plainField 0), "w"⟩ [u32Decl "_0", pairDecl]
            wLayouts ∧
        evalStmt (ocDeinitState slot) ⟨.deinit ⟨1, [.opaqueCast tyU32, .field 0 tyU32]⟩, "w"⟩
            [u32Decl "_0", pairDecl] wLayouts =
          MirStepNode.fail .ub) ∧
      placeTy [u32Decl "_0", ocOuterADecl] ocAdtLayouts ocNestedCastPlace =
        placeTy [u32Decl "_0", ocOuterADecl] ocAdtLayouts ocNestedPlainPlace ∧
      placeTyResolved [u32Decl "_0", ocOuterADecl] ocAdtLayouts ocNestedCastPlace =
        placeTyResolved [u32Decl "_0", ocOuterADecl] ocAdtLayouts ocNestedPlainPlace ∧
      placeTouchesUnion [u32Decl "_0", ocOuterADecl] ocAdtLayouts ocNestedCastPlace = false ∧
      placeTouchesUnion [u32Decl "_0", ocOuterADecl] ocAdtLayouts ocNestedPlainPlace = false ∧
      evalStmt ocNestedState ⟨.assign ocNestedPlainPlace (.use (cU32 42)), "w"⟩
          [u32Decl "_0", ocOuterADecl] ocAdtLayouts =
        MirStepNode.step (advanceStmt ocNestedState
          [.uninit, .init (.aggregate 0 [.aggregate 0 [.scalar ⟨42, 4⟩, .uninit]])]) ∧
      evalStmt ocNestedState ⟨.assign ocNestedCastPlace (.use (cU32 42)), "w"⟩
          [u32Decl "_0", ocOuterADecl] ocAdtLayouts =
        MirStepNode.step (advanceStmt ocNestedState
          [.uninit, .init (.aggregate 0 [.aggregate 0 [.scalar ⟨42, 4⟩, .uninit, .uninit]])]) ∧
      evalStmt ocNestedState ⟨.assign ocNestedCastPlace (.use (cU32 42)), "w"⟩
          [u32Decl "_0", ocOuterADecl] ocAdtLayouts ≠
        evalStmt ocNestedState ⟨.assign ocNestedPlainPlace (.use (cU32 42)), "w"⟩
          [u32Decl "_0", ocOuterADecl] ocAdtLayouts := by
  have h1 : placeTy [u32Decl "_0", pairDecl] wLayouts ⟨1, [.opaqueCast tyU8]⟩ = some tyU8 := rfl
  have h2 : placeTy [u32Decl "_0", pairDecl] wLayouts ⟨1, []⟩ = some tyPair := rfl
  have hnp :
      evalStmt ocNestedState ⟨.assign ocNestedPlainPlace (.use (cU32 42)), "w"⟩
          [u32Decl "_0", ocOuterADecl] ocAdtLayouts =
        MirStepNode.step (advanceStmt ocNestedState
          [.uninit, .init (.aggregate 0 [.aggregate 0 [.scalar ⟨42, 4⟩, .uninit]])]) := rfl
  have hnc :
      evalStmt ocNestedState ⟨.assign ocNestedCastPlace (.use (cU32 42)), "w"⟩
          [u32Decl "_0", ocOuterADecl] ocAdtLayouts =
        MirStepNode.step (advanceStmt ocNestedState
          [.uninit, .init (.aggregate 0 [.aggregate 0 [.scalar ⟨42, 4⟩, .uninit, .uninit]])]) := rfl
  refine ⟨h1, h2, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, hnp, hnc, ?_⟩
  · rw [h1, h2]
    intro h
    simp [tyU8, tyPair] at h
  · intro slot hslot
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hslot
    rcases hslot with rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩
  · rw [hnc, hnp]
    intro h
    have hl := congrArg (fun n : MirStepNode => match n with
      | .tau (.running st) => some st.frame.locals
      | _ => none) h
    simp [MirStepNode.step, advanceStmt] at hl

/-- **Positive witness (moves).** `move (p as T)` moves the *whole* local, exactly like its
post-borrowck erasure `move p`: it yields the value and de-initializes `p` — through one
cast, through a chain of casts, and with the body's declaration table (the moved value is
validated at the cast type). -/
theorem opaqueCast_witness_projected_move :
    evalOperand ocLocals (.move ⟨1, [.opaqueCast tyPair]⟩) = .ok pairVal [.uninit, .uninit] ∧
      evalOperand ocLocals (.move ⟨1, []⟩) = .ok pairVal [.uninit, .uninit] ∧
      evalOperand ocLocals (.move ⟨1, [.opaqueCast tyPair, .opaqueCast tyPair]⟩) =
        .ok pairVal [.uninit, .uninit] ∧
      evalOperand ocLocals (.move ⟨1, [.opaqueCast tyPair]⟩) [] [] wLayouts []
          [u32Decl "_0", pairDecl] =
        .ok pairVal [.uninit, .uninit] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `fn d(p: (u32, u32))`: its entry state holds `p = (7, 9)` in `_1` and an uninitialized
return place `_0` (exactly `ocLocals`). -/
def dBody : CapturedMir := mkBody "w::d" 1 [u32Decl "_0", pairDecl] [blk [] .return_]

def dInit : MachineState := initMachineStateWithCallees dBody [pairVal] []

/-- **Positive witness (root dispatch, `.uninit` field shell, and `SetDiscriminant`), with
fail-closed canaries.** Every statement through a pure opaque cast now steps exactly like its
post-borrowck erasure (`opaqueCast_trusted_root_dispatch_simulation`):
`(_0 as (u32, u32)) = p` and `(_0 as u32) = 42` initialize the uninitialized return place `_0`
like `_0 = …`; partial field initialization `(_1 as (u32, u32)).0 = 42` on an uninitialized
tuple `_1` materializes the tuple shell and writes field `0` like `_1.0 = 42`;
`Deinit((_1 as (u32, u32)))` stores `LocalSlot.uninit` like `Deinit(_1)`; and on a 2-variant
enum `OptU32` with captured `ocAdtLayouts`, `SetDiscriminant((_1 as OptU32), 0)` steps like
`SetDiscriminant(_1, 0)` both on an initialized `Some(7)` local and on an uninitialized one
(initializing `None`). Canaries: a write through a cast into a *dead* local is still UB, and a
cast directly before a dereference still fails closed with `.unsupported`. -/
theorem opaqueCast_witness_root_dispatch :
    writePlaceValue ocLocals [] ⟨0, [.opaqueCast tyPair]⟩ pairVal =
        .ok [.init pairVal, .init pairVal] ∧
      writePlaceValue ocLocals [] ⟨0, []⟩ pairVal = .ok [.init pairVal, .init pairVal] ∧
      dInit.frame.locals = ocLocals ∧
      evalStmt dInit ⟨.assign ⟨0, [.opaqueCast tyU32]⟩ (.use (cU32 42)), "w"⟩ dBody.localDecls
          wLayouts =
        MirStepNode.step (advanceStmt dInit [.init (.scalar ⟨42, 4⟩), .init pairVal]) ∧
      evalStmt dInit ⟨.assign ⟨0, []⟩ (.use (cU32 42)), "w"⟩ dBody.localDecls wLayouts =
        MirStepNode.step (advanceStmt dInit [.init (.scalar ⟨42, 4⟩), .init pairVal]) ∧
      evalStmt { dInit with frame := { dInit.frame with locals := [.uninit, .uninit] } }
          ⟨.assign (ocField 0) (.use (cU32 42)), "w"⟩ dBody.localDecls wLayouts =
        MirStepNode.step
          (advanceStmt dInit [.uninit, .init (.aggregate 0 [.scalar ⟨42, 4⟩, .uninit])]) ∧
      evalStmt { dInit with frame := { dInit.frame with locals := [.uninit, .uninit] } }
          ⟨.assign (plainField 0) (.use (cU32 42)), "w"⟩ dBody.localDecls wLayouts =
        MirStepNode.step
          (advanceStmt dInit [.uninit, .init (.aggregate 0 [.scalar ⟨42, 4⟩, .uninit])]) ∧
      evalStmt dInit ⟨.deinit ⟨1, [.opaqueCast tyPair]⟩, "w"⟩ dBody.localDecls wLayouts =
        MirStepNode.step (advanceStmt dInit [.uninit, .uninit]) ∧
      evalStmt dInit ⟨.deinit ⟨1, []⟩, "w"⟩ dBody.localDecls wLayouts =
        MirStepNode.step (advanceStmt dInit [.uninit, .uninit]) ∧
      evalStmt (ocDeinitState (.init (.aggregate 1 [.scalar ⟨7, 4⟩])))
          ⟨.setDiscriminant ⟨1, [.opaqueCast tyOcEnum]⟩ 0, "w"⟩ [u32Decl "_0", ocEnumDecl]
          ocAdtLayouts =
        MirStepNode.step (advanceStmt (ocDeinitState (.init (.aggregate 1 [.scalar ⟨7, 4⟩])))
          [.uninit, .init (.aggregate 0 [.scalar ⟨7, 4⟩])]) ∧
      evalStmt (ocDeinitState (.init (.aggregate 1 [.scalar ⟨7, 4⟩])))
          ⟨.setDiscriminant ⟨1, []⟩ 0, "w"⟩ [u32Decl "_0", ocEnumDecl] ocAdtLayouts =
        MirStepNode.step (advanceStmt (ocDeinitState (.init (.aggregate 1 [.scalar ⟨7, 4⟩])))
          [.uninit, .init (.aggregate 0 [.scalar ⟨7, 4⟩])]) ∧
      evalStmt (ocDeinitState .uninit)
          ⟨.setDiscriminant ⟨1, [.opaqueCast tyOcEnum]⟩ 0, "w"⟩ [u32Decl "_0", ocEnumDecl]
          ocAdtLayouts =
        MirStepNode.step (advanceStmt (ocDeinitState .uninit) [.uninit, .init (.aggregate 0 [])]) ∧
      evalStmt (ocDeinitState .uninit)
          ⟨.setDiscriminant ⟨1, []⟩ 0, "w"⟩ [u32Decl "_0", ocEnumDecl] ocAdtLayouts =
        MirStepNode.step (advanceStmt (ocDeinitState .uninit) [.uninit, .init (.aggregate 0 [])]) ∧
      writePlaceValue [.dead, .init pairVal] [] ⟨0, [.opaqueCast tyPair]⟩ pairVal = .ub ∧
      writePlaceValue ocLocals [] ⟨1, [.opaqueCast tyPair, .deref]⟩ pairVal = .unsupported :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Negative witnesses.** An opaque cast never masks UB: projecting a missing field
through it, or reading through it from an uninitialized or dead local, is UB exactly as
without it; an opaque cast directly before a dereference fails closed (`.unsupported`). -/
theorem opaqueCast_witness_ub_not_masked :
    evalOperand ocLocals (.copy (ocField 5)) = .ub ∧
      evalOperand ocLocals (.copy (ocField 5)) = evalOperand ocLocals (.copy (plainField 5)) ∧
      evalOperand [.uninit, .uninit] (.copy (ocField 0)) = .ub ∧
      evalOperand [.uninit, .dead] (.copy (ocField 0)) = .ub ∧
      evalOperand ocLocals (.copy ⟨1, [.opaqueCast tyPair, .deref]⟩) = .unsupported :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Negative witness (MiniRustSpec / LeanMiri).** The opaque-cast place has no MiniRust
translation (an assignment through it does not translate), and both concrete LeanMiri
projection paths reject it without a UB verdict. -/
theorem opaqueCast_witness_references_reject :
    MiniRustSpec.Correspondence.translatePlace [u32Decl "_0", pairDecl] (ocField 0) = none ∧
      MiniRustSpec.Correspondence.translateStatement [u32Decl "_0", pairDecl]
        ⟨.assign (ocField 0) (.use (cU32 42)), "w"⟩ wLayouts = none ∧
      MiniRustSpec.Correspondence.translatePlace [u32Decl "_0", pairDecl] (plainField 0) ≠ none ∧
      (LeanMiri.projectOpaqueCast (A := Nat) "T" = .error (.invariant "OpaqueCast after borrowck")) ∧
      (LeanMiri.placeProjectOpaqueCast (A := Nat) "T" =
        .error (.invalidProgram "OpaqueCast after borrowck")) :=
  ⟨rfl, rfl, by decide, rfl, rfl⟩

end OpaqueCast

/-! ## 4. `NonDivergingIntrinsic.copyNonOverlapping` through element sub-place pointers

`copy_nonoverlapping(src, dst, count)` over pointers to *elements* of an array
(`&raw const src[i]`, `&raw mut dst[j]`) formerly copied a single element whatever `count`
was. Trusted now resolves both element windows (`resolveCopySubplaceMulti`, then
`copySliceElements` / `copyBytesSubplace`) and copies `count` elements — or fails closed (UB
for a dead or missing root, a misaligned pointer, an out-of-bounds or overlapping window;
`.unsupported` for a byte window it cannot re-encode). Miri's `Intrinsics.copyWith` is
transcribed in `LeanMiri.copyWith`; upstream `minimize` has no lowering for the statement
(`span_bug!`, anchored above), so the `MiniRustSpec` correspondence is fail-closed. -/

section CopyNonOverlapping

def tyArrU32 (n : Nat) : Ty := { kind := .array (.uint .u32) n, layoutIdx := 0 }

def arrDecl (name : String) (n : Nat) : LocalDecl :=
  { mutability := .mut, ty := tyArrU32 n, debugName := some name }

def tyPtrConstU32 : Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 }

def cptrDecl (name : String) : LocalDecl :=
  { mutability := .mut, ty := tyPtrConstU32, debugName := some name }

def cUsize (v : Nat) : Operand :=
  .constant { ty := { kind := .uint .usize, layoutIdx := 0 }, val := .scalar (.int ⟨v, 8⟩) }

def arrLit (vs : List Nat) : Rvalue := .aggregate (.array tyU32) (vs.map cU32)

/-- The element place `_l[i]` of an `n`-element array local. -/
def elemPlace (l i n : Nat) : Place := ⟨l, [.constantIndex i n false]⟩

/-- `fn cp() -> u32 { let src = [..]; let mut dst = [..];
copy_nonoverlapping(&raw const src[i], &raw mut dst[j], count); dst[0] ^ dst[1] }`
(`_1 = src`, `_2 = dst`, `_3 = p`, `_4 = q`; the copy is statement `10`). -/
def cpBody (srcVals dstVals : List Nat) (srcIdx dstIdx count : Nat) : CapturedMir :=
  mkBody "w::cp" 0
    [u32Decl "_0", arrDecl "src" srcVals.length, arrDecl "dst" dstVals.length, cptrDecl "p",
     ptrDecl "q", u32Decl "t0", u32Decl "t1"]
    [blk [st (.storageLive 1), st (.storageLive 2), st (.storageLive 3), st (.storageLive 4),
          st (.storageLive 5), st (.storageLive 6),
          st (.assign (lc 1) (arrLit srcVals)), st (.assign (lc 2) (arrLit dstVals)),
          st (.assign (lc 3) (.rawPtr .not (elemPlace 1 srcIdx srcVals.length))),
          st (.assign (lc 4) (.rawPtr .mut (elemPlace 2 dstIdx dstVals.length))),
          st (.intrinsic (.copyNonOverlapping (.copy (lc 3)) (.copy (lc 4)) (cUsize count))),
          st (.assign (lc 5) (.use (.copy (elemPlace 2 0 dstVals.length)))),
          st (.assign (lc 6) (.use (.copy (elemPlace 2 1 dstVals.length)))),
          st (.assign (lc 0) (.binaryOp .bitXor (.copy (lc 5)) (.copy (lc 6))))] .return_]

/-- Same-array copy `copy_nonoverlapping(&raw const a[i], &raw mut a[j], count)`, returning
`a[k]` (`_1 = a`; the copy is statement `6`). -/
def cpSameBody (vals : List Nat) (srcIdx dstIdx count k : Nat) : CapturedMir :=
  mkBody "w::cps" 0 [u32Decl "_0", arrDecl "a" vals.length, cptrDecl "p", ptrDecl "q"]
    [blk [st (.storageLive 1), st (.storageLive 2), st (.storageLive 3),
          st (.assign (lc 1) (arrLit vals)),
          st (.assign (lc 2) (.rawPtr .not (elemPlace 1 srcIdx vals.length))),
          st (.assign (lc 3) (.rawPtr .mut (elemPlace 1 dstIdx vals.length))),
          st (.intrinsic (.copyNonOverlapping (.copy (lc 2)) (.copy (lc 3)) (cUsize count))),
          st (.assign (lc 0) (.use (.copy (elemPlace 1 k vals.length))))] .return_]

/-- `fn cpc(p: *const u32, q: *mut u32) -> u32 { copy_nonoverlapping(p, q, count); 1 }`: a
modular root whose pointers address its external caller's memory. -/
def cpCallerBody (count : Nat) : CapturedMir :=
  mkBody "w::cpc" 2 [u32Decl "_0", cptrDecl "p", ptrDecl "q"]
    [blk [st (.intrinsic (.copyNonOverlapping (.copy (lc 1)) (.copy (lc 2)) (cUsize count))),
          assignU32 0 1] .return_]

/-- The external caller owns `[22, 99]` (depth-`0` slot `3`, element `0` borrowed read-only by
tag `1`) and `[0, 0]` (slot `4`, element `0` borrowed mutably by tag `2`). -/
def cpCallerMem (callees : List CapturedMir) : Memory :=
  { callees := callees,
    callerLocals := [.uninit, .uninit, .uninit,
      .init (.aggregate 0 [.scalar ⟨22, 4⟩, .scalar ⟨99, 4⟩]),
      .init (.aggregate 0 [.scalar ⟨0, 4⟩, .scalar ⟨0, 4⟩])],
    borrows := [{ tag := 1, targetLocal := 3, targetProjection := [.constantIndex 0 2 false],
                  perm := .frozen },
                { tag := 2, targetLocal := 4, targetProjection := [.constantIndex 0 2 false],
                  perm := .unique }],
    nextTag := 3 }

/-- `fn gcp(p: *const u32, q: *mut u32, a: u32, b: u32) -> u32 { copy_nonoverlapping(p, q, 2);
1 }` (five locals). -/
def gCpBody : CapturedMir :=
  mkBody "w::gcp" 4 [u32Decl "_0", cptrDecl "p", ptrDecl "q", u32Decl "a", u32Decl "b"]
    [blk [st (.intrinsic (.copyNonOverlapping (.copy (lc 1)) (.copy (lc 2)) (cUsize 2))),
          assignU32 0 1] .return_]

/-- `fn fcp(p: *const u32, q: *mut u32) -> u32 { become gcp(p, q, 5, 6) }` (three locals). -/
def fCpBody : CapturedMir :=
  mkBody "w::fcp" 2 [u32Decl "_0", cptrDecl "p", ptrDecl "q"]
    [blk [] (.tailCall (fnItem "w::gcp") [.copy (lc 1), .copy (lc 2), cU32 5, cU32 6])]

def tyArrU8 (n : Nat) : Ty := { kind := .array (.uint .u8) n, layoutIdx := 0 }

def tyPtrConstU8 : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 0 }

def tyPtrMutU8 : Ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }

def ptrOf (t : Ty) (name : String) : LocalDecl :=
  { mutability := .mut, ty := t, debugName := some name }

/-- `fn bp() -> u8 { let word: u32 = w; let mut bytes = [0u8; 4];
let p = (&raw const word as *const u8).offset(off); let q = &raw mut bytes[j];
copy_nonoverlapping(p, q, n); bytes[k] }` (`_1 = word`, `_2 = bytes`; the copy is statement
`12`): a byte-punned copy out of a scalar. -/
def bytePunBody (w off j n k : Nat) : CapturedMir :=
  mkBody "w::bp" 0
    [{ mutability := .mut, ty := tyU8, debugName := some "_0" }, u32Decl "word",
     { mutability := .mut, ty := tyArrU8 4, debugName := some "bytes" }, cptrDecl "pw",
     ptrOf tyPtrConstU8 "p", ptrOf tyPtrConstU8 "p2", ptrOf tyPtrMutU8 "q"]
    [blk [st (.storageLive 1), st (.storageLive 2), st (.storageLive 3), st (.storageLive 4),
          st (.storageLive 5), st (.storageLive 6),
          assignU32 1 w,
          st (.assign (lc 2) (.aggregate (.array tyU8) [cU8 0, cU8 0, cU8 0, cU8 0])),
          st (.assign (lc 3) (.rawPtr .not (lc 1))),
          st (.assign (lc 4) (.cast .ptrToPtr (.copy (lc 3)) tyPtrConstU8)),
          st (.assign (lc 5) (.binaryOp .offset (.copy (lc 4))
            (.constant { ty := { kind := .int .isize, layoutIdx := 0 },
                         val := .scalar (.int ⟨off, 8⟩) }))),
          st (.assign (lc 6) (.rawPtr .mut (elemPlace 2 j 4))),
          st (.intrinsic (.copyNonOverlapping (.copy (lc 5)) (.copy (lc 6)) (cUsize n))),
          st (.assign (lc 0) (.use (.copy (elemPlace 2 k 4))))] .return_]

/-- `fn cpo() -> u32 { let src = [..]; let mut dst = [..];
let p = (&raw const src[0]).offset(srcOff); let q = (&raw mut dst[0]).offset(dstOff);
copy_nonoverlapping(p, q, count); dst[0] }`: element-window copy through non-zero
`BinOp.offset` byte offsets (the copy is statement `12`). -/
def cpOffsetBody (srcVals dstVals : List Nat) (srcOff dstOff count : Nat) : CapturedMir :=
  mkBody "w::cpo" 0
    [u32Decl "_0", arrDecl "src" srcVals.length, arrDecl "dst" dstVals.length, cptrDecl "p0",
     cptrDecl "p", ptrDecl "q0", ptrDecl "q"]
    [blk [st (.storageLive 1), st (.storageLive 2), st (.storageLive 3), st (.storageLive 4),
          st (.storageLive 5), st (.storageLive 6),
          st (.assign (lc 1) (arrLit srcVals)), st (.assign (lc 2) (arrLit dstVals)),
          st (.assign (lc 3) (.rawPtr .not (elemPlace 1 0 srcVals.length))),
          st (.assign (lc 4) (.binaryOp .offset (.copy (lc 3))
            (.constant { ty := { kind := .int .isize, layoutIdx := 0 },
                         val := .scalar (.int ⟨srcOff, 8⟩) }))),
          st (.assign (lc 5) (.rawPtr .mut (elemPlace 2 0 dstVals.length))),
          st (.assign (lc 6) (.binaryOp .offset (.copy (lc 5))
            (.constant { ty := { kind := .int .isize, layoutIdx := 0 },
                         val := .scalar (.int ⟨dstOff, 8⟩) }))),
          st (.intrinsic (.copyNonOverlapping (.copy (lc 4)) (.copy (lc 6)) (cUsize count))),
          st (.assign (lc 0) (.use (.copy (elemPlace 2 0 dstVals.length))))] .return_]

/-- `fn bpd() -> u8 { let word: u32 = w; let mut bytes = [0u8; dstLen];
let p = &raw const word as *const u8; let q = (&raw mut bytes[0]).offset(dstOff);
copy_nonoverlapping(p, q, n); bytes[dstOff] }`: byte-punned write at a non-zero destination
byte offset (the copy is statement `12`). -/
def bytePunDstOffsetBody (w dstLen dstOff n : Nat) : CapturedMir :=
  mkBody "w::bpd" 0
    [{ mutability := .mut, ty := tyU8, debugName := some "_0" }, u32Decl "word",
     { mutability := .mut, ty := tyArrU8 dstLen, debugName := some "bytes" }, cptrDecl "pw",
     ptrOf tyPtrConstU8 "p", ptrOf tyPtrMutU8 "q0", ptrOf tyPtrMutU8 "q"]
    [blk [st (.storageLive 1), st (.storageLive 2), st (.storageLive 3), st (.storageLive 4),
          st (.storageLive 5), st (.storageLive 6),
          assignU32 1 w,
          st (.assign (lc 2) (.aggregate (.array tyU8) (List.replicate dstLen (cU8 0)))),
          st (.assign (lc 3) (.rawPtr .not (lc 1))),
          st (.assign (lc 4) (.cast .ptrToPtr (.copy (lc 3)) tyPtrConstU8)),
          st (.assign (lc 5) (.rawPtr .mut (elemPlace 2 0 dstLen))),
          st (.assign (lc 6) (.binaryOp .offset (.copy (lc 5))
            (.constant { ty := { kind := .int .isize, layoutIdx := 0 },
                         val := .scalar (.int ⟨dstOff, 8⟩) }))),
          st (.intrinsic (.copyNonOverlapping (.copy (lc 4)) (.copy (lc 6)) (cUsize n))),
          st (.assign (lc 0) (.use (.copy (elemPlace 2 dstOff dstLen))))] .return_]

/-- `fn bps() -> u32 { let src = [..]; let mut word: u32 = 0;
let p = (&raw const src[0]).offset(srcOff); let q = &raw mut word as *mut u8;
copy_nonoverlapping(p, q, n); word }`: byte-punned read from a non-zero source byte offset
into a scalar (the copy is statement `12`). -/
def bytePunSrcToWordBody (srcBytes : List Nat) (srcOff n : Nat) : CapturedMir :=
  mkBody "w::bps" 0
    [u32Decl "_0", { mutability := .mut, ty := tyArrU8 srcBytes.length, debugName := some "src" },
     u32Decl "word", ptrOf tyPtrConstU8 "p0", ptrOf tyPtrConstU8 "p", ptrDecl "qw",
     ptrOf tyPtrMutU8 "q"]
    [blk [st (.storageLive 1), st (.storageLive 2), st (.storageLive 3), st (.storageLive 4),
          st (.storageLive 5), st (.storageLive 6),
          st (.assign (lc 1) (.aggregate (.array tyU8) (srcBytes.map cU8))),
          assignU32 2 0,
          st (.assign (lc 3) (.rawPtr .not (elemPlace 1 0 srcBytes.length))),
          st (.assign (lc 4) (.binaryOp .offset (.copy (lc 3))
            (.constant { ty := { kind := .int .isize, layoutIdx := 0 },
                         val := .scalar (.int ⟨srcOff, 8⟩) }))),
          st (.assign (lc 5) (.rawPtr .mut (lc 2))),
          st (.assign (lc 6) (.cast .ptrToPtr (.copy (lc 5)) tyPtrMutU8)),
          st (.intrinsic (.copyNonOverlapping (.copy (lc 4)) (.copy (lc 6)) (cUsize n))),
          st (.assign (lc 0) (.use (.copy (lc 2))))] .return_]

def tyU16 : Ty := { kind := .uint .u16, layoutIdx := 0 }
def tyArrU16 (n : Nat) : Ty := { kind := .array (.uint .u16) n, layoutIdx := 0 }
def tyPtrConstU16 : Ty := { kind := .rawPtr .not (.uint .u16), layoutIdx := 0 }
def tyPtrMutU16 : Ty := { kind := .rawPtr .mut (.uint .u16), layoutIdx := 0 }
def cU16 (v : Nat) : Operand := .constant { ty := tyU16, val := .scalar (.int ⟨v, 2⟩) }

def tyU64 : Ty := { kind := .uint .u64, layoutIdx := 0 }
def u64Decl (name : String) : LocalDecl := { mutability := .mut, ty := tyU64, debugName := some name }
def cU64 (v : Nat) : Operand := .constant { ty := tyU64, val := .scalar (.int ⟨v, 8⟩) }
def tyPtrConstU64 : Ty := { kind := .rawPtr .not (.uint .u64), layoutIdx := 0 }

/-- Type-confused byte splice into a non-byte container (`u64` copied as `8` `u8` bytes into
`&raw mut dst[0]` of `[u32; 4]`): neither `dst[0]` (`4` bytes) nor `[u32; 4]` (`16` bytes) matches
`8` bytes and `[u32; 4]` is not a byte container, so `copyBytesSubplace` must fail closed
(`.unsupported`), never placing `u8` scalars inside `[u32; 4]` (copy is statement `12`). -/
def byteSpliceNonByteBody : CapturedMir :=
  mkBody "w::bsnb" 0
    [u32Decl "_0", u64Decl "word", arrDecl "dst" 4, ptrOf tyPtrConstU64 "pw",
     ptrOf tyPtrConstU8 "p", ptrDecl "qd", ptrOf tyPtrMutU8 "q"]
    [blk [st (.storageLive 1), st (.storageLive 2), st (.storageLive 3), st (.storageLive 4),
          st (.storageLive 5), st (.storageLive 6),
          st (.assign (lc 1) (.use (cU64 0x0807060504030201))),
          st (.assign (lc 2) (arrLit [0, 0, 0, 0])),
          st (.assign (lc 3) (.rawPtr .not (lc 1))),
          st (.assign (lc 4) (.cast .ptrToPtr (.copy (lc 3)) tyPtrConstU8)),
          st (.assign (lc 5) (.rawPtr .mut (elemPlace 2 0 4))),
          st (.assign (lc 6) (.cast .ptrToPtr (.copy (lc 5)) tyPtrMutU8)),
          st (.intrinsic (.copyNonOverlapping (.copy (lc 4)) (.copy (lc 6)) (cUsize 8))),
          st (.assign (lc 0) (.use (.copy (elemPlace 2 0 4))))] .return_]

/-- Element-stride mismatch (`[u8; 4]` cast to `*const u16` copied into `[u16; 2]`): must fail
closed (`.unsupported`), never placing `u8` scalars into `[u16; 2]` (copy is statement `10`). -/
def strideMismatchBody : CapturedMir :=
  mkBody "w::csm" 0
    [u32Decl "_0", { mutability := .mut, ty := tyArrU8 4, debugName := some "src" },
     { mutability := .mut, ty := tyArrU16 2, debugName := some "dst" },
     ptrOf tyPtrConstU8 "p0", ptrOf tyPtrConstU16 "p", ptrOf tyPtrMutU16 "q"]
    [blk [st (.storageLive 1), st (.storageLive 2), st (.storageLive 3), st (.storageLive 4),
          st (.storageLive 5),
          st (.assign (lc 1) (.aggregate (.array tyU8) [cU8 1, cU8 2, cU8 3, cU8 4])),
          st (.assign (lc 2) (.aggregate (.array tyU16) [cU16 0, cU16 0])),
          st (.assign (lc 3) (.rawPtr .not (elemPlace 1 0 4))),
          st (.assign (lc 4) (.cast .ptrToPtr (.copy (lc 3)) tyPtrConstU16)),
          st (.assign (lc 5) (.rawPtr .mut (elemPlace 2 0 2))),
          st (.intrinsic (.copyNonOverlapping (.copy (lc 4)) (.copy (lc 5)) (cUsize 2))),
          assignU32 0 1] .return_]

/-- Same-tag copy `copy_nonoverlapping(p as *const u32, p, 2)` on `[u32; 4]` (copy is statement
`6`): UB. -/
def cpSameTagBody : CapturedMir :=
  mkBody "w::cpst" 0 [u32Decl "_0", arrDecl "a" 4, ptrDecl "p", cptrDecl "pc"]
    [blk [st (.storageLive 1), st (.storageLive 2), st (.storageLive 3),
          st (.assign (lc 1) (arrLit [1, 2, 3, 4])),
          st (.assign (lc 2) (.rawPtr .mut (elemPlace 1 0 4))),
          st (.assign (lc 3) (.cast .ptrToPtr (.copy (lc 2)) tyPtrConstU32)),
          st (.intrinsic (.copyNonOverlapping (.copy (lc 3)) (.copy (lc 2)) (cUsize 2))),
          assignU32 0 1] .return_]

/-- Caller memory with additional foreign `.unique` borrows (tags `10` on source slot `3`,
`11` on destination slot `4`) to witness Tree Borrows read-then-write transitions during
`copy_nonoverlapping`. -/
def cpCallerTbMem : Memory :=
  { (cpCallerMem []) with
    borrows := [
      { tag := 1, targetLocal := 3, targetProjection := [.constantIndex 0 2 false], perm := .frozen },
      { tag := 2, targetLocal := 4, targetProjection := [.constantIndex 0 2 false], perm := .unique },
      { tag := 10, targetLocal := 3, targetProjection := [.constantIndex 0 2 false], perm := .unique },
      { tag := 11, targetLocal := 4, targetProjection := [.constantIndex 0 2 false], perm := .unique }
    ],
    nextTag := 12 }

def tyPtrUnit : Ty := { kind := .rawPtr .mut (.tuple []), layoutIdx := 0 }

def tyPtrZstArr : Ty := { kind := .rawPtr .mut (.array (.uint .u32) 0), layoutIdx := 0 }

/-- A live `unique` borrow of the whole local `l`. -/
def entryAt (tag l : Nat) : BorrowEntry :=
  { tag := tag, targetLocal := l, targetProjection := [], perm := .unique }

/-- `resolveCopySubplaceMulti` for `copy_nonoverlapping(copy _3, copy _4, n)` in a frame whose
pointers `_3` / `_4` (of type `ptrTy`, byte offsets `srcOff` / `dstOff`) borrow the roots `_1` /
`_2`, which hold `srcSlot` / `dstSlot`. -/
def copyNonOverlappingResolve (ptrTy : Ty) (srcSlot dstSlot : LocalSlot) (srcOff dstOff n : Nat) :
    CopySliceOutcome :=
  resolveCopySubplaceMulti [] [] (.copy (lc 3)) (.copy (lc 4))
    [u32Decl "_0", u32Decl "a", u32Decl "b", ptrOf ptrTy "p", ptrOf ptrTy "q"] wLayouts
    ⟨1, srcOff⟩ ⟨2, dstOff⟩ (entryAt 1 1) (entryAt 2 2) n
    [.uninit, srcSlot, dstSlot, .init (.ptr ⟨1, srcOff⟩ 8), .init (.ptr ⟨2, dstOff⟩ 8)]

/-- The same resolution with a source borrow that names a slot (`9`) that exists nowhere. -/
def copyNonOverlappingResolveMissing : CopySliceOutcome :=
  resolveCopySubplaceMulti [] [] (.copy (lc 3)) (.copy (lc 4))
    [u32Decl "_0", u32Decl "a", u32Decl "b", ptrOf tyPtrUnit "p", ptrOf tyPtrUnit "q"] wLayouts
    ⟨1, 0⟩ ⟨2, 0⟩ (entryAt 1 9) (entryAt 2 2) 5
    [.uninit, .uninit, .uninit, .init (.ptr ⟨1, 0⟩ 8), .init (.ptr ⟨2, 0⟩ 8)]

/-- `n` steps of a body from its entry state (no arguments, no callees). -/
def cpRun (b : CapturedMir) (n : Nat) : Option MirExecState :=
  execN b n (.running (initMachineStateWithCallees b [] []))

/-- `n` steps of a modular root entered with `args` in the memory `mem`. -/
def cpRunMem (b : CapturedMir) (args : List Value) (mem : Memory) (n : Nat) :
    Option MirExecState :=
  execN b n (.running (Trusted.VerificationResult.initMachineStateWithMemory b args mem))

/-- The bit patterns of a list of scalars. -/
def scalarBitsList? : List Value → Option (List Nat)
  | [] => some []
  | .scalar sc :: rest => (scalarBitsList? rest).map (sc.bits :: ·)
  | _ :: _ => none

/-- The element bit patterns of an initialized aggregate slot. -/
def slotScalars? : LocalSlot → Option (List Nat)
  | .init (.aggregate _ fs) => scalarBitsList? fs
  | _ => none

/-- The element bit patterns of the aggregate local `_i` of a running state. -/
def localScalars? (r : Option MirExecState) (i : Nat) : Option (List Nat) :=
  match r with
  | some (.running s) => (get? s.frame.locals i).bind slotScalars?
  | _ => none

/-- The element bit patterns of the caller-owned aggregate slot `i` of a running state. -/
def callerScalars? (r : Option MirExecState) (i : Nat) : Option (List Nat) :=
  match r with
  | some (.running s) => (get? s.memory.callerLocals i).bind slotScalars?
  | _ => none

/-- The bit pattern of the scalar a halted state returned. -/
def haltedBits? : Option MirExecState → Option Nat
  | some (.halted (.normal (.scalar sc, _))) => some sc.bits
  | _ => none

/-- Whether a state is an `.unsupported` (fail-closed) fault. -/
def isUnsupportedFault : Option MirExecState → Bool
  | some (.faulted .unsupported) => true
  | _ => false

/-- The `(tag, permCode)` summary of the borrow table of a running state (for `decide +kernel`):
`0 = reserved`, `1 = reservedFrz`, `2 = unique`, `3 = frozen`, `4 = disabled`, `5 = other`. -/
def borrowTagPerms? : Option MirExecState → Option (List (Nat × Nat))
  | some (.running s) =>
    some (s.memory.borrows.map fun e =>
      (e.tag, match e.perm with
        | .reserved => 0
        | .reservedFrz _ => 1
        | .unique => 2
        | .frozen => 3
        | .disabled => 4
        | .cell => 5
        | .reservedIM => 6))
  | _ => none

/-- The alignment verdict of `resolveCopySubplaceMulti`: both pointers are aligned for their
pointee types (`checkDerefAlign` at the pointers' byte offsets). -/
def cpAligned (decls : List LocalDecl) (layouts : LayoutTable) (src dst : Operand)
    (srcPtr dstPtr : ProvenancePtr) : Bool :=
  Bool.and
    (checkDerefAlign decls layouts (operandPointeeTy decls layouts src) srcPtr.offsetBytes)
    (checkDerefAlign decls layouts (operandPointeeTy decls layouts dst) dstPtr.offsetBytes)

/-- **Trusted `copy_nonoverlapping` sub-place resolution (universal).** The statement is
evaluated by `evalCopyNonOverlapping`, and for a copy of `n ≥ 1` elements between two
stack-borrowed sub-places `resolveCopySubplaceMulti` decides, in this order, for *every*
operand pair, declaration table, pointer pair, and borrow pair whose roots live in the active
frame:
* a **dead** source or destination root is UB — also for a zero-sized pointee;
* a **misaligned** source or destination pointer (`cpAligned = false`) is UB — also for a
  zero-sized pointee, whatever the roots hold;
* with both pointers aligned and compatible pointee sizes, a **zero-sized** pointee is a
  no-op for every `n`, even over uninitialized roots (a ZST copy reads and writes no bytes);
* a non-zero-sized copy out of an **uninitialized** source root is UB;
and a source borrow whose root slot exists neither in the frame nor among the caller-owned
referents is UB. The element-window copy itself (`copySliceElements`) is characterized by
`copyNonOverlapping_trusted_elem_window_universal` and pinned by the witnesses below.
A `count = 0` copy never reaches this resolution: Trusted steps without the alignment check,
whereas Miri checks alignment "including for zero-length copies"
(`copyNonOverlapping_leanMiri_check_order`) — a pre-existing, documented difference outside
this file's scope (`LeanMiriSpec`'s `wit_lm4_2_copy_nonoverlapping_zero_misaligned_divergence`). -/
theorem copyNonOverlapping_trusted_subplace_resolution_universal
    (callerLocals : List LocalSlot) (callStack : List SavedCallerFrame) (src dst : Operand)
    (decls : List LocalDecl) (layouts : LayoutTable) (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry) (n : Nat) (locals : List LocalSlot) :
    (∀ (s : MachineState) (count : Operand) (span : String),
      evalStmt s ⟨.intrinsic (.copyNonOverlapping src dst count), span⟩ decls layouts =
        evalCopyNonOverlapping s src dst count decls layouts) ∧
    (∀ (srcSlot dstSlot : LocalSlot),
      get? locals srcEntry.targetLocal = some srcSlot →
      get? locals dstEntry.targetLocal = some dstSlot →
      (srcSlot = .dead ∨ dstSlot = .dead →
        resolveCopySubplaceMulti callerLocals callStack src dst decls layouts srcPtr dstPtr
          srcEntry dstEntry n locals = .ub) ∧
      (srcSlot ≠ .dead → dstSlot ≠ .dead →
        cpAligned decls layouts src dst srcPtr dstPtr = false →
        resolveCopySubplaceMulti callerLocals callStack src dst decls layouts srcPtr dstPtr
          srcEntry dstEntry n locals = .ub) ∧
      (srcSlot ≠ .dead → dstSlot ≠ .dead →
        cpAligned decls layouts src dst srcPtr dstPtr = true →
        copyPointeeSizesConflict decls layouts (operandPointeeTy decls layouts src)
          (operandPointeeTy decls layouts dst) = false →
        copyPointeeByteSize? decls layouts (operandPointeeTy decls layouts src)
          (operandPointeeTy decls layouts dst) = some 0 →
        resolveCopySubplaceMulti callerLocals callStack src dst decls layouts srcPtr dstPtr
          srcEntry dstEntry n locals = .noop) ∧
      (srcSlot = .uninit → dstSlot ≠ .dead →
        cpAligned decls layouts src dst srcPtr dstPtr = true →
        copyPointeeSizesConflict decls layouts (operandPointeeTy decls layouts src)
          (operandPointeeTy decls layouts dst) = false →
        ∀ k : Nat,
          copyPointeeByteSize? decls layouts (operandPointeeTy decls layouts src)
            (operandPointeeTy decls layouts dst) = some (k + 1) →
          resolveCopySubplaceMulti callerLocals callStack src dst decls layouts srcPtr dstPtr
            srcEntry dstEntry n locals = .ub)) ∧
    (∀ (dstSlot : LocalSlot),
      get? locals srcEntry.targetLocal = none →
      get? callerLocals srcEntry.targetLocal = none →
      get? callerLocals (Nat.sub srcEntry.targetLocal (length locals)) = none →
      get? locals dstEntry.targetLocal = some dstSlot →
      resolveCopySubplaceMulti callerLocals callStack src dst decls layouts srcPtr dstPtr
        srcEntry dstEntry n locals = .ub) := by
  refine ⟨fun _ _ _ => rfl, ?_, ?_⟩
  · intro srcSlot dstSlot hs hd
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro (h | h)
      · subst h
        cases dstSlot <;> simp only [resolveCopySubplaceMulti, hs, hd]
      · subst h
        cases srcSlot <;> simp only [resolveCopySubplaceMulti, hs, hd]
    · intro hsn hdn ha
      unfold cpAligned at ha
      cases srcSlot with
      | dead => exact absurd rfl hsn
      | _ =>
        cases dstSlot with
        | dead => exact absurd rfl hdn
        | _ => simp only [resolveCopySubplaceMulti, hs, hd, ha]
    · intro hsn hdn ha hc hz
      unfold cpAligned at ha
      have hz' : copyPointeeByteSize? decls layouts (operandPointeeTy decls layouts src)
          (operandPointeeTy decls layouts dst) = some Nat.zero := hz
      cases srcSlot with
      | dead => exact absurd rfl hsn
      | _ =>
        cases dstSlot with
        | dead => exact absurd rfl hdn
        | _ => simp only [resolveCopySubplaceMulti, hs, hd, ha, hc, hz']
    · intro hsu hdn ha hc k hk
      subst hsu
      unfold cpAligned at ha
      cases dstSlot with
      | dead => exact absurd rfl hdn
      | _ => simp only [resolveCopySubplaceMulti, hs, hd, ha, hc, hk]
  · intro dstSlot h1 h2 h3 hd
    cases dstSlot <;> simp only [resolveCopySubplaceMulti, h1, h2, h3, hd]

/-- The stride guard of `copySliceElements`: the two pointee types are compatible and each
array's element type and size agree with the copied element size `sz`. -/
def copyNonOverlappingStrideOk (decls : List LocalDecl) (layouts : LayoutTable)
    (locals : List LocalSlot) (srcEp dstEp : CopyEndpoint) (sz : Nat)
    (srcParentProj : List ProjectionElem) (srcElems : List Value)
    (dstParentProj : List ProjectionElem) (dstElems : List Value) : Bool :=
  Bool.and
    (copySlicePointeesCompatible srcEp.pointeeOpt dstEp.pointeeOpt)
    (Bool.and
      (copyContainerStrideOk
        (copyContainerElemKind? decls layouts locals srcEp.entry.targetLocal srcParentProj)
        (copyEffectivePointee? srcEp.pointeeOpt dstEp.pointeeOpt) srcElems (some sz))
      (copyContainerStrideOk
        (copyContainerElemKind? decls layouts locals dstEp.entry.targetLocal dstParentProj)
        (copyEffectivePointee? srcEp.pointeeOpt dstEp.pointeeOpt) dstElems (some sz)))

/-- **Trusted element-window copy (universal).** Once both pointers resolve to element windows
— the source starting `srcOff` elements past index `srcBaseIdx` of the array `srcElems`, the
destination `dstOff` elements past `dstBaseIdx` of `dstElems`, for a known element size `sz` —
`copySliceElements` copies **exactly `n` elements**, for every `n`:
* when both windows lie inside their arrays, the stride guard holds, and the windows do not
  overlap (pointers with distinct tags into distinct locals, or into disjoint ranges of the
  same local), the destination array becomes `dstElems` with its `n` elements from the
  destination start replaced by the `n` source elements from the source start
  (`spliceValues (takeValues n (dropValues …))`) — the former single-element copy wrote one
  element whatever `n` was — and the Tree Borrows accesses are exactly the two `n`-element
  windows (`copySliceWindowProj`);
* when the in-bounds windows overlap (the same pointer tag, or overlapping ranges of the same
  local), the copy is UB, as `copy_nonoverlapping` requires;
* when a window leaves its array and either access is certainly outside its allocation
  (`copyAccessFitsAlloc? = some false`), the copy is UB;
* in every out-of-array case, the outcome is `.ub` or `.unsupported` — never `.write` and never
  a silent `.noop`. -/
theorem copyNonOverlapping_trusted_elem_window_universal
    (decls : List LocalDecl) (layouts : LayoutTable) (locals callerLocals : List LocalSlot)
    (callStack : List SavedCallerFrame) (srcEp dstEp : CopyEndpoint) (sz n : Nat)
    (srcParentProj : List ProjectionElem) (srcBaseIdx : Nat) (srcElems : List Value)
    (dstParentProj : List ProjectionElem) (dstBaseIdx : Nat) (dstElems : List Value)
    (srcOff dstOff : Nat)
    (hso : byteOffsetToElemIdx? srcEp.ptr.offsetBytes sz = some srcOff)
    (hdo : byteOffsetToElemIdx? dstEp.ptr.offsetBytes sz = some dstOff) :
    (Bool.and (Nat.ble (Nat.add (Nat.add srcBaseIdx srcOff) n) (length srcElems))
          (Nat.ble (Nat.add (Nat.add dstBaseIdx dstOff) n) (length dstElems)) = true →
      copyNonOverlappingStrideOk decls layouts locals srcEp dstEp sz srcParentProj srcElems
          dstParentProj dstElems = true →
      Nat.beq srcEp.ptr.tag dstEp.ptr.tag = false →
      (Nat.beq srcEp.entry.targetLocal dstEp.entry.targetLocal = false ∨
        projectionsOverlap
            (copySliceWindowProj srcParentProj (Nat.add srcBaseIdx srcOff) n (length srcElems))
            (copySliceWindowProj dstParentProj (Nat.add dstBaseIdx dstOff) n (length dstElems)) =
          false) →
      copySliceElements decls layouts locals callerLocals callStack srcEp dstEp (some sz) n
          srcParentProj srcBaseIdx srcElems dstParentProj dstBaseIdx dstElems =
        .write ⟨dstEp.entry.targetLocal, dstParentProj⟩
          (.aggregate 0
            (spliceValues (takeValues n (dropValues (Nat.add srcBaseIdx srcOff) srcElems))
              (Nat.add dstBaseIdx dstOff) dstElems))
          (copySliceWindowProj srcParentProj (Nat.add srcBaseIdx srcOff) n (length srcElems))
          (copySliceWindowProj dstParentProj (Nat.add dstBaseIdx dstOff) n (length dstElems))) ∧
    (Bool.and (Nat.ble (Nat.add (Nat.add srcBaseIdx srcOff) n) (length srcElems))
          (Nat.ble (Nat.add (Nat.add dstBaseIdx dstOff) n) (length dstElems)) = true →
      copyNonOverlappingStrideOk decls layouts locals srcEp dstEp sz srcParentProj srcElems
          dstParentProj dstElems = true →
      (Nat.beq srcEp.ptr.tag dstEp.ptr.tag = true ∨
        (Nat.beq srcEp.entry.targetLocal dstEp.entry.targetLocal = true ∧
          projectionsOverlap
              (copySliceWindowProj srcParentProj (Nat.add srcBaseIdx srcOff) n (length srcElems))
              (copySliceWindowProj dstParentProj (Nat.add dstBaseIdx dstOff) n (length dstElems)) =
            true)) →
      copySliceElements decls layouts locals callerLocals callStack srcEp dstEp (some sz) n
          srcParentProj srcBaseIdx srcElems dstParentProj dstBaseIdx dstElems = .ub) ∧
    (Bool.and (Nat.ble (Nat.add (Nat.add srcBaseIdx srcOff) n) (length srcElems))
          (Nat.ble (Nat.add (Nat.add dstBaseIdx dstOff) n) (length dstElems)) = false →
      (copyAccessCertainlyOob
          (copyAccessFitsAlloc? decls layouts locals callerLocals callStack srcEp (Nat.mul n sz)) =
          true ∨
        copyAccessCertainlyOob
          (copyAccessFitsAlloc? decls layouts locals callerLocals callStack dstEp (Nat.mul n sz)) =
          true) →
      copySliceElements decls layouts locals callerLocals callStack srcEp dstEp (some sz) n
          srcParentProj srcBaseIdx srcElems dstParentProj dstBaseIdx dstElems = .ub) ∧
    (Bool.and (Nat.ble (Nat.add (Nat.add srcBaseIdx srcOff) n) (length srcElems))
          (Nat.ble (Nat.add (Nat.add dstBaseIdx dstOff) n) (length dstElems)) = false →
      let out := copySliceElements decls layouts locals callerLocals callStack srcEp dstEp
        (some sz) n srcParentProj srcBaseIdx srcElems dstParentProj dstBaseIdx dstElems
      out = .ub ∨ out = .unsupported) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hin hstride htag hdis
    unfold copyNonOverlappingStrideOk at hstride
    rcases hdis with hloc | hov
    · simp only [copySliceElements, copyEffElemSize?, hso, hdo, hin, hstride, htag, hloc]
    · cases hloc : Nat.beq srcEp.entry.targetLocal dstEp.entry.targetLocal <;>
        simp only [copySliceElements, copyEffElemSize?, hso, hdo, hin, hstride, htag, hloc, hov]
  · intro hin hstride hov
    unfold copyNonOverlappingStrideOk at hstride
    rcases hov with htag | ⟨hloc, hov⟩
    · simp only [copySliceElements, copyEffElemSize?, hso, hdo, hin, hstride, htag]
    · cases htag : Nat.beq srcEp.ptr.tag dstEp.ptr.tag <;>
        simp only [copySliceElements, copyEffElemSize?, hso, hdo, hin, hstride, htag, hloc, hov]
  · intro hin hoob
    rcases hoob with hsrc | hdst
    · simp only [copySliceElements, hso, hdo, hin, hsrc, Bool.true_or]
    · simp only [copySliceElements, hso, hdo, hin, hdst, Bool.or_true]
  · intro hin
    simp only [copySliceElements, copyEffElemSize?, hso, hdo, hin]
    split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · exact Or.inr rfl

private theorem copyBytesSubplace_no_win_ub_or_unsup
    (b0 : Bool)
    (srcOpt : Option (Value × List ProjectionElem × Option (List ProjectionElem × List Value)))
    (rootValOpt : Option Value)
    (fBs : Value → Option (List ProjectionElem × List Value) → Option (List AbstractByte))
    (fLen : List AbstractByte → Bool)
    (fOob : List AbstractByte → Bool) :
    let out : CopySliceOutcome :=
      match b0 with
      | true => .ub
      | false =>
        match srcOpt with
        | .none =>
          match rootValOpt with
          | .none => .ub
          | .some _ => .unsupported
        | .some (sVal, _, sliceInfoOpt) =>
          match fBs sVal sliceInfoOpt with
          | .none => .unsupported
          | .some bs =>
            match fLen bs with
            | false => .unsupported
            | true =>
              match fOob bs with
              | true => .ub
              | false => .unsupported
    out = .ub ∨ out = .unsupported := by
  dsimp only
  cases b0 with
  | true => exact Or.inl rfl
  | false =>
    cases srcOpt with
    | none =>
      cases rootValOpt with
      | none => exact Or.inl rfl
      | some _ => exact Or.inr rfl
    | some p =>
      rcases p with ⟨sVal, _, sliceInfoOpt⟩
      cases h1 : fBs sVal sliceInfoOpt with
      | none => simp [h1]
      | some bs =>
        cases h2 : fLen bs with
        | false => simp [h1, h2]
        | true =>
          cases h3 : fOob bs with
          | true => simp [h1, h2, h3]
          | false => simp [h1, h2, h3]

/-- **Trusted byte-level sub-place copy (universal).** Whenever a `NonDivergingIntrinsic.copyNonOverlapping`
(`evalCopyNonOverlapping` → `resolveCopySubplaceMulti`) has an initialized source root, aligned
compatible non-zero-sized pointees, and at least one non-array endpoint (`resolveArraySliceEndpoint? = none`),
it dispatches to `copyBytesSubplace`, on which:
* an access that is certainly outside either allocation (`copyAccessFitsAlloc? = some false`)
  is UB unconditionally, before any encoding or decoding;
* two pointers carrying the same borrow tag are UB unconditionally (matching the single-element
  and element-window paths);
* a missing source root slot (`srcWinOpt = none`, `srcEp.rootValOpt = none`) is UB;
* a non-zero destination byte offset (`dstEp.ptr.offsetBytes ≠ 0`) into a non-byte destination
  (`dstWinOpt = none`) never writes or silently steps as a no-op: it is `.ub` or `.unsupported`. -/
theorem copyNonOverlapping_trusted_byte_subplace_universal
    (decls : List LocalDecl) (layouts : LayoutTable) (locals callerLocals : List LocalSlot)
    (callStack : List SavedCallerFrame) (srcEp dstEp : CopyEndpoint) (n : Nat)
    (srcWinOpt dstWinOpt : Option (List ProjectionElem × Nat × List Value)) :
    (∀ (s : MachineState) (src dst count : Operand) (span : String),
      evalStmt s ⟨.intrinsic (.copyNonOverlapping src dst count), span⟩ decls layouts =
        evalCopyNonOverlapping s src dst count decls layouts) ∧
    (∀ (src dst : Operand) (srcRootVal : Value) (dstSlot : LocalSlot) (k : Nat),
      get? locals srcEp.entry.targetLocal = some (.init srcRootVal) →
      get? locals dstEp.entry.targetLocal = some dstSlot →
      dstSlot ≠ .dead →
      cpAligned decls layouts src dst srcEp.ptr dstEp.ptr = true →
      copyPointeeSizesConflict decls layouts (operandPointeeTy decls layouts src)
        (operandPointeeTy decls layouts dst) = false →
      copyPointeeByteSize? decls layouts (operandPointeeTy decls layouts src)
        (operandPointeeTy decls layouts dst) = some (k + 1) →
      let srcEp' : CopyEndpoint :=
        { ptr := srcEp.ptr, entry := srcEp.entry, rootValOpt := some srcRootVal,
          pointeeOpt := operandPointeeTy decls layouts src }
      let dstEp' : CopyEndpoint :=
        { ptr := dstEp.ptr, entry := dstEp.entry,
          rootValOpt := match dstSlot with | .init v => some v | _ => none,
          pointeeOpt := operandPointeeTy decls layouts dst }
      (resolveArraySliceEndpoint? decls layouts locals srcEp' (some (k + 1)) = none ∨
        resolveArraySliceEndpoint? decls layouts locals dstEp' (some (k + 1)) = none) →
      resolveCopySubplaceMulti callerLocals callStack src dst decls layouts srcEp.ptr dstEp.ptr
          srcEp.entry dstEp.entry n locals =
        copyBytesSubplace decls layouts locals callerLocals callStack srcEp' dstEp'
          (some (k + 1)) n
          (resolveArraySliceEndpoint? decls layouts locals srcEp' (some (k + 1)))
          (resolveArraySliceEndpoint? decls layouts locals dstEp' (some (k + 1)))) ∧
    (∀ sz : Nat,
      (copyAccessCertainlyOob
          (copyAccessFitsAlloc? decls layouts locals callerLocals callStack srcEp (Nat.mul n sz)) =
          true ∨
        copyAccessCertainlyOob
          (copyAccessFitsAlloc? decls layouts locals callerLocals callStack dstEp (Nat.mul n sz)) =
          true) →
      copyBytesSubplace decls layouts locals callerLocals callStack srcEp dstEp (some sz) n
          srcWinOpt dstWinOpt = .ub) ∧
    (∀ elemSzOpt : Option Nat,
      Nat.beq srcEp.ptr.tag dstEp.ptr.tag = true →
      copyBytesSubplace decls layouts locals callerLocals callStack srcEp dstEp elemSzOpt n
          srcWinOpt dstWinOpt = .ub) ∧
    (∀ elemSzOpt : Option Nat,
      srcWinOpt = none → srcEp.rootValOpt = none →
      copyBytesSubplace decls layouts locals callerLocals callStack srcEp dstEp elemSzOpt n
          srcWinOpt dstWinOpt = .ub) ∧
    (∀ elemSzOpt : Option Nat,
      dstWinOpt = none → Nat.beq dstEp.ptr.offsetBytes 0 = false →
      let out := copyBytesSubplace decls layouts locals callerLocals callStack srcEp dstEp
        elemSzOpt n srcWinOpt dstWinOpt
      out = .ub ∨ out = .unsupported) := by
  refine ⟨fun _ _ _ _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro src dst srcRootVal dstSlot k hs hd hdn ha hc hsz
    dsimp only
    intro hna
    unfold cpAligned at ha
    cases dstSlot with
    | dead => exact absurd rfl hdn
    | uninit =>
      rcases hna with hsrc | hdst
      · simp only [resolveCopySubplaceMulti, hs, hd, ha, hc, hsz, hsrc]
      · simp only [resolveCopySubplaceMulti, hs, hd, ha, hc, hsz, hdst]
        cases resolveArraySliceEndpoint? decls layouts locals
          { ptr := srcEp.ptr, entry := srcEp.entry, rootValOpt := some srcRootVal,
            pointeeOpt := operandPointeeTy decls layouts src } (some (k + 1)) <;> rfl
    | init v =>
      rcases hna with hsrc | hdst
      · simp only [resolveCopySubplaceMulti, hs, hd, ha, hc, hsz, hsrc]
      · simp only [resolveCopySubplaceMulti, hs, hd, ha, hc, hsz, hdst]
        cases resolveArraySliceEndpoint? decls layouts locals
          { ptr := srcEp.ptr, entry := srcEp.entry, rootValOpt := some srcRootVal,
            pointeeOpt := operandPointeeTy decls layouts src } (some (k + 1)) <;> rfl
  · intro sz hoob
    unfold copyBytesSubplace
    dsimp only
    rcases hoob with hsrc | hdst
    · rw [hsrc]; rfl
    · rw [hdst, Bool.or_true]; rfl
  · intro elemSzOpt htag
    unfold copyBytesSubplace
    dsimp only
    rw [htag, Bool.or_true]
  · intro elemSzOpt hsw hrv
    subst hsw
    unfold copyBytesSubplace
    dsimp only
    rw [hrv]
    generalize Bool.or _ _ = g0
    cases g0
    · cases Nat.beq srcEp.ptr.offsetBytes 0 <;> rfl
    · rfl
  · intro elemSzOpt hdw hoff
    subst hdw
    unfold copyBytesSubplace
    dsimp only
    rw [hoff]
    exact copyBytesSubplace_no_win_ub_or_unsup _ _ _ (fun sVal sliceInfoOpt => _) _ _

/-- **MiniRustSpec (universal, fail-closed).** Upstream `minimize` aborts on
`NonDivergingIntrinsic::CopyNonOverlapping` (`span_bug!`, anchored above). The `MiniRustSpec`
transcription mirrors that exactly: the statement does not translate, the fragment check
rejects it, every block containing it fails to translate, and every body containing it lies
outside the `MiniRustSpec` fragment — no `MiniRustSpec` simulation is ever claimed for a body
that copies through raw pointers. -/
theorem copyNonOverlapping_minirustSpec_fail_closed
    (decls : List LocalDecl) (layouts : LayoutTable) (src dst count : Operand) (span : String) :
    MiniRustSpec.Correspondence.translateStatement decls
        ⟨.intrinsic (.copyNonOverlapping src dst count), span⟩ layouts = none ∧
      MiniRustSpec.Correspondence.statementOk decls
        ⟨.intrinsic (.copyNonOverlapping src dst count), span⟩ layouts = false ∧
      (∀ (bb : BasicBlockData) (s : Statement), s ∈ bb.statements →
        s.kind = .intrinsic (.copyNonOverlapping src dst count) →
        MiniRustSpec.Correspondence.translateBlock layouts decls bb = none) ∧
      (∀ (body : CapturedMir) (bb : BasicBlockData) (s : Statement), bb ∈ body.basicBlocks →
        s ∈ bb.statements → s.kind = .intrinsic (.copyNonOverlapping src dst count) →
        MiniRustSpec.Correspondence.inFragment body = false) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro bb s hs hk
    have hnone : bb.statements.mapM
        (fun x => MiniRustSpec.Correspondence.translateStatement decls x layouts) = none :=
      mapM_none_of_mem _ bb.statements s hs (by
        simp [MiniRustSpec.Correspondence.translateStatement, hk])
    simp [MiniRustSpec.Correspondence.translateBlock, hnone]
  · intro body bb s hbb hs hk
    exact inFragment_false_of_stmt hbb hs (by simp [MiniRustSpec.Correspondence.statementOk, hk])

/-- **LeanMiri `copy_nonoverlapping` check order (universal).** For every instantiation of the
interpreter leaves, the transcribed statement is `copyWith … true` (the ranges must not
overlap), and `copyWith` checks, in source order: the total size (UB "overflow computing total
size of copy"), the alignment of the source pointer, the alignment of the destination pointer
— both *before* and independently of the memory copy, so also for a zero-length copy — and
only then the copy itself, which receives the computed total size and whose error (an
out-of-bounds or overlapping range, …) is the statement's. -/
theorem copyNonOverlapping_leanMiri_check_order {Ptr : Type} (h : LeanMiri.CopyHooks Ptr)
    (elemSize elemAlign count : Nat) (source dest : Ptr) :
    LeanMiri.evalCopyNonOverlapping h elemSize elemAlign source dest count =
        LeanMiri.copyWith h elemSize elemAlign source dest count true ∧
      (h.totalSize elemSize count = none →
        LeanMiri.copyWith h elemSize elemAlign source dest count true =
          .error (.undefinedBehavior "overflow computing total size of copy")) ∧
      (∀ (size : Nat) (e : LeanMiri.StepError), h.totalSize elemSize count = some size →
        h.checkAlign source elemAlign = some e →
        LeanMiri.copyWith h elemSize elemAlign source dest count true = .error e) ∧
      (∀ (size : Nat) (e : LeanMiri.StepError), h.totalSize elemSize count = some size →
        h.checkAlign source elemAlign = none → h.checkAlign dest elemAlign = some e →
        LeanMiri.copyWith h elemSize elemAlign source dest count true = .error e) ∧
      (∀ (size : Nat) (e : LeanMiri.StepError), h.totalSize elemSize count = some size →
        h.checkAlign source elemAlign = none → h.checkAlign dest elemAlign = none →
        h.memCopy source dest size true = some e →
        LeanMiri.copyWith h elemSize elemAlign source dest count true = .error e) ∧
      (∀ (size : Nat), h.totalSize elemSize count = some size →
        h.checkAlign source elemAlign = none → h.checkAlign dest elemAlign = none →
        h.memCopy source dest size true = none →
        LeanMiri.copyWith h elemSize elemAlign source dest count true = .ok ()) ∧
      (∀ (e : LeanMiri.StepError), h.totalSize elemSize 0 = some 0 →
        h.checkAlign source elemAlign = some e →
        LeanMiri.evalCopyNonOverlapping h elemSize elemAlign source dest 0 = .error e) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    simp only [LeanMiri.copyWith, h0]
  · intro size e h0 h1
    simp only [LeanMiri.copyWith, h0, h1]
  · intro size e h0 h1 h2
    simp only [LeanMiri.copyWith, h0, h1, h2]
  · intro size e h0 h1 h2 h3
    simp only [LeanMiri.copyWith, h0, h1, h2, h3]
  · intro size h0 h1 h2 h3
    simp only [LeanMiri.copyWith, h0, h1, h2, h3]
  · intro e h0 h1
    simp only [LeanMiri.evalCopyNonOverlapping, LeanMiri.copyWith, h0, h1]

/-- **Positive witnesses (element sub-place copies).** `copy_nonoverlapping(&raw const src[i],
&raw mut dst[j], n)` copies exactly `n` elements between the two element windows:
`[22, 99] → [0, 0]` with `n = 2` yields `dst = [22, 99]` (so `dst[0] ^ dst[1] = 117`, where
the former single-element copy returned `22`), and `[88, 66]` yields `26`; `n = 1` copies one
element; a window may start inside the array (`src[1] → dst[0]`), span three of four
elements, land in the middle of the destination, or be addressed through non-zero pointer
`.offset` byte offsets (`(&raw const src[0]).offset(1)` → `(&raw mut dst[0]).offset(1)`,
converting byte offset `4` to element index `1` rather than raw element `4`); two disjoint
windows of the *same* array are copied in place, as are adjacent single elements; and `n = 0`
writes nothing. -/
theorem copyNonOverlapping_witness_elem_subplace_copies :
    localScalars? (cpRun (cpBody [22, 99] [0, 0] 0 0 2) 11) 2 = some [22, 99] ∧
      haltedBits? (cpRun (cpBody [22, 99] [0, 0] 0 0 2) 15) = some 117 ∧
      haltedBits? (cpRun (cpBody [88, 66] [0, 0] 0 0 2) 15) = some 26 ∧
      localScalars? (cpRun (cpBody [22, 99] [0, 0] 0 0 1) 11) 2 = some [22, 0] ∧
      localScalars? (cpRun (cpBody [22, 99] [0, 0] 1 0 1) 11) 2 = some [99, 0] ∧
      localScalars? (cpRun (cpBody [1, 2, 3, 4] [0, 0, 0, 0] 1 0 3) 11) 2 = some [2, 3, 4, 0] ∧
      localScalars? (cpRun (cpBody [1, 2, 3, 4] [9, 9, 9, 9] 2 1 2) 11) 2 = some [9, 3, 4, 9] ∧
      localScalars? (cpRun (cpOffsetBody [1, 2, 3, 4] [9, 9, 9, 9] 1 1 2) 13) 2 =
        some [9, 2, 3, 9] ∧
      localScalars? (cpRun (cpSameBody [1, 2, 3, 4] 0 2 2 3) 7) 1 = some [1, 2, 1, 2] ∧
      localScalars? (cpRun (cpSameBody [1, 2, 3, 4] 0 1 1 1) 7) 1 = some [1, 1, 3, 4] ∧
      localScalars? (cpRun (cpBody [22, 99] [0, 0] 0 0 0) 11) 2 = some [0, 0] :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Positive witnesses (caller-owned referents, Tree Borrows read-then-write, and byte-punned
offset copies).** A modular root copies two elements between two arrays owned by its external
caller (the destination slot becomes `[22, 99]`, the source slot is untouched, and the run
returns); under Tree Borrows, a foreign `.unique` borrow on the source (tag `10`) is frozen to
`.frozen` (`3`) while a foreign `.unique` borrow on the destination (tag `11`) is disabled to
`.disabled` (`4`); a byte-punned copy of `word: u32 = 0x04030201` into `bytes: [u8; 4]` yields
`[1, 2, 3, 4]`, into `(&raw mut bytes[0]).offset(1)` of `[u8; 6]` yields `[0, 1, 2, 3, 4, 0]`
(non-zero destination byte offset), and from `(&raw const src[0]).offset(1)` of
`[0xAA, 1, 2, 3, 4, 0xBB]` into `&raw mut word as *mut u8` yields `0x04030201` (non-zero source
byte offset). -/
theorem copyNonOverlapping_witness_caller_referents_and_byte_pun :
    callerScalars?
        (cpRunMem (cpCallerBody 2) [.ptr ⟨1, 0⟩ 8, .ptr ⟨2, 0⟩ 8] (cpCallerMem []) 1) 4 =
      some [22, 99] ∧
      callerScalars?
          (cpRunMem (cpCallerBody 2) [.ptr ⟨1, 0⟩ 8, .ptr ⟨2, 0⟩ 8] (cpCallerMem []) 1) 3 =
        some [22, 99] ∧
      haltedBits? (cpRunMem (cpCallerBody 2) [.ptr ⟨1, 0⟩ 8, .ptr ⟨2, 0⟩ 8] (cpCallerMem []) 3) =
        some 1 ∧
      borrowTagPerms? (cpRunMem (cpCallerBody 2) [.ptr ⟨1, 0⟩ 8, .ptr ⟨2, 0⟩ 8] cpCallerTbMem 1) =
        some [(1, 3), (2, 2), (10, 3), (11, 4)] ∧
      localScalars? (cpRun (bytePunBody 0x04030201 0 0 4 0) 13) 2 = some [1, 2, 3, 4] ∧
      haltedBits? (cpRun (bytePunBody 0x04030201 0 0 4 3) 15) = some 4 ∧
      localScalars? (cpRun (bytePunDstOffsetBody 0x04030201 6 1 4) 13) 2 =
        some [0, 1, 2, 3, 4, 0] ∧
      haltedBits? (cpRun (bytePunSrcToWordBody [0xAA, 1, 2, 3, 4, 0xBB] 1 4) 15) =
        some 0x04030201 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Negative canaries (fail-closed copies).** A source window that leaves its array
(`src[1]`, `n = 2`), a destination window that does (`dst[1]`, `n = 2`), and `n = 3` over
two-element arrays are UB; so are overlapping windows of the same array (`a[0..2] → a[1..3]`),
a same-tag copy (`copy_nonoverlapping(p, p, 2)` — confirmed still running immediately before
the copy and UB at step 7), writing through a `.frozen` destination pointer, and a
three-element copy between the caller's two-element arrays. A byte-punned copy of a *partial*
scalar, a byte splice into a non-byte container (`[u32; 2]`), and an element-stride mismatch
(`[u8; 4]` cast to `*const u16` into `[u16; 2]`) all fail closed with `.unsupported` — never a
silently wrong value — and a byte window that leaves the scalar or the array is UB. -/
theorem copyNonOverlapping_witness_ub_canaries :
    isUbFault (cpRun (cpBody [22, 99] [0, 0] 1 0 2) 11) = true ∧
      isUbFault (cpRun (cpBody [22, 99] [0, 0] 0 1 2) 11) = true ∧
      isUbFault (cpRun (cpBody [22, 99] [0, 0] 0 0 3) 11) = true ∧
      isUbFault (cpRun (cpSameBody [1, 2, 3, 4] 0 1 2 3) 7) = true ∧
      localScalars? (cpRun cpSameTagBody 6) 1 = some [1, 2, 3, 4] ∧
      isUbFault (cpRun cpSameTagBody 7) = true ∧
      isUbFault
          (cpRunMem (cpCallerBody 2) [.ptr ⟨2, 0⟩ 8, .ptr ⟨1, 0⟩ 8] (cpCallerMem []) 1) =
        true ∧
      isUbFault
          (cpRunMem (cpCallerBody 3) [.ptr ⟨1, 0⟩ 8, .ptr ⟨2, 0⟩ 8] (cpCallerMem []) 1) =
        true ∧
      isUnsupportedFault (cpRun (bytePunBody 0x04030201 1 0 2 0) 13) = true ∧
      isUnsupportedFault (cpRun (bytePunBody 0x04030201 0 1 2 1) 13) = true ∧
      isUnsupportedFault (cpRun byteSpliceNonByteBody 13) = true ∧
      isUnsupportedFault (cpRun strideMismatchBody 11) = true ∧
      isUbFault (cpRun (bytePunBody 0x04030201 2 0 4 0) 13) = true ∧
      isUbFault (cpRun (bytePunBody 0x04030201 0 2 4 0) 13) = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- **Negative canaries (sub-place resolution).** `resolveCopySubplaceMulti` on concrete
frames: a zero-sized pointee (`()`) is a no-op for `n = 5` over uninitialized *and* over
initialized roots, but UB when the source or the destination root is dead or the source root
slot is missing; a zero-sized `[u32; 0]` pointee is a no-op at an aligned byte offset (`4`)
and UB at a misaligned one (`2`) — alignment is checked before the ZST shortcut; and for a
`u32` pointee a misaligned source pointer or an uninitialized source root is UB. -/
theorem copyNonOverlapping_witness_resolution_canaries :
    copyNonOverlappingResolve tyPtrUnit .uninit .uninit 0 0 5 = .noop ∧
      copyNonOverlappingResolve tyPtrUnit (.init (.scalar ⟨7, 4⟩)) (.init (.scalar ⟨9, 4⟩))
          0 0 5 = .noop ∧
      copyNonOverlappingResolve tyPtrUnit .dead .uninit 0 0 5 = .ub ∧
      copyNonOverlappingResolve tyPtrUnit .uninit .dead 0 0 5 = .ub ∧
      copyNonOverlappingResolveMissing = .ub ∧
      copyNonOverlappingResolve tyPtrZstArr (.init (.scalar ⟨7, 4⟩)) (.init (.scalar ⟨9, 4⟩))
          4 0 5 = .noop ∧
      copyNonOverlappingResolve tyPtrZstArr (.init (.scalar ⟨7, 4⟩)) (.init (.scalar ⟨9, 4⟩))
          2 0 5 = .ub ∧
      copyNonOverlappingResolve tyPtrMutU32 (.init (.scalar ⟨7, 4⟩)) (.init (.scalar ⟨9, 4⟩))
          2 0 2 = .ub ∧
      copyNonOverlappingResolve tyPtrMutU32 .uninit (.init (.scalar ⟨9, 4⟩)) 0 0 2 = .ub :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Positive witness (root tail call, then a copy through the relocated caller referents).**
The modular root `fcp` (three locals) tail-calls the five-local `gcp`, which copies two
elements between the external caller's arrays. The tail call relocates both *live*
caller-owned referents past `gcp`'s frame (slots `3, 4 → 5, 6`,
`tailCall_witness_root_caller_referent_simulation`), and the element-window copy then reads
and writes the relocated caller slots — not `gcp`'s own locals `_3 = 5` and `_4 = 6`, which
formerly shadowed them: the caller's destination array becomes `[22, 99]`, its source array
is untouched, and the run returns. -/
theorem tailCall_witness_root_referent_copy :
    borrowsOf? (cpRunMem fCpBody [.ptr ⟨1, 0⟩ 8, .ptr ⟨2, 0⟩ 8] (cpCallerMem [gCpBody]) 1) =
      some [{ tag := 1, targetLocal := 5, targetProjection := [.constantIndex 0 2 false],
              perm := .frozen },
            { tag := 2, targetLocal := 6, targetProjection := [.constantIndex 0 2 false],
              perm := .unique }] ∧
      callerScalars?
          (cpRunMem fCpBody [.ptr ⟨1, 0⟩ 8, .ptr ⟨2, 0⟩ 8] (cpCallerMem [gCpBody]) 1) 6 =
        some [0, 0] ∧
      callerScalars?
          (cpRunMem fCpBody [.ptr ⟨1, 0⟩ 8, .ptr ⟨2, 0⟩ 8] (cpCallerMem [gCpBody]) 2) 6 =
        some [22, 99] ∧
      callerScalars?
          (cpRunMem fCpBody [.ptr ⟨1, 0⟩ 8, .ptr ⟨2, 0⟩ 8] (cpCallerMem [gCpBody]) 2) 5 =
        some [22, 99] ∧
      haltedBits? (cpRunMem fCpBody [.ptr ⟨1, 0⟩ 8, .ptr ⟨2, 0⟩ 8] (cpCallerMem [gCpBody]) 4) =
        some 1 :=
  ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

end CopyNonOverlapping

/-! ## 5. Kernel axiom and non-vacuity audit

Every declaration of this namespace (definitions, theorems, and their auxiliary `match_` /
`proof_` declarations) is checked: no `unsafe`, and `collectAxioms` within
`{propext, Classical.choice, Quot.sound}` — so no `sorryAx`, no `Lean.ofReduceBool`
(`native_decide`), and no `Lean.trustCompiler`. The coverage manifest is re-checked
semantically: every manifest theorem exists as a theorem of this file; `trusted`,
`minirust`, and `leanmiri` theorems are universally quantified (their statement contains a
`∀` binder); `trusted` theorems reach a Trusted anchor of their variant (its `MirAst`
constructor or the Trusted function implementing it), `leanmiri` theorems reach the
transcribed LeanMiri function, `minirust` theorems reach the Trusted anchor *and* a
`MiniRust.*` / `MiniRustSpec.*` constant, and witnesses reach some anchor of their variant —
where "reach" follows the constants used by statements and proofs through this file's own
data and helper definitions (never through the LeanMiri model itself). -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let ns := `Anneal.MirUntestedVariantCorrespondenceTests
  let lm := ns ++ `LeanMiri
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden : List Name := [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler]
  let mut audited : Nat := 0
  let mut theorems : Nat := 0
  for (n, ci) in env.constants.map₂.toList do
    if ns.isPrefixOf n then
      if ci.isUnsafe then throwError "unsafe declaration: {n}"
      let axs ← collectAxioms n
      for a in axs do
        if forbidden.contains a then throwError "{n} depends on forbidden constant {a}"
        unless allowed.contains a do throwError "{n} depends on disallowed axiom {a}"
      audited := audited + 1
      if ci matches .thmInfo _ then theorems := theorems + 1
  if audited < 150 then throwError "audited only {audited} declarations (expected ≥ 150)"
  let follow : Name → Bool := fun c => ns.isPrefixOf c && !lm.isPrefixOf c
  let reach : Name → NameSet := fun root => Id.run do
    let mut seen : NameSet := {}
    let mut work : Array Name := #[root]
    while !work.isEmpty do
      let c := work.back!
      work := work.pop
      if let some ci := env.find? c then
        for d in ci.getUsedConstantsAsSet do
          if !seen.contains d then
            seen := seen.insert d
            if follow d then work := work.push d
    return seen
  let tr := `Trusted.Rustc.V2026_06_01
  -- (variant, Trusted anchors, LeanMiri anchors, manifest)
  let manifest : List (String × List Name × List Name × List (String × List Name)) := [
    ("constEvalCounter",
      [tr ++ `MirAst.StatementKind.constEvalCounter],
      [lm ++ `StatementKind.ConstEvalCounter, lm ++ `executionIncrementConstEvalCounter],
      [("trusted", [`constEvalCounter_trusted_step_universal, `constEvalCounter_stepMirFn_universal,
          `constEvalCounter_nop_statement_equiv]),
       ("minirust", [`constEvalCounter_minirust_ops_corresponds,
          `constEvalCounter_minirustSpec_fail_closed]),
       ("leanmiri", [`constEvalCounter_leanMiri_lockstep, `constEvalCounter_leanMiri_nop_equiv]),
       ("positive", [`constEvalCounter_witness_runs, `constEvalCounter_leanMiri_witness]),
       ("negative", [`constEvalCounter_witness_ub_not_masked,
          `constEvalCounter_witness_minirustSpec_rejects])]),
    ("tailCall",
      [tr ++ `MirAst.TerminatorKind.tailCall, tr ++ `MirSemantics.enterTailCalleeFrame,
       tr ++ `MirSemantics.resumeExternalTailCall, tr ++ `MirSemantics.evalTailCallTerminator],
      [lm ++ `evalTailCallTerminator, lm ++ `initFnTailCall],
      [("trusted", [`tailCall_trusted_direct_enters_without_push, `tailCall_trusted_vs_call_depth,
          `tailCall_trusted_return_through, `tailCall_trusted_external,
          `tailCall_trusted_external_resume_is_return, `tailCall_trusted_fail_closed_universal,
          `tailCall_trusted_non_function_value_ub, `tailCall_trusted_unwind_through,
          `tailCall_trusted_direct_and_unsupported_fail_closed,
          `tailCall_trusted_return_through_fail_closed]),
       ("minirust", [`tailCall_minirust_corresponds]),
       ("leanmiri", [`tailCall_leanMiri_shape_lockstep, `tailCall_leanMiri_root_stop_diverges,
          `tailCall_leanMiri_arity_ub, `tailCall_leanMiri_ret_abi_and_cleanup_universal,
          `tailCall_leanMiri_arg_abi_universal, `tailCall_leanMiri_checks_classification,
          `tailCall_leanMiri_nounwind_callee_simulation, `tailCall_leanMiri_unwind_verdicts,
          `tailCall_leanMiri_modular_root_unwind, `tailCall_leanMiri_cleanup_frees_caller_locals,
          `tailCall_abi_mismatch_corresponds,
          `tailCall_leanMiri_calling_conv_ub_corresponds, `tailCall_leanMiri_call_pushes]),
       ("positive", [`tailCall_leanMiri_witness, `tailCall_witness_nested_runs, `tailCall_witness_root_runs,
          `tailCall_witness_external, `tailCall_witness_indirect_and_zst,
          `tailCall_witness_root_referent_copy]),
       ("negative", [`tailCall_witness_ub_cases, `tailCall_witness_direct_arity_divergence,
          `tailCall_leanMiri_witness_arg_abi, `tailCall_leanMiri_witness_checks,
          `tailCall_leanMiri_witness_unwind, `tailCall_witness_dangling_caller_local_simulation,
          `tailCall_witness_root_caller_referent_simulation])]),
    ("opaqueCast",
      [tr ++ `MirAst.ProjectionElem.opaqueCast],
      [lm ++ `projectOpaqueCast, lm ++ `placeProjectOpaqueCast],
      [("trusted", [`opaqueCast_trusted_traversal_universal, `opaqueCast_trusted_retype_universal,
          `opaqueCast_trusted_overlap_universal, `opaqueCast_trusted_place_read_universal,
          `opaqueCast_trusted_placeTy_and_helpers_universal,
          `opaqueCast_trusted_write_and_borrow_universal, `opaqueCast_trusted_place_rw_with_decls,
          `opaqueCast_trusted_stmt_placeMention_and_deinit_universal,
          `opaqueCast_trusted_root_dispatch_simulation]),
       ("minirust", [`opaqueCast_minirust_corresponds]),
       ("leanmiri", [`opaqueCast_leanMiri_phase_boundary]),
       ("positive", [`opaqueCast_witness_read_write, `opaqueCast_witness_projected_move,
          `opaqueCast_witness_place_rw_with_decls, `opaqueCast_witness_root_dispatch]),
       ("negative", [`opaqueCast_witness_ub_not_masked, `opaqueCast_witness_references_reject,
          `opaqueCast_witness_type_switch])]),
    ("copyNonOverlapping",
      [tr ++ `MirAst.NonDivergingIntrinsic.copyNonOverlapping,
       tr ++ `MirSemantics.evalCopyNonOverlapping, tr ++ `MirSemantics.resolveCopySubplaceMulti,
       tr ++ `MirSemantics.copySliceElements, tr ++ `MirSemantics.copyBytesSubplace],
      [lm ++ `copyWith, lm ++ `evalCopyNonOverlapping],
      [("trusted", [`copyNonOverlapping_trusted_subplace_resolution_universal,
          `copyNonOverlapping_trusted_elem_window_universal,
          `copyNonOverlapping_trusted_byte_subplace_universal]),
       ("minirust", [`copyNonOverlapping_minirustSpec_fail_closed]),
       ("leanmiri", [`copyNonOverlapping_leanMiri_check_order]),
       ("positive", [`copyNonOverlapping_witness_elem_subplace_copies,
          `copyNonOverlapping_witness_caller_referents_and_byte_pun]),
       ("negative", [`copyNonOverlapping_witness_ub_canaries,
          `copyNonOverlapping_witness_resolution_canaries])])]
  let mut checked : Nat := 0
  for (variant, trAnchors, lmAnchors, entries) in manifest do
    for (key, names) in entries do
      if names.isEmpty then throwError "{variant}: empty manifest key {key}"
      for short in names do
        let n := ns ++ short
        let some ci := env.find? n | throwError "{variant}/{key}: missing theorem {n}"
        unless ci matches .thmInfo _ do throwError "{variant}/{key}: {n} is not a theorem"
        let r := reach n
        let hits (anchors : List Name) : Bool := anchors.any r.contains
        if key == "trusted" || key == "minirust" || key == "leanmiri" then
          unless (ci.type.find? Expr.isForall).isSome do
            throwError "{variant}/{key}: {n} is not universally quantified"
        if key == "trusted" || key == "minirust" then
          unless hits trAnchors do throwError "{variant}/{key}: {n} never reaches a Trusted anchor"
        if key == "leanmiri" then
          unless hits lmAnchors do throwError "{variant}/{key}: {n} never reaches a LeanMiri anchor"
        if key == "minirust" then
          unless r.toList.any (fun c => (`MiniRust).isPrefixOf c || (`MiniRustSpec).isPrefixOf c) do
            throwError "{variant}/{key}: {n} never reaches a MiniRust / MiniRustSpec constant"
        if key == "positive" || key == "negative" then
          unless hits trAnchors || hits lmAnchors do
            throwError "{variant}/{key}: {n} never reaches an anchor of its variant"
        checked := checked + 1
  logInfo m!"kernel audit passed: {audited} declarations ({theorems} theorems): 0 sorryAx, \
    0 Lean.ofReduceBool, 0 unsafe; {checked} manifest theorems non-vacuous"

end Anneal.MirUntestedVariantCorrespondenceTests

