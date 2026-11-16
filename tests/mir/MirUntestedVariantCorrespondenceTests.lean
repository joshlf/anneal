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
`ProjectionElem.opaqueCast` against three references:

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
  indirect calls are checked by both.
* `opaqueCast` is value-transparent and type-switching in Trusted (`readProjectedValue`,
  `writeProjectedValue`, `projectionsOverlap` ignore it; `resolveProjectedTy` and the
  union-aware readers retype to the cast type), whereas both Miri projection paths throw
  ("OpaqueCast after borrowck") — never a UB verdict — because rustc's MIR validator
  forbids `OpaqueCast` at `MirPhase::Runtime` (post-`PostAnalysisNormalize`), the phase of
  every captured body. Trusted therefore agrees with the opaque-cast-erased program, and
  the coverage matrix records `opaqueCast` as `supported_and_tested` (phase boundary).

The final `run_cmd` is a kernel audit: every declaration of this namespace is free of
`sorryAx`, `Lean.ofReduceBool`, and `unsafe`, and every manifest theorem below exists and
mentions its variant constructor (non-vacuity).
-/

/-
Coverage manifest (checked by `scripts/audit_mir_coverage_matrix.py --check` and by the
final `run_cmd`):
-/
-- @mir-variant-coverage StatementKind.constEvalCounter trusted=constEvalCounter_trusted_step_universal,constEvalCounter_stepMirFn_universal,constEvalCounter_nop_statement_equiv minirust=constEvalCounter_minirust_ops_corresponds,constEvalCounter_minirustSpec_fail_closed leanmiri=constEvalCounter_leanMiri_lockstep,constEvalCounter_leanMiri_nop_equiv positive=constEvalCounter_witness_runs,constEvalCounter_leanMiri_witness negative=constEvalCounter_witness_ub_not_masked,constEvalCounter_witness_minirustSpec_rejects
-- @mir-variant-coverage TerminatorKind.tailCall trusted=tailCall_trusted_direct_enters_without_push,tailCall_trusted_vs_call_depth,tailCall_trusted_return_through,tailCall_trusted_external,tailCall_trusted_external_resume_is_return,tailCall_trusted_fail_closed_universal,tailCall_trusted_non_function_value_ub,tailCall_trusted_unwind_through,tailCall_trusted_direct_and_unsupported_fail_closed,tailCall_trusted_return_through_fail_closed minirust=tailCall_minirust_corresponds leanmiri=tailCall_leanMiri_shape_lockstep,tailCall_leanMiri_root_stop_diverges,tailCall_leanMiri_arity_ub,tailCall_leanMiri_ret_abi_and_cleanup_universal,tailCall_leanMiri_arg_abi_universal positive=tailCall_leanMiri_witness,tailCall_witness_nested_runs,tailCall_witness_root_runs,tailCall_witness_external,tailCall_witness_indirect_and_zst negative=tailCall_witness_ub_cases,tailCall_witness_direct_arity_divergence,tailCall_leanMiri_witness_arg_abi
-- @mir-variant-coverage ProjectionElem.opaqueCast trusted=opaqueCast_trusted_traversal_universal,opaqueCast_trusted_retype_universal,opaqueCast_trusted_overlap_universal,opaqueCast_trusted_place_read_universal,opaqueCast_trusted_placeTy_and_helpers_universal,opaqueCast_trusted_write_and_borrow_universal,opaqueCast_trusted_place_rw_with_decls minirust=opaqueCast_minirust_corresponds leanmiri=opaqueCast_leanMiri_phase_boundary positive=opaqueCast_witness_read_write,opaqueCast_witness_projected_move,opaqueCast_witness_place_rw_with_decls negative=opaqueCast_witness_ub_not_masked,opaqueCast_witness_references_reject,opaqueCast_witness_type_switch

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
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#let args := evaluated.args.map fun arg => FnArg.Copy arg.copyFnArg
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#let frame ← h.popRaw choice
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#let (ret, unwind) ← match frame.returnContinuation with
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#| .goto ret unwind => pure (ret, unwind)
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#| .stop _ => throw (.invalidProgram "cannot tailcall as root of stack")
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#evaluated.withCallerLocation, frame.returnPlace, ret, unwind⟩
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#let action ← h.cleanup choice false frame
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#require (action == .normal) "tailcall cleanup must return Normal"
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#require ((← h.frameIndex) == oldIndex) "evaluating this tail call pushed a new stack frame"
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#| none => throw (.undefinedBehavior "calling a function with fewer arguments than it requires")
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#throw (.undefinedBehavior "calling a function with more arguments than it expected")
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#throw (.undefinedBehavior s!"AbiMismatchArgument {calleeIndex}")
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Call.lean#throw (.undefinedBehavior "AbiMismatchReturn")
-- @source-anchor lean-miri/vendor/Miri/Interpreter/Projection.lean#| .OpaqueCast _ => throw (.invariant "OpaqueCast after borrowck")
-- @source-anchor lean-miri/vendor/Miri/Interpreter/PlaceDynamic.lean#| .OpaqueCast _ => throw (.invalidProgram "OpaqueCast after borrowck")
-- @source-anchor minirust/vendor/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/bb.rs#| rs::StatementKind::ConstEvalCounter
-- @source-anchor minirust/vendor/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/bb.rs#| rs::TerminatorKind::TailCall { .. }
-- @source-anchor minirust/vendor/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/rvalue.rs#| smir::ProjectionElem::OpaqueCast(_) => {

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

/-- `Call.initFnTailCall` (`Interpreter/Call.lean:436-446`) with the stack effect of the
`initFnCall` → `initStackFrame` push it performs: pop the active frame (`popRaw`), reject a
root frame (`ReturnContinuation.stop`), check the argument count and return-ABI
compatibility against the callee (`Call.lean:328-355`), push the callee with the popped
frame's return place and continuation, and require `cleanup` to return `.normal`
(`Call.lean:445-446`). -/
def initFnTailCall {B P U M : Type} (callee : B) (calleeArgCount argCount : Nat)
    (state : StepState B P U M) (retAbiCompat : Bool := true)
    (cleanupNormal : Bool := true) (argAbiCompat : Nat → Bool := fun _ => true) :
    Except StepError (StepState B P U M) :=
  match state.frames.getLast? with
  | none => .error .emptyStack
  | some frame =>
    match frame.returnContinuation with
    | .stop _ => .error (.invalidProgram "cannot tailcall as root of stack")
    | .goto ret unwind =>
      match passArgsError argAbiCompat argCount 0 calleeArgCount with
      | some e => .error e
      | none =>
      if !retAbiCompat then
        .error (.undefinedBehavior "AbiMismatchReturn")
      else if calleeArgCount < argCount then
        .error (.undefinedBehavior "calling a function with more arguments than it expected")
      else if !cleanupNormal then
        .error (.invalidProgram "tailcall cleanup must return Normal")
      else
        .ok { state with
          frames := state.frames.dropLast ++
            [{ body := callee, returnContinuation := .goto ret unwind,
               returnPlace := frame.returnPlace, location := .mir ⟨0, 0⟩ }] }

/-- `Call.evalTailCallTerminator` (`Interpreter/Call.lean:464-471`): the tail call must
leave the frame index unchanged. -/
def evalTailCallTerminator {B P U M : Type} (callee : B) (calleeArgCount argCount : Nat)
    (state : StepState B P U M) (retAbiCompat : Bool := true)
    (cleanupNormal : Bool := true) (argAbiCompat : Nat → Bool := fun _ => true) :
    Except StepError (StepState B P U M) :=
  let oldIndex := state.frames.length - 1
  match initFnTailCall callee calleeArgCount argCount state retAbiCompat cleanupNormal
      argAbiCompat with
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

/-- Whether a Miri error is a UB verdict. -/
def StepError.isUB : StepError → Bool
  | .undefinedBehavior _ => true
  | _ => false

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
theorem inFragment_false_of_stmt {body : CapturedMir} {bb : BasicBlockData}
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

/-- **Trusted direct in-table tail call (universal).** A direct `become f(args)` whose
callee has a linked body enters it at `bb0` with the evaluated arguments, *replacing* the
active frame: the call stack is unchanged (no `SavedCallerFrame` is pushed), the moved-out
argument locals of the tail-caller are discarded with its frame, and every other `Memory`
component is untouched. -/
theorem tailCall_trusted_direct_enters_without_push
    (s : MachineState) (func : Operand) (argOps : List Operand) (span : String)
    (callerBody calleeBody : CapturedMir) (defPath : DefPath) (argVals : List Value)
    (locals' : List LocalSlot)
    (hfunc : extractCalleeDefPath? func = some defPath)
    (hargs : evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals = .ok argVals locals')
    (hfind : lookupCallee s.memory.callees callerBody.layouts defPath
      (extractCalleeTypeArgs func) s.memory.traitImpls = some calleeBody) :
    evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) =
        MirStepNode.step (enterTailCalleeFrame s.memory calleeBody argVals) ∧
      (enterTailCalleeFrame s.memory calleeBody argVals).memory =
        { s.memory with activeCallee := some calleeBody } ∧
      (enterTailCalleeFrame s.memory calleeBody argVals).memory.callStack =
        s.memory.callStack ∧
      (enterTailCalleeFrame s.memory calleeBody argVals).frame =
        { blockIdx := 0, stmtIdx := 0, locals := initLocals calleeBody argVals } := by
  refine ⟨?_, rfl, rfl, rfl⟩
  simp only [evalTerminator, evalTailCallTerminator, resolveCallTarget, hfunc,
    hargs, hfind, checkCalleeTargetCompatible_direct]

/-- **Trusted tail call vs. call (universal contrast).** For the same callee and
arguments, a returning `call` pushes exactly one `SavedCallerFrame` (whose continuation is
`targetBb`), whereas `tailCall` leaves the stack depth unchanged. -/
theorem tailCall_trusted_vs_call_depth
    (s : MachineState) (callerBody calleeBody : CapturedMir) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (argVals : List Value)
    (unwind : UnwindAction) :
    (pushCalleeFrame s callerBody locals' destination targetBb calleeBody argVals unwind
        ).memory.callStack.length = s.memory.callStack.length + 1 ∧
      (enterTailCalleeFrame s.memory calleeBody argVals).memory.callStack.length =
        s.memory.callStack.length ∧
      (pushCalleeFrame s callerBody locals' destination targetBb calleeBody argVals unwind).frame =
        (enterTailCalleeFrame s.memory calleeBody argVals).frame :=
  ⟨by simp [pushCalleeFrame], rfl, rfl⟩

/-- **Trusted return-through (universal).** A `return` depends only on `_0` and the
memory, never on the rest of the active frame. Hence once the tail-callee has produced
`retVal`, its `return` is *exactly* the transition the tail-caller's own `return` of
`retVal` would have made: at the root it halts with `retVal`; under a caller it writes
`caller.destination` and resumes the caller at `caller.returnTarget` (the caller's
caller of the original tail-caller frame), restoring its protectors; into a diverging
caller it is UB. -/
theorem tailCall_trusted_return_through
    (s : MachineState) (calleeBody : CapturedMir) (argVals : List Value) (f : StackFrame)
    (retVal : Value) (span : String) (cb : Option CapturedMir)
    (h0 : get? f.locals 0 = some (.init retVal)) :
    (∀ (f' : StackFrame) (span' : String) (cb' : Option CapturedMir),
        get? f'.locals 0 = some (.init retVal) →
        evalTerminator ⟨f, (enterTailCalleeFrame s.memory calleeBody argVals).memory⟩
            ⟨.return_, span⟩ cb =
          evalTerminator ⟨f', (enterTailCalleeFrame s.memory calleeBody argVals).memory⟩
            ⟨.return_, span'⟩ cb') ∧
      (s.memory.callStack = [] →
        evalTerminator ⟨f, (enterTailCalleeFrame s.memory calleeBody argVals).memory⟩
            ⟨.return_, span⟩ cb =
          MirStepNode.retNormal retVal (enterTailCalleeFrame s.memory calleeBody argVals).memory) ∧
      (∀ (caller : SavedCallerFrame) (rest : List SavedCallerFrame) (upd : List LocalSlot),
        s.memory.callStack = caller :: rest → caller.isDiverging = false →
        writePlaceValue caller.frame.locals s.memory.borrows caller.destination retVal = .ok upd →
        evalTerminator ⟨f, (enterTailCalleeFrame s.memory calleeBody argVals).memory⟩
            ⟨.return_, span⟩ cb =
          MirStepNode.step
            { frame := { caller.frame with blockIdx := caller.returnTarget, stmtIdx := 0,
                                           locals := upd }
              memory := { s.memory with callStack := rest,
                                        activeCallee := some caller.callerBody,
                                        activeProtectors := restoreCallerProtectors caller } } ∧
        toMrStackFrame { caller.frame with blockIdx := caller.returnTarget, stmtIdx := 0,
                                           locals := upd } =
          MrStackFrame.jump_to_block (toMrStackFrame caller.frame) caller.returnTarget) ∧
      (∀ (caller : SavedCallerFrame) (rest : List SavedCallerFrame),
        s.memory.callStack = caller :: rest → caller.isDiverging = true →
        evalTerminator ⟨f, (enterTailCalleeFrame s.memory calleeBody argVals).memory⟩
            ⟨.return_, span⟩ cb = MirStepNode.fail .ub) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f' span' cb' h0'
    simp only [evalTerminator, h0, h0']
  · intro hnil
    simp only [evalTerminator, h0, enterTailCalleeFrame, hnil]
  · intro caller rest upd hcs hdiv hw
    refine ⟨?_, rfl⟩
    simp only [evalTerminator, h0, enterTailCalleeFrame, hcs, hdiv, hw]
  · intro caller rest hcs hdiv
    simp only [evalTerminator, h0, enterTailCalleeFrame, hcs, hdiv]

/-- **Trusted external tail call (universal).** A direct tail call to a callee without a
linked body emits the external `MirCallReq` with the evaluated arguments and the current
memory, resuming with `resumeExternalTailCall`. -/
theorem tailCall_trusted_external
    (s : MachineState) (func : Operand) (argOps : List Operand) (span : String)
    (callerBody : CapturedMir) (defPath : DefPath) (argVals : List Value)
    (locals' : List LocalSlot)
    (hfunc : extractCalleeDefPath? func = some defPath)
    (hargs : evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals = .ok argVals locals')
    (hnone : lookupCallee s.memory.callees callerBody.layouts defPath
      (extractCalleeTypeArgs func) s.memory.traitImpls = none) :
    evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) =
      MirStepNode.extCall
        { defPath := defPath, typeArgs := extractCalleeTypeArgs func, args := argVals,
          memory := s.memory }
        resumeExternalTailCall := by
  simp only [evalTerminator, evalTailCallTerminator, resolveCallTarget, hfunc,
    hargs, hnone]

/-- The `MirExecState` a step node denotes (`tau`, `ret`, or a fault). -/
def nodeState : MirStepNode → Option MirExecState
  | .tau s => some s
  | .ret out => some (.halted out)
  | .vis (.inl (.fail k)) _ => some (.faulted k)
  | _ => none

/-- **Trusted external return-through (universal).** When the external tail-callee returns
`retVal` with memory `memAfter`, the resumption is *exactly* the `return` of `retVal` from
any frame in `memAfter` — the external callee, too, returns straight into the caller's
caller (halting at the root, UB into a diverging caller). Unwinding and aborting follow
the caller stack (`unwindFromCallStack`) and abort. -/
theorem tailCall_trusted_external_resume_is_return
    (retVal : Value) (memAfter : Memory) (f : StackFrame) (span : String)
    (cb : Option CapturedMir) (h0 : get? f.locals 0 = some (.init retVal)) :
    some (resumeExternalTailCall (.returned retVal memAfter)) =
        nodeState (evalTerminator ⟨f, memAfter⟩ ⟨.return_, span⟩ cb) ∧
      resumeExternalTailCall (.panicked memAfter) =
        unwindFromCallStack memAfter.callStack memAfter ∧
      resumeExternalTailCall .aborted = .halted .abort := by
  refine ⟨?_, rfl, rfl⟩
  simp only [resumeExternalTailCall, evalTerminator, h0]
  rcases memAfter.callStack with _ | ⟨caller, rest⟩
  · rfl
  · dsimp only
    cases caller.isDiverging
    · dsimp only
      cases writePlaceValue caller.frame.locals memAfter.borrows caller.destination retVal <;> rfl
    · rfl

/-- **Trusted fail-closed tail calls (universal).** Every tail call whose callee or
arguments cannot be resolved faults with UB: a callee operand whose evaluation is UB or
yields a non-function value (a scalar, a non-unit aggregate, a pointer with a non-zero
offset, a pointer that is a stack borrow, an unregistered function pointer, or one whose
signature/arity/ABI is incompatible with the call site), a resolved callee whose linked
body is incompatible with the reified signature (`checkCalleeTargetCompatible`), and an
argument whose evaluation is UB (e.g. moving a dead local). A zero-sized function-item
operand (`.unit` of `FnDef` type) resolves to its function. -/
theorem tailCall_trusted_fail_closed_universal
    (s : MachineState) (func : Operand) (argOps : List Operand) (span : String)
    (callerBody : CapturedMir) (hnodirect : extractCalleeDefPath? func = none) :
    (evalOperand s.frame.locals func s.memory.borrows s.memory.globals callerBody.layouts
        s.memory.callerLocals = .ub →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub) ∧
    (∀ (sc : ScalarInt) (l : List LocalSlot),
      evalOperand s.frame.locals func s.memory.borrows s.memory.globals callerBody.layouts
          s.memory.callerLocals = .ok (.scalar sc) l →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub) ∧
    (∀ (vi : Nat) (v : Value) (vs : List Value) (l : List LocalSlot),
      evalOperand s.frame.locals func s.memory.borrows s.memory.globals callerBody.layouts
          s.memory.callerLocals = .ok (.aggregate vi (v :: vs)) l →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub) ∧
    (∀ (p : ProvenancePtr) (sz : Nat) (l : List LocalSlot),
      evalOperand s.frame.locals func s.memory.borrows s.memory.globals callerBody.layouts
          s.memory.callerLocals = .ok (.ptr p sz) l →
      (sz ≠ 8 ∨ p.offsetBytes ≠ 0 ∨ (lookupBorrow s.memory.borrows p.tag).isSome ∨
        lookupFnPtr s.memory.fnPtrs p.allocId = none) →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub) ∧
    (∀ (p : ProvenancePtr) (l : List LocalSlot) (fnEntry : FnPtrEntry),
      evalOperand s.frame.locals func s.memory.borrows s.memory.globals callerBody.layouts
          s.memory.callerLocals = .ok (.ptr p 8) l →
      p.offsetBytes = 0 → lookupBorrow s.memory.borrows p.tag = none →
      lookupFnPtr s.memory.fnPtrs p.allocId = some fnEntry →
      fnEntryCompatibleWithCallSite fnEntry (length argOps)
          (operandTy callerBody.localDecls callerBody.layouts func) = false →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub) ∧
    (∀ (p : ProvenancePtr) (l : List LocalSlot) (fnEntry : FnPtrEntry) (argVals : List Value)
        (l' : List LocalSlot) (calleeBody : CapturedMir),
      evalOperand s.frame.locals func s.memory.borrows s.memory.globals callerBody.layouts
          s.memory.callerLocals = .ok (.ptr p 8) l →
      p.offsetBytes = 0 → lookupBorrow s.memory.borrows p.tag = none →
      lookupFnPtr s.memory.fnPtrs p.allocId = some fnEntry →
      fnEntryCompatibleWithCallSite fnEntry (length argOps)
          (operandTy callerBody.localDecls callerBody.layouts func) = true →
      evalOperands l argOps s.memory.borrows s.memory.globals callerBody.layouts
          s.memory.callerLocals = .ok argVals l' →
      lookupCallee s.memory.callees callerBody.layouts fnEntry.defPath fnEntry.typeArgs
          s.memory.traitImpls = some calleeBody →
      checkCalleeTargetCompatible
          { defPath := fnEntry.defPath, typeArgs := fnEntry.typeArgs, fnSig := fnEntry.fnSig,
            isIndirect := true } calleeBody (length argVals) = false →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub) ∧
    (∀ (l : List LocalSlot) (dp : DefPath) (tys : List RigidTy),
      evalOperand s.frame.locals func s.memory.borrows s.memory.globals callerBody.layouts
          s.memory.callerLocals = .ok .unit l →
      extractFnItemTarget? (operandTy callerBody.localDecls callerBody.layouts func) =
        some (dp, tys) →
      evalOperands l argOps s.memory.borrows s.memory.globals callerBody.layouts
          s.memory.callerLocals = .ub →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub) ∧
    (∀ (l : List LocalSlot) (dp : DefPath) (tys : List RigidTy) (argVals : List Value)
        (l' : List LocalSlot) (calleeBody : CapturedMir),
      evalOperand s.frame.locals func s.memory.borrows s.memory.globals callerBody.layouts
          s.memory.callerLocals = .ok .unit l →
      extractFnItemTarget? (operandTy callerBody.localDecls callerBody.layouts func) =
        some (dp, tys) →
      evalOperands l argOps s.memory.borrows s.memory.globals callerBody.layouts
          s.memory.callerLocals = .ok argVals l' →
      lookupCallee s.memory.callees callerBody.layouts dp tys s.memory.traitImpls =
        some calleeBody →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) =
        MirStepNode.step (enterTailCalleeFrame s.memory calleeBody argVals)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    simp only [evalTerminator, evalTailCallTerminator, resolveCallTarget,
      hnodirect, h]
  · intro sc l h
    simp only [evalTerminator, evalTailCallTerminator, resolveCallTarget,
      hnodirect, h]
  · intro vi v vs l h
    cases vi <;>
      simp only [evalTerminator, evalTailCallTerminator, resolveCallTarget,
        hnodirect, h]
  · intro p sz l h hbad
    rcases hbad with hsz' | hoff' | hbor' | hnone
    · have hb : Nat.beq sz 8 = false :=
        Bool.eq_false_iff.mpr (fun hh => hsz' (Nat.eq_of_beq_eq_true hh))
      simp only [evalTerminator, evalTailCallTerminator, resolveCallTarget, hnodirect, h, hb,
        Bool.false_and]
    · have ho : Nat.beq p.offsetBytes 0 = false :=
        Bool.eq_false_iff.mpr (fun hh => hoff' (Nat.eq_of_beq_eq_true hh))
      simp only [evalTerminator, evalTailCallTerminator, resolveCallTarget, hnodirect, h, ho,
        Bool.false_and, Bool.and_false]
    · obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hbor'
      simp only [evalTerminator, evalTailCallTerminator, resolveCallTarget, hnodirect, h, he,
        Bool.and_false]
    · rcases Bool.eq_false_or_eq_true (Nat.beq sz 8) with hb | hb <;>
        rcases Bool.eq_false_or_eq_true (Nat.beq p.offsetBytes 0) with ho | ho <;>
        cases hl : lookupBorrow s.memory.borrows p.tag <;>
        simp only [evalTerminator, evalTailCallTerminator, resolveCallTarget, hnodirect, h, hb, ho,
          hl, hnone, Bool.and_true, Bool.and_false]
  · intro p l fnEntry h hoff hbor hfn hcompat
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
      hnodirect, h, hoff, hbor, hfn, hcompat, Nat.beq_refl, Bool.and_self]
  · intro p l fnEntry argVals l' calleeBody h hoff hbor hfn hcompat hargs hfind hbody
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
      hnodirect, h, hoff, hbor, hfn, hcompat, Nat.beq_refl, Bool.and_self, hargs, hfind, hbody]
  · intro l dp tys h hfi hargs
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
      hnodirect, h, hfi, hargs]
  · intro l dp tys argVals l' calleeBody h hfi hargs hfind
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
      hnodirect, h, hfi, hargs, hfind, checkCalleeTargetCompatible_direct]

/-- **Trusted non-function callees (universal).** Whatever a non-direct callee operand
evaluates to, if it is not a pointer and not a zero-sized value of function-item type
(`extractFnItemTarget? = none`), the tail call is UB — scalars, unit, and every aggregate
(including a zero-sized `.aggregate 0 []` of non-function type). -/
theorem tailCall_trusted_non_function_value_ub
    (s : MachineState) (func : Operand) (argOps : List Operand) (span : String)
    (callerBody : CapturedMir) (hnodirect : extractCalleeDefPath? func = none)
    (v : Value) (l : List LocalSlot)
    (h : evalOperand s.frame.locals func s.memory.borrows s.memory.globals callerBody.layouts
      s.memory.callerLocals = .ok v l)
    (hnp : ∀ p sz, v ≠ .ptr p sz)
    (hfi : extractFnItemTarget? (operandTy callerBody.localDecls callerBody.layouts func) = none) :
    evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub := by
  cases v with
  | unit =>
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
      hnodirect, h, hfi]
  | scalar sc =>
    simp only [evalTerminator, evalTailCallTerminator, resolveCallTarget, hnodirect, h]
  | ptr p sz => exact absurd rfl (hnp p sz)
  | aggregate vi fs =>
    cases vi <;> cases fs <;>
      simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
        hnodirect, h, hfi]

/-- **Trusted unwind-through (universal).** Unwinding (`UnwindResume`) out of the
tail-callee depends only on the memory — which the tail call left unchanged except for the
active body — so it is exactly the unwind the tail-caller would have performed: it pops into
the caller's caller with the original call's `returnUnwind` action. -/
theorem tailCall_trusted_unwind_through (s : MachineState) (calleeBody : CapturedMir)
    (argVals : List Value) (f f' : StackFrame) (span span' : String)
    (cb cb' : Option CapturedMir) :
    evalTerminator ⟨f, (enterTailCalleeFrame s.memory calleeBody argVals).memory⟩
        ⟨.unwindResume, span⟩ cb =
      evalTerminator ⟨f', (enterTailCalleeFrame s.memory calleeBody argVals).memory⟩
        ⟨.unwindResume, span'⟩ cb' ∧
    evalTerminator ⟨f, (enterTailCalleeFrame s.memory calleeBody argVals).memory⟩
        ⟨.unwindResume, span⟩ cb =
      match unwindFromCallStack s.memory.callStack
          { s.memory with activeCallee := some calleeBody } with
      | .running nextState => MirStepNode.step nextState
      | .halted out => MirStepNode.retOutcome out
      | .faulted fk => MirStepNode.fail fk :=
  ⟨rfl, rfl⟩

/-- **Trusted direct-call and `.unsupported` fail-closed paths (universal).** Complementing
`tailCall_trusted_fail_closed_universal` (which covered non-direct `func`), a direct tail
call (`extractCalleeDefPath? func = some defPath`) whose argument evaluation is `.ub` or
`.unsupported` fails closed with `MirStepNode.fail .ub` or `MirStepNode.unsupported`; an
indirect tail call whose callee operand evaluation is `.unsupported` fails closed with
`MirStepNode.unsupported`; an indirect tail call through a valid function pointer whose
argument evaluation is `.ub` or `.unsupported` fails closed; and a zero-sized
`.aggregate 0 []` function-item callee resolves to its target just like `.unit`. -/
theorem tailCall_trusted_direct_and_unsupported_fail_closed
    (s : MachineState) (func : Operand) (argOps : List Operand) (span : String)
    (callerBody : CapturedMir) :
    (∀ defPath : DefPath, extractCalleeDefPath? func = some defPath →
      evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals
          callerBody.layouts s.memory.callerLocals = .ub →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub) ∧
    (∀ defPath : DefPath, extractCalleeDefPath? func = some defPath →
      evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals
          callerBody.layouts s.memory.callerLocals = .unsupported →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.unsupported) ∧
    (extractCalleeDefPath? func = none →
      evalOperand s.frame.locals func s.memory.borrows s.memory.globals callerBody.layouts
          s.memory.callerLocals = .unsupported →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.unsupported) ∧
    (∀ (p : ProvenancePtr) (l : List LocalSlot) (fnEntry : FnPtrEntry),
      extractCalleeDefPath? func = none →
      evalOperand s.frame.locals func s.memory.borrows s.memory.globals callerBody.layouts
          s.memory.callerLocals = .ok (.ptr p 8) l →
      p.offsetBytes = 0 → lookupBorrow s.memory.borrows p.tag = none →
      lookupFnPtr s.memory.fnPtrs p.allocId = some fnEntry →
      fnEntryCompatibleWithCallSite fnEntry (length argOps)
          (operandTy callerBody.localDecls callerBody.layouts func) = true →
      (evalOperands l argOps s.memory.borrows s.memory.globals callerBody.layouts
            s.memory.callerLocals = .ub →
        evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) = MirStepNode.fail .ub) ∧
      (evalOperands l argOps s.memory.borrows s.memory.globals callerBody.layouts
            s.memory.callerLocals = .unsupported →
        evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) =
          MirStepNode.unsupported)) ∧
    (∀ (l : List LocalSlot) (dp : DefPath) (tys : List RigidTy) (argVals : List Value)
        (l' : List LocalSlot) (calleeBody : CapturedMir),
      extractCalleeDefPath? func = none →
      evalOperand s.frame.locals func s.memory.borrows s.memory.globals callerBody.layouts
          s.memory.callerLocals = .ok (.aggregate 0 []) l →
      extractFnItemTarget? (operandTy callerBody.localDecls callerBody.layouts func) =
        some (dp, tys) →
      evalOperands l argOps s.memory.borrows s.memory.globals callerBody.layouts
          s.memory.callerLocals = .ok argVals l' →
      lookupCallee s.memory.callees callerBody.layouts dp tys s.memory.traitImpls =
        some calleeBody →
      evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) =
        MirStepNode.step (enterTailCalleeFrame s.memory calleeBody argVals)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro defPath hfunc hargs
    simp only [evalTerminator, evalTailCallTerminator, resolveCallTarget, hfunc, hargs]
  · intro defPath hfunc hargs
    simp only [evalTerminator, evalTailCallTerminator, resolveCallTarget, hfunc, hargs]
  · intro hnodirect hfunc
    simp only [evalTerminator, evalTailCallTerminator, resolveCallTarget, hnodirect, hfunc]
  · intro p l fnEntry hnodirect h hoff hbor hfn hcompat
    refine ⟨?_, ?_⟩ <;> intro hargs <;>
      simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
        hnodirect, h, hoff, hbor, hfn, hcompat, Nat.beq_refl, Bool.and_self, hargs]
  · intro l dp tys argVals l' calleeBody hnodirect h hfi hargs hfind
    simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
      hnodirect, h, hfi, hargs, hfind, checkCalleeTargetCompatible_direct]

/-- **Trusted return-through fail-closed paths (universal).** When the tail-callee executes
`.return_`, an uninitialized, dead, or missing `_0` slot faults with `.ub`; and when `_0` is
initialized to `retVal` under a non-diverging `caller :: rest`, a destination write
(`writePlaceValue`) that faults with `.ub` or `.unsupported` fails closed on both in-table
and external (`resumeExternalTailCall`) tail-call returns. -/
theorem tailCall_trusted_return_through_fail_closed
    (s : MachineState) (calleeBody : CapturedMir) (argVals : List Value) (f : StackFrame)
    (retVal : Value) (span : String) (cb : Option CapturedMir) :
    ((get? f.locals 0 = some .uninit ∨ get? f.locals 0 = some .dead ∨ get? f.locals 0 = none) →
      evalTerminator ⟨f, (enterTailCalleeFrame s.memory calleeBody argVals).memory⟩
          ⟨.return_, span⟩ cb = MirStepNode.fail .ub) ∧
    (∀ (caller : SavedCallerFrame) (rest : List SavedCallerFrame),
      get? f.locals 0 = some (.init retVal) →
      s.memory.callStack = caller :: rest → caller.isDiverging = false →
      writePlaceValue caller.frame.locals s.memory.borrows caller.destination retVal = .ub →
      evalTerminator ⟨f, (enterTailCalleeFrame s.memory calleeBody argVals).memory⟩
          ⟨.return_, span⟩ cb = MirStepNode.fail .ub ∧
      resumeExternalTailCall
          (.returned retVal (enterTailCalleeFrame s.memory calleeBody argVals).memory) =
        .faulted .ub) ∧
    (∀ (caller : SavedCallerFrame) (rest : List SavedCallerFrame),
      get? f.locals 0 = some (.init retVal) →
      s.memory.callStack = caller :: rest → caller.isDiverging = false →
      writePlaceValue caller.frame.locals s.memory.borrows caller.destination retVal =
        .unsupported →
      evalTerminator ⟨f, (enterTailCalleeFrame s.memory calleeBody argVals).memory⟩
          ⟨.return_, span⟩ cb = MirStepNode.unsupported ∧
      resumeExternalTailCall
          (.returned retVal (enterTailCalleeFrame s.memory calleeBody argVals).memory) =
        .faulted .unsupported) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (h0 | h0 | h0) <;> simp only [evalTerminator, h0]
  · intro caller rest h0 hcs hdiv hw
    refine ⟨?_, ?_⟩ <;>
      simp only [evalTerminator, resumeExternalTailCall, h0, enterTailCalleeFrame, hcs, hdiv, hw]
  · intro caller rest h0 hcs hdiv hw
    refine ⟨?_, ?_⟩ <;>
      simp only [evalTerminator, resumeExternalTailCall, h0, enterTailCalleeFrame, hcs, hdiv, hw]

/-- A body whose block ends in a terminator rejected by `MiniRustSpec`'s fragment check is
not in the `MiniRustSpec` fragment. -/
theorem inFragment_false_of_term {body : CapturedMir} {bb : BasicBlockData}
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

/-- **LeanMiri tail-call lockstep (universal).** If the Trusted call stack and the LeanMiri
frames are shape-related and the active frame has a caller continuation (`goto`: a nested
frame, or a modular root with an external caller), then after the Trusted tail call
(`enterTailCalleeFrame`) and the transcribed `Call.evalTailCallTerminator` (matching
arity), the states are again shape-related with the *same* root continuation: the depth
is unchanged in both (no frame is pushed, the frame-index check passes), the machine is
untouched, and the new active LeanMiri frame runs the callee from `bb0[0]` with the
inherited continuation of the tail-caller — so the callee returns where the tail-caller
would have returned. -/
theorem tailCall_leanMiri_shape_lockstep {B P M : Type}
    (s : MachineState) (calleeBody : CapturedMir) (argVals : List Value)
    (rootCont : LeanMiri.ReturnContinuation UnwindAction)
    (m : LeanMiri.StepState B P UnwindAction M) (callee : B) (n : Nat)
    (hrel : StackShapeRel rootCont s.memory.callStack m)
    (hgoto : ∃ ret u, activeCont rootCont s.memory.callStack = .goto ret u) :
    ∃ m', LeanMiri.evalTailCallTerminator callee n n m = .ok m' ∧
      StackShapeRel rootCont (enterTailCalleeFrame s.memory calleeBody argVals).memory.callStack
        m' ∧
      m'.frames.length = m.frames.length ∧ m'.machine = m.machine ∧
      (∃ f, m'.frames.getLast? = some f ∧ f.body = callee ∧ f.location = .mir ⟨0, 0⟩ ∧
        f.returnContinuation = activeCont rootCont s.memory.callStack) := by
  obtain ⟨ret, u, hact⟩ := hgoto
  obtain ⟨init, last, hfr, hlast, hmap⟩ := shape_last hrel
  let newF : LeanMiri.Frame B P UnwindAction :=
    { body := callee, returnContinuation := .goto ret u, returnPlace := last.returnPlace,
      location := .mir ⟨0, 0⟩ }
  refine ⟨{ m with frames := init ++ [newF] }, ?_, ?_, ?_, rfl, ⟨newF, by simp, rfl, rfl, hact.symm⟩⟩
  · rw [hact] at hlast
    have hpass : LeanMiri.passArgsError (fun _ => true) n 0 n = none :=
      passArgsError_all_ok _ n n 0 (by omega) (fun _ _ _ => rfl)
    simp only [LeanMiri.evalTailCallTerminator, LeanMiri.initFnTailCall, hfr,
      List.getLast?_concat, hlast, hpass, Nat.lt_irrefl, ite_false, List.dropLast_concat]
    simp [newF]
  · show (init ++ [newF]).map (·.returnContinuation) = _
    rw [List.map_append]
    show init.map (·.returnContinuation) ++ [LeanMiri.ReturnContinuation.goto ret u] = _
    rw [← hact]
    exact hmap
  · simp [hfr]

/-- **LeanMiri whole-program-root divergence (universal).** At a Trusted root frame that is
shape-related to a LeanMiri `stop` frame (the whole-program root), Trusted's tail call
steps into the callee, whereas the transcribed `Call.initFnTailCall` raises
`invalidProgram "cannot tailcall as root of stack"` (rustc's `bug!("can't tailcall as
root")`) — a non-UB rejection; the modular-root relation (`goto`) is covered by
`tailCall_leanMiri_shape_lockstep`. -/
theorem tailCall_leanMiri_root_stop_diverges {B P M : Type}
    (s : MachineState) (func : Operand) (argOps : List Operand) (span : String)
    (callerBody calleeBody : CapturedMir) (defPath : DefPath) (argVals : List Value)
    (locals' : List LocalSlot)
    (hfunc : extractCalleeDefPath? func = some defPath)
    (hargs : evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals = .ok argVals locals')
    (hfind : lookupCallee s.memory.callees callerBody.layouts defPath
      (extractCalleeTypeArgs func) s.memory.traitImpls = some calleeBody)
    (hroot : s.memory.callStack = []) (c : Bool)
    (m : LeanMiri.StepState B P UnwindAction M) (callee : B) (k n : Nat)
    (hrel : StackShapeRel (.stop c) s.memory.callStack m) :
    evalTerminator s ⟨.tailCall func argOps, span⟩ (some callerBody) =
        MirStepNode.step (enterTailCalleeFrame s.memory calleeBody argVals) ∧
      LeanMiri.evalTailCallTerminator callee k n m =
        .error (.invalidProgram "cannot tailcall as root of stack") ∧
      (LeanMiri.StepError.invalidProgram "cannot tailcall as root of stack").isUB = false := by
  refine ⟨(tailCall_trusted_direct_enters_without_push s func argOps span callerBody calleeBody
    defPath argVals locals' hfunc hargs hfind).1, ?_, rfl⟩
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
    LeanMiri.evalTailCallTerminator callee n n m false cleanupNormal =
        .error (.undefinedBehavior "AbiMismatchReturn") ∧
      (LeanMiri.StepError.undefinedBehavior "AbiMismatchReturn").isUB = true ∧
      LeanMiri.evalTailCallTerminator callee n n m true false =
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
    LeanMiri.evalTailCallTerminator callee n n m retAbiCompat cleanupNormal compat =
        .error (.undefinedBehavior s!"AbiMismatchArgument {j}") ∧
      (LeanMiri.StepError.undefinedBehavior s!"AbiMismatchArgument {j}").isUB = true ∧
      LeanMiri.passArgsError (fun _ => true) n 0 n = none := by
  have hfirst := passArgsError_first_mismatch compat n j hj hbad n 0 (Nat.zero_le j) (by omega)
    (fun x _ hx => hpre x hx)
  refine ⟨?_, rfl, passArgsError_all_ok _ n n 0 (by omega) (fun _ _ _ => rfl)⟩
  simp only [LeanMiri.evalTailCallTerminator, LeanMiri.initFnTailCall, hlast, hgoto, hfirst]



/-- **LeanMiri call contrast (universal).** A returning Trusted `call` (`pushCalleeFrame`)
and the transcribed call push both grow the stack by one frame and stay shape-related —
the pushed continuation is the saved caller's `goto targetBb` — whereas a tail call keeps
the depth (`tailCall_leanMiri_shape_lockstep`). -/
theorem tailCall_leanMiri_call_pushes {B P M : Type}
    (s : MachineState) (callerBody calleeBody : CapturedMir) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (argVals : List Value)
    (unwind : UnwindAction) (rootCont : LeanMiri.ReturnContinuation UnwindAction)
    (m : LeanMiri.StepState B P UnwindAction M) (callee : B) (dest : P)
    (hrel : StackShapeRel rootCont s.memory.callStack m) :
    StackShapeRel rootCont
        (pushCalleeFrame s callerBody locals' destination targetBb calleeBody argVals unwind
          ).memory.callStack
        (LeanMiri.evalCallPush callee dest (some targetBb) unwind m) ∧
      (LeanMiri.evalCallPush callee dest (some targetBb) unwind m).frames.length =
        m.frames.length + 1 := by
  refine ⟨?_, by simp [LeanMiri.evalCallPush]⟩
  unfold StackShapeRel at hrel ⊢
  simp only [LeanMiri.evalCallPush, pushCalleeFrame, List.map_append, hrel, List.map_cons,
    List.reverse_cons, contOfCaller, List.map_nil]
  rfl

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
`main`. The Trusted continuation stack after the call is exactly the LeanMiri shape
`[stop, goto bb1]`. -/
theorem tailCall_witness_nested_runs :
    retVal? (Anneal.MirFuelFree.runMirExecBounded 7 mainBody (.running mainInit)) =
        some (.scalar ⟨5, 4⟩) ∧
      depth? (execN mainBody 2 (.running mainInit)) = some 1 ∧
      depth? (execN mainBody 3 (.running mainInit)) = some 1 ∧
      depth? (execN mainBody 5 (.running mainInit)) = some 0 ∧
      depth? (execN mainCBody 4 (.running mainCInit)) = some 2 ∧
      retVal? (Anneal.MirFuelFree.runMirExecBounded 10 mainCBody (.running mainCInit)) =
        some (.scalar ⟨5, 4⟩) ∧
      trustedConts? (.stop false) (execN mainBody 3 (.running mainInit)) =
        some [.stop false, .goto (some 1) .continue_] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
the external request `ext::h(7)` with the current memory, and the external answer `9` halts
the run with `9`; nested under `main`, the external answer lands in `main`'s destination and
`main` returns `9`. -/
theorem tailCall_witness_external :
    stepMirFn fExtBody (initMachineState fExtBody [.scalar ⟨7, 4⟩]) =
        MirStepNode.extCall
          { defPath := "ext::h", typeArgs := [], args := [.scalar ⟨7, 4⟩],
            memory := (initMachineState fExtBody [.scalar ⟨7, 4⟩]).memory }
          resumeExternalTailCall ∧
      resumeExternalTailCall
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
          LeanMiri.StepState String Nat UnwindAction Unit) true true (fun i => i != 1) =
      .error (.undefinedBehavior "AbiMismatchArgument 1") ∧
    LeanMiri.evalTailCallTerminator "w::g" 2 1
        (⟨[lmFrame "w::f" (.goto (some 3) .continue_)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) true true (fun i => i != 1) =
      .error (.undefinedBehavior "calling a function with fewer arguments than it requires") ∧
    LeanMiri.evalTailCallTerminator "w::g" 2 2
        (⟨[lmFrame "w::f" (.goto (some 3) .continue_)], ()⟩ :
          LeanMiri.StepState String Nat UnwindAction Unit) true true (fun i => i != 0) =
      .error (.undefinedBehavior "AbiMismatchArgument 0") :=
  ⟨rfl, rfl, rfl⟩

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
  refine ⟨rfl, rfl, ?_, ?_, rfl⟩ <;> cases v <;> rfl

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
`uninitFieldWriteShell?` returns `none` (failing closed instead of materializing a default
shell). -/
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
      uninitFieldWriteShell? decls layouts l (.opaqueCast t) rest = none := by
  refine ⟨?_, rfl, ?_, rfl, rfl, rfl, rfl, rfl, ?_, rfl, ?_, ?_, rfl⟩
  · simp [placeTy, hdecl, resolveProjectedTy]
  · simp [placeTyResolved, hdecl, resolveProjectedTyResolved]
  · cases v <;> rfl
  · cases v <;> rfl
  · cases v <;> rfl

/-- **Trusted `evalPlaceRead`, `writePlaceValue`, `evalPlaceWrite`, and
`resolveBorrowWriteLocalProj` (universal).** On non-union places with `e ≠ .deref`,
`evalPlaceRead`, `writePlaceValue`, and `evalPlaceWrite` (with any active protectors)
through `.opaqueCast t :: e :: r` agree with `e :: r` when `decls = []` (or when `placeTy` /
`placeTyResolved` agrees); writing through `.opaqueCast t :: r` into an `.uninit` or `.dead`
local faults with `.ub`, and before a `.deref` on an initialized non-union local fails
closed with `.unsupported`; and `resolveBorrowWriteLocalProj` preserves `.opaqueCast t` in
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
    (∀ (r : List ProjectionElem),
      (get? locals l = some .uninit ∨ get? locals l = some .dead ∨ get? locals l = none) →
      writePlaceValue locals borrows ⟨l, .opaqueCast t :: r⟩ val [] layouts = .ub) ∧
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
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e r hnd
    have hread : ∀ v, readProjectedValue locals v (.opaqueCast t :: e :: r) =
        readProjectedValue locals v (e :: r) := fun v =>
      (opaqueCast_trusted_traversal_universal locals v v t (e :: r)).1
    have hwrite : ∀ v, writeProjectedValue locals v (.opaqueCast t :: e :: r) val =
        writeProjectedValue locals v (e :: r) val := fun v =>
      (opaqueCast_trusted_traversal_universal locals v val t (e :: r)).2.1
    have hpty : ∀ p, placeTyResolved [] layouts p = none := fun _ => by
      simp [placeTyResolved, get?]
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
      | _ => simp only [writePlaceValue, writeProjectedForLocal, hwrite]
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
  · intro r hslot
    rcases hslot with h | h | h <;> simp only [writePlaceValue, h]
  · intro v r hv
    have hw : writeProjectedValue locals v (.opaqueCast t :: .deref :: r) val = .unsupported := by
      rw [(opaqueCast_trusted_traversal_universal locals v val t (.deref :: r)).2.1]
      cases v <;> rfl
    simp only [writePlaceValue, hv, writeProjectedForLocal, hw]
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

/-- **Trusted place read/write with declarations (universal).** For any declaration table
(the one `stepMirFn` passes), a read or write through `(_l as T).e.r` (`e` not a
dereference) agrees with the cast-free place `_l.e.r` whenever neither place touches a union
and the cast does not change the validation types (`placeTy` / `placeTyResolved` agree, e.g.
when `T` is the declared type or the next projection fixes the type) — the type switch is
the *only* way an opaque cast is observable at a place (`opaqueCast_witness_type_switch`). -/
theorem opaqueCast_trusted_place_rw_with_decls
    (locals : List LocalSlot) (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot) (decls : List LocalDecl)
    (l : Nat) (t : Ty) (e : ProjectionElem) (r : List ProjectionElem) (val : Value)
    (hnd : ∀ r', e :: r ≠ .deref :: r')
    (hu : placeTouchesUnion decls layouts ⟨l, .opaqueCast t :: e :: r⟩ = false)
    (hu' : placeTouchesUnion decls layouts ⟨l, e :: r⟩ = false)
    (hty : placeTy decls layouts ⟨l, .opaqueCast t :: e :: r⟩ = placeTy decls layouts ⟨l, e :: r⟩)
    (htyR : placeTyResolved decls layouts ⟨l, .opaqueCast t :: e :: r⟩ =
      placeTyResolved decls layouts ⟨l, e :: r⟩) :
    evalPlaceRead locals ⟨l, .opaqueCast t :: e :: r⟩ borrows globals layouts callerLocals decls =
        evalPlaceRead locals ⟨l, e :: r⟩ borrows globals layouts callerLocals decls ∧
      writePlaceValue locals borrows ⟨l, .opaqueCast t :: e :: r⟩ val decls layouts =
        writePlaceValue locals borrows ⟨l, e :: r⟩ val decls layouts := by
  have hread : ∀ v, readProjectedValue locals v (.opaqueCast t :: e :: r) =
      readProjectedValue locals v (e :: r) := fun v =>
    (opaqueCast_trusted_traversal_universal locals v v t (e :: r)).1
  have hwrite : ∀ v, writeProjectedValue locals v (.opaqueCast t :: e :: r) val =
      writeProjectedValue locals v (e :: r) val := fun v =>
    (opaqueCast_trusted_traversal_universal locals v val t (e :: r)).2.1
  cases e with
  | deref => exact absurd rfl (hnd r)
  | _ =>
    constructor <;>
      simp only [evalPlaceRead, writePlaceValue, readProjectedForLocal, writeProjectedForLocal,
        hu, hu', hty, htyR, hread, hwrite]

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
  (opaqueCast_trusted_place_rw_with_decls ocLocals [] [] wLayouts [] [u32Decl "_0", pairDecl] 1
      tyPair (.field 1 tyU32) [] (.scalar ⟨5, 4⟩) (fun _ h => by cases h) rfl rfl rfl rfl).elim
    fun hr hw => ⟨rfl, hr, hw, rfl⟩

/-- **Documented type switch.** The opaque cast is observable exactly through typing: casting
the `(u32, u32)` local to `u8` switches the static place type (`placeTy`, which drives write
validation, and `placeTyResolved`, which drives read validation) from the declared pair type
to `u8`, while the value read is unchanged — so the agreement hypotheses of
`opaqueCast_trusted_place_rw_with_decls` are genuinely needed. -/
theorem opaqueCast_witness_type_switch :
    placeTy [u32Decl "_0", pairDecl] wLayouts ⟨1, [.opaqueCast tyU8]⟩ = some tyU8 ∧
      placeTy [u32Decl "_0", pairDecl] wLayouts ⟨1, []⟩ = some tyPair ∧
      placeTy [u32Decl "_0", pairDecl] wLayouts ⟨1, [.opaqueCast tyU8]⟩ ≠
        placeTy [u32Decl "_0", pairDecl] wLayouts ⟨1, []⟩ ∧
      evalPlaceRead ocLocals ⟨1, [.opaqueCast tyU8]⟩ [] [] wLayouts [] [u32Decl "_0", pairDecl] =
        evalPlaceRead ocLocals ⟨1, [.opaqueCast tyPair]⟩ [] [] wLayouts [] [u32Decl "_0", pairDecl] := by
  have h1 : placeTy [u32Decl "_0", pairDecl] wLayouts ⟨1, [.opaqueCast tyU8]⟩ = some tyU8 := rfl
  have h2 : placeTy [u32Decl "_0", pairDecl] wLayouts ⟨1, []⟩ = some tyPair := rfl
  refine ⟨h1, h2, ?_, rfl⟩
  rw [h1, h2]
  intro h
  simp [tyU8, tyPair] at h

/-- **Positive witness (moves).** `move (p as T)` is a *projected* move: it yields the whole
value and keeps `p` initialized (like Miri, whose moves do not de-initialize), whereas the
root move `move p` de-initializes `p` in Trusted (stricter than Miri). -/
theorem opaqueCast_witness_projected_move :
    evalOperand ocLocals (.move ⟨1, [.opaqueCast tyPair]⟩) = .ok pairVal ocLocals ∧
      evalOperand ocLocals (.move ⟨1, []⟩) = .ok pairVal [.uninit, .uninit] :=
  ⟨rfl, rfl⟩

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

/-! ## 4. Kernel axiom and non-vacuity audit

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
          `tailCall_leanMiri_arg_abi_universal]),
       ("positive", [`tailCall_leanMiri_witness, `tailCall_witness_nested_runs, `tailCall_witness_root_runs,
          `tailCall_witness_external, `tailCall_witness_indirect_and_zst]),
       ("negative", [`tailCall_witness_ub_cases, `tailCall_witness_direct_arity_divergence,
          `tailCall_leanMiri_witness_arg_abi])]),
    ("opaqueCast",
      [tr ++ `MirAst.ProjectionElem.opaqueCast],
      [lm ++ `projectOpaqueCast, lm ++ `placeProjectOpaqueCast],
      [("trusted", [`opaqueCast_trusted_traversal_universal, `opaqueCast_trusted_retype_universal,
          `opaqueCast_trusted_overlap_universal, `opaqueCast_trusted_place_read_universal,
          `opaqueCast_trusted_placeTy_and_helpers_universal,
          `opaqueCast_trusted_write_and_borrow_universal, `opaqueCast_trusted_place_rw_with_decls]),
       ("minirust", [`opaqueCast_minirust_corresponds]),
       ("leanmiri", [`opaqueCast_leanMiri_phase_boundary]),
       ("positive", [`opaqueCast_witness_read_write, `opaqueCast_witness_projected_move,
          `opaqueCast_witness_place_rw_with_decls]),
       ("negative", [`opaqueCast_witness_ub_not_masked, `opaqueCast_witness_references_reject,
          `opaqueCast_witness_type_switch])])]
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

