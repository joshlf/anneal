import Trusted.Rustc.V2026_06_01.Layout
import Trusted.Rustc.V2026_06_01.MirAst.Types
import Trusted.Rustc.V2026_06_01.MirAst.Places

namespace Trusted.Rustc.V2026_06_01.MirAst

open Trusted.Rustc.V2026_06_01.Layout

/-!
1-to-1 syntax of `Runtime(PostCleanup)` MIR basic-block indices, switch tables,
unwind actions, and control-flow terminators for `rustc 1.98.0-nightly`
(`14210df0e 2026-05-31`, `#99`, `#101`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L692-L1044>

> "pub enum TerminatorKind<'tcx> {
>     /// Block should have one successor in the graph; we jump there
>     Goto { target: BasicBlock },
> ...
>     /// A block terminated by an inline assembly block.
>     InlineAsm { ... },
> }"
-/

/--
0-based index of a basic block in a MIR control-flow graph, modeling
`rustc_middle::mir::BasicBlock`.

Index `0` always denotes `START_BLOCK` (`bb0`), the entry block of the MIR body.

Reference (`compiler/rustc_middle/src/mir/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/mod.rs#L1294-L1303>

> "rustc_index::newtype_index! {
>     /// A node in the MIR control-flow graph. There are no branches (e.g.,
>     /// `if`s, function calls, etc.) within a basic block, which makes it easier
>     /// to do data-flow analyses and optimizations. Instead, branches are
>     /// represented as an edge in a graph between basic blocks.
>     #[derive(HashStable)]
>     #[encodable]
>     #[orderable]
>     #[debug_format = \"bb{}\"]
>     pub struct BasicBlock {
>         const START_BLOCK = 0;
>     }
> }"
-/
abbrev BasicBlockIdx : Type := Nat

/--
Multi-way integer branch table for `TerminatorKind::SwitchInt`, modeling
`rustc_middle::mir::SwitchTargets`.

Field `branches` stores the `(value, targetBlock)` pairs corresponding to the
zipped `values: SmallVec<[u128; 1]>` and `targets[..values.len()]` in
`SwitchTargets`, and `otherwise` corresponds to `SwitchTargets::otherwise()`
(`targets.last()`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L999-L1014>

> "pub struct SwitchTargets {
>     /// Possible values. The locations to branch to in each case
>     /// are found in the corresponding indices from the `targets` vector.
>     values: SmallVec<[u128; 1]>,
>
>     /// Possible branch sites. The last element of this vector is used
>     /// for the otherwise branch, so targets.len() == values.len() + 1
>     /// should hold.
>     //
>     // This invariant is quite non-obvious and also could be improved.
>     // One way to make this invariant is to have something like this instead:
>     //
>     // branches: Vec<(ConstInt, BasicBlock)>,
>     // otherwise: BasicBlock // exhaustive if None
>     targets: SmallVec<[BasicBlock; 2]>,
> }"
-/
structure SwitchTargets : Type where
  /-- Explicit `(value, targetBlock)` pairs tested against the scrutinee. -/
  branches : List (Nat × BasicBlockIdx)
  /-- Fallback target block taken when no explicit value matches. -/
  otherwise : BasicBlockIdx

/--
Unwind behavior on potentially-panicking terminators (`Drop`, `Call`, `Assert`,
`InlineAsm`), modeling `rustc_middle::mir::UnwindAction`.

Constructors `.cleanup`, `.unreachable`, `.terminate`, and `.continue_`
correspond 1-to-1 to `UnwindAction::Cleanup`, `UnwindAction::Unreachable`,
`UnwindAction::Terminate`, and `UnwindAction::Continue`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1018-L1044>

> "pub enum UnwindAction {
>     /// No action is to be taken. Continue unwinding.
>     Continue,
>     /// Unwinding is not possible. Controls flow into the `Unreachable` terminator.
>     ///
>     /// Note that in runtime MIR, unwinding into an `Unreachable` action is UB, whereas in
>     /// analysis MIR it's merely a borrowck signal that unwinding is impossible.
>     Unreachable,
>     /// Terminate the execution of the process (`std::process::abort` or similar).
>     Terminate(UnwindTerminateReason),
>     /// Clean up the current stack frame and jump to the given basic block.
>     Cleanup(BasicBlock),
> }"
-/
inductive UnwindAction : Type where
  /-- Continue unwinding at `cleanupBlock` (`UnwindAction::Cleanup`). -/
  | cleanup (cleanupBlock : BasicBlockIdx) : UnwindAction
  /-- Unwinding is impossible; reaching unwind is UB in `Runtime` MIR
      (`UnwindAction::Unreachable`). -/
  | unreachable : UnwindAction
  /-- Terminate the process (`abort`) on unwind (`UnwindAction::Terminate`). -/
  | terminate : UnwindAction
  /-- Propagate unwind to the caller (`UnwindAction::Continue`). -/
  | continue_ : UnwindAction

/--
Basic-block control-flow terminator kind, modeling
`rustc_middle::mir::TerminatorKind` in `Runtime(PostCleanup)` MIR.

Constructors `.goto`, `.switchInt`, `.unwindResume`, `.unwindTerminate`,
`.return_`, `.unreachable`, `.drop`, `.call`, `.tailCall`, `.assert`, and
`.inlineAsm` correspond 1-to-1 to the runtime-phase variants of
`rustc_middle::mir::TerminatorKind` (coroutine/analysis-only variants `Yield`,
`CoroutineDrop`, `FalseEdge`, and `FalseUnwind` are lowered before
`Runtime(PostCleanup)`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L692-L981>

> "pub enum TerminatorKind<'tcx> {
>     /// Block should have one successor in the graph; we jump there
>     Goto { target: BasicBlock },
>
>     /// Switches based on the computed value.
>     ...
>     SwitchInt {
>         /// The discriminant value being tested.
>         discr: Operand<'tcx>,
>         targets: SwitchTargets,
>     },
>
>     /// Indicates that the landing pad is finished and that the process should
>     /// continue unwinding.
>     UnwindResume,
>
>     /// Indicates that the landing pad is finished and that the process should
>     /// terminate.
>     UnwindTerminate(UnwindTerminateReason),
>
>     /// Returns from the function.
>     ///
>     /// Like function calls, the exact semantics of returns in Rust are unclear. Returning very
>     /// likely at least assigns the value currently in the return place (`_0`) to the place
>     /// specified in the associated `Call` terminator in the calling function, as if assigned via
>     /// `dest = move _0`.
>     Return,
>
>     /// Indicates a terminator that can never be reached.
>     ///
>     /// Executing this terminator is UB.
>     Unreachable,
>
>     /// Drop the `Place`
>     Drop {
>         place: Place<'tcx>,
>         target: BasicBlock,
>         unwind: UnwindAction,
>         replace: bool,
>         drop: Option<BasicBlock>,
>         async_fut: Option<Local>,
>     },
>
>     /// Block ends with the call of a function.
>     Call {
>         func: Operand<'tcx>,
>         args: Box<[Spanned<Operand<'tcx>>]>,
>         destination: Place<'tcx>,
>         target: Option<BasicBlock>,
>         unwind: UnwindAction,
>         call_source: CallSource,
>         fn_span: Span,
>     },
>
>     /// Block ends with the call of a function that does not return to this stack frame.
>     TailCall {
>         func: Operand<'tcx>,
>         args: Box<[Spanned<Operand<'tcx>>]>,
>         fn_span: Span,
>     },
>
>     /// Jumps to the target if the condition has the expected value, otherwise panics.
>     Assert {
>         cond: Operand<'tcx>,
>         expected: bool,
>         msg: Box<AssertMessage<'tcx>>,
>         target: BasicBlock,
>         unwind: UnwindAction,
>     },
>     ...
>     /// A block terminated by an inline assembly block.
>     InlineAsm { ... },
> }"
-/
inductive TerminatorKind : Type where
  /-- Unconditional jump to `target` (`TerminatorKind::Goto`). -/
  | goto (target : BasicBlockIdx) : TerminatorKind
  /-- Multi-way integer branch on `discr` (`TerminatorKind::SwitchInt`). -/
  | switchInt (discr : Operand) (targets : SwitchTargets) : TerminatorKind
  /-- Resume unwinding from a cleanup pad (`TerminatorKind::UnwindResume`). -/
  | unwindResume : TerminatorKind
  /-- Abort unwinding immediately (`TerminatorKind::UnwindTerminate`). -/
  | unwindTerminate : TerminatorKind
  /-- Return from the current function (`TerminatorKind::Return`), reading
      `_0`. -/
  | return_ : TerminatorKind
  /-- Unreachable control flow; reaching this terminator is immediate UB
      (`TerminatorKind::Unreachable`). -/
  | unreachable : TerminatorKind
  /-- Unconditional runtime drop of `place` (`TerminatorKind::Drop`). -/
  | drop (place : Place) (target : BasicBlockIdx) (unwind : UnwindAction) : TerminatorKind
  /-- Function or intrinsic call (`TerminatorKind::Call`). -/
  | call
      (func : Operand)
      (args : List Operand)
      (destination : Place)
      (target : Option BasicBlockIdx)
      (unwind : UnwindAction) :
      TerminatorKind
  /-- Tail call (`TerminatorKind::TailCall`). -/
  | tailCall (func : Operand) (args : List Operand) : TerminatorKind
  /-- Runtime assertion checking that `cond == expected`
      (`TerminatorKind::Assert`). -/
  | assert
      (cond : Operand)
      (expected : Bool)
      (target : BasicBlockIdx)
      (unwind : UnwindAction) :
      TerminatorKind
  /-- Inline assembly execution (`TerminatorKind::InlineAsm`). -/
  | inlineAsm
      (template : String)
      (targets : List BasicBlockIdx)
      (unwind : UnwindAction) :
      TerminatorKind

/--
A MIR basic-block terminator paired with its source span description, modeling
`rustc_middle::mir::Terminator`.

Field `kind` corresponds to `Terminator::kind` and `span` stores the formatted
`SourceInfo::span` (`file:line:col`) for diagnostics.

Reference (`compiler/rustc_middle/src/mir/terminator.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/terminator.rs#L413-L416>

> "pub struct Terminator<'tcx> {
>     pub source_info: SourceInfo,
>     pub kind: TerminatorKind<'tcx>,
> }"
-/
structure Terminator : Type where
  /-- Terminator operation. -/
  kind : TerminatorKind
  /-- Source location summary (`file:line:col`) for diagnostics. -/
  span : String

end Trusted.Rustc.V2026_06_01.MirAst
