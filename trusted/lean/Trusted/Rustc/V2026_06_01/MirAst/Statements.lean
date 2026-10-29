import Trusted.Rustc.V2026_06_01.Layout
import Trusted.Rustc.V2026_06_01.MirAst.Types
import Trusted.Rustc.V2026_06_01.MirAst.Places
import Trusted.Rustc.V2026_06_01.MirAst.Rvalues

namespace Trusted.Rustc.V2026_06_01.MirAst

open Trusted.Rustc.V2026_06_01.Layout

/-!
1-to-1 syntax of `Runtime(PostCleanup)` MIR non-diverging intrinsics, retag
kinds, statement kinds, and spanned statements for `rustc 1.98.0-nightly`
(`14210df0e 2026-05-31`, `#99`, `#101`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L305-L492>

> "pub enum StatementKind<'tcx> {
>     /// Assign statementsroughly correspond to an assignment in Rust proper (`x = ...`)
>     /// except without the possibility of dropping the previous value (that must be done
>     /// separately, if at all).
>     Assign(Box<(Place<'tcx>, Rvalue<'tcx>)>),
> ...
>     /// No-op. Useful for deleting instructions without affecting statement indices.
>     Nop,
> }"
-/

/--
Non-diverging compiler intrinsic statements (`StatementKind::Intrinsic`),
modeling `rustc_middle::mir::NonDivergingIntrinsic`.

Constructor `.assume` corresponds to `NonDivergingIntrinsic::Assume` (where a
`false` operand is immediate undefined behavior) and `.copyNonOverlapping`
corresponds to `NonDivergingIntrinsic::CopyNonOverlapping`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L469-L492>

> "pub enum NonDivergingIntrinsic<'tcx> {
>     /// Informs the optimizer that a condition is always true.
>     /// If the condition is false, the behavior is undefined.
>     Assume(Operand<'tcx>),
>
>     ///projected form of `copy_nonoverlapping` intrinsic,
>     ///copies `count * size_of::<T>()` bytes from `src` to `dst`.
>     CopyNonOverlapping(Box<CopyNonOverlapping<'tcx>>),
> }"
-/
inductive NonDivergingIntrinsic : Type where
  /-- `core::hint::assert_inhabited` / `assume`
      (`NonDivergingIntrinsic::Assume`). -/
  | assume (op : Operand) : NonDivergingIntrinsic
  /-- Non-overlapping memory copy
      (`NonDivergingIntrinsic::CopyNonOverlapping`). -/
  | copyNonOverlapping (src : Operand) (dst : Operand) (count : Operand) : NonDivergingIntrinsic

/--
Retag flavor for pointer aliasing instrumentation (`StatementKind::Retag`),
modeling `rustc_middle::mir::RetagKind`.

Constructors `.fnEntry`, `.twoPhase`, `.raw`, and `.default` correspond 1-to-1
to the four variants of `rustc_middle::mir::RetagKind`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L276-L287>

> "pub enum RetagKind {
>     /// The initial retag of arguments when entering a function.
>     FnEntry,
>     /// Retagging for a two-phase borrow.
>     TwoPhase,
>     /// Retagging raw pointers.
>     Raw,
>     /// Normal retagging of references.
>     Default,
> }"
-/
inductive RetagKind : Type where
  /-- Entry of a function body (`RetagKind::FnEntry`). -/
  | fnEntry : RetagKind
  /-- Two-phase borrow reservation (`RetagKind::TwoPhase`). -/
  | twoPhase : RetagKind
  /-- Raw pointer retag (`RetagKind::Raw`). -/
  | raw : RetagKind
  /-- Standard reference retag (`RetagKind::Default`). -/
  | default : RetagKind

/--
Non-branching basic-block statement kind, modeling
`rustc_middle::mir::StatementKind` in `Runtime(PostCleanup)` MIR.

Constructors `.assign`, `.setDiscriminant`, `.deinit`, `.storageLive`,
`.storageDead`, `.retag`, `.placeMention`, `.intrinsic`, `.coverage`,
`.constEvalCounter`, `.backwardIncompatibleDropHint`, and `.nop` correspond
1-to-1 to the runtime-phase variants of `rustc_middle::mir::StatementKind`
(analysis-only statements `FakeRead` and `AscribeUserType` are eliminated before
`Runtime(PostCleanup)`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L305-L450>

> "pub enum StatementKind<'tcx> {
>     /// Assign statementsroughly correspond to an assignment in Rust proper (`x = ...`)
>     /// except without the possibility of dropping the previous value (that must be done
>     /// separately, if at all).
>     Assign(Box<(Place<'tcx>, Rvalue<'tcx>)>),
>     ...
>     /// Write the discriminant for a variant to the enum Place.
>     SetDiscriminant {
>         place: Box<Place<'tcx>>,
>         variant_index: VariantIdx,
>     },
>
>     /// Deinitializes the place.
>     ///
>     /// This writes `uninit` bytes to the entire place.
>     Deinit(Box<Place<'tcx>>),
>
>     /// `StorageLive` and `StorageDead` statements mark the live range of a local.
>     ...
>     StorageLive(Local),
>     StorageDead(Local),
>
>     /// Retag references in the given place, ensuring they got fresh tags.
>     ...
>     Retag(RetagKind, Box<Place<'tcx>>),
>
>     /// This statement exists to preserve a trace of a scrutinee matched against a wildcard binding.
>     ...
>     PlaceMention(Box<Place<'tcx>>),
>     ...
>     /// Executes a non-diverging intrinsic.
>     Intrinsic(Box<NonDivergingIntrinsic<'tcx>>),
>     ...
>     /// No-op. Useful for deleting instructions without affecting statement indices.
>     Nop,
> }"
-/
inductive StatementKind : Type where
  /-- Assign `rvalue` into `place` (`StatementKind::Assign`). -/
  | assign (place : Place) (rvalue : Rvalue) : StatementKind
  /-- Write discriminant `variantIdx` into `place`
      (`StatementKind::SetDiscriminant`). -/
  | setDiscriminant (place : Place) (variantIdx : VariantIdx) : StatementKind
  /-- Deinitialize `place` (`StatementKind::Deinit`). -/
  | deinit (place : Place) : StatementKind
  /-- Mark storage for `local_` as live (`StatementKind::StorageLive`). -/
  | storageLive (local_ : Local) : StatementKind
  /-- Mark storage for `local_` as dead (`StatementKind::StorageDead`). -/
  | storageDead (local_ : Local) : StatementKind
  /-- Aliasing model retag (`StatementKind::Retag`). -/
  | retag (kind : RetagKind) (place : Place) : StatementKind
  /-- Evaluate `place` without reading its value
      (`StatementKind::PlaceMention`). -/
  | placeMention (place : Place) : StatementKind
  /-- Execute a non-diverging intrinsic (`StatementKind::Intrinsic`). -/
  | intrinsic (intrinsic : NonDivergingIntrinsic) : StatementKind
  /-- Coverage counter increment (`StatementKind::Coverage`). -/
  | coverage : StatementKind
  /-- Const-evaluation step counter (`StatementKind::ConstEvalCounter`). -/
  | constEvalCounter : StatementKind
  /-- Backward-incompatible drop hint
      (`StatementKind::BackwardIncompatibleDropHint`). -/
  | backwardIncompatibleDropHint (place : Place) : StatementKind
  /-- No-operation (`StatementKind::Nop`). -/
  | nop : StatementKind

/--
A MIR statement paired with its human-readable source span description, modeling
`rustc_middle::mir::Statement`.

Field `kind` corresponds to `Statement::kind` and `span` stores the formatted
`SourceInfo::span` (`file:line:col`) for diagnostics.

Reference (`compiler/rustc_middle/src/mir/statement.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/statement.rs#L17-L22>

> "pub struct Statement<'tcx> {
>     pub source_info: SourceInfo,
>     pub kind: StatementKind<'tcx>,
> }"
-/
structure Statement : Type where
  /-- Statement operation. -/
  kind : StatementKind
  /-- Source location summary (`file:line:col`) for diagnostics. -/
  span : String

end Trusted.Rustc.V2026_06_01.MirAst
