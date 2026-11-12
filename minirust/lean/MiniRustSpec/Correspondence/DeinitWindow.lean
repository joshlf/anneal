/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.Run
import MiniRustSpec.Correspondence.DeinitLemmas

/-!
# Projected `Deinit`: the fragment `inFragmentD` and its lockstep simulation

`Trusted.MirSemantics.evalStmt` on a projected `Deinit(_t.f1...fk)` only checks that `_t` is
initialized and that the projected value is readable, and then advances with unchanged locals
(`Statements.lean:2583-2600`, `DeinitBridge.evalStmt_deinit_field`), whereas MiniRust's
`Statement::Deinit` stores `AbstractByte::Uninit` over the field's bytes and keeps every sibling
byte (`DeinitBridge.evalStatement_deinit_fieldPath`). The two models disagree on the field until
it is written again. The fragment below admits programs that never observe the disagreement and
proves a full lockstep simulation for them.

`inFragment` is unchanged: it still rejects every projected `Deinit`, so the inclusions
`inFragment_implies_inFragmentWithIntrinsics` and `inFragment_implies_progInFragmentWithIntrinsics`
and every theorem stated over `inFragment` keep their meaning. Instead:

* `eraseDeinit body` replaces every projected `Deinit(p)` by `PlaceMention(p)`;
* `holeAt body blk stmt` is the per-block forward dataflow of the open *hole*: a projected
  `Deinit(_t.ps)` opens the hole `(t, ps)`, and an assignment to a place of `_t` with the hole's
  byte range (`holeRange`) closes it;
* `deinitWindowOk body` (`blockWindowOk`, `windowStmtOk`) requires that a projected `Deinit`
  opens a hole only when none is open, on a `TupleSpec` local `_t` that is not moved out, at a
  scalar field of positive size (`deinitTargetOk`); that while the hole is open the only
  statements are disjoint sibling reads `_r = copy _t.g` (`siblingReadOk`), possibly through an
  integer cast (`castSiblingReadOk`: `_r = Cast(IntToInt, copy _t.g, it)`), hole-independent scalar
  local copies `_r = copy _q` (`localCopyWindowOk`), and the re-initialization of the hole's byte
  range by an integer constant of the field's type (`reinitOk`: `_t.f = const c`), by copying a
  distinct integer local of the field's type (`reinitCopyOk`: `_t.f = copy _r`), or by an integer
  binary operation of a distinct integer local and a constant (`reinitBinOpOk`:
  `_t.f = BinaryOp(op, copy _q, const c)`); and that the hole is closed before the block's
  terminator;
* `inFragmentD body := inFragment (eraseDeinit body) && deinitWindowOk body`.

The relation `StateRelD` is `StateRelN` of the erased body, or, while the hole `_t.ps` is open,
`StateRelN` of the erased body with a hole-free MiniRust machine `m0` from which the actual machine
differs only in the hole's `Uninit` bytes (`HoleRel`). `step_correspondence_D` proves the one-step
correspondence `StepRelD`:

* projected `Deinit` (`step_projDeinit`): Anneal keeps the locals and MiniRust writes the hole;
* any other statement or terminator while no hole is open: `step_correspondence_NF` applied to the
  erased body and the *actual* translation `translateFn body`, which agree on the current
  statement and terminator (`blk_eraseDeinit`, `stepMirFn_eraseDeinit_stmt`,
  `stepMirFn_eraseDeinit_term`);
* sibling read (`step_window_read`, `step_window_cast_read`), local copy
  (`step_window_local_copy`), and constant, local-copy, or binary-operation re-initialization
  (`step_window_reinit`, `step_window_reinit_copy`, `step_window_reinit_binop`) while the hole is
  open: the MiniRust step is computed on the hole-free and on the actual machine by the
  allocation-data-parametric `evalStatement_siblingRead_any`, `evalStatement_castSiblingRead_any`,
  `evalStatement_localCopy_any`, `evalStatement_reinit_any`, `evalStatement_reinitCopy_any`, and
  `evalStatement_reinitBinOp_any`.
  The read loads the same bytes (`spliceAt_drop_take_disjoint`) into `_r`'s allocation, which is
  not `_t`'s, and keeps the hole; the re-initialization overwrites the hole (`spliceAt_same`), so
  both machines agree and the hole closes.

Every `inFragment` body is an `inFragmentD` body (`inFragment_implies_inFragmentD`: it is its own
erasure and never opens a hole), so `step_correspondence_D` also covers the old fragment.
`reaches_rel_D`, `run_ret_D`, `step_start_D`, `run_ret_from_start_D`, `mirCall_ret_D`, and the full
whole-execution lift suite (`run_ub_rel_D`, `run_ub_D`, `run_ub_rel_from_start_D`,
`run_ub_from_start_D`, `steps_error_D`, `steps_error_from_start_D`, `mirNoUB_safe_D`,
`mirNoUB_safe_from_start_D`, `steps_outcome_D`, `steps_outcome_from_start_D`, `mirNoUB_progress_D`,
`mirNoUB_progress_from_start_D`, `mirNoUB_diverges_steps_ok_D`, `mirNoUB_diverges_from_start_D`,
`mirNoUB_diverges_rel_from_start_D`, `mirCall_ub_D`, `mirCall_ub_rel_D`, `mirCall_noUB_D`,
`mirCall_steps_error_D`, `mirCall_outcome_D`, `mirCall_progress_D`, `mirCall_diverges_steps_ok_D`,
`mirCall_diverges_rel_D`) lift the correspondence to whole executions, exactly as `Run.lean` does
for `inFragment`; `Witness.deinitSiblingReinit_minirust_ret_from_start`,
`Witness.deinitSiblingReinit_minirust_noUB`, `Witness.deinitSiblingCopyReinit_minirust_ret_from_start`,
`Witness.deinitSiblingRelayReinit_minirust_ret_from_start`,
`Witness.paddedDeinitSiblingReinit_minirust_ret_from_start` (cast sibling read and `BinaryOp`
re-initialization), and `Witness.deinitSiblingReinitUb_minirust_ub_from_start` instantiate
`mirCall_ret_D`, `mirCall_noUB_D`, and `mirCall_ub_D` on concrete bodies.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp

/-! ## Erasing projected `Deinit` -/

/-- A projected `Deinit(_i.proj)` becomes `PlaceMention(_i.proj)`; every other statement is
kept. -/
def eraseDeinitStmt (st : MirAst.Statement) : MirAst.Statement :=
  match st.kind with
  | .deinit ⟨i, pe :: rest⟩ => { st with kind := .placeMention ⟨i, pe :: rest⟩ }
  | _ => st

/-- `eraseDeinitStmt` on every statement of a block. -/
def eraseDeinitBlock (bb : BasicBlockData) : BasicBlockData :=
  { bb with statements := bb.statements.map eraseDeinitStmt }

/-- `body` with every projected `Deinit(p)` replaced by `PlaceMention(p)`. -/
def eraseDeinit (body : CapturedMir) : CapturedMir :=
  { body with basicBlocks := body.basicBlocks.map eraseDeinitBlock }

/-- Whether a statement is a projected `Deinit`. -/
def isProjDeinit (st : MirAst.Statement) : Bool :=
  match st.kind with
  | .deinit ⟨_, _ :: _⟩ => true
  | _ => false

/-- `eraseDeinitStmt` keeps every statement other than a projected `Deinit`. -/
theorem eraseDeinitStmt_of_not {st : MirAst.Statement} (h : isProjDeinit st = false) :
    eraseDeinitStmt st = st := by
  obtain ⟨kind, span⟩ := st
  cases kind with
  | deinit p =>
    obtain ⟨i, proj⟩ := p
    cases proj with
    | nil => rfl
    | cons _ _ => simp [isProjDeinit] at h
  | _ => rfl

@[simp] theorem eraseDeinit_localDecls (body : CapturedMir) :
    (eraseDeinit body).localDecls = body.localDecls := rfl

@[simp] theorem eraseDeinit_layouts (body : CapturedMir) :
    (eraseDeinit body).layouts = body.layouts := rfl

@[simp] theorem eraseDeinit_argCount (body : CapturedMir) :
    (eraseDeinit body).argCount = body.argCount := rfl

@[simp] theorem eraseDeinit_phase (body : CapturedMir) :
    (eraseDeinit body).phase = body.phase := rfl

@[simp] theorem eraseDeinit_length (body : CapturedMir) :
    (eraseDeinit body).basicBlocks.length = body.basicBlocks.length := by
  simp [eraseDeinit]

theorem eraseDeinit_block {body : CapturedMir} {blk : Nat} {bb : BasicBlockData}
    (h : body.basicBlocks[blk]? = some bb) :
    (eraseDeinit body).basicBlocks[blk]? = some (eraseDeinitBlock bb) := by
  simp [eraseDeinit, h]

theorem eraseDeinitBlock_stmt {bb : BasicBlockData} {i : Nat} {st : MirAst.Statement}
    (h : bb.statements[i]? = some st) :
    (eraseDeinitBlock bb).statements[i]? = some (eraseDeinitStmt st) := by
  simp [eraseDeinitBlock, h]

@[simp] theorem eraseDeinitBlock_length (bb : BasicBlockData) :
    (eraseDeinitBlock bb).statements.length = bb.statements.length := by
  simp [eraseDeinitBlock]

@[simp] theorem eraseDeinitBlock_terminator (bb : BasicBlockData) :
    (eraseDeinitBlock bb).terminator = bb.terminator := rfl

/-! ## Holes -/

/-- Byte offset and size of field path `projs` of the `TupleSpec` local `_t`. -/
def holeRange (body : CapturedMir) (t : Nat) (projs : List ProjectionElem) : Option (Nat × Nat) :=
  match body.localDecls[t]? with
  | none => none
  | some d =>
    match tupleTypeOf body.layouts d.ty with
    | none => none
    | some (fields, size, align) =>
      match resolveFieldPath body.layouts (.tuple fields size align) projs with
      | none => none
      | some (off, leaf) => some (off, leaf.size)

/-- The open hole (a projected `Deinit` not yet re-initialized) after statement `st`: a
projected `Deinit(_t.projs)` opens the hole `(t, projs)`, and an assignment to a place of `_t`
with the hole's byte range closes it. -/
def holeAfter (body : CapturedMir) : Option (Nat × List ProjectionElem) → MirAst.Statement →
    Option (Nat × List ProjectionElem)
  | none, st =>
    match st.kind with
    | .deinit ⟨t, pe :: rest⟩ => some (t, pe :: rest)
    | _ => none
  | some (t, ps), st =>
    match st.kind with
    | .assign ⟨t', ps'⟩ _ =>
      if t' = t ∧ holeRange body t' ps' = holeRange body t ps then none else some (t, ps)
    | _ => some (t, ps)

/-- The open hole before statement `stmt` of block `blk`. -/
def holeAt (body : CapturedMir) (blk stmt : Nat) : Option (Nat × List ProjectionElem) :=
  match body.basicBlocks[blk]? with
  | some bb => (bb.statements.take stmt).foldl (holeAfter body) none
  | none => none

/-- Admissible targets of a projected `Deinit(_t.projs)`: a `TupleSpec` local whose field
path resolves to a scalar leaf of positive size. -/
def deinitTargetOk (body : CapturedMir) (t : Nat) (projs : List ProjectionElem) : Bool :=
  match body.localDecls[t]? with
  | none => false
  | some d =>
    match tupleTypeOf body.layouts d.ty with
    | none => false
    | some (fields, size, align) =>
      match resolveFieldPath body.layouts (.tuple fields size align) projs with
      | some (_, .scalar it) => decide (0 < it.size.bytes)
      | _ => false

/-- A sibling read `_r = copy _t.projs'` while `_t.projs` is a hole: `_r` is an integer
local other than `_t`, and `projs'` resolves to a scalar leaf of `_r`'s integer type whose
bytes are disjoint from the hole. -/
def siblingReadOk (body : CapturedMir) (t r : Nat) (projs projs' : List ProjectionElem) : Bool :=
  decide (r ≠ t) &&
  match body.localDecls[r]?, body.localDecls[t]? with
  | some dr, some d =>
    match intTypeOf dr.ty, tupleTypeOf body.layouts d.ty with
    | some it, some (fields, size, align) =>
      match resolveFieldPath body.layouts (.tuple fields size align) projs,
            resolveFieldPath body.layouts (.tuple fields size align) projs' with
      | some (off, leaf), some (off', .scalar it') =>
        decide (it' = it) && (decide (off' + it'.size.bytes ≤ off) || decide (off + leaf.size ≤ off'))
      | _, _ => false
    | _, _ => false
  | _, _ => false

/-- A re-initialization `_t.projs = const c`: `projs` resolves to a scalar leaf of positive
size and `c` is a non-`bool` integer constant of the leaf's type with an in-range bit pattern
(so that `translateOperand` lowers it to `Constant::Int`). -/
def reinitOk (body : CapturedMir) (t : Nat) (projs : List ProjectionElem) (c : ConstOperand) :
    Bool :=
  match body.localDecls[t]? with
  | none => false
  | some d =>
    match tupleTypeOf body.layouts d.ty with
    | none => false
    | some (fields, size, align) =>
      match resolveFieldPath body.layouts (.tuple fields size align) projs with
      | some (_, .scalar it) =>
        decide (0 < it.size.bytes) && !isBoolTy c.ty &&
        match c.val, intTypeOf c.ty with
        | .scalar (.int ⟨bits, sz⟩), some it' =>
          decide (it' = it) && decide (sz = it.size.bytes) && decide (bits < 2 ^ (8 * sz))
        | _, _ => false
      | _ => false

/-- A re-initialization `_t.projs = copy _r` from a distinct integer local `_r`: `r ≠ t`, `_r` is
an integer local of type `it`, and `projs` resolves in `_t`'s `TupleSpec` to a scalar leaf of the
same integer type `it` with positive size. -/
def reinitCopyOk (body : CapturedMir) (t r : Nat) (projs : List ProjectionElem) : Bool :=
  decide (r ≠ t) &&
  match body.localDecls[r]?, body.localDecls[t]? with
  | some dr, some d =>
    match intTypeOf dr.ty, tupleTypeOf body.layouts d.ty with
    | some it, some (fields, size, align) =>
      match resolveFieldPath body.layouts (.tuple fields size align) projs with
      | some (_, .scalar it') => decide (it' = it) && decide (0 < it.size.bytes)
      | _ => false
    | _, _ => false
  | _, _ => false

/-- A hole-independent scalar local copy `_r = copy _q` while `_t.projs` is a hole: `r ≠ t`,
`q ≠ t`, `r ≠ q`, `_r` and `_q` are integer locals of the same integer type `it` with positive
byte size and valid alignment (`goodAlignBytes it.size.bytes = true`), and `_t` is a `TupleSpec`
local. -/
def localCopyWindowOk (body : CapturedMir) (t r q : Nat) : Bool :=
  decide (r ≠ t) && decide (q ≠ t) && decide (r ≠ q) &&
  match body.localDecls[r]?, body.localDecls[q]?, body.localDecls[t]? with
  | some dr, some dq, some d =>
    match intTypeOf dr.ty, intTypeOf dq.ty, tupleTypeOf body.layouts d.ty with
    | some it, some it', some _ =>
      decide (it' = it) && decide (0 < it.size.bytes) && goodAlignBytes it.size.bytes
    | _, _, _ => false
  | _, _, _ => false

/-- A sibling read through an integer cast `_r = Cast(IntToInt, copy _t.projs', castTy)` while
`_t.projs` is a hole: `_r` is an integer local other than `_t` whose integer type `it` is the cast's
target type `castTy` (with a valid size and alignment), the operand translates as an integer operand
(`operandType` is `Int`), and `projs'` resolves in `_t`'s `TupleSpec` to a scalar leaf of some
integer type `it'` (the cast's source) whose bytes are disjoint from the hole. -/
def castSiblingReadOk (body : CapturedMir) (t r : Nat) (projs projs' : List ProjectionElem)
    (castTy : MirAst.Ty) : Bool :=
  decide (r ≠ t) &&
  (match operandType body.layouts body.localDecls (.copy ⟨t, projs'⟩) with
   | some (.Int _) => true
   | _ => false) &&
  match body.localDecls[r]?, body.localDecls[t]? with
  | some dr, some d =>
    match intTypeOf dr.ty, intTypeOf castTy, tupleTypeOf body.layouts d.ty with
    | some it, some ct, some (fields, size, align) =>
      decide (ct = it) && goodAlignBytes it.size.bytes &&
      match resolveFieldPath body.layouts (.tuple fields size align) projs,
            resolveFieldPath body.layouts (.tuple fields size align) projs' with
      | some (off, leaf), some (off', .scalar it') =>
        decide (off' + it'.size.bytes ≤ off) || decide (off + leaf.size ≤ off')
      | _, _ => false
    | _, _, _ => false
  | _, _ => false

/-- A re-initialization `_t.projs = BinaryOp(op, copy _q, const c)` of the hole by an integer
arithmetic or bitwise operation (`translateRelOp op = none`, `translateBinOp op = some _`) of a
hole-independent integer local `_q` (`q ≠ t`) and a constant: `projs` resolves in `_t`'s `TupleSpec`
to a scalar leaf of positive size whose integer type `it` is `_q`'s type, and `c` is a non-`bool`
integer constant of type `it` with an in-range bit pattern (so that `translateOperand` lowers it to
`Constant::Int`). -/
def reinitBinOpOk (body : CapturedMir) (t q : Nat) (projs : List ProjectionElem)
    (op : MirAst.BinOp) (c : ConstOperand) : Bool :=
  decide (q ≠ t) && (translateRelOp op).isNone && (translateBinOp op).isSome &&
  match body.localDecls[q]?, body.localDecls[t]? with
  | some dq, some d =>
    match intTypeOf dq.ty, tupleTypeOf body.layouts d.ty with
    | some it, some (fields, size, align) =>
      match resolveFieldPath body.layouts (.tuple fields size align) projs with
      | some (_, .scalar it') =>
        decide (it' = it) && decide (0 < it.size.bytes) && !isBoolTy c.ty &&
        match c.val, intTypeOf c.ty with
        | .scalar (.int ⟨bits, sz⟩), some ic =>
          decide (ic = it) && decide (sz = it.size.bytes) && decide (bits < 2 ^ (8 * sz))
        | _, _ => false
      | _ => false
    | _, _ => false
  | _, _ => false

/-- A hole-independent integer binary operation `_r = BinaryOp(op, copy _q, const c)` into a
scalar local `_r` while `_t.projs` is a hole: `r ≠ t`, `q ≠ t`, `r ≠ q`, `_r` and `_q` are integer
locals of the same integer type `it` with positive byte size and valid alignment
(`goodAlignBytes it.size.bytes = true`), `op` is a non-relational integer binary operation, `c` is
a non-`bool` integer constant of type `it` with an in-range bit pattern, and `_t` is a `TupleSpec`
local. -/
def binOpWindowOk (body : CapturedMir) (t r q : Nat) (op : MirAst.BinOp) (c : ConstOperand) : Bool :=
  decide (r ≠ t) && decide (q ≠ t) && decide (r ≠ q) &&
  (translateRelOp op).isNone && (translateBinOp op).isSome &&
  match body.localDecls[r]?, body.localDecls[q]?, body.localDecls[t]? with
  | some dr, some dq, some d =>
    match intTypeOf dr.ty, intTypeOf dq.ty, tupleTypeOf body.layouts d.ty with
    | some it, some it', some _ =>
      decide (it' = it) && decide (0 < it.size.bytes) && goodAlignBytes it.size.bytes &&
      !isBoolTy c.ty &&
      match c.val, intTypeOf c.ty with
      | .scalar (.int ⟨bits, sz⟩), some ic =>
        decide (ic = it) && decide (sz = it.size.bytes) && decide (bits < 2 ^ (8 * sz))
      | _, _ => false
    | _, _, _ => false
  | _, _, _ => false

/-- The statements admitted before statement `idx` of block `blk` when the hole state is
`hole`: with no hole, any statement (a projected `Deinit` must target an admissible,
not-moved-out `TupleSpec` local); with a hole on `_t.projs`, only a disjoint sibling read
`_r = copy _t.projs'` (possibly through an integer cast, `_r = Cast(IntToInt, copy _t.projs', it)`),
a hole-independent scalar local copy `_r = copy _q`, a hole-independent scalar binary operation
`_r = BinaryOp(op, copy _q, const c)`, a constant re-initialization
`_t.projs = const c`, a local-copy re-initialization `_t.projs = copy _r`, or a binary-operation
re-initialization `_t.projs = BinaryOp(op, copy _q, const c)`. -/
def windowStmtOk (body : CapturedMir) (blk idx : Nat) :
    Option (Nat × List ProjectionElem) → MirAst.Statement → Bool
  | none, st =>
    match st.kind with
    | .deinit ⟨t, pe :: rest⟩ =>
      deinitTargetOk body t (pe :: rest) &&
        !(movedBefore (eraseDeinit body) blk idx).contains t
    | _ => true
  | some (t, ps), st =>
    match st.kind with
    | .assign ⟨r, []⟩ (.use (.copy ⟨q, []⟩)) => localCopyWindowOk body t r q
    | .assign ⟨r, []⟩ (.use (.copy ⟨t', qp :: qps⟩)) =>
      decide (t' = t) && siblingReadOk body t r ps (qp :: qps)
    | .assign ⟨t', rp :: rps⟩ (.use (.copy ⟨r, []⟩)) =>
      decide (t' = t) && reinitCopyOk body t r (rp :: rps) &&
        decide (holeRange body t (rp :: rps) = holeRange body t ps)
    | .assign ⟨t', ps'⟩ (.use (.constant c)) =>
      decide (t' = t) && reinitOk body t ps' c &&
        decide (holeRange body t ps' = holeRange body t ps)
    | .assign ⟨r, []⟩ (.cast .intToInt (.copy ⟨t', qp :: qps⟩) castTy) =>
      decide (t' = t) && castSiblingReadOk body t r ps (qp :: qps) castTy
    | .assign ⟨r, []⟩ (.binaryOp op (.copy ⟨q, []⟩) (.constant c)) =>
      binOpWindowOk body t r q op c
    | .assign ⟨t', rp :: rps⟩ (.binaryOp op (.copy ⟨q, []⟩) (.constant c)) =>
      decide (t' = t) && reinitBinOpOk body t q (rp :: rps) op c &&
        decide (holeRange body t (rp :: rps) = holeRange body t ps)
    | _ => false

/-- Whether the statements `sts` (starting at index `idx` with hole state `hole`) satisfy
`windowStmtOk` and close every hole before the terminator. -/
def blockWindowOk (body : CapturedMir) (blk : Nat) :
    List MirAst.Statement → Nat → Option (Nat × List ProjectionElem) → Bool
  | [], _, hole => hole.isNone
  | st :: sts, idx, hole =>
    windowStmtOk body blk idx hole st &&
      blockWindowOk body blk sts (idx + 1) (holeAfter body hole st)

/-- Every block satisfies `blockWindowOk` from an empty hole state. -/
def deinitWindowOk (body : CapturedMir) : Bool :=
  (List.range body.basicBlocks.length).all fun blk =>
    match body.basicBlocks[blk]? with
    | some bb => blockWindowOk body blk bb.statements 0 none
    | none => true

/-- The single-body fragment with projected `Deinit`: erasing every projected `Deinit` gives
an `inFragment` body, and every projected `Deinit` opens a hole that only disjoint sibling
reads cross before its re-initialization by a constant, within its block. -/
def inFragmentD (body : CapturedMir) : Bool :=
  inFragment (eraseDeinit body) && deinitWindowOk body


/-! ## Facts about the fragment and the erasure -/

/-- The two conjuncts of `inFragmentD`. -/
theorem inFragmentD_spec {body : CapturedMir} (h : inFragmentD body = true) :
    inFragment (eraseDeinit body) = true ∧ deinitWindowOk body = true := by
  simpa [inFragmentD] using h

/-- No hole is open at the entry of a block. -/
theorem holeAt_zero (body : CapturedMir) (blk : Nat) : holeAt body blk 0 = none := by
  unfold holeAt
  split <;> simp

/-- `holeAt` after statement `i` is `holeAfter` of the hole before it. -/
theorem holeAt_succ {body : CapturedMir} {blk i : Nat} {bb : BasicBlockData} {st : MirAst.Statement}
    (hbb : body.basicBlocks[blk]? = some bb) (hst : bb.statements[i]? = some st) :
    holeAt body blk (i + 1) = holeAfter body (holeAt body blk i) st := by
  simp only [holeAt, hbb]
  rw [List.take_add_one, hst, Option.toList_some, List.foldl_append]
  rfl

/-- `blockWindowOk` checks `windowStmtOk` at every statement against the hole computed by the
forward scan, and leaves no hole open at the end. -/
theorem blockWindowOk_spec {body : CapturedMir} {blk : Nat} :
    ∀ (sts : List MirAst.Statement) (n : Nat) (h : Option (Nat × List ProjectionElem)),
      blockWindowOk body blk sts n h = true →
      (∀ (j : Nat) (st : MirAst.Statement), sts[j]? = some st →
        windowStmtOk body blk (n + j) ((sts.take j).foldl (holeAfter body) h) st = true) ∧
      sts.foldl (holeAfter body) h = none
  | [], n, h, hok => by
    simp only [blockWindowOk, Option.isNone_iff_eq_none] at hok
    subst hok
    exact ⟨fun j st hj => by simp at hj, rfl⟩
  | st0 :: sts, n, h, hok => by
    simp only [blockWindowOk, Bool.and_eq_true] at hok
    obtain ⟨hst0, hrest⟩ := hok
    obtain ⟨ih1, ih2⟩ := blockWindowOk_spec sts (n + 1) (holeAfter body h st0) hrest
    refine ⟨fun j st hj => ?_, by simpa using ih2⟩
    cases j with
    | zero =>
      simp at hj
      subst hj
      simpa using hst0
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      have := ih1 j st hj
      simp only [List.take_succ_cons, List.foldl_cons]
      rw [show n + (j + 1) = n + 1 + j by omega]
      exact this

/-- `deinitWindowOk` gives `windowStmtOk` at every statement against `holeAt`, and no hole
open before the terminator. -/
theorem deinitWindowOk_spec {body : CapturedMir} (h : deinitWindowOk body = true)
    {blk : Nat} {bb : BasicBlockData} (hbb : body.basicBlocks[blk]? = some bb) :
    (∀ (i : Nat) (st : MirAst.Statement), bb.statements[i]? = some st →
      windowStmtOk body blk i (holeAt body blk i) st = true) ∧
    holeAt body blk bb.statements.length = none := by
  have hblk : blk < body.basicBlocks.length := (List.getElem?_eq_some_iff.mp hbb).1
  have hb := (List.all_eq_true.mp h) blk (List.mem_range.mpr hblk)
  simp only [hbb] at hb
  obtain ⟨h1, h2⟩ := blockWindowOk_spec bb.statements 0 none hb
  refine ⟨fun i st hst => ?_, ?_⟩
  · have := h1 i st hst
    simp only [Nat.zero_add] at this
    simpa [holeAt, hbb] using this
  · simpa [holeAt, hbb] using h2

/-- A statement other than a projected `Deinit` steps alike in `body` and `eraseDeinit body`. -/
theorem stepMirFn_eraseDeinit_stmt {body : CapturedMir} {s : MachineState} {bb : BasicBlockData}
    {st : MirAst.Statement} (hcallee : s.memory.activeCallee = none)
    (hphase : body.phase = .runtimePostCleanup)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some st) (hnd : isProjDeinit st = false) :
    stepMirFn body s = stepMirFn (eraseDeinit body) s := by
  rw [stepMirFn_stmt body s bb st hcallee hphase hbb hst,
    stepMirFn_stmt (eraseDeinit body) s (eraseDeinitBlock bb) (eraseDeinitStmt st) hcallee hphase
      (eraseDeinit_block hbb) (eraseDeinitBlock_stmt hst), eraseDeinitStmt_of_not hnd]
  rfl

/-- A fragment terminator steps alike in `body` and `eraseDeinit body`. -/
theorem stepMirFn_eraseDeinit_term {body : CapturedMir} {s : MachineState} {bb : BasicBlockData}
    (hcallee : s.memory.activeCallee = none) (hphase : body.phase = .runtimePostCleanup)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hlen : s.frame.stmtIdx = bb.statements.length)
    (hterm : terminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator = true) :
    stepMirFn body s = stepMirFn (eraseDeinit body) s := by
  rw [stepMirFn_term body s bb hcallee hphase hbb hlen,
    stepMirFn_term (eraseDeinit body) s (eraseDeinitBlock bb) hcallee hphase
      (eraseDeinit_block hbb) (by simpa using hlen)]
  simp only [eraseDeinitBlock_terminator]
  cases hT : bb.terminator with
  | mk tk tspan =>
    rw [hT] at hterm
    cases tk <;> simp_all [terminatorOk, MirSemantics.evalTerminator]

/-- `translateFn body` has the local declarations of `eraseDeinit body`. -/
theorem fnLocalsSpec_eraseDeinit {body : CapturedMir} {f : Gen.Function}
    (hf : translateFn body = some f) : FnLocalsSpec (eraseDeinit body) f := by
  have h := FnLocalsSpec.of_translateFn hf
  exact h

/-- The current-block hypothesis of `step_correspondence_NF` for `eraseDeinit body` and
`translateFn body`, away from projected `Deinit`s. -/
theorem blk_eraseDeinit {body : CapturedMir} {f : Gen.Function} (hf : translateFn body = some f)
    {blk i : Nat} {bb : BasicBlockData} (hbb : body.basicBlocks[blk]? = some bb)
    (hnd : ∀ st, bb.statements[i]? = some st → isProjDeinit st = false) :
    ∀ bb', (eraseDeinit body).basicBlocks[blk]? = some bb' →
      ∃ tb, mapGet f.blocks (bbName blk) = some tb ∧
        tb.statements.length = bb'.statements.length ∧
        (∀ st, bb'.statements[i]? = some st →
          ∃ st', translateStatement (eraseDeinit body).localDecls st (eraseDeinit body).layouts =
              some st' ∧ tb.statements[i]? = some st') ∧
        translateTerminator (eraseDeinit body).layouts (eraseDeinit body).localDecls bb'.terminator =
          some tb.terminator := by
  intro bb' hbb'
  rw [eraseDeinit_block hbb] at hbb'
  cases hbb'
  obtain ⟨tb, htb, hgetb⟩ := (translateFn_spec body f hf).2.2 _ bb hbb
  obtain ⟨hlen, hstspec, htermspec⟩ := translateBlock_spec _ _ bb tb htb
  refine ⟨tb, hgetb, by simpa using hlen, fun st hst => ?_, by simpa using htermspec⟩
  simp only [eraseDeinitBlock, List.getElem?_map, Option.map_eq_some_iff] at hst
  obtain ⟨st0, hst0, rfl⟩ := hst
  rw [eraseDeinitStmt_of_not (hnd st0 hst0)]
  exact hstspec i st0 hst0


/-- `statementOk` rejects every projected `Deinit`. -/
theorem isProjDeinit_false_of_statementOk {decls : List LocalDecl} {layouts : Layout.LayoutTable}
    {st : MirAst.Statement} (h : statementOk decls st layouts = true) : isProjDeinit st = false := by
  obtain ⟨kind, span⟩ := st
  cases kind with
  | deinit p =>
    obtain ⟨i, proj⟩ := p
    cases proj with
    | nil => rfl
    | cons _ _ => simp [statementOk] at h
  | _ => rfl

/-- Without projected `Deinit`, no hole ever opens and every block passes the window check. -/
theorem blockWindowOk_of_noProjDeinit {body : CapturedMir} {blk : Nat} :
    ∀ (sts : List MirAst.Statement) (n : Nat), (∀ st ∈ sts, isProjDeinit st = false) →
      blockWindowOk body blk sts n none = true
  | [], _, _ => rfl
  | st :: sts, n, h => by
    have hst := h st (List.mem_cons_self ..)
    have hrest := blockWindowOk_of_noProjDeinit (body := body) (blk := blk) sts (n + 1)
      (fun st' hst' => h st' (List.mem_cons_of_mem _ hst'))
    obtain ⟨kind, span⟩ := st
    have hwin : windowStmtOk body blk n none ⟨kind, span⟩ = true := by
      cases kind with
      | deinit p =>
        obtain ⟨i, proj⟩ := p
        cases proj with
        | nil => rfl
        | cons _ _ => simp [isProjDeinit] at hst
      | _ => rfl
    have hafter : holeAfter body none ⟨kind, span⟩ = none := by
      cases kind with
      | deinit p =>
        obtain ⟨i, proj⟩ := p
        cases proj with
        | nil => rfl
        | cons _ _ => simp [isProjDeinit] at hst
      | _ => rfl
    simp only [blockWindowOk, hwin, hafter, hrest, Bool.and_self]

/-- **`inFragmentD` extends `inFragment`.** A body without projected `Deinit` is its own
erasure, and no hole ever opens in it. -/
theorem inFragment_implies_inFragmentD {body : CapturedMir} (h : inFragment body = true) :
    inFragmentD body = true := by
  obtain ⟨_, _, _, _, _, _, hbbs, _, _, _⟩ := inFragment_spec body h
  have hnd : ∀ bb ∈ body.basicBlocks, ∀ st ∈ bb.statements, isProjDeinit st = false :=
    fun bb hbb st hst => isProjDeinit_false_of_statementOk ((hbbs bb hbb).2.1 st hst)
  have herase : eraseDeinit body = body := by
    have hblocks : body.basicBlocks.map eraseDeinitBlock = body.basicBlocks := by
      conv => rhs; rw [← List.map_id body.basicBlocks]
      refine List.map_congr_left fun bb hbb => ?_
      have hs : bb.statements.map eraseDeinitStmt = bb.statements := by
        conv => rhs; rw [← List.map_id bb.statements]
        exact List.map_congr_left fun st hst => eraseDeinitStmt_of_not (hnd bb hbb st hst)
      simp [eraseDeinitBlock, hs]
    simp [eraseDeinit, hblocks]
  simp only [inFragmentD, herase, h, Bool.true_and]
  unfold deinitWindowOk
  refine List.all_eq_true.mpr fun blk _ => ?_
  cases hbb : body.basicBlocks[blk]? with
  | none => rfl
  | some bb =>
    exact blockWindowOk_of_noProjDeinit bb.statements 0
      (fun st hst => hnd bb (List.mem_of_getElem? hbb) st hst)

/-! ## The relation -/

/-- `m` with its allocations replaced by `A`. -/
def setAllocs (m : Mach) (A : List Gen.Allocation) : Mach :=
  { m with mem := { m.mem with memory := { m.mem.memory with allocations := A } } }

@[simp] theorem setAllocs_threads (m : Mach) (A : List Gen.Allocation) :
    (setAllocs m A).threads = m.threads := rfl

@[simp] theorem setAllocs_active (m : Mach) (A : List Gen.Allocation) :
    (setAllocs m A).active_thread = m.active_thread := rfl

@[simp] theorem setAllocs_allocations (m : Mach) (A : List Gen.Allocation) :
    (setAllocs m A).mem.memory.allocations = A := rfl

/-- How the MiniRust machine `m` differs from a hole-free machine `m0` while the field
`_t.ps` is a hole: same threads and active thread, and the same allocations except that the
hole's bytes `[off, off + sz)` of `_t`'s allocation are `Uninit`. -/
def HoleRel (body : CapturedMir) (f : Gen.Function) (ctx : Ctx) (blk stmt t : Nat)
    (ps : List ProjectionElem) (m0 m : Mach) : Prop :=
  ∃ (lm : Map Gen.LocalName Ptr) (p : Ptr) (k : Nat) (a : Gen.Allocation) (off sz : Nat),
    m0.threads = [thread1 ctx [ctx.caller, calleeFrameL f ctx lm blk stmt]] ∧
    mapGet lm (localName t) = some p ∧ p.provenance = some (⟨(k : Int)⟩, ()) ∧
    m0.mem.memory.allocations[k]? = some a ∧
    holeRange body t ps = some (off, sz) ∧
    m.threads = m0.threads ∧ m.active_thread = m0.active_thread ∧
    m.mem.memory.allocations = m0.mem.memory.allocations.set k
      { a with data := spliceAt a.data off (List.replicate sz .Uninit) }

/-- The state relation for `inFragmentD` bodies: either the plain `StateRelN` of the erased
body, or, while the hole `_t.ps` of `holeAt` is open, `StateRelN` of the erased body with a
hole-free machine `m0` from which `m` differs only by the hole (`HoleRel`). -/
def StateRelD (body : CapturedMir) (f : Gen.Function) (ctx : Ctx) (s : MachineState) (m : Mach) :
    Prop :=
  StateRelN (eraseDeinit body) f ctx s m ∨
  ∃ (t : Nat) (ps : List ProjectionElem) (m0 : Mach),
    holeAt body s.frame.blockIdx s.frame.stmtIdx = some (t, ps) ∧
    StateRelN (eraseDeinit body) f ctx s m0 ∧
    HoleRel body f ctx s.frame.blockIdx s.frame.stmtIdx t ps m0 m

/-- One Anneal step and one MiniRust step for `inFragmentD` bodies (`StepRelN` with
`StateRelD`). -/
def StepRelD (body : CapturedMir) (f : Gen.Function) (ctx : Ctx) (s : MachineState)
    (a : MirStepNode) (r : Interp Mach) : Prop :=
  match a with
  | .tau (.running s') => ∃ m', r = .ok m' ∧ StateRelD body f ctx s' m'
  | .vis (.inr (.inl (.emit _))) k =>
    ∃ s' m', k PUnit.unit = .running s' ∧ r = .ok m' ∧ StateRelD body f ctx s' m'
  | .ret (.normal (v, _)) => ∃ m', r = .ok m' ∧ ReturnRel body ctx s v m'
  | .vis (.inl (.fail .ub)) _ => ∃ msg, r = .error (.ub msg)
  | _ => False

/-- `StateRelN` depends on the MiniRust machine only through its threads, active thread, and
allocations. -/
theorem StateRelN.of_obs {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s : MachineState}
    {m m' : Mach} (h : StateRelN body f ctx s m) (hthr : m'.threads = m.threads)
    (hact : m'.active_thread = m.active_thread)
    (hal : m'.mem.memory.allocations = m.mem.memory.allocations) :
    StateRelN body f ctx s m' := by
  obtain ⟨view, lm, hrel, hthr0, hlo, hns, hbo⟩ := h
  obtain ⟨lm', hthr1, hlo1⟩ := hrel.frame
  refine ⟨view, lm, { hrel with frame := ⟨lm', hthr ▸ hthr1, hal ▸ hlo1⟩, active := hact ▸ hrel.active },
    hthr ▸ hthr0, hal ▸ hlo, hns, hbo⟩

/-- A `StepRelN` of the erased body is a `StepRelD`. -/
theorem StepRelN.toStepRelD {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s : MachineState}
    {a : MirStepNode} {r : Interp Mach} (h : StepRelN (eraseDeinit body) f ctx s a r) :
    StepRelD body f ctx s a r := by
  unfold StepRelN at h
  unfold StepRelD
  split at h
  · obtain ⟨m', hr, h'⟩ := h; exact ⟨m', hr, .inl h'⟩
  · obtain ⟨s', m', hk, hr, h'⟩ := h; exact ⟨s', m', hk, hr, .inl h'⟩
  · exact h
  · exact h
  · exact h.elim


/-! ## The projected `Deinit` step -/

/-- **Projected `Deinit` step.** At a projected `Deinit(_t.f1...fk)` of a `TupleSpec` local
(no hole open, `_t` not moved out), Anneal advances with unchanged locals while MiniRust stores
`Uninit` over the field's bytes; the new states are related through the hole `_t.f1...fk`. -/
theorem step_projDeinit {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment (eraseDeinit body) = true) (hwin : deinitWindowOk body = true)
    (hf : translateFn body = some f) {ctx : Ctx} {s : MachineState} {m : Mach}
    (hrelN : StateRelN (eraseDeinit body) f ctx s m) {bb : BasicBlockData} {st : MirAst.Statement}
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some st) (hpd : isProjDeinit st = true) :
    StepRelD body f ctx s (stepMirFn body s) (Interp.step m) := by
  obtain ⟨view, lm, hrel, hthr, hlo, hns, hbo⟩ := hrelN
  obtain ⟨hphase, _, _, _, hdeclsOk, _, _, _, _, _⟩ := inFragment_spec _ hfrag
  have hlt : s.frame.stmtIdx < bb.statements.length := (List.getElem?_eq_some_iff.mp hst).1
  have hwst := (deinitWindowOk_spec hwin hbb).1 _ _ hst
  obtain ⟨kind, span⟩ := st
  cases kind with
  | deinit p =>
    obtain ⟨t, proj⟩ := p
    cases proj with
    | nil => simp [isProjDeinit] at hpd
    | cons pe rest =>
      cases hh : holeAt body s.frame.blockIdx s.frame.stmtIdx with
      | some hole =>
        obtain ⟨t', ps⟩ := hole
        simp [hh, windowStmtOk] at hwst
      | none =>
        simp only [hh, windowStmtOk, Bool.and_eq_true, Bool.not_eq_true'] at hwst
        obtain ⟨htgt, hnm⟩ := hwst
        have hnm' : t ∉ movedBefore (eraseDeinit body) s.frame.blockIdx s.frame.stmtIdx := by
          simpa using hnm
        unfold deinitTargetOk at htgt
        cases hd : body.localDecls[t]? with
        | none => simp [hd] at htgt
        | some d =>
          cases ht : tupleTypeOf body.layouts d.ty with
          | none => simp [hd, ht] at htgt
          | some trip =>
            obtain ⟨fields, size, align⟩ := trip
            cases hres : resolveFieldPath body.layouts (.tuple fields size align) (pe :: rest) with
            | none => simp [hd, ht, hres] at htgt
            | some pr =>
              obtain ⟨off, leaf⟩ := pr
              cases leaf with
              | tuple _ _ _ => simp [hd, ht, hres] at htgt
              | scalar it =>
                simp only [hd, ht, hres, decide_eq_true_eq] at htgt
                cases pe with
                | field idx fTy =>
                  have ht_lt : t < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
                  obtain ⟨slot, hsV⟩ : ∃ slot, view[t]? = some slot :=
                    ⟨_, List.getElem?_eq_getElem (by rw [hlo.nlocals]; exact ht_lt)⟩
                  obtain ⟨⟨rootVal, rfl⟩, _⟩ := hns t d slot hd hsV
                    (scalarTypeOf_none_of_tupleTypeOf ht) (isPtrTy_false_of_tupleTypeOf ht)
                  have hsA : s.frame.locals[t]? = some (.init rootVal) :=
                    (hrel.stale.agree hnm').trans hsV
                  have hslotsA : SlotsOk body.layouts body.localDecls s.frame.locals :=
                    hrel.stale.slots hlo.slots
                  -- Anneal: the projected `Deinit` keeps the locals.
                  rw [stepMirFn_stmt body s bb _ hrel.activeCallee hphase hbb hst,
                    DeinitBridge.evalStmt_deinit_field s body.localDecls t d fields size align off
                      (.scalar it) (.field idx fTy) rest span rootVal hd ht hslotsA hsA hres]
                  -- MiniRust: `Deinit` stores `Uninit` over the field's bytes.
                  obtain ⟨tb, htb, hgetb⟩ := (translateFn_spec body f hf).2.2 _ bb hbb
                  obtain ⟨hlen, hstspec, _⟩ := translateBlock_spec _ _ bb tb htb
                  obtain ⟨st', hst', htst⟩ := hstspec _ _ hst
                  obtain ⟨pe', hpe', rfl⟩ : ∃ pe', translatePlace body.localDecls
                      ⟨t, .field idx fTy :: rest⟩ = some pe' ∧ st' = .Deinit pe' := by
                    simp only [translateStatement] at hst'
                    cases hp : translatePlace body.localDecls ⟨t, .field idx fTy :: rest⟩ with
                    | none => simp [hp] at hst'
                    | some pe' =>
                      simp only [hp, Option.map_some, Option.some.injEq] at hst'
                      exact ⟨pe', rfl, hst'.symm⟩
                  have hshape : Shape m (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows)
                      [(ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows).caller,
                        calleeFrameL f (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows) lm
                          s.frame.blockIdx s.frame.stmtIdx]
                      m.mem.memory.allocations := ⟨hthr, hrel.active, rfl⟩
                  have hframe : FrameOk (eraseDeinit body) f
                      (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows) view lm (resetPick m)
                      s.frame.blockIdx s.frame.stmtIdx :=
                    ⟨fnLocalsSpec_eraseDeinit hf, resetPick_shape hshape, hlo, hdeclsOk, hns⟩
                  obtain ⟨deinitVal, ptr, k, hw, hptr, hpk, hev⟩ :=
                    DeinitBridge.evalStatement_deinit_fieldPath hframe t idx fTy rest d fields size
                      align off (.scalar it) pe' rootVal hd ht hsV hpe' hres
                      (by simpa [TupleSpec.size] using htgt)
                  have hra : (resetPick m).mem.memory.allocations = m.mem.memory.allocations := rfl
                  rw [hra] at hev
                  have h3 := withMem_shape (resetPick_shape hshape)
                    (allocs' := m.mem.memory.allocations.set k
                      (stackAlloc ptr.addr (itOf d body.layouts)
                        ((TupleSpec.tuple fields size align).encodeVal deinitVal)))
                    ⟨.Store, .None, (offsetPtr ptr off).addr, ⟨(TupleSpec.scalar it).size⟩⟩
                  obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3
                  have hne : ((s.frame.stmtIdx : Nat) : Int) ≠ (tb.statements.length : Int) := by
                    rw [hlen]; omega
                  have hstep : Interp.step m = .ok m4 := by
                    rw [step_callee hshape tb hgetb]
                    simp [hne, listIndex_nat _ _ _ htst, hev, hm4, check_after h4]
                  -- The hole-free machine and the hole.
                  obtain ⟨k', hpk', _, _, _, _, hA⟩ := hlo.storage_nonptr t d (.init rootVal) ptr hd
                    hsV hptr (isPtrTy_false_of_tupleTypeOf ht)
                  simp only [eraseDeinit_layouts] at hA
                  rw [declSlotData_of_tupleSpec ht] at hA
                  have hkk : k' = k := by
                    rw [hpk] at hpk'
                    simp at hpk'
                    omega
                  subst hkk
                  obtain ⟨hrootWf, hrootVal⟩ :=
                    (DeclSlotOk_of_tupleTypeOf ht (.init rootVal)).mp (hlo.slots t d _ hd hsV)
                  obtain ⟨dv, hw', henc, _⟩ :=
                    DeinitBridge.resolveFieldPath_deinit_unit hrootWf hrootVal hres
                  rw [hw] at hw'
                  cases hw'
                  refine ⟨m4, hstep, .inr ⟨t, .field idx fTy :: rest,
                    setAllocs m4 m.mem.memory.allocations, ?_, ?_, ?_⟩⟩
                  · show holeAt body s.frame.blockIdx (s.frame.stmtIdx + 1) = _
                    rw [holeAt_succ hbb hst, hh]
                    rfl
                  · exact hrel.advanceN hfrag (eraseDeinit_block hbb) (by simpa using hlt)
                      s.frame.locals view s.memory lm (setAllocs m4 m.mem.memory.allocations)
                      h4.threads h4.active hlo hns
                      (hrel.stale.keep (eraseDeinit_block hbb) (eraseDeinitBlock_stmt hst) rfl)
                      hrel.retLive
                      (hbo.advance_keep (eraseDeinit_block hbb) (eraseDeinitBlock_stmt hst)
                        (by simp [ptrStmtStep, eraseDeinitStmt]))
                      rfl rfl rfl rfl
                  · refine ⟨lm, ptr, k', _, off, (TupleSpec.scalar it).size, h4.threads, hptr, hpk', hA,
                      by simp [holeRange, hd, ht, hres], rfl, rfl, ?_⟩
                    rw [h4.allocs, henc]
                    rfl
                | _ => simp [resolveFieldPath] at hres
  | _ => simp [isProjDeinit] at hpd


/-! ## Window statements -/

/-- The field place `_t.projs` of a `TupleSpec` local evaluates to the field's byte offset in
`_t`'s allocation on any machine of the right shape, whatever the allocation's bytes. -/
theorem evalPlace_field_any {m : Mach} {ctx : Ctx} {f : Gen.Function} {lm : Map Gen.LocalName Ptr}
    {blk stmt : Nat} {A : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] A)
    {body : CapturedMir} (hfl : FnLocalsSpec body f)
    {t : Nat} {d : LocalDecl} (hd : body.localDecls[t]? = some d)
    {fields : List (Nat × TupleSpec)} {size align : Nat}
    (ht : tupleTypeOf body.layouts d.ty = some (fields, size, align))
    (hrootWf : (TupleSpec.tuple fields size align).wf = true)
    {p : Ptr} (hp : mapGet lm (localName t) = some p) {k : Nat}
    (hpk : p.provenance = some (⟨(k : Int)⟩, ())) (haddr0 : 0 ≤ p.addr)
    (haddrMax : p.addr + (size : Int) < 2 ^ 64)
    {D : List Byte} (hD : D.length = size)
    (hA : A[k]? = some (stackAlloc p.addr (itOf d body.layouts) D))
    {projs : List ProjectionElem} {pe : Gen.PlaceExpr}
    (hpe : translateFieldPlace (.Local (localName t)) projs = some pe)
    {off : Nat} {leaf : TupleSpec}
    (hres : resolveFieldPath body.layouts (.tuple fields size align) projs = some (off, leaf)) :
    evalPlace m pe =
      .ok (({ ptr := { thin_pointer := offsetPtr p off, metadata := none }, aligned := true },
        leaf.toMiniRustTy), m) := by
  obtain ⟨hTd, _⟩ := tyOf_tupleSpec ht
  have hloc := (hfl.2 t d hd).2
  rw [hTd] at hloc
  have hbound : size < 2 ^ 63 := by
    simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hrootWf
    exact hrootWf.1.2
  have hplaceBase := evalPlace_local_some h t _ hloc p hp
  have hrootEval : evalPlace m (.Local (localName t)) =
      .ok (({ ptr := { thin_pointer := offsetPtr p 0, metadata := none }, aligned := true },
        (TupleSpec.tuple fields size align).toMiniRustTy), m) := by
    simpa using hplaceBase
  have hpeEval := evalPlace_ptr_fieldPath h p k hpk (itOf d body.layouts) D hA
    (by rw [hD]; exact hbound) haddr0 (by rw [hD]; exact haddrMax)
    (.Local (localName t)) 0 (.tuple fields size align) hrootEval hrootWf
    (by simp [TupleSpec.size, hD]) projs pe hpe off leaf hres
  simpa using hpeEval

/-- **Re-initialization of a scalar field by a constant, on any allocation bytes.** -/
theorem evalStatement_reinit_any {m : Mach} {ctx : Ctx} {f : Gen.Function}
    {lm : Map Gen.LocalName Ptr} {blk stmt : Nat} {A : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] A)
    {body : CapturedMir} (hfl : FnLocalsSpec body f)
    {t : Nat} {d : LocalDecl} (hd : body.localDecls[t]? = some d)
    {fields : List (Nat × TupleSpec)} {size align : Nat}
    (ht : tupleTypeOf body.layouts d.ty = some (fields, size, align))
    (hrootWf : (TupleSpec.tuple fields size align).wf = true)
    {p : Ptr} (hp : mapGet lm (localName t) = some p) {k : Nat}
    (hpk : p.provenance = some (⟨(k : Int)⟩, ())) (haddr0 : 0 ≤ p.addr)
    (haddrMax : p.addr + (size : Int) < 2 ^ 64)
    {D : List Byte} (hD : D.length = size)
    (hA : A[k]? = some (stackAlloc p.addr (itOf d body.layouts) D))
    {projs : List ProjectionElem} {pe : Gen.PlaceExpr}
    (hpe : translateFieldPlace (.Local (localName t)) projs = some pe)
    {off : Nat} {it : Gen.IntType}
    (hres : resolveFieldPath body.layouts (.tuple fields size align) projs = some (off, .scalar it))
    {bits : Nat} (hbits : bits < 2 ^ (8 * it.size.bytes)) :
    evalStatement m (.Assign pe (.Constant (.Int (intFromBits bits it)) (.Int it))) =
      .ok (withMem m (A.set k (stackAlloc p.addr (itOf d body.layouts)
        (spliceAt D off (scalarBytes it bits))))
        ⟨.Store, .None, (offsetPtr p off).addr, ⟨it.size.bytes⟩⟩) := by
  have hpeEval := evalPlace_field_any h hfl hd ht hrootWf hp hpk haddr0 haddrMax hD hA hpe hres
  obtain ⟨hleafWf, hrelBound⟩ := resolveFieldPath_wf hrootWf hres
  have hv : (TupleSpec.scalar it).valOk (.scalar ⟨bits, it.size.bytes⟩) = true := by
    simp [TupleSpec.valOk, hbits]
  have hst := typedStore_ptr_tuple_slice h p k hpk (itOf d body.layouts) D hA off (.scalar it)
    (.scalar ⟨bits, it.size.bytes⟩) hleafWf hv (by simp [TupleSpec.size] at hrelBound ⊢; omega)
  simp only [TupleSpec.toMiniRustVal, TupleSpec.toMiniRustTy, TupleSpec.encodeVal, valBytes,
    TupleSpec.size] at hst
  simp only [TupleSpec.toMiniRustTy] at hpeEval
  simp [evalStatement, hpeEval, evalValue, evalConstant, placeStore, hst]

/-- **Sibling read `_r = copy _t.projs` of a scalar field, on any allocation bytes whose field
slice encodes the field's value.** -/
theorem evalStatement_siblingRead_any {m : Mach} {ctx : Ctx} {f : Gen.Function}
    {lm : Map Gen.LocalName Ptr} {blk stmt : Nat} {A : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] A)
    {body : CapturedMir} (hfl : FnLocalsSpec body f)
    {t : Nat} {d : LocalDecl} (hd : body.localDecls[t]? = some d)
    {fields : List (Nat × TupleSpec)} {size align : Nat}
    (ht : tupleTypeOf body.layouts d.ty = some (fields, size, align))
    (hrootWf : (TupleSpec.tuple fields size align).wf = true)
    {p : Ptr} (hp : mapGet lm (localName t) = some p) {k : Nat}
    (hpk : p.provenance = some (⟨(k : Int)⟩, ())) (haddr0 : 0 ≤ p.addr)
    (haddrMax : p.addr + (size : Int) < 2 ^ 64)
    {D : List Byte} (hD : D.length = size)
    (hA : A[k]? = some (stackAlloc p.addr (itOf d body.layouts) D))
    {projs : List ProjectionElem} {pe : Gen.PlaceExpr}
    (hpe : translateFieldPlace (.Local (localName t)) projs = some pe)
    {off : Nat} {it : Gen.IntType}
    (hres : resolveFieldPath body.layouts (.tuple fields size align) projs = some (off, .scalar it))
    {bits : Nat} (hbits : bits < 2 ^ (8 * it.size.bytes))
    (hslice : (D.drop off).take it.size.bytes = scalarBytes it bits)
    {r : Nat} {dr : LocalDecl} (hdr : body.localDecls[r]? = some dr)
    (hit : intTypeOf dr.ty = some it) :
    (mapGet lm (localName r) = none →
      evalStatement m (.Assign (.Local (localName r)) (.Load pe)) =
        .error (.ub "access to a dead local")) ∧
    (∀ (pr : Ptr) (kr : Nat) (Dr : List Byte), mapGet lm (localName r) = some pr →
      pr.provenance = some (⟨(kr : Int)⟩, ()) →
      A[kr]? = some (stackAlloc pr.addr it Dr) → Dr.length = it.size.bytes →
      ∃ m', evalStatement m (.Assign (.Local (localName r)) (.Load pe)) = .ok m' ∧
        Shape m' ctx [ctx.caller, calleeFrameL f ctx lm blk stmt]
          (A.set kr (stackAlloc pr.addr it (scalarBytes it bits)))) := by
  obtain ⟨hTr, _⟩ := tyOf_int (layouts := body.layouts) hit
  have hlocr := (hfl.2 r dr hdr).2
  rw [hTr] at hlocr
  have hpeEval := evalPlace_field_any h hfl hd ht hrootWf hp hpk haddr0 haddrMax hD hA hpe hres
  obtain ⟨hleafWf, hrelBound⟩ := resolveFieldPath_wf hrootWf hres
  have hv : (TupleSpec.scalar it).valOk (.scalar ⟨bits, it.size.bytes⟩) = true := by
    simp [TupleSpec.valOk, hbits]
  have hgood : GoodSize it.size.bytes := by
    simp only [TupleSpec.wf] at hleafWf
    exact (goodAlignBytes_iff it.size.bytes).mp hleafWf
  obtain ⟨m1, hm1, h1⟩ := typedLoad_ptr_tuple_slice h p k hpk (itOf d body.layouts) D hA off
    (.scalar it) (.scalar ⟨bits, it.size.bytes⟩) hleafWf hv
    (by simp [TupleSpec.size] at hrelBound ⊢; omega) (by simpa [TupleSpec.encodeVal, valBytes,
      TupleSpec.size] using hslice)
  simp only [TupleSpec.toMiniRustVal, TupleSpec.toMiniRustTy] at hm1 hpeEval
  refine ⟨fun hnone => ?_, fun pr kr Dr hpr hprk hAr hlen => ?_⟩
  · rw [evalStatement, evalPlace_local_none h r _ hlocr hnone]
    rfl
  · have hst := typedStore_ptr_frag h1 pr kr hprk (FragTy.int it hgood) Dr bits hbits hAr hlen
    refine ⟨withMem m1 (A.set kr (stackAlloc pr.addr it (scalarBytes it bits)))
      ⟨.Store, .None, pr.addr, it.size⟩, ?_, withMem_shape h1 _⟩
    simp only [valOf] at hst
    simp [evalStatement, evalPlace_local_some h r _ hlocr pr hpr, evalValue, hpeEval, placeLoad,
      hm1, placeStore, hst]


/-- A slice disjoint from the spliced range is unchanged by `spliceAt`. -/
theorem spliceAt_drop_take_disjoint {α : Type} (xs bs : List α) (off off' n : Nat)
    (hb : off + bs.length ≤ xs.length) (hdis : off' + n ≤ off ∨ off + bs.length ≤ off') :
    ((spliceAt xs off bs).drop off').take n = (xs.drop off').take n := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_take, List.getElem?_drop]
  by_cases hj : j < n
  · simp only [hj, ↓reduceIte]
    rw [getElem?_spliceAt xs off bs hb]
    rcases hdis with h | h
    · simp [show off' + j < off by omega]
    · simp [show ¬ (off' + j < off) by omega, show ¬ (off' + j < off + bs.length) by omega]
  · simp [hj]

/-- Two thread lists of the related shape agree on the program counter and locals map. -/
theorem frame_pc_of_threads {f : Gen.Function} {ctx : Ctx} {lm lm' : Map Gen.LocalName Ptr}
    {blk stmt blk' stmt' : Nat} {m : Mach}
    (h1 : m.threads = [thread1 ctx [ctx.caller, calleeFrameL f ctx lm blk stmt]])
    (h2 : m.threads = [thread1 ctx [ctx.caller, calleeFrameL f ctx lm' blk' stmt']]) :
    blk = blk' ∧ stmt = stmt' ∧ lm = lm' := by
  rw [h1] at h2
  simp [thread1, calleeFrameL] at h2
  obtain ⟨hlm, hb, hs⟩ := h2
  exact ⟨(bbName_inj _ _).mp hb, by exact_mod_cast hs, hlm⟩

/-- `ReturnRel` depends on the MiniRust machine only through its threads and allocations. -/
theorem ReturnRel.of_obs {body : CapturedMir} {ctx : Ctx} {s : MachineState} {v : Value}
    {m m' : Mach} (h : ReturnRel body ctx s v m) (hthr : m'.threads = m.threads)
    (hal : m'.mem.memory.allocations = m.mem.memory.allocations) : ReturnRel body ctx s v m' := by
  obtain ⟨r, a, d, R, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨r, a, d, R, h1, h2, h3, h4, hthr ▸ h5, hal ▸ h6, h7⟩

/-- A `StepRelN` of the erased body reaching `m4` gives a `StepRelD` reaching any machine with
the same threads, active thread, and allocations. -/
theorem StepRelN.toStepRelD_obs {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {s : MachineState} {a : MirStepNode} {m4 m4' : Mach}
    (h : StepRelN (eraseDeinit body) f ctx s a (.ok m4)) (hthr : m4'.threads = m4.threads)
    (hact : m4'.active_thread = m4.active_thread)
    (hal : m4'.mem.memory.allocations = m4.mem.memory.allocations) :
    StepRelD body f ctx s a (.ok m4') := by
  unfold StepRelN at h
  unfold StepRelD
  split at h
  · obtain ⟨m', hr, h'⟩ := h
    cases hr
    exact ⟨m4', rfl, .inl (h'.of_obs hthr hact hal)⟩
  · obtain ⟨s', m', hk, hr, h'⟩ := h
    cases hr
    exact ⟨s', m4', hk, rfl, .inl (h'.of_obs hthr hact hal)⟩
  · obtain ⟨m', hr, h'⟩ := h
    cases hr
    exact ⟨m4', rfl, h'.of_obs hthr hal⟩
  · obtain ⟨msg, hr⟩ := h
    cases hr
  · exact h.elim

/-- A `StepRelN` of the erased body reaching `m4` at statement `i + 1` of block `blk` gives a
`StepRelD` reaching the machine `m4h` that differs from `m4` only by the open hole. -/
theorem StepRelN.toStepRelD_hole {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {s : MachineState} {a : MirStepNode} {m4 m4h : Mach} {lm : Map Gen.LocalName Ptr}
    {blk i t k off sz : Nat} {ps : List ProjectionElem} {p : Ptr} {a0 : Gen.Allocation}
    (h : StepRelN (eraseDeinit body) f ctx s a (.ok m4))
    (hthr4 : m4.threads = [thread1 ctx [ctx.caller, calleeFrameL f ctx lm blk (i + 1)]])
    (hhole : holeAt body blk (i + 1) = some (t, ps))
    (hp : mapGet lm (localName t) = some p) (hpk : p.provenance = some (⟨(k : Int)⟩, ()))
    (ha : m4.mem.memory.allocations[k]? = some a0) (hrng : holeRange body t ps = some (off, sz))
    (hthrH : m4h.threads = m4.threads) (hactH : m4h.active_thread = m4.active_thread)
    (hallocH : m4h.mem.memory.allocations = m4.mem.memory.allocations.set k
      { a0 with data := spliceAt a0.data off (List.replicate sz .Uninit) }) :
    StepRelD body f ctx s a (.ok m4h) := by
  have hhr : ∀ s' : MachineState, StateRelN (eraseDeinit body) f ctx s' m4 →
      StateRelD body f ctx s' m4h := by
    intro s' hN'
    obtain ⟨_, _, hrelA', _, _, _, _⟩ := id hN'
    obtain ⟨lm', hthr', _⟩ := hrelA'.frame
    obtain ⟨hb, hs, hl⟩ := frame_pc_of_threads hthr4 hthr'
    refine .inr ⟨t, ps, m4, by rw [← hb, ← hs]; exact hhole, hN', lm, p, k, a0, off, sz, ?_, hp, hpk,
      ha, hrng, hthrH, hactH, hallocH⟩
    rw [hthr4, ← hb, ← hs]
  unfold StepRelN at h
  unfold StepRelD
  split at h
  · obtain ⟨m', hr, h'⟩ := h
    cases hr
    exact ⟨m4h, rfl, hhr _ h'⟩
  · obtain ⟨s', m', hk, hr, h'⟩ := h
    cases hr
    exact ⟨s', m4h, hk, rfl, hhr _ h'⟩
  · obtain ⟨m', hr, h'⟩ := h
    cases hr
    obtain ⟨_, _, _, _, _, _, _, _, hthr, _, _⟩ := h'
    rw [hthr4] at hthr
    simp [thread1] at hthr
  · obtain ⟨msg, hr⟩ := h
    cases hr
  · exact h.elim

/-- What `reinitOk` gives: the field's `TupleSpec` resolution and the translation of the
constant to `Constant::Int` of the field's type. -/
theorem reinitOk_spec {body : CapturedMir} {t : Nat} {projs : List ProjectionElem}
    {c : ConstOperand} (h : reinitOk body t projs c = true) :
    ∃ (d : LocalDecl) (fields : List (Nat × TupleSpec)) (size align off : Nat) (it : Gen.IntType)
      (bits : Nat),
      body.localDecls[t]? = some d ∧ tupleTypeOf body.layouts d.ty = some (fields, size, align) ∧
      resolveFieldPath body.layouts (.tuple fields size align) projs = some (off, .scalar it) ∧
      0 < it.size.bytes ∧ bits < 2 ^ (8 * it.size.bytes) ∧
      translateOperand body.localDecls (.constant c) =
        some (.Constant (.Int (intFromBits bits it)) (.Int it)) := by
  unfold reinitOk at h
  cases hd : body.localDecls[t]? with
  | none => simp [hd] at h
  | some d =>
    cases ht : tupleTypeOf body.layouts d.ty with
    | none => simp [hd, ht] at h
    | some trip =>
      obtain ⟨fields, size, align⟩ := trip
      cases hres : resolveFieldPath body.layouts (.tuple fields size align) projs with
      | none => simp [hd, ht, hres] at h
      | some pr =>
        obtain ⟨off, leaf⟩ := pr
        cases leaf with
        | tuple _ _ _ => simp [hd, ht, hres] at h
        | scalar it =>
          obtain ⟨cty, cval⟩ := c
          cases cval with
          | scalar cs =>
            cases cs with
            | int sc =>
              obtain ⟨bits, csz⟩ := sc
              cases hcit : intTypeOf cty with
              | none => simp [hd, ht, hres, hcit] at h
              | some it' =>
                simp only [hd, ht, hres, hcit, Bool.and_eq_true, decide_eq_true_eq,
                  Bool.not_eq_true'] at h
                obtain ⟨⟨hpos, hnb⟩, ⟨hii, hcsz⟩, hbits⟩ := h
                rw [hii] at hcit
                subst hcsz
                refine ⟨d, fields, size, align, off, it, bits, rfl, ht, hres, hpos, hbits, ?_⟩
                simp [translateOperand, hnb, hcit, hbits]
            | ptr _ _ => simp [hd, ht, hres] at h
          | _ => simp [hd, ht, hres] at h

/-- What `siblingReadOk` gives: both field paths resolve in `_t`'s `TupleSpec`, the read one to
a scalar of `_r`'s integer type, and the byte ranges are disjoint. -/
theorem siblingReadOk_spec {body : CapturedMir} {t r : Nat} {ps ps' : List ProjectionElem}
    (h : siblingReadOk body t r ps ps' = true) :
    r ≠ t ∧ ∃ (dr d : LocalDecl) (fields : List (Nat × TupleSpec)) (size align : Nat)
      (it : Gen.IntType) (off : Nat) (leaf : TupleSpec) (off' : Nat),
      body.localDecls[r]? = some dr ∧ body.localDecls[t]? = some d ∧ intTypeOf dr.ty = some it ∧
      tupleTypeOf body.layouts d.ty = some (fields, size, align) ∧
      resolveFieldPath body.layouts (.tuple fields size align) ps = some (off, leaf) ∧
      resolveFieldPath body.layouts (.tuple fields size align) ps' = some (off', .scalar it) ∧
      (off' + it.size.bytes ≤ off ∨ off + leaf.size ≤ off') := by
  unfold siblingReadOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hrt, h⟩ := h
  refine ⟨hrt, ?_⟩
  cases hdr : body.localDecls[r]? with
  | none => simp [hdr] at h
  | some dr =>
    cases hd : body.localDecls[t]? with
    | none => simp [hdr, hd] at h
    | some d =>
      cases hit : intTypeOf dr.ty with
      | none => simp [hdr, hd, hit] at h
      | some it =>
        cases ht : tupleTypeOf body.layouts d.ty with
        | none => simp [hdr, hd, hit, ht] at h
        | some trip =>
          obtain ⟨fields, size, align⟩ := trip
          cases hres : resolveFieldPath body.layouts (.tuple fields size align) ps with
          | none => simp [hdr, hd, hit, ht, hres] at h
          | some pr =>
            obtain ⟨off, leaf⟩ := pr
            cases hres' : resolveFieldPath body.layouts (.tuple fields size align) ps' with
            | none => simp [hdr, hd, hit, ht, hres, hres'] at h
            | some pr' =>
              obtain ⟨off', leaf'⟩ := pr'
              cases leaf' with
              | tuple _ _ _ => simp [hdr, hd, hit, ht, hres, hres'] at h
              | scalar it' =>
                simp only [hdr, hd, hit, ht, hres, hres', Bool.and_eq_true, decide_eq_true_eq,
                  Bool.or_eq_true] at h
                obtain ⟨rfl, hdis⟩ := h
                exact ⟨dr, d, fields, size, align, it', off, leaf, off', rfl, rfl, hit, ht, hres,
                  hres', hdis⟩

/-- The hole's `TupleSpec` local `_t` in the hole-free machine `m0` and the machine `m` with
the hole: its root value, pointer, allocation, and the two allocation images. -/
theorem holeLocal_spec {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s : MachineState}
    {m m0 : Mach} {t : Nat} {ps : List ProjectionElem}
    (hN0 : StateRelN (eraseDeinit body) f ctx s m0)
    (hHR : HoleRel body f ctx s.frame.blockIdx s.frame.stmtIdx t ps m0 m)
    {d : LocalDecl} (hd : body.localDecls[t]? = some d)
    {fields : List (Nat × TupleSpec)} {size align : Nat}
    (ht : tupleTypeOf body.layouts d.ty = some (fields, size, align)) :
    ∃ (view : List LocalSlot) (lm : Map Gen.LocalName Ptr) (p : Ptr) (k : Nat) (rootVal : Value)
      (off sz : Nat),
      m0.threads = [thread1 ctx [ctx.caller, calleeFrameL f ctx lm s.frame.blockIdx s.frame.stmtIdx]] ∧
      LocalsOk (eraseDeinit body) (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows) view lm
        m0.mem.memory.allocations ∧
      view[t]? = some (.init rootVal) ∧
      mapGet lm (localName t) = some p ∧ p.provenance = some (⟨(k : Int)⟩, ()) ∧
      0 ≤ p.addr ∧ p.addr + (size : Int) < 2 ^ 64 ∧
      (TupleSpec.tuple fields size align).wf = true ∧
      (TupleSpec.tuple fields size align).valOk rootVal = true ∧
      ((TupleSpec.tuple fields size align).encodeVal rootVal).length = size ∧
      m0.mem.memory.allocations[k]? = some (stackAlloc p.addr (itOf d body.layouts)
        ((TupleSpec.tuple fields size align).encodeVal rootVal)) ∧
      holeRange body t ps = some (off, sz) ∧
      m.threads = m0.threads ∧ m.active_thread = m0.active_thread ∧
      m.mem.memory.allocations = m0.mem.memory.allocations.set k
        (stackAlloc p.addr (itOf d body.layouts)
          (spliceAt ((TupleSpec.tuple fields size align).encodeVal rootVal) off
            (List.replicate sz .Uninit))) := by
  obtain ⟨view, lm0, hrel0, hthr0, hlo0, hns0, _⟩ := hN0
  obtain ⟨lm, p, k, a, off, sz, hthrH, hp, hpk, ha, hrng, hthrE, hactE, hallocE⟩ := hHR
  obtain ⟨-, -, rfl⟩ := frame_pc_of_threads hthr0 hthrH
  have ht_lt : t < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  obtain ⟨slot, hsV⟩ : ∃ slot, view[t]? = some slot :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlo0.nlocals]; exact ht_lt)⟩
  obtain ⟨⟨rootVal, rfl⟩, _⟩ := hns0 t d slot hd hsV
    (scalarTypeOf_none_of_tupleTypeOf ht) (isPtrTy_false_of_tupleTypeOf ht)
  obtain ⟨k', hpk', _, haddr, haddrMax, _, hA0⟩ := hlo0.storage_nonptr t d (.init rootVal) p hd
    hsV hp (isPtrTy_false_of_tupleTypeOf ht)
  simp only [eraseDeinit_layouts] at hA0 haddr haddrMax
  rw [declSlotData_of_tupleSpec ht] at hA0
  have hkk : k' = k := by
    rw [hpk] at hpk'
    simp at hpk'
    omega
  subst hkk
  rw [ha] at hA0
  cases hA0
  obtain ⟨hrootWf, hrootVal⟩ :=
    (DeclSlotOk_of_tupleTypeOf ht (.init rootVal)).mp (hlo0.slots t d _ hd hsV)
  obtain ⟨hTd, _⟩ := tyOf_tupleSpec ht
  rw [hTd] at haddrMax
  simp only [TupleSpec.toMiniRustTy, tyBytes] at haddrMax
  refine ⟨view, lm0, p, k', rootVal, off, sz, hthr0, hlo0, hsV, hp, hpk', haddr.nonneg, haddrMax,
    hrootWf, hrootVal, TupleSpec.encodeVal_length _ rootVal hrootWf, ha, hrng, hthrE, hactE, ?_⟩
  rw [hallocE]
  rfl

/-- **Re-initialization step.** While `_t.ps` is a hole, `_t.ps' = const` with the hole's byte
range stores the constant over the hole in both the hole-free machine and the machine with the
hole, which then agree: the hole closes and the plain relation holds again. -/
theorem step_window_reinit {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment (eraseDeinit body) = true) (hf : translateFn body = some f)
    {ctx : Ctx} {s : MachineState} {m m0 : Mach} {t : Nat} {ps : List ProjectionElem}
    (_hhole : holeAt body s.frame.blockIdx s.frame.stmtIdx = some (t, ps))
    (hN0 : StateRelN (eraseDeinit body) f ctx s m0)
    (hHR : HoleRel body f ctx s.frame.blockIdx s.frame.stmtIdx t ps m0 m)
    {bb : BasicBlockData} {ps' : List ProjectionElem} {c : ConstOperand} {span : String}
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some ⟨.assign ⟨t, ps'⟩ (.use (.constant c)), span⟩)
    (hre : reinitOk body t ps' c = true) (hrange : holeRange body t ps' = holeRange body t ps) :
    StepRelD body f ctx s (stepMirFn body s) (Interp.step m) := by
  obtain ⟨_, _, hrel0, _, _, _, _⟩ := id hN0
  obtain ⟨hphase, _, _, _, _, _, _, _, _, _⟩ := inFragment_spec _ hfrag
  obtain ⟨d, fields, size, align, off', it, bits, hd, ht, hres', _, hbits, hop⟩ := reinitOk_spec hre
  obtain ⟨view, lm, p, k, rootVal, off, sz, hthr0, _, _, hp, hpk, haddr0, haddrMax, hrootWf,
    _, hD0, hA0, hrng, hthrE, hactE, hallocE⟩ := holeLocal_spec hN0 hHR hd ht
  have hr' : holeRange body t ps' = some (off', it.size.bytes) := by
    simp [holeRange, hd, ht, hres', TupleSpec.size]
  rw [hr', hrng] at hrange
  simp only [Option.some.injEq, Prod.mk.injEq] at hrange
  obtain ⟨hoff, hsz⟩ := hrange
  subst off'
  subst sz
  obtain ⟨_, hrelBound⟩ := resolveFieldPath_wf hrootWf hres'
  have hoffb : off + it.size.bytes ≤ size := by simpa [TupleSpec.size] using hrelBound
  obtain ⟨tb, htb, hgetb⟩ := (translateFn_spec body f hf).2.2 _ bb hbb
  obtain ⟨hlen, hstspec, _⟩ := translateBlock_spec _ _ bb tb htb
  obtain ⟨st', hst', htst⟩ := hstspec _ _ hst
  cases ps' with
  | nil => simp [resolveFieldPath] at hres'
  | cons pe0 rest =>
    cases pe0 with
    | field idx fTy =>
      obtain ⟨pe, hpe, rfl⟩ : ∃ pe, translateFieldPlace (.Local (localName t))
          (.field idx fTy :: rest) = some pe ∧
          st' = .Assign pe (.Constant (.Int (intFromBits bits it)) (.Int it)) := by
        simp only [translateStatement, translatePlace] at hst'
        cases hp' : translateFieldPlace (.Local (localName t)) (.field idx fTy :: rest) with
        | none => simp [hp'] at hst'
        | some pe =>
          refine ⟨pe, rfl, ?_⟩
          simp [hp', copyRv, copyOp, translateRvalue, hop] at hst'
          exact hst'.symm
      have hshape0 : Shape m0 (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows)
          [(ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows).caller,
            calleeFrameL f (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows) lm
              s.frame.blockIdx s.frame.stmtIdx] m0.mem.memory.allocations :=
        ⟨hthr0, hrel0.active, rfl⟩
      have hshapeH : Shape m (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows)
          [(ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows).caller,
            calleeFrameL f (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows) lm
              s.frame.blockIdx s.frame.stmtIdx] m.mem.memory.allocations :=
        ⟨hthrE.trans hthr0, hactE.trans hrel0.active, rfl⟩
      have hk_lt : k < m0.mem.memory.allocations.length := (List.getElem?_eq_some_iff.mp hA0).1
      have hDh : (spliceAt ((TupleSpec.tuple fields size align).encodeVal rootVal) off
          (List.replicate it.size.bytes .Uninit)).length = size := by
        rw [spliceAt_length _ _ _ (by rw [List.length_replicate, hD0]; omega), hD0]
      have hAh : m.mem.memory.allocations[k]? = some (stackAlloc p.addr (itOf d body.layouts)
          (spliceAt ((TupleSpec.tuple fields size align).encodeVal rootVal) off
            (List.replicate it.size.bytes .Uninit))) := by
        rw [hallocE]
        simp [hk_lt]
      have hfl := FnLocalsSpec.of_translateFn hf
      have hev0 := evalStatement_reinit_any (resetPick_shape hshape0) hfl hd ht hrootWf hp hpk
        haddr0 haddrMax hD0 hA0 hpe hres' hbits
      have hevH := evalStatement_reinit_any (resetPick_shape hshapeH) hfl hd ht hrootWf hp hpk
        haddr0 haddrMax hDh hAh hpe hres' hbits
      have hwlen : (scalarBytes it bits).length = it.size.bytes := by
        simp [scalarBytes, leBytes_length]
      rw [spliceAt_same _ off _ _ (by rw [List.length_replicate, hD0]; omega)
        (by rw [List.length_replicate, hwlen]), hallocE, List.set_set] at hevH
      obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee (withMem_shape (resetPick_shape hshape0)
        (allocs' := m0.mem.memory.allocations.set k (stackAlloc p.addr (itOf d body.layouts)
          (spliceAt ((TupleSpec.tuple fields size align).encodeVal rootVal) off
            (scalarBytes it bits))))
        ⟨.Store, .None, (offsetPtr p off).addr, ⟨it.size.bytes⟩⟩)
      obtain ⟨m4h, hm4h, h4h⟩ := bumpStmt_callee (withMem_shape (resetPick_shape hshapeH)
        (allocs' := m0.mem.memory.allocations.set k (stackAlloc p.addr (itOf d body.layouts)
          (spliceAt ((TupleSpec.tuple fields size align).encodeVal rootVal) off
            (scalarBytes it bits))))
        ⟨.Store, .None, (offsetPtr p off).addr, ⟨it.size.bytes⟩⟩)
      have hne : ((s.frame.stmtIdx : Nat) : Int) ≠ (tb.statements.length : Int) := by
        have := (List.getElem?_eq_some_iff.mp hst).1
        rw [hlen]
        omega
      have hstep0 : Interp.step m0 = .ok m4 := by
        rw [step_callee hshape0 tb hgetb]
        simp [hne, listIndex_nat _ _ _ htst, hev0, hm4, check_after h4]
      have hstepH : Interp.step m = .ok m4h := by
        rw [step_callee hshapeH tb hgetb]
        simp [hne, listIndex_nat _ _ _ htst, hevH, hm4h, check_after h4h]
      have hnd : ∀ st, bb.statements[s.frame.stmtIdx]? = some st → isProjDeinit st = false := by
        intro st hst2
        rw [hst] at hst2
        cases hst2
        rfl
      have hNF := step_correspondence_NF (eraseDeinit body) f hfrag (fnLocalsSpec_eraseDeinit hf)
        ctx s m0 (blk_eraseDeinit hf hbb hnd) hN0
      rw [stepMirFn_eraseDeinit_stmt (body := body) hrel0.activeCallee hphase hbb hst rfl, hstepH]
      rw [hstep0] at hNF
      exact StepRelN.toStepRelD_obs hNF (h4h.threads.trans h4.threads.symm)
        (h4h.active.trans h4.active.symm) (h4h.allocs.trans h4.allocs.symm)
    | _ => simp [resolveFieldPath] at hres'

/-- **Sibling-read step.** While `_t.ps` is a hole, `_r = copy _t.ps'` of a disjoint scalar
field reads the same bytes from the hole-free machine and from the machine with the hole, and
stores into `_r`'s allocation, which is not `_t`'s: the hole stays open. -/
theorem step_window_read {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment (eraseDeinit body) = true) (hf : translateFn body = some f)
    {ctx : Ctx} {s : MachineState} {m m0 : Mach} {t : Nat} {ps : List ProjectionElem}
    (hhole : holeAt body s.frame.blockIdx s.frame.stmtIdx = some (t, ps))
    (hN0 : StateRelN (eraseDeinit body) f ctx s m0)
    (hHR : HoleRel body f ctx s.frame.blockIdx s.frame.stmtIdx t ps m0 m)
    {bb : BasicBlockData} {r : Nat} {ps' : List ProjectionElem} {span : String}
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some ⟨.assign ⟨r, []⟩ (.use (.copy ⟨t, ps'⟩)), span⟩)
    (hsib : siblingReadOk body t r ps ps' = true) :
    StepRelD body f ctx s (stepMirFn body s) (Interp.step m) := by
  obtain ⟨_, _, hrel0, _, _, _, _⟩ := id hN0
  obtain ⟨hphase, _, _, _, _, _, _, _, _, _⟩ := inFragment_spec _ hfrag
  obtain ⟨hrt, dr, d, fields, size, align, it, off0, leaf, off', hdr, hd, hit, ht, hres, hres',
    hdis⟩ := siblingReadOk_spec hsib
  obtain ⟨view, lm, p, k, rootVal, off, sz, hthr0, hlo0, _, hp, hpk, haddr0, haddrMax, hrootWf,
    hrootVal, hD0, hA0, hrng, hthrE, hactE, hallocE⟩ := holeLocal_spec hN0 hHR hd ht
  have hr0 : holeRange body t ps = some (off0, leaf.size) := by
    simp [holeRange, hd, ht, hres]
  rw [hr0] at hrng
  simp only [Option.some.injEq, Prod.mk.injEq] at hrng
  obtain ⟨hoff, hsz⟩ := hrng
  subst off0
  subst sz
  obtain ⟨_, hrelB0⟩ := resolveFieldPath_wf hrootWf hres
  have hoffb : off + leaf.size ≤ size := by simpa [TupleSpec.size] using hrelB0
  obtain ⟨leafVal, _, hleafOk, hslice0, _⟩ := resolveFieldPath_read hrootWf hrootVal hres'
  cases leafVal with
  | scalar sc =>
    have hbits : sc.bits < 2 ^ (8 * it.size.bytes) := by
      simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hleafOk
      exact hleafOk.2
    simp only [TupleSpec.size, TupleSpec.encodeVal, valBytes] at hslice0
    have hsliceH : ((spliceAt ((TupleSpec.tuple fields size align).encodeVal rootVal) off
        (List.replicate leaf.size .Uninit)).drop off').take it.size.bytes =
        scalarBytes it sc.bits := by
      rw [spliceAt_drop_take_disjoint _ _ _ _ _ (by rw [List.length_replicate, hD0]; exact hoffb)
        (by rw [List.length_replicate]; exact hdis)]
      exact hslice0
    obtain ⟨tb, htb, hgetb⟩ := (translateFn_spec body f hf).2.2 _ bb hbb
    obtain ⟨hlen, hstspec, _⟩ := translateBlock_spec _ _ bb tb htb
    obtain ⟨st', hst', htst⟩ := hstspec _ _ hst
    cases ps' with
    | nil => simp [resolveFieldPath] at hres'
    | cons pe0 rest =>
      cases pe0 with
      | field idx fTy =>
        obtain ⟨pe, hpe, rfl⟩ : ∃ pe, translateFieldPlace (.Local (localName t))
            (.field idx fTy :: rest) = some pe ∧
            st' = .Assign (.Local (localName r)) (.Load pe) := by
          simp only [translateStatement, translatePlace] at hst'
          cases hp' : translateFieldPlace (.Local (localName t)) (.field idx fTy :: rest) with
          | none => simp [hp', copyRv, copyOp, translateRvalue, translateOperand, translatePlace] at hst'
          | some pe =>
            refine ⟨pe, rfl, ?_⟩
            simp [hp', copyRv, copyOp, translateRvalue, translateOperand, translatePlace] at hst'
            exact hst'.symm
        have hshape0 : Shape m0 (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows)
            [(ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows).caller,
              calleeFrameL f (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows) lm
                s.frame.blockIdx s.frame.stmtIdx] m0.mem.memory.allocations :=
          ⟨hthr0, hrel0.active, rfl⟩
        have hshapeH : Shape m (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows)
            [(ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows).caller,
              calleeFrameL f (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows) lm
                s.frame.blockIdx s.frame.stmtIdx] m.mem.memory.allocations :=
          ⟨hthrE.trans hthr0, hactE.trans hrel0.active, rfl⟩
        have hk_lt : k < m0.mem.memory.allocations.length := (List.getElem?_eq_some_iff.mp hA0).1
        have hDh : (spliceAt ((TupleSpec.tuple fields size align).encodeVal rootVal) off
            (List.replicate leaf.size .Uninit)).length = size := by
          rw [spliceAt_length _ _ _ (by rw [List.length_replicate, hD0]; omega), hD0]
        have hAh : m.mem.memory.allocations[k]? = some (stackAlloc p.addr (itOf d body.layouts)
            (spliceAt ((TupleSpec.tuple fields size align).encodeVal rootVal) off
              (List.replicate leaf.size .Uninit))) := by
          rw [hallocE]
          simp [hk_lt]
        have hfl := FnLocalsSpec.of_translateFn hf
        obtain ⟨hdead0, hlive0⟩ := evalStatement_siblingRead_any (resetPick_shape hshape0) hfl hd
          ht hrootWf hp hpk haddr0 haddrMax hD0 hA0 hpe hres' hbits hslice0 hdr hit
        obtain ⟨hdeadH, hliveH⟩ := evalStatement_siblingRead_any (resetPick_shape hshapeH) hfl hd
          ht hrootWf hp hpk haddr0 haddrMax hDh hAh hpe hres' hbits hsliceH hdr hit
        have hne : ((s.frame.stmtIdx : Nat) : Int) ≠ (tb.statements.length : Int) := by
          have := (List.getElem?_eq_some_iff.mp hst).1
          rw [hlen]
          omega
        have hnd : ∀ st, bb.statements[s.frame.stmtIdx]? = some st →
            isProjDeinit st = false := by
          intro st hst2
          rw [hst] at hst2
          cases hst2
          rfl
        have hNF := step_correspondence_NF (eraseDeinit body) f hfrag
          (fnLocalsSpec_eraseDeinit hf) ctx s m0 (blk_eraseDeinit hf hbb hnd) hN0
        rw [stepMirFn_eraseDeinit_stmt (body := body) hrel0.activeCallee hphase hbb hst rfl]
        cases hpr : mapGet lm (localName r) with
        | none =>
          have hs0 : Interp.step m0 = .error (.ub "access to a dead local") := by
            rw [step_callee hshape0 tb hgetb]
            simp [hne, listIndex_nat _ _ _ htst, hdead0 hpr]
          have hsH : Interp.step m = .error (.ub "access to a dead local") := by
            rw [step_callee hshapeH tb hgetb]
            simp [hne, listIndex_nat _ _ _ htst, hdeadH hpr]
          rw [hs0] at hNF
          rw [hsH]
          exact hNF.toStepRelD
        | some pr =>
          have hr_lt : r < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdr).1
          obtain ⟨slotr, hsVr⟩ : ∃ slot, view[r]? = some slot :=
            ⟨_, List.getElem?_eq_getElem (by rw [hlo0.nlocals]; exact hr_lt)⟩
          have hscr : scalarTypeOf dr.ty = some (.Int it) := scalarTypeOf_int hit
          obtain ⟨kr, hprk, _, _, _, _, hAr⟩ := hlo0.storage_nonptr r dr slotr pr hdr hsVr hpr
            (isPtrTy_false_of_scalarTypeOf hscr)
          simp only [eraseDeinit_layouts] at hAr
          obtain ⟨hTr, hIr⟩ := tyOf_int (layouts := body.layouts) hit
          rw [hIr] at hAr
          have hlenr : (declSlotData dr slotr body.layouts).length = it.size.bytes := by
            rw [declSlotData_length (by rw [hTr]; exact hscr), hTr]
            rfl
          have hkr : kr ≠ k := by
            intro hkk
            subst hkk
            exact hrt (hlo0.inj r t pr p hpr hp (by rw [hprk, hpk]))
          have hArH : m.mem.memory.allocations[kr]? =
              some (stackAlloc pr.addr it (declSlotData dr slotr body.layouts)) := by
            rw [hallocE, List.getElem?_set_ne (Ne.symm hkr)]
            exact hAr
          obtain ⟨m3, hev0, h3⟩ := hlive0 pr kr _ hpr hprk hAr hlenr
          obtain ⟨m3h, hevH, h3h⟩ := hliveH pr kr _ hpr hprk hArH hlenr
          obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3
          obtain ⟨m4h, hm4h, h4h⟩ := bumpStmt_callee h3h
          have hs0 : Interp.step m0 = .ok m4 := by
            rw [step_callee hshape0 tb hgetb]
            simp [hne, listIndex_nat _ _ _ htst, hev0, hm4, check_after h4]
          have hsH : Interp.step m = .ok m4h := by
            rw [step_callee hshapeH tb hgetb]
            simp [hne, listIndex_nat _ _ _ htst, hevH, hm4h, check_after h4h]
          rw [hs0] at hNF
          rw [hsH]
          have hhole' : holeAt body s.frame.blockIdx (s.frame.stmtIdx + 1) = some (t, ps) := by
            rw [holeAt_succ hbb hst, hhole]
            simp [holeAfter, hrt]
          refine StepRelN.toStepRelD_hole hNF h4.threads hhole' hp hpk
            (by rw [h4.allocs, List.getElem?_set_ne hkr]; exact hA0) hr0
            (h4h.threads.trans h4.threads.symm) (h4h.active.trans h4.active.symm) ?_
          rw [h4h.allocs, h4.allocs, hallocE]
          exact List.set_comm _ _ (Ne.symm hkr)
      | _ => simp [resolveFieldPath] at hres'
  | _ => simp [TupleSpec.valOk] at hleafOk

/-- What `reinitCopyOk` gives: `r ≠ t`, `_r`'s integer type `it`, and the resolution of `ps'` in
`_t`'s `TupleSpec` to a scalar leaf of the same integer type `it` with positive size. -/
theorem reinitCopyOk_spec {body : CapturedMir} {t r : Nat} {ps' : List ProjectionElem}
    (h : reinitCopyOk body t r ps' = true) :
    r ≠ t ∧ ∃ (dr d : LocalDecl) (fields : List (Nat × TupleSpec)) (size align off' : Nat)
      (it : Gen.IntType),
      body.localDecls[r]? = some dr ∧ body.localDecls[t]? = some d ∧ intTypeOf dr.ty = some it ∧
      tupleTypeOf body.layouts d.ty = some (fields, size, align) ∧
      resolveFieldPath body.layouts (.tuple fields size align) ps' = some (off', .scalar it) ∧
      0 < it.size.bytes := by
  unfold reinitCopyOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hrt, h⟩ := h
  refine ⟨hrt, ?_⟩
  cases hdr : body.localDecls[r]? with
  | none => simp [hdr] at h
  | some dr =>
    cases hd : body.localDecls[t]? with
    | none => simp [hdr, hd] at h
    | some d =>
      cases hit : intTypeOf dr.ty with
      | none => simp [hdr, hd, hit] at h
      | some it =>
        cases ht : tupleTypeOf body.layouts d.ty with
        | none => simp [hdr, hd, hit, ht] at h
        | some trip =>
          obtain ⟨fields, size, align⟩ := trip
          cases hres' : resolveFieldPath body.layouts (.tuple fields size align) ps' with
          | none => simp [hdr, hd, hit, ht, hres'] at h
          | some pr' =>
            obtain ⟨off', leaf'⟩ := pr'
            cases leaf' with
            | tuple _ _ _ => simp [hdr, hd, hit, ht, hres'] at h
            | scalar it' =>
              simp only [hdr, hd, hit, ht, hres', Bool.and_eq_true, decide_eq_true_eq] at h
              obtain ⟨rfl, hpos⟩ := h
              exact ⟨dr, d, fields, size, align, off', it', rfl, rfl, hit, ht, hres', hpos⟩

/-- **Re-initialization `_t.projs = copy _r` of a scalar field from a distinct integer local `_r`,
on any allocation bytes `D` of `_t`.** -/
theorem evalStatement_reinitCopy_any {m : Mach} {ctx : Ctx} {f : Gen.Function}
    {lm : Map Gen.LocalName Ptr} {blk stmt : Nat} {A : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] A)
    {body : CapturedMir} (hfl : FnLocalsSpec body f)
    {t : Nat} {d : LocalDecl} (hd : body.localDecls[t]? = some d)
    {fields : List (Nat × TupleSpec)} {size align : Nat}
    (ht : tupleTypeOf body.layouts d.ty = some (fields, size, align))
    (hrootWf : (TupleSpec.tuple fields size align).wf = true)
    {p : Ptr} (hp : mapGet lm (localName t) = some p) {k : Nat}
    (hpk : p.provenance = some (⟨(k : Int)⟩, ())) (haddr0 : 0 ≤ p.addr)
    (haddrMax : p.addr + (size : Int) < 2 ^ 64)
    {D : List Byte} (hD : D.length = size)
    (hA : A[k]? = some (stackAlloc p.addr (itOf d body.layouts) D))
    {projs : List ProjectionElem} {pe : Gen.PlaceExpr}
    (hpe : translateFieldPlace (.Local (localName t)) projs = some pe)
    {off : Nat} {it : Gen.IntType}
    (hres : resolveFieldPath body.layouts (.tuple fields size align) projs = some (off, .scalar it))
    {r : Nat} {dr : LocalDecl} (hdr : body.localDecls[r]? = some dr)
    (hit : intTypeOf dr.ty = some it) :
    (mapGet lm (localName r) = none →
      evalStatement m (.Assign pe (.Load (.Local (localName r)))) =
        .error (.ub "access to a dead local")) ∧
    (∀ (pr : Ptr) (kr : Nat), mapGet lm (localName r) = some pr →
      pr.provenance = some (⟨(kr : Int)⟩, ()) →
      A[kr]? = some (stackAlloc pr.addr it (List.replicate it.size.bytes .Uninit)) →
      ∃ msg, evalStatement m (.Assign pe (.Load (.Local (localName r)))) = .error (.ub msg)) ∧
    (∀ (pr : Ptr) (kr : Nat) (bits : Nat), mapGet lm (localName r) = some pr →
      pr.provenance = some (⟨(kr : Int)⟩, ()) →
      bits < 2 ^ (8 * it.size.bytes) →
      A[kr]? = some (stackAlloc pr.addr it (scalarBytes it bits)) →
      ∃ m', evalStatement m (.Assign pe (.Load (.Local (localName r)))) = .ok m' ∧
        Shape m' ctx [ctx.caller, calleeFrameL f ctx lm blk stmt]
          (A.set k (stackAlloc p.addr (itOf d body.layouts) (spliceAt D off (scalarBytes it bits))))) := by
  obtain ⟨hTr, _⟩ := tyOf_int (layouts := body.layouts) hit
  have hlocr := (hfl.2 r dr hdr).2
  rw [hTr] at hlocr
  have hpeEval := evalPlace_field_any h hfl hd ht hrootWf hp hpk haddr0 haddrMax hD hA hpe hres
  obtain ⟨hleafWf, hrelBound⟩ := resolveFieldPath_wf hrootWf hres
  have hgood : GoodSize it.size.bytes := by
    simp only [TupleSpec.wf] at hleafWf
    exact (goodAlignBytes_iff it.size.bytes).mp hleafWf
  simp only [TupleSpec.toMiniRustTy] at hpeEval
  refine ⟨fun hnone => ?_, fun pr kr hpr hprk hAr => ?_, fun pr kr bits hpr hprk hbits hAr => ?_⟩
  · simp [evalStatement, hpeEval, evalValue, evalPlace_local_none h r _ hlocr hnone]
  · have hplacer := evalPlace_local_some h r _ hlocr pr hpr
    obtain ⟨msg, hmsg⟩ := typedLoad_ptr_frag_uninit h pr kr hprk (FragTy.int it hgood) hAr
    exact ⟨msg, by simp [evalStatement, hpeEval, evalValue, hplacer, placeLoad, hmsg]⟩
  · have hplacer := evalPlace_local_some h r _ hlocr pr hpr
    obtain ⟨m1, hm1, h1⟩ := typedLoad_ptr_frag h pr kr hprk (FragTy.int it hgood) bits hbits hAr
    have hv : (TupleSpec.scalar it).valOk (.scalar ⟨bits, it.size.bytes⟩) = true := by
      simp [TupleSpec.valOk, hbits]
    have hst := typedStore_ptr_tuple_slice h1 p k hpk (itOf d body.layouts) D hA off (.scalar it)
      (.scalar ⟨bits, it.size.bytes⟩) hleafWf hv (by simp [TupleSpec.size] at hrelBound ⊢; omega)
    simp only [TupleSpec.toMiniRustVal, TupleSpec.toMiniRustTy, TupleSpec.encodeVal, valBytes,
      TupleSpec.size] at hst
    simp only [valOf] at hm1
    refine ⟨withMem m1 (A.set k (stackAlloc p.addr (itOf d body.layouts)
      (spliceAt D off (scalarBytes it bits))))
      ⟨.Store, .None, (offsetPtr p off).addr, ⟨it.size.bytes⟩⟩, ?_, withMem_shape h1 _⟩
    simp [evalStatement, hpeEval, evalValue, hplacer, placeLoad, hm1, placeStore, hst]

/-- A `StepRelN` whose MiniRust side errors with UB gives a `StepRelD` for any MiniRust result
that also errors with UB. -/
theorem StepRelN.toStepRelD_ub {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {s : MachineState} {a : MirStepNode} {msg0 msg : String}
    (h : StepRelN (eraseDeinit body) f ctx s a (.error (.ub msg0))) :
    StepRelD body f ctx s a (.error (.ub msg)) := by
  unfold StepRelN at h
  unfold StepRelD
  split at h
  · obtain ⟨_, hr, _⟩ := h; cases hr
  · obtain ⟨_, _, _, hr, _⟩ := h; cases hr
  · obtain ⟨_, hr, _⟩ := h; cases hr
  · exact ⟨msg, rfl⟩
  · exact h.elim

/-- **Local-copy re-initialization step.** While `_t.ps` is a hole, `_t.ps' = copy _r` (where
`r ≠ t` is an integer local of the leaf's type and `ps'` has the hole's byte range) either faults
on `_r` in both machines or stores `_r`'s bytes over the hole in both machines, closing the hole
and restoring `StateRelN`. -/
theorem step_window_reinit_copy {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment (eraseDeinit body) = true) (hf : translateFn body = some f)
    {ctx : Ctx} {s : MachineState} {m m0 : Mach} {t : Nat} {ps : List ProjectionElem}
    (_hhole : holeAt body s.frame.blockIdx s.frame.stmtIdx = some (t, ps))
    (hN0 : StateRelN (eraseDeinit body) f ctx s m0)
    (hHR : HoleRel body f ctx s.frame.blockIdx s.frame.stmtIdx t ps m0 m)
    {bb : BasicBlockData} {r : Nat} {ps' : List ProjectionElem} {span : String}
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some ⟨.assign ⟨t, ps'⟩ (.use (.copy ⟨r, []⟩)), span⟩)
    (hrc : reinitCopyOk body t r ps' = true)
    (hrange : holeRange body t ps' = holeRange body t ps) :
    StepRelD body f ctx s (stepMirFn body s) (Interp.step m) := by
  obtain ⟨_, _, hrel0, _, _, _, _⟩ := id hN0
  obtain ⟨hphase, _, _, _, _, _, _, _, _, _⟩ := inFragment_spec _ hfrag
  obtain ⟨hrt, dr, d, fields, size, align, off', it, hdr, hd, hit, ht, hres', _⟩ :=
    reinitCopyOk_spec hrc
  obtain ⟨view, lm, p, k, rootVal, off, sz, hthr0, hlo0, _, hp, hpk, haddr0, haddrMax, hrootWf,
    _, hD0, hA0, hrng, hthrE, hactE, hallocE⟩ := holeLocal_spec hN0 hHR hd ht
  have hr' : holeRange body t ps' = some (off', it.size.bytes) := by
    simp [holeRange, hd, ht, hres', TupleSpec.size]
  rw [hr', hrng] at hrange
  simp only [Option.some.injEq, Prod.mk.injEq] at hrange
  obtain ⟨hoff, hsz⟩ := hrange
  subst off'
  subst sz
  obtain ⟨_, hrelBound⟩ := resolveFieldPath_wf hrootWf hres'
  have hoffb : off + it.size.bytes ≤ size := by simpa [TupleSpec.size] using hrelBound
  obtain ⟨tb, htb, hgetb⟩ := (translateFn_spec body f hf).2.2 _ bb hbb
  obtain ⟨hlen, hstspec, _⟩ := translateBlock_spec _ _ bb tb htb
  obtain ⟨st', hst', htst⟩ := hstspec _ _ hst
  cases ps' with
  | nil => simp [resolveFieldPath] at hres'
  | cons pe0 rest =>
    cases pe0 with
    | field idx fTy =>
      obtain ⟨pe, hpe, rfl⟩ : ∃ pe, translateFieldPlace (.Local (localName t))
          (.field idx fTy :: rest) = some pe ∧
          st' = .Assign pe (.Load (.Local (localName r))) := by
        simp only [translateStatement, translatePlace] at hst'
        cases hp' : translateFieldPlace (.Local (localName t)) (.field idx fTy :: rest) with
        | none => simp [hp', copyRv, copyOp, translateRvalue, translateOperand, translatePlace] at hst'
        | some pe =>
          refine ⟨pe, rfl, ?_⟩
          simp [hp', copyRv, copyOp, translateRvalue, translateOperand, translatePlace] at hst'
          exact hst'.symm
      have hshape0 : Shape m0 (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows)
          [(ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows).caller,
            calleeFrameL f (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows) lm
              s.frame.blockIdx s.frame.stmtIdx] m0.mem.memory.allocations :=
        ⟨hthr0, hrel0.active, rfl⟩
      have hshapeH : Shape m (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows)
          [(ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows).caller,
            calleeFrameL f (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows) lm
              s.frame.blockIdx s.frame.stmtIdx] m.mem.memory.allocations :=
        ⟨hthrE.trans hthr0, hactE.trans hrel0.active, rfl⟩
      have hk_lt : k < m0.mem.memory.allocations.length := (List.getElem?_eq_some_iff.mp hA0).1
      have hDh : (spliceAt ((TupleSpec.tuple fields size align).encodeVal rootVal) off
          (List.replicate it.size.bytes .Uninit)).length = size := by
        rw [spliceAt_length _ _ _ (by rw [List.length_replicate, hD0]; omega), hD0]
      have hAh : m.mem.memory.allocations[k]? = some (stackAlloc p.addr (itOf d body.layouts)
          (spliceAt ((TupleSpec.tuple fields size align).encodeVal rootVal) off
            (List.replicate it.size.bytes .Uninit))) := by
        rw [hallocE]; simp [hk_lt]
      have hfl := FnLocalsSpec.of_translateFn hf
      obtain ⟨hdead0, huninit0, hlive0⟩ := evalStatement_reinitCopy_any (resetPick_shape hshape0)
        hfl hd ht hrootWf hp hpk haddr0 haddrMax hD0 hA0 hpe hres' hdr hit
      obtain ⟨hdeadH, huninitH, hliveH⟩ := evalStatement_reinitCopy_any (resetPick_shape hshapeH)
        hfl hd ht hrootWf hp hpk haddr0 haddrMax hDh hAh hpe hres' hdr hit
      have hne : ((s.frame.stmtIdx : Nat) : Int) ≠ (tb.statements.length : Int) := by
        have := (List.getElem?_eq_some_iff.mp hst).1
        rw [hlen]; omega
      have hnd : ∀ st, bb.statements[s.frame.stmtIdx]? = some st → isProjDeinit st = false := by
        intro st hst2; rw [hst] at hst2; cases hst2; rfl
      have hNF := step_correspondence_NF (eraseDeinit body) f hfrag
        (fnLocalsSpec_eraseDeinit hf) ctx s m0 (blk_eraseDeinit hf hbb hnd) hN0
      rw [stepMirFn_eraseDeinit_stmt (body := body) hrel0.activeCallee hphase hbb hst rfl]
      cases hpr : mapGet lm (localName r) with
      | none =>
        have hs0 : Interp.step m0 = .error (.ub "access to a dead local") := by
          rw [step_callee hshape0 tb hgetb]
          simp [hne, listIndex_nat _ _ _ htst, hdead0 hpr]
        have hsH : Interp.step m = .error (.ub "access to a dead local") := by
          rw [step_callee hshapeH tb hgetb]
          simp [hne, listIndex_nat _ _ _ htst, hdeadH hpr]
        rw [hs0] at hNF
        rw [hsH]
        exact hNF.toStepRelD
      | some pr =>
        have hr_lt : r < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdr).1
        obtain ⟨slotr, hsVr⟩ : ∃ slot, view[r]? = some slot :=
          ⟨_, List.getElem?_eq_getElem (by rw [hlo0.nlocals]; exact hr_lt)⟩
        have hscr : scalarTypeOf dr.ty = some (.Int it) := scalarTypeOf_int hit
        obtain ⟨kr, hprk, _, _, _, _, hAr⟩ := hlo0.storage_nonptr r dr slotr pr hdr hsVr hpr
          (isPtrTy_false_of_scalarTypeOf hscr)
        simp only [eraseDeinit_layouts] at hAr
        obtain ⟨hTr, hIr⟩ := tyOf_int (layouts := body.layouts) hit
        rw [hIr] at hAr
        have hkr : kr ≠ k := by
          intro hkk; subst hkk
          exact hrt (hlo0.inj r t pr p hpr hp (by rw [hprk, hpk]))
        have hArH : m.mem.memory.allocations[kr]? =
            some (stackAlloc pr.addr it (declSlotData dr slotr body.layouts)) := by
          rw [hallocE, List.getElem?_set_ne (Ne.symm hkr)]; exact hAr
        have hslotr := (DeclSlotOk_of_scalarTypeOf hscr slotr).mp (hlo0.slots r dr slotr hdr hsVr)
        simp only [eraseDeinit_layouts] at hslotr
        rw [hTr] at hslotr
        obtain ⟨hleafWf, _⟩ := resolveFieldPath_wf hrootWf hres'
        have hgood : GoodSize it.size.bytes := by
          simp only [TupleSpec.wf] at hleafWf
          exact (goodAlignBytes_iff it.size.bytes).mp hleafWf
        have hfragd : FragTy (tyOf dr body.layouts) (itOf dr body.layouts) :=
          fragTy_of_scalarTypeOf hscr (FragTy.int it hgood)
        rw [hfragd.declSlotData, hIr] at hAr hArH
        match slotr, hslotr, hAr, hArH with
        | .dead, _, hAr, hArH =>
          obtain ⟨msg0, hev0⟩ := huninit0 pr kr hpr hprk hAr
          obtain ⟨msgH, hevH⟩ := huninitH pr kr hpr hprk hArH
          have hs0 : Interp.step m0 = .error (.ub msg0) := by
            rw [step_callee hshape0 tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hev0]
          have hsH : Interp.step m = .error (.ub msgH) := by
            rw [step_callee hshapeH tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hevH]
          rw [hs0] at hNF; rw [hsH]
          exact hNF.toStepRelD_ub
        | .uninit, _, hAr, hArH =>
          obtain ⟨msg0, hev0⟩ := huninit0 pr kr hpr hprk hAr
          obtain ⟨msgH, hevH⟩ := huninitH pr kr hpr hprk hArH
          have hs0 : Interp.step m0 = .error (.ub msg0) := by
            rw [step_callee hshape0 tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hev0]
          have hsH : Interp.step m = .error (.ub msgH) := by
            rw [step_callee hshapeH tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hevH]
          rw [hs0] at hNF; rw [hsH]
          exact hNF.toStepRelD_ub
        | .init (.scalar sc), ⟨_, hbits⟩, hAr, hArH =>
          obtain ⟨m3, hev0, h3⟩ := hlive0 pr kr sc.bits hpr hprk hbits hAr
          obtain ⟨m3h, hevH, h3h⟩ := hliveH pr kr sc.bits hpr hprk hbits hArH
          have hwlen : (scalarBytes it sc.bits).length = it.size.bytes := by
            simp [scalarBytes, leBytes_length]
          rw [spliceAt_same _ off _ _ (by rw [List.length_replicate, hD0]; omega)
            (by rw [List.length_replicate, hwlen]), hallocE, List.set_set] at h3h
          obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3
          obtain ⟨m4h, hm4h, h4h⟩ := bumpStmt_callee h3h
          have hs0 : Interp.step m0 = .ok m4 := by
            rw [step_callee hshape0 tb hgetb]
            simp [hne, listIndex_nat _ _ _ htst, hev0, hm4, check_after h4]
          have hsH : Interp.step m = .ok m4h := by
            rw [step_callee hshapeH tb hgetb]
            simp [hne, listIndex_nat _ _ _ htst, hevH, hm4h, check_after h4h]
          rw [hs0] at hNF; rw [hsH]
          exact StepRelN.toStepRelD_obs hNF (h4h.threads.trans h4.threads.symm)
            (h4h.active.trans h4.active.symm) (h4h.allocs.trans h4.allocs.symm)
        | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨_, htyT, _⟩, _, _ =>
          nomatch htyT
    | _ => simp [resolveFieldPath] at hres'

theorem localCopyWindowOk_spec {body : CapturedMir} {t r q : Nat}
    (h : localCopyWindowOk body t r q = true) :
    r ≠ t ∧ q ≠ t ∧ r ≠ q ∧
    ∃ (dr dq d : LocalDecl) (fields : List (Nat × TupleSpec)) (size align : Nat)
      (it : Gen.IntType),
      body.localDecls[r]? = some dr ∧ body.localDecls[q]? = some dq ∧
      body.localDecls[t]? = some d ∧
      intTypeOf dr.ty = some it ∧ intTypeOf dq.ty = some it ∧
      tupleTypeOf body.layouts d.ty = some (fields, size, align) ∧
      0 < it.size.bytes ∧ GoodSize it.size.bytes := by
  unfold localCopyWindowOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hrt, hqt⟩, hrq⟩, h⟩ := h
  refine ⟨hrt, hqt, hrq, ?_⟩
  cases hdr : body.localDecls[r]? with
  | none => simp [hdr] at h
  | some dr =>
    cases hdq : body.localDecls[q]? with
    | none => simp [hdr, hdq] at h
    | some dq =>
      cases hd : body.localDecls[t]? with
      | none => simp [hdr, hdq, hd] at h
      | some d =>
        cases hit : intTypeOf dr.ty with
        | none => simp [hdr, hdq, hd, hit] at h
        | some it =>
          cases hitq : intTypeOf dq.ty with
          | none => simp [hdr, hdq, hd, hit, hitq] at h
          | some it' =>
            cases ht : tupleTypeOf body.layouts d.ty with
            | none => simp [hdr, hdq, hd, hit, hitq, ht] at h
            | some trip =>
              obtain ⟨fields, size, align⟩ := trip
              simp only [hdr, hdq, hd, hit, hitq, ht, Bool.and_eq_true, decide_eq_true_eq] at h
              obtain ⟨⟨rfl, hpos⟩, hgood⟩ := h
              exact ⟨dr, dq, d, fields, size, align, it', rfl, rfl, rfl, hit, hitq, ht, hpos,
                (goodAlignBytes_iff it'.size.bytes).mp hgood⟩

/-- **Hole-independent scalar local copy `_r = copy _q` between two integer locals of type `it`.** -/
theorem evalStatement_localCopy_any {m : Mach} {ctx : Ctx} {f : Gen.Function}
    {lm : Map Gen.LocalName Ptr} {blk stmt : Nat} {A : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] A)
    {body : CapturedMir} (hfl : FnLocalsSpec body f)
    {r q : Nat} {dr dq : LocalDecl} {it : Gen.IntType}
    (hdr : body.localDecls[r]? = some dr) (hdq : body.localDecls[q]? = some dq)
    (hit : intTypeOf dr.ty = some it) (hitq : intTypeOf dq.ty = some it)
    (hgood : GoodSize it.size.bytes) :
    (mapGet lm (localName r) = none →
      evalStatement m (.Assign (.Local (localName r)) (.Load (.Local (localName q)))) =
        .error (.ub "access to a dead local")) ∧
    (∀ (pr : Ptr), mapGet lm (localName r) = some pr →
      mapGet lm (localName q) = none →
      evalStatement m (.Assign (.Local (localName r)) (.Load (.Local (localName q)))) =
        .error (.ub "access to a dead local")) ∧
    (∀ (pr pq : Ptr) (kq : Nat), mapGet lm (localName r) = some pr →
      mapGet lm (localName q) = some pq →
      pq.provenance = some (⟨(kq : Int)⟩, ()) →
      A[kq]? = some (stackAlloc pq.addr it (List.replicate it.size.bytes .Uninit)) →
      ∃ msg, evalStatement m (.Assign (.Local (localName r)) (.Load (.Local (localName q)))) =
        .error (.ub msg)) ∧
    (∀ (pr pq : Ptr) (kr kq : Nat) (Dr : List Byte) (bits : Nat),
      mapGet lm (localName r) = some pr →
      mapGet lm (localName q) = some pq →
      pr.provenance = some (⟨(kr : Int)⟩, ()) →
      pq.provenance = some (⟨(kq : Int)⟩, ()) →
      bits < 2 ^ (8 * it.size.bytes) →
      A[kq]? = some (stackAlloc pq.addr it (scalarBytes it bits)) →
      A[kr]? = some (stackAlloc pr.addr it Dr) →
      Dr.length = it.size.bytes →
      ∃ m', evalStatement m (.Assign (.Local (localName r)) (.Load (.Local (localName q)))) =
          .ok m' ∧
        Shape m' ctx [ctx.caller, calleeFrameL f ctx lm blk stmt]
          (A.set kr (stackAlloc pr.addr it (scalarBytes it bits)))) := by
  obtain ⟨hTr, _⟩ := tyOf_int (layouts := body.layouts) hit
  obtain ⟨hTq, _⟩ := tyOf_int (layouts := body.layouts) hitq
  have hlocr := (hfl.2 r dr hdr).2
  have hlocq := (hfl.2 q dq hdq).2
  rw [hTr] at hlocr
  rw [hTq] at hlocq
  refine ⟨fun hnone => ?_, fun pr hpr hnoneq => ?_, fun pr pq kq hpr hpq hpqk hAq => ?_,
    fun pr pq kr kq Dr bits hpr hpq hprk hpqk hbits hAq hAr hlenr => ?_⟩
  · simp [evalStatement, evalPlace_local_none h r _ hlocr hnone]
  · simp [evalStatement, evalPlace_local_some h r _ hlocr pr hpr, evalValue,
      evalPlace_local_none h q _ hlocq hnoneq]
  · have hplacer := evalPlace_local_some h r _ hlocr pr hpr
    have hplaceq := evalPlace_local_some h q _ hlocq pq hpq
    obtain ⟨msg, hmsg⟩ := typedLoad_ptr_frag_uninit h pq kq hpqk (FragTy.int it hgood) hAq
    exact ⟨msg, by simp [evalStatement, hplacer, evalValue, hplaceq, placeLoad, hmsg]⟩
  · have hplacer := evalPlace_local_some h r _ hlocr pr hpr
    have hplaceq := evalPlace_local_some h q _ hlocq pq hpq
    obtain ⟨m1, hm1, h1⟩ := typedLoad_ptr_frag h pq kq hpqk (FragTy.int it hgood) bits hbits hAq
    have hst := typedStore_ptr_frag h1 pr kr hprk (FragTy.int it hgood) Dr bits hbits hAr hlenr
    simp only [valOf] at hm1 hst
    refine ⟨withMem m1 (A.set kr (stackAlloc pr.addr it (scalarBytes it bits)))
      ⟨.Store, .None, pr.addr, it.size⟩, ?_, withMem_shape h1 _⟩
    simp [evalStatement, hplacer, evalValue, hplaceq, placeLoad, hm1, placeStore, hst]

/-- **Hole-independent scalar local copy step.** While `_t.ps` is a hole, `_r = copy _q` (where
`r ≠ t`, `q ≠ t`, `r ≠ q` are integer locals of the same type `it`) either faults on `_r` or `_q`
in both machines or copies `_q`'s bytes into `_r`'s allocation in both machines while leaving the
open hole on `_t.ps` untouched. -/
theorem step_window_local_copy {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment (eraseDeinit body) = true) (hf : translateFn body = some f)
    {ctx : Ctx} {s : MachineState} {m m0 : Mach} {t : Nat} {ps : List ProjectionElem}
    (hhole : holeAt body s.frame.blockIdx s.frame.stmtIdx = some (t, ps))
    (hN0 : StateRelN (eraseDeinit body) f ctx s m0)
    (hHR : HoleRel body f ctx s.frame.blockIdx s.frame.stmtIdx t ps m0 m)
    {bb : BasicBlockData} {r q : Nat} {span : String}
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some ⟨.assign ⟨r, []⟩ (.use (.copy ⟨q, []⟩)), span⟩)
    (hlc : localCopyWindowOk body t r q = true) :
    StepRelD body f ctx s (stepMirFn body s) (Interp.step m) := by
  obtain ⟨_, _, hrel0, _, _, _, _⟩ := id hN0
  obtain ⟨hphase, _, _, _, _, _, _, _, _, _⟩ := inFragment_spec _ hfrag
  obtain ⟨hrt, hqt, _hrq, dr, dq, d, fields, size, align, it, hdr, hdq, hd, hit, hitq, ht, _,
    hgood⟩ := localCopyWindowOk_spec hlc
  obtain ⟨view, lm, p, k, rootVal, off, sz, hthr0, hlo0, _, hp, hpk, _, _, _, _, _, hA0, hrng,
    hthrE, hactE, hallocE⟩ := holeLocal_spec hN0 hHR hd ht
  obtain ⟨tb, htb, hgetb⟩ := (translateFn_spec body f hf).2.2 _ bb hbb
  obtain ⟨hlen, hstspec, _⟩ := translateBlock_spec _ _ bb tb htb
  obtain ⟨st', hst', htst⟩ := hstspec _ _ hst
  have hstEq : st' = .Assign (.Local (localName r)) (.Load (.Local (localName q))) := by
    simp [translateStatement, translatePlace, copyRv, copyOp, translateRvalue, translateOperand] at hst'
    exact hst'.symm
  subst hstEq
  have hshape0 : Shape m0 (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows)
      [(ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows).caller,
        calleeFrameL f (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows) lm
          s.frame.blockIdx s.frame.stmtIdx] m0.mem.memory.allocations :=
    ⟨hthr0, hrel0.active, rfl⟩
  have hshapeH : Shape m (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows)
      [(ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows).caller,
        calleeFrameL f (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows) lm
          s.frame.blockIdx s.frame.stmtIdx] m.mem.memory.allocations :=
    ⟨hthrE.trans hthr0, hactE.trans hrel0.active, rfl⟩
  have hfl := FnLocalsSpec.of_translateFn hf
  obtain ⟨hdeadR0, hdeadQ0, huninitQ0, hlive0⟩ :=
    evalStatement_localCopy_any (resetPick_shape hshape0) hfl hdr hdq hit hitq hgood
  obtain ⟨hdeadRH, hdeadQH, huninitQH, hliveH⟩ :=
    evalStatement_localCopy_any (resetPick_shape hshapeH) hfl hdr hdq hit hitq hgood
  have hne : ((s.frame.stmtIdx : Nat) : Int) ≠ (tb.statements.length : Int) := by
    have := (List.getElem?_eq_some_iff.mp hst).1
    rw [hlen]; omega
  have hnd : ∀ st, bb.statements[s.frame.stmtIdx]? = some st → isProjDeinit st = false := by
    intro st hst2; rw [hst] at hst2; cases hst2; rfl
  have hNF := step_correspondence_NF (eraseDeinit body) f hfrag
    (fnLocalsSpec_eraseDeinit hf) ctx s m0 (blk_eraseDeinit hf hbb hnd) hN0
  rw [stepMirFn_eraseDeinit_stmt (body := body) hrel0.activeCallee hphase hbb hst rfl]
  cases hpr : mapGet lm (localName r) with
  | none =>
    have hs0 : Interp.step m0 = .error (.ub "access to a dead local") := by
      rw [step_callee hshape0 tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hdeadR0 hpr]
    have hsH : Interp.step m = .error (.ub "access to a dead local") := by
      rw [step_callee hshapeH tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hdeadRH hpr]
    rw [hs0] at hNF; rw [hsH]
    exact hNF.toStepRelD
  | some pr =>
    cases hpq : mapGet lm (localName q) with
    | none =>
      have hs0 : Interp.step m0 = .error (.ub "access to a dead local") := by
        rw [step_callee hshape0 tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hdeadQ0 pr hpr hpq]
      have hsH : Interp.step m = .error (.ub "access to a dead local") := by
        rw [step_callee hshapeH tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hdeadQH pr hpr hpq]
      rw [hs0] at hNF; rw [hsH]
      exact hNF.toStepRelD
    | some pq =>
      have hr_lt : r < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdr).1
      have hq_lt : q < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdq).1
      obtain ⟨slotr, hsVr⟩ : ∃ slot, view[r]? = some slot :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlo0.nlocals]; exact hr_lt)⟩
      obtain ⟨slotq, hsVq⟩ : ∃ slot, view[q]? = some slot :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlo0.nlocals]; exact hq_lt)⟩
      have hscr : scalarTypeOf dr.ty = some (.Int it) := scalarTypeOf_int hit
      have hscq : scalarTypeOf dq.ty = some (.Int it) := scalarTypeOf_int hitq
      obtain ⟨kr, hprk, _, _, _, _, hAr⟩ := hlo0.storage_nonptr r dr slotr pr hdr hsVr hpr
        (isPtrTy_false_of_scalarTypeOf hscr)
      obtain ⟨kq, hpqk, _, _, _, _, hAq⟩ := hlo0.storage_nonptr q dq slotq pq hdq hsVq hpq
        (isPtrTy_false_of_scalarTypeOf hscq)
      simp only [eraseDeinit_layouts] at hAr hAq
      obtain ⟨hTr, hIr⟩ := tyOf_int (layouts := body.layouts) hit
      obtain ⟨hTq, hIq⟩ := tyOf_int (layouts := body.layouts) hitq
      rw [hIr] at hAr
      rw [hIq] at hAq
      have hlenr : (declSlotData dr slotr body.layouts).length = it.size.bytes := by
        rw [declSlotData_length (by rw [hTr]; exact hscr), hTr]; rfl
      have hkr : kr ≠ k := by
        intro hkk; subst hkk
        exact hrt (hlo0.inj r t pr p hpr hp (by rw [hprk, hpk]))
      have hkq : kq ≠ k := by
        intro hkk; subst hkk
        exact hqt (hlo0.inj q t pq p hpq hp (by rw [hpqk, hpk]))
      have hArH : m.mem.memory.allocations[kr]? =
          some (stackAlloc pr.addr it (declSlotData dr slotr body.layouts)) := by
        rw [hallocE, List.getElem?_set_ne (Ne.symm hkr)]; exact hAr
      have hAqH : m.mem.memory.allocations[kq]? =
          some (stackAlloc pq.addr it (declSlotData dq slotq body.layouts)) := by
        rw [hallocE, List.getElem?_set_ne (Ne.symm hkq)]; exact hAq
      have hslotq := (DeclSlotOk_of_scalarTypeOf hscq slotq).mp (hlo0.slots q dq slotq hdq hsVq)
      simp only [eraseDeinit_layouts] at hslotq
      rw [hTq] at hslotq
      have hfragdq : FragTy (tyOf dq body.layouts) (itOf dq body.layouts) :=
        fragTy_of_scalarTypeOf hscq (FragTy.int it hgood)
      rw [hfragdq.declSlotData, hIq] at hAq hAqH
      match slotq, hslotq, hAq, hAqH with
      | .dead, _, hAq, hAqH =>
        obtain ⟨msg0, hev0⟩ := huninitQ0 pr pq kq hpr hpq hpqk hAq
        obtain ⟨msgH, hevH⟩ := huninitQH pr pq kq hpr hpq hpqk hAqH
        have hs0 : Interp.step m0 = .error (.ub msg0) := by
          rw [step_callee hshape0 tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hev0]
        have hsH : Interp.step m = .error (.ub msgH) := by
          rw [step_callee hshapeH tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hevH]
        rw [hs0] at hNF; rw [hsH]
        exact hNF.toStepRelD_ub
      | .uninit, _, hAq, hAqH =>
        obtain ⟨msg0, hev0⟩ := huninitQ0 pr pq kq hpr hpq hpqk hAq
        obtain ⟨msgH, hevH⟩ := huninitQH pr pq kq hpr hpq hpqk hAqH
        have hs0 : Interp.step m0 = .error (.ub msg0) := by
          rw [step_callee hshape0 tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hev0]
        have hsH : Interp.step m = .error (.ub msgH) := by
          rw [step_callee hshapeH tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hevH]
        rw [hs0] at hNF; rw [hsH]
        exact hNF.toStepRelD_ub
      | .init (.scalar sc), ⟨_, hbits⟩, hAq, hAqH =>
        obtain ⟨m3, hev0, h3⟩ := hlive0 pr pq kr kq _ sc.bits hpr hpq hprk hpqk hbits hAq hAr hlenr
        obtain ⟨m3h, hevH, h3h⟩ := hliveH pr pq kr kq _ sc.bits hpr hpq hprk hpqk hbits hAqH hArH hlenr
        obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3
        obtain ⟨m4h, hm4h, h4h⟩ := bumpStmt_callee h3h
        have hs0 : Interp.step m0 = .ok m4 := by
          rw [step_callee hshape0 tb hgetb]
          simp [hne, listIndex_nat _ _ _ htst, hev0, hm4, check_after h4]
        have hsH : Interp.step m = .ok m4h := by
          rw [step_callee hshapeH tb hgetb]
          simp [hne, listIndex_nat _ _ _ htst, hevH, hm4h, check_after h4h]
        rw [hs0] at hNF; rw [hsH]
        have hhole' : holeAt body s.frame.blockIdx (s.frame.stmtIdx + 1) = some (t, ps) := by
          rw [holeAt_succ hbb hst, hhole]
          simp [holeAfter, hrt]
        refine StepRelN.toStepRelD_hole hNF h4.threads hhole' hp hpk
          (by rw [h4.allocs, List.getElem?_set_ne hkr]; exact hA0) hrng
          (h4h.threads.trans h4.threads.symm) (h4h.active.trans h4.active.symm) ?_
        rw [h4h.allocs, h4.allocs, hallocE]
        exact List.set_comm _ _ (Ne.symm hkr)
      | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨_, htyT, _⟩, _, _ =>
        nomatch htyT

/-! ## Cast sibling reads and binary-operation re-initializations

A sibling read through an integer cast (`castSiblingReadOk`) loads the same disjoint field bytes from
the hole-free and the actual machine and casts them alike (`evalStatement_castSiblingRead_any`); a
binary-operation re-initialization (`reinitBinOpOk`) loads the same hole-independent local `_q`
(whose allocation is not `_t`'s) on both machines, computes the same `intBinEval` result or the same
UB, and stores the same bytes over the hole (`evalStatement_reinitBinOp_any`, `spliceAt_same`). -/

theorem castSiblingReadOk_spec {body : CapturedMir} {t r : Nat} {ps ps' : List ProjectionElem}
    {castTy : MirAst.Ty} (h : castSiblingReadOk body t r ps ps' castTy = true) :
    r ≠ t ∧ (∃ it'', operandType body.layouts body.localDecls (.copy ⟨t, ps'⟩) = some (.Int it'')) ∧
    ∃ (dr d : LocalDecl) (fields : List (Nat × TupleSpec)) (size align : Nat)
      (it it' : Gen.IntType) (off : Nat) (leaf : TupleSpec) (off' : Nat),
      body.localDecls[r]? = some dr ∧ body.localDecls[t]? = some d ∧ intTypeOf dr.ty = some it ∧
      intTypeOf castTy = some it ∧
      tupleTypeOf body.layouts d.ty = some (fields, size, align) ∧ GoodSize it.size.bytes ∧
      resolveFieldPath body.layouts (.tuple fields size align) ps = some (off, leaf) ∧
      resolveFieldPath body.layouts (.tuple fields size align) ps' = some (off', .scalar it') ∧
      (off' + it'.size.bytes ≤ off ∨ off + leaf.size ≤ off') := by
  unfold castSiblingReadOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hrt, hop⟩, h⟩ := h
  refine ⟨hrt, ?_, ?_⟩
  · revert hop
    cases operandType body.layouts body.localDecls (.copy ⟨t, ps'⟩) with
    | none => intro hop; simp at hop
    | some T =>
      cases T with
      | Int it'' => intro _; exact ⟨it'', rfl⟩
      | _ => intro hop; simp at hop
  cases hdr : body.localDecls[r]? with
  | none => simp [hdr] at h
  | some dr =>
    cases hd : body.localDecls[t]? with
    | none => simp [hdr, hd] at h
    | some d =>
      cases hit : intTypeOf dr.ty with
      | none => simp [hdr, hd, hit] at h
      | some it =>
        cases hct : intTypeOf castTy with
        | none => simp [hdr, hd, hit, hct] at h
        | some ct =>
          cases ht : tupleTypeOf body.layouts d.ty with
          | none => simp [hdr, hd, hit, hct, ht] at h
          | some trip =>
            obtain ⟨fields, size, align⟩ := trip
            cases hres : resolveFieldPath body.layouts (.tuple fields size align) ps with
            | none => simp [hdr, hd, hit, hct, ht, hres] at h
            | some pr =>
              obtain ⟨off, leaf⟩ := pr
              cases hres' : resolveFieldPath body.layouts (.tuple fields size align) ps' with
              | none => simp [hdr, hd, hit, hct, ht, hres, hres'] at h
              | some pr' =>
                obtain ⟨off', leaf'⟩ := pr'
                cases leaf' with
                | tuple _ _ _ => simp [hdr, hd, hit, hct, ht, hres, hres'] at h
                | scalar it' =>
                  simp only [hdr, hd, hit, hct, ht, hres, hres', Bool.and_eq_true,
                    decide_eq_true_eq, Bool.or_eq_true] at h
                  obtain ⟨⟨rfl, hgood⟩, hdis⟩ := h
                  exact ⟨dr, d, fields, size, align, ct, it', off, leaf, off', rfl, rfl, hit, rfl,
                    ht, (goodAlignBytes_iff ct.size.bytes).mp hgood, hres, hres', hdis⟩

theorem reinitBinOpOk_spec {body : CapturedMir} {t q : Nat} {ps' : List ProjectionElem}
    {op : MirAst.BinOp} {c : ConstOperand} (h : reinitBinOpOk body t q ps' op c = true) :
    q ≠ t ∧ translateRelOp op = none ∧
    ∃ (dq d : LocalDecl) (fields : List (Nat × TupleSpec)) (size align off' : Nat)
      (it : Gen.IntType) (iop : Gen.IntBinOp) (cbits : Nat),
      body.localDecls[q]? = some dq ∧ body.localDecls[t]? = some d ∧ intTypeOf dq.ty = some it ∧
      tupleTypeOf body.layouts d.ty = some (fields, size, align) ∧
      resolveFieldPath body.layouts (.tuple fields size align) ps' = some (off', .scalar it) ∧
      0 < it.size.bytes ∧ translateBinOp op = some iop ∧ cbits < 2 ^ (8 * it.size.bytes) ∧
      translateOperand body.localDecls (.constant c) =
        some (.Constant (.Int (intFromBits cbits it)) (.Int it)) := by
  unfold reinitBinOpOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hqt, hrel⟩, hbin⟩, h⟩ := h
  have hrel' : translateRelOp op = none := Option.isNone_iff_eq_none.mp hrel
  obtain ⟨iop, hiop⟩ := Option.isSome_iff_exists.mp hbin
  refine ⟨hqt, hrel', ?_⟩
  cases hdq : body.localDecls[q]? with
  | none => simp [hdq] at h
  | some dq =>
    cases hd : body.localDecls[t]? with
    | none => simp [hdq, hd] at h
    | some d =>
      cases hit : intTypeOf dq.ty with
      | none => simp [hdq, hd, hit] at h
      | some it =>
        cases ht : tupleTypeOf body.layouts d.ty with
        | none => simp [hdq, hd, hit, ht] at h
        | some trip =>
          obtain ⟨fields, size, align⟩ := trip
          cases hres' : resolveFieldPath body.layouts (.tuple fields size align) ps' with
          | none => simp [hdq, hd, hit, ht, hres'] at h
          | some pr' =>
            obtain ⟨off', leaf'⟩ := pr'
            cases leaf' with
            | tuple _ _ _ => simp [hdq, hd, hit, ht, hres'] at h
            | scalar it' =>
              obtain ⟨cty, cval⟩ := c
              cases cval with
              | scalar cs =>
                cases cs with
                | int sc =>
                  obtain ⟨cbits, csz⟩ := sc
                  cases hcit : intTypeOf cty with
                  | none => simp [hdq, hd, hit, ht, hres', hcit] at h
                  | some ic =>
                    simp only [hdq, hd, hit, ht, hres', hcit, Bool.and_eq_true, decide_eq_true_eq,
                      Bool.not_eq_true'] at h
                    obtain ⟨⟨⟨rfl, hpos⟩, hnb⟩, ⟨rfl, rfl⟩, hcbits⟩ := h
                    refine ⟨dq, d, fields, size, align, off', _, iop, cbits, rfl, rfl, hit, ht,
                      hres', hpos, hiop, hcbits, ?_⟩
                    simp [translateOperand, hnb, hcit, hcbits]
                | ptr _ _ => simp [hdq, hd, hit, ht, hres'] at h
              | _ => simp [hdq, hd, hit, ht, hres'] at h

/-- **Sibling read through an integer cast `_r = Cast(IntToInt, copy _t.projs, it)` of a scalar
field of integer type `it'`, on any allocation bytes `D` whose field slice encodes the field's
value**: `_r`'s place is evaluated first (a dead `_r` is UB), then the field is loaded, cast to
`it` (`bring_in_bounds`), and stored into `_r`'s allocation. -/
theorem evalStatement_castSiblingRead_any {m : Mach} {ctx : Ctx} {f : Gen.Function}
    {lm : Map Gen.LocalName Ptr} {blk stmt : Nat} {A : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] A)
    {body : CapturedMir} (hfl : FnLocalsSpec body f)
    {t : Nat} {d : LocalDecl} (hd : body.localDecls[t]? = some d)
    {fields : List (Nat × TupleSpec)} {size align : Nat}
    (ht : tupleTypeOf body.layouts d.ty = some (fields, size, align))
    (hrootWf : (TupleSpec.tuple fields size align).wf = true)
    {p : Ptr} (hp : mapGet lm (localName t) = some p) {k : Nat}
    (hpk : p.provenance = some (⟨(k : Int)⟩, ())) (haddr0 : 0 ≤ p.addr)
    (haddrMax : p.addr + (size : Int) < 2 ^ 64)
    {D : List Byte} (hD : D.length = size)
    (hA : A[k]? = some (stackAlloc p.addr (itOf d body.layouts) D))
    {projs : List ProjectionElem} {pe : Gen.PlaceExpr}
    (hpe : translateFieldPlace (.Local (localName t)) projs = some pe)
    {off : Nat} {it' : Gen.IntType}
    (hres : resolveFieldPath body.layouts (.tuple fields size align) projs = some (off, .scalar it'))
    {bits : Nat} (hbits : bits < 2 ^ (8 * it'.size.bytes))
    (hslice : (D.drop off).take it'.size.bytes = scalarBytes it' bits)
    {r : Nat} {dr : LocalDecl} (hdr : body.localDecls[r]? = some dr) {it : Gen.IntType}
    (hit : intTypeOf dr.ty = some it) (hgood : GoodSize it.size.bytes) :
    (mapGet lm (localName r) = none →
      evalStatement m (.Assign (.Local (localName r)) (.UnOp (.Cast (.IntToInt it)) (.Load pe))) =
        .error (.ub "access to a dead local")) ∧
    (∀ (pr : Ptr) (kr : Nat) (Dr : List Byte), mapGet lm (localName r) = some pr →
      pr.provenance = some (⟨(kr : Int)⟩, ()) →
      A[kr]? = some (stackAlloc pr.addr it Dr) → Dr.length = it.size.bytes →
      ∃ m', evalStatement m
          (.Assign (.Local (localName r)) (.UnOp (.Cast (.IntToInt it)) (.Load pe))) = .ok m' ∧
        Shape m' ctx [ctx.caller, calleeFrameL f ctx lm blk stmt]
          (A.set kr (stackAlloc pr.addr it
            (scalarBytes it (intFromBits bits it' % 2 ^ (8 * it.size.bytes)).toNat)))) := by
  obtain ⟨hTr, _⟩ := tyOf_int (layouts := body.layouts) hit
  have hlocr := (hfl.2 r dr hdr).2
  rw [hTr] at hlocr
  have hpeEval := evalPlace_field_any h hfl hd ht hrootWf hp hpk haddr0 haddrMax hD hA hpe hres
  obtain ⟨hleafWf, hrelBound⟩ := resolveFieldPath_wf hrootWf hres
  have hv : (TupleSpec.scalar it').valOk (.scalar ⟨bits, it'.size.bytes⟩) = true := by
    simp [TupleSpec.valOk, hbits]
  obtain ⟨m1, hm1, h1⟩ := typedLoad_ptr_tuple_slice h p k hpk (itOf d body.layouts) D hA off
    (.scalar it') (.scalar ⟨bits, it'.size.bytes⟩) hleafWf hv
    (by simp [TupleSpec.size] at hrelBound ⊢; omega) (by simpa [TupleSpec.encodeVal, valBytes,
      TupleSpec.size] using hslice)
  simp only [TupleSpec.toMiniRustVal, TupleSpec.toMiniRustTy] at hm1 hpeEval
  have hpos := two_pow_pos (8 * it.size.bytes)
  have hlt : (intFromBits bits it' % 2 ^ (8 * it.size.bytes)).toNat < 2 ^ (8 * it.size.bytes) := by
    have h0 := Int.emod_nonneg (intFromBits bits it') (Int.ne_of_gt hpos)
    have hlt' := Int.emod_lt_of_pos (intFromBits bits it') hpos
    have : (((intFromBits bits it' % 2 ^ (8 * it.size.bytes)).toNat : Int)) <
        2 ^ (8 * it.size.bytes) := by
      rw [Int.toNat_of_nonneg h0]; exact hlt'
    exact_mod_cast this
  refine ⟨fun hnone => ?_, fun pr kr Dr hpr hprk hAr hlen => ?_⟩
  · rw [evalStatement, evalPlace_local_none h r _ hlocr hnone]
    rfl
  · have hst := typedStore_ptr_frag h1 pr kr hprk (FragTy.int it hgood) Dr _ hlt hAr hlen
    refine ⟨withMem m1 (A.set kr (stackAlloc pr.addr it
      (scalarBytes it (intFromBits bits it' % 2 ^ (8 * it.size.bytes)).toNat)))
      ⟨.Store, .None, pr.addr, it.size⟩, ?_, withMem_shape h1 _⟩
    simp only [valOf] at hst
    simp [evalStatement, evalPlace_local_some h r _ hlocr pr hpr, evalValue, hpeEval, placeLoad,
      hm1, evalUnOp, evalCastOp, bringInBounds_eq_intFromBits it hgood, placeStore, hst]

/-- **Re-initialization `_t.projs = BinOp(iop, copy _q, const c)` of a scalar field of integer type
`it` by an integer operation of a distinct integer local `_q` of type `it` and a constant of type
`it`, on any allocation bytes `D` of `_t`**: `_t.projs` is evaluated first, then `_q` is loaded (a
dead or uninitialized `_q` is UB), the operation is evaluated (`intBinEval`: UB exactly when it is
`none`), and the in-bounds result is stored over the field's bytes. -/
theorem evalStatement_reinitBinOp_any {m : Mach} {ctx : Ctx} {f : Gen.Function}
    {lm : Map Gen.LocalName Ptr} {blk stmt : Nat} {A : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] A)
    {body : CapturedMir} (hfl : FnLocalsSpec body f)
    {t : Nat} {d : LocalDecl} (hd : body.localDecls[t]? = some d)
    {fields : List (Nat × TupleSpec)} {size align : Nat}
    (ht : tupleTypeOf body.layouts d.ty = some (fields, size, align))
    (hrootWf : (TupleSpec.tuple fields size align).wf = true)
    {p : Ptr} (hp : mapGet lm (localName t) = some p) {k : Nat}
    (hpk : p.provenance = some (⟨(k : Int)⟩, ())) (haddr0 : 0 ≤ p.addr)
    (haddrMax : p.addr + (size : Int) < 2 ^ 64)
    {D : List Byte} (hD : D.length = size)
    (hA : A[k]? = some (stackAlloc p.addr (itOf d body.layouts) D))
    {projs : List ProjectionElem} {pe : Gen.PlaceExpr}
    (hpe : translateFieldPlace (.Local (localName t)) projs = some pe)
    {off : Nat} {it : Gen.IntType}
    (hres : resolveFieldPath body.layouts (.tuple fields size align) projs = some (off, .scalar it))
    {q : Nat} {dq : LocalDecl} (hdq : body.localDecls[q]? = some dq)
    (hitq : intTypeOf dq.ty = some it)
    {op : MirAst.BinOp} {iop : Gen.IntBinOp} (hiop : translateBinOp op = some iop)
    (cbits : Nat) :
    (mapGet lm (localName q) = none →
      evalStatement m (.Assign pe (.BinOp (.Int iop) (.Load (.Local (localName q)))
        (.Constant (.Int (intFromBits cbits it)) (.Int it)))) =
        .error (.ub "access to a dead local")) ∧
    (∀ (pq : Ptr) (kq : Nat), mapGet lm (localName q) = some pq →
      pq.provenance = some (⟨(kq : Int)⟩, ()) →
      A[kq]? = some (stackAlloc pq.addr it (List.replicate it.size.bytes .Uninit)) →
      ∃ msg, evalStatement m (.Assign pe (.BinOp (.Int iop) (.Load (.Local (localName q)))
        (.Constant (.Int (intFromBits cbits it)) (.Int it)))) = .error (.ub msg)) ∧
    (∀ (pq : Ptr) (kq : Nat) (bits : Nat), mapGet lm (localName q) = some pq →
      pq.provenance = some (⟨(kq : Int)⟩, ()) →
      bits < 2 ^ (8 * it.size.bytes) →
      A[kq]? = some (stackAlloc pq.addr it (scalarBytes it bits)) →
      (intBinEval iop (intFromBits bits it) (intFromBits cbits it) it = none →
        ∃ msg, evalStatement m (.Assign pe (.BinOp (.Int iop) (.Load (.Local (localName q)))
          (.Constant (.Int (intFromBits cbits it)) (.Int it)))) = .error (.ub msg)) ∧
      (∀ z, intBinEval iop (intFromBits bits it) (intFromBits cbits it) it = some z →
        ∃ m', evalStatement m (.Assign pe (.BinOp (.Int iop) (.Load (.Local (localName q)))
            (.Constant (.Int (intFromBits cbits it)) (.Int it)))) = .ok m' ∧
          Shape m' ctx [ctx.caller, calleeFrameL f ctx lm blk stmt]
            (A.set k (stackAlloc p.addr (itOf d body.layouts)
              (spliceAt D off (scalarBytes it (z % 2 ^ (8 * it.size.bytes)).toNat)))))) := by
  obtain ⟨hTq, _⟩ := tyOf_int (layouts := body.layouts) hitq
  have hlocq := (hfl.2 q dq hdq).2
  rw [hTq] at hlocq
  have hpeEval := evalPlace_field_any h hfl hd ht hrootWf hp hpk haddr0 haddrMax hD hA hpe hres
  obtain ⟨hleafWf, hrelBound⟩ := resolveFieldPath_wf hrootWf hres
  have hgood : GoodSize it.size.bytes := by
    simp only [TupleSpec.wf] at hleafWf
    exact (goodAlignBytes_iff it.size.bytes).mp hleafWf
  simp only [TupleSpec.toMiniRustTy] at hpeEval
  refine ⟨fun hnone => ?_, fun pq kq hpq hpqk hAq => ?_, fun pq kq bits hpq hpqk hbits hAq => ?_⟩
  · simp [evalStatement, hpeEval, evalValue, evalPlace_local_none h q _ hlocq hnone]
  · have hplaceq := evalPlace_local_some h q _ hlocq pq hpq
    obtain ⟨msg, hmsg⟩ := typedLoad_ptr_frag_uninit h pq kq hpqk (FragTy.int it hgood) hAq
    exact ⟨msg, by simp [evalStatement, hpeEval, evalValue, hplaceq, placeLoad, hmsg]⟩
  · have hplaceq := evalPlace_local_some h q _ hlocq pq hpq
    obtain ⟨m1, hm1, h1⟩ := typedLoad_ptr_frag h pq kq hpqk (FragTy.int it hgood) bits hbits hAq
    simp only [valOf] at hm1
    obtain ⟨hevalOk, hevalNone⟩ :=
      evalIntBinOp_spec op iop hiop (intFromBits bits it) (intFromBits cbits it) it
    refine ⟨fun hz => ?_, fun z hz => ?_⟩
    · obtain ⟨msg, hmsg⟩ := hevalNone hz
      exact ⟨msg, by simp [evalStatement, hpeEval, evalValue, hplaceq, placeLoad, hm1,
        evalConstant, evalBinOp, hmsg]⟩
    · have hpos := two_pow_pos (8 * it.size.bytes)
      have hlt : (z % 2 ^ (8 * it.size.bytes)).toNat < 2 ^ (8 * it.size.bytes) := by
        have h0 := Int.emod_nonneg z (Int.ne_of_gt hpos)
        have hlt' := Int.emod_lt_of_pos z hpos
        have : ((z % 2 ^ (8 * it.size.bytes)).toNat : Int) < 2 ^ (8 * it.size.bytes) := by
          rw [Int.toNat_of_nonneg h0]; exact hlt'
        exact_mod_cast this
      have hv : (TupleSpec.scalar it).valOk
          (.scalar ⟨(z % 2 ^ (8 * it.size.bytes)).toNat, it.size.bytes⟩) = true := by
        simp [TupleSpec.valOk, hlt]
      have hst := typedStore_ptr_tuple_slice h1 p k hpk (itOf d body.layouts) D hA off (.scalar it)
        (.scalar ⟨(z % 2 ^ (8 * it.size.bytes)).toNat, it.size.bytes⟩) hleafWf hv
        (by simp [TupleSpec.size] at hrelBound ⊢; omega)
      simp only [TupleSpec.toMiniRustVal, TupleSpec.toMiniRustTy, TupleSpec.encodeVal, valBytes,
        TupleSpec.size] at hst
      refine ⟨withMem m1 (A.set k (stackAlloc p.addr (itOf d body.layouts)
        (spliceAt D off (scalarBytes it (z % 2 ^ (8 * it.size.bytes)).toNat))))
        ⟨.Store, .None, (offsetPtr p off).addr, ⟨it.size.bytes⟩⟩, ?_, withMem_shape h1 _⟩
      simp [evalStatement, hpeEval, evalValue, hplaceq, placeLoad, hm1, evalConstant, evalBinOp,
        hevalOk z hz, bringInBounds_eq_intFromBits it hgood z, placeStore, hst]

/-- **Cast sibling-read step.** While `_t.ps` is a hole, `_r = Cast(IntToInt, copy _t.ps', it)` of a
disjoint scalar field reads the same bytes from the hole-free machine and from the machine with the
hole, casts them alike, and stores into `_r`'s allocation, which is not `_t`'s: the hole stays
open. -/
theorem step_window_cast_read {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment (eraseDeinit body) = true) (hf : translateFn body = some f)
    {ctx : Ctx} {s : MachineState} {m m0 : Mach} {t : Nat} {ps : List ProjectionElem}
    (hhole : holeAt body s.frame.blockIdx s.frame.stmtIdx = some (t, ps))
    (hN0 : StateRelN (eraseDeinit body) f ctx s m0)
    (hHR : HoleRel body f ctx s.frame.blockIdx s.frame.stmtIdx t ps m0 m)
    {bb : BasicBlockData} {r : Nat} {ps' : List ProjectionElem} {castTy : MirAst.Ty}
    {span : String}
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? =
      some ⟨.assign ⟨r, []⟩ (.cast .intToInt (.copy ⟨t, ps'⟩) castTy), span⟩)
    (hcsib : castSiblingReadOk body t r ps ps' castTy = true) :
    StepRelD body f ctx s (stepMirFn body s) (Interp.step m) := by
  obtain ⟨_, _, hrel0, _, _, _, _⟩ := id hN0
  obtain ⟨hphase, _, _, _, _, _, _, _, _, _⟩ := inFragment_spec _ hfrag
  obtain ⟨hrt, ⟨it'', hopTy⟩, dr, d, fields, size, align, it, it', off0, leaf, off', hdr, hd, hit,
    hct, ht, hgood, hres, hres', hdis⟩ := castSiblingReadOk_spec hcsib
  obtain ⟨view, lm, p, k, rootVal, off, sz, hthr0, hlo0, _, hp, hpk, haddr0, haddrMax, hrootWf,
    hrootVal, hD0, hA0, hrng, hthrE, hactE, hallocE⟩ := holeLocal_spec hN0 hHR hd ht
  have hr0 : holeRange body t ps = some (off0, leaf.size) := by
    simp [holeRange, hd, ht, hres]
  rw [hr0] at hrng
  simp only [Option.some.injEq, Prod.mk.injEq] at hrng
  obtain ⟨hoff, hsz⟩ := hrng
  subst off0
  subst sz
  obtain ⟨_, hrelB0⟩ := resolveFieldPath_wf hrootWf hres
  have hoffb : off + leaf.size ≤ size := by simpa [TupleSpec.size] using hrelB0
  obtain ⟨leafVal, _, hleafOk, hslice0, _⟩ := resolveFieldPath_read hrootWf hrootVal hres'
  cases leafVal with
  | scalar sc =>
    have hbits : sc.bits < 2 ^ (8 * it'.size.bytes) := by
      simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hleafOk
      exact hleafOk.2
    simp only [TupleSpec.size, TupleSpec.encodeVal, valBytes] at hslice0
    have hsliceH : ((spliceAt ((TupleSpec.tuple fields size align).encodeVal rootVal) off
        (List.replicate leaf.size .Uninit)).drop off').take it'.size.bytes =
        scalarBytes it' sc.bits := by
      rw [spliceAt_drop_take_disjoint _ _ _ _ _ (by rw [List.length_replicate, hD0]; exact hoffb)
        (by rw [List.length_replicate]; exact hdis)]
      exact hslice0
    obtain ⟨tb, htb, hgetb⟩ := (translateFn_spec body f hf).2.2 _ bb hbb
    obtain ⟨hlen, hstspec, _⟩ := translateBlock_spec _ _ bb tb htb
    obtain ⟨st', hst', htst⟩ := hstspec _ _ hst
    cases ps' with
    | nil => simp [resolveFieldPath] at hres'
    | cons pe0 rest =>
      cases pe0 with
      | field idx fTy =>
        obtain ⟨pe, hpe, rfl⟩ : ∃ pe, translateFieldPlace (.Local (localName t))
            (.field idx fTy :: rest) = some pe ∧
            st' = .Assign (.Local (localName r)) (.UnOp (.Cast (.IntToInt it)) (.Load pe)) := by
          simp only [translateStatement, translatePlace] at hst'
          cases hp' : translateFieldPlace (.Local (localName t)) (.field idx fTy :: rest) with
          | none =>
            simp [hp', copyRv, copyOp, translateRvalue, translateOperand, translatePlace] at hst'
          | some pe =>
            refine ⟨pe, rfl, ?_⟩
            simp [hp', copyRv, copyOp, translateRvalue, translateOperand, translatePlace, hct,
              hopTy] at hst'
            exact hst'.symm
        have hshape0 : Shape m0 (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows)
            [(ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows).caller,
              calleeFrameL f (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows) lm
                s.frame.blockIdx s.frame.stmtIdx] m0.mem.memory.allocations :=
          ⟨hthr0, hrel0.active, rfl⟩
        have hshapeH : Shape m (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows)
            [(ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows).caller,
              calleeFrameL f (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows) lm
                s.frame.blockIdx s.frame.stmtIdx] m.mem.memory.allocations :=
          ⟨hthrE.trans hthr0, hactE.trans hrel0.active, rfl⟩
        have hk_lt : k < m0.mem.memory.allocations.length := (List.getElem?_eq_some_iff.mp hA0).1
        have hDh : (spliceAt ((TupleSpec.tuple fields size align).encodeVal rootVal) off
            (List.replicate leaf.size .Uninit)).length = size := by
          rw [spliceAt_length _ _ _ (by rw [List.length_replicate, hD0]; omega), hD0]
        have hAh : m.mem.memory.allocations[k]? = some (stackAlloc p.addr (itOf d body.layouts)
            (spliceAt ((TupleSpec.tuple fields size align).encodeVal rootVal) off
              (List.replicate leaf.size .Uninit))) := by
          rw [hallocE]
          simp [hk_lt]
        have hfl := FnLocalsSpec.of_translateFn hf
        obtain ⟨hdead0, hlive0⟩ := evalStatement_castSiblingRead_any (resetPick_shape hshape0) hfl
          hd ht hrootWf hp hpk haddr0 haddrMax hD0 hA0 hpe hres' hbits hslice0 hdr hit hgood
        obtain ⟨hdeadH, hliveH⟩ := evalStatement_castSiblingRead_any (resetPick_shape hshapeH) hfl
          hd ht hrootWf hp hpk haddr0 haddrMax hDh hAh hpe hres' hbits hsliceH hdr hit hgood
        have hne : ((s.frame.stmtIdx : Nat) : Int) ≠ (tb.statements.length : Int) := by
          have := (List.getElem?_eq_some_iff.mp hst).1
          rw [hlen]
          omega
        have hnd : ∀ st, bb.statements[s.frame.stmtIdx]? = some st →
            isProjDeinit st = false := by
          intro st hst2
          rw [hst] at hst2
          cases hst2
          rfl
        have hNF := step_correspondence_NF (eraseDeinit body) f hfrag
          (fnLocalsSpec_eraseDeinit hf) ctx s m0 (blk_eraseDeinit hf hbb hnd) hN0
        rw [stepMirFn_eraseDeinit_stmt (body := body) hrel0.activeCallee hphase hbb hst rfl]
        cases hpr : mapGet lm (localName r) with
        | none =>
          have hs0 : Interp.step m0 = .error (.ub "access to a dead local") := by
            rw [step_callee hshape0 tb hgetb]
            simp [hne, listIndex_nat _ _ _ htst, hdead0 hpr]
          have hsH : Interp.step m = .error (.ub "access to a dead local") := by
            rw [step_callee hshapeH tb hgetb]
            simp [hne, listIndex_nat _ _ _ htst, hdeadH hpr]
          rw [hs0] at hNF
          rw [hsH]
          exact hNF.toStepRelD
        | some pr =>
          have hr_lt : r < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdr).1
          obtain ⟨slotr, hsVr⟩ : ∃ slot, view[r]? = some slot :=
            ⟨_, List.getElem?_eq_getElem (by rw [hlo0.nlocals]; exact hr_lt)⟩
          have hscr : scalarTypeOf dr.ty = some (.Int it) := scalarTypeOf_int hit
          obtain ⟨kr, hprk, _, _, _, _, hAr⟩ := hlo0.storage_nonptr r dr slotr pr hdr hsVr hpr
            (isPtrTy_false_of_scalarTypeOf hscr)
          simp only [eraseDeinit_layouts] at hAr
          obtain ⟨hTr, hIr⟩ := tyOf_int (layouts := body.layouts) hit
          rw [hIr] at hAr
          have hlenr : (declSlotData dr slotr body.layouts).length = it.size.bytes := by
            rw [declSlotData_length (by rw [hTr]; exact hscr), hTr]
            rfl
          have hkr : kr ≠ k := by
            intro hkk
            subst hkk
            exact hrt (hlo0.inj r t pr p hpr hp (by rw [hprk, hpk]))
          have hArH : m.mem.memory.allocations[kr]? =
              some (stackAlloc pr.addr it (declSlotData dr slotr body.layouts)) := by
            rw [hallocE, List.getElem?_set_ne (Ne.symm hkr)]
            exact hAr
          obtain ⟨m3, hev0, h3⟩ := hlive0 pr kr _ hpr hprk hAr hlenr
          obtain ⟨m3h, hevH, h3h⟩ := hliveH pr kr _ hpr hprk hArH hlenr
          obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3
          obtain ⟨m4h, hm4h, h4h⟩ := bumpStmt_callee h3h
          have hs0 : Interp.step m0 = .ok m4 := by
            rw [step_callee hshape0 tb hgetb]
            simp [hne, listIndex_nat _ _ _ htst, hev0, hm4, check_after h4]
          have hsH : Interp.step m = .ok m4h := by
            rw [step_callee hshapeH tb hgetb]
            simp [hne, listIndex_nat _ _ _ htst, hevH, hm4h, check_after h4h]
          rw [hs0] at hNF
          rw [hsH]
          have hhole' : holeAt body s.frame.blockIdx (s.frame.stmtIdx + 1) = some (t, ps) := by
            rw [holeAt_succ hbb hst, hhole]
            simp [holeAfter, hrt]
          refine StepRelN.toStepRelD_hole hNF h4.threads hhole' hp hpk
            (by rw [h4.allocs, List.getElem?_set_ne hkr]; exact hA0) hr0
            (h4h.threads.trans h4.threads.symm) (h4h.active.trans h4.active.symm) ?_
          rw [h4h.allocs, h4.allocs, hallocE]
          exact List.set_comm _ _ (Ne.symm hkr)
      | _ => simp [resolveFieldPath] at hres'
  | _ => simp [TupleSpec.valOk] at hleafOk

/-- **Binary-operation re-initialization step.** While `_t.ps` is a hole,
`_t.ps' = BinOp(op, copy _q, const c)` (where `q ≠ t` is an integer local of the leaf's type, `c` a
constant of the leaf's type, and `ps'` has the hole's byte range) either faults (dead or
uninitialized `_q`, or a UB operation such as division by zero) in both machines, or stores the same
result over the hole in both machines, closing the hole and restoring `StateRelN`. -/
theorem step_window_reinit_binop {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment (eraseDeinit body) = true) (hf : translateFn body = some f)
    {ctx : Ctx} {s : MachineState} {m m0 : Mach} {t : Nat} {ps : List ProjectionElem}
    (_hhole : holeAt body s.frame.blockIdx s.frame.stmtIdx = some (t, ps))
    (hN0 : StateRelN (eraseDeinit body) f ctx s m0)
    (hHR : HoleRel body f ctx s.frame.blockIdx s.frame.stmtIdx t ps m0 m)
    {bb : BasicBlockData} {q : Nat} {ps' : List ProjectionElem} {op : MirAst.BinOp}
    {c : ConstOperand} {span : String}
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? =
      some ⟨.assign ⟨t, ps'⟩ (.binaryOp op (.copy ⟨q, []⟩) (.constant c)), span⟩)
    (hrb : reinitBinOpOk body t q ps' op c = true)
    (hrange : holeRange body t ps' = holeRange body t ps) :
    StepRelD body f ctx s (stepMirFn body s) (Interp.step m) := by
  obtain ⟨_, _, hrel0, _, _, _, _⟩ := id hN0
  obtain ⟨hphase, _, _, _, _, _, _, _, _, _⟩ := inFragment_spec _ hfrag
  obtain ⟨hqt, hrel, dq, d, fields, size, align, off', it, iop, cbits, hdq, hd, hitq, ht, hres',
    _, hiop, _, hcop⟩ := reinitBinOpOk_spec hrb
  obtain ⟨view, lm, p, k, rootVal, off, sz, hthr0, hlo0, _, hp, hpk, haddr0, haddrMax, hrootWf,
    _, hD0, hA0, hrng, hthrE, hactE, hallocE⟩ := holeLocal_spec hN0 hHR hd ht
  have hr' : holeRange body t ps' = some (off', it.size.bytes) := by
    simp [holeRange, hd, ht, hres', TupleSpec.size]
  rw [hr', hrng] at hrange
  simp only [Option.some.injEq, Prod.mk.injEq] at hrange
  obtain ⟨hoff, hsz⟩ := hrange
  subst off'
  subst sz
  obtain ⟨_, hrelBound⟩ := resolveFieldPath_wf hrootWf hres'
  have hoffb : off + it.size.bytes ≤ size := by simpa [TupleSpec.size] using hrelBound
  have hopTyQ : operandType body.layouts body.localDecls (.copy ⟨q, []⟩) = some (.Int it) := by
    simp [operandType, hdq, scalarTypeOf_int hitq]
  obtain ⟨tb, htb, hgetb⟩ := (translateFn_spec body f hf).2.2 _ bb hbb
  obtain ⟨hlen, hstspec, _⟩ := translateBlock_spec _ _ bb tb htb
  obtain ⟨st', hst', htst⟩ := hstspec _ _ hst
  cases ps' with
  | nil => simp [resolveFieldPath] at hres'
  | cons pe0 rest =>
    cases pe0 with
    | field idx fTy =>
      obtain ⟨pe, hpe, rfl⟩ : ∃ pe, translateFieldPlace (.Local (localName t))
          (.field idx fTy :: rest) = some pe ∧
          st' = .Assign pe (.BinOp (.Int iop) (.Load (.Local (localName q)))
            (.Constant (.Int (intFromBits cbits it)) (.Int it))) := by
        simp only [translateStatement, translatePlace] at hst'
        cases hp' : translateFieldPlace (.Local (localName t)) (.field idx fTy :: rest) with
        | none =>
          simp [hp', copyRv, copyOp, translateRvalue, translateOperand, translatePlace] at hst'
        | some pe =>
          refine ⟨pe, rfl, ?_⟩
          simp [hp', copyRv, copyOp, translateRvalue, translateOperand, translatePlace, hrel,
            hiop, hopTyQ] at hst'
          simp only [translateOperand] at hcop
          rw [hcop] at hst'
          simp at hst'
          exact hst'.symm
      have hshape0 : Shape m0 (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows)
          [(ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows).caller,
            calleeFrameL f (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows) lm
              s.frame.blockIdx s.frame.stmtIdx] m0.mem.memory.allocations :=
        ⟨hthr0, hrel0.active, rfl⟩
      have hshapeH : Shape m (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows)
          [(ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows).caller,
            calleeFrameL f (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows) lm
              s.frame.blockIdx s.frame.stmtIdx] m.mem.memory.allocations :=
        ⟨hthrE.trans hthr0, hactE.trans hrel0.active, rfl⟩
      have hk_lt : k < m0.mem.memory.allocations.length := (List.getElem?_eq_some_iff.mp hA0).1
      have hDh : (spliceAt ((TupleSpec.tuple fields size align).encodeVal rootVal) off
          (List.replicate it.size.bytes .Uninit)).length = size := by
        rw [spliceAt_length _ _ _ (by rw [List.length_replicate, hD0]; omega), hD0]
      have hAh : m.mem.memory.allocations[k]? = some (stackAlloc p.addr (itOf d body.layouts)
          (spliceAt ((TupleSpec.tuple fields size align).encodeVal rootVal) off
            (List.replicate it.size.bytes .Uninit))) := by
        rw [hallocE]; simp [hk_lt]
      have hfl := FnLocalsSpec.of_translateFn hf
      obtain ⟨hdead0, huninit0, hlive0⟩ := evalStatement_reinitBinOp_any (resetPick_shape hshape0)
        hfl hd ht hrootWf hp hpk haddr0 haddrMax hD0 hA0 hpe hres' hdq hitq hiop cbits
      obtain ⟨hdeadH, huninitH, hliveH⟩ := evalStatement_reinitBinOp_any (resetPick_shape hshapeH)
        hfl hd ht hrootWf hp hpk haddr0 haddrMax hDh hAh hpe hres' hdq hitq hiop cbits
      have hne : ((s.frame.stmtIdx : Nat) : Int) ≠ (tb.statements.length : Int) := by
        have := (List.getElem?_eq_some_iff.mp hst).1
        rw [hlen]; omega
      have hnd : ∀ st, bb.statements[s.frame.stmtIdx]? = some st → isProjDeinit st = false := by
        intro st hst2; rw [hst] at hst2; cases hst2; rfl
      have hNF := step_correspondence_NF (eraseDeinit body) f hfrag
        (fnLocalsSpec_eraseDeinit hf) ctx s m0 (blk_eraseDeinit hf hbb hnd) hN0
      rw [stepMirFn_eraseDeinit_stmt (body := body) hrel0.activeCallee hphase hbb hst rfl]
      cases hpq : mapGet lm (localName q) with
      | none =>
        have hs0 : Interp.step m0 = .error (.ub "access to a dead local") := by
          rw [step_callee hshape0 tb hgetb]
          simp [hne, listIndex_nat _ _ _ htst, hdead0 hpq]
        have hsH : Interp.step m = .error (.ub "access to a dead local") := by
          rw [step_callee hshapeH tb hgetb]
          simp [hne, listIndex_nat _ _ _ htst, hdeadH hpq]
        rw [hs0] at hNF
        rw [hsH]
        exact hNF.toStepRelD
      | some pq =>
        have hq_lt : q < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdq).1
        obtain ⟨slotq, hsVq⟩ : ∃ slot, view[q]? = some slot :=
          ⟨_, List.getElem?_eq_getElem (by rw [hlo0.nlocals]; exact hq_lt)⟩
        have hscq : scalarTypeOf dq.ty = some (.Int it) := scalarTypeOf_int hitq
        obtain ⟨kq, hpqk, _, _, _, _, hAq⟩ := hlo0.storage_nonptr q dq slotq pq hdq hsVq hpq
          (isPtrTy_false_of_scalarTypeOf hscq)
        simp only [eraseDeinit_layouts] at hAq
        obtain ⟨hTq, hIq⟩ := tyOf_int (layouts := body.layouts) hitq
        rw [hIq] at hAq
        have hkq : kq ≠ k := by
          intro hkk; subst hkk
          exact hqt (hlo0.inj q t pq p hpq hp (by rw [hpqk, hpk]))
        have hAqH : m.mem.memory.allocations[kq]? =
            some (stackAlloc pq.addr it (declSlotData dq slotq body.layouts)) := by
          rw [hallocE, List.getElem?_set_ne (Ne.symm hkq)]; exact hAq
        have hslotq := (DeclSlotOk_of_scalarTypeOf hscq slotq).mp (hlo0.slots q dq slotq hdq hsVq)
        simp only [eraseDeinit_layouts] at hslotq
        rw [hTq] at hslotq
        obtain ⟨hleafWf, _⟩ := resolveFieldPath_wf hrootWf hres'
        have hgood : GoodSize it.size.bytes := by
          simp only [TupleSpec.wf] at hleafWf
          exact (goodAlignBytes_iff it.size.bytes).mp hleafWf
        have hfragd : FragTy (tyOf dq body.layouts) (itOf dq body.layouts) :=
          fragTy_of_scalarTypeOf hscq (FragTy.int it hgood)
        rw [hfragd.declSlotData, hIq] at hAq hAqH
        match slotq, hslotq, hAq, hAqH with
        | .dead, _, hAq, hAqH =>
          obtain ⟨msg0, hev0⟩ := huninit0 pq kq hpq hpqk hAq
          obtain ⟨msgH, hevH⟩ := huninitH pq kq hpq hpqk hAqH
          have hs0 : Interp.step m0 = .error (.ub msg0) := by
            rw [step_callee hshape0 tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hev0]
          have hsH : Interp.step m = .error (.ub msgH) := by
            rw [step_callee hshapeH tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hevH]
          rw [hs0] at hNF; rw [hsH]
          exact hNF.toStepRelD_ub
        | .uninit, _, hAq, hAqH =>
          obtain ⟨msg0, hev0⟩ := huninit0 pq kq hpq hpqk hAq
          obtain ⟨msgH, hevH⟩ := huninitH pq kq hpq hpqk hAqH
          have hs0 : Interp.step m0 = .error (.ub msg0) := by
            rw [step_callee hshape0 tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hev0]
          have hsH : Interp.step m = .error (.ub msgH) := by
            rw [step_callee hshapeH tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hevH]
          rw [hs0] at hNF; rw [hsH]
          exact hNF.toStepRelD_ub
        | .init (.scalar sc), ⟨_, hbits⟩, hAq, hAqH =>
          obtain ⟨hub0, hok0⟩ := hlive0 pq kq sc.bits hpq hpqk hbits hAq
          obtain ⟨hubH, hokH⟩ := hliveH pq kq sc.bits hpq hpqk hbits hAqH
          cases hz : intBinEval iop (intFromBits sc.bits it) (intFromBits cbits it) it with
          | none =>
            obtain ⟨msg0, hev0⟩ := hub0 hz
            obtain ⟨msgH, hevH⟩ := hubH hz
            have hs0 : Interp.step m0 = .error (.ub msg0) := by
              rw [step_callee hshape0 tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hev0]
            have hsH : Interp.step m = .error (.ub msgH) := by
              rw [step_callee hshapeH tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hevH]
            rw [hs0] at hNF; rw [hsH]
            exact hNF.toStepRelD_ub
          | some z =>
            obtain ⟨m3, hev0, h3⟩ := hok0 z hz
            obtain ⟨m3h, hevH, h3h⟩ := hokH z hz
            have hwlen : (scalarBytes it (z % 2 ^ (8 * it.size.bytes)).toNat).length =
                it.size.bytes := by
              simp [scalarBytes, leBytes_length]
            rw [spliceAt_same _ off _ _ (by rw [List.length_replicate, hD0]; omega)
              (by rw [List.length_replicate, hwlen]), hallocE, List.set_set] at h3h
            obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3
            obtain ⟨m4h, hm4h, h4h⟩ := bumpStmt_callee h3h
            have hs0 : Interp.step m0 = .ok m4 := by
              rw [step_callee hshape0 tb hgetb]
              simp [hne, listIndex_nat _ _ _ htst, hev0, hm4, check_after h4]
            have hsH : Interp.step m = .ok m4h := by
              rw [step_callee hshapeH tb hgetb]
              simp [hne, listIndex_nat _ _ _ htst, hevH, hm4h, check_after h4h]
            rw [hs0] at hNF; rw [hsH]
            exact StepRelN.toStepRelD_obs hNF (h4h.threads.trans h4.threads.symm)
              (h4h.active.trans h4.active.symm) (h4h.allocs.trans h4.allocs.symm)
        | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨_, htyT, _⟩, _, _ =>
          nomatch htyT
    | _ => simp [resolveFieldPath] at hres'

theorem binOpWindowOk_spec {body : CapturedMir} {t r q : Nat} {op : MirAst.BinOp}
    {c : ConstOperand} (h : binOpWindowOk body t r q op c = true) :
    r ≠ t ∧ q ≠ t ∧ r ≠ q ∧ translateRelOp op = none ∧
    ∃ (dr dq d : LocalDecl) (fields : List (Nat × TupleSpec)) (size align : Nat)
      (it : Gen.IntType) (iop : Gen.IntBinOp) (cbits : Nat),
      body.localDecls[r]? = some dr ∧ body.localDecls[q]? = some dq ∧
      body.localDecls[t]? = some d ∧
      intTypeOf dr.ty = some it ∧ intTypeOf dq.ty = some it ∧
      tupleTypeOf body.layouts d.ty = some (fields, size, align) ∧
      0 < it.size.bytes ∧ GoodSize it.size.bytes ∧
      translateBinOp op = some iop ∧ cbits < 2 ^ (8 * it.size.bytes) ∧
      translateOperand body.localDecls (.constant c) =
        some (.Constant (.Int (intFromBits cbits it)) (.Int it)) := by
  unfold binOpWindowOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hrt, hqt⟩, hrq⟩, hrel⟩, hbin⟩, h⟩ := h
  have hrel' : translateRelOp op = none := Option.isNone_iff_eq_none.mp hrel
  obtain ⟨iop, hiop⟩ := Option.isSome_iff_exists.mp hbin
  refine ⟨hrt, hqt, hrq, hrel', ?_⟩
  cases hdr : body.localDecls[r]? with
  | none => simp [hdr] at h
  | some dr =>
    cases hdq : body.localDecls[q]? with
    | none => simp [hdr, hdq] at h
    | some dq =>
      cases hd : body.localDecls[t]? with
      | none => simp [hdr, hdq, hd] at h
      | some d =>
        cases hit : intTypeOf dr.ty with
        | none => simp [hdr, hdq, hd, hit] at h
        | some it =>
          cases hitq : intTypeOf dq.ty with
          | none => simp [hdr, hdq, hd, hit, hitq] at h
          | some it' =>
            cases ht : tupleTypeOf body.layouts d.ty with
            | none => simp [hdr, hdq, hd, hit, hitq, ht] at h
            | some trip =>
              obtain ⟨fields, size, align⟩ := trip
              obtain ⟨cty, cval⟩ := c
              cases cval with
              | scalar cs =>
                cases cs with
                | int sc =>
                  obtain ⟨cbits, csz⟩ := sc
                  cases hcit : intTypeOf cty with
                  | none => simp [hdr, hdq, hd, hit, hitq, ht, hcit] at h
                  | some ic =>
                    simp only [hdr, hdq, hd, hit, hitq, ht, hcit, Bool.and_eq_true,
                      decide_eq_true_eq, Bool.not_eq_true'] at h
                    obtain ⟨⟨⟨⟨rfl, hpos⟩, hgood⟩, hnb⟩, ⟨rfl, rfl⟩, hcbits⟩ := h
                    refine ⟨dr, dq, d, fields, size, align, ic, iop, cbits, rfl, rfl, rfl, hit,
                      hitq, ht, hpos, (goodAlignBytes_iff ic.size.bytes).mp hgood, hiop,
                      hcbits, ?_⟩
                    simp [translateOperand, hnb, hcit, hcbits]
                | ptr _ _ => simp [hdr, hdq, hd, hit, hitq, ht] at h
              | _ => simp [hdr, hdq, hd, hit, hitq, ht] at h

/-- **Hole-independent scalar binary operation `_r = BinOp(iop, copy _q, const c)` between two
integer locals `_r` and `_q` of type `it` and a constant `c` of type `it`.** -/
theorem evalStatement_binOpWindow_any {m : Mach} {ctx : Ctx} {f : Gen.Function}
    {lm : Map Gen.LocalName Ptr} {blk stmt : Nat} {A : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] A)
    {body : CapturedMir} (hfl : FnLocalsSpec body f)
    {r q : Nat} {dr dq : LocalDecl} {it : Gen.IntType}
    (hdr : body.localDecls[r]? = some dr) (hdq : body.localDecls[q]? = some dq)
    (hit : intTypeOf dr.ty = some it) (hitq : intTypeOf dq.ty = some it)
    (hgood : GoodSize it.size.bytes)
    {op : MirAst.BinOp} {iop : Gen.IntBinOp} (hiop : translateBinOp op = some iop)
    (cbits : Nat) :
    (mapGet lm (localName r) = none →
      evalStatement m (.Assign (.Local (localName r))
        (.BinOp (.Int iop) (.Load (.Local (localName q)))
          (.Constant (.Int (intFromBits cbits it)) (.Int it)))) =
        .error (.ub "access to a dead local")) ∧
    (∀ (pr : Ptr), mapGet lm (localName r) = some pr →
      mapGet lm (localName q) = none →
      evalStatement m (.Assign (.Local (localName r))
        (.BinOp (.Int iop) (.Load (.Local (localName q)))
          (.Constant (.Int (intFromBits cbits it)) (.Int it)))) =
        .error (.ub "access to a dead local")) ∧
    (∀ (pr pq : Ptr) (kq : Nat), mapGet lm (localName r) = some pr →
      mapGet lm (localName q) = some pq →
      pq.provenance = some (⟨(kq : Int)⟩, ()) →
      A[kq]? = some (stackAlloc pq.addr it (List.replicate it.size.bytes .Uninit)) →
      ∃ msg, evalStatement m (.Assign (.Local (localName r))
        (.BinOp (.Int iop) (.Load (.Local (localName q)))
          (.Constant (.Int (intFromBits cbits it)) (.Int it)))) =
        .error (.ub msg)) ∧
    (∀ (pr pq : Ptr) (kr kq : Nat) (Dr : List Byte) (bits : Nat),
      mapGet lm (localName r) = some pr →
      mapGet lm (localName q) = some pq →
      pr.provenance = some (⟨(kr : Int)⟩, ()) →
      pq.provenance = some (⟨(kq : Int)⟩, ()) →
      bits < 2 ^ (8 * it.size.bytes) →
      A[kq]? = some (stackAlloc pq.addr it (scalarBytes it bits)) →
      A[kr]? = some (stackAlloc pr.addr it Dr) →
      Dr.length = it.size.bytes →
      (intBinEval iop (intFromBits bits it) (intFromBits cbits it) it = none →
        ∃ msg, evalStatement m (.Assign (.Local (localName r))
          (.BinOp (.Int iop) (.Load (.Local (localName q)))
            (.Constant (.Int (intFromBits cbits it)) (.Int it)))) =
          .error (.ub msg)) ∧
      (∀ z, intBinEval iop (intFromBits bits it) (intFromBits cbits it) it = some z →
        ∃ m', evalStatement m (.Assign (.Local (localName r))
            (.BinOp (.Int iop) (.Load (.Local (localName q)))
              (.Constant (.Int (intFromBits cbits it)) (.Int it)))) = .ok m' ∧
          Shape m' ctx [ctx.caller, calleeFrameL f ctx lm blk stmt]
            (A.set kr (stackAlloc pr.addr it
              (scalarBytes it (z % 2 ^ (8 * it.size.bytes)).toNat))))) := by
  obtain ⟨hTr, _⟩ := tyOf_int (layouts := body.layouts) hit
  obtain ⟨hTq, _⟩ := tyOf_int (layouts := body.layouts) hitq
  have hlocr := (hfl.2 r dr hdr).2
  have hlocq := (hfl.2 q dq hdq).2
  rw [hTr] at hlocr
  rw [hTq] at hlocq
  refine ⟨fun hnone => ?_, fun pr hpr hnoneq => ?_, fun pr pq kq hpr hpq hpqk hAq => ?_,
    fun pr pq kr kq Dr bits hpr hpq hprk hpqk hbits hAq hAr hlenr => ?_⟩
  · simp [evalStatement, evalPlace_local_none h r _ hlocr hnone]
  · simp [evalStatement, evalPlace_local_some h r _ hlocr pr hpr, evalValue,
      evalPlace_local_none h q _ hlocq hnoneq]
  · have hplacer := evalPlace_local_some h r _ hlocr pr hpr
    have hplaceq := evalPlace_local_some h q _ hlocq pq hpq
    obtain ⟨msg, hmsg⟩ := typedLoad_ptr_frag_uninit h pq kq hpqk (FragTy.int it hgood) hAq
    exact ⟨msg, by simp [evalStatement, hplacer, evalValue, hplaceq, placeLoad, hmsg]⟩
  · have hplacer := evalPlace_local_some h r _ hlocr pr hpr
    have hplaceq := evalPlace_local_some h q _ hlocq pq hpq
    obtain ⟨m1, hm1, h1⟩ := typedLoad_ptr_frag h pq kq hpqk (FragTy.int it hgood) bits hbits hAq
    simp only [valOf] at hm1
    obtain ⟨hevalOk, hevalNone⟩ :=
      evalIntBinOp_spec op iop hiop (intFromBits bits it) (intFromBits cbits it) it
    refine ⟨fun hz => ?_, fun z hz => ?_⟩
    · obtain ⟨msg, hmsg⟩ := hevalNone hz
      exact ⟨msg, by simp [evalStatement, hplacer, evalValue, hplaceq, placeLoad, hm1,
        evalConstant, evalBinOp, hmsg]⟩
    · have hpos := two_pow_pos (8 * it.size.bytes)
      have hlt : (z % 2 ^ (8 * it.size.bytes)).toNat < 2 ^ (8 * it.size.bytes) := by
        have h0 := Int.emod_nonneg z (Int.ne_of_gt hpos)
        have hlt' := Int.emod_lt_of_pos z hpos
        have : ((z % 2 ^ (8 * it.size.bytes)).toNat : Int) < 2 ^ (8 * it.size.bytes) := by
          rw [Int.toNat_of_nonneg h0]; exact hlt'
        exact_mod_cast this
      have hst := typedStore_ptr_frag h1 pr kr hprk (FragTy.int it hgood) Dr
        (z % 2 ^ (8 * it.size.bytes)).toNat hlt hAr hlenr
      simp only [valOf] at hst
      refine ⟨withMem m1 (A.set kr (stackAlloc pr.addr it
        (scalarBytes it (z % 2 ^ (8 * it.size.bytes)).toNat)))
        ⟨.Store, .None, pr.addr, it.size⟩, ?_, withMem_shape h1 _⟩
      simp [evalStatement, hplacer, evalValue, hplaceq, placeLoad, hm1, evalConstant, evalBinOp,
        hevalOk z hz, bringInBounds_eq_intFromBits it hgood z, placeStore, hst]

/-- **Hole-independent scalar binary-operation step.** While `_t.ps` is a hole,
`_r = BinOp(op, copy _q, const c)` (where `r ≠ t`, `q ≠ t`, `r ≠ q` are integer locals of the same
type `it` and `c` is a constant of type `it`) either faults (dead `_r`, dead/uninitialized `_q`, or
a UB operation such as division by zero) in both machines, or stores the computed result into `_r`'s
allocation in both machines while leaving the open hole on `_t.ps` untouched. -/
theorem step_window_binop_local {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment (eraseDeinit body) = true) (hf : translateFn body = some f)
    {ctx : Ctx} {s : MachineState} {m m0 : Mach} {t : Nat} {ps : List ProjectionElem}
    (hhole : holeAt body s.frame.blockIdx s.frame.stmtIdx = some (t, ps))
    (hN0 : StateRelN (eraseDeinit body) f ctx s m0)
    (hHR : HoleRel body f ctx s.frame.blockIdx s.frame.stmtIdx t ps m0 m)
    {bb : BasicBlockData} {r q : Nat} {op : MirAst.BinOp} {c : ConstOperand} {span : String}
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? =
      some ⟨.assign ⟨r, []⟩ (.binaryOp op (.copy ⟨q, []⟩) (.constant c)), span⟩)
    (hbw : binOpWindowOk body t r q op c = true) :
    StepRelD body f ctx s (stepMirFn body s) (Interp.step m) := by
  obtain ⟨_, _, hrel0, _, _, _, _⟩ := id hN0
  obtain ⟨hphase, _, _, _, _, _, _, _, _, _⟩ := inFragment_spec _ hfrag
  obtain ⟨hrt, hqt, _hrq, hrel, dr, dq, d, fields, size, align, it, iop, cbits, hdr, hdq, hd, hit,
    hitq, ht, _, hgood, hiop, _, hcop⟩ := binOpWindowOk_spec hbw
  obtain ⟨view, lm, p, k, rootVal, off, sz, hthr0, hlo0, _, hp, hpk, _, _, _, _, _, hA0, hrng,
    hthrE, hactE, hallocE⟩ := holeLocal_spec hN0 hHR hd ht
  have hopTyQ : operandType body.layouts body.localDecls (.copy ⟨q, []⟩) = some (.Int it) := by
    simp [operandType, hdq, scalarTypeOf_int hitq]
  obtain ⟨tb, htb, hgetb⟩ := (translateFn_spec body f hf).2.2 _ bb hbb
  obtain ⟨hlen, hstspec, _⟩ := translateBlock_spec _ _ bb tb htb
  obtain ⟨st', hst', htst⟩ := hstspec _ _ hst
  have hstEq : st' = .Assign (.Local (localName r))
      (.BinOp (.Int iop) (.Load (.Local (localName q)))
        (.Constant (.Int (intFromBits cbits it)) (.Int it))) := by
    simp only [translateStatement, translatePlace, copyRv, copyOp, translateRvalue,
      translateOperand, hrel, hiop, hopTyQ] at hst'
    simp only [translateOperand] at hcop
    rw [hcop] at hst'
    simp at hst'
    exact hst'.symm
  subst hstEq
  have hshape0 : Shape m0 (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows)
      [(ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows).caller,
        calleeFrameL f (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows) lm
          s.frame.blockIdx s.frame.stmtIdx] m0.mem.memory.allocations :=
    ⟨hthr0, hrel0.active, rfl⟩
  have hshapeH : Shape m (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows)
      [(ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows).caller,
        calleeFrameL f (ctxWithBorrows (eraseDeinit body) ctx s.memory.borrows) lm
          s.frame.blockIdx s.frame.stmtIdx] m.mem.memory.allocations :=
    ⟨hthrE.trans hthr0, hactE.trans hrel0.active, rfl⟩
  have hfl := FnLocalsSpec.of_translateFn hf
  obtain ⟨hdeadR0, hdeadQ0, huninitQ0, hlive0⟩ :=
    evalStatement_binOpWindow_any (resetPick_shape hshape0) hfl hdr hdq hit hitq hgood hiop cbits
  obtain ⟨hdeadRH, hdeadQH, huninitQH, hliveH⟩ :=
    evalStatement_binOpWindow_any (resetPick_shape hshapeH) hfl hdr hdq hit hitq hgood hiop cbits
  have hne : ((s.frame.stmtIdx : Nat) : Int) ≠ (tb.statements.length : Int) := by
    have := (List.getElem?_eq_some_iff.mp hst).1
    rw [hlen]; omega
  have hnd : ∀ st, bb.statements[s.frame.stmtIdx]? = some st → isProjDeinit st = false := by
    intro st hst2; rw [hst] at hst2; cases hst2; rfl
  have hNF := step_correspondence_NF (eraseDeinit body) f hfrag
    (fnLocalsSpec_eraseDeinit hf) ctx s m0 (blk_eraseDeinit hf hbb hnd) hN0
  rw [stepMirFn_eraseDeinit_stmt (body := body) hrel0.activeCallee hphase hbb hst rfl]
  cases hpr : mapGet lm (localName r) with
  | none =>
    have hs0 : Interp.step m0 = .error (.ub "access to a dead local") := by
      rw [step_callee hshape0 tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hdeadR0 hpr]
    have hsH : Interp.step m = .error (.ub "access to a dead local") := by
      rw [step_callee hshapeH tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hdeadRH hpr]
    rw [hs0] at hNF; rw [hsH]
    exact hNF.toStepRelD
  | some pr =>
    cases hpq : mapGet lm (localName q) with
    | none =>
      have hs0 : Interp.step m0 = .error (.ub "access to a dead local") := by
        rw [step_callee hshape0 tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hdeadQ0 pr hpr hpq]
      have hsH : Interp.step m = .error (.ub "access to a dead local") := by
        rw [step_callee hshapeH tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hdeadQH pr hpr hpq]
      rw [hs0] at hNF; rw [hsH]
      exact hNF.toStepRelD
    | some pq =>
      have hr_lt : r < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdr).1
      have hq_lt : q < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdq).1
      obtain ⟨slotr, hsVr⟩ : ∃ slot, view[r]? = some slot :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlo0.nlocals]; exact hr_lt)⟩
      obtain ⟨slotq, hsVq⟩ : ∃ slot, view[q]? = some slot :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlo0.nlocals]; exact hq_lt)⟩
      have hscr : scalarTypeOf dr.ty = some (.Int it) := scalarTypeOf_int hit
      have hscq : scalarTypeOf dq.ty = some (.Int it) := scalarTypeOf_int hitq
      obtain ⟨kr, hprk, _, _, _, _, hAr⟩ := hlo0.storage_nonptr r dr slotr pr hdr hsVr hpr
        (isPtrTy_false_of_scalarTypeOf hscr)
      obtain ⟨kq, hpqk, _, _, _, _, hAq⟩ := hlo0.storage_nonptr q dq slotq pq hdq hsVq hpq
        (isPtrTy_false_of_scalarTypeOf hscq)
      simp only [eraseDeinit_layouts] at hAr hAq
      obtain ⟨hTr, hIr⟩ := tyOf_int (layouts := body.layouts) hit
      obtain ⟨hTq, hIq⟩ := tyOf_int (layouts := body.layouts) hitq
      rw [hIr] at hAr
      rw [hIq] at hAq
      have hlenr : (declSlotData dr slotr body.layouts).length = it.size.bytes := by
        rw [declSlotData_length (by rw [hTr]; exact hscr), hTr]; rfl
      have hkr : kr ≠ k := by
        intro hkk; subst hkk
        exact hrt (hlo0.inj r t pr p hpr hp (by rw [hprk, hpk]))
      have hkq : kq ≠ k := by
        intro hkk; subst hkk
        exact hqt (hlo0.inj q t pq p hpq hp (by rw [hpqk, hpk]))
      have hArH : m.mem.memory.allocations[kr]? =
          some (stackAlloc pr.addr it (declSlotData dr slotr body.layouts)) := by
        rw [hallocE, List.getElem?_set_ne (Ne.symm hkr)]; exact hAr
      have hAqH : m.mem.memory.allocations[kq]? =
          some (stackAlloc pq.addr it (declSlotData dq slotq body.layouts)) := by
        rw [hallocE, List.getElem?_set_ne (Ne.symm hkq)]; exact hAq
      have hslotq := (DeclSlotOk_of_scalarTypeOf hscq slotq).mp (hlo0.slots q dq slotq hdq hsVq)
      simp only [eraseDeinit_layouts] at hslotq
      rw [hTq] at hslotq
      have hfragdq : FragTy (tyOf dq body.layouts) (itOf dq body.layouts) :=
        fragTy_of_scalarTypeOf hscq (FragTy.int it hgood)
      rw [hfragdq.declSlotData, hIq] at hAq hAqH
      match slotq, hslotq, hAq, hAqH with
      | .dead, _, hAq, hAqH =>
        obtain ⟨msg0, hev0⟩ := huninitQ0 pr pq kq hpr hpq hpqk hAq
        obtain ⟨msgH, hevH⟩ := huninitQH pr pq kq hpr hpq hpqk hAqH
        have hs0 : Interp.step m0 = .error (.ub msg0) := by
          rw [step_callee hshape0 tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hev0]
        have hsH : Interp.step m = .error (.ub msgH) := by
          rw [step_callee hshapeH tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hevH]
        rw [hs0] at hNF; rw [hsH]
        exact hNF.toStepRelD_ub
      | .uninit, _, hAq, hAqH =>
        obtain ⟨msg0, hev0⟩ := huninitQ0 pr pq kq hpr hpq hpqk hAq
        obtain ⟨msgH, hevH⟩ := huninitQH pr pq kq hpr hpq hpqk hAqH
        have hs0 : Interp.step m0 = .error (.ub msg0) := by
          rw [step_callee hshape0 tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hev0]
        have hsH : Interp.step m = .error (.ub msgH) := by
          rw [step_callee hshapeH tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hevH]
        rw [hs0] at hNF; rw [hsH]
        exact hNF.toStepRelD_ub
      | .init (.scalar sc), ⟨_, hbits⟩, hAq, hAqH =>
        obtain ⟨hub0, hok0⟩ := hlive0 pr pq kr kq _ sc.bits hpr hpq hprk hpqk hbits hAq hAr hlenr
        obtain ⟨hubH, hokH⟩ := hliveH pr pq kr kq _ sc.bits hpr hpq hprk hpqk hbits hAqH hArH hlenr
        cases hz : intBinEval iop (intFromBits sc.bits it) (intFromBits cbits it) it with
        | none =>
          obtain ⟨msg0, hev0⟩ := hub0 hz
          obtain ⟨msgH, hevH⟩ := hubH hz
          have hs0 : Interp.step m0 = .error (.ub msg0) := by
            rw [step_callee hshape0 tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hev0]
          have hsH : Interp.step m = .error (.ub msgH) := by
            rw [step_callee hshapeH tb hgetb]; simp [hne, listIndex_nat _ _ _ htst, hevH]
          rw [hs0] at hNF; rw [hsH]
          exact hNF.toStepRelD_ub
        | some z =>
          obtain ⟨m3, hev0, h3⟩ := hok0 z hz
          obtain ⟨m3h, hevH, h3h⟩ := hokH z hz
          obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3
          obtain ⟨m4h, hm4h, h4h⟩ := bumpStmt_callee h3h
          have hs0 : Interp.step m0 = .ok m4 := by
            rw [step_callee hshape0 tb hgetb]
            simp [hne, listIndex_nat _ _ _ htst, hev0, hm4, check_after h4]
          have hsH : Interp.step m = .ok m4h := by
            rw [step_callee hshapeH tb hgetb]
            simp [hne, listIndex_nat _ _ _ htst, hevH, hm4h, check_after h4h]
          rw [hs0] at hNF; rw [hsH]
          have hhole' : holeAt body s.frame.blockIdx (s.frame.stmtIdx + 1) = some (t, ps) := by
            rw [holeAt_succ hbb hst, hhole]
            simp [holeAfter, hrt]
          refine StepRelN.toStepRelD_hole hNF h4.threads hhole' hp hpk
            (by rw [h4.allocs, List.getElem?_set_ne hkr]; exact hA0) hrng
            (h4h.threads.trans h4.threads.symm) (h4h.active.trans h4.active.symm) ?_
          rw [h4h.allocs, h4.allocs, hallocE]
          exact List.set_comm _ _ (Ne.symm hkr)
      | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨_, htyT, _⟩, _, _ =>
        nomatch htyT

/-! ## The correspondence theorem for `inFragmentD` -/

/-- **Correspondence theorem for projected `Deinit` (one step, preserving `StateRelD`).**
For an `inFragmentD` body `body`, its translation `f`, and related states (`StateRelD`), one
Anneal MIR step and one MiniRust `Machine::step` correspond in the sense of `StepRelD`. -/
theorem step_correspondence_D (body : CapturedMir) (f : Gen.Function)
    (hfragD : inFragmentD body = true) (hf : translateFn body = some f) (ctx : Ctx)
    (s : MachineState) (m : Mach) (hrel : StateRelD body f ctx s m) :
    StepRelD body f ctx s (stepMirFn body s) (Interp.step m) := by
  obtain ⟨hfrag, hwin⟩ := inFragmentD_spec hfragD
  obtain ⟨hphase, _, _, _, _, _, hbbs, _, _, _⟩ := inFragment_spec _ hfrag
  rcases hrel with hN | ⟨t, ps, m0, hhole, hN0, hHR⟩
  · obtain ⟨view, lm, hrelA, _, _, _, _⟩ := id hN
    have hblk : s.frame.blockIdx < body.basicBlocks.length := by
      simpa using hrelA.blk
    obtain ⟨bb, hbb⟩ : ∃ bb, body.basicBlocks[s.frame.blockIdx]? = some bb :=
      ⟨_, List.getElem?_eq_getElem hblk⟩
    by_cases hpd : ∃ st, bb.statements[s.frame.stmtIdx]? = some st ∧ isProjDeinit st = true
    · obtain ⟨st, hst, hpd⟩ := hpd
      exact step_projDeinit hfrag hwin hf hN hbb hst hpd
    · have hnd : ∀ st, bb.statements[s.frame.stmtIdx]? = some st → isProjDeinit st = false := by
        intro st hst
        cases h : isProjDeinit st
        · rfl
        · exact absurd ⟨st, hst, h⟩ hpd
      have hstepEq : stepMirFn body s = stepMirFn (eraseDeinit body) s := by
        rcases Nat.lt_or_ge s.frame.stmtIdx bb.statements.length with hlt | hge
        · obtain ⟨st, hst⟩ : ∃ st, bb.statements[s.frame.stmtIdx]? = some st :=
            ⟨_, List.getElem?_eq_getElem hlt⟩
          exact stepMirFn_eraseDeinit_stmt hrelA.activeCallee hphase hbb hst (hnd st hst)
        · have hle := hrelA.stmt _ (eraseDeinit_block hbb)
          simp only [eraseDeinitBlock_length] at hle
          have heq : s.frame.stmtIdx = bb.statements.length := by omega
          have hterm := (hbbs _ (List.mem_of_getElem? (eraseDeinit_block hbb))).2.2
          simp only [eraseDeinitBlock_terminator, eraseDeinit_length, eraseDeinit_layouts,
            eraseDeinit_localDecls] at hterm
          exact stepMirFn_eraseDeinit_term hrelA.activeCallee hphase hbb heq hterm
      rw [hstepEq]
      exact (step_correspondence_NF (eraseDeinit body) f hfrag (fnLocalsSpec_eraseDeinit hf) ctx
        s m (blk_eraseDeinit hf hbb hnd) hN).toStepRelD
  · obtain ⟨view, lm, hrelA, _, _, _, _⟩ := id hN0
    have hblk : s.frame.blockIdx < body.basicBlocks.length := by
      simpa using hrelA.blk
    obtain ⟨bb, hbb⟩ : ∃ bb, body.basicBlocks[s.frame.blockIdx]? = some bb :=
      ⟨_, List.getElem?_eq_getElem hblk⟩
    obtain ⟨hwst, hend⟩ := deinitWindowOk_spec hwin hbb
    have hle := hrelA.stmt _ (eraseDeinit_block hbb)
    simp only [eraseDeinitBlock_length] at hle
    have hlt : s.frame.stmtIdx < bb.statements.length := by
      rcases Nat.lt_or_ge s.frame.stmtIdx bb.statements.length with h | h
      · exact h
      · have heq : s.frame.stmtIdx = bb.statements.length := by omega
        rw [heq, hend] at hhole
        cases hhole
    obtain ⟨st, hst⟩ : ∃ st, bb.statements[s.frame.stmtIdx]? = some st :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    have hw := hwst _ _ hst
    rw [hhole] at hw
    obtain ⟨kind, span⟩ := st
    cases kind with
    | assign dst rv =>
      obtain ⟨r, rproj⟩ := dst
      cases rv with
      | use op =>
        cases op with
        | copy q =>
          obtain ⟨t', ps'⟩ := q
          cases rproj with
          | nil =>
            cases ps' with
            | nil =>
              simp only [windowStmtOk] at hw
              exact step_window_local_copy hfrag hf hhole hN0 hHR hbb hst hw
            | cons qp qps =>
              simp only [windowStmtOk, Bool.and_eq_true, decide_eq_true_eq] at hw
              obtain ⟨rfl, hsib⟩ := hw
              exact step_window_read hfrag hf hhole hN0 hHR hbb hst hsib
          | cons rp rps =>
            cases ps' with
            | nil =>
              simp only [windowStmtOk, Bool.and_eq_true, decide_eq_true_eq] at hw
              obtain ⟨⟨rfl, hrc⟩, hrange⟩ := hw
              exact step_window_reinit_copy hfrag hf hhole hN0 hHR hbb hst hrc hrange
            | cons _ _ => simp [windowStmtOk] at hw
        | constant c =>
          cases rproj with
          | nil =>
            simp only [windowStmtOk, Bool.and_eq_true, decide_eq_true_eq] at hw
            obtain ⟨⟨rfl, hre⟩, hrange⟩ := hw
            exact step_window_reinit hfrag hf hhole hN0 hHR hbb hst hre hrange
          | cons _ _ =>
            simp only [windowStmtOk, Bool.and_eq_true, decide_eq_true_eq] at hw
            obtain ⟨⟨rfl, hre⟩, hrange⟩ := hw
            exact step_window_reinit hfrag hf hhole hN0 hHR hbb hst hre hrange
        | move _ => simp [windowStmtOk] at hw
      | cast ck op castTy =>
        cases ck with
        | intToInt =>
          cases op with
          | copy q =>
            obtain ⟨t', ps'⟩ := q
            cases rproj with
            | nil =>
              cases ps' with
              | nil => simp [windowStmtOk] at hw
              | cons qp qps =>
                simp only [windowStmtOk, Bool.and_eq_true, decide_eq_true_eq] at hw
                obtain ⟨rfl, hcsib⟩ := hw
                exact step_window_cast_read hfrag hf hhole hN0 hHR hbb hst hcsib
            | cons _ _ => simp [windowStmtOk] at hw
          | _ => simp [windowStmtOk] at hw
        | _ => simp [windowStmtOk] at hw
      | binaryOp bop a b =>
        cases rproj with
        | nil =>
          cases a with
          | copy qa =>
            obtain ⟨q, qproj⟩ := qa
            cases qproj with
            | nil =>
              cases b with
              | constant c =>
                simp only [windowStmtOk] at hw
                exact step_window_binop_local hfrag hf hhole hN0 hHR hbb hst hw
              | _ => simp [windowStmtOk] at hw
            | cons _ _ => simp [windowStmtOk] at hw
          | _ => simp [windowStmtOk] at hw
        | cons rp rps =>
          cases a with
          | copy qa =>
            obtain ⟨q, qproj⟩ := qa
            cases qproj with
            | nil =>
              cases b with
              | constant c =>
                simp only [windowStmtOk, Bool.and_eq_true, decide_eq_true_eq] at hw
                obtain ⟨⟨rfl, hrb⟩, hrange⟩ := hw
                exact step_window_reinit_binop hfrag hf hhole hN0 hHR hbb hst hrb hrange
              | _ => simp [windowStmtOk] at hw
            | cons _ _ => simp [windowStmtOk] at hw
          | _ => simp [windowStmtOk] at hw
      | _ => simp [windowStmtOk] at hw
    | _ => simp [windowStmtOk] at hw

/-! ## Whole executions for `inFragmentD` bodies

`step_correspondence_D` lifted to whole executions, mirroring `Run.lean`: `reaches_rel_D`,
`run_ret_D`, the init block (`step_start_D`, through `step_start_NF` on `eraseDeinit body`),
`run_ret_from_start_D`, and the call-tree entry theorem `mirCall_ret_D`. -/

/-! ### The erasure keeps the storage markers, the borrows, and the entry state -/

/-- `eraseDeinitStmt` only rewrites a projected `Deinit` into a `PlaceMention` of the same
place: every other statement kind is kept. -/
theorem eraseDeinitStmt_kind (st : MirAst.Statement) :
    (eraseDeinitStmt st).kind = st.kind ∨
      ∃ p, st.kind = .deinit p ∧ (eraseDeinitStmt st).kind = .placeMention p := by
  obtain ⟨kind, span⟩ := st
  cases kind with
  | deinit p =>
    obtain ⟨i, proj⟩ := p
    cases proj with
    | nil => exact .inl rfl
    | cons pe rest => exact .inr ⟨_, rfl, rfl⟩
  | _ => exact .inl rfl

@[simp] theorem hasStorageMarker_eraseDeinit (body : CapturedMir) (loc : Nat) :
    hasStorageMarker (eraseDeinit body) loc = hasStorageMarker body loc := by
  simp only [hasStorageMarker, eraseDeinit, List.any_map]
  refine congrArg (List.any body.basicBlocks) (funext fun bb => ?_)
  simp only [Function.comp_apply, eraseDeinitBlock, List.any_map]
  refine congrArg (List.any bb.statements) (funext fun st => ?_)
  rcases eraseDeinitStmt_kind st with h | ⟨p, h1, h2⟩
  · simp only [Function.comp_apply, h]
  · simp only [Function.comp_apply, h1, h2]

@[simp] theorem alwaysStorageLiveLocals_eraseDeinit (body : CapturedMir) :
    alwaysStorageLiveLocals (eraseDeinit body) = alwaysStorageLiveLocals body := by
  unfold alwaysStorageLiveLocals
  simp only [hasStorageMarker_eraseDeinit]
  rfl

@[simp] theorem initBlock_eraseDeinit (body : CapturedMir) :
    initBlock (eraseDeinit body) = initBlock body := by
  simp only [initBlock, alwaysStorageLiveLocals_eraseDeinit]

@[simp] theorem initLen_eraseDeinit (body : CapturedMir) :
    initLen (eraseDeinit body) = initLen body := by
  simp only [initLen, alwaysStorageLiveLocals_eraseDeinit]

@[simp] theorem bodyAddrTakenLocals_eraseDeinit (body : CapturedMir) :
    bodyAddrTakenLocals (eraseDeinit body) = bodyAddrTakenLocals body := by
  simp only [bodyAddrTakenLocals, eraseDeinit, List.flatMap_map]
  refine congrArg (List.flatMap · body.basicBlocks) (funext fun bb => ?_)
  simp only [eraseDeinitBlock, List.filterMap_map]
  refine congrArg (List.filterMap · bb.statements) (funext fun st => ?_)
  rcases eraseDeinitStmt_kind st with h | ⟨p, h1, h2⟩
  · simp only [Function.comp_apply, h]
  · simp only [Function.comp_apply, h1, h2]

@[simp] theorem nonScalarSlotsInit_eraseDeinit (body : CapturedMir) (locals : List LocalSlot) :
    nonScalarSlotsInit (eraseDeinit body) locals = nonScalarSlotsInit body locals := by
  unfold nonScalarSlotsInit
  simp only [bodyAddrTakenLocals_eraseDeinit]
  rfl

@[simp] theorem initMachineState_eraseDeinit (body : CapturedMir) (args : List Value) :
    initMachineState (eraseDeinit body) args = initMachineState body args := rfl

@[simp] theorem argsOk_eraseDeinit (body : CapturedMir) (args : List Value) :
    argsOk (eraseDeinit body) args = argsOk body args := rfl

theorem CtxOk.toEraseDeinit {body : CapturedMir} {ctx : Ctx} (h : CtxOk body ctx) :
    CtxOk (eraseDeinit body) ctx :=
  ⟨h.addrs, h.ret, h.baseLow⟩

/-- `StartRel` only depends on `body` through its locals, layouts, argument count, and number
of blocks, which `eraseDeinit` keeps. -/
theorem StartRel.toEraseDeinit {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {s : MachineState} {mInit : Mach} (h : StartRel body f ctx s mInit) :
    StartRel (eraseDeinit body) f ctx s mInit where
  threads := h.threads
  active := h.active
  allocs := h.allocs
  blk0 := h.blk0
  stmt0 := h.stmt0
  hasBlocks := by simpa using h.hasBlocks
  nlocals := h.nlocals
  slots := h.slots
  argsLive := h.argsLive
  tempsDead := h.tempsDead
  addrs := h.addrs
  ret := h.ret
  baseLow := h.baseLow
  borrows := h.borrows
  nextTag_pos := h.nextTag_pos
  callStack := h.callStack
  activeCallee := h.activeCallee
  protectors := h.protectors
  callerLocals := h.callerLocals

theorem StartRel.ofEraseDeinit {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {s : MachineState} {mInit : Mach} (h : StartRel (eraseDeinit body) f ctx s mInit) :
    StartRel body f ctx s mInit where
  threads := h.threads
  active := h.active
  allocs := h.allocs
  blk0 := h.blk0
  stmt0 := h.stmt0
  hasBlocks := by simpa using h.hasBlocks
  nlocals := h.nlocals
  slots := h.slots
  argsLive := h.argsLive
  tempsDead := h.tempsDead
  addrs := h.addrs
  ret := h.ret
  baseLow := h.baseLow
  borrows := h.borrows
  nextTag_pos := h.nextTag_pos
  callStack := h.callStack
  activeCallee := h.activeCallee
  protectors := h.protectors
  callerLocals := h.callerLocals

/-! ### Return-freedom and execution prefixes -/

/-- No `StateRelD`-related machine satisfies `ReturnRel`: in both disjuncts the active thread
has the 2-frame stack `[ctx.caller, calleeFrameL ..]` (for `HoleRel`, `m.threads = m0.threads`),
whereas `ReturnRel` requires a 1-frame stack. -/
theorem StateRelD.not_returnRel {body b' : CapturedMir} {f : Gen.Function} {ctx c' : Ctx}
    {s s' : MachineState} {v : Value} {m : Mach} (hrel : StateRelD body f ctx s m) :
    ¬ ReturnRel b' c' s' v m := by
  rcases hrel with hN | ⟨_, _, _, _, _, hHR⟩
  · exact hN.toStateRel.not_returnRel
  · obtain ⟨_, _, _, _, _, _, hthr0, _, _, _, _, hthr, _, _⟩ := hHR
    intro ⟨_, _, _, _, _, _, _, _, hthrR, _, _⟩
    rw [hthr, hthr0] at hthrR
    have hlen := congrArg (fun ts => ts.map (·.stack.length)) hthrR
    simp [thread1] at hlen

/-- Every Anneal execution prefix from `StateRelD`-related states is matched by MiniRust steps
to a `StateRelD`-related state, and no intermediate step satisfies `ReturnRel`. -/
theorem reaches_rel_no_returnRel_D {body : CapturedMir} {f : Gen.Function}
    (hfragD : inFragmentD body = true)
    (hf : translateFn body = some f) (ctx : Ctx) {t u : ITree MirEffect MirOutcome}
    {tr : List (Event MirEffect)} (h : Reaches t tr u) :
    ∀ (s : MachineState) (m : Mach), t = mirTree body s → StateRelD body f ctx s m →
      ∃ (n : Nat) (s' : MachineState) (m' : Mach), Interp.steps n m = .ok m' ∧
        StateRelD body f ctx s' m' ∧ u = mirTree body s' ∧
        (∀ k ≤ n, ∀ mk, Interp.steps k m = .ok mk →
          ∀ b' c' s'' v, ¬ ReturnRel b' c' s'' v mk) := by
  induction h with
  | refl t =>
    intro s m ht hrel
    refine ⟨0, s, m, rfl, hrel, ht, fun k hk mk hmk => ?_⟩
    have hk0 : k = 0 := by omega
    subst hk0
    cases hmk
    exact fun _ _ _ _ => hrel.not_returnRel
  | tau hobs _ ih =>
    intro s m ht hrel
    subst ht
    have hsr := step_correspondence_D body f hfragD hf ctx s m hrel
    rw [mirTree_observe] at hobs
    generalize stepMirFn body s = node at hsr hobs
    cases node with
    | ret r => simp [ITreeF.map] at hobs
    | vis i k => simp [ITreeF.map] at hobs
    | tau x =>
      simp only [ITreeF.map, ITreeF.tau.injEq] at hobs
      cases x with
      | running s1 =>
        obtain ⟨m1, hm1, hrel1⟩ := hsr
        obtain ⟨n, s', m', hsteps, hrel', hu, hno⟩ := ih s1 m1 hobs.symm hrel1
        refine ⟨n + 1, s', m', by simp [Interp.steps, hm1, hsteps], hrel', hu,
          fun k hk mk hmk => ?_⟩
        cases k with
        | zero =>
          cases hmk
          exact fun _ _ _ _ => hrel.not_returnRel
        | succ k' =>
          simp only [Interp.steps, hm1, ok_bind] at hmk
          exact hno k' (by omega) mk hmk
      | halted _ => exact False.elim hsr
      | faulted _ => exact False.elim hsr
  | vis hobs hnf o _ ih =>
    intro s m ht hrel
    subst ht
    have hsr := step_correspondence_D body f hfragD hf ctx s m hrel
    rw [mirTree_observe] at hobs
    generalize stepMirFn body s = node at hsr hobs
    cases node with
    | ret r => simp [ITreeF.map] at hobs
    | tau x => simp [ITreeF.map] at hobs
    | vis i0 k0 =>
      simp only [ITreeF.map] at hobs
      injection hobs with hi hk
      subst hi
      have hk' := eq_of_heq hk
      subst hk'
      cases i0 with
      | inl a => exact False.elim (hnf trivial)
      | inr b =>
        cases b with
        | inr c => exact False.elim hsr
        | inl ob =>
          obtain ⟨s1, m1, hk1, hm1, hrel1⟩ := hsr
          cases o
          have ht' : ITree.cofix (stepMirState body) (k0 PUnit.unit) = mirTree body s1 := by
            rw [hk1]; rfl
          obtain ⟨n, s', m', hsteps, hrel', hu, hno⟩ := ih s1 m1 ht' hrel1
          refine ⟨n + 1, s', m', by simp [Interp.steps, hm1, hsteps], hrel', hu,
            fun k hk mk hmk => ?_⟩
          cases k with
          | zero =>
            cases hmk
            exact fun _ _ _ _ => hrel.not_returnRel
          | succ k' =>
            simp only [Interp.steps, hm1, ok_bind] at hmk
            exact hno k' (by omega) mk hmk

/-- Every Anneal execution prefix from `StateRelD`-related states is matched by MiniRust steps
to a `StateRelD`-related state. -/
theorem reaches_rel_D {body : CapturedMir} {f : Gen.Function} (hfragD : inFragmentD body = true)
    (hf : translateFn body = some f) (ctx : Ctx) {t u : ITree MirEffect MirOutcome}
    {tr : List (Event MirEffect)} (h : Reaches t tr u) :
    ∀ (s : MachineState) (m : Mach), t = mirTree body s → StateRelD body f ctx s m →
      ∃ (n : Nat) (s' : MachineState) (m' : Mach), Interp.steps n m = .ok m' ∧
        StateRelD body f ctx s' m' ∧ u = mirTree body s' :=
  fun s m ht hrel =>
    let ⟨n, s', m', hsteps, hrel', hu, _⟩ := reaches_rel_no_returnRel_D hfragD hf ctx h s m ht hrel
    ⟨n, s', m', hsteps, hrel', hu⟩

/-- **Returns (`StateRelD`).** If Anneal's semantics of an `inFragmentD` body `body` from `s`
returns `v` (along any trace of branch observations), MiniRust, started from a
`StateRelD`-related machine, performs the corresponding function return after finitely many
steps. -/
theorem run_ret_D {body : CapturedMir} {f : Gen.Function} (hfragD : inFragmentD body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRelD body f ctx s m) {tr : List (Event MirEffect)} {v : Value}
    {mem : MirSemantics.Memory} (hret : ReachesRet (mirTree body s) tr (.normal (v, mem))) :
    ∃ (n : Nat) (s' : MachineState) (m' : Mach),
      Interp.steps n m = .ok m' ∧ ReturnRel body ctx s' v m' := by
  obtain ⟨u, hreach, hu⟩ := hret
  obtain ⟨n, s', m', hsteps, hrel', rfl⟩ := reaches_rel_D hfragD hf ctx hreach s m rfl hrel
  have hsr := step_correspondence_D body f hfragD hf ctx s' m' hrel'
  rw [mirTree_observe] at hu
  generalize stepMirFn body s' = node at hsr hu
  cases node with
  | tau x => simp [ITreeF.map] at hu
  | vis i k => simp [ITreeF.map] at hu
  | ret r =>
    simp only [ITreeF.map, ITreeF.ret.injEq] at hu
    subst hu
    obtain ⟨m'', hm'', hret⟩ := hsr
    exact ⟨n + 1, s', m'', by rw [steps_add, hsteps]; simp [Interp.steps, hm''], hret⟩

/-! ### The init block and the call tree -/

/-- **Init block (`StateRelD`).** From `StartRel` (Anneal at `(0, 0)` and MiniRust at
`f.start`), `initLen body` MiniRust steps execute `minimize`'s init block and land in
`StateRelD` (its `StateRelN` disjunct for `eraseDeinit body`, by `step_start_NF`). -/
theorem step_start_D {body : CapturedMir} {f : Gen.Function} (hfragD : inFragmentD body = true)
    (hf : translateFn body = some f) {ctx : Ctx} {s : MachineState} {mInit : Mach}
    (hstart : StartRel body f ctx s mInit)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    ∃ m0, Interp.steps (initLen body) mInit = .ok m0 ∧ StateRelD body f ctx s m0 := by
  have hfragE := (inFragmentD_spec hfragD).1
  have hst0 : f.start = bbName (eraseDeinit body).basicBlocks.length ∧
      mapGet f.blocks (bbName (eraseDeinit body).basicBlocks.length) =
        some (initBlock (eraseDeinit body)) := by
    rw [eraseDeinit_length, initBlock_eraseDeinit]
    exact translateFn_start body f hf
  obtain ⟨m0, hm0, hrel0⟩ := step_start_NF hfragE (fnLocalsSpec_eraseDeinit hf) hst0
    hstart.toEraseDeinit (by rw [nonScalarSlotsInit_eraseDeinit]; exact hns)
  rw [initLen_eraseDeinit] at hm0
  exact ⟨m0, hm0, .inl hrel0⟩

/-- **Returns from `f.start` (`inFragmentD`).** Starting MiniRust at the `minimize` entry
block under `StartRel` steps through `initBlock` into `bb0` and then matches Anneal's return
from `s`. -/
theorem run_ret_from_start_D {body : CapturedMir} {f : Gen.Function}
    (hfragD : inFragmentD body = true) (hf : translateFn body = some f) (ctx : Ctx)
    (s : MachineState) (mInit : Mach) (hstart : StartRel body f ctx s mInit)
    {tr : List (Event MirEffect)} {v : Value} {mem : MirSemantics.Memory}
    (hret : ReachesRet (mirTree body s) tr (.normal (v, mem)))
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    ∃ (n : Nat) (s' : MachineState) (m' : Mach),
      Interp.steps n mInit = .ok m' ∧ ReturnRel body ctx s' v m' := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start_D hfragD hf hstart hns
  obtain ⟨n, s', m', hsteps, hret'⟩ := run_ret_D hfragD hf ctx s m0 hrel0 hret
  exact ⟨initLen body + n, s', m', by rw [steps_add, hm0, ok_bind, hsteps], hret'⟩

/-- Entry-state bridge for `inFragmentD` bodies (`initMachineState_startRel` on
`eraseDeinit body`, transferred back to `body`). -/
theorem initMachineState_startRel_D {body : CapturedMir} {f : Gen.Function}
    (hfragD : inFragmentD body = true) (ctx : Ctx) (hctx : CtxOk body ctx)
    (args : List Value) (hargs : argsOk body args = true) (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals body.layouts) :
    StartRel body f ctx (initMachineState body args) mInit :=
  (initMachineState_startRel (inFragmentD_spec hfragD).1 ctx hctx.toEraseDeinit args hargs mInit
    hthreads hactive hallocs).ofEraseDeinit

/-- `nonScalarSlotsInit` holds on the entry state of `mirCallTree body args`. -/
theorem initMachineState_nonScalar_D {body : CapturedMir} (hfragD : inFragmentD body = true)
    (args : List Value) (hargs : argsOk body args = true) :
    nonScalarSlotsInit body (initMachineState body args).frame.locals = true := by
  rw [← nonScalarSlotsInit_eraseDeinit]
  exact initMachineState_nonScalar (inFragmentD_spec hfragD).1 args hargs

/-- **Call-tree return (`inFragmentD`).** For any `inFragmentD` body and well-typed `args`, if
`mirCallTree body args` returns `v`, MiniRust started at `f.start` performs the corresponding
return (`ReturnRel`) after finitely many steps. Same hypotheses as `mirCall_ret`, with
`inFragmentD` in place of `inFragment`. -/
theorem mirCall_ret_D {body : CapturedMir} {f : Gen.Function} (hfrag : inFragmentD body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (hctx : CtxOk body ctx)
    (args : List Value) (hargs : argsOk body args = true) (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals body.layouts)
    {tr : List (Event MirEffect)} {v : Value} {mem : MirSemantics.Memory}
    (hret : ReachesRet (mirCallTree body args) tr (.normal (v, mem))) :
    ∃ (n : Nat) (s' : MachineState) (m' : Mach),
      Interp.steps n mInit = .ok m' ∧ ReturnRel body ctx s' v m' :=
  run_ret_from_start_D hfrag hf ctx (initMachineState body args) mInit
    (initMachineState_startRel_D hfrag ctx hctx args hargs mInit hthreads hactive hallocs) hret
    (initMachineState_nonScalar_D hfrag args hargs)

/-- No prefix step `j ≤ initLen body` of `step_start_D` can satisfy `ReturnRel`. -/
theorem step_start_no_returnRel_D {body : CapturedMir} {f : Gen.Function}
    (hfragD : inFragmentD body = true) (hf : translateFn body = some f)
    {ctx : Ctx} {s : MachineState} {mInit : Mach}
    (hstart : StartRel body f ctx s mInit)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    ∀ j ≤ initLen body, ∀ mj, Interp.steps j mInit = .ok mj →
      ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mj := by
  have hkey : ∀ (b : CapturedMir), inFragment b = true → FnLocalsSpec b f →
      (f.start = bbName b.basicBlocks.length ∧
        mapGet f.blocks (bbName b.basicBlocks.length) = some (initBlock b)) →
      StartRel b f ctx s mInit →
      nonScalarSlotsInit b s.frame.locals = true →
      ∀ k, k ≤ (alwaysStorageLiveLocals b).length → ∃ m lm,
      Interp.steps k mInit = .ok m ∧
      Shape m ctx [ctx.caller, calleeFrameL f ctx lm b.basicBlocks.length k]
        m.mem.memory.allocations ∧
      LocalsOkA b ctx ((alwaysStorageLiveLocals b).take k) s.frame.locals lm
        m.mem.memory.allocations ∧
      NonScalarLive b s.frame.locals lm ∧
      (∀ j, j < b.argCount + 1 → mapGet lm (localName j) = some (localPtr ctx j)) := by
    intro b hfrag hfl hst0 hstartB hnsB
    obtain ⟨_, hargs, hn31, _, hdeclsOk, htemps, _, _, _, _⟩ := inFragment_spec b hfrag
    obtain ⟨hfstart, hinit⟩ := hst0
    have hAnd := alwaysStorageLiveLocals_nodup b
    have hlenS : (initBlock b).statements.length = (alwaysStorageLiveLocals b).length := by
      simp [initBlock]
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨mInit, localsMap ctx (b.argCount + 1), rfl, ⟨?_, hstartB.active, rfl⟩,
        by simpa using hstartB.localsOk hargs (inFragment_params_not_ptr b hfrag),
        hstartB.nonScalarLive hfrag hnsB, fun j hj => mapGet_localsMap ctx _ j hj⟩
      rw [hstartB.threads]
      simp [calleeFrame, calleeFrameL, hfstart]
    | succ k ih =>
      intro hk
      obtain ⟨m, lm, hm, hsh, hlo, hnsL, hlmP⟩ := ih (by omega)
      have hkA : k < (alwaysStorageLiveLocals b).length := by omega
      obtain ⟨hlo1, hlo2⟩ := alwaysStorageLiveLocals_spec
        (List.getElem_mem (l := alwaysStorageLiveLocals b) hkA)
      have hnot : (alwaysStorageLiveLocals b)[k] ∉ (alwaysStorageLiveLocals b).take k := by
        intro hmem
        obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hmem
        rw [List.getElem_take] at hjk
        have := hAnd.getElem_inj.mp hjk
        simp at hj
        omega
      have hst : (initBlock b).statements[k]? =
          some (.StorageLive (localName (alwaysStorageLiveLocals b)[k])) := by
        simp [initBlock, List.getElem?_map, List.getElem?_eq_getElem hkA]
      have htake : (alwaysStorageLiveLocals b).take (k + 1) =
          (alwaysStorageLiveLocals b).take k ++ [(alwaysStorageLiveLocals b)[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hkA, Option.toList_some]
      generalize (alwaysStorageLiveLocals b)[k] = a at hnot hlo1 hlo2 hst htake
      obtain ⟨d, hd⟩ : ∃ d, b.localDecls[a]? = some d := ⟨_, List.getElem?_eq_getElem hlo2⟩
      have hscalar : (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true := by
        have hdrop : (b.localDecls.drop (b.argCount + 1))[a - (b.argCount + 1)]? = some d := by
          rw [List.getElem?_drop, Nat.add_sub_cancel' hlo1, hd]
        exact htemps d (List.mem_of_getElem? hdrop)
      have hsa : s.frame.locals[a]? = some .dead := hstartB.tempsDead a (by omega) hlo2
      have hpa : mapGet lm (localName a) = none := by
        cases hp : mapGet lm (localName a) with
        | none => rfl
        | some p =>
          have := (hlo.live a .dead hsa).mp (by simp [hp])
          simp [hnot] at this
      obtain ⟨m3, lm3, hm3, hsh3, hlo3, hns3, hlm3⟩ :=
        evalStatement_storageLive_init hfl
        (resetPick_shape hsh) hlo hdeclsOk hnsL a d hd hscalar hsa hpa hstartB.baseLow hn31
      obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee hsh3
      have hne : ((k : Nat) : Int) ≠ ((initBlock b).statements.length : Int) := by
        rw [hlenS]; omega
      have hstep : Interp.step m = .ok m4 := by
        rw [step_callee hsh (initBlock b) hinit]
        simp [hne, listIndex_nat _ _ _ hst, hm3, hm4, check_after h4]
      refine ⟨m4, lm3, ?_, ⟨h4.threads, h4.active, rfl⟩, ?_, hns3,
        fun j hj => (hlm3 j (by omega)).trans (hlmP j hj)⟩
      · rw [steps_add, hm, ok_bind, steps_one hstep]
      · rw [htake, h4.allocs]
        exact hlo3
  have hfragE := (inFragmentD_spec hfragD).1
  have hst0 : f.start = bbName (eraseDeinit body).basicBlocks.length ∧
      mapGet f.blocks (bbName (eraseDeinit body).basicBlocks.length) =
        some (initBlock (eraseDeinit body)) := by
    rw [eraseDeinit_length, initBlock_eraseDeinit]
    exact translateFn_start body f hf
  intro j hj mj hmj b' c' s' v
  rcases Nat.lt_or_eq_of_le hj with hjlt | rfl
  · obtain ⟨mk, lmk, hmk, hshk, _⟩ :=
      hkey (eraseDeinit body) hfragE (fnLocalsSpec_eraseDeinit hf) hst0
        hstart.toEraseDeinit (by rw [nonScalarSlotsInit_eraseDeinit]; exact hns) j
        (by rw [alwaysStorageLiveLocals_eraseDeinit]; rw [initLen] at hjlt; omega)
    rw [hmk] at hmj
    cases hmj
    exact Shape.not_returnRel_of_ne_nil (callerFrames := [ctx.caller]) hshk (by simp)
  · obtain ⟨m0, hm0, hrel0⟩ := step_start_D hfragD hf hstart hns
    rw [hm0] at hmj
    cases hmj
    exact hrel0.not_returnRel

/-- **Localized single-body UB (`StateRelD`).** -/
theorem run_ub_rel_D {body : CapturedMir} {f : Gen.Function} (hfragD : inFragmentD body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRelD body f ctx s m) {tr : List (Event MirEffect)} {u : ITree MirEffect MirOutcome}
    (hreach : Reaches (mirTree body s) tr u) (hfault : FaultNow u) :
    ∃ (n : Nat) (sLast : MachineState) (mLast : Mach) (msg : String),
      Interp.steps n m = .ok mLast ∧ StateRelD body f ctx sLast mLast ∧
      Interp.step mLast = .error (.ub msg) ∧ Interp.steps (n + 1) m = .error (.ub msg) ∧
      (∀ k ≤ n, ∀ mk, Interp.steps k m = .ok mk →
        ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mk) := by
  obtain ⟨t', i, k, htau, hobs, hfi⟩ := hfault
  obtain ⟨n1, s1, m1, h1, hrel1, rfl, hno1⟩ :=
    reaches_rel_no_returnRel_D hfragD hf ctx hreach s m rfl hrel
  obtain ⟨n2, s2, m2, h2, hrel2, rfl, hno2⟩ :=
    reaches_rel_no_returnRel_D hfragD hf ctx (tauStar_reaches htau) s1 m1 rfl hrel1
  have hsr := step_correspondence_D body f hfragD hf ctx s2 m2 hrel2
  rw [mirTree_observe] at hobs
  generalize stepMirFn body s2 = node at hsr hobs
  cases node with
  | ret r => simp [ITreeF.map] at hobs
  | tau x => simp [ITreeF.map] at hobs
  | vis i0 k0 =>
    simp only [ITreeF.map] at hobs
    injection hobs with hi _
    subst hi
    cases i0 with
    | inr b =>
      cases b with
      | inl _ => exact False.elim hfi
      | inr _ => exact False.elim hfi
    | inl a =>
      cases a with
      | fail fk =>
        cases fk with
        | unsupported => exact False.elim hsr
        | outOfFuel => exact False.elim hsr
        | ub =>
          obtain ⟨msg, hmsg⟩ := hsr
          have h12 : Interp.steps (n1 + n2) m = .ok m2 := by
            rw [steps_add, h1, ok_bind, h2]
          refine ⟨n1 + n2, s2, m2, msg, h12, hrel2, hmsg, ?_,
            steps_add_no_returnRel h1 hno1 hno2⟩
          rw [steps_add, h12, ok_bind, Interp.steps, hmsg]
          rfl

/-- **Localized single-body UB from `f.start` (`inFragmentD`).** -/
theorem run_ub_rel_from_start_D {body : CapturedMir} {f : Gen.Function}
    (hfragD : inFragmentD body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : StartRel body f ctx s mInit)
    {tr : List (Event MirEffect)} {u : ITree MirEffect MirOutcome}
    (hreach : Reaches (mirTree body s) tr u) (hfault : FaultNow u)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    ∃ (n : Nat) (sLast : MachineState) (mLast : Mach) (msg : String),
      Interp.steps n mInit = .ok mLast ∧ StateRelD body f ctx sLast mLast ∧
      Interp.step mLast = .error (.ub msg) ∧ Interp.steps (n + 1) mInit = .error (.ub msg) ∧
      (∀ k ≤ n, ∀ mk, Interp.steps k mInit = .ok mk →
        ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mk) := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start_D hfragD hf hstart hns
  have hno0 := step_start_no_returnRel_D hfragD hf hstart hns
  obtain ⟨n, sLast, mLast, msg, hsteps, hrelLast, hstep, hsteps1, hno⟩ :=
    run_ub_rel_D hfragD hf ctx s m0 hrel0 hreach hfault
  refine ⟨initLen body + n, sLast, mLast, msg, ?_, hrelLast, hstep, ?_,
    steps_add_no_returnRel hm0 hno0 hno⟩
  · rw [steps_add, hm0, ok_bind, hsteps]
  · rw [Nat.add_assoc, steps_add, hm0, ok_bind, hsteps1]

/-- **UB (`StateRelD`).** -/
theorem run_ub_D {body : CapturedMir} {f : Gen.Function} (hfragD : inFragmentD body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRelD body f ctx s m) {tr : List (Event MirEffect)} {u : ITree MirEffect MirOutcome}
    (hreach : Reaches (mirTree body s) tr u) (hfault : FaultNow u) :
    ∃ (n : Nat) (msg : String), Interp.steps n m = .error (.ub msg) := by
  obtain ⟨n, _, _, msg, _, _, _, hsteps1, _⟩ := run_ub_rel_D hfragD hf ctx s m hrel hreach hfault
  exact ⟨n + 1, msg, hsteps1⟩

/-- **UB from `f.start` (`inFragmentD`).** -/
theorem run_ub_from_start_D {body : CapturedMir} {f : Gen.Function}
    (hfragD : inFragmentD body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : StartRel body f ctx s mInit)
    {tr : List (Event MirEffect)} {u : ITree MirEffect MirOutcome}
    (hreach : Reaches (mirTree body s) tr u) (hfault : FaultNow u)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    ∃ (n : Nat) (msg : String), Interp.steps n mInit = .error (.ub msg) := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start_D hfragD hf hstart hns
  obtain ⟨n, msg, hsteps⟩ := run_ub_D hfragD hf ctx s m0 hrel0 hreach hfault
  exact ⟨initLen body + n, msg, by rw [steps_add, hm0, ok_bind, hsteps]⟩

/-- **Errors (`StateRelD`).** Converse error soundness for `inFragmentD`. -/
theorem steps_error_D {body : CapturedMir} {f : Gen.Function} (hfragD : inFragmentD body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (n : Nat) :
    ∀ (s : MachineState) (m : Mach) (e : Stop), StateRelD body f ctx s m →
      Interp.steps n m = .error e →
      (∃ msg, e = .ub msg ∧ ∃ tr u, Reaches (mirTree body s) tr u ∧ FaultNow u) ∨
      (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k m = .ok mRet ∧
        ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) := by
  induction n with
  | zero => intro s m e _ h; simp [Interp.steps] at h
  | succ n ih =>
    intro s m e hrel h
    have hsr := step_correspondence_D body f hfragD hf ctx s m hrel
    have hobs := mirTree_observe body s
    generalize stepMirFn body s = node at hsr hobs
    cases node with
    | tau x =>
      simp only [ITreeF.map] at hobs
      cases x with
      | running s1 =>
        obtain ⟨m1, hm1, hrel1⟩ := hsr
        simp only [Interp.steps, hm1, ok_bind] at h
        rcases ih s1 m1 e hrel1 h with
          ⟨msg, he, tr, u, hr, hfault⟩ | ⟨k, s', mRet, tr, v, mem, hklt, hksteps, hretRel, u, hr, hu⟩
        · exact .inl ⟨msg, he, tr, u, .tau hobs hr, hfault⟩
        · exact .inr ⟨k + 1, s', mRet, tr, v, mem, by omega,
            by simp [Interp.steps, hm1, hksteps], hretRel, u, .tau hobs hr, hu⟩
      | halted _ => exact False.elim hsr
      | faulted _ => exact False.elim hsr
    | ret r =>
      simp only [ITreeF.map] at hobs
      cases r with
      | normal p =>
        obtain ⟨mRet, hmRet, hretRel⟩ := hsr
        cases n with
        | zero => simp [Interp.steps, hmRet] at h
        | succ n' =>
          exact .inr ⟨1, s, mRet, [], p.1, p.2, by omega,
            by simp [Interp.steps, hmRet], hretRel, mirTree body s, .refl _, hobs⟩
      | panic => exact False.elim hsr
      | abort => exact False.elim hsr
    | vis i0 k0 =>
      simp only [ITreeF.map] at hobs
      cases i0 with
      | inl a =>
        cases a with
        | fail fk =>
          cases fk with
          | unsupported => exact False.elim hsr
          | outOfFuel => exact False.elim hsr
          | ub =>
            obtain ⟨msg, hmsg⟩ := hsr
            simp [Interp.steps, hmsg] at h
            exact .inl ⟨msg, h.symm, [], mirTree body s, .refl _,
              ⟨mirTree body s, _, _, .refl _, hobs, trivial⟩⟩
      | inr b =>
        cases b with
        | inr _ => exact False.elim hsr
        | inl ob =>
          obtain ⟨s1, m1, hk1, hm1, hrel1⟩ := hsr
          simp only [Interp.steps, hm1, ok_bind] at h
          have hnext : ITree.cofix (stepMirState body) (k0 PUnit.unit) = mirTree body s1 := by
            rw [hk1]; rfl
          rcases ih s1 m1 e hrel1 h with
            ⟨msg, he, tr, u, hr, hfault⟩ | ⟨k, s', mRet, tr, v, mem, hklt, hksteps, hretRel, u, hr, hu⟩
          · refine .inl ⟨msg, he, ⟨.inr (.inl ob), PUnit.unit⟩ :: tr, u,
              .vis hobs (fun h => h) PUnit.unit ?_, hfault⟩
            rw [hnext]; exact hr
          · refine .inr ⟨k + 1, s', mRet, ⟨.inr (.inl ob), PUnit.unit⟩ :: tr, v, mem, by omega,
              by simp [Interp.steps, hm1, hksteps], hretRel, u,
              .vis hobs (fun h => h) PUnit.unit ?_, hu⟩
            rw [hnext]; exact hr

/-- **Errors from `f.start` (`inFragmentD`).** -/
theorem steps_error_from_start_D {body : CapturedMir} {f : Gen.Function}
    (hfragD : inFragmentD body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (n : Nat) (s : MachineState) (mInit : Mach) (e : Stop)
    (hstart : StartRel body f ctx s mInit) (h : Interp.steps n mInit = .error e)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    (∃ msg, e = .ub msg ∧ ∃ tr u, Reaches (mirTree body s) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start_D hfragD hf hstart hns
  by_cases hn : n ≤ initLen body
  · obtain ⟨mj, hmj⟩ := steps_ok_mono hn hm0
    rw [hmj] at h
    cases h
  · obtain ⟨n', rfl⟩ : ∃ n', n = initLen body + n' := ⟨n - initLen body, by omega⟩
    rw [steps_add, hm0, ok_bind] at h
    rcases steps_error_D hfragD hf ctx n' s m0 e hrel0 h with
      hUb | ⟨k, s', mRet, tr, v, mem, hklt, hksteps, hretRel, hret⟩
    · exact .inl hUb
    · exact .inr ⟨initLen body + k, s', mRet, tr, v, mem, by omega,
        by rw [steps_add, hm0, ok_bind, hksteps], hretRel, hret⟩

/-- **UB-freedom transfer (`StateRelD`).** -/
theorem mirNoUB_safe_D {body : CapturedMir} {f : Gen.Function} (hfragD : inFragmentD body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRelD body f ctx s m) (hsafe : MirNoUBTree (mirTree body s))
    {n : Nat} {e : Stop} (herr : Interp.steps n m = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k m = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem)) := by
  rcases steps_error_D hfragD hf ctx n s m e hrel herr with ⟨_, _, tr, u, hr, hfault⟩ | hret
  · exact False.elim (hsafe tr u hr hfault)
  · exact hret

/-- **UB-freedom transfer from `f.start` (`inFragmentD`).** -/
theorem mirNoUB_safe_from_start_D {body : CapturedMir} {f : Gen.Function}
    (hfragD : inFragmentD body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : StartRel body f ctx s mInit) (hsafe : MirNoUBTree (mirTree body s))
    {n : Nat} {e : Stop} (herr : Interp.steps n mInit = .error e)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem)) := by
  rcases steps_error_from_start_D hfragD hf ctx n s mInit e hstart herr hns with
    ⟨_, _, tr, u, hr, hfault⟩ | hret
  · exact False.elim (hsafe tr u hr hfault)
  · exact hret

/-- **Total `n`-step outcome trichotomy (`StateRelD`).** -/
theorem steps_outcome_D {body : CapturedMir} {f : Gen.Function} (hfragD : inFragmentD body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (n : Nat) :
    ∀ (s : MachineState) (m : Mach), StateRelD body f ctx s m →
      (∃ s' m' tr, Interp.steps n m = .ok m' ∧ StateRelD body f ctx s' m' ∧
        Reaches (mirTree body s) tr (mirTree body s')) ∨
      (∃ k s' mRet tr v mem, k ≤ n ∧ Interp.steps k m = .ok mRet ∧
        ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) ∨
      (∃ msg, Interp.steps n m = .error (.ub msg) ∧
        ∃ tr u, Reaches (mirTree body s) tr u ∧ FaultNow u) := by
  induction n with
  | zero =>
    intro s m hrel
    exact .inl ⟨s, m, [], rfl, hrel, .refl _⟩
  | succ n ih =>
    intro s m hrel
    have hsr := step_correspondence_D body f hfragD hf ctx s m hrel
    have hobs := mirTree_observe body s
    generalize stepMirFn body s = node at hsr hobs
    cases node with
    | tau x =>
      simp only [ITreeF.map] at hobs
      cases x with
      | running s1 =>
        obtain ⟨m1, hm1, hrel1⟩ := hsr
        rcases ih s1 m1 hrel1 with
          ⟨s', m', tr, hsteps, hrel', hr⟩ |
          ⟨k, s', mRet, tr, v, mem, hkle, hksteps, hretRel, u, hr, hu⟩ |
          ⟨msg, herr, tr, u, hr, hfault⟩
        · exact .inl ⟨s', m', tr, by simp [Interp.steps, hm1, hsteps], hrel', .tau hobs hr⟩
        · exact .inr (.inl ⟨k + 1, s', mRet, tr, v, mem, by omega,
            by simp [Interp.steps, hm1, hksteps], hretRel, u, .tau hobs hr, hu⟩)
        · exact .inr (.inr ⟨msg, by simp [Interp.steps, hm1, herr], tr, u, .tau hobs hr, hfault⟩)
      | halted _ => exact False.elim hsr
      | faulted _ => exact False.elim hsr
    | ret r =>
      simp only [ITreeF.map] at hobs
      cases r with
      | normal p =>
        obtain ⟨mRet, hmRet, hretRel⟩ := hsr
        exact .inr (.inl ⟨1, s, mRet, [], p.1, p.2, by omega,
          by simp [Interp.steps, hmRet], hretRel, mirTree body s, .refl _, hobs⟩)
      | panic => exact False.elim hsr
      | abort => exact False.elim hsr
    | vis i0 k0 =>
      simp only [ITreeF.map] at hobs
      cases i0 with
      | inl a =>
        cases a with
        | fail fk =>
          cases fk with
          | unsupported => exact False.elim hsr
          | outOfFuel => exact False.elim hsr
          | ub =>
            obtain ⟨msg, hmsg⟩ := hsr
            exact .inr (.inr ⟨msg, by simp [Interp.steps, hmsg], [], mirTree body s, .refl _,
              ⟨mirTree body s, _, _, .refl _, hobs, trivial⟩⟩)
      | inr b =>
        cases b with
        | inr _ => exact False.elim hsr
        | inl ob =>
          obtain ⟨s1, m1, hk1, hm1, hrel1⟩ := hsr
          have hnext : ITree.cofix (stepMirState body) (k0 PUnit.unit) = mirTree body s1 := by
            rw [hk1]; rfl
          rcases ih s1 m1 hrel1 with
            ⟨s', m', tr, hsteps, hrel', hr⟩ |
            ⟨k, s', mRet, tr, v, mem, hkle, hksteps, hretRel, u, hr, hu⟩ |
            ⟨msg, herr, tr, u, hr, hfault⟩
          · refine .inl ⟨s', m', ⟨.inr (.inl ob), PUnit.unit⟩ :: tr,
              by simp [Interp.steps, hm1, hsteps], hrel',
              .vis hobs (fun h => h) PUnit.unit ?_⟩
            rw [hnext]; exact hr
          · refine .inr (.inl ⟨k + 1, s', mRet, ⟨.inr (.inl ob), PUnit.unit⟩ :: tr,
              v, mem, by omega, by simp [Interp.steps, hm1, hksteps], hretRel, u,
              .vis hobs (fun h => h) PUnit.unit ?_, hu⟩)
            rw [hnext]; exact hr
          · refine .inr (.inr ⟨msg, by simp [Interp.steps, hm1, herr],
              ⟨.inr (.inl ob), PUnit.unit⟩ :: tr, u,
              .vis hobs (fun h => h) PUnit.unit ?_, hfault⟩)
            rw [hnext]; exact hr

/-- **Total `(initLen body + n)`-step outcome trichotomy from `f.start` (`StateRelD`).** -/
theorem steps_outcome_from_start_D {body : CapturedMir} {f : Gen.Function}
    (hfragD : inFragmentD body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (n : Nat) (s : MachineState) (mInit : Mach)
    (hstart : StartRel body f ctx s mInit)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    (∃ s' m' tr, Interp.steps (initLen body + n) mInit = .ok m' ∧ StateRelD body f ctx s' m' ∧
      Reaches (mirTree body s) tr (mirTree body s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen body + n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen body + n) mInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirTree body s) tr u ∧ FaultNow u) := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start_D hfragD hf hstart hns
  rcases steps_outcome_D hfragD hf ctx n s m0 hrel0 with
    ⟨s', m', tr, hsteps, hrel', hr⟩ |
    ⟨k, s', mRet, tr, v, mem, hkle, hksteps, hretRel, hret⟩ |
    ⟨msg, herr, hfault⟩
  · exact .inl ⟨s', m', tr, by rw [steps_add, hm0, ok_bind, hsteps], hrel', hr⟩
  · exact .inr (.inl ⟨initLen body + k, s', mRet, tr, v, mem, by omega,
      by rw [steps_add, hm0, ok_bind, hksteps], hretRel, hret⟩)
  · exact .inr (.inr ⟨msg, by rw [steps_add, hm0, ok_bind, herr], hfault⟩)

/-- **Forward progress under `MirNoUBTree` (`StateRelD`).** -/
theorem mirNoUB_progress_D {body : CapturedMir} {f : Gen.Function}
    (hfragD : inFragmentD body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRelD body f ctx s m) (hsafe : MirNoUBTree (mirTree body s)) (n : Nat) :
    (∃ s' m' tr, Interp.steps n m = .ok m' ∧ StateRelD body f ctx s' m' ∧
      Reaches (mirTree body s) tr (mirTree body s')) ∨
    (∃ k s' mRet tr v mem, k ≤ n ∧ Interp.steps k m = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) := by
  rcases steps_outcome_D hfragD hf ctx n s m hrel with hrun | hret | ⟨_, _, tr, u, hr, hfault⟩
  · exact .inl hrun
  · exact .inr hret
  · exact False.elim (hsafe tr u hr hfault)

/-- **Forward progress from `f.start` under `MirNoUBTree` (`StateRelD`).** -/
theorem mirNoUB_progress_from_start_D {body : CapturedMir} {f : Gen.Function}
    (hfragD : inFragmentD body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : StartRel body f ctx s mInit) (hsafe : MirNoUBTree (mirTree body s)) (n : Nat)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    (∃ s' m' tr, Interp.steps (initLen body + n) mInit = .ok m' ∧ StateRelD body f ctx s' m' ∧
      Reaches (mirTree body s) tr (mirTree body s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen body + n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start_D hfragD hf hstart hns
  rcases mirNoUB_progress_D hfragD hf ctx s m0 hrel0 hsafe n with
    ⟨s', m', tr, hsteps, hrel', hr⟩ | ⟨k, s', mRet, tr, v, mem, hkle, hksteps, hretRel, hret⟩
  · exact .inl ⟨s', m', tr, by rw [steps_add, hm0, ok_bind, hsteps], hrel', hr⟩
  · exact .inr ⟨initLen body + k, s', mRet, tr, v, mem, by omega,
      by rw [steps_add, hm0, ok_bind, hksteps], hretRel, hret⟩

/-- **Diverging UB-free execution from `StateRelD`.** -/
theorem mirNoUB_diverges_steps_ok_D {body : CapturedMir} {f : Gen.Function}
    (hfragD : inFragmentD body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRelD body f ctx s m) (hsafe : MirNoUBTree (mirTree body s))
    (hdiv : ∀ tr o, ¬ ReachesRet (mirTree body s) tr o) (n : Nat) :
    ∃ s' m' tr, Interp.steps n m = .ok m' ∧ StateRelD body f ctx s' m' ∧
      Reaches (mirTree body s) tr (mirTree body s') := by
  rcases mirNoUB_progress_D hfragD hf ctx s m hrel hsafe n with
    hrun | ⟨_, _, _, tr, v, mem, _, _, _, hret⟩
  · exact hrun
  · exact False.elim (hdiv tr (.normal (v, mem)) hret)

/-- **Diverging UB-free execution from `f.start` (`inFragmentD`).** -/
theorem mirNoUB_diverges_from_start_D {body : CapturedMir} {f : Gen.Function}
    (hfragD : inFragmentD body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : StartRel body f ctx s mInit) (hsafe : MirNoUBTree (mirTree body s))
    (hdiv : ∀ tr o, ¬ ReachesRet (mirTree body s) tr o) (n : Nat)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    ∃ m', Interp.steps n mInit = .ok m' := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start_D hfragD hf hstart hns
  by_cases hn : n ≤ initLen body
  · exact steps_ok_mono hn hm0
  · obtain ⟨n', rfl⟩ : ∃ n', n = initLen body + n' := ⟨n - initLen body, by omega⟩
    obtain ⟨_, m', _, hsteps, _, _⟩ :=
      mirNoUB_diverges_steps_ok_D hfragD hf ctx s m0 hrel0 hsafe hdiv n'
    exact ⟨m', by rw [steps_add, hm0, ok_bind, hsteps]⟩

/-- **Coupled diverging UB-free execution from `f.start` (`StateRelD`).** -/
theorem mirNoUB_diverges_rel_from_start_D {body : CapturedMir} {f : Gen.Function}
    (hfragD : inFragmentD body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : StartRel body f ctx s mInit) (hsafe : MirNoUBTree (mirTree body s))
    (hdiv : ∀ tr o, ¬ ReachesRet (mirTree body s) tr o) (n : Nat)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    ∃ s' m' tr, Interp.steps (initLen body + n) mInit = .ok m' ∧ StateRelD body f ctx s' m' ∧
      Reaches (mirTree body s) tr (mirTree body s') := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start_D hfragD hf hstart hns
  obtain ⟨s', m', tr, hsteps, hrel', hr⟩ :=
    mirNoUB_diverges_steps_ok_D hfragD hf ctx s m0 hrel0 hsafe hdiv n
  exact ⟨s', m', tr, by rw [steps_add, hm0, ok_bind, hsteps], hrel', hr⟩

/-- **Call-tree UB (`inFragmentD`).** -/
theorem mirCall_ub_D {body : CapturedMir} {f : Gen.Function} (hfrag : inFragmentD body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (hctx : CtxOk body ctx)
    (args : List Value) (hargs : argsOk body args = true) (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals body.layouts)
    {tr : List (Event MirEffect)} {u : ITree MirEffect MirOutcome}
    (hreach : Reaches (mirCallTree body args) tr u) (hfault : FaultNow u) :
    ∃ (n : Nat) (msg : String), Interp.steps n mInit = .error (.ub msg) :=
  run_ub_from_start_D hfrag hf ctx (initMachineState body args) mInit
    (initMachineState_startRel_D hfrag ctx hctx args hargs mInit hthreads hactive hallocs)
    hreach hfault (initMachineState_nonScalar_D hfrag args hargs)

/-- **Localized single-body call-tree UB (`inFragmentD`).** -/
theorem mirCall_ub_rel_D {body : CapturedMir} {f : Gen.Function} (hfrag : inFragmentD body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (hctx : CtxOk body ctx)
    (args : List Value) (hargs : argsOk body args = true) (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals body.layouts)
    {tr : List (Event MirEffect)} {u : ITree MirEffect MirOutcome}
    (hreach : Reaches (mirCallTree body args) tr u) (hfault : FaultNow u) :
    ∃ (n : Nat) (sLast : MachineState) (mLast : Mach) (msg : String),
      Interp.steps n mInit = .ok mLast ∧ StateRelD body f ctx sLast mLast ∧
      Interp.step mLast = .error (.ub msg) ∧ Interp.steps (n + 1) mInit = .error (.ub msg) ∧
      (∀ k ≤ n, ∀ mk, Interp.steps k mInit = .ok mk →
        ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mk) :=
  run_ub_rel_from_start_D hfrag hf ctx (initMachineState body args) mInit
    (initMachineState_startRel_D hfrag ctx hctx args hargs mInit hthreads hactive hallocs)
    hreach hfault (initMachineState_nonScalar_D hfrag args hargs)

/-- **Call-tree UB-freedom transfer (`inFragmentD`).** -/
theorem mirCall_noUB_D {body : CapturedMir} {f : Gen.Function} (hfrag : inFragmentD body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (hctx : CtxOk body ctx)
    (args : List Value) (hargs : argsOk body args = true) (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals body.layouts)
    (hsafe : MirNoUBTree (mirCallTree body args))
    {n : Nat} {e : Stop} (herr : Interp.steps n mInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirCallTree body args) tr (.normal (v, mem)) :=
  mirNoUB_safe_from_start_D hfrag hf ctx (initMachineState body args) mInit
    (initMachineState_startRel_D hfrag ctx hctx args hargs mInit hthreads hactive hallocs)
    hsafe herr (initMachineState_nonScalar_D hfrag args hargs)

/-- **Call-tree converse error soundness (`inFragmentD`).** -/
theorem mirCall_steps_error_D {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragmentD body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (hctx : CtxOk body ctx) (args : List Value) (hargs : argsOk body args = true)
    (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals body.layouts)
    {n : Nat} {e : Stop} (herr : Interp.steps n mInit = .error e) :
    (∃ msg, e = .ub msg ∧ ∃ tr u, Reaches (mirCallTree body args) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirCallTree body args) tr (.normal (v, mem))) :=
  steps_error_from_start_D hfrag hf ctx n (initMachineState body args) mInit e
    (initMachineState_startRel_D hfrag ctx hctx args hargs mInit hthreads hactive hallocs)
    herr (initMachineState_nonScalar_D hfrag args hargs)

/-- **Call-tree total `(initLen body + n)`-step outcome trichotomy (`inFragmentD`).** -/
theorem mirCall_outcome_D {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragmentD body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (hctx : CtxOk body ctx) (args : List Value) (hargs : argsOk body args = true)
    (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals body.layouts)
    (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen body + n) mInit = .ok m' ∧ StateRelD body f ctx s' m' ∧
      Reaches (mirCallTree body args) tr (mirTree body s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen body + n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirCallTree body args) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen body + n) mInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree body args) tr u ∧ FaultNow u) :=
  steps_outcome_from_start_D hfrag hf ctx n (initMachineState body args) mInit
    (initMachineState_startRel_D hfrag ctx hctx args hargs mInit hthreads hactive hallocs)
    (initMachineState_nonScalar_D hfrag args hargs)

/-- **Call-tree forward progress (`inFragmentD`).** -/
theorem mirCall_progress_D {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragmentD body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (hctx : CtxOk body ctx) (args : List Value) (hargs : argsOk body args = true)
    (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals body.layouts)
    (hsafe : MirNoUBTree (mirCallTree body args)) (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen body + n) mInit = .ok m' ∧ StateRelD body f ctx s' m' ∧
      Reaches (mirCallTree body args) tr (mirTree body s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen body + n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirCallTree body args) tr (.normal (v, mem))) :=
  mirNoUB_progress_from_start_D hfrag hf ctx (initMachineState body args) mInit
    (initMachineState_startRel_D hfrag ctx hctx args hargs mInit hthreads hactive hallocs)
    hsafe n (initMachineState_nonScalar_D hfrag args hargs)

/-- **Call-tree diverging UB-free execution (`inFragmentD`).** -/
theorem mirCall_diverges_steps_ok_D {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragmentD body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (hctx : CtxOk body ctx) (args : List Value) (hargs : argsOk body args = true)
    (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals body.layouts)
    (hsafe : MirNoUBTree (mirCallTree body args))
    (hdiv : ∀ tr o, ¬ ReachesRet (mirCallTree body args) tr o) (n : Nat) :
    ∃ m', Interp.steps n mInit = .ok m' :=
  mirNoUB_diverges_from_start_D hfrag hf ctx (initMachineState body args) mInit
    (initMachineState_startRel_D hfrag ctx hctx args hargs mInit hthreads hactive hallocs)
    hsafe hdiv n (initMachineState_nonScalar_D hfrag args hargs)

/-- **Call-tree coupled diverging UB-free execution (`inFragmentD`).** -/
theorem mirCall_diverges_rel_D {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragmentD body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (hctx : CtxOk body ctx) (args : List Value) (hargs : argsOk body args = true)
    (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals body.layouts)
    (hsafe : MirNoUBTree (mirCallTree body args))
    (hdiv : ∀ tr o, ¬ ReachesRet (mirCallTree body args) tr o) (n : Nat) :
    ∃ s' m' tr, Interp.steps (initLen body + n) mInit = .ok m' ∧ StateRelD body f ctx s' m' ∧
      Reaches (mirCallTree body args) tr (mirTree body s') :=
  mirNoUB_diverges_rel_from_start_D hfrag hf ctx (initMachineState body args) mInit
    (initMachineState_startRel_D hfrag ctx hctx args hargs mInit hthreads hactive hallocs)
    hsafe hdiv n (initMachineState_nonScalar_D hfrag args hargs)

end MiniRustSpec.Correspondence
