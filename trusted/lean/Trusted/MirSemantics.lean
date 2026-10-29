prelude
import Init.NotationExtra
import Trusted.Refinement
import Trusted.StepResult
import Trusted.MirAst
import Trusted.Memory

/-!
# Trusted MIR Operational Semantics and Crate Theorem (`Trusted/MirSemantics.lean`)

This module defines the small-step operational semantics `MirSem` for the
minimal MIR fragment (`Trusted/MirAst.lean`) coupled with the weak-memory state
(`Trusted/Memory.lean`) and the top-level crate verification obligation
`Trusted.CrateTheorem` (`#100` §4, `#103` §4, `#109`).

Every declaration in this file that models a Rust execution rule cites the
normative Rust Reference or `rustc` documentation at the repository's pinned
revisions (`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b` and
`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`).

This module belongs to `trusted/lean/` and contains only definitions, structures,
inductives, and opaque interfaces (zero theorems). All proofs (`TotalStep`,
`InhabitedDemonic`, view partial-order lemmas, single-threaded/lock ownership
helpers, adequacy canaries, and `id` / `load_relaxed` verification lemmas) live
in `theory/Anneal/MirLemmas.lean`.
-/

namespace Trusted

/-- Instantaneous execution state of a `MirBody`, recording the contents of
    each local slot (`none` when uninitialized or deallocated, `some v` when
    holding an initialized `MirVal`), the operational memory state `mem`
    (`Trusted/Memory.lean`), the active basic block index, and the statement
    index within that basic block. -/
structure MirState where
  locals : Nat → Option MirVal
  mem : MemState
  block : Nat
  stmtIdx : Nat

/-- Update local slot `target` in a local store `locals`. -/
def updateLocal (locals : Nat → Option MirVal) (target : Nat)
    (val : Option MirVal) : Nat → Option MirVal :=
  fun i => if i == target then val else locals i

/-- Dynamic type-validity relation matching an initialized `MirVal` against a
    `MirTy` in memory state `m`.

    Corresponds to Rust's value validity requirement that every produced scalar
    value or reference be initialized, non-dangling, and match its static type
    (`r[undefined.invalid]`, `r[undefined.validity.reference-box]`):

    > "The Rust compiler assumes that all values produced during program
    > execution are "valid", and producing an invalid value is hence immediate
    > UB."
    >
    > "* A reference or [`Box<T>`] must be aligned and non-null, it cannot be
    > [dangling], and it must point to a valid value"

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L114-L147 -/
def MirVal.hasTy (m : MemState) (v : MirVal) (ty : MirTy) : Prop :=
  match v, ty with
  | .usize _, .usize => True
  | .bool _, .bool => True
  | .unit, .unit => True
  | .atomicLoc loc, .refAtomicUsize => m.visibleAtomicMsgs loc ≠ []
  | .refSharedLoc loc, .refSharedUsize =>
    ∃ n, m.naVal loc = some (.usize n) ∧
      m.naWriteTs loc ≤ m.curView loc
  | .refMutLoc loc, .refMutUsize =>
    ∃ n, m.naVal loc = some (.usize n) ∧
      m.naWriteTs loc ≤ m.curView loc ∧
      m.naReadTs loc ≤ m.curView loc
  | .ordering _, .atomicOrdering => True
  | _, _ => False

/-- Parameter validity at argument index `k` (`1 ..= argTys.length`), combining
    value validity (`MirVal.hasTy`) with Rust's reference aliasing rules
    (`r[undefined.alias]`: a `&mut usize` parameter cannot alias any preceding
    `&mut usize` or `&usize` parameter, and a `&usize` parameter cannot alias
    any preceding `&mut usize` parameter, while `&usize` parameters may alias
    each other):

    > "* Breaking the [pointer aliasing rules]. `Box<T>`, `&mut T`, and `&T`
    > follow LLVM's scoped `noalias` model, except if the `&T` contains an
    > [`UnsafeCell<U>`]. This means references and boxes cannot be dangling
    > while they are live, and mutable references and boxes cannot be aliased"

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L48-L52 -/
def argValidAt (m : MemState) (locals : Nat → Option MirVal) (k : Nat)
    (v : MirVal) (ty : MirTy) : Prop :=
  match ty with
  | .refMutUsize =>
    v.hasTy m .refMutUsize ∧
      ∀ loc i, v = .refMutLoc loc → 1 ≤ i → i < k →
        locals i ≠ some (.refMutLoc loc) ∧ locals i ≠ some (.refSharedLoc loc)
  | .refSharedUsize =>
    v.hasTy m .refSharedUsize ∧
      ∀ loc i, v = .refSharedLoc loc → 1 ≤ i → i < k →
        locals i ≠ some (.refMutLoc loc)
  | _ => v.hasTy m ty

/-- Entry initialization condition for function arguments and non-argument
    locals.

    Starting at local `1` at function entry, each parameter type in `argTys`
    holds an initialized `MirVal` matching its `MirTy` in `m`, while remaining
    locals start uninitialized (`none`):

    > "Starting at local 1, `arg_count` locals will be provided by the caller
    > and can be assumed to be initialized."
    >
    > "At any point during the execution of a function, each local is either
    > allocated or unallocated. Except as noted below, all locals except
    > function parameters are initially unallocated."

    Sources:
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L245-L249
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L366-L368 -/
def argsMatchLocals (m : MemState) (argTys : List MirTy)
    (locals : Nat → Option MirVal) : Prop :=
  argTys.foldr
    (fun ty rest k => (∃ v, locals k = some v ∧ argValidAt m locals k v ty) ∧ rest (k + 1))
    (fun k => ∀ j, k ≤ j → locals j = none)
    1

/-- Entry state predicate for a `MirBody`: execution starts at basic block `0`,
    statement `0`, with the return place `_0` uninitialized and argument locals
    `1 ..= argTys.length` initialized to type-valid values in `s.mem`.

    Corresponds to function body entry in the Rust Reference and `rustc` MIR:

    > "The body block of a function is conceptually wrapped in another block
    > that first binds the argument patterns and then `return`s the value of
    > the function's body."

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/items/functions.md#L114-L116 -/
def initMirState (body : MirBody) (s : MirState) : Prop :=
  s.block = 0 ∧
  s.stmtIdx = 0 ∧
  s.locals 0 = none ∧
  argsMatchLocals s.mem body.argTys s.locals

/-- Evaluate a MIR `Operand` against a local store `locals`, returning the
    produced `MirVal` and the updated local store (`Operand.copy` preserves the
    source local; `Operand.move` deinitializes it; reading an uninitialized
    local returns `none` for immediate UB):

    > "* Producing an [invalid value][invalid-values]. "Producing" a value
    > happens any time a value is assigned to or read from a place, passed to a
    > function/primitive operation or returned from a function/primitive
    > operation."
    >
    > "If the type of that value implements [`Copy`], then the value will be
    > copied."
    >
    > "After moving out of a place expression that evaluates to a local
    > variable, the location is deinitialized and cannot be read from again
    > until it is reinitialized."

    Sources:
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L54-L55
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/expressions.md#L199-L215 -/
def evalOperand (locals : Nat → Option MirVal) (op : Operand) :
    Option (MirVal × (Nat → Option MirVal)) :=
  match op with
  | .copy src =>
    match locals src.index with
    | some v => some (v, locals)
    | none => none
  | .move src =>
    match locals src.index with
    | some v => some (v, updateLocal locals src.index none)
    | none => none
  | .constVal v =>
    some (v, locals)

/-- Evaluate a binary comparison or bitwise operator on two `MirVal.usize`
    values, returning `some (.bool b)` for comparisons or `some (.usize n)` for
    bitwise operations on `.usize` inputs, and `none` on type mismatch
    (`r[undefined.invalid]`).

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L1409-L1443 -/
def evalBinOp (op : BinOp) (v1 v2 : MirVal) : Option MirVal :=
  match v1, v2 with
  | .usize n1, .usize n2 =>
    match op with
    | .lt => some (.bool (decide (n1 < n2)))
    | .le => some (.bool (decide (n1 ≤ n2)))
    | .eq => some (.bool (decide (n1 = n2)))
    | .ne => some (.bool (decide (n1 ≠ n2)))
    | .gt => some (.bool (decide (n2 < n1)))
    | .ge => some (.bool (decide (n2 ≤ n1)))
    | .bitAnd => some (.usize (Nat.land n1 n2))
    | .bitOr => some (.usize (Nat.lor n1 n2))
    | .bitXor => some (.usize (Nat.xor n1 n2))
  | _, _ => none

/-- Single-step operational evaluation of a MIR statement.

    Models `Operand::Copy`, `Operand::Move`, `Rvalue::Use`, dereference reads
    `copy (*src)`, `Rvalue::BinaryOp`, `StatementKind::Assign` (to a local or
    dereferenced place `(*dst) = op`), `StatementKind::StorageLive`,
    `StatementKind::StorageDead`, and `StatementKind::Nop`.

    Sources:
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L305-L385
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L975-L1005 -/
def evalMirStmt (s : MirState) (stmt : Stmt) : StepResult MirState Unit MirVal :=
  match stmt with
  | .assign dst (.use op) =>
    match evalOperand s.locals op with
    | some (v, locals') =>
      .step () { s with
        locals := updateLocal locals' dst.index (some v)
        stmtIdx := s.stmtIdx + 1
      }
    | none => .failed .ub
  | .assign dst (.deref src) =>
    match s.locals src.index with
    | some (.refMutLoc loc) | some (.refSharedLoc loc) =>
      match s.mem.readNA loc with
      | some (v, mem') =>
        .step () { s with
          locals := updateLocal s.locals dst.index (some v)
          mem := mem'
          stmtIdx := s.stmtIdx + 1
        }
      | none => .failed .ub
    | _ => .failed .ub
  | .assign dst (.binaryOp op lhs rhs) =>
    match evalOperand s.locals lhs with
    | none => .failed .ub
    | some (v1, locals1) =>
      match evalOperand locals1 rhs with
      | none => .failed .ub
      | some (v2, locals2) =>
        match evalBinOp op v1 v2 with
        | some res =>
          .step () { s with
            locals := updateLocal locals2 dst.index (some res)
            stmtIdx := s.stmtIdx + 1
          }
        | none => .failed .ub
  | .assignDeref dst op =>
    match evalOperand s.locals op with
    | none => .failed .ub
    | some (v, locals1) =>
      match locals1 dst.index with
      | some (.refMutLoc loc) =>
        match s.mem.writeNA loc v with
        | some mem' =>
          .step () { s with
            locals := locals1
            mem := mem'
            stmtIdx := s.stmtIdx + 1
          }
        | none => .failed .ub
      | _ => .failed .ub
  | .storageLive loc =>
    .step () { s with
      locals := updateLocal s.locals loc.index none
      stmtIdx := s.stmtIdx + 1
    }
  | .storageDead loc =>
    .step () { s with
      locals := updateLocal s.locals loc.index none
      stmtIdx := s.stmtIdx + 1
    }
  | .nop =>
    .step () { s with stmtIdx := s.stmtIdx + 1 }

/-- Single-step operational evaluation of a MIR basic-block terminator.

    Models `TerminatorKind::Return`, `TerminatorKind::Goto`,
    `TerminatorKind::Unreachable`, `TerminatorKind::Call` specialized to
    `Atomic::<usize>::load`, and `TerminatorKind::SwitchInt` on boolean
    discriminants:
    - `Terminator.return_` reads the return place `_0` (`s.locals 0`) and
      completes with `.terminated (.normal retVal)` if initialized, or triggers
      `.failed .ub` if `_0` is uninitialized (`r[undefined.invalid]`).
    - `Terminator.goto target` transfers control to statement `0` of
      `target.index`.
    - `Terminator.unreachable` triggers immediate `.failed .ub`.
    - `Terminator.callAtomicLoad dst ptrOp ordOp target` evaluates `ptrOp` and
      `ordOp` left-to-right (`syntax.rs#L783-L784`) and performs an atomic load
      on `s.mem` (`atomic.rs#L2891-L2917`, `#L3990-L4001`): if `loc` has
      visible modification-order messages `head :: tail` (`s.mem.curView loc ≤ msg.ts`),
      it emits a demonic choice (`.choice .demonic`) over every visible message
      `msg ∈ head :: tail`, storing `MirVal.usize msg.bits` into `dst` and
      advancing `s.mem` via `s.mem.applyAtomicLoad ord msg`.
    - `Terminator.switchInt discr falseTarget trueTarget` evaluates `discr` to a
      `MirVal.bool b` and jumps to `falseTarget` when `b = false` (`0`) or
      `trueTarget` when `b = true` (`otherwise`).

    > "Block has one successor; we continue execution there."
    >
    > "Returning very likely at least assigns the value currently in the return
    > place (`_0`) to the place specified in the associated `Call` terminator
    > in the calling function, as if assigned via `dest = move _0`."
    >
    > "Indicates a terminator that can never be reached.
    >
    > Executing this terminator is UB."
    >
    > "The evaluation order is currently "first compute destination place, then
    > `func` operand, then the arguments in left-to-right order"."

    Sources:
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L684-L808
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L2891-L2917
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L3990-L4001 -/
def evalMirTerminator (s : MirState) (term : Terminator) :
    StepResult MirState Unit MirVal :=
  match term with
  | .return_ =>
    match s.locals 0 with
    | some retVal => .terminated (.normal retVal)
    | none => .failed .ub
  | .goto target =>
    .step () { s with block := target.index, stmtIdx := 0 }
  | .unreachable =>
    .failed .ub
  | .callAtomicLoad dst ptrOp ordOp target =>
    match evalOperand s.locals ptrOp with
    | none => .failed .ub
    | some (ptrVal, locals1) =>
      match evalOperand locals1 ordOp with
      | none => .failed .ub
      | some (ordVal, locals2) =>
        match ptrVal, ordVal with
        | .atomicLoc loc, .ordering ord =>
          match s.mem.visibleAtomicMsgs loc with
          | [] => .failed .ub
          | head :: tail =>
            .choice .demonic (fun s' =>
              ∃ msg, msg ∈ (head :: tail) ∧
                s' = {
                  locals := updateLocal locals2 dst.index (some (.usize msg.bits))
                  mem := s.mem.applyAtomicLoad ord msg
                  block := target.index
                  stmtIdx := 0
                })
        | _, _ => .failed .ub
  | .switchInt discr falseTarget trueTarget =>
    match evalOperand s.locals discr with
    | some (.bool false, locals') =>
      .step () { s with
        locals := locals'
        block := falseTarget.index
        stmtIdx := 0
      }
    | some (.bool true, locals') =>
      .step () { s with
        locals := locals'
        block := trueTarget.index
        stmtIdx := 0
      }
    | _ => .failed .ub

/-- Single-step transition function of a `MirBody`: executes the statement at
    `s.stmtIdx` in block `s.block`, or the block's terminator once all
    statements in `s.block` have completed. Jumping to an out-of-bounds basic
    block index triggers `.failed .ub`. -/
def evalMirStep (body : MirBody) (s : MirState) :
    StepResult MirState Unit MirVal :=
  match body.blocks[s.block]? with
  | none => .failed .ub
  | some bb =>
    match bb.stmts[s.stmtIdx]? with
    | some stmt => evalMirStmt s stmt
    | none => evalMirTerminator s bb.terminator

/-- Small-step operational machine for `MirBody`. -/
def MirMachine : SmallStepMachine MirBody MirState Unit MirVal where
  initState := initMirState
  step body s r := r = evalMirStep body s

/-- Operational language of Rust MIR (`MirMachine.toLanguage`). -/
def MirLang : Language :=
  MirMachine.toLanguage

/-- Operational behavior of a `MirBody`: the query-indexed partial behavior
    (`ExecQuery MirState → Partial (ExecOut Unit MirVal → Prop)`) induced by
    `MirMachine`. -/
abbrev MirSem (body : MirBody) : MirLang.Behavior :=
  MirLang.sem body

/-- Postcondition specification for a safe function asserting that:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), and
    - `val`: any normal return value equals the initial value of argument local
      `argLocal` (`1` for the first parameter `_1`). -/
def EnsuresEqArg (argLocal : Nat) : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      q.init.locals argLocal = some ret)

/-- Postcondition specification for a safe atomic load from `&AtomicUsize`
    argument `argLocal` (`1` for the first parameter `_1`):
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), and
    - `val`: any normal return value `ret` equals `MirVal.usize msg.bits` for
      some modification-order message `msg` at `argLocal`'s atomic location that
      was visible in `q.init.mem`. -/
def EnsuresAtomicLoad (argLocal : Nat) : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      ∃ loc msg,
        q.init.locals argLocal = some (.atomicLoc loc) ∧
        msg ∈ q.init.mem.visibleAtomicMsgs loc ∧
        ret = .usize msg.bits)

/-- Postcondition specification for `pub fn max_assign(x: &mut usize, y: usize) -> usize`:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), and
    - `val`: for any initial state where `_1` points to non-atomic location
      `loc` holding `.usize x0` and `_2` holds `.usize y0`, any normal return
      value `ret` equals `.usize (if decide (x0 < y0) then y0 else x0)`. -/
def EnsuresMaxAssign : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret loc x0 y0,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.refMutLoc loc) →
      q.init.mem.naVal loc = some (.usize x0) →
      q.init.locals 2 = some (.usize y0) →
      ret = .usize (if decide (x0 < y0) then y0 else x0))

/-- Postcondition specification for
    `pub fn update_min(x: &mut usize, y: &mut usize, v: usize) -> usize`:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), and
    - `val`: for any initial state where `_1` points to non-atomic location
      `locX` holding `.usize x0`, `_2` points to non-atomic location `locY`
      holding `.usize y0`, and `_3` holds `.usize v0`, any normal return value
      `ret` (which reads `*x` after mutating the conditionally borrowed minimum
      reference `r = if *x <= *y { &mut *x } else { &mut *y }` to `v`) equals
      `.usize (if decide (x0 ≤ y0) then v0 else x0)`. -/
def EnsuresUpdateMin : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret locX locY x0 y0 v0,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.refMutLoc locX) →
      q.init.mem.naVal locX = some (.usize x0) →
      q.init.locals 2 = some (.refMutLoc locY) →
      q.init.mem.naVal locY = some (.usize y0) →
      q.init.locals 3 = some (.usize v0) →
      ret = .usize (if decide (x0 ≤ y0) then v0 else x0))

/-- Postcondition specification for
    `pub fn clamp_assign(x: &mut usize, lo: usize, hi: usize) -> usize`:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), and
    - `val`: for any initial state where `_1` points to non-atomic location
      `loc` holding `.usize x0`, `_2` holds `.usize lo`, and `_3` holds
      `.usize hi`, any normal return value `ret` equals
      `.usize (if decide (x0 < lo) then lo else if decide (hi < x0) then hi else x0)`. -/
def EnsuresClampAssign : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret loc x0 lo hi,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.refMutLoc loc) →
      q.init.mem.naVal loc = some (.usize x0) →
      q.init.locals 2 = some (.usize lo) →
      q.init.locals 3 = some (.usize hi) →
      ret = .usize (if decide (x0 < lo) then lo else if decide (hi < x0) then hi else x0))

/-- Postcondition specification for
    `pub fn is_aligned_mask(addr: usize, mask: usize) -> bool`:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), and
    - `val`: for any initial state where `_1` holds `.usize addr` and `_2`
      holds `.usize mask`, any normal return value `ret` equals
      `.bool (decide (Nat.land addr mask = 0))`. -/
def EnsuresIsAlignedMask : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret addr mask,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.usize addr) →
      q.init.locals 2 = some (.usize mask) →
      ret = .bool (decide (Nat.land addr mask = 0)))

/-- Postcondition specification for
    `pub fn shared_max(x: &usize, y: &usize) -> usize`:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), including when `x` and `y` alias the same
      memory location (`locX = locY`), and
    - `val`: for any initial state where `_1` points to shared location `locX`
      holding `.usize x0` and `_2` points to shared location `locY` holding
      `.usize y0`, any normal return value `ret` equals
      `.usize (if decide (x0 < y0) then y0 else x0)`. -/
def EnsuresSharedMax : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret locX locY x0 y0,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.refSharedLoc locX) →
      q.init.mem.naVal locX = some (.usize x0) →
      q.init.locals 2 = some (.refSharedLoc locY) →
      q.init.mem.naVal locY = some (.usize y0) →
      ret = .usize (if decide (x0 < y0) then y0 else x0))

/-- Postcondition specification for
    `pub fn max_assign_shared(dst: &mut usize, src: &usize) -> usize`:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), and
    - `val`: for any initial state where `_1` points to mutable location `locDst`
      holding `.usize d0` and `_2` points to shared location `locSrc` holding
      `.usize s0`, any normal return value `ret` equals
      `.usize (if decide (d0 < s0) then s0 else d0)`. -/
def EnsuresMaxAssignShared : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret locDst locSrc d0 s0,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.refMutLoc locDst) →
      q.init.mem.naVal locDst = some (.usize d0) →
      q.init.locals 2 = some (.refSharedLoc locSrc) →
      q.init.mem.naVal locSrc = some (.usize s0) →
      ret = .usize (if decide (d0 < s0) then s0 else d0))

/-- Postcondition specification for
    `pub fn sort_pair(x: &mut usize, y: &mut usize) -> usize`:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), and
    - `val`: for any initial state where `_1` points to `locX` holding
      `.usize x0` and `_2` points to `locY` holding `.usize y0`, any normal
      return value `ret` equals `.usize (if decide (y0 < x0) then y0 else x0)`. -/
def EnsuresSortPair : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret locX locY x0 y0,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.refMutLoc locX) →
      q.init.mem.naVal locX = some (.usize x0) →
      q.init.locals 2 = some (.refMutLoc locY) →
      q.init.mem.naVal locY = some (.usize y0) →
      ret = .usize (if decide (y0 < x0) then y0 else x0))

/-- Postcondition specification for
    `pub fn two_phase_reborrow(x: &mut usize, y: &mut usize, a: usize, b: usize) -> usize`:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), and
    - `val`: for any initial state where `_1` points to `locX` holding
      `.usize x0`, `_2` points to `locY` holding `.usize y0`, `_3 = some (.usize a)`,
      and `_4 = some (.usize b)`, any normal return value `ret` equals
      `.usize (if decide ((if decide (x0 ≤ y0) then a else x0) ≤ (if decide (x0 ≤ y0) then y0 else a)) then (if decide (x0 ≤ y0) then a else x0) else b)`. -/
def EnsuresTwoPhaseReborrow : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret locX locY x0 y0 a b,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.refMutLoc locX) →
      q.init.mem.naVal locX = some (.usize x0) →
      q.init.locals 2 = some (.refMutLoc locY) →
      q.init.mem.naVal locY = some (.usize y0) →
      q.init.locals 3 = some (.usize a) →
      q.init.locals 4 = some (.usize b) →
      ret = .usize
        (if decide ((if decide (x0 ≤ y0) then a else x0) ≤ (if decide (x0 ≤ y0) then y0 else a))
         then (if decide (x0 ≤ y0) then a else x0)
         else b))

/-- Abstract type of compiled target artifacts produced by `rustc`. -/
structure TargetArtifact where
  private mk ::
  unit : Unit

/-- Abstract `rustc` lowering from a `MirBody` to a `TargetArtifact`. Declared
    `opaque` so that proofs cannot unfold target compilation and must instead
    invoke the audited `TCBItem.rustcLowering` assumption. -/
opaque rustc : MirBody → TargetArtifact := fun _ => { unit := () }

/-- Abstract operational behavior of a compiled `TargetArtifact`. -/
opaque TargetSem :
    TargetArtifact → ExecQuery MirState → Partial (ExecOut Unit MirVal → Prop) :=
  fun _ _ => Partial.ub

/-- Target language of compiled `TargetArtifact`s. -/
def TargetLang : Language where
  Prog := TargetArtifact
  Query := ExecQuery MirState
  Out := ExecOut Unit MirVal
  sem := TargetSem

/-- Abstract compiler behavior mapping from MIR behaviors to target
    behaviors. -/
opaque π_c : MirLang.Behavior → TargetLang.Behavior :=
  fun b => b

/-- `rustc` compiler lowering from `MirLang` to `TargetLang` under `π_c`. -/
def RustcCompiler : Compiler MirLang TargetLang where
  compile := rustc
  π := π_c

/-- Audited assumption category in a crate's Trusted Computing Base. -/
inductive TCBItem where
  /-- Standard compiler lowering assumption for a function: `RustcCompiler` is
      sound on `body` (`RustcCompiler.SoundOn body`). -/
  | rustcLowering (fnName : String) (body : MirBody)
  /-- Explicit user-supplied axiom assumption (`#[anneal::axiom]`). -/
  | userAxiom (name : String) (prop : Prop)

/-- Semantic meaning of each Rust `TCBItem` as a `TrustedAssumption`. -/
instance instTrustedAssumptionTCBItem : TrustedAssumption TCBItem where
  meaning
    | .rustcLowering _ body => RustcCompiler.SoundOn body
    | .userAxiom _ prop => prop

/-- Default trust policy: standard `rustc` lowering assumptions are permitted;
    unapproved user axioms are rejected. -/
def defaultTrustPolicy : TrustPolicy TCBItem where
  isAllowed
    | .rustcLowering _ _ => True
    | .userAxiom _ _ => False

/-- Captured MIR function pairing its identifier (`name`), lowered `MirBody`
    (`prog`), caller safety precondition (`pre`, defaulting to `fun _ => True`
    for safe functions), and additional specifications (`specs`, defaulting to
    `[]`). -/
structure CapturedFn where
  name : String
  prog : MirBody
  pre : ExecQuery MirState → Prop := fun _ => True
  specs : List MirLang.Behavior := []

/-- Captured Rust crate bundling its functions and TCB audit log. -/
structure Crate where
  functions : List CapturedFn
  tcb : List TCBItem

/-- Top-level theorem required of every verified Rust crate:
    1. The crate contains at least one captured function (`c.functions ≠ []`).
    2. Every captured function `fn ∈ c.functions` satisfies
       `VerificationResultOn RustcCompiler defaultTrustPolicy c.tcb fn.prog fn.pre fn.specs`
       —proving that `c.tcb` complies with `defaultTrustPolicy` and, assuming
       the meaning of every item in `c.tcb`, proving
       `RustcCompiler.Verified fn.prog` on the non-empty specification list
       `MirLang.WellFormedOn fn.pre :: fn.specs`. -/
def CrateTheorem (c : Crate) : Prop :=
  c.functions ≠ [] ∧
  AllHold (c.functions.map (fun fn =>
    VerificationResultOn RustcCompiler defaultTrustPolicy c.tcb fn.prog fn.pre fn.specs))

end Trusted
