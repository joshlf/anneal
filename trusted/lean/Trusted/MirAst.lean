-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Trusted.Refinement

/-!
# Trusted MIR Abstract Syntax Tree (`Trusted/MirAst.lean`)

This module defines the minimal owned representation of `rustc`'s
`MirPhase::Runtime(RuntimePhase::PostCleanup)` Mid-level Intermediate
Representation (MIR) required for the `#109` end-to-end verification slice and
atomic weak-memory loads (`#99`, `#101`, `#109`).

Every declaration in this file that models a `rustc` MIR construct or Rust
type/value concept cites its normative source at the repository's pinned
revisions (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` and
`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b`).

This module belongs to `trusted/lean/` and contains only data definitions
(zero theorems).
-/

namespace Trusted

/-- Index of a MIR local variable or temporary (`_0`, `_1`, ...).

    Corresponds to `rustc_middle::mir::Local` indexing into `Body::local_decls`,
    where local `0` (`_0`) is the return place, `1 ..= arg_count` (`_1`, ...)
    are caller-initialized function arguments, and higher indices are
    user-declared variables and temporaries:

    > "The first local is the return value pointer, followed by `arg_count`
    > locals for the function arguments, followed by any user-declared
    > variables and temporaries."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L235-L240 -/
@[candidate mir_ast]
structure LocalId where
  index : Nat

/-- Index of a basic block (`bb0`, `bb1`, ...) within a MIR body.

    Corresponds to `rustc_middle::mir::BasicBlock` indexing into
    `Body::basic_blocks`:

    > "A list of basic blocks. References to basic block use a newtyped index
    > type [`BasicBlock`] that indexes into this vector."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L207-L209 -/
@[candidate mir_ast]
structure BlockId where
  index : Nat

/-- Atomic memory ordering for atomic load operations.

    Corresponds to `core::sync::atomic::Ordering` variants valid on atomic
    loads (`Ordering::Relaxed` and `Ordering::Acquire`):

    > "Memory orderings specify the way atomic operations synchronize memory.
    > In its weakest [`Ordering::Relaxed`], only the memory directly touched by
    > the operation is synchronized."
    >
    > "No ordering constraints, only atomic operations. Corresponds to
    > [`memory_order_relaxed`] in C++20."
    >
    > "When coupled with a load, if the loaded value was written by a store
    > operation with [`Release`] (or stronger) ordering, then all subsequent
    > operations become ordered after that store."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L450-L503 -/
@[candidate mir_ast]
inductive AtomicOrdering where
  | relaxed
  | acquire

/-- Minimal MIR type grammar (`usize`, `()`, `&Atomic<usize>`, and `Ordering`).

    - `MirTy.usize` models Rust's pointer-sized unsigned integer type `usize`:

      > "The `usize` type is an unsigned integer type with the same number of
      > bits as the platform's pointer type. It can represent every memory
      > address in the process."

    - `MirTy.refAtomicUsize` models a shared reference `&AtomicUsize`
      (`&core::sync::atomic::Atomic<usize>`) to an atomic `usize` object:

      > "The end result is *almost* equivalent to saying that creating a
      > *shared reference* to one of the Rust atomic types corresponds to
      > creating an `atomic_ref` in C++, with the `atomic_ref` being destroyed
      > when the lifetime of the shared reference ends."

    - `MirTy.atomicOrdering` models `core::sync::atomic::Ordering`.

    Sources:
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/types/numeric.md#L37-L38
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L36-L42
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L466-L527 -/
@[candidate mir_ast]
inductive MirTy where
  | usize
  | unit
  | refAtomicUsize
  | atomicOrdering

/-- Initialized runtime scalar value (`usize`, `()`, `&AtomicUsize` location,
    or `Ordering`).

    In Rust, scalar values and references must be initialized and valid when
    produced; uninitialized locals are represented in `MirState` by
    `Option.none` rather than a `MirVal` constructor:

    > "The Rust compiler assumes that all values produced during program
    > execution are "valid", and producing an invalid value is hence immediate
    > UB."
    >
    > "* An integer (`i*`/`u*`), floating point value (`f*`), or raw pointer
    > must be initialized, i.e., must not be obtained from uninitialized
    > memory."
    >
    > "* A reference or [`Box<T>`] must be aligned and non-null, it cannot be
    > [dangling], and it must point to a valid value"

    Sources:
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L114-L147
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L466-L527 -/
@[candidate mir_ast]
inductive MirVal where
  | usize (bits : Nat)
  | unit
  | atomicLoc (loc : Nat)
  | ordering (ord : AtomicOrdering)

/-- MIR operand evaluated to produce a value in an `Rvalue` or terminator.

    Corresponds to `rustc_middle::mir::Operand` (`Copy`, `Move`, `Constant`)
    specialized to unprojected local places (`Place { local, projection: [] }`):

    > "Creates a value by loading the given place.
    >
    > Before drop elaboration, the type of the place must be `Copy`. After drop
    > elaboration there is no such requirement."
    >
    > "Creates a value by performing loading the place, just like the `Copy`
    > operand.
    >
    > This *may* additionally overwrite the place with `uninit` bytes,
    > depending on how we decide in [UCG#188]. You should not emit MIR that may
    > attempt a subsequent second load of this place without first
    > re-initializing it."
    >
    > "Constants are already semantically values, and remain unchanged."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L1282-L1310 -/
@[candidate mir_ast]
inductive Operand where
  | copy (src : LocalId)
  | move (src : LocalId)
  | constVal (val : MirVal)

/-- Right-hand side value computation of a MIR assignment statement.

    Corresponds to `rustc_middle::mir::Rvalue::Use`:

    > "Yields the operand unchanged, except for a potential retag."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L1342-L1345 -/
@[candidate mir_ast]
inductive Rvalue where
  | use (op : Operand)

/-- Sequential statement inside a MIR basic block.

    Corresponds to `rustc_middle::mir::StatementKind` (`Assign`, `StorageLive`,
    `StorageDead`, and no-op statements):

    > "Assign statements roughly correspond to an assignment in Rust proper
    > (`x = ...`) except without the possibility of dropping the previous value
    > (that must be done separately, if at all). The *exact* way this works is
    > undecided. It probably does something like evaluating the LHS to a place,
    > then the RHS to a value, and then storing the value to the place."
    >
    > "`StorageLive` and `StorageDead` statements mark the live range of a
    > local."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L305-L385 -/
@[candidate mir_ast]
inductive Stmt where
  | assign (dst : LocalId) (rv : Rvalue)
  | storageLive (loc : LocalId)
  | storageDead (loc : LocalId)
  | nop

/-- Control-flow transfer at the end of a MIR basic block.

    Corresponds to `rustc_middle::mir::TerminatorKind` (`Return`, `Goto`,
    `Unreachable`, and `Call` specialized to `Atomic::<usize>::load`):

    > "Block has one successor; we continue execution there."
    >
    > "Returns from the function.
    >
    > Like function calls, the exact semantics of returns in Rust are unclear.
    > Returning very likely at least assigns the value currently in the return
    > place (`_0`) to the place specified in the associated `Call` terminator
    > in the calling function, as if assigned via `dest = move _0`."
    >
    > "Indicates a terminator that can never be reached.
    >
    > Executing this terminator is UB."
    >
    > "Roughly speaking, evaluates the `func` operand and the arguments, and
    > starts execution of the referred to function. The operand types must
    > match the argument types of the function. The return place type must
    > match the return type."
    >
    > "Loads a value from the atomic integer. `load` takes an [`Ordering`]
    > argument which describes the memory ordering of this operation. Possible
    > values are [`SeqCst`], [`Acquire`] and [`Relaxed`]."

    Sources:
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L683-L808
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L2891-L2917 -/
@[candidate mir_ast]
inductive Terminator where
  | return_
  | goto (target : BlockId)
  | unreachable
  | callAtomicLoad (dst : LocalId) (ptr : Operand) (ord : Operand) (target : BlockId)

/-- Basic block consisting of sequential statements and a single terminator.

    Corresponds to `rustc_middle::mir::BasicBlockData` in `Body::basic_blocks`.

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L207-L209 -/
@[candidate mir_ast]
structure BasicBlock where
  stmts : List Stmt
  terminator : Terminator

/-- Lowered `Runtime(PostCleanup)` MIR body of a single function.

    Corresponds to `rustc_middle::mir::Body`, recording the parameter types
    (`arg_count` arguments starting at local `1`), the return type (`_0`), the
    total number of locals, and the control-flow graph of basic blocks:

    > "The lowered representation of a single function."
    >
    > "Starting at local 1, `arg_count` locals will be provided by the caller
    > and can be assumed to be initialized."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L204-L251 -/
@[candidate mir_ast]
structure MirBody where
  argTys : List MirTy
  retTy : MirTy
  localCount : Nat
  blocks : List BasicBlock

end Trusted
