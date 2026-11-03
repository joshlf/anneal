/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.Arith

/-!
# State relation between Anneal MIR states and MiniRust machines

An Anneal `MachineState` executing a fragment body `body` corresponds to a
MiniRust `Machine<BasicMemory<x86_64>>` in which:

* there is exactly one thread, it is enabled and active, and its stack is
  `[caller, callee]`: the callee frame runs `translateFn body`, and the caller
  frame is an arbitrary frame that will receive the return value. A caller is
  necessary because MiniRust makes it UB for the bottom frame of the main
  thread to return ("the start function must not return",
  `spec/lang/step/terminators.md`), whereas Anneal's root body returns
  normally;
* the callee's program counter (`next_block`, `next_stmt`) equals Anneal's
  (`blockIdx`, `stmtIdx`);
* every MIR local `_i` is live in both models. In MiniRust it is a pointer to
  its own `Stack` allocation whose bytes are the representation-relation
  encoding of Anneal's slot: `Uninit` bytes for an uninitialized slot and the
  little-endian bytes of the bit pattern for an initialized scalar. The
  callee's allocations sit after an arbitrary prefix `base` of allocations,
  which contains the caller's return place;
* the Anneal state has no borrows, protectors, call stack, active callee, or
  caller-owned referents (the fragment cannot create any).

The relation deliberately says nothing about the rest of the MiniRust machine
(program, globals, function pointers, the access log, ...), which the fragment
neither reads nor writes.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp

/-- MiniRust integer type of a MIR local declaration (the default is never
used for fragment bodies, whose locals all have integer types). -/
def itOf (d : LocalDecl) : Gen.IntType := (intTypeOf d.ty).getD ⟨.Unsigned, ⟨1⟩⟩

/-- `Type::encode` of `Value::Int(int_from_bits(bits))` at `Type::Int(it)`:
little-endian bytes without provenance. -/
def scalarBytes (it : Gen.IntType) (bits : Nat) : List Byte :=
  (leBytes bits it.size.bytes).map (fun b => .Init b none)

/-- The contents of a freshly allocated MiniRust local: all `Uninit`. -/
def uninitBytes (it : Gen.IntType) : List Byte := List.replicate it.size.bytes .Uninit

/-- MiniRust bytes corresponding to an Anneal local slot (meaningful for
fragment slots, see `SlotOk`). -/
def slotData (it : Gen.IntType) : LocalSlot → List Byte
  | .init (.scalar sc) => scalarBytes it sc.bits
  | _ => uninitBytes it

/-- Fragment slots: live, and holding either nothing or a scalar of the
declared size whose bit pattern is in range. -/
def SlotOk (it : Gen.IntType) : LocalSlot → Prop
  | .uninit => True
  | .init (.scalar sc) => sc.sizeBytes = it.size.bytes ∧ sc.bits < 2 ^ (8 * it.size.bytes)
  | _ => False

/-- The parts of the MiniRust machine that the callee's execution does not
determine but must keep stable: the caller frame, the caller's continuation
and return place, the thread's unwind payloads, the allocations below the
callee's locals, and the addresses of the callee's locals. -/
structure Ctx : Type where
  caller : Frame
  payloads : List Ptr
  base : List Gen.Allocation
  addrs : List Int
  nextBlock : Gen.BbName
  unwindBlock : Option Gen.BbName
  retPtr : Ptr

/-- The pointer to local `_i`: allocation number `base.length + i`. -/
def localPtr (ctx : Ctx) (i : Nat) : Ptr :=
  { addr := ctx.addrs.getD i 0, provenance := some (⟨((ctx.base.length + i : Nat) : Int)⟩, ()) }

/-- The allocation backing local `_i`, as created by `storage_live`
("mem.allocate(AllocationKind::Stack, pointee_size, pointee_align)"). -/
def localAlloc (ctx : Ctx) (i : Nat) (it : Gen.IntType) (data : List Byte) : Gen.Allocation :=
  { data := data, addr := ctx.addrs.getD i 0, align := ⟨it.size.bytes⟩, kind := .Stack,
    live := true, extra := () }

/-- The callee's allocations for locals `_i, _(i+1), ..`, in local order. -/
def localAllocsFrom (ctx : Ctx) : Nat → List LocalDecl → List LocalSlot → List Gen.Allocation
  | i, d :: ds, slot :: slots =>
    localAlloc ctx i (itOf d) (slotData (itOf d) slot) :: localAllocsFrom ctx (i + 1) ds slots
  | _, _, _ => []

/-- The callee's allocations, one per local, in local order. -/
def localAllocs (ctx : Ctx) (decls : List LocalDecl) (locals : List LocalSlot) :
    List Gen.Allocation :=
  localAllocsFrom ctx 0 decls locals

/-- The callee frame's `locals` map: every local is live. -/
def localsMap (ctx : Ctx) (n : Nat) : Map Gen.LocalName Ptr :=
  ⟨(List.range n).map (fun i => (localName i, localPtr ctx i))⟩

/-- The callee frame at program counter `(blk, stmt)`. -/
def calleeFrame (f : Gen.Function) (ctx : Ctx) (n blk stmt : Nat) : Frame :=
  { func := f, locals := localsMap ctx n,
    stack_pop_action := .BackToCaller (some ctx.nextBlock) ctx.unwindBlock ctx.retPtr,
    next_block := bbName blk, next_stmt := (stmt : Int), extra := () }

/-- The single enabled thread with the given stack. -/
def thread1 (ctx : Ctx) (frames : List Frame) : Gen.Thread BM :=
  { stack := frames, state := .Enabled, unwind_payloads := ctx.payloads }

/-- The caller's return place: a live allocation in `base`, large enough for
the callee's return type and aligned for it. -/
def RetPlaceOk (ctx : Ctx) (it : Gen.IntType) : Prop :=
  ∃ (r : Nat) (a : Gen.Allocation), ctx.retPtr.provenance = some (⟨(r : Int)⟩, ()) ∧
    ctx.base[r]? = some a ∧ a.live = true ∧ a.addr = ctx.retPtr.addr ∧
    a.data.length = it.size.bytes ∧ ctx.retPtr.addr % (it.size.bytes : Int) = 0

/-- The state relation; see the module docs. -/
structure StateRel (body : CapturedMir) (f : Gen.Function) (ctx : Ctx) (s : MachineState)
    (m : Mach) : Prop where
  threads : m.threads =
    [thread1 ctx [ctx.caller, calleeFrame f ctx body.localDecls.length s.frame.blockIdx s.frame.stmtIdx]]
  active : m.active_thread = 0
  allocs : m.mem.memory.allocations = ctx.base ++ localAllocs ctx body.localDecls s.frame.locals
  blk : s.frame.blockIdx < body.basicBlocks.length
  stmt : ∀ bb, body.basicBlocks[s.frame.blockIdx]? = some bb → s.frame.stmtIdx ≤ bb.statements.length
  nlocals : s.frame.locals.length = body.localDecls.length
  slots : ∀ (i : Nat) d slot, body.localDecls[i]? = some d → s.frame.locals[i]? = some slot →
    SlotOk (itOf d) slot
  addrs : ∀ (i : Nat) d, body.localDecls[i]? = some d →
    ctx.addrs.getD i 0 % ((itOf d).size.bytes : Int) = 0
  ret : ∀ d, body.localDecls[0]? = some d → RetPlaceOk ctx (itOf d)
  borrows : s.memory.borrows = []
  callStack : s.memory.callStack = []
  activeCallee : s.memory.activeCallee = none
  protectors : s.memory.activeProtectors = []
  callerLocals : s.memory.callerLocals = []

/-- The MiniRust machine after the callee returned value `v` from state `s`:
the callee frame is gone, the caller continues at `nextBlock`, the return
place holds the encoding of `v`, and every callee allocation is dead. -/
def ReturnRel (body : CapturedMir) (ctx : Ctx) (s : MachineState) (v : Value) (m : Mach) : Prop :=
  ∃ (bits r : Nat) (a : Gen.Allocation) (d : LocalDecl),
    body.localDecls[0]? = some d ∧ v = .scalar ⟨bits, (itOf d).size.bytes⟩ ∧
    ctx.retPtr.provenance = some (⟨(r : Int)⟩, ()) ∧ ctx.base[r]? = some a ∧
    m.threads = [thread1 ctx [{ ctx.caller with next_block := ctx.nextBlock, next_stmt := 0 }]] ∧
    m.mem.memory.allocations =
      ctx.base.set r { a with data := scalarBytes (itOf d) bits } ++
        (localAllocs ctx body.localDecls s.frame.locals).map (fun a => { a with live := false })

/-- How one Anneal step and one MiniRust step correspond:

* a silent Anneal step corresponds to a MiniRust step to a related state;
* an Anneal branch-observation event (`switchInt` emits the scrutinee as a
  leakage tag; MiniRust has no such observable) followed by state `s'`
  corresponds to a MiniRust step to a state related to `s'`;
* an Anneal normal return of `v` corresponds to a MiniRust step that performs
  the full stack-pop action (`ReturnRel`);
* Anneal UB corresponds to MiniRust UB (`throw_ub!`), never to a specr-lang
  panic, a deadlock, or an unsupported construct;
* no other Anneal outcome (in particular `unsupported`) is possible. -/
def StepRel (body : CapturedMir) (f : Gen.Function) (ctx : Ctx) (s : MachineState)
    (a : MirStepNode) (r : Interp Mach) : Prop :=
  match a with
  | .tau (.running s') => ∃ m', r = .ok m' ∧ StateRel body f ctx s' m'
  | .vis (.inr (.inl (.emit _))) k =>
    ∃ s' m', k PUnit.unit = .running s' ∧ r = .ok m' ∧ StateRel body f ctx s' m'
  | .ret (.normal (v, _)) => ∃ m', r = .ok m' ∧ ReturnRel body ctx s v m'
  | .vis (.inl (.fail .ub)) _ => ∃ msg, r = .error (.ub msg)
  | _ => False

end MiniRustSpec.Correspondence
