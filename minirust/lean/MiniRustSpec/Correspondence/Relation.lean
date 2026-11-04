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
  encoding of Anneal's slot (`declSlotData`): for scalar locals, `Uninit` bytes
  when `.uninit` and the little-endian bytes of the bit pattern when
  `.init (.scalar sc)`; for homogeneous array locals `[T; N]`, the concatenated
  little-endian byte encodings of the `N` scalar elements in
  `.init (.aggregate 0 elems)`. The callee's allocations sit after an arbitrary
  prefix `base` of allocations, which contains the caller's return place;
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

/-- MiniRust integer type (or element integer type for an array local, or an
integer type carrying the alignment of a tuple/struct local) of a MIR local
declaration. -/
def itOf (layouts : Layout.LayoutTable := ⟨64, true, []⟩) (d : LocalDecl) : Gen.IntType :=
  match arrayTypeOf d.ty with
  | some (elemIt, _) => elemIt
  | none =>
    match tupleTypeOf layouts d.ty with
    | some (_, _, align) => ⟨.Unsigned, ⟨align⟩⟩
    | none => (intTypeOf d.ty).getD ⟨.Unsigned, ⟨1⟩⟩

/-- `Type::encode` of `Value::Int(int_from_bits(bits))` at `Type::Int(it)`:
little-endian bytes without provenance. -/
def scalarBytes (it : Gen.IntType) (bits : Nat) : List Byte :=
  (leBytes bits it.size.bytes).map (fun b => .Init b none)

/-- The contents of a freshly allocated MiniRust local: all `Uninit`. -/
def uninitBytes (it : Gen.IntType) : List Byte := List.replicate it.size.bytes .Uninit

/-- MiniRust bytes corresponding to an Anneal scalar value at integer type `it`. -/
def valBytes (it : Gen.IntType) : Value → List Byte
  | .scalar sc => scalarBytes it sc.bits
  | _ => uninitBytes it

/-- Splice `bs` into `xs` starting at byte offset `off`, replacing `bs.length`
elements (`List::write_subslice_at_index` when `off + bs.length ≤ xs.length`). -/
def spliceAt {α : Type} (xs : List α) (off : Nat) (bs : List α) : List α :=
  xs.take off ++ bs ++ xs.drop (off + bs.length)

mutual

/-- MiniRust byte representation (`Type::encode`) of an Anneal value `v` at
`TupleSpec` `spec`:
- for `.scalar it`, the little-endian bytes `valBytes it v`;
- for `.tuple fields size align` and `.aggregate 0 vals`, starts from
  `List.replicate size .Uninit` and splices each field's encoding at its offset,
  preserving `.Uninit` in all inter-field and trailing padding gaps. -/
def TupleSpec.encodeVal : TupleSpec → Value → List Byte
  | .scalar it, v => valBytes it v
  | .tuple fields size _, .aggregate 0 vals =>
    TupleSpec.encodeFields fields vals (List.replicate size .Uninit)
  | .tuple _ size _, _ => List.replicate size .Uninit

/-- Field-by-field byte splicing for `TupleSpec.encodeVal`. -/
def TupleSpec.encodeFields : List (Nat × TupleSpec) → List Value → List Byte → List Byte
  | [], _, bytes => bytes
  | _, [], bytes => bytes
  | (off, s) :: restF, v :: restV, bytes =>
    TupleSpec.encodeFields restF restV (spliceAt bytes off (s.encodeVal v))

end

mutual

/-- MiniRust runtime `Val` corresponding to an Anneal `Value` at `TupleSpec`:
- for `.scalar it` and `.scalar sc`, `.Int (intFromBits sc.bits it)`;
- for `.tuple fields _ _` and `.aggregate 0 vals`,
  `.Tuple (TupleSpec.fieldsToMiniRustVal fields vals)`. -/
def TupleSpec.toMiniRustVal : TupleSpec → Value → Val
  | .scalar it, .scalar sc => .Int (intFromBits sc.bits it)
  | .scalar it, _ => .Int (intFromBits 0 it)
  | .tuple fields _ _, .aggregate 0 vals =>
    .Tuple (TupleSpec.fieldsToMiniRustVal fields vals)
  | .tuple _ _ _, _ => .Tuple []

/-- Pointwise conversion of tuple/struct field values to MiniRust `Val`s. -/
def TupleSpec.fieldsToMiniRustVal : List (Nat × TupleSpec) → List Value → List Val
  | [], _ => []
  | _, [] => []
  | (_, s) :: restF, v :: restV =>
    s.toMiniRustVal v :: TupleSpec.fieldsToMiniRustVal restF restV

end

mutual

/-- Decidable well-formedness of an initialized Anneal `Value` at `TupleSpec`:
for `.scalar it`, a scalar of `it.size.bytes` bytes with `bits < 2^(8 * it.size.bytes)`;
for `.tuple fields size align`, an `.aggregate 0 vals` with `vals.length = fields.length`
whose elements recursively satisfy `valOk`. -/
def TupleSpec.valOk : TupleSpec → Value → Bool
  | .scalar it, .scalar sc =>
    decide (sc.sizeBytes = it.size.bytes) && decide (sc.bits < 2 ^ (8 * it.size.bytes))
  | .scalar _, _ => false
  | .tuple fields _ _, .aggregate 0 vals =>
    decide (vals.length = fields.length) && TupleSpec.fieldsValOk fields vals
  | .tuple _ _ _, _ => false

/-- Pointwise `TupleSpec.valOk` across tuple/struct fields. -/
def TupleSpec.fieldsValOk : List (Nat × TupleSpec) → List Value → Bool
  | [], [] => true
  | (_, s) :: restF, v :: restV => s.valOk v && TupleSpec.fieldsValOk restF restV
  | _, _ => false

end

/-- MiniRust bytes corresponding to an Anneal local slot (meaningful for
fragment slots, see `SlotOk`). -/
def slotData (it : Gen.IntType) : LocalSlot → List Byte
  | .init (.scalar sc) => scalarBytes it sc.bits
  | _ => uninitBytes it

/-- MiniRust bytes corresponding to a scalar, homogeneous-array, or padded
tuple/struct local slot. -/
def declSlotData (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (d : LocalDecl) (slot : LocalSlot) : List Byte :=
  match arrayTypeOf d.ty with
  | some (elemIt, count) =>
    match slot with
    | .init (.aggregate 0 elems) => (elems.map (valBytes elemIt)).flatten
    | _ => List.replicate (count * elemIt.size.bytes) .Uninit
  | none =>
    match tupleTypeOf layouts d.ty with
    | some (fields, size, align) =>
      match slot with
      | .init v => (TupleSpec.tuple fields size align).encodeVal v
      | _ => List.replicate size .Uninit
    | none => slotData (itOf layouts d) slot

/-- Fragment slots: live, and holding either nothing or a scalar of the
declared size whose bit pattern is in range. -/
def SlotOk (it : Gen.IntType) : LocalSlot → Prop
  | .uninit => True
  | .init (.scalar sc) => sc.sizeBytes = it.size.bytes ∧ sc.bits < 2 ^ (8 * it.size.bytes)
  | _ => False

/-- Well-formedness of an initialized scalar element at integer type `it`. -/
def ElemOk (it : Gen.IntType) : Value → Prop
  | .scalar sc => sc.sizeBytes = it.size.bytes ∧ sc.bits < 2 ^ (8 * it.size.bytes)
  | _ => False

/-- Well-formedness of a fragment local slot for declaration `d`: scalar locals
satisfy `SlotOk (itOf layouts d) slot`, array locals `[elemIt; count]` hold an
initialized `.aggregate 0 elems` of `count` well-formed elements, and tuple or
struct locals hold an initialized value satisfying `TupleSpec.valOk`. -/
def DeclSlotOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (d : LocalDecl) (slot : LocalSlot) : Prop :=
  match arrayTypeOf d.ty with
  | some (elemIt, count) =>
    match slot with
    | .init (.aggregate 0 elems) =>
      elems.length = count ∧ ∀ v ∈ elems, ElemOk elemIt v
    | _ => False
  | none =>
    match tupleTypeOf layouts d.ty with
    | some (fields, size, align) =>
      match slot with
      | .init v =>
        (TupleSpec.tuple fields size align).wf = true ∧
        (TupleSpec.tuple fields size align).valOk v = true
      | _ => False
    | none => SlotOk (itOf layouts d) slot

/-- Alignment and address-space bounds for a local allocation at `addr`:
reduces definitionally to `addr % (itOf layouts d).size.bytes = 0` for scalar
locals, and additionally requires `0 ≤ addr` and `addr + byte_size < 2^64` for
array and tuple/struct locals so `ptr_offset_inbounds` does not overflow the
64-bit address space. -/
def AddrOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (addr : Int) (d : LocalDecl) : Prop :=
  match arrayTypeOf d.ty with
  | some (elemIt, count) =>
    addr % (elemIt.size.bytes : Int) = 0 ∧
    0 ≤ addr ∧
    addr + ((count * elemIt.size.bytes : Nat) : Int) < 2 ^ 64
  | none =>
    match tupleTypeOf layouts d.ty with
    | some (_, size, align) =>
      addr % (align : Int) = 0 ∧
      0 ≤ addr ∧
      addr + (size : Int) < 2 ^ 64
    | none => addr % ((itOf layouts d).size.bytes : Int) = 0

instance (layouts : Layout.LayoutTable) (addr : Int) (d : LocalDecl) :
    Decidable (AddrOk layouts addr d) := by
  unfold AddrOk
  cases arrayTypeOf d.ty with
  | some _ => infer_instance
  | none =>
    cases tupleTypeOf layouts d.ty <;> infer_instance

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
def localAllocsFrom (layouts : Layout.LayoutTable := ⟨64, true, []⟩) (ctx : Ctx) :
    Nat → List LocalDecl → List LocalSlot → List Gen.Allocation
  | i, d :: ds, slot :: slots =>
    localAlloc ctx i (itOf layouts d) (declSlotData layouts d slot) ::
      localAllocsFrom layouts ctx (i + 1) ds slots
  | _, _, _ => []

/-- The callee's allocations, one per local, in local order. -/
def localAllocs (layouts : Layout.LayoutTable := ⟨64, true, []⟩) (ctx : Ctx)
    (decls : List LocalDecl) (locals : List LocalSlot) :
    List Gen.Allocation :=
  localAllocsFrom layouts ctx 0 decls locals

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
  allocs : m.mem.memory.allocations =
    ctx.base ++ localAllocs body.layouts ctx body.localDecls s.frame.locals
  blk : s.frame.blockIdx < body.basicBlocks.length
  stmt : ∀ bb, body.basicBlocks[s.frame.blockIdx]? = some bb → s.frame.stmtIdx ≤ bb.statements.length
  nlocals : s.frame.locals.length = body.localDecls.length
  slots : ∀ (i : Nat) d slot, body.localDecls[i]? = some d → s.frame.locals[i]? = some slot →
    DeclSlotOk body.layouts d slot
  addrs : ∀ (i : Nat) d, body.localDecls[i]? = some d →
    AddrOk body.layouts (ctx.addrs.getD i 0) d
  ret : ∀ d, body.localDecls[0]? = some d → RetPlaceOk ctx (itOf body.layouts d)
  borrows : s.memory.borrows = []
  callStack : s.memory.callStack = []
  activeCallee : s.memory.activeCallee = none
  protectors : s.memory.activeProtectors = []
  callerLocals : s.memory.callerLocals = []

/-- Initial-entry relation at MiniRust's `f.start` (`minimize`'s synthesized
entry block `bbName body.basicBlocks.length`) and Anneal's entry point
(`blockIdx = 0`, `stmtIdx = 0`). One `Machine::step` executes `initBlock`
(`Goto(bb0)`) and lands in `StateRel`, without requiring a phantom `bb0`
machine. -/
structure StartRel (body : CapturedMir) (f : Gen.Function) (ctx : Ctx) (s : MachineState)
    (mInit : Mach) : Prop where
  threads : mInit.threads =
    [thread1 ctx [ctx.caller,
      { calleeFrame f ctx body.localDecls.length 0 0 with next_block := f.start }]]
  active : mInit.active_thread = 0
  allocs : mInit.mem.memory.allocations =
    ctx.base ++ localAllocs body.layouts ctx body.localDecls s.frame.locals
  blk0 : s.frame.blockIdx = 0
  stmt0 : s.frame.stmtIdx = 0
  hasBlocks : 0 < body.basicBlocks.length
  nlocals : s.frame.locals.length = body.localDecls.length
  slots : ∀ (i : Nat) d slot, body.localDecls[i]? = some d → s.frame.locals[i]? = some slot →
    DeclSlotOk body.layouts d slot
  addrs : ∀ (i : Nat) d, body.localDecls[i]? = some d →
    AddrOk body.layouts (ctx.addrs.getD i 0) d
  ret : ∀ d, body.localDecls[0]? = some d → RetPlaceOk ctx (itOf body.layouts d)
  borrows : s.memory.borrows = []
  callStack : s.memory.callStack = []
  activeCallee : s.memory.activeCallee = none
  protectors : s.memory.activeProtectors = []
  callerLocals : s.memory.callerLocals = []

/-- Well-formed caller context for executing `body`: every callee local address
is aligned for its type (and within address-space bounds for arrays and tuples),
and the caller's return place is a live, aligned allocation of `_0`'s byte size. -/
structure CtxOk (body : CapturedMir) (ctx : Ctx) : Prop where
  addrs : ∀ (i : Nat) d, body.localDecls[i]? = some d →
    AddrOk body.layouts (ctx.addrs.getD i 0) d
  ret : ∀ d, body.localDecls[0]? = some d → RetPlaceOk ctx (itOf body.layouts d)

/-- Decidable well-typedness of an incoming argument `v` for integer parameter
type `it`. -/
def argOk (it : Gen.IntType) : Value → Bool
  | .scalar sc => decide (sc.sizeBytes = it.size.bytes) && decide (sc.bits < 2 ^ (8 * it.size.bytes))
  | _ => false

/-- Decidable well-typedness of an incoming argument `v` for parameter
declaration `d` (scalar integer, homogeneous array, or padded tuple/struct). -/
def declArgOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (d : LocalDecl) (v : Value) : Bool :=
  match arrayTypeOf d.ty with
  | some (elemIt, count) =>
    match v with
    | .aggregate 0 elems =>
      decide (elems.length = count) && elems.all (argOk elemIt)
    | _ => false
  | none =>
    match tupleTypeOf layouts d.ty with
    | some (fields, size, align) =>
      (TupleSpec.tuple fields size align).wf &&
      (TupleSpec.tuple fields size align).valOk v
    | none => argOk (itOf layouts d) v

/-- Decidable well-typedness of argument values `args` against parameter
declarations `decls` (`_1 .. _argCount`). -/
def argsOkAux (layouts : Layout.LayoutTable := ⟨64, true, []⟩) :
    List LocalDecl → List Value → Bool
  | [], [] => true
  | d :: ds, v :: vs => declArgOk layouts d v && argsOkAux layouts ds vs
  | _, _ => false

/-- Decidable well-typedness of `args` for `mirCallTree body args`. -/
def argsOk (body : CapturedMir) (args : List Value) : Bool :=
  argsOkAux body.layouts body.localDecls.tail args

/-- The MiniRust machine after the callee returned value `v` from state `s`:
the callee frame is gone, the caller continues at `nextBlock`, the return
place holds the encoding of `v`, and every callee allocation is dead. -/
def ReturnRel (body : CapturedMir) (ctx : Ctx) (s : MachineState) (v : Value) (m : Mach) : Prop :=
  ∃ (bits r : Nat) (a : Gen.Allocation) (d : LocalDecl),
    body.localDecls[0]? = some d ∧ v = .scalar ⟨bits, (itOf body.layouts d).size.bytes⟩ ∧
    ctx.retPtr.provenance = some (⟨(r : Int)⟩, ()) ∧ ctx.base[r]? = some a ∧
    m.threads = [thread1 ctx [{ ctx.caller with next_block := ctx.nextBlock, next_stmt := 0 }]] ∧
    m.mem.memory.allocations =
      ctx.base.set r { a with data := scalarBytes (itOf body.layouts d) bits } ++
        (localAllocs body.layouts ctx body.localDecls s.frame.locals).map (fun a => { a with live := false })

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
