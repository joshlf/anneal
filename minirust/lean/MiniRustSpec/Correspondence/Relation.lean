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
* a MIR local `_i` is in the callee's `locals` map exactly when it is live in
  Anneal (its slot is not `.dead`), except for the temporaries that
  `minimize`'s init block allocates, which Anneal keeps dead and the fragment
  never mentions. A live local points to its own `Stack` allocation whose
  bytes are the representation-relation encoding of the slot: `Uninit` bytes
  for an uninitialized slot and the little-endian bytes of the bit pattern for
  an initialized scalar. An initialized `bool` slot holds `0` or `1`, and an
  initialized `core::cmp::Ordering` slot holds the bit pattern `255`, `0`, or
  `1` of the tag `-1`, `0`, or `1` (`ValidBits`), so its one byte decodes at
  its MiniRust type. Because `StorageLive` allocates afresh, the callee's
  allocations are not in local order: `LocalsOk` tracks, for each local, the
  pointer that the locals map holds. All of them sit after an arbitrary
  prefix `base` of allocations, which contains the caller's return place;
* the only exception to the encoding is a local that Anneal's `move` has
  de-initialized while MiniRust, whose `move` is a plain load, still holds the
  old bytes (`StaleOk`); the fragment check `movesOk` guarantees that no such
  local is read before it is written again;
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

/-- MiniRust storage integer type of a MIR local declaration: its own integer
type, the field-0 integer type `it` for an `(it, bool)` 2-tuple local (whose
alignment is `it.size.bytes`), or `u8` (the default) for a `bool` or
`core::cmp::Ordering` local, which occupies one byte with alignment one just
like a `u8` (`Type::layout` gives `Bool` the layout
`Sized(Size::from_bytes_const(1), Align::ONE)`, and `orderingTy` has size and
alignment 1). -/
def itOf (d : LocalDecl) : Gen.IntType :=
  ((intTypeOf d.ty).or (intBoolTupleOf d.ty)).getD ⟨.Unsigned, ⟨1⟩⟩

/-- MiniRust type of a fragment local declaration (`Type::Int(..)`,
`Type::Bool`, `orderingTy`, or `intBoolTupleTy`, as `minimize` translates it);
the default is never used for fragment bodies. -/
def tyOf (d : LocalDecl) : Gen.Type := (scalarTypeOf d.ty).getD (.Int (itOf d))

/-- Byte size of a fragment type. -/
def tyBytes : Gen.Type → Nat
  | .Int it => it.size.bytes
  | .Enum _ _ _ size _ => size.bytes
  | .Tuple _ ⟨end_, _, _⟩ _ => end_.bytes
  | _ => 1

/-- Whether a MiniRust type is `intBoolTupleTy it`, returning `it`. -/
def tupleIntOfTy : Gen.Type → Option Gen.IntType
  | .Tuple [(⟨0⟩, .Int it), (off1, .Bool)] ⟨end_, align, none⟩ none =>
    if off1 = it.size ∧ end_ = ⟨it.size.bytes + it.size.bytes⟩ ∧ align = ⟨it.size.bytes⟩ then
      some it
    else none
  | _ => none

/-- `Type::encode` of `Value::Int(int_from_bits(bits))` at `Type::Int(it)`:
little-endian bytes without provenance. -/
def scalarBytes (it : Gen.IntType) (bits : Nat) : List Byte :=
  (leBytes bits it.size.bytes).map (fun b => .Init b none)

/-- `Type::encode` of `Value::Tuple([Value::Int(intFromBits bits it), Value::Bool(b == 1)])`
at `intBoolTupleTy it`: field 0's `it.size.bytes` little-endian bytes at offset
`0`, field 1's `0`/`1` byte at offset `it.size.bytes`, and `it.size.bytes - 1`
trailing `AbstractByte::Uninit` padding bytes (`spec/lang/representation.md`). -/
def tupleBytes (it : Gen.IntType) (bits b : Nat) : List Byte :=
  scalarBytes it bits ++ scalarBytes u8Ty b ++ List.replicate (it.size.bytes - 1) .Uninit

/-- Whether a decoding result is a value (`Some(_)`, not `None` or a stop). -/
def decodesOk : Interp (Option Val) → Bool
  | .ok (some _) => true
  | _ => false

theorem decodesOk_iff (r : Interp (Option Val)) : decodesOk r = true ↔ ∃ v, r = .ok (some v) := by
  rcases r with _ | (_ | v) <;> simp [decodesOk]

/-- The bit patterns that encode a value of a fragment type: every in-range
pattern for an integer type; only `0` (`false`) and `1` (`true`) for `bool`,
whose other byte values MiniRust's `decode` rejects; and, for an enum (the
fragment's only enum is `core::cmp::Ordering`, `orderingTy`), the in-range
patterns whose little-endian bytes `Type::decode` accepts, that is, whose tag
the enum's discriminator maps to a variant. -/
def ValidBits : Gen.Type → Nat → Prop
  | .Int it, bits => bits < 2 ^ (8 * it.size.bytes)
  | .Bool, bits => bits < 2
  | T@(.Enum _ _ _ size _), bits => bits < 2 ^ (8 * size.bytes) ∧
      ∃ v, Type.decode T (scalarBytes ⟨.Unsigned, size⟩ bits) = .ok (some v)
  | _, _ => False

/-- Decidable `ValidBits`. -/
def validBits : Gen.Type → Nat → Bool
  | .Int it, bits => decide (bits < 2 ^ (8 * it.size.bytes))
  | .Bool, bits => decide (bits < 2)
  | T@(.Enum _ _ _ size _), bits => decide (bits < 2 ^ (8 * size.bytes)) &&
      decodesOk (Type.decode T (scalarBytes ⟨.Unsigned, size⟩ bits))
  | _, _ => false

theorem validBits_iff (T : Gen.Type) (bits : Nat) : validBits T bits = true ↔ ValidBits T bits := by
  cases T <;> simp [validBits, ValidBits, decodesOk_iff]

instance (T : Gen.Type) (bits : Nat) : Decidable (ValidBits T bits) :=
  decidable_of_iff _ (validBits_iff T bits)

/-- The contents of a freshly allocated MiniRust local: all `Uninit`. -/
def uninitBytes (it : Gen.IntType) : List Byte := List.replicate it.size.bytes .Uninit

/-- MiniRust bytes corresponding to an Anneal scalar local slot (meaningful for
scalar fragment slots, see `SlotOk`). -/
def slotData (it : Gen.IntType) : LocalSlot → List Byte
  | .init (.scalar sc) => scalarBytes it sc.bits
  | _ => uninitBytes it

/-- MiniRust bytes corresponding to an Anneal `(it, bool)` 2-tuple local slot. -/
def tupleSlotData (it : Gen.IntType) : LocalSlot → List Byte
  | .init (.aggregate 0 [.scalar sc0, .scalar sc1]) => tupleBytes it sc0.bits sc1.bits
  | _ => List.replicate (it.size.bytes + it.size.bytes) .Uninit

/-- MiniRust bytes corresponding to an Anneal local slot of declaration `d`. -/
def declSlotData (d : LocalDecl) (slot : LocalSlot) : List Byte :=
  match intBoolTupleOf d.ty with
  | some it => tupleSlotData it slot
  | none => slotData (itOf d) slot

/-- Fragment slots of type `T`: dead, or live and holding either nothing, a
scalar of `T`'s size whose bit pattern encodes a value of `T` (`ValidBits`),
or (when `T = intBoolTupleTy it`) a 2-tuple aggregate `(sc0, sc1)` of an
in-range integer scalar `sc0` of size `it.size.bytes` and a boolean scalar
`sc1` (`0` or `1`). -/
def SlotOk (T : Gen.Type) : LocalSlot → Prop
  | .dead => True
  | .uninit => True
  | .init (.scalar sc) => sc.sizeBytes = tyBytes T ∧ ValidBits T sc.bits
  | .init (.aggregate 0 [.scalar sc0, .scalar sc1]) =>
    ∃ it, tupleIntOfTy T = some it ∧
      sc0.sizeBytes = it.size.bytes ∧ sc0.bits < 2 ^ (8 * it.size.bytes) ∧
      sc1.sizeBytes = 1 ∧ sc1.bits < 2
  | _ => False

/-- The parts of the MiniRust machine that the callee's execution does not
determine but must keep stable: the caller frame, the caller's continuation
and return place, the thread's unwind payloads, the allocations below the
callee's locals, and the addresses at which the caller allocated the return
place and the arguments. -/
structure Ctx : Type where
  caller : Frame
  payloads : List Ptr
  base : List Gen.Allocation
  addrs : List Int
  nextBlock : Gen.BbName
  unwindBlock : Option Gen.BbName
  retPtr : Ptr

/-- The pointer to local `_i` in the callee's initial frame: allocation number
`base.length + i`. -/
def localPtr (ctx : Ctx) (i : Nat) : Ptr :=
  { addr := ctx.addrs.getD i 0, provenance := some (⟨((ctx.base.length + i : Nat) : Int)⟩, ()) }

/-- A live stack allocation for a local of storage integer type `it` at
address `addr` holding `data`, as created by `storage_live`
("mem.allocate(AllocationKind::Stack, pointee_size, pointee_align)") and then
written by stores. -/
def stackAlloc (addr : Int) (it : Gen.IntType) (data : List Byte) : Gen.Allocation :=
  { data := data, addr := addr, align := ⟨it.size.bytes⟩, kind := .Stack, live := true, extra := () }

/-- The allocation backing local `_i` in the callee's initial frame. -/
def localAlloc (ctx : Ctx) (i : Nat) (it : Gen.IntType) (data : List Byte) : Gen.Allocation :=
  stackAlloc (ctx.addrs.getD i 0) it data

/-- The callee's initial allocations for locals `_i, _(i+1), ..`, in local
order. -/
def localAllocsFrom (ctx : Ctx) : Nat → List LocalDecl → List LocalSlot → List Gen.Allocation
  | i, d :: ds, slot :: slots =>
    localAlloc ctx i (itOf d) (declSlotData d slot) :: localAllocsFrom ctx (i + 1) ds slots
  | _, _, _ => []

/-- The callee's initial allocations, one per local of `decls`, in local
order. -/
def localAllocs (ctx : Ctx) (decls : List LocalDecl) (locals : List LocalSlot) :
    List Gen.Allocation :=
  localAllocsFrom ctx 0 decls locals

/-- The locals map of a frame in which locals `_0 .. _(n-1)` live in their
initial allocations. -/
def localsMap (ctx : Ctx) (n : Nat) : Map Gen.LocalName Ptr :=
  ⟨(List.range n).map (fun i => (localName i, localPtr ctx i))⟩

/-- The callee frame with locals map `lm` at program counter `(blk, stmt)`. -/
def calleeFrameL (f : Gen.Function) (ctx : Ctx) (lm : Map Gen.LocalName Ptr) (blk stmt : Nat) :
    Frame :=
  { func := f, locals := lm,
    stack_pop_action := .BackToCaller (some ctx.nextBlock) ctx.unwindBlock ctx.retPtr,
    next_block := bbName blk, next_stmt := (stmt : Int), extra := () }

/-- The callee frame at program counter `(blk, stmt)` in which locals
`_0 .. _(n-1)` live in their initial allocations. -/
def calleeFrame (f : Gen.Function) (ctx : Ctx) (n blk stmt : Nat) : Frame :=
  calleeFrameL f ctx (localsMap ctx n) blk stmt

/-- The single enabled thread with the given stack. -/
def thread1 (ctx : Ctx) (frames : List Frame) : Gen.Thread BM :=
  { stack := frames, state := .Enabled, unwind_payloads := ctx.payloads }

/-- Address well-formedness for local `_i` of storage integer type `it`:
aligned to `it.size.bytes` and within `[0, 2^64)` so field-projection
`ptr_offset_inbounds` does not wrap around `2^64`. -/
@[reducible] def AddrOk (addr : Int) (it : Gen.IntType) : Prop :=
  addr % (it.size.bytes : Int) = 0 ∧ 0 ≤ addr ∧ addr + (it.size.bytes : Int) < 2 ^ 64

/-- Where the callee's locals may live: below `2^32` (where the caller
allocated the return place and the arguments), or at a first-fit candidate
address of `BM.pickAddr` (`allocCandidate k`), where `StorageLive` allocates.
This keeps the candidates that the callee's own locals do not occupy free for
the next `StorageLive`. -/
def AddrClass (addr : Int) (size : Nat) : Prop :=
  addr + (size : Int) < 2 ^ 32 ∨ ∃ k : Nat, addr = allocCandidate k

/-- MiniRust's storage for local `_i` (declaration `d`, Anneal slot `slot`)
behind pointer `p`: allocation number `id` (at or above the caller's
allocations `base`), at an address that is well formed for `d`'s storage type,
holding the representation of `slot`. -/
def LocalStorage (ctx : Ctx) (allocs : List Gen.Allocation) (d : LocalDecl) (slot : LocalSlot)
    (p : Ptr) : Prop :=
  ∃ id : Nat, p.provenance = some (⟨(id : Int)⟩, ()) ∧ ctx.base.length ≤ id ∧
    AddrOk p.addr (itOf d) ∧ AddrClass p.addr (tyBytes (tyOf d)) ∧
    allocs[id]? = some (stackAlloc p.addr (itOf d) (declSlotData d slot))

/-- Agreement of the callee's MiniRust locals map `lm` and the allocations
`allocs` with Anneal slots `locals`, once `minimize`'s init block has
allocated the temporaries `al` (a prefix of `alwaysStorageLiveLocals`, which
Anneal keeps dead and the fragment never mentions):

* the allocations extend the caller's `base`;
* `lm` maps each local at most once, and only locals of the body;
* a local is in `lm` exactly when its slot is live or it is one of `al`;
* each local in `lm` points to its own allocation (`LocalStorage`; distinct
  locals use distinct allocations);
* every live allocation above `base` belongs to a local in `lm`, so that
  `Return` deallocates all of them. -/
structure LocalsOkA (body : CapturedMir) (ctx : Ctx) (al : List Nat) (locals : List LocalSlot)
    (lm : Map Gen.LocalName Ptr) (allocs : List Gen.Allocation) : Prop where
  nlocals : locals.length = body.localDecls.length
  slots : ∀ (i : Nat) d slot, body.localDecls[i]? = some d → locals[i]? = some slot →
    SlotOk (tyOf d) slot
  base : ∃ R, allocs = ctx.base ++ R
  keysNodup : (lm.entries.map Prod.fst).Nodup
  keysLocal : ∀ e ∈ lm.entries, ∃ i, i < body.localDecls.length ∧ e.1 = localName i
  live : ∀ (i : Nat) slot, locals[i]? = some slot →
    ((mapGet lm (localName i)).isSome = true ↔ (slot ≠ .dead ∨ i ∈ al))
  storage : ∀ (i : Nat) d slot p, body.localDecls[i]? = some d → locals[i]? = some slot →
    mapGet lm (localName i) = some p → LocalStorage ctx allocs d slot p
  inj : ∀ (i j : Nat) p q, mapGet lm (localName i) = some p → mapGet lm (localName j) = some q →
    p.provenance = q.provenance → i = j
  owned : ∀ (id : Nat) a, allocs[id]? = some a → a.live = true → ctx.base.length ≤ id →
    ∃ (i : Nat) (p : Ptr), mapGet lm (localName i) = some p ∧ p.provenance = some (⟨(id : Int)⟩, ())

/-- `LocalsOkA` after the init block: all of `alwaysStorageLiveLocals` are
allocated. -/
abbrev LocalsOk (body : CapturedMir) (ctx : Ctx) (locals : List LocalSlot)
    (lm : Map Gen.LocalName Ptr) (allocs : List Gen.Allocation) : Prop :=
  LocalsOkA body ctx (alwaysStorageLiveLocals body) locals lm allocs

/-- The caller's return place: a live allocation in `base`, large enough for
the callee's return type `T` and aligned for `it`. -/
def RetPlaceOk (ctx : Ctx) (T : Gen.Type) (it : Gen.IntType) : Prop :=
  ∃ (r : Nat) (a : Gen.Allocation), ctx.retPtr.provenance = some (⟨(r : Int)⟩, ()) ∧
    ctx.base[r]? = some a ∧ a.live = true ∧ a.addr = ctx.retPtr.addr ∧
    a.data.length = tyBytes T ∧ ctx.retPtr.addr % (it.size.bytes : Int) = 0

/-- The caller's live allocations lie below `2^32`, clear of every first-fit
candidate address (`AddrClass`). -/
def BaseLow (ctx : Ctx) : Prop :=
  ∀ a ∈ ctx.base, a.live = true → a.addr + (a.data.length : Int) < 2 ^ 32

/-- How Anneal's slots `actual` may differ from the slots `view` that
MiniRust's memory represents: only for a local that the fragment check
`movesOk` treats as possibly moved out before statement `stmt` of block `blk`
(`movedBefore`), whose Anneal slot is then `.uninit` (Anneal's `move`
de-initialized it) while MiniRust still holds an allocation for it (with the
old bytes, since MiniRust's `move` is a plain load). -/
def StaleOk (body : CapturedMir) (actual view : List LocalSlot) (blk stmt : Nat) : Prop :=
  actual.length = view.length ∧
  ∀ j : Nat, actual[j]? ≠ view[j]? →
    j ∈ movedBefore body blk stmt ∧ actual[j]? = some .uninit ∧ view[j]? ≠ some .dead

/-- The state relation for a given MiniRust view `view` of the callee's
slots; see the module docs. -/
structure StateRelAt (body : CapturedMir) (f : Gen.Function) (ctx : Ctx) (s : MachineState)
    (view : List LocalSlot) (m : Mach) : Prop where
  frame : ∃ lm, m.threads =
      [thread1 ctx [ctx.caller, calleeFrameL f ctx lm s.frame.blockIdx s.frame.stmtIdx]] ∧
    LocalsOk body ctx view lm m.mem.memory.allocations
  active : m.active_thread = 0
  blk : s.frame.blockIdx < body.basicBlocks.length
  stmt : ∀ bb, body.basicBlocks[s.frame.blockIdx]? = some bb → s.frame.stmtIdx ≤ bb.statements.length
  stale : StaleOk body s.frame.locals view s.frame.blockIdx s.frame.stmtIdx
  retLive : view[0]? ≠ some .dead
  ret : ∀ d, body.localDecls[0]? = some d → RetPlaceOk ctx (tyOf d) (itOf d)
  baseLow : BaseLow ctx
  borrows : s.memory.borrows = []
  callStack : s.memory.callStack = []
  activeCallee : s.memory.activeCallee = none
  protectors : s.memory.activeProtectors = []
  callerLocals : s.memory.callerLocals = []

/-- The state relation; see the module docs. -/
def StateRel (body : CapturedMir) (f : Gen.Function) (ctx : Ctx) (s : MachineState) (m : Mach) :
    Prop :=
  ∃ view, StateRelAt body f ctx s view m

/-- Initial-entry relation at MiniRust's `f.start` (`minimize`'s synthesized
entry block `bbName body.basicBlocks.length`) and Anneal's entry point
(`blockIdx = 0`, `stmtIdx = 0`). The caller has allocated the return place
and the arguments, `_0 .. _argCount`, in local order at the addresses
`ctx.addrs` (`Machine::create_frame` in `spec/lang/step/terminators.md`
marks exactly these locals live), and Anneal's temporaries are dead. Running
`initBlock` (`StorageLive` of `alwaysStorageLiveLocals`, then `Goto(bb0)`)
lands in `StateRel`. -/
structure StartRel (body : CapturedMir) (f : Gen.Function) (ctx : Ctx) (s : MachineState)
    (mInit : Mach) : Prop where
  threads : mInit.threads =
    [thread1 ctx [ctx.caller,
      { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]]
  active : mInit.active_thread = 0
  allocs : mInit.mem.memory.allocations =
    ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1)) s.frame.locals
  blk0 : s.frame.blockIdx = 0
  stmt0 : s.frame.stmtIdx = 0
  hasBlocks : 0 < body.basicBlocks.length
  nlocals : s.frame.locals.length = body.localDecls.length
  slots : ∀ (i : Nat) d slot, body.localDecls[i]? = some d → s.frame.locals[i]? = some slot →
    SlotOk (tyOf d) slot
  argsLive : ∀ (i : Nat) slot, i ≤ body.argCount → s.frame.locals[i]? = some slot → slot ≠ .dead
  tempsDead : ∀ (i : Nat), body.argCount < i → i < body.localDecls.length →
    s.frame.locals[i]? = some .dead
  addrs : ∀ (i : Nat) d, i ≤ body.argCount → body.localDecls[i]? = some d →
    AddrOk (ctx.addrs.getD i 0) (itOf d) ∧ ctx.addrs.getD i 0 + (tyBytes (tyOf d) : Int) < 2 ^ 32
  ret : ∀ d, body.localDecls[0]? = some d → RetPlaceOk ctx (tyOf d) (itOf d)
  baseLow : BaseLow ctx
  borrows : s.memory.borrows = []
  callStack : s.memory.callStack = []
  activeCallee : s.memory.activeCallee = none
  protectors : s.memory.activeProtectors = []
  callerLocals : s.memory.callerLocals = []

/-- Well-formed caller context for executing `body`: the caller allocated the
return place and the arguments (`i ≤ body.argCount`) at addresses that are
aligned for their storage types and lie below `2^32`, the caller's own live
allocations lie below `2^32` (so `StorageLive` finds a free first-fit
candidate), and the caller's return place is a live, aligned allocation of
`_0`'s byte size. -/
structure CtxOk (body : CapturedMir) (ctx : Ctx) : Prop where
  addrs : ∀ (i : Nat) d, i ≤ body.argCount → body.localDecls[i]? = some d →
    AddrOk (ctx.addrs.getD i 0) (itOf d) ∧ ctx.addrs.getD i 0 + (tyBytes (tyOf d) : Int) < 2 ^ 32
  ret : ∀ d, body.localDecls[0]? = some d → RetPlaceOk ctx (tyOf d) (itOf d)
  baseLow : BaseLow ctx

/-- Decidable well-typedness of an incoming argument `v` for a parameter of
fragment type `T`: a scalar of `T`'s size whose bit pattern encodes a value of
`T` (for `bool`, only `0` and `1`), or a 2-tuple aggregate `(sc0, sc1)` when
`T = intBoolTupleTy it`. -/
def argOk (T : Gen.Type) : Value → Bool
  | .scalar sc => decide (sc.sizeBytes = tyBytes T) && validBits T sc.bits
  | .aggregate 0 [.scalar sc0, .scalar sc1] =>
    match tupleIntOfTy T with
    | some it =>
      decide (sc0.sizeBytes = it.size.bytes) && decide (sc0.bits < 2 ^ (8 * it.size.bytes)) &&
      decide (sc1.sizeBytes = 1) && decide (sc1.bits < 2)
    | none => false
  | _ => false

/-- Decidable well-typedness of argument values `args` against parameter
declarations `decls` (`_1 .. _argCount`). -/
def argsOkAux : List LocalDecl → List Value → Bool
  | [], [] => true
  | d :: ds, v :: vs => argOk (tyOf d) v && argsOkAux ds vs
  | _, _ => false

/-- Decidable well-typedness of `args` for `mirCallTree body args`: one
well-typed value per parameter `_1 .. _argCount`. -/
def argsOk (body : CapturedMir) (args : List Value) : Bool :=
  argsOkAux ((body.localDecls.take (body.argCount + 1)).drop 1) args

/-- The MiniRust machine after the callee returned value `v`: the callee frame
is gone, the caller continues at `nextBlock`, the return place holds the
encoding of `v`, and every allocation above the caller's `base` is dead. -/
def ReturnRel (body : CapturedMir) (ctx : Ctx) (_s : MachineState) (v : Value) (m : Mach) : Prop :=
  ∃ (r : Nat) (a : Gen.Allocation) (d : LocalDecl) (R : List Gen.Allocation),
    body.localDecls[0]? = some d ∧ SlotOk (tyOf d) (.init v) ∧
    ctx.retPtr.provenance = some (⟨(r : Int)⟩, ()) ∧ ctx.base[r]? = some a ∧
    m.threads = [thread1 ctx [{ ctx.caller with next_block := ctx.nextBlock, next_stmt := 0 }]] ∧
    m.mem.memory.allocations = ctx.base.set r { a with data := declSlotData d (.init v) } ++ R ∧
    ∀ b ∈ R, b.live = false

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

/-! ## Multi-function & multi-frame stack relation (`MR-4.1`) -/

/-- Local-declaration part of `translateFn` / `translateFnInProg` needed by
place evaluation, statement evaluation, and frame teardown: `f.ret` is `_0`
and `f.locals` maps every declared local `_i` to `tyOf d`. -/
def FnLocalsSpec (body : CapturedMir) (f : Gen.Function) : Prop :=
  f.ret = localName 0 ∧
  ∀ (i : Nat) d, body.localDecls[i]? = some d →
    scalarTypeOf d.ty = some (tyOf d) ∧ mapGet f.locals (localName i) = some (tyOf d)

/-- Generalized allocation-address bound on `base`: every live allocation in
`base` either lies below `2^32` (external caller allocations and function
pointers) or sits at one of at most `bound` stack-candidate addresses
`allocCandidate j` with byte length `≤ 32` (suspended MiniRust caller frames). -/
def BaseCandBounded (base : List Gen.Allocation) (bound : Nat) : Prop :=
  ∃ cands : List Nat, cands.length ≤ bound ∧
    ∀ a ∈ base, a.live = true →
      a.addr + (a.data.length : Int) < 2 ^ 32 ∨
      ∃ j ∈ cands, a.addr = allocCandidate j ∧ a.data.length ≤ 32

theorem BaseLow.toBaseCandBounded {ctx : Ctx} (h : BaseLow ctx) :
    BaseCandBounded ctx.base 0 :=
  ⟨[], Nat.le_refl _, fun a ha hl => .inl (h a ha hl)⟩

/-- Program and function-pointer table agreement on a MiniRust machine: `m.prog`
is `prog`, and every `(dp, fn)` in `fnMap` has a thin pointer in `m.fn_ptrs`
whose reverse lookup in `m.fn_ptrs` resolves uniquely back to `fn`. -/
def ProgEnvOk (prog : Gen.Program) (fnMap : FnMap)
    (m : Mach) : Prop :=
  m.prog = prog ∧
  ∀ dp fn, lookupFnName fnMap dp = some fn →
    ∃ ptr : Ptr, mapGet m.fn_ptrs fn = some ptr ∧
      m.fn_ptrs.entries.find? (fun (_, (fp : Ptr)) => decide (fp = ptr)) = some (fn, ptr)

/-- Must-live local invariant on an Anneal frame at `(blockIdx, stmtIdx)`. -/
def LiveInv (body : CapturedMir) (fr : StackFrame) : Prop :=
  ∀ i ∈ mustLiveBefore body fr.blockIdx fr.stmtIdx, fr.locals[i]? ≠ some .dead

/-- Must-initialized 2-tuple local invariant on an Anneal frame at
`(blockIdx, stmtIdx)`. -/
def TupleInv (body : CapturedMir) (fr : StackFrame) : Prop :=
  ∀ i ∈ tupleInitBefore body fr.blockIdx fr.stmtIdx,
    ∃ sc0 sc1, fr.locals[i]? = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1]))

/-- How a suspended caller's return destination `destination`, post-argument
locals `callerActual` and MiniRust view `callerView`, locals map `callerLm`, and
the callee's base allocations `calleeBase` and return pointer `calleeRetPtr`
relate while a callee is executing:
* `root`: `destination = ⟨dst, []⟩`, `prepare_for_inplace_passing` wrote
  `Uninit` bytes to `_dst` (`callerView[dst]? = some .uninit`), and
  `LocalsOk callerBody callerCtx callerView callerLm calleeBase` holds directly;
* `field0`: `destination = ⟨dst, [.field 0 fTy]⟩` of an `(it, bool)` tuple local
  holding `(sc0, sc1)`, `prepare_for_inplace_passing` wrote `Uninit` to field 0
  while preserving `sc1` and trailing padding, and `calleeRetPtr` points to the
  start of `_dst`'s allocation;
* `field1`: `destination = ⟨dst, [.field 1 fTy]⟩` of an `(it, bool)` tuple local
  holding `(sc0, sc1)`, `prepare_for_inplace_passing` wrote `Uninit` to field 1
  at byte offset `it.size.bytes` while preserving `sc0` and trailing padding,
  and `calleeRetPtr` points to offset `it.size.bytes` of `_dst`'s allocation. -/
inductive CallerDestRel (callerBody : CapturedMir) (callerCtx : Ctx)
    (callerActual callerView : List LocalSlot) (callerLm : Map Gen.LocalName Ptr)
    (calleeRetDecl : LocalDecl) (calleeBase : List Gen.Allocation)
    (calleeRetPtr : Ptr) : Place → Prop where
  | root (dst : Nat) (dDst : LocalDecl) (callerSlot : LocalSlot)
      (hActual : callerActual[dst]? = some callerSlot)
      (hLive : callerSlot ≠ .dead)
      (hView : callerView[dst]? = some .uninit)
      (hdDst : callerBody.localDecls[dst]? = some dDst)
      (hSameTy : sameFragmentTy dDst.ty calleeRetDecl.ty = true)
      (hLocs : LocalsOk callerBody callerCtx callerView callerLm calleeBase)
      (hPtr : mapGet callerLm (localName dst) = some calleeRetPtr) :
      CallerDestRel callerBody callerCtx callerActual callerView callerLm
        calleeRetDecl calleeBase calleeRetPtr ⟨dst, []⟩
  | field0 (dst : Nat) (fTy : Ty) (dDst : LocalDecl) (it : Gen.IntType)
      (sc0 sc1 : ScalarInt) (allocPre : List Gen.Allocation) (idDst : Nat)
      (hActual : callerActual[dst]? = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1])))
      (hView : callerView[dst]? = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1])))
      (hdDst : callerBody.localDecls[dst]? = some dDst)
      (hTup : intBoolTupleOf dDst.ty = some it)
      (hfTy : intTypeOf fTy = some it)
      (hRetTy : intTypeOf calleeRetDecl.ty = some it)
      (hsc1 : sc1.sizeBytes = 1 ∧ sc1.bits < 2)
      (hLocs : LocalsOk callerBody callerCtx callerView callerLm allocPre)
      (hPtr : mapGet callerLm (localName dst) = some calleeRetPtr)
      (hProv : calleeRetPtr.provenance = some (⟨(idDst : Int)⟩, ()))
      (hAllocPre : allocPre[idDst]? =
        some (stackAlloc calleeRetPtr.addr it (tupleBytes it sc0.bits sc1.bits)))
      (hBase : calleeBase = allocPre.set idDst
        (stackAlloc calleeRetPtr.addr it
          (uninitBytes it ++ scalarBytes u8Ty sc1.bits ++
            List.replicate (it.size.bytes - 1) .Uninit))) :
      CallerDestRel callerBody callerCtx callerActual callerView callerLm
        calleeRetDecl calleeBase calleeRetPtr ⟨dst, [.field 0 fTy]⟩
  | field1 (dst : Nat) (fTy : Ty) (dDst : LocalDecl) (it : Gen.IntType)
      (sc0 sc1 : ScalarInt) (allocPre : List Gen.Allocation) (pDst : Ptr) (idDst : Nat)
      (hActual : callerActual[dst]? = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1])))
      (hView : callerView[dst]? = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1])))
      (hdDst : callerBody.localDecls[dst]? = some dDst)
      (hTup : intBoolTupleOf dDst.ty = some it)
      (hfTy : isBoolTy fTy = true)
      (hRetTy : isBoolTy calleeRetDecl.ty = true)
      (hsc0 : sc0.sizeBytes = it.size.bytes ∧ sc0.bits < 2 ^ (8 * it.size.bytes))
      (hLocs : LocalsOk callerBody callerCtx callerView callerLm allocPre)
      (hPtr : mapGet callerLm (localName dst) = some pDst)
      (hProv : pDst.provenance = some (⟨(idDst : Int)⟩, ()))
      (hRetPtr : calleeRetPtr = { addr := pDst.addr + (it.size.bytes : Int), provenance := pDst.provenance })
      (hAllocPre : allocPre[idDst]? =
        some (stackAlloc pDst.addr it (tupleBytes it sc0.bits sc1.bits)))
      (hBase : calleeBase = allocPre.set idDst
        (stackAlloc pDst.addr it
          (scalarBytes it sc0.bits ++ [.Uninit] ++
            List.replicate (it.size.bytes - 1) .Uninit))) :
      CallerDestRel callerBody callerCtx callerActual callerView callerLm
        calleeRetDecl calleeBase calleeRetPtr ⟨dst, [.field 1 fTy]⟩

/-- Inductive correspondence between Anneal's top-first `callStack : List SavedCallerFrame`
and MiniRust's bottom-first prefix `callerFrames : List Frame` below the active
body `curBody` (whose active context is `curCtx`, stack-candidate bound is
`candBound`, and remaining call-graph fuel is `remFuel`). -/
inductive CallStackRel (entry : CapturedMir) (callees : List CapturedMir)
    (fnMap : FnMap) (rootCtx : Ctx) :
    List SavedCallerFrame → List Frame → CapturedMir → Ctx → Nat → Nat → Prop where
  | nil (hBase : BaseLow rootCtx)
      (hRet : ∀ d, entry.localDecls[0]? = some d → RetPlaceOk rootCtx (tyOf d) (itOf d))
      (rootBudget : Nat)
      (hBudget : maxStackLocalsAux (callees.length + 1) callees entry = some rootBudget)
      (hBudgetLt : rootBudget < 2 ^ 31) :
      CallStackRel entry callees fnMap rootCtx [] [rootCtx.caller] entry rootCtx
        0 (callees.length + 1)
  | cons {savedCaller : SavedCallerFrame} {restStack : List SavedCallerFrame}
      {preFrames : List Frame} {callerBody curBody : CapturedMir}
      {callerFn : Gen.Function} {callerCtx curCtx : Ctx}
      {callerCandBound callerFuel : Nat}
      {callerView : List LocalSlot} {callerLm : Map Gen.LocalName Ptr}
      {calleeRetDecl : LocalDecl} {callerBudget curBudget : Nat}
      (hRest : CallStackRel entry callees fnMap rootCtx restStack preFrames
        callerBody callerCtx callerCandBound (callerFuel + 1))
      (hCallerEq : savedCaller.callerBody = callerBody)
      (hCallerMem : callerBody ∈ entry :: callees)
      (hCallerFn : translateFnInProg fnMap callerBody = some callerFn)
      (hProtNone : savedCaller.callerProtector = none)
      (hCalleeProts : savedCaller.calleeProtectors = [])
      (hTargetLt : savedCaller.returnTarget < callerBody.basicBlocks.length)
      (hPayloads : curCtx.payloads = rootCtx.payloads)
      (hNextBlk : curCtx.nextBlock = bbName savedCaller.returnTarget)
      (hCallerFrame : curCtx.caller =
        calleeFrameL callerFn callerCtx callerLm
          savedCaller.frame.blockIdx savedCaller.frame.stmtIdx)
      (hCalleeRetDecl : curBody.localDecls[0]? = some calleeRetDecl)
      (hDest : CallerDestRel callerBody callerCtx savedCaller.frame.locals callerView
        callerLm calleeRetDecl curCtx.base curCtx.retPtr savedCaller.destination)
      (hCallerCand : BaseCandBounded callerCtx.base callerCandBound)
      (hCallerBudget : maxStackLocalsAux (callerFuel + 1) callees callerBody = some callerBudget)
      (hCurBudget : maxStackLocalsAux callerFuel callees curBody = some curBudget)
      (hStepBudget : callerBody.localDecls.length + curBudget ≤ callerBudget)
      (hCallerBudgetLt : callerCandBound + callerBudget < 2 ^ 31)
      (hPostLen : savedCaller.frame.locals.length = callerView.length)
      (hPostStale : ∀ j : Nat, j ≠ savedCaller.destination.local_ →
        savedCaller.frame.locals[j]? ≠ callerView[j]? →
        j ∈ movedBefore callerBody savedCaller.returnTarget 0 ∧
          savedCaller.frame.locals[j]? = some .uninit ∧ callerView[j]? ≠ some .dead)
      (hPostLive : ∀ i ∈ liveAtEntry callerBody savedCaller.returnTarget,
        i ≠ savedCaller.destination.local_ → savedCaller.frame.locals[i]? ≠ some .dead)
      (hPostTuple : ∀ i ∈ tupleInitAtEntry callerBody savedCaller.returnTarget,
        i ≠ savedCaller.destination.local_ →
        ∃ sc0 sc1, savedCaller.frame.locals[i]? =
          some (.init (.aggregate 0 [.scalar sc0, .scalar sc1]))) :
      CallStackRel entry callees fnMap rootCtx (savedCaller :: restStack)
        (preFrames ++ [curCtx.caller]) curBody curCtx
        (callerCandBound + callerBody.localDecls.length) callerFuel

/-- Multi-frame state relation at active MiniRust view `view` for `(entry, callees, prog)`
and external root caller context `rootCtx`. -/
structure MultiStateRelAt (entry : CapturedMir) (callees : List CapturedMir)
    (prog : Gen.Program) (rootCtx : Ctx) (s : MachineState)
    (view : List LocalSlot) (m : Mach) : Prop where
  stack : ∃ (callerFrames : List Frame) (curCtx : Ctx) (curFn : Gen.Function)
      (curLm : Map Gen.LocalName Ptr) (candBound remFuel curBudget : Nat),
    let curBody := s.memory.activeCallee.getD entry
    let fnMap := fnNameMap entry callees
    curBody ∈ entry :: callees ∧
    translateFnInProg fnMap curBody = some curFn ∧
    CallStackRel entry callees fnMap rootCtx s.memory.callStack callerFrames
      curBody curCtx candBound remFuel ∧
    curCtx.payloads = rootCtx.payloads ∧
    BaseCandBounded curCtx.base candBound ∧
    maxStackLocalsAux remFuel callees curBody = some curBudget ∧
    candBound + curBudget < 2 ^ 31 ∧
    m.threads =
      [thread1 rootCtx
        (callerFrames ++ [calleeFrameL curFn curCtx curLm s.frame.blockIdx s.frame.stmtIdx])] ∧
    LocalsOk curBody curCtx view curLm m.mem.memory.allocations
  env : ProgEnvOk prog (fnNameMap entry callees) m
  active : m.active_thread = 0
  blk : s.frame.blockIdx < (s.memory.activeCallee.getD entry).basicBlocks.length
  stmt : ∀ bb, (s.memory.activeCallee.getD entry).basicBlocks[s.frame.blockIdx]? = some bb →
    s.frame.stmtIdx ≤ bb.statements.length
  stale : StaleOk (s.memory.activeCallee.getD entry) s.frame.locals view
    s.frame.blockIdx s.frame.stmtIdx
  retLive : view[0]? ≠ some .dead
  liveInv : LiveInv (s.memory.activeCallee.getD entry) s.frame
  tupleInv : TupleInv (s.memory.activeCallee.getD entry) s.frame
  calleesEq : s.memory.callees = callees
  activeCalleeOk :
    (s.memory.callStack = [] →
      s.memory.activeCallee = none ∨ s.memory.activeCallee = some entry) ∧
    (s.memory.callStack ≠ [] → ∃ c, s.memory.activeCallee = some c)
  borrows : s.memory.borrows = []
  protectors : s.memory.activeProtectors = []
  callerLocals : s.memory.callerLocals = []

/-- Multi-frame state relation between an Anneal `MachineState` and a MiniRust
machine `m` executing `(entry, callees)` translated to `prog`. -/
def MultiStateRel (entry : CapturedMir) (callees : List CapturedMir)
    (prog : Gen.Program) (rootCtx : Ctx) (s : MachineState) (m : Mach) : Prop :=
  ∃ view, MultiStateRelAt entry callees prog rootCtx s view m

/-- Multi-function initial-entry relation at `fEntry.start` (`initBlock entry`)
and Anneal's `initMachineStateWithCallees entry args callees`. -/
structure MultiStartRel (entry : CapturedMir) (callees : List CapturedMir)
    (prog : Gen.Program) (fEntry : Gen.Function) (rootCtx : Ctx)
    (s : MachineState) (mInit : Mach) : Prop where
  hfEntry : translateFnInProg (fnNameMap entry callees) entry = some fEntry
  env : ProgEnvOk prog (fnNameMap entry callees) mInit
  threads : mInit.threads =
    [thread1 rootCtx [rootCtx.caller,
      { calleeFrame fEntry rootCtx (entry.argCount + 1) 0 0 with next_block := fEntry.start }]]
  active : mInit.active_thread = 0
  allocs : mInit.mem.memory.allocations =
    rootCtx.base ++ localAllocs rootCtx (entry.localDecls.take (entry.argCount + 1)) s.frame.locals
  blk0 : s.frame.blockIdx = 0
  stmt0 : s.frame.stmtIdx = 0
  hasBlocks : 0 < entry.basicBlocks.length
  nlocals : s.frame.locals.length = entry.localDecls.length
  slots : ∀ (i : Nat) d slot, entry.localDecls[i]? = some d → s.frame.locals[i]? = some slot →
    SlotOk (tyOf d) slot
  argsInit : ∀ (i : Nat) d, 1 ≤ i → i ≤ entry.argCount → entry.localDecls[i]? = some d →
    ∃ v, s.frame.locals[i]? = some (.init v) ∧ SlotOk (tyOf d) (.init v)
  argsLive : ∀ (i : Nat) slot, i ≤ entry.argCount → s.frame.locals[i]? = some slot → slot ≠ .dead
  tempsDead : ∀ (i : Nat), entry.argCount < i → i < entry.localDecls.length →
    s.frame.locals[i]? = some .dead
  addrs : ∀ (i : Nat) d, i ≤ entry.argCount → entry.localDecls[i]? = some d →
    AddrOk (rootCtx.addrs.getD i 0) (itOf d) ∧ rootCtx.addrs.getD i 0 + (tyBytes (tyOf d) : Int) < 2 ^ 32
  ret : ∀ d, entry.localDecls[0]? = some d → RetPlaceOk rootCtx (tyOf d) (itOf d)
  baseLow : BaseLow rootCtx
  calleesEq : s.memory.callees = callees
  borrows : s.memory.borrows = []
  callStack : s.memory.callStack = []
  activeCallee : s.memory.activeCallee = none
  protectors : s.memory.activeProtectors = []
  callerLocals : s.memory.callerLocals = []

/-- Multi-frame step correspondence:
* one Anneal silent step `.tau` corresponds to `k ≥ 1` MiniRust steps
  (`k = 1` for statements, `Goto`, and `Return` to a caller frame;
  `k = 1 + initLen callee` for `TerminatorKind.call`, running `Call` plus the
  callee's `initBlock`) reaching a related `MultiStateRel` state (`steps_ok_mono`
  guarantees all intermediate steps `< k` also succeed);
* one Anneal branch-observation event `.emit` corresponds to `1` MiniRust step
  reaching a related `MultiStateRel` state;
* an Anneal root normal return corresponds to `1` MiniRust step (`Return` on the
  bottom `entry` frame) satisfying `ReturnRel entry rootCtx s v m'`;
* Anneal UB corresponds to `1` MiniRust step throwing UB (`Interp.step m =
  .error (.ub msg)`), including call-argument evaluation UB and callee UB;
* no other Anneal outcome (`unsupported`, panic, deadlock) is possible. -/
def MultiStepRel (entry : CapturedMir) (callees : List CapturedMir)
    (prog : Gen.Program) (rootCtx : Ctx) (s : MachineState)
    (a : MirStepNode) (m : Mach) : Prop :=
  match a with
  | .tau (.running s') =>
    ∃ k m', 1 ≤ k ∧ Interp.steps k m = .ok m' ∧
      MultiStateRel entry callees prog rootCtx s' m'
  | .vis (.inr (.inl (.emit _))) k =>
    ∃ s' m', k PUnit.unit = .running s' ∧ Interp.step m = .ok m' ∧
      MultiStateRel entry callees prog rootCtx s' m'
  | .ret (.normal (v, _)) =>
    ∃ m', Interp.step m = .ok m' ∧ ReturnRel entry rootCtx s v m'
  | .vis (.inl (.fail .ub)) _ =>
    ∃ msg, Interp.step m = .error (.ub msg)
  | _ => False

end MiniRustSpec.Correspondence
