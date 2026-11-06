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

/-- MiniRust storage integer type of a MIR local declaration: `u8` for `bool` or
`core::cmp::Ordering`, its own integer type for scalar integers, the field-0
integer type `it` for `(it, bool)` 2-tuples, the element integer type for
homogeneous arrays `[T; N]`, an unsigned integer type carrying the alignment
of a layout-backed tuple/struct (`TupleSpec`), or `usizeIt` (`8` bytes) for
thin raw pointers. -/
def itOf (d : LocalDecl) (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : Gen.IntType :=
  if isBoolTy d.ty || isOrderingTy d.ty then ⟨.Unsigned, ⟨1⟩⟩
  else
    match intTypeOf d.ty with
    | some it => it
    | none =>
      match intBoolTupleOf d.ty with
      | some it => it
      | none =>
        match arrayTypeOf d.ty with
        | some (elemIt, _) => elemIt
        | none =>
          match tupleTypeOf layouts d.ty with
          | some (_, _, align) => ⟨.Unsigned, ⟨align⟩⟩
          | none =>
            if isPtrTy d.ty then usizeIt
            else ⟨.Unsigned, ⟨1⟩⟩

/-- MiniRust type of a fragment local declaration (`Type::Int(..)`,
`Type::Bool`, `orderingTy`, `intBoolTupleTy`, `Type::Array`, `TupleSpec`'s
`Type::Tuple`, or `thinRawPtrTy`, as `minimize` translates it); the default is
never used for fragment bodies. -/
def tyOf (d : LocalDecl) (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : Gen.Type :=
  (translateTy layouts d.ty).getD (.Int (itOf d layouts))

/-- Byte size of a fragment type. -/
def tyBytes : Gen.Type → Nat
  | .Int it => it.size.bytes
  | .Enum _ _ _ size _ => size.bytes
  | .Tuple _ ⟨end_, _, _⟩ _ => end_.bytes
  | .Array (.Int elemIt) count => count.toNat * elemIt.size.bytes
  | .Ptr (.Raw .None) => 8
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

/-- The bytes `encode_ptr` produces for the thin pointer `⟨addr, prov⟩` with
`addr < 2^64` (`encodePtr_eq`). -/
def ptrBytes (addr : Nat) (prov : Option Prov) : List Byte :=
  encodePtrBytes prov 0 (leBytes addr 8)

theorem encodePtrBytes_length (prov : Option Prov) (i : Nat) (data : List UInt8) :
    (encodePtrBytes prov i data).length = data.length := by
  induction data generalizing i with
  | nil => rfl
  | cons b rest ih => simp [encodePtrBytes, ih]

theorem ptrBytes_length (addr : Nat) (prov : Option Prov) : (ptrBytes addr prov).length = 8 := by
  simp [ptrBytes, encodePtrBytes_length, leBytes_length]

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

/-- MiniRust bytes corresponding to an Anneal scalar local slot (meaningful for
scalar fragment slots, see `SlotOk`). -/
def slotData (it : Gen.IntType) : LocalSlot → List Byte
  | .init (.scalar sc) => scalarBytes it sc.bits
  | _ => uninitBytes it

/-- MiniRust bytes corresponding to an Anneal `(it, bool)` 2-tuple local slot. -/
def tupleSlotData (it : Gen.IntType) : LocalSlot → List Byte
  | .init (.aggregate 0 [.scalar sc0, .scalar sc1]) => tupleBytes it sc0.bits sc1.bits
  | _ => List.replicate (it.size.bytes + it.size.bytes) .Uninit

/-- MiniRust bytes corresponding to an Anneal local slot of declaration `d`
(scalar, `(Int, bool)` 2-tuple, homogeneous array, or padded tuple/struct). -/
def declSlotData (d : LocalDecl) (slot : LocalSlot)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : List Byte :=
  match intBoolTupleOf d.ty with
  | some it => tupleSlotData it slot
  | none =>
    if isBoolTy d.ty || isOrderingTy d.ty || (intTypeOf d.ty).isSome then
      slotData (itOf d layouts) slot
    else
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
        | none => slotData (itOf d layouts) slot

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

/-- Well-formedness of an initialized scalar element at integer type `it`. -/
def ElemOk (it : Gen.IntType) : Value → Prop
  | .scalar sc => sc.sizeBytes = it.size.bytes ∧ sc.bits < 2 ^ (8 * it.size.bytes)
  | _ => False

/-- Well-formedness of a fragment local slot for declaration `d`: scalar-family
locals satisfy `SlotOk (tyOf d layouts) slot`, array locals `[elemIt; count]`
hold an initialized `.aggregate 0 elems` of `count` well-formed elements, and
layout-backed tuple or struct locals hold an initialized value satisfying
`TupleSpec.valOk`. -/
def DeclSlotOk (d : LocalDecl) (slot : LocalSlot)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : Prop :=
  if (scalarTypeOf d.ty).isSome then
    SlotOk (tyOf d layouts) slot
  else
    match slot with
    | .dead => True
    | .uninit => True
    | .init v =>
      match arrayTypeOf d.ty with
      | some (elemIt, count) =>
        match v with
        | .aggregate 0 elems => elems.length = count ∧ ∀ e ∈ elems, ElemOk elemIt e
        | _ => False
      | none =>
        match tupleTypeOf layouts d.ty with
        | some (fields, size, align) =>
          (TupleSpec.tuple fields size align).wf = true ∧
          (TupleSpec.tuple fields size align).valOk v = true
        | none =>
          if isPtrTy d.ty then
            ∃ ptrVal, v = .ptr ptrVal 8
          else
            SlotOk (tyOf d layouts) (.init v)

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
  ptrTargets : Nat → Option (Nat × Option Prov) := fun _ => none

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
def localAllocsFrom (ctx : Ctx) (i : Nat) (decls : List LocalDecl) (locals : List LocalSlot)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : List Gen.Allocation :=
  match decls, locals with
  | d :: ds, slot :: slots =>
    localAlloc ctx i (itOf d layouts) (declSlotData d slot layouts) ::
      localAllocsFrom ctx (i + 1) ds slots layouts
  | _, _ => []

/-- The callee's initial allocations, one per local of `decls`, in local
order. -/
def localAllocs (ctx : Ctx) (decls : List LocalDecl) (locals : List LocalSlot)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : List Gen.Allocation :=
  localAllocsFrom ctx 0 decls locals layouts

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
  addr + (size : Int) < 2 ^ 32 ∨ (size < 2 ^ 63 ∧ ∃ k : Nat, addr = allocCandidate k)

/-- MiniRust's storage for local `_i` (declaration `d`, Anneal slot `slot`)
behind pointer `p`: allocation number `id` (at or above the caller's
allocations `base`), at an address that is well formed for `d`'s storage type,
holding the representation of `slot` (for an initialized thin raw pointer
local, 8 encoded pointer bytes `ptrBytes tAddr tProv` for some `tAddr < 2^64`,
whose exact target provenance and offset are tied to `s.memory.borrows` by
`BorrowsOk`). -/
def LocalStorage (ctx : Ctx) (allocs : List Gen.Allocation) (d : LocalDecl) (slot : LocalSlot)
    (p : Ptr) (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : Prop :=
  ∃ id : Nat, p.provenance = some (⟨(id : Int)⟩, ()) ∧ ctx.base.length ≤ id ∧
    AddrOk p.addr (itOf d layouts) ∧
    p.addr + (tyBytes (tyOf d layouts) : Int) < 2 ^ 64 ∧
    AddrClass p.addr (tyBytes (tyOf d layouts)) ∧
    if isPtrTy d.ty then
      match slot with
      | .init (.ptr pv 8) =>
        ∃ (tAddr : Nat) (tProv : Option Prov), tAddr < 2 ^ 64 ∧
          (∀ a pr, ctx.ptrTargets pv.allocId = some (a, pr) → tAddr = a ∧ tProv = pr) ∧
          allocs[id]? = some (stackAlloc p.addr (itOf d layouts) (ptrBytes tAddr tProv))
      | _ =>
        allocs[id]? = some (stackAlloc p.addr (itOf d layouts) (declSlotData d slot layouts))
    else
      allocs[id]? = some (stackAlloc p.addr (itOf d layouts) (declSlotData d slot layouts))

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
    DeclSlotOk d slot body.layouts
  base : ∃ R, allocs = ctx.base ++ R
  keysNodup : (lm.entries.map Prod.fst).Nodup
  keysLocal : ∀ e ∈ lm.entries, ∃ i, i < body.localDecls.length ∧ e.1 = localName i
  live : ∀ (i : Nat) slot, locals[i]? = some slot →
    ((mapGet lm (localName i)).isSome = true ↔ (slot ≠ .dead ∨ i ∈ al))
  storage : ∀ (i : Nat) d slot p, body.localDecls[i]? = some d → locals[i]? = some slot →
    mapGet lm (localName i) = some p → LocalStorage ctx allocs d slot p body.layouts
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
    LocalsOk body { ctx with ptrTargets := fun _ => none } view lm m.mem.memory.allocations
  active : m.active_thread = 0
  blk : s.frame.blockIdx < body.basicBlocks.length
  stmt : ∀ bb, body.basicBlocks[s.frame.blockIdx]? = some bb → s.frame.stmtIdx ≤ bb.statements.length
  stale : StaleOk body s.frame.locals view s.frame.blockIdx s.frame.stmtIdx
  retLive : view[0]? ≠ some .dead
  ret : ∀ d, body.localDecls[0]? = some d → RetPlaceOk ctx (tyOf d body.layouts) (itOf d body.layouts)
  baseLow : BaseLow ctx
  borrows : s.memory.borrows = [] ∨
    ¬ body.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true
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
    ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1)) s.frame.locals body.layouts
  blk0 : s.frame.blockIdx = 0
  stmt0 : s.frame.stmtIdx = 0
  hasBlocks : 0 < body.basicBlocks.length
  nlocals : s.frame.locals.length = body.localDecls.length
  slots : ∀ (i : Nat) d slot, body.localDecls[i]? = some d → s.frame.locals[i]? = some slot →
    DeclSlotOk d slot body.layouts
  argsLive : ∀ (i : Nat) slot, i ≤ body.argCount → s.frame.locals[i]? = some slot → slot ≠ .dead
  tempsDead : ∀ (i : Nat), body.argCount < i → i < body.localDecls.length →
    s.frame.locals[i]? = some .dead
  addrs : ∀ (i : Nat) d, i ≤ body.argCount → body.localDecls[i]? = some d →
    AddrOk (ctx.addrs.getD i 0) (itOf d body.layouts) ∧
      ctx.addrs.getD i 0 + (tyBytes (tyOf d body.layouts) : Int) < 2 ^ 32
  ret : ∀ d, body.localDecls[0]? = some d → RetPlaceOk ctx (tyOf d body.layouts) (itOf d body.layouts)
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
    AddrOk (ctx.addrs.getD i 0) (itOf d body.layouts) ∧
      ctx.addrs.getD i 0 + (tyBytes (tyOf d body.layouts) : Int) < 2 ^ 32
  ret : ∀ d, body.localDecls[0]? = some d → RetPlaceOk ctx (tyOf d body.layouts) (itOf d body.layouts)
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

/-- Decidable well-typedness of an incoming argument `v` for parameter
declaration `d` (scalar-family, homogeneous array, or padded tuple/struct). -/
def declArgOk (d : LocalDecl) (v : Value)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : Bool :=
  if (scalarTypeOf d.ty).isSome then
    argOk (tyOf d layouts) v
  else
    match arrayTypeOf d.ty with
    | some (elemIt, count) =>
      match v with
      | .aggregate 0 elems =>
        decide (elems.length = count) && elems.all (argOk (.Int elemIt))
      | _ => false
    | none =>
      match tupleTypeOf layouts d.ty with
      | some (fields, size, align) =>
        (TupleSpec.tuple fields size align).wf &&
        (TupleSpec.tuple fields size align).valOk v
      | none => argOk (tyOf d layouts) v

/-- Decidable well-typedness of argument values `args` against parameter
declarations `decls` (`_1 .. _argCount`). -/
def argsOkAux (decls : List LocalDecl) (vals : List Value)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : Bool :=
  match decls, vals with
  | [], [] => true
  | d :: ds, v :: vs => declArgOk d v layouts && argsOkAux ds vs layouts
  | _, _ => false

/-- Decidable well-typedness of `args` for `mirCallTree body args`: one
well-typed value per parameter `_1 .. _argCount`. -/
def argsOk (body : CapturedMir) (args : List Value) : Bool :=
  argsOkAux ((body.localDecls.take (body.argCount + 1)).drop 1) args body.layouts

/-- The MiniRust machine after the callee returned value `v`: the callee frame
is gone, the caller continues at `nextBlock`, the return place holds the
encoding of `v`, and every allocation above the caller's `base` is dead. -/
def ReturnRel (body : CapturedMir) (ctx : Ctx) (_s : MachineState) (v : Value) (m : Mach) : Prop :=
  ∃ (r : Nat) (a : Gen.Allocation) (d : LocalDecl) (R : List Gen.Allocation),
    body.localDecls[0]? = some d ∧ SlotOk (tyOf d body.layouts) (.init v) ∧
    ctx.retPtr.provenance = some (⟨(r : Int)⟩, ()) ∧ ctx.base[r]? = some a ∧
    m.threads = [thread1 ctx [{ ctx.caller with next_block := ctx.nextBlock, next_stmt := 0 }]] ∧
    m.mem.memory.allocations =
      ctx.base.set r { a with data := declSlotData d (.init v) body.layouts } ++ R ∧
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

end MiniRustSpec.Correspondence
