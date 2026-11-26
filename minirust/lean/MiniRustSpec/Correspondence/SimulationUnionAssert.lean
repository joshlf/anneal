/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.Simulation

/-!
# Union (`Type.Union`) and `TerminatorKind.assert` Simulation (`MiniRustSpec.Correspondence.SimulationUnionAssert`)

Extracted from `MiniRustSpec.Correspondence.Simulation` to keep every union/assert
module strictly `< 3,500` LOC while preserving `Simulation.lean` at its baseline scope.

Scope disclosures:
* `translateFnWithUnions` requires `blocksAreExits body = true` (exit-only blocks whose
  terminators are `return` or `unreachable`, avoiding cross-block `StorageLive` prologue
  clobbering; multi-block CFGs are out of scope and return `none`).
* `reaches_rel_withUnions`, `run_ret_withUnions`, and `run_ub_withUnions` are conditional
  simulation schemas parameterized by `(Inv, hinv, hstep)` instantiated on concrete
  witnesses (see `MiniRustSpec.Correspondence.WitnessUnionAssert`), rather than universal
  arbitrary-CFG lowering theorems.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Sequence
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp

/-! ## `Type.Union` (`MaybeUninit<T>`, `ManuallyDrop<T>`, and Padded `[(); N]` ZST-Arm Unions)

MiniRust represents a union value as the bytes of its chunks
(`Value.Union chunkData`). This section covers single-chunk unions
(`mrUnionTy fields S al`, one chunk `[(0, S)]`):

* `Type_decode_mrUnionTy`, `checkValue_mrUnionTy`, and `Type_encode_mrUnionTy`:
  a whole-union load accepts any `S` bytes, `.Uninit` ones included, and a
  whole-union store writes them back unchanged, so whole-union copies and
  moves preserve uninitialized padding bytes.
* `evalPlace_field_mrUnionTy`: projecting a field at offset `0` is an address
  computation that reads no byte of the union.
* `placeLoad_mrUnitTy` and `placeLoad_mrZstArrayTy`: a load at `()` or
  `[(); N]` reads no allocation, so reading an inhabited 0-byte arm succeeds
  however many of the union's bytes are uninitialized (`kani#5176`).
* `placeLoad_mrUninhabitedZstTy`: a load at an uninhabited 0-byte type
  (`mrUninhabitedZstTy`) is UB, whatever the union's bytes are (`kani#5159`).
* `Type_decode_int_of_uninit`: a load at an integer type is UB when one of the
  bytes it reads is `.Uninit`.

Two modeling choices are not `minimize`'s:

* `minimize`'s union chunks come from `calc_chunks`
  (`tooling/minimize/src/chunks.rs`), which marks only the data bytes of the
  fields, not their padding. They form the single chunk `[(0, S)]` exactly when
  the fields' data bytes together cover `[0, S)`, as the `u32` field alone does
  in `MaybeUninit<u32>` and in the witnesses' `PU`. If no field covers some
  byte, that byte lies outside every chunk, and MiniRust's whole-union copy
  resets it to `.Uninit`.
* `minimize` lowers a union aggregate `_u = U { f: op }` to
  `ValueExpr::Union { field, expr, union_ty }` (`tooling/minimize/src/rvalue.rs`),
  which `Interp.evalValue` does not implement. Its value is `S` uninitialized
  bytes with `op`'s encoding written at field `f`'s offset
  (`spec/lang/step/expressions.md`), so storing it has the effect of
  `Deinit(_u)` followed by the field assignment `_u.f = op`; the witnesses in
  `Witness.lean` lower union aggregates that way. -/

/-- MiniRust `()` type (`0` bytes, alignment `1`). -/
def mrUnitTy : Gen.«Type» := .Tuple [] ⟨⟨0⟩, ⟨1⟩, none⟩ none

/-- MiniRust `[(); N]` ZST array type (`0` bytes, alignment `1`). -/
def mrZstArrayTy (N : Nat) : Gen.«Type» := .Array mrUnitTy (N : Int)

/-- MiniRust uninhabited 0-byte type (`Never` / `VoidZst`: `0` variants,
`Discriminator.Invalid`, `0` bytes, alignment `1`). -/
def mrUninhabitedZstTy : Gen.«Type» := .Enum ⟨[]⟩ u8Ty .Invalid ⟨0⟩ ⟨1⟩

/-- MiniRust `#[repr(transparent)] struct ManuallyDrop<T> { value: T }`
(single field at offset `0`). -/
def mrManuallyDropTy (innerTy : Gen.«Type») (sizeBytes alignBytes : Nat) : Gen.«Type» :=
  .Tuple [(⟨0⟩, innerTy)] ⟨⟨sizeBytes⟩, ⟨alignBytes⟩, none⟩ none

/-- Single-chunk MiniRust `Type.Union` of size `sizeBytes` and alignment
`alignBytes`, with chunk `[(⟨0⟩, ⟨sizeBytes⟩)]` covering `[0, sizeBytes)`, so
whole-union `Type.decode` and `Type.encode` preserve all `.Init` and `.Uninit`
bytes. `minimize` gives a union this chunk list only when its fields' data
bytes together cover `[0, sizeBytes)` (see the section comment). -/
def mrUnionTy (fields : List (Gen.Offset × Gen.«Type»)) (sizeBytes alignBytes : Nat) : Gen.«Type» :=
  .Union fields [(⟨0⟩, ⟨sizeBytes⟩)] ⟨sizeBytes⟩ ⟨alignBytes⟩

/-- MiniRust `MaybeUninit<T>` (`union MaybeUninit<T> { uninit: (), value: ManuallyDrop<T> }`). -/
def mrMaybeUninitTy (innerTy : Gen.«Type») (sizeBytes alignBytes : Nat) : Gen.«Type» :=
  mrUnionTy [(⟨0⟩, mrUnitTy), (⟨0⟩, mrManuallyDropTy innerTy sizeBytes alignBytes)] sizeBytes alignBytes

/-- MiniRust padded `#[repr(C)] union PU { z: [(); N], p: Payload }` (`kani#5176`)
with optional uninhabited 0-byte arm `void: VoidZst` (`kani#5159`). -/
def mrPaddedZstUnionTy (N : Nat) (payloadTy : Gen.«Type») (sizeBytes alignBytes : Nat) : Gen.«Type» :=
  mrUnionTy [(⟨0⟩, mrZstArrayTy N), (⟨0⟩, payloadTy), (⟨0⟩, mrUninhabitedZstTy)] sizeBytes alignBytes

theorem Type_layout_mrUnitTy :
    Interp.Type.layout mrUnitTy = .ok (.Sized ⟨0⟩ ⟨1⟩) := rfl

theorem Type_layout_mrZstArrayTy (N : Nat) :
    Interp.Type.layout (mrZstArrayTy N) = .ok (.Sized ⟨0⟩ ⟨1⟩) := by
  simp [mrZstArrayTy, Interp.Type.layout, mrUnitTy, TupleHeadLayout.head_size_and_align,
    Size.align_to, LayoutStrategy.expect_size, LayoutStrategy.expect_align,
    Size.mulInt, Size.from_bytes, pure, Except.pure, bind, Except.bind]

theorem Type_layout_mrUnionTy (fields : List (Gen.Offset × Gen.«Type»)) (sz al : Nat) :
    Interp.Type.layout (mrUnionTy fields sz al) = .ok (.Sized ⟨sz⟩ ⟨al⟩) := rfl

theorem Type_decode_mrUnitTy :
    Interp.Type.decode mrUnitTy [] = .ok (some (.Tuple [])) := rfl

theorem checkValue_mrUnitTy (m : Option Mach := none) :
    Interp.checkValue (.Tuple []) mrUnitTy m = .ok () := rfl

theorem Type_encode_mrUnitTy :
    Interp.Type.encode mrUnitTy (.Tuple []) = .ok [] := rfl

theorem Type_decode_mrUninhabitedZstTy :
    Interp.Type.decode mrUninhabitedZstTy [] = .ok none := rfl

/-- Decoding any `sz`-byte buffer `bytes` (including `.Uninit` padding or
uninitialized bytes) at `mrUnionTy fields sz al` succeeds and wraps `bytes` in
`Value.Union [bytes]`. -/
theorem Type_decode_mrUnionTy (fields : List (Gen.Offset × Gen.«Type»)) (sz al : Nat)
    {bytes : List Byte} (hlen : bytes.length = sz) :
    Interp.Type.decode (mrUnionTy fields sz al) bytes = .ok (some (.Union [bytes])) := by
  subst hlen
  simp [mrUnionTy, Interp.Type.decode, subsliceWithLength, pure, Except.pure, bind, Except.bind]

/-- `checkValue` accepts `Value.Union [bytes]` at `mrUnionTy fields sz al`
whenever `bytes.length = sz`, regardless of whether `bytes` contains `.Uninit`. -/
theorem checkValue_mrUnionTy (fields : List (Gen.Offset × Gen.«Type»)) (sz al : Nat)
    {bytes : List Byte} (hlen : bytes.length = sz) (m : Option Mach := none) :
    Interp.checkValue (.Union [bytes]) (mrUnionTy fields sz al) m = .ok () := by
  subst hlen
  unfold mrUnionTy Interp.checkValue Interp.checkUnionChunks Interp.ensureElseUb
  simp [pure, Except.pure, bind, Except.bind]
  rfl

/-- Encoding `Value.Union [bytes]` at `mrUnionTy fields sz al` when
`bytes.length = sz` reproduces `bytes` exactly (preserving all `.Init` and
`.Uninit` bytes). -/
theorem Type_encode_mrUnionTy (fields : List (Gen.Offset × Gen.«Type»)) (sz al : Nat)
    {bytes : List Byte} (hlen : bytes.length = sz) :
    Interp.Type.encode (mrUnionTy fields sz al) (.Union [bytes]) = .ok bytes := by
  subst hlen
  simp [mrUnionTy, Interp.Type.encode, Interp.Type.encodeUnionChunks, writeSubsliceAtIndex,
    List.drop_replicate, pure, Except.pure, bind, Except.bind]

/-- Byte-level correspondence between an Anneal union `Value` (`annealVal`,
whose `encodeByLayoutIdxAux` image is `abBytes`) and MiniRust's allocation bytes
`mrBytes` (`mrBytes.length = S`): every byte `k < S` is `.uninit` in Anneal iff
it is `.Uninit` in MiniRust, and `.init b none` in Anneal iff `.Init b none` in
MiniRust. -/
def annealByteToMiniRust : MirSemantics.AbstractByte → Option Byte
  | .uninit => some .Uninit
  | .init b none => some (.Init b none)
  | .init _ (some _) => none

def MiniRustUnionBytesRel (layouts : Layout.LayoutTable) (uTy : MirAst.Ty) (S : Nat)
    (annealVal : MirSemantics.Value) (mrBytes : List Byte) : Prop :=
  mrBytes.length = S ∧
  ∃ abBytes,
    MirSemantics.encodeByLayoutIdxAux 8 layouts uTy.layoutIdx annealVal = some abBytes ∧
    abBytes.length = S ∧
    abBytes.mapM annealByteToMiniRust = some mrBytes

/-- Whole-union `typedLoad` followed by `typedStore` on `mrUnionTy fields S al`
preserves any `MiniRustUnionBytesRel`-related byte buffer `mrBytes` (including
uninitialized padding bytes). -/
theorem mrUnionTy_roundtrip_preserves_bytesRel
    {layouts : Layout.LayoutTable} {uTy : MirAst.Ty} {S al : Nat}
    {fields : List (Gen.Offset × Gen.«Type»)}
    {annealVal : MirSemantics.Value} {mrBytes : List Byte}
    (hrel : MiniRustUnionBytesRel layouts uTy S annealVal mrBytes)
    (m : Option Mach := none) :
    Interp.Type.decode (mrUnionTy fields S al) mrBytes = .ok (some (.Union [mrBytes])) ∧
    Interp.checkValue (.Union [mrBytes]) (mrUnionTy fields S al) m = .ok () ∧
    Interp.Type.encode (mrUnionTy fields S al) (.Union [mrBytes]) = .ok mrBytes ∧
    MiniRustUnionBytesRel layouts uTy S annealVal mrBytes :=
  ⟨Type_decode_mrUnionTy fields S al hrel.1,
   checkValue_mrUnionTy fields S al hrel.1 m,
   Type_encode_mrUnionTy fields S al hrel.1,
   hrel⟩

/-- Transmuting `Value.Union [mrBytes]` from `mrMaybeUninitTy (.Int it) it.size.bytes al`
(or any `mrUnionTy fields it.size.bytes al`) to `.Int it` (`MaybeUninit<T>::assume_init`
via `CastOp.Transmute`):
1. When `mrBytes = scalarBytes it bits` (`bits < 2 ^ (8 * it.size.bytes)`),
   `transmute` succeeds with `.ok (.Int (intFromBits bits it))`;
2. When `mrBytes` has length `it.size.bytes` and contains `.Uninit` (e.g.
   `uninitBytes it` for `MaybeUninit::uninit()` when `0 < it.size.bytes`),
   `transmute` fails with `.error (.ub "transmuted value is not valid at new type")`. -/
theorem transmute_mrUnionTy_to_int_spec
    (fields : List (Gen.Offset × Gen.«Type»)) (it : Gen.IntType) (al : Nat)
    (hgood : GoodSize it.size.bytes) (m : Option Mach := none) :
    (∀ bits, bits < 2 ^ (8 * it.size.bytes) →
      Interp.transmute (.Union [scalarBytes it bits])
        (mrUnionTy fields it.size.bytes al) (.Int it) m =
        .ok (.Int (intFromBits bits it))) ∧
    (Interp.transmute (.Union [uninitBytes it])
        (mrUnionTy fields it.size.bytes al) (.Int it) m =
        .error (.ub "transmuted value is not valid at new type")) := by
  have hlay := layout_eq it hgood
  refine ⟨fun bits hbits => ?_, ?_⟩
  · have hlen : (scalarBytes it bits).length = it.size.bytes := scalarBytes_length it bits
    have henc := Type_encode_mrUnionTy fields it.size.bytes al hlen
    have hdec := decode_int_scalarBytes it bits hbits
    have hchk := checkValue_int (m? := m) (canRepresent_intFromBits it bits hgood hbits)
    simp [Interp.transmute, Type_layout_mrUnionTy, hlay, LayoutStrategy.expect_size,
      henc, hdec, hchk, pure, Except.pure, bind, Except.bind]
  · have hlen : (uninitBytes it).length = it.size.bytes := by simp [uninitBytes]
    have henc := Type_encode_mrUnionTy fields it.size.bytes al hlen
    have hdec := decode_int_uninitBytes it hgood
    simp [Interp.transmute, Type_layout_mrUnionTy, hlay, LayoutStrategy.expect_size,
      henc, hdec, ub, pure, Except.pure, bind, Except.bind]

/-! ### Union field projections and loads at the union's field types -/

theorem mapM_const_ok {α β : Type} (b : β) :
    ∀ l : List α, List.mapM (fun _ => (Except.ok b : Interp β)) l = .ok (List.replicate l.length b)
  | [] => rfl
  | _ :: l => by
    simp [List.mapM_cons, mapM_const_ok b l, List.replicate_succ, bind, Except.bind, pure, Except.pure]

theorem tryMapM_replicate_ok {α β : Type} (f : α → Interp (Option β)) (a : α) (b : β)
    (hf : f a = .ok (some b)) :
    ∀ n, tryMapM f (List.replicate n a) = .ok (some (List.replicate n b))
  | 0 => rfl
  | n + 1 => by
    simp [tryMapM, List.replicate_succ, hf, tryMapM_replicate_ok f a b hf n, bind, Except.bind,
      pure, Except.pure]

theorem forM_replicate_ok {α : Type} (f : α → Interp Unit) (a : α) (hf : f a = .ok ()) :
    ∀ n, forM (List.replicate n a) f = .ok ()
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.forM_cons, hf]
    exact forM_replicate_ok f a hf n

/-- `[(); N]` decodes from zero bytes to `N` unit values. -/
theorem Type_decode_mrZstArrayTy (N : Nat) :
    Interp.Type.decode (mrZstArrayTy N) [] = .ok (some (.Tuple (List.replicate N (.Tuple [])))) := by
  have h0 : subsliceWithLength ([] : List Byte) 0 0 = .ok [] := rfl
  have ht := tryMapM_replicate_ok (Interp.Type.decode mrUnitTy) [] (.Tuple []) Type_decode_mrUnitTy N
  simp only [mrZstArrayTy, Interp.Type.decode, Type_layout_mrUnitTy]
  simp [LayoutStrategy.expect_size, Size.mulInt, Size.from_bytes, h0, mapM_const_ok, bind,
    Except.bind, pure, Except.pure]
  rw [ht]
  rfl

theorem checkValue_mrZstArrayTy (N : Nat) (m : Option Mach := none) :
    Interp.checkValue (.Tuple (List.replicate N (.Tuple []))) (mrZstArrayTy N) m = .ok () := by
  have hf := forM_replicate_ok (fun val => Interp.checkValue val mrUnitTy m) (Gen.Value.Tuple [])
    (checkValue_mrUnitTy m) N
  simp [mrZstArrayTy, Interp.checkValue, ensureElseUb, hf, bind, Except.bind, pure, Except.pure]

/-- A load at `()` from any aligned place reads no allocation: it succeeds
with `()` and only appends the zero-length access to the access log, whatever
the bytes behind the place are. -/
theorem placeLoad_mrUnitTy (m : Mach) (place : Gen.Place BM) (haligned : place.aligned = true) :
    placeLoad m place mrUnitTy =
      .ok (.Tuple [], { m with mem := { m.mem with accesses :=
        m.mem.accesses ++ [⟨.Load, .None, place.ptr.thin_pointer.addr, ⟨0⟩⟩] } }) := by
  simp [placeLoad, haligned, typedLoad, Type_layout_mrUnitTy, LayoutStrategy.expect_size, CM.load,
    BM.load, Align.is_aligned, BM.check_ptr, Type_decode_mrUnitTy,
    checkValue_mrUnitTy, bind, Except.bind, pure, Except.pure]

/-- A load at `[(); N]` from any aligned place reads no allocation
(`kani#5176`): it succeeds with `N` unit values whatever the bytes behind the
place are, all-`.Uninit` union storage included. -/
theorem placeLoad_mrZstArrayTy (N : Nat) (m : Mach) (place : Gen.Place BM)
    (haligned : place.aligned = true) :
    placeLoad m place (mrZstArrayTy N) =
      .ok (.Tuple (List.replicate N (.Tuple [])), { m with mem := { m.mem with accesses :=
        m.mem.accesses ++ [⟨.Load, .None, place.ptr.thin_pointer.addr, ⟨0⟩⟩] } }) := by
  simp [placeLoad, haligned, typedLoad, Type_layout_mrZstArrayTy, LayoutStrategy.expect_size, CM.load,
    BM.load, Align.is_aligned, BM.check_ptr, Type_decode_mrZstArrayTy,
    checkValue_mrZstArrayTy, bind, Except.bind, pure, Except.pure]

/-- A load at an uninhabited 0-byte type from any aligned place is UB
(`kani#5159`), whatever the bytes behind the place are: zero bytes never decode
at an enum without variants. -/
theorem placeLoad_mrUninhabitedZstTy (m : Mach) (place : Gen.Place BM)
    (haligned : place.aligned = true) :
    placeLoad m place mrUninhabitedZstTy =
      .error (.ub "load at type but the data in memory violates the language invariant") := by
  simp [placeLoad, haligned, typedLoad, mrUninhabitedZstTy, Interp.Type.layout,
    LayoutStrategy.expect_size, CM.load, BM.load, Align.is_aligned, BM.check_ptr, bind,
    Except.bind, pure, Except.pure, ub]
  rfl

theorem mapM_data_none_of_uninit {bytes : List Byte} (hu : Gen.AbstractByte.Uninit ∈ bytes) :
    bytes.mapM AbstractByte.data = none := by
  induction bytes with
  | nil => simp at hu
  | cons b bs ih =>
    rcases List.mem_cons.mp hu with h | h
    · subst h; simp [List.mapM_cons, AbstractByte.data]
    · cases hb : AbstractByte.data b <;> simp [List.mapM_cons, hb, ih h]

/-- Bytes containing an `.Uninit` byte do not decode at an integer type, so a
load of an integer union field that covers an uninitialized byte is UB
(`typedLoad`'s `none` arm). -/
theorem Type_decode_int_of_uninit (it : Gen.IntType) {bytes : List Byte}
    (hlen : bytes.length = it.size.bytes) (hu : Gen.AbstractByte.Uninit ∈ bytes) :
    Interp.Type.decode (.Int it) bytes = .ok none := by
  obtain ⟨signed, size⟩ := it
  simp [Interp.Type.decode, Type.decodeInt, hlen, mapM_data_none_of_uninit hu, pure, Except.pure]

/-- Projecting field `j` of a single-chunk union whose field `j` sits at offset
`0` keeps the union's thin pointer and alignment flag, and reads no byte of the
union: MiniRust's `eval_place` for `PlaceExpr::Field` on `Type::Union` is
`fields[field]` plus an in-bounds offset of `0`. -/
theorem evalPlace_field_mrUnionTy {m m' : Mach} {root : Gen.PlaceExpr} {rootPlace : Gen.Place BM}
    {fields : List (Gen.Offset × Gen.«Type»)} {S al : Nat} {j : Nat} {fty : Gen.«Type»}
    {fsz : Size} {fal : Align}
    (hroot : evalPlace m root = .ok ((rootPlace, mrUnionTy fields S al), m'))
    (hfield : fields[j]? = some (⟨0⟩, fty))
    (hsized : Interp.Type.layout fty = .ok (.Sized fsz fal))
    (hmeta : rootPlace.ptr.metadata = none)
    (haddr0 : 0 ≤ rootPlace.ptr.thin_pointer.addr)
    (haddrMax : rootPlace.ptr.thin_pointer.addr < 2 ^ 64) :
    evalPlace m (.Field root (j : Int)) =
      .ok (({ rootPlace with ptr := ThinPointer.widen rootPlace.ptr.thin_pointer none }, fty), m') := by
  have hidx : listIndex fields (j : Int) "fields[field]" = .ok (⟨0⟩, fty) := by
    simp [listIndex, hfield]
  have hlay : Interp.Type.layout (.Union fields [(⟨0⟩, ⟨S⟩)] ⟨S⟩ ⟨al⟩) = .ok (.Sized ⟨S⟩ ⟨al⟩) := rfl
  simp [evalPlace, hroot, mrUnionTy, hidx, hlay, computeSize, hmeta,
    ptrOffsetInbounds_zero m' _ haddr0 haddrMax, hsized, LayoutStrategy.is_sized, bind,
    Except.bind, pure, Except.pure]

/-! ### Union Local Storage Relation, Two-Sided Step Simulation, and Computed Translation (`G2`) -/

/-- A 0-byte store at `mrUnitTy` to an aligned place succeeds and leaves all
allocations unchanged. -/
theorem placeStore_mrUnitTy (m : Mach) (place : Gen.Place BM) (haligned : place.aligned = true) :
    placeStore m place (.Tuple []) mrUnitTy =
      .ok { m with mem := { m.mem with accesses :=
        m.mem.accesses ++ [⟨.Store, .None, place.ptr.thin_pointer.addr, ⟨0⟩⟩] } } := by
  simp [placeStore, haligned, typedStore, checkValue_mrUnitTy,
    Type_encode_mrUnitTy, CM.store, BM.store, Align.is_aligned, BM.check_ptr,
    bind, Except.bind, pure, Except.pure]

private theorem mapM_replicate_ok_local {α β : Type} (f : α → Interp β) (a : α) (b : β)
    (hf : f a = .ok b) :
    ∀ n, List.mapM f (List.replicate n a) = .ok (List.replicate n b)
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.mapM_cons, hf, mapM_replicate_ok_local f a b hf n]
    rfl

private theorem replicate_nil_flatten : ∀ n : Nat, (List.replicate n ([] : List Byte)).flatten = []
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, List.flatten_cons, List.nil_append, replicate_nil_flatten n]

theorem Type_encode_mrZstArrayTy (N : Nat) :
    Interp.Type.encode (mrZstArrayTy N) (.Tuple (List.replicate N (.Tuple []))) = .ok [] := by
  simp only [mrZstArrayTy, Interp.Type.encode, List.length_replicate, ne_eq, not_true_eq_false, ↓reduceIte]
  let f := fun value : Gen.Value BM => do
    let bytes ← Interp.Type.encode mrUnitTy value
    let elemLayout ← Interp.Type.layout mrUnitTy
    let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array element is sized"
    if bytes.length ≠ elemSize.bytes then specPanic "encode: Type::Array element byte length mismatch"
    else pure bytes
  have hm : List.mapM f (List.replicate N (.Tuple [])) = .ok (List.replicate N ([] : List Byte)) :=
    mapM_replicate_ok_local f (.Tuple []) [] rfl N
  change (do let encoded ← List.mapM f (List.replicate N (.Tuple [])); pure encoded.flatten) = .ok []
  rw [hm]
  simp [replicate_nil_flatten N, bind, Except.bind, pure, Except.pure]

/-- A 0-byte store at `mrZstArrayTy N` (`[(); N]`) to an aligned place succeeds
and leaves all allocations (including any union payload and `.Uninit` padding
bytes behind `place`) unchanged. -/
theorem placeStore_mrZstArrayTy (N : Nat) (m : Mach) (place : Gen.Place BM)
    (haligned : place.aligned = true) :
    placeStore m place (.Tuple (List.replicate N (.Tuple []))) (mrZstArrayTy N) =
      .ok { m with mem := { m.mem with accesses :=
        m.mem.accesses ++ [⟨.Store, .None, place.ptr.thin_pointer.addr, ⟨0⟩⟩] } } := by
  simp [placeStore, haligned, typedStore, checkValue_mrZstArrayTy,
    Type_encode_mrZstArrayTy, CM.store, BM.store, Align.is_aligned, BM.check_ptr,
    bind, Except.bind, pure, Except.pure]

/-- Loading `localPtr ctx u` at `mrUnionTy fields S al` on a `Shape` machine
whose allocation `L[u]` holds `mrBytes` (`mrBytes.length = S`, `0 < S`) succeeds
with `.ok (.Union [mrBytes], m')` and preserves `Shape`, even when `mrBytes`
contains `.Uninit` bytes. -/
theorem typedLoad_local_mrUnionTy {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L))
    (u : Nat) (fields : List (Gen.Offset × Gen.«Type»)) (S al : Nat)
    (hpos : 0 < S) {mrBytes : List Byte} (hlen : mrBytes.length = S)
    (hL : L[u]? = some (localAlloc ctx u ⟨.Unsigned, ⟨al⟩⟩ mrBytes))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD u 0) = true) :
    ∃ m', typedLoad m (localPtr ctx u) (mrUnionTy fields S al) align .None =
        .ok (.Union [mrBytes], m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  obtain ⟨hu, hLu⟩ := List.getElem?_eq_some_iff.mp hL
  have hset := set_self_of_getElem? L u _ hL
  have htk : mrBytes.take S = mrBytes := List.take_of_length_le (by omega)
  have hcm : CM.load m.mem (localPtr ctx u) ⟨S⟩ align .None =
      .ok (mrBytes, (withMem m (ctx.base ++ L) ⟨.Load, .None, ctx.addrs.getD u 0, ⟨S⟩⟩).mem) := by
    simp only [CM.load, BM.load, hal, BM.check_ptr, localPtr, listIndex, h.allocs]
    simp [Nat.ne_of_gt hpos, hu, hLu, Allocation.size, hlen, listSet, subsliceWithLength,
      hset, htk, withMem]
  refine ⟨withMem m (ctx.base ++ L) ⟨.Load, .None, ctx.addrs.getD u 0, ⟨S⟩⟩, ?_, withMem_shape h _⟩
  exact typedLoad_of_ok (Type_layout_mrUnionTy fields S al) hcm
    (Type_decode_mrUnionTy fields S al hlen) (checkValue_mrUnionTy fields S al hlen _)

/-- Storing `.Union [mrBytes]` at `mrUnionTy fields S al` into `localPtr ctx w`
on a `Shape` machine whose allocation `L[w]` has length `S` (`0 < S`) writes
`mrBytes` (including any `.Uninit` bytes) into `L[w]` and preserves `Shape`. -/
theorem typedStore_local_mrUnionTy {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L))
    (w : Nat) (fields : List (Gen.Offset × Gen.«Type»)) (S al : Nat)
    (hpos : 0 < S) {oldData mrBytes : List Byte}
    (hold : oldData.length = S) (hlen : mrBytes.length = S)
    (hL : L[w]? = some (localAlloc ctx w ⟨.Unsigned, ⟨al⟩⟩ oldData))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD w 0) = true) :
    typedStore m (localPtr ctx w) (.Union [mrBytes]) (mrUnionTy fields S al) align .None =
      .ok (withMem m (ctx.base ++ L.set w (localAlloc ctx w ⟨.Unsigned, ⟨al⟩⟩ mrBytes))
            ⟨.Store, .None, ctx.addrs.getD w 0, ⟨S⟩⟩) := by
  obtain ⟨hw, hLw⟩ := List.getElem?_eq_some_iff.mp hL
  have hck := checkValue_mrUnionTy fields S al hlen (some m)
  have henc := Type_encode_mrUnionTy fields S al hlen
  have hne : mrBytes ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hdrop : oldData.drop S = [] := List.drop_eq_nil_of_le (by omega)
  simp only [typedStore, hck, henc, CM.store, BM.store, hal, BM.check_ptr, localPtr,
    listIndex, h.allocs]
  simp [hne, hw, hLw, localAlloc, stackAlloc, Allocation.size, hold, hlen,
    writeSubsliceAtIndex, listSet, withMem, hdrop]

/-- Local storage invariant tying an Anneal union local `u` (`slot`) to its
MiniRust allocation `L[u]` on `Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] (ctx.base ++ L)`:
* `f.locals` maps `localName u` to `mrUnionTy fields S al` (`0 < S`);
* `lm` maps `localName u` to `localPtr ctx u` with aligned in-bounds address;
* `L[u]` is `localAlloc ctx u ⟨.Unsigned, ⟨al⟩⟩ mrBytes` (`mrBytes.length = S`),
  where `mrBytes = List.replicate S .Uninit` when `slot = .uninit`, and
  `MiniRustUnionBytesRel layouts uTy S val mrBytes` when `slot = .init val`. -/
structure MiniRustUnionLocalStorage (ctx : Ctx) (L : List Gen.Allocation)
    (f : Gen.Function) (lm : Map Gen.LocalName Ptr) (layouts : Layout.LayoutTable)
    (u : Nat) (uTy : MirAst.Ty) (fields : List (Gen.Offset × Gen.«Type»))
    (S al : Nat) (slot : LocalSlot) (mrBytes : List Byte) : Prop where
  pos_size : 0 < S
  align_ok : Align.is_aligned ⟨al⟩ (ctx.addrs.getD u 0) = true
  addr_nonneg : 0 ≤ ctx.addrs.getD u 0
  addr_lt : ctx.addrs.getD u 0 + (S : Int) < 2 ^ 64
  fn_local : mapGet f.locals (localName u) = some (mrUnionTy fields S al)
  lm_ptr : mapGet lm (localName u) = some (localPtr ctx u)
  bytes_len : mrBytes.length = S
  alloc_eq : L[u]? = some (localAlloc ctx u ⟨.Unsigned, ⟨al⟩⟩ mrBytes)
  slot_rel :
    match slot with
    | .uninit => mrBytes = List.replicate S .Uninit
    | .init val => MiniRustUnionBytesRel layouts uTy S val mrBytes
    | .dead => False

/-- **Two-sided whole-union copy simulation (`G2`)**:
Given a `Shape` state where union local `u` holds `.init val` with bytes
`mrBytes` (`MiniRustUnionLocalStorage ... (.init val) mrBytes`, including any
`.Uninit` padding bytes) and union local `w` has `MiniRustUnionLocalStorage ... wSlot oldBytes`:
1. In Anneal (`s.memory.borrows = []`, `s.memory.activeProtectors = []`,
   `s.memory.callerLocals = []`), `evalStmt s ⟨.assign ⟨w, []⟩ (.use (.copy ⟨u, []⟩)), span⟩`
   steps to `advanceStmt s (s.frame.locals.set w (.init val)) s.memory`;
2. In MiniRust, `evalStatement (resetPick m) (.Assign (.Local (localName w)) (.Load (.Local (localName u))))`
   and `Interp.step m` step to `m'`, copying `mrBytes` into `L[w]` and
   establishing `MiniRustUnionLocalStorage ctx (L.set w (localAlloc ctx w ⟨.Unsigned, ⟨al⟩⟩ mrBytes)) f lm body.layouts w uTy fields S al (.init val) mrBytes`! -/
theorem step_union_whole_copy_minirust_simulation
    {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {lm : Map Gen.LocalName Ptr} {L : List Gen.Allocation}
    {s : MachineState} {m : Mach} {tb : Gen.BasicBlock}
    {u w : Nat} {uTy : MirAst.Ty} {fields : List (Gen.Offset × Gen.«Type»)}
    {S al : Nat} {val : MirSemantics.Value} {wSlot : LocalSlot}
    {mrBytes oldBytes : List Byte} {span : String}
    (hsh : Shape m ctx [ctx.caller, calleeFrameL f ctx lm s.frame.blockIdx s.frame.stmtIdx]
      (ctx.base ++ L))
    (hu : MiniRustUnionLocalStorage ctx L f lm body.layouts u uTy fields S al (.init val) mrBytes)
    (hw : MiniRustUnionLocalStorage ctx L f lm body.layouts w uTy fields S al wSlot oldBytes)
    (hu_slot : s.frame.locals[u]? = some (.init val))
    (hw_live : s.frame.locals[w]? = some wSlot)
    (hw_not_dead : wSlot ≠ .dead)
    (hbor : s.memory.borrows = [])
    (hprot : s.memory.activeProtectors = [])
    (_hcaller : s.memory.callerLocals = [])
    (htb : mapGet f.blocks (bbName s.frame.blockIdx) = some tb)
    (hlt_tb : s.frame.stmtIdx < tb.statements.length)
    (htst : tb.statements[s.frame.stmtIdx]? =
      some (.Assign (.Local (localName w)) (.Load (.Local (localName u)))))
    (hval : MirSemantics.validateLoadedValue body.layouts body.localDecls (.copy ⟨u, []⟩) val = true := by decide)
    (hnoUninit : MirSemantics.valueContainsUninit val = false := by decide) :
    evalStmt s ⟨.assign ⟨w, []⟩ (.use (.copy ⟨u, []⟩)), span⟩ body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (s.frame.locals.set w (.init val)) s.memory) ∧
    ∃ m',
      Interp.step m = .ok m' ∧
      Shape m' ctx [ctx.caller, calleeFrameL f ctx lm s.frame.blockIdx (s.frame.stmtIdx + 1)]
        (ctx.base ++ L.set w (localAlloc ctx w ⟨.Unsigned, ⟨al⟩⟩ mrBytes)) ∧
      MiniRustUnionLocalStorage ctx
        (L.set w (localAlloc ctx w ⟨.Unsigned, ⟨al⟩⟩ mrBytes))
        f lm body.layouts w uTy fields S al (.init val) mrBytes := by
  have hw_lt_af : w < s.frame.locals.length := (List.getElem?_eq_some_iff.mp hw_live).1
  have hA : evalStmt s ⟨.assign ⟨w, []⟩ (.use (.copy ⟨u, []⟩)), span⟩
      body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (s.frame.locals.set w (.init val)) s.memory) := by
    have hop : evalOperand s.frame.locals (.copy ⟨u, []⟩) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
        .ok val s.frame.locals := by
      simp [evalOperand, get?, hu_slot, readProjectedValue, hnoUninit]
    have hrv := evalRvalue_use_ok hop hval rfl
    have hinv : MirSemantics.invalidateConflictingBorrows s.memory.borrows w .none
        s.memory.callStack.length = s.memory.borrows := by
      rw [hbor]; rfl
    simp only [evalStmt, hrv, get?, hw_live, set?, Trusted.Sequence.length, hw_lt_af, ↓reduceIte, hprot, hinv]
    cases wSlot with
    | dead => exact absurd rfl hw_not_dead
    | uninit | init _ =>
      rw [memory_mk_nil_prot s.memory hprot]
  have hsh0 := resetPick_shape hsh
  have hpl_w := evalPlace_local_some hsh0 w (mrUnionTy fields S al) hw.fn_local
    (localPtr ctx w) hw.lm_ptr
  have hpl_u := evalPlace_local_some hsh0 u (mrUnionTy fields S al) hu.fn_local
    (localPtr ctx u) hu.lm_ptr
  obtain ⟨m1, hload, hsh1⟩ := typedLoad_local_mrUnionTy hsh0 u fields S al
    hu.pos_size hu.bytes_len hu.alloc_eq ⟨1⟩ (by simp [Align.is_aligned])
  have hev_u : evalValue (resetPick m) (.Load (.Local (localName u))) =
      .ok ((.Union [mrBytes], mrUnionTy fields S al), m1) := by
    simp [evalValue, hpl_u, placeLoad, hload, bind, Except.bind, pure, Except.pure]
  have hstore := typedStore_local_mrUnionTy hsh1 w fields S al
    hw.pos_size hw.bytes_len hu.bytes_len hw.alloc_eq ⟨1⟩ (by simp [Align.is_aligned])
  let m2 := withMem m1 (ctx.base ++ L.set w (localAlloc ctx w ⟨.Unsigned, ⟨al⟩⟩ mrBytes))
    ⟨.Store, .None, ctx.addrs.getD w 0, ⟨S⟩⟩
  have hsh2 : Shape m2 ctx [ctx.caller, calleeFrameL f ctx lm s.frame.blockIdx s.frame.stmtIdx]
      (ctx.base ++ L.set w (localAlloc ctx w ⟨.Unsigned, ⟨al⟩⟩ mrBytes)) :=
    withMem_shape hsh1 _
  have hev_st : evalStatement (resetPick m)
      (.Assign (.Local (localName w)) (.Load (.Local (localName u)))) = .ok m2 := by
    simp [evalStatement, hpl_w, hev_u, placeStore, hstore, bind, Except.bind, m2]
  obtain ⟨m3, hm3, hsh3⟩ := bumpStmt_callee hsh2
  have hne : ((s.frame.stmtIdx : Nat) : Int) ≠ (tb.statements.length : Int) := by omega
  have hstepM : Interp.step m = .ok m3 := by
    rw [step_callee hsh tb htb]
    simp [hne, listIndex_nat _ _ _ htst, hev_st, hm3, check_after hsh3]
  have hw_lt_L : w < L.length := (List.getElem?_eq_some_iff.mp hw.alloc_eq).1
  refine ⟨hA, m3, hstepM, hsh3, {
    pos_size := hw.pos_size
    align_ok := hw.align_ok
    addr_nonneg := hw.addr_nonneg
    addr_lt := hw.addr_lt
    fn_local := hw.fn_local
    lm_ptr := hw.lm_ptr
    bytes_len := hu.bytes_len
    alloc_eq := List.getElem?_set_self hw_lt_L
    slot_rel := hu.slot_rel }⟩

/-- **MiniRust side of a 0-byte `[(); N]` union field read (`G2`, `kani#5176`)**:
On a `Shape` state where union local `u` satisfies `MiniRustUnionLocalStorage`
(whether `.uninit` or `.init val` with uninitialized padding bytes) and field
`j` of `mrUnionTy fields S al` is `mrZstArrayTy N`, the read succeeds. This
lemma has no Anneal side. Anneal agrees for an `.init` union, but it faults on
a field read of an `.uninit` union local, which MiniRust (and rustc's
interpreter, which reads zero bytes) accepts. Here:
`evalValue m (.Load (.Field (.Local (localName u)) (j : Int)))` succeeds with
`(.Tuple (List.replicate N (.Tuple [])), mrZstArrayTy N)` and leaves all
allocations unchanged. -/
theorem evalValue_load_union_zstArray_field
    {m : Mach} {ctx : Ctx} {f : Gen.Function} {lm : Map Gen.LocalName Ptr}
    {L : List Gen.Allocation} {layouts : Layout.LayoutTable}
    {blk stmt u j N : Nat} {uTy : MirAst.Ty}
    {fields : List (Gen.Offset × Gen.«Type»)} {S al : Nat}
    {slot : LocalSlot} {mrBytes : List Byte}
    (hsh : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] (ctx.base ++ L))
    (hu : MiniRustUnionLocalStorage ctx L f lm layouts u uTy fields S al slot mrBytes)
    (hfld : fields[j]? = some (⟨0⟩, mrZstArrayTy N)) :
    ∃ m',
      evalValue m (.Load (.Field (.Local (localName u)) (j : Int))) =
        .ok ((.Tuple (List.replicate N (.Tuple [])), mrZstArrayTy N), m') ∧
      Shape m' ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] (ctx.base ++ L) := by
  have hroot := evalPlace_local_some hsh u (mrUnionTy fields S al) hu.fn_local
    (localPtr ctx u) hu.lm_ptr
  have haddrMax : (localPtr ctx u).addr < 2 ^ 64 := by
    change ctx.addrs.getD u 0 < 2 ^ 64
    have h1 := hu.pos_size; have h2 := hu.addr_lt; omega
  have hfp := evalPlace_field_mrUnionTy hroot hfld (Type_layout_mrZstArrayTy N)
    rfl hu.addr_nonneg haddrMax
  have hload := placeLoad_mrZstArrayTy N m
    { ptr := ThinPointer.widen (localPtr ctx u) none, aligned := true } rfl
  let m' : Mach := { m with mem := { m.mem with accesses :=
    m.mem.accesses ++ [⟨.Load, .None, (ThinPointer.widen (localPtr ctx u) none).thin_pointer.addr, ⟨0⟩⟩] } }
  refine ⟨m', ?_, ⟨hsh.threads, hsh.active, hsh.allocs⟩⟩
  simp [evalValue, hfp, hload, bind, Except.bind, pure, Except.pure, m']

/-- **MiniRust side of an uninhabited 0-byte union field read (`G2`,
`kani#5159`)**: On a `Shape` state where union local `u` satisfies
`MiniRustUnionLocalStorage` and field `j` is `mrUninhabitedZstTy`, the read is
UB. This lemma has no Anneal side:
`evalValue m (.Load (.Field (.Local (localName u)) (j : Int)))` fails with
`.error (.ub "load at type but the data in memory violates the language invariant")`,
even when all `S` bytes of `mrBytes` are initialized! -/
theorem evalValue_load_union_uninhabited_ub
    {m : Mach} {ctx : Ctx} {f : Gen.Function} {lm : Map Gen.LocalName Ptr}
    {L : List Gen.Allocation} {layouts : Layout.LayoutTable}
    {blk stmt u j : Nat} {uTy : MirAst.Ty}
    {fields : List (Gen.Offset × Gen.«Type»)} {S al : Nat}
    {slot : LocalSlot} {mrBytes : List Byte}
    (hsh : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] (ctx.base ++ L))
    (hu : MiniRustUnionLocalStorage ctx L f lm layouts u uTy fields S al slot mrBytes)
    (hfld : fields[j]? = some (⟨0⟩, mrUninhabitedZstTy)) :
    evalValue m (.Load (.Field (.Local (localName u)) (j : Int))) =
      .error (.ub "load at type but the data in memory violates the language invariant") := by
  have hroot := evalPlace_local_some hsh u (mrUnionTy fields S al) hu.fn_local
    (localPtr ctx u) hu.lm_ptr
  have haddrMax : (localPtr ctx u).addr < 2 ^ 64 := by
    change ctx.addrs.getD u 0 < 2 ^ 64
    have h1 := hu.pos_size; have h2 := hu.addr_lt; omega
  have hlay : Interp.Type.layout mrUninhabitedZstTy = .ok (.Sized ⟨0⟩ ⟨1⟩) := rfl
  have hfp := evalPlace_field_mrUnionTy hroot hfld hlay rfl hu.addr_nonneg haddrMax
  have hload := placeLoad_mrUninhabitedZstTy m
    { ptr := ThinPointer.widen (localPtr ctx u) none, aligned := true } rfl
  simp [evalValue, hfp, hload, bind, Except.bind]

/-- **MiniRust side of an uninitialized integer union field read (`G2`)**;
this lemma has no Anneal side. On a `Shape` state where union local `u`
satisfies `MiniRustUnionLocalStorage`,
field `j` is `.Int it` (`GoodSize it.size.bytes`, `it.size.bytes ≤ S`), and at
least one byte in `mrBytes.take it.size.bytes` is `.Uninit`:
`evalValue m (.Load (.Field (.Local (localName u)) (j : Int)))` fails with
`.error (.ub "load at type but the data in memory violates the language invariant")`. -/
theorem evalValue_load_union_int_uninit_ub
    {m : Mach} {ctx : Ctx} {f : Gen.Function} {lm : Map Gen.LocalName Ptr}
    {L : List Gen.Allocation} {layouts : Layout.LayoutTable}
    {blk stmt u j : Nat} {uTy : MirAst.Ty}
    {fields : List (Gen.Offset × Gen.«Type»)} {S al : Nat}
    {slot : LocalSlot} {mrBytes : List Byte} {it : Gen.IntType}
    (hsh : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] (ctx.base ++ L))
    (hu : MiniRustUnionLocalStorage ctx L f lm layouts u uTy fields S al slot mrBytes)
    (hfld : fields[j]? = some (⟨0⟩, .Int it))
    (hgood : GoodSize it.size.bytes)
    (hle : it.size.bytes ≤ S)
    (huninit : Gen.AbstractByte.Uninit ∈ mrBytes.take it.size.bytes) :
    evalValue m (.Load (.Field (.Local (localName u)) (j : Int))) =
      .error (.ub "load at type but the data in memory violates the language invariant") := by
  have hpos := hgood.pos
  have hroot := evalPlace_local_some hsh u (mrUnionTy fields S al) hu.fn_local
    (localPtr ctx u) hu.lm_ptr
  have haddrMax : (localPtr ctx u).addr < 2 ^ 64 := by
    change ctx.addrs.getD u 0 < 2 ^ 64
    have h1 := hu.pos_size; have h2 := hu.addr_lt; omega
  have hfp := evalPlace_field_mrUnionTy hroot hfld (layout_eq it hgood) rfl hu.addr_nonneg haddrMax
  obtain ⟨hu_lt, hLu⟩ := List.getElem?_eq_some_iff.mp hu.alloc_eq
  have hlen_take : (mrBytes.take it.size.bytes).length = it.size.bytes := by
    rw [List.length_take, hu.bytes_len, Nat.min_eq_left hle]
  have hdec := Type_decode_int_of_uninit it hlen_take huninit
  have hle_int : (it.size.bytes : Int) ≤ (S : Int) := by omega
  have hnot_lt_int : ¬ ((S : Int) < (it.size.bytes : Int)) := by omega
  simp only [evalValue, hfp, placeLoad, typedLoad, layout_eq it hgood,
    LayoutStrategy.expect_size, CM.load, BM.load, Align.is_aligned, BM.check_ptr,
    ThinPointer.widen, localPtr, listIndex, hsh.allocs, bind, Except.bind, pure, Except.pure]
  simp [Nat.ne_of_gt hpos, hu_lt, hLu, localAlloc, stackAlloc, Allocation.size, hu.bytes_len,
    hle_int, hnot_lt_int, listSet, subsliceWithLength, hdec, ub]

/-! ### Computed Lowering for Union Bodies (`translateFnWithUnions`, `G2`) -/

/-- Translate a MIR `Ty` (including `()`, `[(); N]`, `VoidZst`, `ManuallyDrop<T>`,
and single-chunk `#[repr(C)] union` ADTs) to a MiniRust `Gen.Type`. -/
def translateTyWithUnions (layouts : Layout.LayoutTable) (fuel : Nat) (ty : MirAst.Ty) :
    Option Gen.«Type» :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match translateTy layouts ty with
    | some T => some T
    | none =>
      match ty.kind with
      | .tuple [] => some mrUnitTy
      | .array (.tuple []) n => some (mrZstArrayTy n)
      | .adt _ _ =>
        match layouts.lookup ty.layoutIdx with
        | none => none
        | some tl =>
          if tl.isUninhabited && tl.size.bytes == 0 then
            some mrUninhabitedZstTy
          else
            match tl.fields with
            | .arbitrary [⟨0⟩] [0] =>
              match tl.fieldLayouts with
              | [flIdx] => do
                let inner ← translateLayoutEntryWithUnions layouts fuel' flIdx
                some (mrManuallyDropTy inner tl.size.bytes tl.align.bytes)
              | _ => none
            | .union _ => do
              let fTys ← tl.fieldLayouts.mapM (translateLayoutEntryWithUnions layouts fuel')
              some (mrUnionTy (fTys.map (fun t => (⟨0⟩, t))) tl.size.bytes tl.align.bytes)
            | _ => none
      | _ => none
where
  translateLayoutEntryWithUnions (layouts : Layout.LayoutTable) (fuel : Nat) (idx : Nat) :
      Option Gen.«Type» :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      match layouts.lookup idx with
      | none => none
      | some tl =>
        if tl.isUninhabited && tl.size.bytes == 0 then
          some mrUninhabitedZstTy
        else
          match tl.fields with
          | .primitive =>
            match tl.backendRepr with
            | .scalar (.initialized (.int bits signed) _) =>
              some (.Int ⟨if signed then .Signed else .Unsigned, ⟨bits / 8⟩⟩)
            | _ => none
          | .arbitrary [] [] => some mrUnitTy
          | .arbitrary [⟨0⟩] [0] =>
            match tl.fieldLayouts with
            | [flIdx] => do
              let inner ← translateLayoutEntryWithUnions layouts fuel' flIdx
              some (mrManuallyDropTy inner tl.size.bytes tl.align.bytes)
            | _ => none
          | .array ⟨0⟩ n => some (mrZstArrayTy n)
          | _ => none

def translateLocalsWithUnions (layouts : Layout.LayoutTable) :
    Nat → List LocalDecl → Option (List (Gen.LocalName × Gen.«Type»))
  | _, [] => some []
  | i, d :: ds => do
    let ty ← translateTyWithUnions layouts 4 d.ty
    let rest ← translateLocalsWithUnions layouts (i + 1) ds
    some ((localName i, ty) :: rest)

def translateOperandWithUnions (decls : List LocalDecl) (op : MirAst.Operand) :
    Option Gen.ValueExpr :=
  match op with
  | .copy p | .move p => do
    let pe ← translatePlace decls p
    some (.Load pe)
  | .constant c =>
    match c.val with
    | .zeroSized =>
      match c.ty.kind with
      | .tuple [] => some (.Tuple [] mrUnitTy)
      | _ => translateOperand decls op
    | _ => translateOperand decls op

/-- Lower a MIR statement on union, `ManuallyDrop`, and ZST locals to MiniRust
statements (`ValueExpr::Union` lowered to `Deinit` + field assignment when
`deinitUnionAgg = true`, or field assignment when `deinitUnionAgg = false`). -/
def translateStatementWithUnions (layouts : Layout.LayoutTable) (decls : List LocalDecl)
    (deinitUnionAgg : Bool := true) (st : MirAst.Statement) : Option (List Gen.Statement) :=
  match st.kind with
  | .assign ⟨u, []⟩ (.aggregate (.adt _ 0 (some fIdx)) [op]) => do
    let val ← translateOperandWithUnions decls op
    let assignStmt := Gen.Statement.Assign (.Field (.Local (localName u)) (fIdx : Int)) val
    if deinitUnionAgg then
      some [.Deinit (.Local (localName u)), assignStmt]
    else
      some [assignStmt]
  | .assign dst (.aggregate (.adt _ 0 none) ops) => do
    let pe ← translatePlace decls dst
    let d ← decls[dst.local_]?
    let ty ← translateTyWithUnions layouts 4 d.ty
    let vals ← ops.mapM (translateOperandWithUnions decls)
    some [.Assign pe (.Tuple vals ty)]
  | .assign _ (.repeat (.constant { val := .zeroSized, .. }) _) =>
    -- In `minimize`/MiniRust, a `[(); N]` local allocated by `StorageLive`
    -- already decodes to `N` unit values from `0` bytes (`placeLoad_mrZstArrayTy`),
    -- so initializing a `[(); N]` temporary from `[(); N]` is a zero-byte no-op.
    some []
  | .assign dst (.use op) => do
    let pe ← translatePlace decls dst
    let val ← translateOperandWithUnions decls op
    some [.Assign pe val]
  | .assign dst (.cast .intToInt op targetTy) => do
    let pe ← translatePlace decls dst
    let val ← translateOperandWithUnions decls op
    let it ← intTypeOf targetTy
    some [.Assign pe (.UnOp (.Cast (.IntToInt it)) val)]
  | _ => do
    let st' ← translateStatement decls st layouts
    some [st']

/-- Non-return locals (`1 ≤ i < decls.length`) mentioned in `bb.statements`. -/
def blockMentionedLocals (body : CapturedMir) (bb : BasicBlockData) : List Nat :=
  (List.range body.localDecls.length).filter fun i =>
    decide (body.argCount + 1 ≤ i) &&
    bb.statements.any (fun s => (stmtLocals s).contains i)

def translateBlocksWithUnions (body : CapturedMir) (deinitUnionAgg : Bool := true) :
    Nat → List BasicBlockData → Option (List (Gen.BbName × Gen.BasicBlock))
  | _, [] => some []
  | i, bb :: bbs => do
    let liveLocs := blockMentionedLocals body bb
    let slStmts := liveLocs.map (fun loc => Gen.Statement.StorageLive (localName loc))
    let bodyStmts ← bb.statements.mapM
      (translateStatementWithUnions body.layouts body.localDecls deinitUnionAgg)
    let term ← translateTerminator body.layouts body.localDecls bb.terminator
    let rest ← translateBlocksWithUnions body deinitUnionAgg (i + 1) bbs
    some ((bbName i, ⟨slStmts ++ bodyStmts.flatten, term, .Regular⟩) :: rest)

/-- Whether no block of `body` passes control to another block: every
terminator is `return` or `unreachable`. -/
def blocksAreExits (body : CapturedMir) : Bool :=
  body.basicBlocks.all fun bb =>
    match bb.terminator.kind with
    | .return_ | .unreachable => true
    | _ => false

/-- The witnesses' lowering of a union-bearing body (`G2`).

**Explicit scope disclosure (`blocksAreExits`, exit-only lowering):**
This lowering is NOT `minimize`'s arbitrary-CFG translation:
* It explicitly requires `blocksAreExits body = true` (every basic block must
  terminate in `return` or `unreachable`; any body with intra-function control
  flow such as `goto`/`switchInt`/`assert` returns `none`).
* Each block begins with `StorageLive` of the non-argument locals that its
  statements mention, so that a run can start at any block of a frame in which
  only the return place and the arguments are allocated (`Witness.machine`).
  A `StorageLive` of an already-live local reallocates it uninitialized, so
  this prologue would clobber values flowing across blocks; restricting to
  exit-only bodies (`blocksAreExits`) avoids cross-block prologue clobbering.
* A union aggregate becomes `Deinit` plus a field assignment (only the field
  assignment when `deinitUnionAgg = false`, the negative control), because
  `Interp.evalValue` does not implement `minimize`'s `ValueExpr::Union`.
* `_d = [const (); N]` (`Rvalue::Repeat` of a zero-sized constant), which
  stores no bytes, is dropped. -/
def translateFnWithUnions (body : CapturedMir) (deinitUnionAgg : Bool := true) :
    Option Gen.Function :=
  if blocksAreExits body then do
    let conv ← translateCallConv body.fnAbi.conv
    let locals ← translateLocalsWithUnions body.layouts 0 body.localDecls
    let blocks ← translateBlocksWithUnions body deinitUnionAgg 0 body.basicBlocks
    some {
      locals := ⟨locals⟩
      args := (List.range body.argCount).map (fun k => localName (k + 1))
      ret := localName 0
      calling_convention := conv
      blocks := ⟨blocks⟩
      start := bbName 0
      implicit_writes := true
    }
  else none

/-! ## `TerminatorKind.assert` (`assert cond expected target unwind`)

`minimize` lowers `TerminatorKind::Assert` to a two-way `Switch` on the checked
condition (`tooling/minimize/src/bb.rs` at the pinned commit):
> "rs::TerminatorKind::Assert { cond, expected, target, unwind, .. } => {
>      let mut condition = self.translate_operand(cond, span);
>      ..
>      if !expected {
>          condition = build::not(condition);
>      }
>      // Create panic block in case of `expected != condition`
>      let terminator = self.translate_panic(*unwind, bb);
>      let panic_block_name = self.fresh_bb_name();
>      ..
>      Terminator::Switch {
>          value: build::bool_to_int::<u8>(condition),
>          cases: [(Int::from(1), next_block)].into_iter().collect(),
>          fallback: panic_block_name,
>      }
>  }"
Under `panic = unwind`, `translate_panic` returns
`Terminator::StartUnwind { unwind_payload: build::unit_ptr(), unwind_block }`,
where `unwind_block` comes from `translate_unwind_action`
(`translateUnwindAction`): the cleanup block itself for `Cleanup(bb)`, and a
fresh `Unreachable`, `build::abort()`, or `ResumeUnwind` block for
`Unreachable`, `Terminate`, and `Continue`.

`MiniRustSpec.Interp.evalTerminator` implements neither `StartUnwind` nor
`ResumeUnwind` (both fall into its `unsupported` arm), so the failure edge
cannot run as `minimize` emits it. `translateTerminatorAssert` keeps the
condition (`assertDiscrExpr`) and the success edge, and sends the failure edge
straight to the block that `StartUnwind` would jump to
(`spec/lang/step/terminators.md`: "self.jump_to_block(unwind_block)?"); see
`assertFailTarget`:

* `Cleanup(bb)`: the `Switch` falls back to `bbName bb`.
* `Unreachable` and `Terminate`: the `Switch` falls back to a fresh block with
  `translate_unwind_action`'s terminator (`Unreachable`, `build::abort()`).
* `Continue`: `translate_unwind_action`'s `ResumeUnwind` block would pop the
  frame. The caller of an entry function is `minimize`'s `mk_start_fn`, whose
  unwind block aborts (`mkStartFn`'s `b2`: "If `entry` unwinds, we jump here
  and abort"), so the fresh block holds that `build::abort()`. This case
  therefore models only an entry function (`s.memory.callStack = []` in
  `step_terminator_assert_simulation`).

The model drops one effect of `StartUnwind`, pushing the unwind payload, which
only `ResumeUnwind` and `StopUnwind` read; `Interp` supports neither. MiniRust
requires a `Switch` target to have the kind of the `Switch`'s own block
(`checkNextBlock`), so the fresh blocks are `Regular`, not `Cleanup`;
`Interp.step` never reads a block's kind.
`assertFailTarget_eq_translateUnwindAction` and `assertFailTarget_continue`
state exactly how the model differs from `translateUnwindAction`. -/

/-- The MiniRust `u8` switch discriminant expression for `assert(cond == expected)`:
`boolToU8 v` when `expected = true`, and `boolToU8 (boolNot v)` when
`expected = false`. Evaluates to `1_u8` when `cond == expected`, `0_u8` when
`cond != expected`, and raises UB when `cond` is uninitialized or invalid. -/
def assertDiscrExpr (expected : Bool) (v : Gen.ValueExpr) : Gen.ValueExpr :=
  if expected then boolToU8 v else boolToU8 (boolNot v)

/-- The failure edge of `translateTerminatorAssert` for unwind action `unwind`,
given the next fresh block number `nextFresh`: the `Switch` fallback, the next
fresh block number after the edge, and the fresh blocks (see the section
comment). `minimize` names the `StartUnwind` block after the
`translate_unwind_action` block, and this model skips that name too, so later
fresh blocks keep `minimize`'s names. -/
def assertFailTarget (nextFresh : Nat) :
    UnwindAction → Gen.BbName × Nat × List (Gen.BbName × Gen.BasicBlock)
  | .cleanup cleanupBb => (bbName cleanupBb, nextFresh + 1, [])
  | .unreachable =>
    (bbName nextFresh, nextFresh + 2, [(bbName nextFresh, ⟨[], .Unreachable, .Regular⟩)])
  | .terminate =>
    (bbName nextFresh, nextFresh + 2, [(bbName nextFresh, ⟨[], abortTerminator, .Regular⟩)])
  | .continue_ =>
    (bbName nextFresh, nextFresh + 2, [(bbName nextFresh, ⟨[], abortTerminator, .Regular⟩)])

/-- Outside `Continue`, `assertFailTarget` is `minimize`'s
`translateUnwindAction` with one more fresh number (the skipped `StartUnwind`
block) and its fresh block relabeled `Regular`. -/
theorem assertFailTarget_eq_translateUnwindAction (nextFresh : Nat)
    {unwind : UnwindAction} (hu : unwind ≠ .continue_) :
    assertFailTarget nextFresh unwind =
      ((translateUnwindAction nextFresh unwind).1,
        (translateUnwindAction nextFresh unwind).2.1 + 1,
        (translateUnwindAction nextFresh unwind).2.2.map
          (fun p => (p.1, { p.2 with kind := .Regular }))) := by
  cases unwind with
  | continue_ => exact absurd rfl hu
  | _ => rfl

/-- For `Continue`, `assertFailTarget` uses `translateUnwindAction`'s block name
and fresh number, but its fresh block holds the terminator of `mkStartFn`'s
`Catch` block `b2`, which aborts when the entry function unwinds. -/
theorem assertFailTarget_continue (nextFresh entryIdx : Nat) :
    ∃ b2, mapGet (mkStartFn entryIdx).blocks (bbName 2) = some b2 ∧ b2.kind = .Catch ∧
      assertFailTarget nextFresh .continue_ =
        ((translateUnwindAction nextFresh .continue_).1,
          (translateUnwindAction nextFresh .continue_).2.1 + 1,
          [((translateUnwindAction nextFresh .continue_).1, { b2 with kind := .Regular })]) :=
  ⟨_, rfl, rfl, rfl⟩

/-- `minimize`'s lowering of `TerminatorKind.assert cond expected target unwind`,
with the failure edge modeled by `assertFailTarget` (see the section comment):
the `Switch` on `assertDiscrExpr expected v`, the next fresh block number, and
the fresh blocks, numbered from `nextFresh`. -/
def translateTerminatorAssert (decls : List LocalDecl) (nextFresh : Nat)
    (t : MirAst.Terminator) :
    Option (Gen.Terminator × Nat × List (Gen.BbName × Gen.BasicBlock)) :=
  match t.kind with
  | .assert cond expected target unwind => do
    let v ← translateOperand decls (copyOp cond)
    some (.Switch (assertDiscrExpr expected v) ⟨[(1, bbName target)]⟩
        (assertFailTarget nextFresh unwind).1,
      (assertFailTarget nextFresh unwind).2.1, (assertFailTarget nextFresh unwind).2.2)
  | _ => none

/-- Fragment check for `TerminatorKind.assert`: `cond` is a valid boolean
operand (`operandOkB`), `target < nblocks`, and any `.cleanup cleanupBb` unwind
target satisfies `cleanupBb < nblocks`. -/
def assertTerminatorOk (layouts : Layout.LayoutTable) (decls : List LocalDecl)
    (nblocks : Nat) (t : MirAst.Terminator) : Bool :=
  match t.kind with
  | .assert cond _ target unwind =>
    operandOkB layouts decls (copyOp cond) &&
    decide (target < nblocks) &&
    match unwind with
    | .cleanup cleanupBb => decide (cleanupBb < nblocks)
    | .continue_ | .unreachable | .terminate => true
  | _ => false

theorem assertTerminatorOk_spec {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {nblocks : Nat} {t : MirAst.Terminator}
    {cond : Operand} {expected : Bool} {target : BasicBlockIdx} {unwind : UnwindAction}
    (h : assertTerminatorOk layouts decls nblocks t = true)
    (hk : t.kind = .assert cond expected target unwind) :
    operandOkB layouts decls (copyOp cond) = true ∧
    target < nblocks ∧
    (∀ cleanupBb, unwind = .cleanup cleanupBb → cleanupBb < nblocks) := by
  simp only [assertTerminatorOk, hk, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1, h.1.2, fun cleanupBb hu => ?_⟩
  subst hu
  simpa using h.2

/-- Specification of `assertDiscrExpr expected v` on a `FrameOk` state:
* When `opBits locals (copyOp cond) = some bits`, `bits < 2` (`bits = 0 ∨ bits = 1`),
  and `evalValue m (assertDiscrExpr expected v)` evaluates to
  `(.Int (if (decide (bits = 1) == expected) then 1 else 0), .Int u8Ty)`
  while preserving `FrameOk`;
* When `opBits locals (copyOp cond) = none`, `evalValue m (assertDiscrExpr expected v)`
  raises `Stop.ub`. -/
theorem assert_discr_spec {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    {cond : Operand} (expected : Bool)
    (hdok : operandOkB body.layouts body.localDecls (copyOp cond) = true)
    {v : Gen.ValueExpr} (hv : translateOperand body.localDecls (copyOp cond) = some v) :
    RelOperandOk body.layouts body.localDecls .Bool u8Ty (copyOp cond) ∧
    (∀ bits, opBits locals (copyOp cond) = some bits →
      bits < 2 ∧
      ∃ m', evalValue m (assertDiscrExpr expected v) =
          .ok ((.Int (if (decide (bits = 1) == expected) then 1 else 0), .Int u8Ty), m') ∧
        FrameOk body f ctx locals lm m' blk stmt) ∧
    (opBits locals (copyOp cond) = none →
      ∃ msg, evalValue m (assertDiscrExpr expected v) = .error (.ub msg)) := by
  have hokT := operandOkB_T hdok
  obtain ⟨hsome, hnone⟩ := evalValue_operandT h .bool (copyOp cond) hokT v hv
  refine ⟨.bool (copyOp cond) hdok, fun bits hb => ?_, fun hb => ?_⟩
  · obtain ⟨hbv, m', hm', h'⟩ := hsome bits hb
    have hb2 : bits < 2 := by simpa [ValidBits] using hbv
    have hm_bool : evalValue m v = .ok ((.Bool (decide (bits = 1)), .Bool), m') := by
      simpa [valOf] using hm'
    refine ⟨hb2, m', ?_, h'⟩
    cases expected
    · simp only [assertDiscrExpr, Bool.false_eq_true, ↓reduceIte]
      have hnot := evalValue_boolNot m m' v (decide (bits = 1)) hm_bool
      have h8 := evalValue_boolToU8 m m' (boolNot v) (!decide (bits = 1)) hnot
      rcases (by omega : bits = 0 ∨ bits = 1) with rfl | rfl <;> exact h8
    · simp only [assertDiscrExpr, ↓reduceIte]
      have h8 := evalValue_boolToU8 m m' v (decide (bits = 1)) hm_bool
      rcases (by omega : bits = 0 ∨ bits = 1) with rfl | rfl <;> exact h8
  · obtain ⟨msg, hmsg⟩ := hnone hb
    cases expected
    · exact ⟨msg, by simp [assertDiscrExpr, boolToU8, boolNot, evalValue, evalConstant, hmsg]⟩
    · exact ⟨msg, by simp [assertDiscrExpr, boolToU8, evalValue, hmsg]⟩

/-- **Lockstep and bounded-step simulation for `TerminatorKind.assert`
(`assert cond expected target unwind`)**:
Given a block `bb` at `s.frame.blockIdx` whose statements have finished
(`s.frame.stmtIdx = bb.statements.length`) and whose terminator is
`.assert cond expected target unwind`, translated by
`translateTerminatorAssert body.localDecls nextFresh` into `tb.terminator` and
the fresh blocks `extra`, all of which `f` contains (`hextra`):
1. **Uninitialized or invalid `cond` (`opBits view (copyOp cond) = none`)**:
   Anneal returns `MirStepNode.fail .ub` and MiniRust returns `Interp.step m = .error (.ub msg)`;
2. **Passing branch (`(decide (bits = 1) == expected) = true`)**:
   Anneal (`stepMirFn`) and MiniRust (`Interp.step`) both step in 1 lockstep step
   to `target` with `opPost s.frame.locals cond`;
3. **Failing branch with `unwind = .cleanup cleanupBb`**:
   Anneal (`applyUnwindAction`) and MiniRust (`Interp.step`) both step in 1 lockstep
   step to `cleanupBb` with `opPost s.frame.locals cond`;
4. **Failing branch with `unwind = .unreachable`**:
   Anneal returns `MirStepNode.fail .ub`, and MiniRust jumps to the fresh
   `Unreachable` block and reaches
   `Interp.steps 2 m = .error (.ub "reached unreachable code")`;
5. **Failing branch with `unwind = .terminate`**:
   Anneal returns `MirStepNode.retOutcome .abort`, and MiniRust jumps to the
   fresh `build::abort()` block and reaches `Interp.steps 2 m = .error .abort`;
6. **Failing branch with `unwind = .continue_` in an entry function
   (`s.memory.callStack = []`)**: Anneal unwinds out of the root frame
   (`MirStepNode.retOutcome .panic`), and MiniRust jumps to the fresh
   `build::abort()` block that stands for `mk_start_fn`'s unwind block and
   reaches `Interp.steps 2 m = .error .abort`. -/
theorem step_terminator_assert_simulation
    {body : CapturedMir} {bMove : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {view : List LocalSlot} {lm : Map Gen.LocalName Ptr}
    {s : MachineState} {m : Mach} {bb : BasicBlockData} {tb : Gen.BasicBlock}
    {cond : Operand} {expected : Bool} {target : BasicBlockIdx} {unwind : UnwindAction}
    {nextFresh nextFresh' : Nat} {extra : List (Gen.BbName × Gen.BasicBlock)}
    (hphase : body.phase = .runtimePostCleanup)
    (hcal : s.memory.activeCallee = none)
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hstmt_end : s.frame.stmtIdx = bb.statements.length)
    (hk : bb.terminator.kind = .assert cond expected target unwind)
    (hok : assertTerminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator = true)
    (hgetb : mapGet f.blocks (bbName s.frame.blockIdx) = some tb)
    (hlen : tb.statements.length = bb.statements.length)
    (htt : translateTerminatorAssert body.localDecls nextFresh bb.terminator =
      some (tb.terminator, nextFresh', extra))
    (hextra : ∀ b blk, (b, blk) ∈ extra → mapGet f.blocks b = some blk)
    (hshape : Shape m (ctxWithBorrows body ctx s.memory.borrows)
      [(ctxWithBorrows body ctx s.memory.borrows).caller,
        calleeFrameL f (ctxWithBorrows body ctx s.memory.borrows) lm s.frame.blockIdx
          s.frame.stmtIdx]
      m.mem.memory.allocations)
    (hfl : FnLocalsSpec body f)
    (hlo : LocalsOk body (ctxWithBorrows body ctx s.memory.borrows) view lm m.mem.memory.allocations)
    (hns : NonScalarLive body view lm)
    (hstale : StaleOk bMove s.frame.locals view s.frame.blockIdx s.frame.stmtIdx)
    (hreads : readsOk (movedBefore bMove s.frame.blockIdx bb.statements.length) [cond] = true) :
    (opBits view (copyOp cond) = none →
      stepMirFn body s = MirStepNode.fail .ub ∧
      ∃ msg, Interp.step m = .error (.ub msg)) ∧
    (∀ bits, opBits view (copyOp cond) = some bits →
      (decide (bits = 1) == expected) = true →
      stepMirFn body s = .tau (.running (jumpState s target (opPost s.frame.locals cond))) ∧
      ∃ m', Interp.step m = .ok m' ∧
        Shape m' (ctxWithBorrows body ctx s.memory.borrows)
          [(ctxWithBorrows body ctx s.memory.borrows).caller,
            calleeFrameL f (ctxWithBorrows body ctx s.memory.borrows) lm target 0]
          m'.mem.memory.allocations ∧
        LocalsOk body (ctxWithBorrows body ctx s.memory.borrows) view lm m'.mem.memory.allocations ∧
        NonScalarLive body view lm) ∧
    (∀ bits cleanupBb, opBits view (copyOp cond) = some bits →
      (decide (bits = 1) == expected) = false →
      unwind = .cleanup cleanupBb →
      stepMirFn body s = .tau (.running (jumpState s cleanupBb (opPost s.frame.locals cond))) ∧
      ∃ m', Interp.step m = .ok m' ∧
        Shape m' (ctxWithBorrows body ctx s.memory.borrows)
          [(ctxWithBorrows body ctx s.memory.borrows).caller,
            calleeFrameL f (ctxWithBorrows body ctx s.memory.borrows) lm cleanupBb 0]
          m'.mem.memory.allocations ∧
        LocalsOk body (ctxWithBorrows body ctx s.memory.borrows) view lm m'.mem.memory.allocations ∧
        NonScalarLive body view lm) ∧
    (∀ bits, opBits view (copyOp cond) = some bits →
      (decide (bits = 1) == expected) = false →
      unwind = .unreachable →
      stepMirFn body s = MirStepNode.fail .ub ∧
      Interp.steps 2 m = .error (.ub "reached unreachable code")) ∧
    (∀ bits, opBits view (copyOp cond) = some bits →
      (decide (bits = 1) == expected) = false →
      unwind = .terminate →
      stepMirFn body s = MirStepNode.retOutcome .abort ∧
      Interp.steps 2 m = .error .abort) ∧
    (∀ bits, opBits view (copyOp cond) = some bits →
      (decide (bits = 1) == expected) = false →
      unwind = .continue_ →
      s.memory.callStack = [] →
      s.memory.rootUnwindCeiling = true →
      stepMirFn body s = MirStepNode.retOutcome .panic ∧
      Interp.steps 2 m = .error .abort) := by
  obtain ⟨hdok, _, _⟩ := assertTerminatorOk_spec hok hk
  have hframe : FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm (resetPick m)
      s.frame.blockIdx s.frame.stmtIdx :=
    ⟨hfl, resetPick_shape hshape, hlo, hdeclsOk, hns⟩
  have hslotsA : SlotsOk body.layouts body.localDecls s.frame.locals := hstale.slots hlo.slots
  have hnA : s.frame.locals.length = body.localDecls.length := hstale.1.trans hlo.nlocals
  simp only [translateTerminatorAssert, hk, Option.bind_eq_bind] at htt
  cases hv : translateOperand body.localDecls (copyOp cond) with
  | none => simp [hv] at htt
  | some v =>
    simp only [hv, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at htt
    obtain ⟨htt, -, hex⟩ := htt
    obtain ⟨hokT, hMok, hMnone⟩ := assert_discr_spec hframe expected hdok hv
    have hsimple : simpleOp cond = true := (readsOk_spec hreads cond (by simp)).1
    have hstale_end : StaleOk bMove s.frame.locals view s.frame.blockIdx bb.statements.length := by
      rw [← hstmt_end]; exact hstale
    have hbitsEq : opBits s.frame.locals (copyOp cond) = opBits view (copyOp cond) :=
      opBits_frame _ (by
        rw [opLocals_copyOp]
        exact fun j hj => hstale_end.agree ((readsOk_spec hreads cond (by simp)).2 j hj))
    obtain ⟨hAok, hAnone⟩ := evalRelOperand_frag body.localDecls s.frame.locals hslotsA hnA
      (copyOp cond) hokT s.memory.borrows s.memory.globals s.memory.callerLocals
    have hdeq := @evalOperand_decls_eq_nil_of_RelOperandOk body.layouts
      body.localDecls s.frame.locals .Bool u8Ty
      (copyOp cond) hokT s.memory.borrows s.memory.globals s.memory.callerLocals
    have hmove := evalOperand_move s.frame.locals cond hsimple s.memory.borrows s.memory.globals
      body.layouts s.memory.callerLocals []
    have hcastEq :
        evalOperandWithBodyCast s.frame.locals cond s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals (MirSemantics.bodyLocalDeclsOf (some body)) s.memory.callStack =
        evalOperand s.frame.locals cond s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals [] s.memory.callStack :=
      evalOperandWithBodyCast_eq_evalOperand _ _ _ _ _ _ _ _
        (operandIsLeadingOpaqueCastMove_of_simpleOp hsimple)
    have hif : ((s.frame.stmtIdx : Nat) : Int) = (tb.statements.length : Int) := by
      rw [hlen, hstmt_end]
    have hstepA_eq := stepMirFn_term body s bb hcal hphase hbb hstmt_end
    have hstepM_eq := step_callee hshape tb hgetb
    have hmap1 : mapGet ⟨[(1, bbName target)]⟩ (1 : Int) = some (bbName target) := rfl
    have hmap0 : mapGet ⟨[(1, bbName target)]⟩ (0 : Int) = none := rfl
    refine ⟨fun hb => ?_, fun bits hb hpass => ?_, fun bits cleanupBb hb hfail hu => ?_,
      fun bits hb hfail hu => ?_, fun bits hb hfail hu => ?_,
      fun bits hb hfail hu hcs hceil => ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [hstepA_eq]
        unfold MirSemantics.evalTerminator
        rw [hk]
        dsimp only
        rw [hcastEq, hmove, hdeq, hAnone (hbitsEq.trans hb)]
        rfl
      · obtain ⟨msg, hmsg⟩ := hMnone hb
        exact ⟨msg, by simp [hstepM_eq, hif, ← htt, Interp.evalTerminator, hmsg, bind, Except.bind]⟩
    · obtain ⟨hb2, m3, hm3, h3⟩ := hMok bits hb
      have hcond_eval : evalOperand s.frame.locals cond s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals [] s.memory.callStack =
          .ok (.scalar ⟨bits, 1⟩) (opPost s.frame.locals cond) := by
        rw [hmove, hdeq, hAok bits (hbitsEq.trans hb)]; rfl
      have hA : stepMirFn body s = .tau (.running (jumpState s target (opPost s.frame.locals cond))) := by
        rw [hstepA_eq]
        unfold MirSemantics.evalTerminator
        rw [hk]
        dsimp only
        rw [hcastEq, hcond_eval]
        rcases (by omega : bits = 0 ∨ bits = 1) with rfl | rfl <;>
          cases expected <;> first | (exfalso; revert hpass; decide) | rfl
      obtain ⟨m4, hm4, h4⟩ := jumpToBlock_callee h3.shape target
      have hM : Interp.step m = .ok m4 := by
        rw [hstepM_eq]
        simp [hif, ← htt, Interp.evalTerminator, hm3, hpass, ok_bind, hmap1, Option.getD, hm4, check_after h4]
      exact ⟨hA, m4, hM, ⟨h4.threads, h4.active, rfl⟩, by rw [h4.allocs]; exact h3.locs, h3.nonScalar⟩
    · subst hu
      obtain ⟨hb2, m3, hm3, h3⟩ := hMok bits hb
      have hcond_eval : evalOperand s.frame.locals cond s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals [] s.memory.callStack =
          .ok (.scalar ⟨bits, 1⟩) (opPost s.frame.locals cond) := by
        rw [hmove, hdeq, hAok bits (hbitsEq.trans hb)]; rfl
      have hA : stepMirFn body s = .tau (.running (jumpState s cleanupBb (opPost s.frame.locals cond))) := by
        rw [hstepA_eq]
        unfold MirSemantics.evalTerminator
        rw [hk]
        dsimp only
        rw [hcastEq, hcond_eval]
        rcases (by omega : bits = 0 ∨ bits = 1) with rfl | rfl <;>
          cases expected <;> first | (exfalso; revert hfail; decide) | rfl
      obtain ⟨m4, hm4, h4⟩ := jumpToBlock_callee h3.shape cleanupBb
      have hM : Interp.step m = .ok m4 := by
        rw [hstepM_eq]
        simp [hif, ← htt, Interp.evalTerminator, hm3, hfail, ok_bind, hmap0, Option.getD,
          assertFailTarget, hm4, check_after h4]
      exact ⟨hA, m4, hM, ⟨h4.threads, h4.active, rfl⟩, by rw [h4.allocs]; exact h3.locs, h3.nonScalar⟩
    · subst hu
      obtain ⟨hb2, m3, hm3, h3⟩ := hMok bits hb
      have hcond_eval : evalOperand s.frame.locals cond s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals [] s.memory.callStack =
          .ok (.scalar ⟨bits, 1⟩) (opPost s.frame.locals cond) := by
        rw [hmove, hdeq, hAok bits (hbitsEq.trans hb)]; rfl
      have hA : stepMirFn body s = MirStepNode.fail .ub := by
        rw [hstepA_eq]
        unfold MirSemantics.evalTerminator
        rw [hk]
        dsimp only
        rw [hcastEq, hcond_eval]
        rcases (by omega : bits = 0 ∨ bits = 1) with rfl | rfl <;>
          cases expected <;> first | (exfalso; revert hfail; decide) | rfl
      have hpanic : mapGet f.blocks (bbName nextFresh) = some ⟨[], .Unreachable, .Regular⟩ :=
        hextra _ _ (by rw [← hex]; simp [assertFailTarget])
      obtain ⟨m4, hm4, h4⟩ := jumpToBlock_callee h3.shape nextFresh
      have hstep1 : Interp.step m = .ok m4 := by
        rw [hstepM_eq]
        simp [hif, ← htt, Interp.evalTerminator, hm3, hfail, ok_bind, hmap0, Option.getD,
          assertFailTarget, hm4, check_after h4]
      have hstep2 : Interp.step m4 = .error (.ub "reached unreachable code") := by
        rw [step_callee h4 ⟨[], .Unreachable, .Regular⟩ hpanic]
        rfl
      exact ⟨hA, by simp [Interp.steps, hstep1, hstep2]⟩
    · subst hu
      obtain ⟨hb2, m3, hm3, h3⟩ := hMok bits hb
      have hcond_eval : evalOperand s.frame.locals cond s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals [] s.memory.callStack =
          .ok (.scalar ⟨bits, 1⟩) (opPost s.frame.locals cond) := by
        rw [hmove, hdeq, hAok bits (hbitsEq.trans hb)]; rfl
      have hA : stepMirFn body s = MirStepNode.retOutcome .abort := by
        rw [hstepA_eq]
        unfold MirSemantics.evalTerminator
        rw [hk]
        dsimp only
        rw [hcastEq, hcond_eval]
        rcases (by omega : bits = 0 ∨ bits = 1) with rfl | rfl <;>
          cases expected <;> first | (exfalso; revert hfail; decide) | rfl
      have hpanic : mapGet f.blocks (bbName nextFresh) = some ⟨[], abortTerminator, .Regular⟩ :=
        hextra _ _ (by rw [← hex]; simp [assertFailTarget])
      obtain ⟨m4, hm4, h4⟩ := jumpToBlock_callee h3.shape nextFresh
      have hstep1 : Interp.step m = .ok m4 := by
        rw [hstepM_eq]
        simp [hif, ← htt, Interp.evalTerminator, hm3, hfail, ok_bind, hmap0, Option.getD,
          assertFailTarget, hm4, check_after h4]
      have hstep2 : Interp.step m4 = .error .abort := by
        rw [step_callee h4 ⟨[], abortTerminator, .Regular⟩ hpanic]
        rfl
      exact ⟨hA, by simp [Interp.steps, hstep1, hstep2]⟩
    · subst hu
      obtain ⟨hb2, m3, hm3, h3⟩ := hMok bits hb
      have hcond_eval : evalOperand s.frame.locals cond s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals [] s.memory.callStack =
          .ok (.scalar ⟨bits, 1⟩) (opPost s.frame.locals cond) := by
        rw [hmove, hdeq, hAok bits (hbitsEq.trans hb)]; rfl
      have hA : stepMirFn body s = MirStepNode.retOutcome .panic := by
        rw [hstepA_eq]
        unfold MirSemantics.evalTerminator
        rw [hk]
        dsimp only
        rw [hcastEq, hcond_eval]
        rcases (by omega : bits = 0 ∨ bits = 1) with rfl | rfl <;>
          cases expected <;> first | (exfalso; revert hfail; decide) |
            simp [MirSemantics.applyUnwindAction, MirSemantics.unwindFromCallStack, hcs, hceil]
      have hpanic : mapGet f.blocks (bbName nextFresh) = some ⟨[], abortTerminator, .Regular⟩ :=
        hextra _ _ (by rw [← hex]; simp [assertFailTarget])
      obtain ⟨m4, hm4, h4⟩ := jumpToBlock_callee h3.shape nextFresh
      have hstep1 : Interp.step m = .ok m4 := by
        rw [hstepM_eq]
        simp [hif, ← htt, Interp.evalTerminator, hm3, hfail, ok_bind, hmap0, Option.getD,
          assertFailTarget, hm4, check_after h4]
      have hstep2 : Interp.step m4 = .error .abort := by
        rw [step_callee h4 ⟨[], abortTerminator, .Regular⟩ hpanic]
        rfl
      exact ⟨hA, by simp [Interp.steps, hstep1, hstep2]⟩

/-! ### Whole-function translation with `assert` terminators

`translateFn` translates terminators with `translateTerminator`, which rejects
`assert`. The definitions below translate a function whose terminators are
fragment terminators or `assert`s: each `assert` goes through
`translateTerminatorAssert`, and the fresh blocks it creates follow
`initBlock`, numbered from `n + 1` for a body of `n` blocks, as
`translateFnInProg` numbers the fresh blocks of call unwind edges. The
witnesses in `Witness.lean` compute their MiniRust functions with
`translateFnWithAssert` rather than writing them by hand. -/

/-- `translateTerminator`, with `translateTerminatorAssert` for `assert`:
the MiniRust terminator, the next fresh block number, and the fresh blocks. -/
def translateTerminatorWithAssert (layouts : Layout.LayoutTable) (decls : List LocalDecl)
    (nextFresh : Nat) (t : MirAst.Terminator) :
    Option (Gen.Terminator × Nat × List (Gen.BbName × Gen.BasicBlock)) :=
  match t.kind with
  | .assert .. => translateTerminatorAssert decls nextFresh t
  | _ => do
    let term ← translateTerminator layouts decls t
    pure (term, nextFresh, [])

/-- `translateBlocks` with `translateTerminatorWithAssert`: the translated
blocks (named `bbName i` from `i`) and the fresh blocks (numbered from
`nextFresh`). -/
def translateBlocksWithAssert (layouts : Layout.LayoutTable) (decls : List LocalDecl) :
    Nat → Nat → List BasicBlockData →
      Option (List (Gen.BbName × Gen.BasicBlock) × List (Gen.BbName × Gen.BasicBlock))
  | _, _, [] => some ([], [])
  | i, nextFresh, bb :: bbs => do
    let stmts ← bb.statements.mapM (translateStatement decls · layouts)
    let (term, nextFresh', extra) ←
      translateTerminatorWithAssert layouts decls nextFresh bb.terminator
    let (rest, restExtra) ← translateBlocksWithAssert layouts decls (i + 1) nextFresh' bbs
    pure ((bbName i, ⟨stmts, term, .Regular⟩) :: rest, extra ++ restExtra)

/-- `translateFn` with `translateBlocksWithAssert`; the fresh blocks follow
`initBlock`. -/
def translateFnWithAssert (body : CapturedMir) : Option Gen.Function := do
  let conv ← translateCallConv body.fnAbi.conv
  let locals ← translateLocals body.layouts 0 body.localDecls
  let n := body.basicBlocks.length
  let (blocks, extra) ←
    translateBlocksWithAssert body.layouts body.localDecls 0 (n + 1) body.basicBlocks
  pure {
    locals := ⟨locals⟩
    args := (List.range body.argCount).map (fun k => localName (k + 1))
    ret := localName 0
    calling_convention := conv
    blocks := ⟨blocks ++ [(bbName n, initBlock body)] ++ extra⟩
    start := bbName n
    implicit_writes := true
  }

/-! ### `inFragmentWithAssert`, `StepRelWithAssert`, and Whole-Execution Lift (`G1`) -/

/-- Replace `.assert cond expected target unwind` by a `.switchInt` terminator
with the same operand reads, moves, and in-body successor targets (`[target, cleanupBb]`
for `.cleanup cleanupBb`, `[target]` otherwise), so all `inFragment` dataflow
analyses (`movesOk`, `mentionsOk`, `storageDeadOk`, `ptrAliasingOk`, `livenessOk`,
`tupleInitOk`) apply directly to `eraseAssert body`. -/
def eraseAssertSwitchTargets (expected : Bool) (target : BasicBlockIdx)
    (unwind : UnwindAction) : MirAst.SwitchTargets :=
  { branches := [(if expected then 1 else 0, target)]
    otherwise := match unwind with | .cleanup cleanupBb => cleanupBb | _ => target }

def eraseAssertTerm (t : MirAst.Terminator) : MirAst.Terminator :=
  match t.kind with
  | .assert cond expected target unwind =>
    { t with kind := .switchInt cond (eraseAssertSwitchTargets expected target unwind) }
  | _ => t

def isAssertTerm (t : MirAst.Terminator) : Bool :=
  match t.kind with
  | .assert .. => true
  | _ => false

theorem eraseAssertTerm_of_not {t : MirAst.Terminator} (h : isAssertTerm t = false) :
    eraseAssertTerm t = t := by
  obtain ⟨kind, span⟩ := t
  cases kind <;> first | rfl | simp [isAssertTerm] at h

def eraseAssertBlock (bb : BasicBlockData) : BasicBlockData :=
  { bb with terminator := eraseAssertTerm bb.terminator, isCleanup := false }

def eraseAssert (body : CapturedMir) : CapturedMir :=
  { body with basicBlocks := body.basicBlocks.map eraseAssertBlock }

@[simp] theorem eraseAssert_localDecls (body : CapturedMir) :
    (eraseAssert body).localDecls = body.localDecls := rfl

@[simp] theorem eraseAssert_layouts (body : CapturedMir) :
    (eraseAssert body).layouts = body.layouts := rfl

@[simp] theorem eraseAssert_argCount (body : CapturedMir) :
    (eraseAssert body).argCount = body.argCount := rfl

@[simp] theorem eraseAssert_phase (body : CapturedMir) :
    (eraseAssert body).phase = body.phase := rfl

@[simp] theorem eraseAssert_length (body : CapturedMir) :
    (eraseAssert body).basicBlocks.length = body.basicBlocks.length := by
  simp [eraseAssert]

theorem eraseAssert_block {body : CapturedMir} {blk : Nat} {bb : BasicBlockData}
    (h : body.basicBlocks[blk]? = some bb) :
    (eraseAssert body).basicBlocks[blk]? = some (eraseAssertBlock bb) := by
  simp [eraseAssert, h]

@[simp] theorem eraseAssertBlock_statements (bb : BasicBlockData) :
    (eraseAssertBlock bb).statements = bb.statements := rfl

@[simp] theorem hasStorageMarker_eraseAssert (body : CapturedMir) (loc : Nat) :
    hasStorageMarker (eraseAssert body) loc = hasStorageMarker body loc := by
  simp [hasStorageMarker, eraseAssert, Function.comp_def]

@[simp] theorem alwaysStorageLiveLocals_eraseAssert (body : CapturedMir) :
    alwaysStorageLiveLocals (eraseAssert body) = alwaysStorageLiveLocals body := by
  unfold alwaysStorageLiveLocals
  congr 1
  funext loc
  rw [hasStorageMarker_eraseAssert]
  rfl

theorem LocalsOk.toEraseAssert {body : CapturedMir} {ctx : Ctx} {locals : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} {allocs : List Gen.Allocation}
    (h : LocalsOk body ctx locals lm allocs) :
    LocalsOk (eraseAssert body) ctx locals lm allocs :=
  ⟨h.nlocals, h.slots, h.base, h.keysNodup, h.keysLocal,
    fun i slot hs => by rw [alwaysStorageLiveLocals_eraseAssert]; exact h.live i slot hs,
    h.storage, h.inj, h.owned⟩

theorem LocalsOk.ofEraseAssert {body : CapturedMir} {ctx : Ctx} {locals : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} {allocs : List Gen.Allocation}
    (h : LocalsOk (eraseAssert body) ctx locals lm allocs) :
    LocalsOk body ctx locals lm allocs :=
  ⟨h.nlocals, h.slots, h.base, h.keysNodup, h.keysLocal,
    fun i slot hs => by rw [← alwaysStorageLiveLocals_eraseAssert]; exact h.live i slot hs,
    h.storage, h.inj, h.owned⟩

@[simp] theorem initBlock_eraseAssert (body : CapturedMir) :
    initBlock (eraseAssert body) = initBlock body := by
  simp [initBlock]

@[simp] theorem initLen_eraseAssert (body : CapturedMir) :
    initLen (eraseAssert body) = initLen body := by
  simp [initLen]

@[simp] theorem bodyAddrTakenLocals_eraseAssert (body : CapturedMir) :
    bodyAddrTakenLocals (eraseAssert body) = bodyAddrTakenLocals body := by
  simp [bodyAddrTakenLocals, eraseAssert, List.flatMap_map]

@[simp] theorem nonScalarSlotsInit_eraseAssert (body : CapturedMir) (locals : List LocalSlot) :
    nonScalarSlotsInit (eraseAssert body) locals = nonScalarSlotsInit body locals := by
  simp [nonScalarSlotsInit]

@[simp] theorem initMachineState_eraseAssert (body : CapturedMir) (args : List Value) :
    initMachineState (eraseAssert body) args = initMachineState body args := rfl

@[simp] theorem argsOk_eraseAssert (body : CapturedMir) (args : List Value) :
    argsOk (eraseAssert body) args = argsOk body args := rfl

theorem CtxOk.toEraseAssert {body : CapturedMir} {ctx : Ctx} (h : CtxOk body ctx) :
    CtxOk (eraseAssert body) ctx :=
  ⟨h.addrs, h.ret, h.baseLow⟩

theorem StartRel.toEraseAssert {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {s : MachineState} {mInit : Mach} (h : StartRel body f ctx s mInit) :
    StartRel (eraseAssert body) f ctx s mInit where
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

theorem StartRel.ofEraseAssert {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {s : MachineState} {mInit : Mach} (h : StartRel (eraseAssert body) f ctx s mInit) :
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

/-- Fragment check for bodies that may contain `TerminatorKind.assert`:
`eraseAssert body` satisfies `inFragment`, and every `.assert` terminator
satisfies `assertTerminatorOk`. -/
def inFragmentWithAssert (body : CapturedMir) : Bool :=
  inFragment (eraseAssert body) &&
  body.basicBlocks.all fun bb =>
    match bb.terminator.kind with
    | .assert .. =>
      assertTerminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator
    | _ => true

theorem inFragmentWithAssert_spec {body : CapturedMir} (h : inFragmentWithAssert body = true) :
    inFragment (eraseAssert body) = true ∧
    ∀ bb ∈ body.basicBlocks,
      isAssertTerm bb.terminator = true →
      assertTerminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator = true := by
  simp only [inFragmentWithAssert, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨h.1, fun bb hbb ha => ?_⟩
  have hb := h.2 bb hbb
  cases hk : bb.terminator.kind <;> simp_all [isAssertTerm]

/-- State relation for `inFragmentWithAssert`: `StateRelN` of `eraseAssert body`
together with `s.memory.rootUnwindCeiling = true` (entry-function unwind ceiling
matching `mk_start_fn`). -/
abbrev StateRelWithAssert (body : CapturedMir) (f : Gen.Function) (ctx : Ctx)
    (s : MachineState) (m : Mach) : Prop :=
  StateRelN (eraseAssert body) f ctx s m ∧ s.memory.rootUnwindCeiling = true

/-- Step relation for `inFragmentWithAssert` bodies, covering 1-step `.tau`
(statements, `goto`, passing `assert`, and failing `assert` with `.cleanup`),
1-step `.emit` (`switchInt`), 1-step `.ret (.normal _)`, 1- or 2-step `.ub`
(1 step on statement/switch/uninit-assert-cond UB, 2 steps on failing `assert`
with `.unreachable`), and 2-step `.abort` on failing `assert` with `.terminate`
or `.continue_`. -/
def StepRelWithAssert (body : CapturedMir) (f : Gen.Function) (ctx : Ctx) (s : MachineState)
    (a : MirStepNode) (m : Mach) : Prop :=
  match a with
  | .tau (.running s') => ∃ m', Interp.step m = .ok m' ∧ StateRelWithAssert body f ctx s' m'
  | .vis (.inr (.inl (.emit _))) k =>
    ∃ s' m', k PUnit.unit = .running s' ∧ Interp.step m = .ok m' ∧
      StateRelWithAssert body f ctx s' m'
  | .ret (.normal (v, _)) => ∃ m', Interp.step m = .ok m' ∧ ReturnRel body ctx s v m'
  | .vis (.inl (.fail .ub)) _ =>
    ∃ k msg, (k = 1 ∨ k = 2) ∧ Interp.steps k m = .error (.ub msg)
  | .ret .abort => Interp.steps 2 m = .error .abort
  | .ret .panic => Interp.steps 2 m = .error .abort
  | _ => False

theorem StepRelN.toStepRelWithAssert {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {s : MachineState} {m : Mach} {n : MirStepNode}
    (h : StepRelN (eraseAssert body) f ctx s n (Interp.step m))
    (hceilTau : ∀ s', n = .tau (.running s') → s'.memory.rootUnwindCeiling = true)
    (hceilVis : ∀ ev k s', n = .vis (.inr (.inl (.emit ev))) k →
      k PUnit.unit = .running s' → s'.memory.rootUnwindCeiling = true) :
    StepRelWithAssert body f ctx s n m := by
  unfold StepRelN at h
  unfold StepRelWithAssert
  split at h
  · obtain ⟨m', hr, hst⟩ := h
    exact ⟨m', hr, hst, hceilTau _ rfl⟩
  · obtain ⟨s', m', hk, hr, hst⟩ := h
    exact ⟨s', m', hk, hr, hst, hceilVis _ _ _ rfl hk⟩
  · obtain ⟨m', hr, hret⟩ := h
    obtain ⟨r0, a0, d0, R, hd0, hv0, hp, hr0, hthr, hallocs, hR⟩ := hret
    exact ⟨m', hr, ⟨r0, a0, d0, R, hd0, hv0, hp, hr0, hthr, hallocs, hR⟩⟩
  · obtain ⟨msg, hr⟩ := h
    exact ⟨1, msg, .inl rfl, steps_one_error hr⟩
  · exact h.elim
where
  steps_one_error {m : Mach} {e : Stop} (hr : Interp.step m = .error e) :
      Interp.steps 1 m = .error e := by
    simp [Interp.steps, hr]

theorem translateFnWithAssert_locals {body : CapturedMir} {f : Gen.Function}
    (hf : translateFnWithAssert body = some f) :
    FnLocalsSpec body f ∧ FnLocalsSpec (eraseAssert body) f := by
  have hfl : FnLocalsSpec body f := by
    simp only [translateFnWithAssert, Option.bind_eq_bind] at hf
    cases hC : translateCallConv body.fnAbi.conv with
    | none => simp [hC] at hf
    | some conv =>
      cases hL : translateLocals body.layouts 0 body.localDecls with
      | none => simp [hC, hL] at hf
      | some L =>
        cases hB : translateBlocksWithAssert body.layouts body.localDecls 0
            (body.basicBlocks.length + 1) body.basicBlocks with
        | none => simp [hC, hL, hB] at hf
        | some Bpair =>
          rcases Bpair with ⟨blocks, extra⟩
          simp only [hC, hL, hB, Option.bind_some, Option.pure_def, Option.some.injEq] at hf
          subst hf
          refine ⟨rfl, fun i d hd => ?_⟩
          obtain ⟨T, hT, hget⟩ := translateLocals_get body.layouts 0 body.localDecls L hL i d hd
          rw [tyOf_of_translateTy hT]
          exact ⟨hT, by simpa using hget⟩
  exact ⟨hfl, hfl⟩

private theorem assertFailTarget_keys (nextFresh : Nat) (unwind : UnwindAction) :
    nextFresh < (assertFailTarget nextFresh unwind).2.1 ∧
    ((assertFailTarget nextFresh unwind).2.2.map Prod.fst).Nodup ∧
    ∀ b blk, (b, blk) ∈ (assertFailTarget nextFresh unwind).2.2 →
      ∃ k, b = bbName k ∧ nextFresh ≤ k ∧ k < (assertFailTarget nextFresh unwind).2.1 := by
  cases unwind with
  | cleanup cleanupBb =>
    dsimp [assertFailTarget]
    refine ⟨by omega, List.nodup_nil, fun _ _ h => by simp at h⟩
  | unreachable | terminate | continue_ =>
    dsimp [assertFailTarget]
    refine ⟨by omega, by simp, fun b blk h => ?_⟩
    simp only [List.mem_singleton, Prod.mk.injEq] at h
    exact ⟨nextFresh, h.1, Nat.le_refl _, by omega⟩

private theorem translateTerminatorWithAssert_keys (layouts : Layout.LayoutTable)
    (decls : List LocalDecl) (nextFresh nextFresh' : Nat) (t : MirAst.Terminator)
    (term : Gen.Terminator) (extra : List (Gen.BbName × Gen.BasicBlock))
    (h : translateTerminatorWithAssert layouts decls nextFresh t =
      some (term, nextFresh', extra)) :
    nextFresh ≤ nextFresh' ∧
    (extra.map Prod.fst).Nodup ∧
    (∀ b blk, (b, blk) ∈ extra → ∃ k, b = bbName k ∧ nextFresh ≤ k ∧ k < nextFresh') ∧
    (isAssertTerm t = false →
      translateTerminator layouts decls t = some term ∧ nextFresh' = nextFresh ∧ extra = []) := by
  unfold translateTerminatorWithAssert at h
  split at h
  · next cond expected target unwind hk =>
    simp only [translateTerminatorAssert, hk, Option.bind_eq_bind] at h
    cases hv : translateOperand decls (copyOp cond) with
    | none => simp [hv] at h
    | some v =>
      simp only [hv, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl, rfl⟩ := h
      obtain ⟨hlt, hnd, hmem⟩ := assertFailTarget_keys nextFresh unwind
      exact ⟨Nat.le_of_lt hlt, hnd, hmem, fun hna => by simp [isAssertTerm, hk] at hna⟩
  · next hna =>
    simp only [Option.bind_eq_bind] at h
    cases ht : translateTerminator layouts decls t with
    | none => simp [ht] at h
    | some tm =>
      simp only [ht, Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨Nat.le_refl _, List.nodup_nil, fun _ _ hm => by simp at hm,
        fun _ => ⟨rfl, rfl, rfl⟩⟩

private theorem mapGet_of_mem_nodup_local {K V : Type} [DecidableEq K]
    {entries : List (K × V)} (hnd : (entries.map Prod.fst).Nodup)
    {k : K} {v : V} (hmem : (k, v) ∈ entries) :
    mapGet ⟨entries⟩ k = some v := by
  induction entries with
  | nil => simp at hmem
  | cons p rest ih =>
    obtain ⟨k0, v0⟩ := p
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨hne, hndRest⟩ := hnd
    simp only [mapGet, List.find?_cons]
    rcases List.mem_cons.mp hmem with hEq | hRest
    · injection hEq with hk hv
      subst hk hv
      simp
    · have hk0 : decide (k0 = k) = false :=
        decide_eq_false (fun hkk => by subst hkk; exact hne ⟨(k0, v), hRest, rfl⟩)
      rw [hk0]
      exact ih hndRest hRest

private theorem nodup_append_of_disjoint {α : Type} {xs ys : List α}
    (hx : xs.Nodup) (hy : ys.Nodup) (hdisj : ∀ a ∈ xs, a ∉ ys) :
    (xs ++ ys).Nodup :=
  List.nodup_append.mpr ⟨hx, hy, fun a ha b hb hEq => by subst hEq; exact hdisj a ha hb⟩

private theorem translateBlocksWithAssert_spec (layouts : Layout.LayoutTable)
    (decls : List LocalDecl) :
    ∀ (i nextFresh : Nat) (bbs : List BasicBlockData)
      (blocks extra : List (Gen.BbName × Gen.BasicBlock)),
      translateBlocksWithAssert layouts decls i nextFresh bbs = some (blocks, extra) →
      ∃ nextFresh_end,
        nextFresh ≤ nextFresh_end ∧
        blocks.length = bbs.length ∧
        (blocks.map Prod.fst).Nodup ∧
        (extra.map Prod.fst).Nodup ∧
        (∀ b blk, (b, blk) ∈ blocks → ∃ m, b = bbName m ∧ i ≤ m ∧ m < i + bbs.length) ∧
        (∀ b blk, (b, blk) ∈ extra → ∃ m, b = bbName m ∧ nextFresh ≤ m ∧ m < nextFresh_end) ∧
        (∀ (k : Nat) bb, bbs[k]? = some bb →
          ∃ tb nf nf' ext,
            (bbName (i + k), tb) ∈ blocks ∧
            tb.statements.length = bb.statements.length ∧
            (∀ (sIdx : Nat) st, bb.statements[sIdx]? = some st →
              ∃ st', translateStatement decls st layouts = some st' ∧
                tb.statements[sIdx]? = some st') ∧
            translateTerminatorWithAssert layouts decls nf bb.terminator =
              some (tb.terminator, nf', ext) ∧
            (∀ p ∈ ext, p ∈ extra))
  | i, nextFresh, [], blocks, extra, h => by
    simp [translateBlocksWithAssert] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨nextFresh, Nat.le_refl _, rfl, List.nodup_nil, List.nodup_nil,
      fun _ _ hm => by simp at hm, fun _ _ hm => by simp at hm, fun k _ hk => by simp at hk⟩
  | i, nextFresh, bb :: bbs, blocks, extra, h => by
    simp only [translateBlocksWithAssert, Option.bind_eq_bind] at h
    cases hs : bb.statements.mapM (translateStatement decls · layouts) with
    | none => simp [hs] at h
    | some stmts =>
      cases ht : translateTerminatorWithAssert layouts decls nextFresh bb.terminator with
      | none => simp [hs, ht] at h
      | some t =>
        rcases t with ⟨term, nextFresh', ext⟩
        cases hrest : translateBlocksWithAssert layouts decls (i + 1) nextFresh' bbs with
        | none => simp [hs, ht, hrest] at h
        | some rpair =>
          rcases rpair with ⟨restBlocks, restExtra⟩
          simp only [hs, ht, hrest, Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hlenS, hgetS⟩ := mapM_option_spec (translateStatement decls · layouts)
            bb.statements stmts hs
          obtain ⟨hnf1, hndExt, hmemExt, _⟩ :=
            translateTerminatorWithAssert_keys layouts decls nextFresh nextFresh'
              bb.terminator term ext ht
          obtain ⟨nfEnd, hnf2, hlenR, hndR, hndRExt, hmemR, hmemRExt, hgetR⟩ :=
            translateBlocksWithAssert_spec layouts decls (i + 1) nextFresh' bbs
              restBlocks restExtra hrest
          refine ⟨nfEnd, Nat.le_trans hnf1 hnf2, by simp [hlenR], ?_, ?_, ?_, ?_, ?_⟩
          · simp only [List.map_cons, List.nodup_cons, List.mem_map]
            refine ⟨?_, hndR⟩
            rintro ⟨⟨b, blk⟩, hmem, hbEq⟩
            obtain ⟨m, rfl, hm1, _⟩ := hmemR b blk hmem
            have := (localName_inj m i).mp (by simpa [bbName, localName] using hbEq)
            omega
          · rw [List.map_append]
            refine nodup_append_of_disjoint hndExt hndRExt ?_
            intro b hb1 hb2
            obtain ⟨⟨b1, blk1⟩, hm1, rfl⟩ := List.mem_map.mp hb1
            obtain ⟨⟨b2, blk2⟩, hm2, hbEq⟩ := List.mem_map.mp hb2
            obtain ⟨m1, rfl, _, hm1_lt⟩ := hmemExt b1 blk1 hm1
            obtain ⟨m2, rfl, hm2_le, _⟩ := hmemRExt b2 blk2 hm2
            have := (localName_inj m2 m1).mp (by simpa [bbName, localName] using hbEq)
            omega
          · intro b blk hmem
            rcases List.mem_cons.mp hmem with hEq | hRest
            · injection hEq with hb _
              exact ⟨i, hb, Nat.le_refl _, by simp⟩
            · obtain ⟨m, rfl, hm1, hm2⟩ := hmemR b blk hRest
              exact ⟨m, rfl, by omega, by simp; omega⟩
          · intro b blk hmem
            rcases List.mem_append.mp hmem with h1 | h2
            · obtain ⟨m, rfl, hm1, hm2⟩ := hmemExt b blk h1
              exact ⟨m, rfl, hm1, Nat.lt_of_lt_of_le hm2 hnf2⟩
            · obtain ⟨m, rfl, hm1, hm2⟩ := hmemRExt b blk h2
              exact ⟨m, rfl, Nat.le_trans hnf1 hm1, hm2⟩
          · intro k bb' hk
            cases k with
            | zero =>
              simp at hk; subst hk
              exact ⟨⟨stmts, term, .Regular⟩, nextFresh, nextFresh', ext,
                by simp, hlenS, hgetS, ht, fun p hp => List.mem_append_left _ hp⟩
            | succ k' =>
              simp only [List.getElem?_cons_succ] at hk
              obtain ⟨tb, nf, nf', ext', hmemB, hlenB, hstB, httB, hextB⟩ := hgetR k' bb' hk
              have hik : i + 1 + k' = i + (k' + 1) := by omega
              rw [hik] at hmemB
              exact ⟨tb, nf, nf', ext', List.mem_cons_of_mem _ hmemB, hlenB, hstB, httB,
                fun p hp => List.mem_append_right _ (hextB p hp)⟩

theorem translateFnWithAssert_spec {body : CapturedMir} {f : Gen.Function}
    (hf : translateFnWithAssert body = some f) :
    FnLocalsSpec body f ∧
    (f.start = bbName body.basicBlocks.length ∧
      mapGet f.blocks (bbName body.basicBlocks.length) = some (initBlock body)) ∧
    (∀ (blk : Nat) bb, body.basicBlocks[blk]? = some bb →
      ∃ tb nf nf' extra,
        mapGet f.blocks (bbName blk) = some tb ∧
        tb.statements.length = bb.statements.length ∧
        (∀ (sIdx : Nat) st, bb.statements[sIdx]? = some st →
          ∃ st', translateStatement body.localDecls st body.layouts = some st' ∧
            tb.statements[sIdx]? = some st') ∧
        translateTerminatorWithAssert body.layouts body.localDecls nf bb.terminator =
          some (tb.terminator, nf', extra) ∧
        (∀ b bblk, (b, bblk) ∈ extra → mapGet f.blocks b = some bblk)) := by
  have hfl := (translateFnWithAssert_locals hf).1
  simp only [translateFnWithAssert, Option.bind_eq_bind] at hf
  cases hC : translateCallConv body.fnAbi.conv with
  | none => simp [hC] at hf
  | some conv =>
    cases hL : translateLocals body.layouts 0 body.localDecls with
    | none => simp [hC, hL] at hf
    | some L =>
      cases hB : translateBlocksWithAssert body.layouts body.localDecls 0
          (body.basicBlocks.length + 1) body.basicBlocks with
      | none => simp [hC, hL, hB] at hf
      | some Bpair =>
        rcases Bpair with ⟨blocks, extra⟩
        simp only [hC, hL, hB, Option.bind_some, Option.pure_def, Option.some.injEq] at hf
        subst hf
        dsimp only
        obtain ⟨nfEnd, _, _, hndB, hndE, hmemB, hmemE, hgetB⟩ :=
          translateBlocksWithAssert_spec body.layouts body.localDecls 0
            (body.basicBlocks.length + 1) body.basicBlocks blocks extra hB
        let n := body.basicBlocks.length
        have hndAll : ((blocks ++ [(bbName n, initBlock body)] ++ extra).map Prod.fst).Nodup := by
          rw [List.map_append, List.map_append]
          refine nodup_append_of_disjoint ?_ hndE ?_
          · refine nodup_append_of_disjoint hndB (by simp) ?_
            intro b hb1 hb2
            obtain ⟨⟨b1, blk1⟩, hm1, rfl⟩ := List.mem_map.mp hb1
            simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb2
            obtain ⟨m, rfl, _, hm_lt⟩ := hmemB b1 blk1 hm1
            have := (localName_inj m n).mp (by simpa [bbName, localName] using hb2)
            omega
          · intro b hb1 hb2
            obtain ⟨⟨b2, blk2⟩, hm2, hbEq⟩ := List.mem_map.mp hb2
            obtain ⟨m2, rfl, hm2_le, _⟩ := hmemE b2 blk2 hm2
            rcases List.mem_append.mp hb1 with hbB | hbI
            · obtain ⟨⟨b1, blk1⟩, hm1, rfl⟩ := List.mem_map.mp hbB
              obtain ⟨m1, rfl, _, hm1_lt⟩ := hmemB b1 blk1 hm1
              have := (localName_inj m2 m1).mp (by simpa [bbName, localName] using hbEq)
              omega
            · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hbI
              subst hbI
              have := (localName_inj m2 n).mp (by simpa [bbName, localName] using hbEq)
              omega
        refine ⟨hfl, ⟨rfl, mapGet_of_mem_nodup_local hndAll
            (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))⟩,
          fun blk bb hbb => ?_⟩
        obtain ⟨tb, nf, nf', ext, hmemTb, hlenTb, hstTb, httTb, hextTb⟩ := hgetB blk bb hbb
        rw [Nat.zero_add] at hmemTb
        refine ⟨tb, nf, nf', ext,
          mapGet_of_mem_nodup_local hndAll (List.mem_append_left _ (List.mem_append_left _ hmemTb)),
          hlenTb, hstTb, httTb, fun b bblk hmemExt =>
            mapGet_of_mem_nodup_local hndAll (List.mem_append_right _ (hextTb (b, bblk) hmemExt))⟩

private theorem stepMirFn_eraseAssert_stmt {body : CapturedMir} {s : MachineState}
    {bb : BasicBlockData} {st : MirAst.Statement}
    (hcal : s.memory.activeCallee = none) (hphase : body.phase = .runtimePostCleanup)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some st) :
    stepMirFn body s = stepMirFn (eraseAssert body) s := by
  have hbbE := eraseAssert_block hbb
  have hstE : (eraseAssertBlock bb).statements[s.frame.stmtIdx]? = some st := hst
  rw [stepMirFn_stmt body s bb st hcal hphase hbb hst,
    stepMirFn_stmt (eraseAssert body) s (eraseAssertBlock bb) st hcal hphase hbbE hstE]
  rfl

private theorem stepMirFn_eraseAssert_term_nonAssert {body : CapturedMir} {s : MachineState}
    {bb : BasicBlockData}
    (hcal : s.memory.activeCallee = none) (hphase : body.phase = .runtimePostCleanup)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (heq : s.frame.stmtIdx = bb.statements.length)
    (hterm : terminatorOk body.layouts body.localDecls body.basicBlocks.length
      (eraseAssertBlock bb).terminator = true)
    (hna : isAssertTerm bb.terminator = false) :
    stepMirFn body s = stepMirFn (eraseAssert body) s := by
  have hbbE := eraseAssert_block hbb
  have heqE : s.frame.stmtIdx = (eraseAssertBlock bb).statements.length := heq
  have htEq : (eraseAssertBlock bb).terminator = bb.terminator := eraseAssertTerm_of_not hna
  rw [stepMirFn_term body s bb hcal hphase hbb heq,
    stepMirFn_term (eraseAssert body) s (eraseAssertBlock bb) hcal hphase hbbE heqE, htEq]
  rw [htEq] at hterm
  rcases hbt : bb.terminator with ⟨kind, span⟩
  rw [hbt] at hterm
  cases kind with
  | goto _ | switchInt _ _ | unreachable | return_ => rfl
  | _ => simp [terminatorOk] at hterm

private def MemUnwindPreserved (m1 m2 : MirSemantics.Memory) : Prop :=
  m2.rootUnwindCeiling = m1.rootUnwindCeiling ∧
  m2.callStack = m1.callStack ∧ m2.callerLocals = m1.callerLocals

private theorem evalSliceFatPtrDerefBorrow_memPreserved
    {locals mem parentPtr ptrSz lenSc restProj perm isMut pointeeTyOpt layouts checkPerm decls
      accessedTyOpt checkResultRefAlign v locals' mem'}
    (h : evalSliceFatPtrDerefBorrow locals mem parentPtr ptrSz lenSc restProj perm isMut
      pointeeTyOpt layouts checkPerm decls accessedTyOpt checkResultRefAlign = .ok v locals' mem') :
    MemUnwindPreserved mem mem' := by
  unfold evalSliceFatPtrDerefBorrow at h
  cases hlb : lookupBorrow mem.borrows parentPtr.tag <;> simp only [hlb] at h <;>
    repeat' (first | contradiction | (cases h; exact ⟨rfl, rfl, rfl⟩) | split at h | dsimp only at h)

private theorem evalGlobalThinPtrDerefBorrow_memPreserved
    {locals mem alloc parentPtr ptrSz restProj isMut pointeeTyOpt layouts decls isRaw accessedTyOpt
      v locals' mem'}
    (h : evalGlobalThinPtrDerefBorrow locals mem alloc parentPtr ptrSz restProj isMut
      pointeeTyOpt layouts decls isRaw accessedTyOpt = .ok v locals' mem') :
    MemUnwindPreserved mem mem' := by
  unfold evalGlobalThinPtrDerefBorrow at h
  repeat' (first | contradiction | (cases h; exact ⟨rfl, rfl, rfl⟩) | split at h | dsimp only at h)

private theorem evalRvalueRefDeref_memPreserved
    {locals borrowKind place restProj perm mem decls layouts v locals' mem'}
    (h : evalRvalueRefDeref locals borrowKind place restProj perm mem decls layouts = .ok v locals' mem') :
    MemUnwindPreserved mem mem' := by
  unfold evalRvalueRefDeref at h
  repeat' (first | contradiction | exact evalGlobalThinPtrDerefBorrow_memPreserved h | exact evalSliceFatPtrDerefBorrow_memPreserved h | (cases h; exact ⟨rfl, rfl, rfl⟩) | split at h | dsimp only at h)

private theorem evalRvalueRawPtr_memPreserved
    {locals mutability place mem decls layouts v locals' mem'}
    (h : evalRvalueRawPtr locals mutability place mem decls layouts = .ok v locals' mem') :
    MemUnwindPreserved mem mem' := by
  unfold evalRvalueRawPtr at h
  cases hp : place.projection <;> simp only [hp] at h <;>
    repeat' (first | contradiction | exact evalGlobalThinPtrDerefBorrow_memPreserved h | exact evalSliceFatPtrDerefBorrow_memPreserved h | (unfold evalScalarSliceFatPtrDerefRaw at h; repeat' (first | contradiction | (cases h; exact ⟨rfl, rfl, rfl⟩) | split at h | dsimp only at h)) | (cases h; exact ⟨rfl, rfl, rfl⟩) | split at h | dsimp only at h)

private theorem evalCastPtrToPtr_memPreserved
    {locals op targetTy mem decls layouts v locals' mem'}
    (h : evalCastPtrToPtr locals op targetTy mem decls layouts = .ok v locals' mem') :
    MemUnwindPreserved mem mem' := by
  unfold evalCastPtrToPtr at h
  have hDerive : ∀ l1 ptr entry metaOpt pb v' l' m',
      deriveStackElemThinPtr l1 mem ptr entry metaOpt pb = .ok v' l' m' → MemUnwindPreserved mem m' := by
    intro _ _ _ _ _ _ _ _ hd; unfold deriveStackElemThinPtr at hd
    repeat' (first | contradiction | (cases hd; exact ⟨rfl, rfl, rfl⟩) | split at hd | dsimp only at hd)
  repeat' (first | contradiction | exact hDerive _ _ _ _ _ _ _ _ h | (cases h; exact ⟨rfl, rfl, rfl⟩) | split at h | dsimp only at h)

private theorem evalRvalue_memPreserved
    (locals : List LocalSlot) (rv : Rvalue) (mem : MirSemantics.Memory)
    (decls : List LocalDecl) (layouts : Layout.LayoutTable) (dstTy : Option Ty)
    (ht : (translateRvalue layouts decls dstTy (copyRv rv)).isSome = true)
    (v : Value) (locals' : List LocalSlot) (mem' : MirSemantics.Memory)
    (h : evalRvalue locals rv mem decls layouts = .ok v locals' mem') :
    MemUnwindPreserved mem mem' := by
  cases rv with
  | use _ | copyForDeref _ | «repeat» _ _ =>
    simp only [evalRvalue] at h
    repeat' (first | contradiction | (cases h; exact ⟨rfl, rfl, rfl⟩) | split at h | dsimp only at h)
  | binaryOp _ _ _ =>
    simp only [evalRvalue, evalFloatScalarBinOp, evalScalarPtrOffsetBinOp, evalScalarBinOp,
      evalPtrOffsetBinOp, evalWidePtrAggregateRelBinOp, evalWidePtrRelBinOp, evalSignedDiv, evalSignedRem] at h
    repeat' (first | contradiction | (cases h; exact ⟨rfl, rfl, rfl⟩) | split at h | dsimp only at h)
  | ref _ _ =>
    simp only [evalRvalue] at h
    repeat' (first | contradiction | exact evalRvalueRefDeref_memPreserved h | (cases h; exact ⟨rfl, rfl, rfl⟩) | split at h | dsimp only at h)
  | rawPtr _ _ => simp only [evalRvalue] at h; exact evalRvalueRawPtr_memPreserved h
  | len _ =>
    simp only [evalRvalue, evalPlaceLen] at h
    repeat' (first | contradiction | (cases h; exact ⟨rfl, rfl, rfl⟩) | split at h | dsimp only at h)
  | cast ck _ _ =>
    cases ck with
    | intToInt =>
      simp only [evalRvalue] at h
      repeat' (first | contradiction | (cases h; exact ⟨rfl, rfl, rfl⟩) | split at h | dsimp only at h)
    | ptrToPtr => simp only [evalRvalue] at h; exact evalCastPtrToPtr_memPreserved h
    | transmute =>
      simp only [evalRvalue, evalByteCast] at h
      repeat' (first | contradiction | (cases h; exact ⟨rfl, rfl, rfl⟩) | split at h | dsimp only at h)
    | _ => simp [copyRv, translateRvalue] at ht
  | unaryOp _ _ =>
    simp only [evalRvalue, evalFloatUnaryNeg, evalUnaryNot, evalUnaryPtrMetadata] at h
    repeat' (first | contradiction | (cases h; exact ⟨rfl, rfl, rfl⟩) | split at h | dsimp only at h)
  | discriminant _ =>
    simp only [evalRvalue, evalPlaceDiscriminant] at h
    repeat' (first | contradiction | (cases h; exact ⟨rfl, rfl, rfl⟩) | split at h | dsimp only at h)
  | aggregate ak _ =>
    cases ak with
    | array _ | tuple =>
      simp only [evalRvalue] at h
      repeat' (first | contradiction | (cases h; exact ⟨rfl, rfl, rfl⟩) | split at h | dsimp only at h)
    | adt _ vIdx active =>
      cases vIdx <;> cases active <;> try (simp [copyRv, translateRvalue] at ht)
      simp only [evalRvalue, evalAggregateAdt] at h
      repeat' (first | contradiction | (cases h; exact ⟨rfl, rfl, rfl⟩) | split at h | dsimp only at h)
    | _ => simp [copyRv, translateRvalue] at ht
  | _ => simp [copyRv, translateRvalue] at ht

private theorem evalFnEntryRetag_rootUnwindCeiling
    (s s' : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (place : Place) (ptrVal : ProvenancePtr) (sz : Nat) (parentEntry : BorrowEntry) (locals' : List LocalSlot)
    (h : evalFnEntryRetag s decls layouts place ptrVal sz parentEntry locals' = .tau (.running s')) :
    s'.memory.rootUnwindCeiling = s.memory.rootUnwindCeiling := by
  unfold evalFnEntryRetag at h
  repeat' (first | contradiction | (cases h; rfl) | split at h | dsimp only at h)

private theorem evalFnEntryRetag_ne_emit
    (s : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (place : Place) (ptrVal : ProvenancePtr) (sz : Nat) (parentEntry : BorrowEntry) (locals' : List LocalSlot)
    (ev : MirObs) (k : PUnit → MirExecState)
    (h : evalFnEntryRetag s decls layouts place ptrVal sz parentEntry locals' = .vis (.inr (.inl (.emit ev))) k) :
    False := by
  unfold evalFnEntryRetag at h
  repeat' (first | contradiction | (simp only [MirStepNode.step, MirStepNode.fail, MirStepNode.unsupported] at h; cases h) | split at h | dsimp only at h)

private theorem evalForeignFrameDerefWrite_of_nil
    (s : MachineState) (locals₁ : List LocalSlot) (mem₁ : MirSemantics.Memory)
    (place : Place) (restProj : List ProjectionElem) (val : Value)
    (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (hcs : mem₁.callStack = []) (hcl : mem₁.callerLocals = []) :
    (∀ s', evalForeignFrameDerefWrite s locals₁ mem₁ place restProj val decls layouts = .tau (.running s') →
      s'.memory.rootUnwindCeiling = mem₁.rootUnwindCeiling) ∧
    (∀ ev k, evalForeignFrameDerefWrite s locals₁ mem₁ place restProj val decls layouts =
      .vis (.inr (.inl (.emit ev))) k → False) := by
  have hfw : ∀ l2 m2, foreignFrameDerefWrite locals₁ mem₁ place restProj val decls layouts = .ok l2 m2 →
      m2.rootUnwindCeiling = mem₁.rootUnwindCeiling := by
    intro l2 m2 h; unfold foreignFrameDerefWrite at h; simp only [hcs, hcl, foreignFrameTarget?] at h
    repeat' (first | contradiction | (cases h; rfl) | split at h | dsimp only at h)
  refine ⟨fun s' h => ?_, fun ev k h => ?_⟩
  · unfold evalForeignFrameDerefWrite at h
    repeat' (first | contradiction | (cases h; exact hfw _ _ ‹_›) | split at h | dsimp only at h)
  · unfold evalForeignFrameDerefWrite at h
    repeat' (first | contradiction | (simp only [MirStepNode.step, MirStepNode.fail, MirStepNode.unsupported] at h; cases h) | split at h | dsimp only at h)

private theorem evalNonFnEntryRetag_rootUnwindCeiling
    (retagKind : RetagKind) (s s' : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (place : Place) (ptrVal : ProvenancePtr) (sz : Nat) (parentEntry : BorrowEntry) (locals' : List LocalSlot)
    (h : evalNonFnEntryRetag retagKind s decls layouts place ptrVal sz parentEntry locals' = .tau (.running s')) :
    s'.memory.rootUnwindCeiling = s.memory.rootUnwindCeiling := by
  unfold evalNonFnEntryRetag at h
  repeat' (first | contradiction | (cases h; rfl) | split at h | dsimp only at h)

private theorem evalNonFnEntryRetag_ne_emit
    (retagKind : RetagKind) (s : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (place : Place) (ptrVal : ProvenancePtr) (sz : Nat) (parentEntry : BorrowEntry) (locals' : List LocalSlot)
    (ev : MirObs) (k : PUnit → MirExecState)
    (h : evalNonFnEntryRetag retagKind s decls layouts place ptrVal sz parentEntry locals' = .vis (.inr (.inl (.emit ev))) k) :
    False := by
  unfold evalNonFnEntryRetag at h
  repeat' (first | contradiction | (simp only [MirStepNode.step, MirStepNode.fail, MirStepNode.unsupported] at h; cases h) | split at h | dsimp only at h)

private theorem evalStmt_preserves_rootUnwindCeiling
    (s : MachineState) (st : MirAst.Statement) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable)
    (hcs : s.memory.callStack = []) (hcl : s.memory.callerLocals = [])
    (ht : (translateStatement decls st layouts).isSome = true) :
    (∀ s', evalStmt s st decls layouts = .tau (.running s') →
      s'.memory.rootUnwindCeiling = s.memory.rootUnwindCeiling) ∧
    (∀ ev k s', evalStmt s st decls layouts = .vis (.inr (.inl (.emit ev))) k →
      k PUnit.unit = .running s' →
      s'.memory.rootUnwindCeiling = s.memory.rootUnwindCeiling) := by
  rcases st with ⟨kind, span⟩
  cases kind with
  | assign dst rv =>
    have hrvT : (translateRvalue layouts decls (placeMirTy decls dst) (copyRv rv)).isSome = true := by
      obtain ⟨st', hst'⟩ := Option.isSome_iff_exists.mp ht
      simp only [translateStatement, bind, Option.bind] at hst'
      cases hp : translatePlace decls dst <;> rw [hp] at hst' <;> try cases hst'
      cases hr : translateRvalue layouts decls (placeMirTy decls dst) (copyRv rv) <;>
        rw [hr] at hst' <;> try cases hst'
      rfl
    refine ⟨fun s' h => ?_, fun ev k s' h _ => ?_⟩
    · simp only [evalStmt] at h
      repeat'
        (first
         | contradiction
         | (have hmp := evalRvalue_memPreserved _ _ _ _ _ _ hrvT _ _ _ ‹_›
            exact ((evalForeignFrameDerefWrite_of_nil _ _ _ _ _ _ _ _ (hmp.2.1.trans hcs) (hmp.2.2.trans hcl)).1 _ h).trans hmp.1)
         | (simp only [MirStepNode.step, MirStepNode.fail, MirStepNode.unsupported] at h; cases h;
            simp only [advanceStmt]; exact (evalRvalue_memPreserved _ _ _ _ _ _ hrvT _ _ _ ‹_›).1)
         | split at h
         | dsimp only at h)
    · simp only [evalStmt] at h
      repeat'
        (first
         | contradiction
         | (have hmp := evalRvalue_memPreserved _ _ _ _ _ _ hrvT _ _ _ ‹_›
            exact False.elim ((evalForeignFrameDerefWrite_of_nil _ _ _ _ _ _ _ _ (hmp.2.1.trans hcs) (hmp.2.2.trans hcl)).2 _ _ h))
         | (simp only [MirStepNode.step, MirStepNode.fail, MirStepNode.unsupported] at h; cases h)
         | split at h
         | dsimp only at h)
  | placeMention _ | storageLive _ | storageDead _ | deinit _ | retag _ _ =>
    refine ⟨fun s' h => ?_, fun ev k s' h _ => ?_⟩
    · simp only [evalStmt] at h
      repeat'
        (first
         | contradiction
         | exact evalNonFnEntryRetag_rootUnwindCeiling _ _ _ _ _ _ _ _ _ _ h
         | exact evalFnEntryRetag_rootUnwindCeiling _ _ _ _ _ _ _ _ _ h
         | (cases h; rfl)
         | (simp only [MirStepNode.step, MirStepNode.fail, MirStepNode.unsupported] at h; cases h; rfl)
         | split at h
         | dsimp only at h)
    · simp only [evalStmt] at h
      repeat'
        (first
         | contradiction
         | exact False.elim (evalNonFnEntryRetag_ne_emit _ _ _ _ _ _ _ _ _ _ _ h)
         | exact False.elim (evalFnEntryRetag_ne_emit _ _ _ _ _ _ _ _ _ _ h)
         | (simp only [MirStepNode.step, MirStepNode.fail, MirStepNode.unsupported] at h; cases h)
         | split at h
         | dsimp only at h)
  | _ => simp [translateStatement] at ht

private theorem evalTerminator_nonAssert_preserves_rootUnwindCeiling
    (s : MachineState) (t : MirAst.Terminator) (body : CapturedMir)
    (hcs : s.memory.callStack = [])
    (hterm : terminatorOk body.layouts body.localDecls body.basicBlocks.length t = true) :
    (∀ s', MirSemantics.evalTerminator s t (some body) = .tau (.running s') →
      s'.memory.rootUnwindCeiling = s.memory.rootUnwindCeiling) ∧
    (∀ ev k s', MirSemantics.evalTerminator s t (some body) = .vis (.inr (.inl (.emit ev))) k →
      k PUnit.unit = .running s' →
      s'.memory.rootUnwindCeiling = s.memory.rootUnwindCeiling) := by
  rcases t with ⟨kind, span⟩
  cases kind with
  | goto tgt =>
    refine ⟨fun s' h => ?_, fun _ _ _ h _ => ?_⟩
    · simp only [MirSemantics.evalTerminator, MirStepNode.step] at h; cases h; rfl
    · simp only [MirSemantics.evalTerminator, MirStepNode.step] at h; cases h
  | switchInt discr targets =>
    refine ⟨fun s' h => ?_, fun ev k s' h hk => ?_⟩
    · simp only [MirSemantics.evalTerminator] at h
      split at h <;> (simp only [MirStepNode.fail, MirStepNode.emitStep, MirStepNode.unsupported] at h; cases h)
    · simp only [MirSemantics.evalTerminator] at h
      split at h <;> try (simp only [MirStepNode.fail, MirStepNode.unsupported] at h; cases h)
      simp only [MirStepNode.emitStep] at h
      injection h with _ hkEq
      rw [← hkEq] at hk
      cases hk; rfl
  | unreachable =>
    refine ⟨fun _ h => ?_, fun _ _ _ h _ => ?_⟩
    · simp only [MirSemantics.evalTerminator, MirStepNode.fail] at h; cases h
    · simp only [MirSemantics.evalTerminator, MirStepNode.fail] at h; cases h
  | return_ =>
    refine ⟨fun _ h => ?_, fun _ _ _ h _ => ?_⟩
    · simp only [MirSemantics.evalTerminator, hcs] at h
      repeat' (first | contradiction | (simp only [MirStepNode.fail, MirStepNode.retNormal] at h; cases h) | split at h | dsimp only at h)
    · simp only [MirSemantics.evalTerminator, hcs] at h
      repeat' (first | contradiction | (simp only [MirStepNode.fail, MirStepNode.retNormal] at h; cases h) | split at h | dsimp only at h)
  | _ => simp [terminatorOk] at hterm

/-- **One-step correspondence for `inFragmentWithAssert` bodies (`G1`)**:
For any `body` in `inFragmentWithAssert` and its translation
`translateFnWithAssert body = some f`, every step from `StateRelWithAssert`
satisfies `StepRelWithAssert` (and when `bb.terminator` is `.assert ..` with
`unwind = .continue_`, requires `s.memory.callStack = []` and
`s.memory.rootUnwindCeiling = true`, which `StateRelWithAssert` guarantees). -/
theorem step_correspondence_withAssert (body : CapturedMir) (f : Gen.Function)
    (hfragA : inFragmentWithAssert body = true)
    (hf : translateFnWithAssert body = some f) (ctx : Ctx)
    (s : MachineState) (m : Mach) (hrel : StateRelWithAssert body f ctx s m) :
    StepRelWithAssert body f ctx s (stepMirFn body s) m := by
  obtain ⟨hfragE, hasserts⟩ := inFragmentWithAssert_spec hfragA
  obtain ⟨hfl, _, hblkSpec⟩ := translateFnWithAssert_spec hf
  have hflE := (translateFnWithAssert_locals hf).2
  obtain ⟨hphaseE, _, _, _, hdeclsOk, _, hbbsE, _, hmvOkE, _⟩ := inFragment_spec _ hfragE
  have hphase : body.phase = .runtimePostCleanup := hphaseE
  obtain ⟨hpaE, _⟩ := inFragment_ptr _ hfragE
  obtain ⟨⟨view, lm, hrelA, hthr, hlo, hns, hbo⟩, hceil⟩ := hrel
  have hblk_lt : s.frame.blockIdx < body.basicBlocks.length := by simpa using hrelA.blk
  obtain ⟨bb, hbb⟩ : ∃ bb, body.basicBlocks[s.frame.blockIdx]? = some bb :=
    ⟨_, List.getElem?_eq_getElem hblk_lt⟩
  have hbbmem : bb ∈ body.basicBlocks := List.mem_of_getElem? hbb
  have hbbE := eraseAssert_block hbb
  have hle : s.frame.stmtIdx ≤ bb.statements.length := hrelA.stmt (eraseAssertBlock bb) hbbE
  rcases Nat.lt_or_ge s.frame.stmtIdx bb.statements.length with hlt | hge
  · obtain ⟨st, hst⟩ : ∃ st, bb.statements[s.frame.stmtIdx]? = some st :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    obtain ⟨tb, nf, nf', ext, hgetb, hlen, hstB, _, _⟩ := hblkSpec _ bb hbb
    obtain ⟨st', htrSt, _⟩ := hstB _ st hst
    have htrSome : (translateStatement body.localDecls st body.layouts).isSome = true := by
      rw [htrSt]; rfl
    have hpres := evalStmt_preserves_rootUnwindCeiling s st body.localDecls body.layouts
      hrelA.callStack hrelA.callerLocals htrSome
    have hstepEq := stepMirFn_stmt body s bb st hrelA.activeCallee hphase hbb hst
    rw [stepMirFn_eraseAssert_stmt hrelA.activeCallee hphase hbb hst]
    apply StepRelN.toStepRelWithAssert
    · refine step_correspondence_NF_at (eraseAssert body) f hfragE hflE ctx s m ?_
        ⟨view, lm, hrelA, hthr, hlo, hns, hbo⟩
      intro bb' hbb'
      rw [hbbE] at hbb'; cases hbb'
      exact ⟨tb, hgetb, hlen, fun st' hst' => hstB _ st' hst', fun heq => by dsimp [eraseAssertBlock] at heq; omega⟩
    · intro s' hs'
      rw [← stepMirFn_eraseAssert_stmt hrelA.activeCallee hphase hbb hst, hstepEq] at hs'
      exact (hpres.1 s' hs').trans hceil
    · intro ev k s' hs' hk'
      rw [← stepMirFn_eraseAssert_stmt hrelA.activeCallee hphase hbb hst, hstepEq] at hs'
      exact (hpres.2 ev k s' hs' hk').trans hceil
  · have heq : s.frame.stmtIdx = bb.statements.length := by omega
    obtain ⟨tb, nf, nf', ext, hgetb, hlen, hstB, htt, hextra⟩ := hblkSpec _ bb hbb
    by_cases ha : isAssertTerm bb.terminator = true
    · obtain ⟨cond, expected, target, unwind, hk⟩ :
          ∃ cond expected target unwind,
            bb.terminator.kind = .assert cond expected target unwind := by
        cases htk : bb.terminator.kind <;> first | exact ⟨_, _, _, _, rfl⟩ | simp [isAssertTerm, htk] at ha
      have hok : assertTerminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator = true :=
        hasserts bb hbbmem ha
      obtain ⟨_, htarget_lt, hclean_lt⟩ := assertTerminatorOk_spec hok hk
      have httA : translateTerminatorAssert body.localDecls nf bb.terminator =
          some (tb.terminator, nf', ext) := by
        simpa [translateTerminatorWithAssert, hk] using htt
      obtain ⟨_, hmvT, hmvEdge⟩ := movesOk_spec hmvOkE hbbE
      have hreads : readsOk (movedBefore (eraseAssert body) s.frame.blockIdx bb.statements.length)
          [cond] = true := by
        simpa [eraseAssertBlock, eraseAssertTerm, eraseAssertSwitchTargets, hk, termReadsOk] using hmvT
      have hshape : Shape m (ctxWithBorrows body ctx s.memory.borrows)
          [(ctxWithBorrows body ctx s.memory.borrows).caller,
            calleeFrameL f (ctxWithBorrows body ctx s.memory.borrows) lm s.frame.blockIdx
              s.frame.stmtIdx]
          m.mem.memory.allocations := ⟨hthr, hrelA.active, rfl⟩
      have hstale_end : StaleOk (eraseAssert body) s.frame.locals view s.frame.blockIdx
          bb.statements.length := by
        rw [← heq]; exact hrelA.stale
      obtain ⟨hnone, hpass, hclean, hunreach, htermA, hcont⟩ :=
        step_terminator_assert_simulation (body := body) (bMove := eraseAssert body)
          hphase hrelA.activeCallee hdeclsOk hbb heq hk hok hgetb hlen httA hextra
          hshape hfl hlo.ofEraseAssert hns hrelA.stale hreads
      cases hb : opBits view (copyOp cond) with
      | none =>
        obtain ⟨hA, msg, hM⟩ := hnone hb
        rw [hA]
        exact ⟨1, msg, .inl rfl, by simp [Interp.steps, hM]⟩
      | some bits =>
        by_cases hpassB : (decide (bits = 1) == expected) = true
        · obtain ⟨hA, m', hM, hsh', hlo', hns'⟩ := hpass bits hb hpassB
          rw [hA]
          have htMem : target ∈ termTargets (eraseAssertBlock bb).terminator := by
            simp [eraseAssertBlock, eraseAssertTerm, eraseAssertSwitchTargets, hk, termTargets]
          have hsub : ∀ j ∈ moveOut (movedBefore (eraseAssert body) s.frame.blockIdx bb.statements.length) cond,
              j ∈ movedBefore (eraseAssert body) target 0 := by
            have hm := hmvEdge target htMem
            simpa [eraseAssertBlock, eraseAssertTerm, eraseAssertSwitchTargets, hk, termMoved] using hm
          exact ⟨m', hM, hrelA.jumpN hfragE lm target (by simpa using htarget_lt) _
            hsh'.threads hsh'.active hlo'.toEraseAssert hns'
            (hstale_end.toBlockMove cond hsub)
            (hbo.jump hpaE hbbE hge target htMem _), hceil⟩
        · have hfailB : (decide (bits = 1) == expected) = false :=
            Bool.eq_false_iff.mpr hpassB
          cases unwind with
          | cleanup cleanupBb =>
            obtain ⟨hA, m', hM, hsh', hlo', hns'⟩ := hclean bits cleanupBb hb hfailB rfl
            rw [hA]
            have hcMem : cleanupBb ∈ termTargets (eraseAssertBlock bb).terminator := by
              simp [eraseAssertBlock, eraseAssertTerm, eraseAssertSwitchTargets, hk, termTargets]
            have hsub : ∀ j ∈ moveOut (movedBefore (eraseAssert body) s.frame.blockIdx bb.statements.length) cond,
                j ∈ movedBefore (eraseAssert body) cleanupBb 0 := by
              have hm := hmvEdge cleanupBb hcMem
              simpa [eraseAssertBlock, eraseAssertTerm, eraseAssertSwitchTargets, hk, termMoved] using hm
            exact ⟨m', hM, hrelA.jumpN hfragE lm cleanupBb
              (by simpa using hclean_lt cleanupBb rfl) _
              hsh'.threads hsh'.active hlo'.toEraseAssert hns'
              (hstale_end.toBlockMove cond hsub)
              (hbo.jump hpaE hbbE hge cleanupBb hcMem _), hceil⟩
          | unreachable =>
            obtain ⟨hA, hM⟩ := hunreach bits hb hfailB rfl
            rw [hA]
            exact ⟨2, "reached unreachable code", .inr rfl, hM⟩
          | terminate =>
            obtain ⟨hA, hM⟩ := htermA bits hb hfailB rfl
            rw [hA]
            exact hM
          | continue_ =>
            obtain ⟨hA, hM⟩ := hcont bits hb hfailB rfl hrelA.callStack hceil
            rw [hA]
            exact hM
    · have hna : isAssertTerm bb.terminator = false := Bool.eq_false_iff.mpr ha
      have htermE := (hbbsE _ (List.mem_of_getElem? hbbE)).2.2
      simp only [eraseAssert_layouts, eraseAssert_localDecls, eraseAssert_length] at htermE
      have htEq : (eraseAssertBlock bb).terminator = bb.terminator := eraseAssertTerm_of_not hna
      have htermB : terminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator = true := by
        rwa [htEq] at htermE
      have hpres := evalTerminator_nonAssert_preserves_rootUnwindCeiling s bb.terminator body hrelA.callStack htermB
      have hstepEq := stepMirFn_term body s bb hrelA.activeCallee hphase hbb heq
      rw [stepMirFn_eraseAssert_term_nonAssert hrelA.activeCallee hphase hbb heq htermE hna]
      apply StepRelN.toStepRelWithAssert
      · refine step_correspondence_NF (eraseAssert body) f hfragE hflE ctx s m ?_
          ⟨view, lm, hrelA, hthr, hlo, hns, hbo⟩
        intro bb' hbb'
        rw [hbbE] at hbb'; cases hbb'
        have httE : translateTerminator body.layouts body.localDecls
            (eraseAssertBlock bb).terminator = some tb.terminator := by
          rw [eraseAssertBlock, eraseAssertTerm_of_not hna]
          exact ((translateTerminatorWithAssert_keys body.layouts body.localDecls nf nf'
            bb.terminator tb.terminator ext htt).2.2.2 hna).1
        exact ⟨tb, hgetb, hlen, fun st' hst' => hstB _ st' hst', httE⟩
      · intro s' hs'
        rw [← stepMirFn_eraseAssert_term_nonAssert hrelA.activeCallee hphase hbb heq htermE hna, hstepEq] at hs'
        exact (hpres.1 s' hs').trans hceil
      · intro ev k s' hs' hk'
        rw [← stepMirFn_eraseAssert_term_nonAssert hrelA.activeCallee hphase hbb heq htermE hna, hstepEq] at hs'
        exact (hpres.2 ev k s' hs' hk').trans hceil

/-- **Init block (`StateRelWithAssert`)**: from `StartRel` at `f.start`,
`initLen body` MiniRust steps land in `StateRelWithAssert`. -/
theorem step_start_withAssert {body : CapturedMir} {f : Gen.Function}
    (hfragA : inFragmentWithAssert body = true)
    (hf : translateFnWithAssert body = some f) {ctx : Ctx} {s : MachineState} {mInit : Mach}
    (hstart : StartRel body f ctx s mInit)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide)
    (hceil : s.memory.rootUnwindCeiling = true := by rfl) :
    ∃ m0, Interp.steps (initLen body) mInit = .ok m0 ∧ StateRelWithAssert body f ctx s m0 := by
  have hfragE := (inFragmentWithAssert_spec hfragA).1
  obtain ⟨_, hst0, _⟩ := translateFnWithAssert_spec hf
  have hst0E : f.start = bbName (eraseAssert body).basicBlocks.length ∧
      mapGet f.blocks (bbName (eraseAssert body).basicBlocks.length) =
        some (initBlock (eraseAssert body)) := by
    rw [eraseAssert_length, initBlock_eraseAssert]
    exact hst0
  obtain ⟨m0, hm0, hrel0⟩ := step_start_NF hfragE (translateFnWithAssert_locals hf).2
    hst0E hstart.toEraseAssert (by rw [nonScalarSlotsInit_eraseAssert]; exact hns)
  rw [initLen_eraseAssert] at hm0
  exact ⟨m0, hm0, hrel0, hceil⟩

private theorem mirTree_observe_local (body : CapturedMir) (s : MachineState) :
    (mirTree body s).observe = (stepMirFn body s).map (Trusted.ITree.ITree.cofix (stepMirState body)) := by
  simp [mirTree, Trusted.ITree.ITree.observe_cofix, stepMirState]

private theorem tauStar_reaches_local {t u : Trusted.ITree.ITree MirEffect MirOutcome}
    (h : Trusted.ITree.TauStar t u) : Trusted.ITree.Reaches t [] u := by
  induction h with
  | refl t => exact .refl t
  | step hobs _ ih => exact .tau hobs ih

/-- Every Anneal execution prefix `Reaches (mirTree body s) tr u` on an
`inFragmentWithAssert` body is matched by MiniRust steps to a
`StateRelWithAssert`-related state. -/
theorem reaches_rel_withAssert {body : CapturedMir} {f : Gen.Function}
    (hfragA : inFragmentWithAssert body = true)
    (hf : translateFnWithAssert body = some f) (ctx : Ctx)
    {t u : Trusted.ITree.ITree MirEffect MirOutcome}
    {tr : List (Trusted.Effect.Event MirEffect)} (h : Trusted.ITree.Reaches t tr u) :
    ∀ (s : MachineState) (m : Mach), t = mirTree body s → StateRelWithAssert body f ctx s m →
      ∃ (n : Nat) (s' : MachineState) (m' : Mach), Interp.steps n m = .ok m' ∧
        StateRelWithAssert body f ctx s' m' ∧ u = mirTree body s' := by
  induction h with
  | refl t =>
    intro s m ht hrel
    exact ⟨0, s, m, rfl, hrel, ht⟩
  | tau hobs _ ih =>
    intro s m ht hrel
    subst ht
    have hsr := step_correspondence_withAssert body f hfragA hf ctx s m hrel
    rw [mirTree_observe_local] at hobs
    generalize stepMirFn body s = node at hsr hobs
    cases node with
    | ret r => simp [Trusted.ITree.ITreeF.map] at hobs
    | vis i k => simp [Trusted.ITree.ITreeF.map] at hobs
    | tau x =>
      simp only [Trusted.ITree.ITreeF.map, Trusted.ITree.ITreeF.tau.injEq] at hobs
      cases x with
      | running s1 =>
        obtain ⟨m1, hm1, hrel1⟩ := hsr
        obtain ⟨n, s', m', hsteps, hrel', hu⟩ := ih s1 m1 hobs.symm hrel1
        exact ⟨n + 1, s', m', by simp [Interp.steps, hm1, hsteps], hrel', hu⟩
      | halted _ => exact False.elim hsr
      | faulted _ => exact False.elim hsr
  | vis hobs hnf o _ ih =>
    intro s m ht hrel
    subst ht
    have hsr := step_correspondence_withAssert body f hfragA hf ctx s m hrel
    rw [mirTree_observe_local] at hobs
    generalize stepMirFn body s = node at hsr hobs
    cases node with
    | ret r => simp [Trusted.ITree.ITreeF.map] at hobs
    | tau x => simp [Trusted.ITree.ITreeF.map] at hobs
    | vis i0 k0 =>
      simp only [Trusted.ITree.ITreeF.map] at hobs
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
          have ht' : Trusted.ITree.ITree.cofix (stepMirState body) (k0 PUnit.unit) =
              mirTree body s1 := by
            rw [hk1]; rfl
          obtain ⟨n, s', m', hsteps, hrel', hu⟩ := ih s1 m1 ht' hrel1
          exact ⟨n + 1, s', m', by simp [Interp.steps, hm1, hsteps], hrel', hu⟩

/-- **Whole-execution normal return for `inFragmentWithAssert` (`G1`)**:
If Anneal's semantics of `body` from `s` returns `.normal (v, mem)`, MiniRust
from a `StateRelWithAssert`-related state reaches `ReturnRel` after finitely
many steps. -/
theorem run_ret_withAssert {body : CapturedMir} {f : Gen.Function}
    (hfragA : inFragmentWithAssert body = true)
    (hf : translateFnWithAssert body = some f) (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRelWithAssert body f ctx s m)
    {tr : List (Trusted.Effect.Event MirEffect)} {v : Value} {mem : MirSemantics.Memory}
    (hret : Trusted.ITree.ReachesRet (mirTree body s) tr (.normal (v, mem))) :
    ∃ (n : Nat) (s' : MachineState) (m' : Mach),
      Interp.steps n m = .ok m' ∧ ReturnRel body ctx s' v m' := by
  obtain ⟨u, hreach, hu⟩ := hret
  obtain ⟨n, s', m', hsteps, hrel', rfl⟩ :=
    reaches_rel_withAssert hfragA hf ctx hreach s m rfl hrel
  have hsr := step_correspondence_withAssert body f hfragA hf ctx s' m' hrel'
  rw [mirTree_observe_local] at hu
  generalize stepMirFn body s' = node at hsr hu
  cases node with
  | tau x => simp [Trusted.ITree.ITreeF.map] at hu
  | vis i k => simp [Trusted.ITree.ITreeF.map] at hu
  | ret r =>
    simp only [Trusted.ITree.ITreeF.map, Trusted.ITree.ITreeF.ret.injEq] at hu
    subst hu
    obtain ⟨m'', hm'', hret'⟩ := hsr
    exact ⟨n + 1, s', m'', by rw [steps_add, hsteps]; simp [Interp.steps, hm''], hret'⟩

/-- **Whole-execution UB for `inFragmentWithAssert` (`G1`)**:
If Anneal's semantics of `body` from `s` reaches `FaultNow` (either a 1-step
UB or a failing `assert` with `unwind = .unreachable`), MiniRust from a
`StateRelWithAssert`-related state stops with `.error (.ub msg)` after finitely
many steps. -/
theorem run_ub_withAssert {body : CapturedMir} {f : Gen.Function}
    (hfragA : inFragmentWithAssert body = true)
    (hf : translateFnWithAssert body = some f) (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRelWithAssert body f ctx s m)
    {tr : List (Trusted.Effect.Event MirEffect)} {u : Trusted.ITree.ITree MirEffect MirOutcome}
    (hreach : Trusted.ITree.Reaches (mirTree body s) tr u)
    (hfault : Trusted.ITree.FaultNow u) :
    ∃ (n : Nat) (msg : String), Interp.steps n m = .error (.ub msg) := by
  obtain ⟨t', i, k, htau, hobs, hfi⟩ := hfault
  obtain ⟨n1, s1, m1, h1, hrel1, rfl⟩ :=
    reaches_rel_withAssert hfragA hf ctx hreach s m rfl hrel
  obtain ⟨n2, s2, m2, h2, hrel2, rfl⟩ :=
    reaches_rel_withAssert hfragA hf ctx (tauStar_reaches_local htau) s1 m1 rfl hrel1
  have hsr := step_correspondence_withAssert body f hfragA hf ctx s2 m2 hrel2
  rw [mirTree_observe_local] at hobs
  generalize stepMirFn body s2 = node at hsr hobs
  cases node with
  | ret r => simp [Trusted.ITree.ITreeF.map] at hobs
  | tau x => simp [Trusted.ITree.ITreeF.map] at hobs
  | vis i0 k0 =>
    simp only [Trusted.ITree.ITreeF.map] at hobs
    injection hobs with hi _
    subst hi
    cases i0 with
    | inr b =>
      cases b with
      | inl _ => exact False.elim hfi
      | inr _ => exact False.elim hfi
    | inl f0 =>
      cases f0 with
      | fail reason =>
        cases reason with
        | ub =>
          obtain ⟨kStep, msg, _, hkStep⟩ := hsr
          exact ⟨(n1 + n2) + kStep, msg, by rw [steps_add, steps_add, h1, ok_bind, h2, ok_bind, hkStep]⟩
        | unsupported | outOfFuel => exact False.elim hsr

/-- **Whole-execution abort/panic for `inFragmentWithAssert` (`G1`)**:
If Anneal's semantics of `body` from `s` reaches `.abort` (failing `assert`
with `unwind = .terminate`) or `.panic` (failing `assert` with
`unwind = .continue_`), MiniRust from a `StateRelWithAssert`-related state
reaches `.error .abort` after finitely many steps. -/
theorem run_abort_or_panic_withAssert {body : CapturedMir} {f : Gen.Function}
    (hfragA : inFragmentWithAssert body = true)
    (hf : translateFnWithAssert body = some f) (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRelWithAssert body f ctx s m)
    {tr : List (Trusted.Effect.Event MirEffect)} {o : MirOutcome}
    (hret : Trusted.ITree.ReachesRet (mirTree body s) tr o)
    (ho : o = .abort ∨ o = .panic) :
    ∃ (n : Nat), Interp.steps n m = .error .abort := by
  obtain ⟨u, hreach, hu⟩ := hret
  obtain ⟨n, s', m', hsteps, hrel', rfl⟩ :=
    reaches_rel_withAssert hfragA hf ctx hreach s m rfl hrel
  have hsr := step_correspondence_withAssert body f hfragA hf ctx s' m' hrel'
  rw [mirTree_observe_local] at hu
  generalize stepMirFn body s' = node at hsr hu
  cases node with
  | tau x => simp [Trusted.ITree.ITreeF.map] at hu
  | vis i k => simp [Trusted.ITree.ITreeF.map] at hu
  | ret r =>
    simp only [Trusted.ITree.ITreeF.map, Trusted.ITree.ITreeF.ret.injEq] at hu
    subst hu
    rcases ho with rfl | rfl <;> exact ⟨n + 2, by rw [steps_add, hsteps, ok_bind, hsr]⟩

/-- **Call-tree normal return from `f.start` for `inFragmentWithAssert` (`G1`)**. -/
theorem mirCall_ret_withAssert {body : CapturedMir} {f : Gen.Function}
    (hfragA : inFragmentWithAssert body = true)
    (hf : translateFnWithAssert body = some f) (ctx : Ctx) (hctx : CtxOk body ctx)
    (args : List Value) (hargs : argsOk body args = true) (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals body.layouts)
    {tr : List (Trusted.Effect.Event MirEffect)} {v : Value} {mem : MirSemantics.Memory}
    (hret : Trusted.ITree.ReachesRet (mirCallTree body args) tr (.normal (v, mem))) :
    ∃ (n : Nat) (s' : MachineState) (m' : Mach),
      Interp.steps n mInit = .ok m' ∧ ReturnRel body ctx s' v m' := by
  have hfragE := (inFragmentWithAssert_spec hfragA).1
  have hstart : StartRel body f ctx (initMachineState body args) mInit :=
    (initMachineState_startRel hfragE ctx hctx.toEraseAssert args hargs mInit
      hthreads hactive hallocs).ofEraseAssert
  have hns : nonScalarSlotsInit body (initMachineState body args).frame.locals = true := by
    rw [← nonScalarSlotsInit_eraseAssert]
    exact initMachineState_nonScalar hfragE args hargs
  obtain ⟨m0, hm0, hrel0⟩ := step_start_withAssert hfragA hf hstart hns
  obtain ⟨n, s', m', hsteps, hret'⟩ :=
    run_ret_withAssert hfragA hf ctx (initMachineState body args) m0 hrel0 hret
  exact ⟨initLen body + n, s', m', by rw [steps_add, hm0, ok_bind, hsteps], hret'⟩

/-- **Call-tree UB from `f.start` for `inFragmentWithAssert` (`G1`)**. -/
theorem mirCall_ub_withAssert {body : CapturedMir} {f : Gen.Function}
    (hfragA : inFragmentWithAssert body = true)
    (hf : translateFnWithAssert body = some f) (ctx : Ctx) (hctx : CtxOk body ctx)
    (args : List Value) (hargs : argsOk body args = true) (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals body.layouts)
    {tr : List (Trusted.Effect.Event MirEffect)} {u : Trusted.ITree.ITree MirEffect MirOutcome}
    (hreach : Trusted.ITree.Reaches (mirCallTree body args) tr u)
    (hfault : Trusted.ITree.FaultNow u) :
    ∃ (n : Nat) (msg : String), Interp.steps n mInit = .error (.ub msg) := by
  have hfragE := (inFragmentWithAssert_spec hfragA).1
  have hstart : StartRel body f ctx (initMachineState body args) mInit :=
    (initMachineState_startRel hfragE ctx hctx.toEraseAssert args hargs mInit
      hthreads hactive hallocs).ofEraseAssert
  have hns : nonScalarSlotsInit body (initMachineState body args).frame.locals = true := by
    rw [← nonScalarSlotsInit_eraseAssert]
    exact initMachineState_nonScalar hfragE args hargs
  obtain ⟨m0, hm0, hrel0⟩ := step_start_withAssert hfragA hf hstart hns
  obtain ⟨n, msg, hsteps⟩ :=
    run_ub_withAssert hfragA hf ctx (initMachineState body args) m0 hrel0 hreach hfault
  exact ⟨initLen body + n, msg, by rw [steps_add, hm0, ok_bind, hsteps]⟩

/-- **Call-tree abort/panic from `f.start` for `inFragmentWithAssert` (`G1`)**. -/
theorem mirCall_abort_or_panic_withAssert {body : CapturedMir} {f : Gen.Function}
    (hfragA : inFragmentWithAssert body = true)
    (hf : translateFnWithAssert body = some f) (ctx : Ctx) (hctx : CtxOk body ctx)
    (args : List Value) (hargs : argsOk body args = true) (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals body.layouts)
    {tr : List (Trusted.Effect.Event MirEffect)} {o : MirOutcome}
    (hret : Trusted.ITree.ReachesRet (mirCallTree body args) tr o)
    (ho : o = .abort ∨ o = .panic) :
    ∃ (n : Nat), Interp.steps n mInit = .error .abort := by
  have hfragE := (inFragmentWithAssert_spec hfragA).1
  have hstart : StartRel body f ctx (initMachineState body args) mInit :=
    (initMachineState_startRel hfragE ctx hctx.toEraseAssert args hargs mInit
      hthreads hactive hallocs).ofEraseAssert
  have hns : nonScalarSlotsInit body (initMachineState body args).frame.locals = true := by
    rw [← nonScalarSlotsInit_eraseAssert]
    exact initMachineState_nonScalar hfragE args hargs
  obtain ⟨m0, hm0, hrel0⟩ := step_start_withAssert hfragA hf hstart hns
  obtain ⟨n, hsteps⟩ :=
    run_abort_or_panic_withAssert hfragA hf ctx (initMachineState body args) m0 hrel0 hret ho
  exact ⟨initLen body + n, by rw [steps_add, hm0, ok_bind, hsteps]⟩

/-! ## Union-Extended Local & Machine State Relation and Multi-Step Run Composition (`R-d`)

`Relation.lean` (outside Episode 2's edit scope) restricts `LocalsOk` /
`StateRelN` to `LocalTy` locals (`scalar`, `intBoolTuple`, `[Int; N]`,
`TupleSpec`, `thinRawPtr`, `&T`). The definitions below extend `LocalStorage`,
`LocalsOkA`, and `StateRelN` additively in `Simulation.lean` to cover frames
containing `Type.Union` locals (`mrUnionTy fields S al` with
`MiniRustUnionBytesRel`, including `.Uninit` padding bytes) and 0-byte ZST
locals (`mrUnitTy`, `mrZstArrayTy N`, `mrUninhabitedZstTy`) alongside standard
`LocalStorage` locals:
* `LocalsOkA.toWithUnions` and `StateRelN.toStateRelWithUnions` embed existing
  `LocalsOkA` / `StateRelN` states;
* `step_union_whole_copy_stateRelWithUnions` lifts
  `step_union_whole_copy_minirust_simulation` onto `StateRelWithUnions`;
* `evalReturn_withUnions` and `step_return_withUnions` prove `Return` teardown
  across mixed scalar + ZST + `Type.Union` frames, establishing `ReturnRel`;
* `reaches_rel_withUnions`, `run_ret_withUnions`, and `run_ub_withUnions`
  compose per-step union simulations into whole-execution normal return
  (`ReturnRel`) and UB (`Stop.ub`) theorems. -/

/-- `StackFrame::storage_dead` on any live local whose MiniRust type `T` has
sized layout `.Sized ⟨sz⟩ ⟨al⟩` (generalizing `storageDead_some` from `LocalTy`
to include `mrUnionTy`, `mrZstArrayTy`, `mrUnitTy`, and `mrUninhabitedZstTy`). -/
theorem storageDead_sized {fr : Frame} {cm : Gen.ConcurrentMemory BM} {key : Gen.LocalName}
    {T : Gen.«Type»} {sz al : Nat}
    (hlay : Interp.Type.layout T = .ok (.Sized ⟨sz⟩ ⟨al⟩))
    (hty : mapGet fr.func.locals key = some T)
    {p : Ptr} (hp : mapGet fr.locals key = some p) {k : Nat}
    (hpk : p.provenance = some (⟨(k : Int)⟩, ())) {a : Gen.Allocation}
    (hA : cm.memory.allocations[k]? = some a) (hlive : a.live = true) (haddr : a.addr = p.addr)
    (hkind : a.kind = .Stack) (hlen : a.data.length = sz) (halign : a.align = ⟨al⟩) :
    storageDead fr cm key =
      .ok ({ fr with locals := ⟨fr.locals.entries.filter (fun e => !decide (e.1 = key))⟩ },
           { cm with memory := { cm.memory with allocations := cm.memory.allocations.set k (kill a) } }) := by
  obtain ⟨hk, hAk⟩ := List.getElem?_eq_some_iff.mp hA
  simp [storageDead, mapIndex, hty, hlay, LayoutStrategy.expect_size,
    LayoutStrategy.expect_align, mapRemove, hp, CM.deallocate, BM.deallocate, hpk, listIndex, hk,
    hAk, hlive, haddr, hkind, Allocation.size, hlen, halign, listSet, kill]

/-- Frame teardown loop of `Return` (`deallocAll`) generalized from `LocalTy`
(`deallocAll_gen`) to arbitrary sized MiniRust types (including `Type.Union` and
0-byte ZST locals). -/
theorem deallocAll_sized (fuel : Nat) (fr : Frame) (cm : Gen.ConcurrentMemory BM)
    (es : List (Gen.LocalName × Ptr)) (hfuel : es.length ≤ fuel) (hloc : fr.locals = ⟨es⟩)
    (hnodup : (es.map Prod.fst).Nodup) (hidnd : (es.map (fun e => provId e.2)).Nodup)
    (hok : ∀ e ∈ es, ∃ T sz al a, mapGet fr.func.locals e.1 = some T ∧
      Interp.Type.layout T = .ok (.Sized ⟨sz⟩ ⟨al⟩) ∧
      e.2.provenance = some (⟨(provId e.2 : Int)⟩, ()) ∧
      cm.memory.allocations[provId e.2]? = some a ∧ a.live = true ∧ a.addr = e.2.addr ∧
      a.kind = .Stack ∧ a.data.length = sz ∧ a.align = ⟨al⟩) :
    ∃ cm', deallocAll fuel fr cm = .ok ({ fr with locals := ⟨[]⟩ }, cm') ∧
      cm'.memory.allocations = killAt cm.memory.allocations (es.map (fun e => provId e.2)) := by
  induction es generalizing fuel fr cm with
  | nil =>
    refine ⟨cm, ?_, by simp [killAt_nil]⟩
    have hfr : fr = { fr with locals := ⟨[]⟩ } := by
      cases fr; simp at hloc; simp [hloc]
    cases fuel <;> (simp only [deallocAll, hloc]; rw [← hfr]; rfl)
  | cons e es ih =>
    obtain ⟨key, p⟩ := e
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    rw [List.map_cons, List.nodup_cons] at hnodup hidnd
    obtain ⟨hni, hnd⟩ := hnodup
    obtain ⟨hnid, hndid⟩ := hidnd
    obtain ⟨T, sz, al, a, hty, hlay, hpk, ha, hlive, haddr, hkind, hlen, halign⟩ :=
      hok (key, p) (by simp)
    have hrest : ∀ e ∈ es, e.1 ≠ key := fun e he hek => hni (List.mem_map.mpr ⟨e, he, hek⟩)
    have hp : mapGet fr.locals key = some p := by rw [hloc, mapGet_cons]; simp
    have hsd := storageDead_sized hlay hty hp hpk ha hlive haddr hkind hlen halign
    have hfil : fr.locals.entries.filter (fun e => !decide (e.1 = key)) = es := by
      rw [hloc]; exact filter_key_cons_self key p es hrest
    rw [hfil] at hsd
    obtain ⟨cm', hcm', hcm'mem⟩ := ih fuel' { fr with locals := ⟨es⟩ }
      { cm with memory := { cm.memory with
          allocations := cm.memory.allocations.set (provId p) (kill a) } }
      (by simp at hfuel; omega) rfl hnd hndid
      (by
        intro e he
        obtain ⟨T', sz', al', a', hty', hlay', hpk', ha', h1, h2, h3, h4, h5⟩ := hok e (by simp [he])
        have hij : provId p ≠ provId e.2 := fun hij => hnid (List.mem_map.mpr ⟨e, he, hij.symm⟩)
        exact ⟨T', sz', al', a', hty', hlay', hpk',
          by simp only; rw [List.getElem?_set_ne hij]; exact ha', h1, h2, h3, h4, h5⟩)
    refine ⟨cm', ?_, ?_⟩
    · rw [deallocAll]; simp only [hloc]; rw [hsd]; simpa using hcm'
    · rw [hcm'mem, List.map_cons, killAt_cons _ _ _ a ha hnid]

/-- Additive per-local storage relation extending `LocalStorage` with 0-byte ZST
locals (`()`, `[(); N]`, uninhabited 0-byte enums) and `Type.Union` locals
(`mrUnionTy fields S al` related by `MiniRustUnionBytesRel`). -/
inductive LocalStorageWithUnions (f : Gen.Function) (ctx : Ctx) (allocs : List Gen.Allocation)
    (layouts : Layout.LayoutTable) (i : Nat) (d : LocalDecl) (slot : LocalSlot) (p : Ptr) : Prop
  | base :
      mapGet f.locals (localName i) = some (tyOf d layouts) →
      localDeclOk layouts d = true →
      DeclSlotOk d slot layouts →
      LocalStorage ctx allocs d slot p layouts →
      LocalStorageWithUnions f ctx allocs layouts i d slot p
  | zstUnit (id : Nat) :
      d.ty.kind = .tuple [] →
      mapGet f.locals (localName i) = some mrUnitTy →
      p.provenance = some (⟨(id : Int)⟩, ()) →
      ctx.base.length ≤ id →
      0 ≤ p.addr →
      p.addr < 2 ^ 64 →
      (slot = .uninit ∨ slot = .init .unit) →
      allocs[id]? = some (stackAlloc p.addr ⟨.Unsigned, ⟨1⟩⟩ []) →
      LocalStorageWithUnions f ctx allocs layouts i d slot p
  | zstArray (N id : Nat) :
      d.ty.kind = .array (.tuple []) N →
      mapGet f.locals (localName i) = some (mrZstArrayTy N) →
      p.provenance = some (⟨(id : Int)⟩, ()) →
      ctx.base.length ≤ id →
      0 ≤ p.addr →
      p.addr < 2 ^ 64 →
      (slot = .uninit ∨ slot = .init (.aggregate 0 (List.replicate N .unit)) ∨
        slot = .init (.aggregate 0 (List.replicate N (.aggregate 0 [])))) →
      allocs[id]? = some (stackAlloc p.addr ⟨.Unsigned, ⟨1⟩⟩ []) →
      LocalStorageWithUnions f ctx allocs layouts i d slot p
  | zstUninhabited (id : Nat) :
      (scalarTypeOf d.ty).isSome = false →
      mapGet f.locals (localName i) = some mrUninhabitedZstTy →
      p.provenance = some (⟨(id : Int)⟩, ()) →
      ctx.base.length ≤ id →
      0 ≤ p.addr →
      p.addr < 2 ^ 64 →
      slot = .uninit →
      allocs[id]? = some (stackAlloc p.addr ⟨.Unsigned, ⟨1⟩⟩ []) →
      LocalStorageWithUnions f ctx allocs layouts i d slot p
  | union (fields : List (Gen.Offset × Gen.«Type»)) (S al id : Nat) (mrBytes : List Byte) :
      (scalarTypeOf d.ty).isSome = false →
      0 < S →
      mapGet f.locals (localName i) = some (mrUnionTy fields S al) →
      p.provenance = some (⟨(id : Int)⟩, ()) →
      ctx.base.length ≤ id →
      Align.is_aligned ⟨al⟩ p.addr = true →
      0 ≤ p.addr →
      p.addr + (S : Int) < 2 ^ 64 →
      mrBytes.length = S →
      allocs[id]? = some (stackAlloc p.addr ⟨.Unsigned, ⟨al⟩⟩ mrBytes) →
      (match slot with
       | .uninit => mrBytes = List.replicate S .Uninit
       | .init val => MiniRustUnionBytesRel layouts d.ty S val mrBytes
       | .dead => False) →
      LocalStorageWithUnions f ctx allocs layouts i d slot p

/-- Any `MiniRustUnionLocalStorage` at `localPtr ctx u` in `ctx.base ++ L`
(for a non-scalar union declaration `d`) satisfies `LocalStorageWithUnions.union`. -/
theorem LocalStorageWithUnions.ofMiniRustUnionLocalStorage
    {f : Gen.Function} {ctx : Ctx} {L : List Gen.Allocation} {lm : Map Gen.LocalName Ptr}
    {layouts : Layout.LayoutTable} {u : Nat} {d : LocalDecl}
    {fields : List (Gen.Offset × Gen.«Type»)} {S al : Nat}
    {slot : LocalSlot} {mrBytes : List Byte}
    (hnonSc : (scalarTypeOf d.ty).isSome = false)
    (hu : MiniRustUnionLocalStorage ctx L f lm layouts u d.ty fields S al slot mrBytes) :
    LocalStorageWithUnions f ctx (ctx.base ++ L) layouts u d slot (localPtr ctx u) := by
  refine .union fields S al (ctx.base.length + u) mrBytes hnonSc hu.pos_size hu.fn_local rfl
    (Nat.le_add_right _ _) hu.align_ok hu.addr_nonneg hu.addr_lt hu.bytes_len ?_ hu.slot_rel
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact hu.alloc_eq

theorem LocalStorageWithUnions.teardown_entry
    {f : Gen.Function} {ctx : Ctx} {allocs : List Gen.Allocation}
    {layouts : Layout.LayoutTable} {i : Nat} {d : LocalDecl} {slot : LocalSlot} {p : Ptr}
    (h : LocalStorageWithUnions f ctx allocs layouts i d slot p) :
    ∃ (id : Nat) (T : Gen.«Type») (sz al : Nat) (data : List Byte),
      p.provenance = some (⟨(id : Int)⟩, ()) ∧
      ctx.base.length ≤ id ∧
      mapGet f.locals (localName i) = some T ∧
      Interp.Type.layout T = .ok (.Sized ⟨sz⟩ ⟨al⟩) ∧
      data.length = sz ∧
      allocs[id]? = some (stackAlloc p.addr ⟨.Unsigned, ⟨al⟩⟩ data) := by
  cases h with
  | base hfn hdok hsl hls =>
    obtain ⟨id, hpid, hb, _, _, _, hA⟩ := hls
    have hlt := localTy_of_declOk hdok
    cases hp_ty : isPtrTy d.ty with
    | false =>
      simp only [hp_ty, Bool.false_eq_true, ↓reduceIte] at hA
      refine ⟨id, tyOf d layouts, tyBytes (tyOf d layouts), (itOf d layouts).size.bytes,
        declSlotData d slot layouts, hpid, hb, hfn, hlt.layout,
        declSlotData_length_of_declOk hdok hsl, ?_⟩
      simpa [stackAlloc] using hA
    | true =>
      simp only [hp_ty, ↓reduceIte] at hA
      obtain ⟨hTd, _⟩ := tyOf_isPtrTy (layouts := layouts) hp_ty
      match slot, hsl, hA with
      | .dead, hsl, hA =>
        refine ⟨id, tyOf d layouts, tyBytes (tyOf d layouts), (itOf d layouts).size.bytes,
          _, hpid, hb, hfn, hlt.layout, declSlotData_length_of_declOk hdok hsl, ?_⟩
        simpa [stackAlloc] using hA
      | .uninit, hsl, hA =>
        refine ⟨id, tyOf d layouts, tyBytes (tyOf d layouts), (itOf d layouts).size.bytes,
          _, hpid, hb, hfn, hlt.layout, declSlotData_length_of_declOk hdok hsl, ?_⟩
        simpa [stackAlloc] using hA
      | .init v, hsl, hA =>
        obtain ⟨pv, rfl⟩ := (DeclSlotOk_of_isPtrTy hp_ty (.init v)).mp hsl
        obtain ⟨tAddr, tProv, _, _, hA'⟩ := hA
        refine ⟨id, tyOf d layouts, tyBytes (tyOf d layouts), (itOf d layouts).size.bytes,
          ptrBytes tAddr tProv, hpid, hb, hfn, hlt.layout,
          by rw [ptrBytes_length, hTd, tyBytes_declPtrTy], ?_⟩
        simpa [stackAlloc] using hA'
  | zstUnit id _ hfn hpid hb _ _ _ hA =>
    exact ⟨id, mrUnitTy, 0, 1, [], hpid, hb, hfn, Type_layout_mrUnitTy, rfl, hA⟩
  | zstArray N id _ hfn hpid hb _ _ _ hA =>
    exact ⟨id, mrZstArrayTy N, 0, 1, [], hpid, hb, hfn, Type_layout_mrZstArrayTy N, rfl, hA⟩
  | zstUninhabited id _ hfn hpid hb _ _ _ hA =>
    exact ⟨id, mrUninhabitedZstTy, 0, 1, [], hpid, hb, hfn, rfl, rfl, hA⟩
  | union fields S al id mrBytes _ _ hfn hpid hb _ _ _ hlen hA _ =>
    exact ⟨id, mrUnionTy fields S al, S, al, mrBytes, hpid, hb, hfn,
      Type_layout_mrUnionTy fields S al, hlen, hA⟩

/-- Frame-wide local agreement extending `LocalsOkA` to support `Type.Union`
(`mrUnionTy` + `MiniRustUnionBytesRel`) and 0-byte ZST locals alongside standard
`LocalStorage` locals (`R-d`). -/
structure LocalsOkWithUnions (body : CapturedMir) (f : Gen.Function) (ctx : Ctx)
    (al : List Nat) (locals : List LocalSlot) (lm : Map Gen.LocalName Ptr)
    (allocs : List Gen.Allocation) : Prop where
  nlocals : locals.length = body.localDecls.length
  base : ∃ R, allocs = ctx.base ++ R
  keysNodup : (lm.entries.map Prod.fst).Nodup
  keysLocal : ∀ e ∈ lm.entries, ∃ i, i < body.localDecls.length ∧ e.1 = localName i
  live : ∀ (i : Nat) slot, locals[i]? = some slot →
    ((mapGet lm (localName i)).isSome = true ↔ (slot ≠ .dead ∨ i ∈ al))
  storage : ∀ (i : Nat) d slot p, body.localDecls[i]? = some d → locals[i]? = some slot →
    mapGet lm (localName i) = some p → LocalStorageWithUnions f ctx allocs body.layouts i d slot p
  inj : ∀ (i j : Nat) p q, mapGet lm (localName i) = some p → mapGet lm (localName j) = some q →
    p.provenance = q.provenance → i = j
  owned : ∀ (id : Nat) a, allocs[id]? = some a → a.live = true → ctx.base.length ≤ id →
    ∃ (i : Nat) (p : Ptr), mapGet lm (localName i) = some p ∧ p.provenance = some (⟨(id : Int)⟩, ())

/-- Every `LocalsOkA` state embeds into `LocalsOkWithUnions`. -/
theorem LocalsOkA.toWithUnions {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {al : List Nat} {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr}
    {allocs : List Gen.Allocation}
    (hf : FnLocalsSpec body f)
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true)
    (h : LocalsOkA body ctx al locals lm allocs) :
    LocalsOkWithUnions body f ctx al locals lm allocs where
  nlocals := h.nlocals
  base := h.base
  keysNodup := h.keysNodup
  keysLocal := h.keysLocal
  live := h.live
  storage i d slot p hd hs hp :=
    .base (hf.2 i d hd).2 (hdeclsOk d (List.mem_of_getElem? hd))
      (h.slots i d slot hd hs) (h.storage i d slot p hd hs hp)
  inj := h.inj
  owned := h.owned

theorem LocalsOkWithUnions.teardown {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {al : List Nat} {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr}
    {A : List Gen.Allocation}
    (hlo : LocalsOkWithUnions body f ctx al locals lm A) :
    (lm.entries.map (fun e => provId e.2)).Nodup ∧
    (∀ e ∈ lm.entries, ∃ T sz aln a, mapGet f.locals e.1 = some T ∧
      Interp.Type.layout T = .ok (.Sized ⟨sz⟩ ⟨aln⟩) ∧
      e.2.provenance = some (⟨(provId e.2 : Int)⟩, ()) ∧ A[provId e.2]? = some a ∧
      a.live = true ∧ a.addr = e.2.addr ∧ a.kind = .Stack ∧ a.data.length = sz ∧
      a.align = ⟨aln⟩) ∧
    (∀ id ∈ lm.entries.map (fun e => provId e.2), ctx.base.length ≤ id) ∧
    (∀ (id : Nat) a, A[id]? = some a → a.live = true → ctx.base.length ≤ id →
      id ∈ lm.entries.map (fun e => provId e.2)) := by
  have hentry : ∀ e ∈ lm.entries, ∃ i d slot, body.localDecls[i]? = some d ∧
      locals[i]? = some slot ∧ e.1 = localName i ∧ mapGet lm (localName i) = some e.2 := by
    intro e he
    obtain ⟨i, hi, hei⟩ := hlo.keysLocal e he
    have hil : i < locals.length := by rw [hlo.nlocals]; exact hi
    refine ⟨i, _, _, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hil, hei, ?_⟩
    rw [← hei]
    exact mapGet_of_mem_nodup (by simpa using he) hlo.keysNodup
  have hstore : ∀ e ∈ lm.entries, ∃ i T sz aln data,
      e.1 = localName i ∧ mapGet lm (localName i) = some e.2 ∧
      e.2.provenance = some (⟨(provId e.2 : Int)⟩, ()) ∧ ctx.base.length ≤ provId e.2 ∧
      mapGet f.locals (localName i) = some T ∧
      Interp.Type.layout T = .ok (.Sized ⟨sz⟩ ⟨aln⟩) ∧
      data.length = sz ∧
      A[provId e.2]? = some (stackAlloc e.2.addr ⟨.Unsigned, ⟨aln⟩⟩ data) := by
    intro e he
    obtain ⟨i, d, slot, hd, hs, hei, hmg⟩ := hentry e he
    obtain ⟨id, T, sz, aln, data, hpid, hb, hfn, hlay, hlen, hA⟩ :=
      (hlo.storage i d slot e.2 hd hs hmg).teardown_entry
    rw [provId_of hpid]
    exact ⟨i, T, sz, aln, data, hei, hmg, hpid, hb, hfn, hlay, hlen, hA⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply nodup_map_of_inj_on _ _ (nodup_of_map Prod.fst hlo.keysNodup)
    intro x hx y hy hxy
    obtain ⟨i, _, _, _, _, hxi, hmx, hpx, _, _, _, _, _⟩ := hstore x hx
    obtain ⟨j, _, _, _, _, hyj, hmy, hpy, _, _, _, _, _⟩ := hstore y hy
    have hij : i = j := hlo.inj i j x.2 y.2 hmx hmy (by rw [hpx, hpy, hxy])
    subst hij
    have hv : x.2 = y.2 := by rw [hmx] at hmy; exact Option.some.inj hmy
    obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
    simp only at hxi hyj hv
    rw [hxi, hyj, hv]
  · intro e he
    obtain ⟨i, T, sz, aln, data, hei, _, hpid, _, hfn, hlay, hlen, hA⟩ := hstore e he
    exact ⟨T, sz, aln, _, by rw [hei]; exact hfn, hlay, hpid, hA, rfl, rfl, rfl, hlen, rfl⟩
  · intro id hid
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hid
    obtain ⟨_, _, _, _, _, _, _, _, hb, _, _, _, _⟩ := hstore e he
    exact hb
  · intro id a hA hlive hb
    obtain ⟨i, q, hq, hqid⟩ := hlo.owned id a hA hlive hb
    exact List.mem_map.mpr ⟨(localName i, q), mapGet_mem hq, provId_of hqid⟩

/-- Machine-level state relation extending `StateRelN` with
`LocalsOkWithUnions` (`R-d`), allowing `Type.Union` locals (`mrUnionTy` +
`MiniRustUnionBytesRel`) and 0-byte ZST locals (`()`, `[(); N]`, `VoidZst`) to
coexist with scalar/fragment locals across multi-step runs and `Return`.
Here `mStmt` is MiniRust's statement index inside `bbName s.frame.blockIdx`,
allowing `StorageLive` prologues or `Deinit + Assign` union aggregate lowerings
to advance `mStmt` independently of `s.frame.stmtIdx`. -/
structure StateRelWithUnionsAt (body : CapturedMir) (f : Gen.Function) (ctx : Ctx)
    (al : List Nat) (s : MachineState) (view : List LocalSlot)
    (lm : Map Gen.LocalName Ptr) (mStmt : Nat) (m : Mach) : Prop where
  shape : Shape m ctx [ctx.caller, calleeFrameL f ctx lm s.frame.blockIdx mStmt]
    m.mem.memory.allocations
  retName : f.ret = localName 0
  locs : LocalsOkWithUnions body f ctx al view lm m.mem.memory.allocations
  blk : s.frame.blockIdx < body.basicBlocks.length
  stmt : ∀ bb, body.basicBlocks[s.frame.blockIdx]? = some bb → s.frame.stmtIdx ≤ bb.statements.length
  stale : StaleOk body s.frame.locals view s.frame.blockIdx s.frame.stmtIdx
  retLive : view[0]? ≠ some .dead
  ret : ∀ d, body.localDecls[0]? = some d → RetPlaceOk ctx (tyOf d body.layouts) (itOf d body.layouts)
  baseLow : BaseLow ctx
  borrows : s.memory.borrows = []
  callStack : s.memory.callStack = []
  activeCallee : s.memory.activeCallee = none
  protectors : s.memory.activeProtectors = []
  callerLocals : s.memory.callerLocals = []

/-- Existentially packaged `StateRelWithUnionsAt`. -/
def StateRelWithUnions (body : CapturedMir) (f : Gen.Function) (ctx : Ctx)
    (s : MachineState) (m : Mach) : Prop :=
  ∃ al view lm mStmt, StateRelWithUnionsAt body f ctx al s view lm mStmt m

/-- Every borrow-free `StateRelN` (with `ctx.ptrTargets = fun _ => none`, the
default on `Ctx`) embeds into `StateRelWithUnions`. -/
theorem StateRelN.toStateRelWithUnions {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {s : MachineState} {m : Mach}
    (hf : FnLocalsSpec body f)
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true)
    (hbor : s.memory.borrows = [])
    (hpt : ctx.ptrTargets = fun _ => none)
    (h : StateRelN body f ctx s m) :
    StateRelWithUnions body f ctx s m := by
  obtain ⟨view, lm, hrel, hthr, hlo, _, _⟩ := h
  rw [hbor, ctxWithBorrows_nil] at hlo
  have hctx : { ctx with ptrTargets := fun _ => none } = ctx := by
    cases ctx; dsimp only at hpt; subst hpt; rfl
  rw [hctx] at hlo
  exact ⟨alwaysStorageLiveLocals body, view, lm, s.frame.stmtIdx, {
    shape := ⟨hthr, hrel.active, rfl⟩
    retName := hf.1
    locs := hlo.toWithUnions hf hdeclsOk
    blk := hrel.blk
    stmt := hrel.stmt
    stale := hrel.stale
    retLive := hrel.retLive
    ret := hrel.ret
    baseLow := hrel.baseLow
    borrows := hbor
    callStack := hrel.callStack
    activeCallee := hrel.activeCallee
    protectors := hrel.protectors
    callerLocals := hrel.callerLocals }⟩

/-- **`Terminator::Return` on `StateRelWithUnionsAt` (`R-d`)**:
When `_0` is a scalar return local (`(scalarTypeOf d0.ty).isSome = true`),
`evalReturn` loads `_0`, deallocates every live local in `lm` (including all
`mrUnionTy` union allocations and 0-byte ZST allocations) via `deallocAll_sized`,
writes the return value to `ctx.retPtr`, and establishes `ReturnRel`! -/
theorem evalReturn_withUnions {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {al : List Nat} {s : MachineState} {view : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} {mStmt : Nat} {m : Mach}
    (h : StateRelWithUnionsAt body f ctx al s view lm mStmt m)
    {d0 : LocalDecl} (hd0 : body.localDecls[0]? = some d0)
    (h0scalar : (scalarTypeOf d0.ty).isSome = true) :
    (∀ v, view[0]? = some (.init v) →
      ∃ m', evalReturn m = .ok m' ∧ m'.active_thread = 0 ∧ ReturnRel body ctx s v m') ∧
    (view[0]? = some .uninit → ∃ msg, evalReturn m = .error (.ub msg)) := by
  have hdScalar : scalarTypeOf d0.ty = some (tyOf d0 body.layouts) := by
    obtain ⟨T0, hT0⟩ := Option.isSome_iff_exists.mp h0scalar
    exact (tyOf_of_scalarTypeOf hT0) ▸ hT0
  have hnp0 : isPtrTy d0.ty = false := isPtrTy_false_of_scalarTypeOf hdScalar
  obtain ⟨r0, a0, hp, hr0, hlive, haddrr, hlenr, halr⟩ := h.ret d0 hd0
  have hact : activeThread m = .ok (thread1 ctx [ctx.caller, calleeFrameL f ctx lm s.frame.blockIdx mStmt]) := by
    simp [activeThread, listIndex, h.shape.threads, h.shape.active]
  have hs3 : Shape { m with threads := [thread1 ctx [ctx.caller]] } ctx [ctx.caller]
      m.mem.memory.allocations := ⟨rfl, h.shape.active, rfl⟩
  have hstore0 : ∀ slot0, view[0]? = some slot0 → slot0 ≠ .dead →
      ∃ (p0 : Ptr) (id0 : Nat),
        mapGet f.locals (localName 0) = some (tyOf d0 body.layouts) ∧
        LocalTy (tyOf d0 body.layouts) (itOf d0 body.layouts) ∧
        DeclSlotOk d0 slot0 body.layouts ∧
        mapGet lm (localName 0) = some p0 ∧
        p0.provenance = some (⟨(id0 : Int)⟩, ()) ∧
        Align.is_aligned ⟨(itOf d0 body.layouts).size.bytes⟩ p0.addr = true ∧
        m.mem.memory.allocations[id0]? =
          some (stackAlloc p0.addr (itOf d0 body.layouts) (declSlotData d0 slot0 body.layouts)) := by
    intro slot0 hs0 hne
    have hsome : (mapGet lm (localName 0)).isSome = true := (h.locs.live 0 slot0 hs0).mpr (.inl hne)
    obtain ⟨p0, hp0⟩ := Option.isSome_iff_exists.mp hsome
    have hls0 := h.locs.storage 0 d0 slot0 p0 hd0 hs0 hp0
    cases hls0 with
    | base hfn0 hdok0 hsl0 hst0 =>
      obtain ⟨id0, hpid0, _, haddr0, _, _, hif0⟩ := hst0
      simp only [hnp0, Bool.false_eq_true, ↓reduceIte] at hif0
      exact ⟨p0, id0, hfn0, localTy_of_declOk hdok0, hsl0, hp0, hpid0,
        by simp only [Align.is_aligned, haddr0.1]; rfl, hif0⟩
    | zstUnit _ hk0 =>
      obtain ⟨_, ⟨k0, _⟩, _⟩ := d0; dsimp only at hk0; subst hk0; cases h0scalar
    | zstArray _ _ hk0 =>
      obtain ⟨_, ⟨k0, _⟩, _⟩ := d0; dsimp only at hk0; subst hk0; cases h0scalar
    | zstUninhabited _ hns => rw [h0scalar] at hns; cases hns
    | union _ _ _ _ _ hns => rw [h0scalar] at hns; cases hns
  have hprefix : ∀ (p0 : Ptr) (hfn0 : mapGet f.locals (localName 0) = some (tyOf d0 body.layouts))
      (hlt0 : LocalTy (tyOf d0 body.layouts) (itOf d0 body.layouts)),
      mapGet lm (localName 0) = some p0 → evalReturn m = (do
        let (retVal, m4) ← typedLoad { m with threads := [thread1 ctx [ctx.caller]] } p0
          (tyOf d0 body.layouts) ⟨(itOf d0 body.layouts).size.bytes⟩ .None
        let (frame, cm) ← deallocAll lm.entries.length
          (calleeFrameL f ctx lm s.frame.blockIdx mStmt) m4.mem
        let m5 := { m4 with mem := cm }
        match frame.stack_pop_action with
        | .BottomOfStack => terminateActiveThread m5
        | .BackToCaller nextBlock _ callerRetPtr => do
          let t ← activeThread m5
          if t.stack.length = 0 then specPanic "assertion failed: self.active_thread().stack.len() > 0"
          else do
            let m6 ← typedStore m5 callerRetPtr retVal (tyOf d0 body.layouts)
              ⟨(itOf d0 body.layouts).size.bytes⟩ .None
            match nextBlock with
            | some nb => jumpToBlock m6 nb
            | none => ub "return from a function where caller did not specify next block") := by
    intro p0 hfn0 hlt0 hp0
    simp only [evalReturn, hact, ok_bind, thread1, List.getLast?_cons_cons, List.getLast?_singleton,
      listSet, h.shape.active, h.shape.threads]
    simp [calleeFrameL, h.retName, mapIndex, hfn0, hlt0.layout, expect_align_sized, hp0]
    rfl
  constructor
  · intro v hv
    obtain ⟨p0, id0, hfn0, hlt0, hsl0, hp0, hpid0, hal0, hA0⟩ := hstore0 _ hv (by simp)
    have hslot0 : SlotOk (tyOf d0 body.layouts) (.init v) :=
      (DeclSlotOk_of_scalarTypeOf hdScalar (.init v)).mp hsl0
    obtain ⟨m4, hm4, hs4⟩ := typedLoad_ptr_localTy hs3 p0 id0 hpid0 d0 hdScalar v hslot0 hA0 _ hal0
    obtain ⟨hidnd, hok, hlow, hown⟩ := h.locs.teardown
    obtain ⟨cm5, hcm5, hcm5mem⟩ := deallocAll_sized lm.entries.length
      (calleeFrameL f ctx lm s.frame.blockIdx mStmt) m4.mem lm.entries (Nat.le_refl _) rfl
      h.locs.keysNodup hidnd
      (by
        intro e he
        obtain ⟨T, sz, aln, a', h1, h2, h3, h4, h5⟩ := hok e he
        exact ⟨T, sz, aln, a', h1, h2, h3, by rw [hs4.allocs]; exact h4, h5⟩)
    obtain ⟨R0, hR0⟩ := h.locs.base
    have hall : ∀ (j : Nat) b, R0[j]? = some b → b.live = true →
        ctx.base.length + j ∈ lm.entries.map (fun e => provId e.2) := by
      intro j b hb hlb
      refine hown (ctx.base.length + j) b ?_ hlb (by omega)
      rw [hR0, List.getElem?_append_right (by omega)]
      simpa using hb
    obtain ⟨R, hRk, hRdead⟩ := killAt_append_dead ctx.base R0 _ hlow hall
    rw [hs4.allocs, hR0, hRk] at hcm5mem
    have hs5 : Shape { m4 with mem := cm5 } ctx [ctx.caller] (ctx.base ++ R) :=
      ⟨hs4.threads, hs4.active, hcm5mem⟩
    have hact5 : activeThread { m4 with mem := cm5 } = .ok (thread1 ctx [ctx.caller]) := by
      simp [activeThread, listIndex, hs4.threads, hs4.active]
    obtain ⟨acc, hst⟩ := typedStore_base_localTy hs5 ctx.retPtr r0 a0 hp hr0 hlive haddrr d0 hdScalar
      hlenr v hslot0 ⟨(itOf d0 body.layouts).size.bytes⟩ (by simp only [Align.is_aligned, halr]; rfl)
    have hs6 := withMem_shape
      (allocs' := ctx.base.set r0 { a0 with data := declSlotData d0 (.init v) body.layouts } ++ R) hs5 acc
    obtain ⟨m7, hm7, hs7⟩ := mutateCurFrame_single hs6
      (fun fr => { fr with next_block := ctx.nextBlock, next_stmt := 0 })
    refine ⟨m7, ?_, hs7.active, ⟨r0, a0, d0, R, hd0, hslot0, hp, hr0, hs7.threads, hs7.allocs, hRdead⟩⟩
    rw [hprefix p0 hfn0 hlt0 hp0, hm4]
    simp only [ok_bind]
    rw [hcm5]
    simp only [ok_bind, calleeFrameL, hact5, thread1, hst]
    simp [jumpToBlock, hm7]
  · intro hu
    obtain ⟨p0, id0, hfn0, hlt0, _, hp0, hpid0, hal0, hA0⟩ := hstore0 _ hu (by simp)
    obtain ⟨msg, hmsg⟩ := typedLoad_ptr_localTy_uninit hs3 p0 id0 hpid0 d0 hdScalar hA0 _ hal0
    exact ⟨msg, by rw [hprefix p0 hfn0 hlt0 hp0, hmsg]; rfl⟩

/-- **`step_return_withUnions` (`R-d`)**:
On a `StateRelWithUnionsAt` state at the end of `bb` (`s.frame.stmtIdx = bb.statements.length`,
`mStmt = tb.statements.length`) with `bb.terminator.kind = .return_` and `tb.terminator = .Return`:
1. When `s.frame.locals[0]? = view[0]? = some (.init v)`, `stepMirFn body s` returns
   `.ret (.normal (v, ...))` and `Interp.step m` succeeds with `ReturnRel body ctx s v m'`;
2. When `s.frame.locals[0]? = view[0]? = some .uninit`, `stepMirFn body s = MirStepNode.fail .ub`
   and `Interp.step m = .error (.ub msg)`. -/
theorem step_return_withUnions {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {al : List Nat} {s : MachineState} {view : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} {mStmt : Nat} {m : Mach}
    {bb : BasicBlockData} {tb : Gen.BasicBlock} {d0 : LocalDecl}
    (h : StateRelWithUnionsAt body f ctx al s view lm mStmt m)
    (hphase : body.phase = .runtimePostCleanup)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hstmt_end : s.frame.stmtIdx = bb.statements.length)
    (hk : bb.terminator.kind = .return_)
    (hgetb : mapGet f.blocks (bbName s.frame.blockIdx) = some tb)
    (hmstmt_end : mStmt = tb.statements.length)
    (htt : tb.terminator = .Return)
    (hd0 : body.localDecls[0]? = some d0)
    (h0scalar : (scalarTypeOf d0.ty).isSome = true)
    (h0eq : s.frame.locals[0]? = view[0]?) :
    (∀ v, view[0]? = some (.init v) →
      stepMirFn body s =
        MirStepNode.retNormal v
          { s.memory with
            borrows := MirSemantics.disableFrameBorrows s.memory.borrows 0 s.frame.locals.length } ∧
      ∃ m', Interp.step m = .ok m' ∧ ReturnRel body ctx s v m') ∧
    (view[0]? = some .uninit →
      stepMirFn body s = MirStepNode.fail .ub ∧
      ∃ msg, Interp.step m = .error (.ub msg)) := by
  have hframe0 : StateRelWithUnionsAt body f ctx al s view lm mStmt (resetPick m) :=
    { h with shape := resetPick_shape h.shape }
  obtain ⟨hretOk, hretUb⟩ := evalReturn_withUnions hframe0 hd0 h0scalar
  have hstepA := stepMirFn_term body s bb h.activeCallee hphase hbb hstmt_end
  have hstepM := step_callee h.shape tb hgetb
  have hif : ((mStmt : Nat) : Int) = (tb.statements.length : Int) := by rw [hmstmt_end]
  refine ⟨fun v hv => ?_, fun hu => ?_⟩
  · have hsA : s.frame.locals[0]? = some (.init v) := h0eq.trans hv
    have hvInit : valueContainsUninit v = false := by
      have hsome : (mapGet lm (localName 0)).isSome = true :=
        (h.locs.live 0 (.init v) hv).mpr (.inl (by simp))
      obtain ⟨p0, hp0⟩ := Option.isSome_iff_exists.mp hsome
      cases h.locs.storage 0 d0 (.init v) p0 hd0 hv hp0 with
      | base _ _ hsl0 _ => exact declSlotOk_valueContainsUninit hsl0
      | zstUnit _ hk0 =>
        obtain ⟨_, ⟨k0, _⟩, _⟩ := d0; dsimp only at hk0; subst hk0; cases h0scalar
      | zstArray _ _ hk0 =>
        obtain ⟨_, ⟨k0, _⟩, _⟩ := d0; dsimp only at hk0; subst hk0; cases h0scalar
      | zstUninhabited _ hns => rw [h0scalar] at hns; cases hns
      | union _ _ _ _ _ hns => rw [h0scalar] at hns; cases hns
    have hA : stepMirFn body s =
        MirStepNode.retNormal v
          { s.memory with
            borrows := MirSemantics.disableFrameBorrows s.memory.borrows 0 s.frame.locals.length } := by
      rw [hstepA]
      simp [MirSemantics.evalTerminator, hk, get?, hsA, hvInit, h.callStack, h.protectors,
        MirSemantics.hasFrameDeallocProtectorConflict]
      rfl
    obtain ⟨m', hm', hact', hR⟩ := hretOk v hv
    have hchk : CM.check_data_races m'.mem m'.active_thread
        (setInsert m.synchronized_threads 0, m.mem.accesses) = .ok () := by
      rw [hact']; exact check_ok _ _ _
    exact ⟨hA, m', by simp [hstepM, hif, htt, Interp.evalTerminator, hm', ok_bind, hchk], hR⟩
  · have hsA : s.frame.locals[0]? = some .uninit := h0eq.trans hu
    have hA : stepMirFn body s = MirStepNode.fail .ub := by
      rw [hstepA]
      simp [MirSemantics.evalTerminator, hk, get?, hsA]
    obtain ⟨msg, hmsg⟩ := hretUb hu
    exact ⟨hA, msg, by simp [hstepM, hif, htt, Interp.evalTerminator, hmsg, bind, Except.bind]⟩

theorem LocalStorage.set_other {ctx : Ctx} {allocs : List Gen.Allocation}
    {d : LocalDecl} {slot : LocalSlot} {p : Ptr} {layouts : Layout.LayoutTable}
    {k : Nat} {a : Gen.Allocation}
    (hls : LocalStorage ctx allocs d slot p layouts)
    (hne : ∀ (id : Nat), p.provenance = some (⟨(id : Int)⟩, ()) → k ≠ id) :
    LocalStorage ctx (allocs.set k a) d slot p layouts := by
  obtain ⟨id, hpid, hb, haddr, hlt64, hcls, hif⟩ := hls
  have hkid : k ≠ id := hne id hpid
  refine ⟨id, hpid, hb, haddr, hlt64, hcls, ?_⟩
  by_cases hptr : isPtrTy d.ty = true
  · simp only [hptr, ↓reduceIte] at hif ⊢
    split at hif
    · obtain ⟨tAddr, tProv, h1, h2, hA⟩ := hif
      exact ⟨tAddr, tProv, h1, h2, by rw [List.getElem?_set_ne hkid]; exact hA⟩
    · rw [List.getElem?_set_ne hkid]; exact hif
  · simp only [hptr, Bool.false_eq_true, ↓reduceIte] at hif ⊢
    rw [List.getElem?_set_ne hkid]; exact hif

theorem LocalStorageWithUnions.set_other
    {f : Gen.Function} {ctx : Ctx} {allocs : List Gen.Allocation}
    {layouts : Layout.LayoutTable} {i : Nat} {d : LocalDecl} {slot : LocalSlot} {p : Ptr}
    {k : Nat} {a : Gen.Allocation}
    (h : LocalStorageWithUnions f ctx allocs layouts i d slot p)
    (hne : ∀ (id : Nat), p.provenance = some (⟨(id : Int)⟩, ()) → k ≠ id) :
    LocalStorageWithUnions f ctx (allocs.set k a) layouts i d slot p := by
  cases h with
  | base hfn hlt hsl hls =>
    exact .base hfn hlt hsl (hls.set_other hne)
  | zstUnit id hk hfn hpid hb h0 h64 hsl hA =>
    exact .zstUnit id hk hfn hpid hb h0 h64 hsl (by rw [List.getElem?_set_ne (hne id hpid)]; exact hA)
  | zstArray N id hk hfn hpid hb h0 h64 hsl hA =>
    exact .zstArray N id hk hfn hpid hb h0 h64 hsl (by rw [List.getElem?_set_ne (hne id hpid)]; exact hA)
  | zstUninhabited id hns hfn hpid hb h0 h64 hsl hA =>
    exact .zstUninhabited id hns hfn hpid hb h0 h64 hsl (by rw [List.getElem?_set_ne (hne id hpid)]; exact hA)
  | union fields S al id mrBytes hns hpos hfn hpid hb hal h0 h64 hlen hA hrel =>
    exact .union fields S al id mrBytes hns hpos hfn hpid hb hal h0 h64 hlen
      (by rw [List.getElem?_set_ne (hne id hpid)]; exact hA) hrel

/-- **Lifting `step_union_whole_copy_minirust_simulation` onto `StateRelWithUnionsAt` (`R-d`)**:
On a `StateRelWithUnionsAt` state (`s.frame.locals = view`, `m.mem.memory.allocations = ctx.base ++ L`)
where union local `u` holds `.init val` with bytes `mrBytes` (including any `.Uninit`
padding bytes) and union local `w ≠ 0` is live, `_w = copy _u` steps in lockstep in
Anneal (`stepMirFn body s`) and MiniRust (`Interp.step m`) and preserves
`StateRelWithUnionsAt` (and hence `StateRelWithUnions`)! -/
theorem step_union_whole_copy_stateRelWithUnions
    {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {al : List Nat} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {L : List Gen.Allocation} {mStmt : Nat} {m : Mach}
    {bb : BasicBlockData} {tb : Gen.BasicBlock}
    {u w : Nat} {uDecl wDecl : LocalDecl}
    {fields : List (Gen.Offset × Gen.«Type»)}
    {S align : Nat} {val : MirSemantics.Value} {wSlot : LocalSlot}
    {mrBytes oldBytes : List Byte} {span : String}
    (hphase : body.phase = .runtimePostCleanup)
    (hrel : StateRelWithUnionsAt body f ctx al s s.frame.locals lm mStmt m)
    (hallocs : m.mem.memory.allocations = ctx.base ++ L)
    (hu : MiniRustUnionLocalStorage ctx L f lm body.layouts u uDecl.ty fields S align (.init val) mrBytes)
    (hw : MiniRustUnionLocalStorage ctx L f lm body.layouts w wDecl.ty fields S align wSlot oldBytes)
    (_hdu : body.localDecls[u]? = some uDecl)
    (hdw : body.localDecls[w]? = some wDecl)
    (hty_eq : wDecl.ty = uDecl.ty)
    (hw_nonSc : (scalarTypeOf wDecl.ty).isSome = false)
    (hw0 : w ≠ 0)
    (hu_slot : s.frame.locals[u]? = some (.init val))
    (hw_live : s.frame.locals[w]? = some wSlot)
    (hw_not_dead : wSlot ≠ .dead)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some ⟨.assign ⟨w, []⟩ (.use (.copy ⟨u, []⟩)), span⟩)
    (htb : mapGet f.blocks (bbName s.frame.blockIdx) = some tb)
    (hlt_tb : mStmt < tb.statements.length)
    (htst : tb.statements[mStmt]? =
      some (.Assign (.Local (localName w)) (.Load (.Local (localName u)))))
    (hval : MirSemantics.validateLoadedValue body.layouts body.localDecls (.copy ⟨u, []⟩) val = true)
    (hnoUninit : MirSemantics.valueContainsUninit val = false := by decide) :
    let s' := advanceStmt s (s.frame.locals.set w (.init val)) s.memory
    stepMirFn body s = .tau (.running s') ∧
    ∃ m',
      Interp.step m = .ok m' ∧
      StateRelWithUnionsAt body f ctx al s' s'.frame.locals lm (mStmt + 1) m' ∧
      StateRelWithUnions body f ctx s' m' := by
  have hlt_bb : s.frame.stmtIdx < bb.statements.length := (List.getElem?_eq_some_iff.mp hst).1
  have hstepA_eq := stepMirFn_stmt body s bb _ hrel.activeCallee hphase hbb hst
  -- Reuse `step_union_whole_copy_minirust_simulation` at `mStmt` by re-indexing `s`'s `stmtIdx` for the MiniRust shape!
  let sM : MachineState := { s with frame := { s.frame with stmtIdx := mStmt } }
  have hshM : Shape m ctx [ctx.caller, calleeFrameL f ctx lm sM.frame.blockIdx sM.frame.stmtIdx]
      (ctx.base ++ L) := by
    refine ⟨hrel.shape.threads, hrel.shape.active, hallocs⟩
  have hu' : MiniRustUnionLocalStorage ctx L f lm body.layouts u wDecl.ty fields S align (.init val) mrBytes :=
    hty_eq ▸ hu
  obtain ⟨_, m', hstepM, hsh', hw'⟩ :=
    step_union_whole_copy_minirust_simulation (body := body) (s := sM) (span := span)
      hshM hu' hw hu_slot hw_live hw_not_dead hrel.borrows hrel.protectors hrel.callerLocals
      htb hlt_tb htst hval hnoUninit
  -- And on `s` itself, `evalStmt` is identical apart from advancing `s.frame.stmtIdx`:
  have hw_lt_af : w < s.frame.locals.length := (List.getElem?_eq_some_iff.mp hw_live).1
  have hA : evalStmt s ⟨.assign ⟨w, []⟩ (.use (.copy ⟨u, []⟩)), span⟩
      body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (s.frame.locals.set w (.init val)) s.memory) := by
    have hop : evalOperand s.frame.locals (.copy ⟨u, []⟩) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
        .ok val s.frame.locals := by
      simp [evalOperand, get?, hu_slot, readProjectedValue, hnoUninit]
    have hrv := evalRvalue_use_ok hop hval rfl
    have hinv : MirSemantics.invalidateConflictingBorrows s.memory.borrows w .none
        s.memory.callStack.length = s.memory.borrows := by
      rw [hrel.borrows]; rfl
    simp only [evalStmt, hrv, get?, hw_live, set?, Trusted.Sequence.length, hw_lt_af, ↓reduceIte,
      hrel.protectors, hinv]
    cases wSlot with
    | dead => exact absurd rfl hw_not_dead
    | uninit | init _ => rw [memory_mk_nil_prot s.memory hrel.protectors]
  let L' := L.set w (localAlloc ctx w ⟨.Unsigned, ⟨align⟩⟩ mrBytes)
  let s' := advanceStmt s (s.frame.locals.set w (.init val)) s.memory
  have hw_lt_L : w < L.length := (List.getElem?_eq_some_iff.mp hw.alloc_eq).1
  have hallocs_set : ctx.base ++ L' =
      (ctx.base ++ L).set (ctx.base.length + w) (localAlloc ctx w ⟨.Unsigned, ⟨align⟩⟩ mrBytes) := by
    rw [List.set_append_right _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  have hlocs' : LocalsOkWithUnions body f ctx al s'.frame.locals lm m'.mem.memory.allocations := by
    rw [hsh'.allocs]
    refine {
      nlocals := by simp [s', advanceStmt, hrel.locs.nlocals]
      base := ⟨L', rfl⟩
      keysNodup := hrel.locs.keysNodup
      keysLocal := hrel.locs.keysLocal
      live := fun i sl hsl => by
        simp only [s', advanceStmt, List.getElem?_set] at hsl
        by_cases hwi : w = i
        · subst hwi
          simp only [↓reduceIte, hw_lt_af, Option.some.injEq] at hsl
          subst hsl
          have h1 := (hrel.locs.live w wSlot hw_live).mpr (.inl hw_not_dead)
          exact ⟨fun _ => .inl (by simp), fun _ => h1⟩
        · simp only [hwi, ↓reduceIte] at hsl
          exact hrel.locs.live i sl hsl
      storage := fun i di sli pi hdi hsli hpi => by
        simp only [s', advanceStmt, List.getElem?_set] at hsli
        by_cases hwi : w = i
        · subst hwi
          simp only [↓reduceIte, hw_lt_af, Option.some.injEq] at hsli
          subst hsli
          rw [hdw] at hdi; cases hdi
          rw [hw.lm_ptr] at hpi; cases hpi
          exact LocalStorageWithUnions.ofMiniRustUnionLocalStorage hw_nonSc hw'
        · simp only [hwi, ↓reduceIte] at hsli
          have h0 := hrel.locs.storage i di sli pi hdi hsli hpi
          rw [hallocs] at h0
          rw [hallocs_set]
          refine h0.set_other (fun id hpid hkid => hwi ?_)
          subst hkid
          exact hrel.locs.inj w i (localPtr ctx w) pi hw.lm_ptr hpi (by rw [hpid]; rfl)
      inj := hrel.locs.inj
      owned := fun id a hA hlive_a hb => by
        rw [hallocs_set, List.getElem?_set] at hA
        by_cases hk : ctx.base.length + w = id
        · subst hk
          exact ⟨w, localPtr ctx w, hw.lm_ptr, rfl⟩
        · simp only [hk, ↓reduceIte] at hA
          have hA0 : m.mem.memory.allocations[id]? = some a := by rw [hallocs]; exact hA
          exact hrel.locs.owned id a hA0 hlive_a hb }
  have hrel' : StateRelWithUnionsAt body f ctx al s' s'.frame.locals lm (mStmt + 1) m' := {
    shape := ⟨hsh'.threads, hsh'.active, rfl⟩
    retName := hrel.retName
    locs := hlocs'
    blk := hrel.blk
    stmt := fun bb' hbb' => by
      dsimp only [s', advanceStmt] at hbb' ⊢
      rw [hbb] at hbb'; cases hbb'; exact Nat.succ_le_of_lt hlt_bb
    stale := ⟨rfl, fun _ hj => absurd rfl hj⟩
    retLive := by
      simp only [s', advanceStmt, List.getElem?_set_ne hw0]
      exact hrel.retLive
    ret := hrel.ret
    baseLow := hrel.baseLow
    borrows := hrel.borrows
    callStack := hrel.callStack
    activeCallee := hrel.activeCallee
    protectors := hrel.protectors
    callerLocals := hrel.callerLocals }
  exact ⟨by rw [hstepA_eq, hA]; rfl, m', hstepM, hrel', ⟨al, s'.frame.locals, lm, mStmt + 1, hrel'⟩⟩

/-- Step relation parameterized by a union-aware state invariant `Inv` (`Inv s m → StateRelWithUnions body f ctx s m`),
supporting 1-or-more MiniRust steps per Anneal step (`1 ≤ k`, covering 1-step
statement lockstep such as `_w = copy _u` as well as `StorageLive` prologues,
`Deinit + Assign` union aggregate lowerings, and `StorageDead` epilogues before `Return`). -/
def StepRelWithUnionsInv (Inv : MachineState → Mach → Prop)
    (body : CapturedMir) (ctx : Ctx) (s : MachineState) (a : MirStepNode) (m : Mach) : Prop :=
  match a with
  | .tau (.running s') => ∃ k m', 1 ≤ k ∧ Interp.steps k m = .ok m' ∧ Inv s' m'
  | .vis (.inr (.inl (.emit _))) kCont =>
    ∃ s' k m', 1 ≤ k ∧ kCont PUnit.unit = .running s' ∧ Interp.steps k m = .ok m' ∧ Inv s' m'
  | .ret (.normal (v, _)) => ∃ k m', 1 ≤ k ∧ Interp.steps k m = .ok m' ∧ ReturnRel body ctx s v m'
  | .vis (.inl (.fail .ub)) _ => ∃ k msg, 1 ≤ k ∧ Interp.steps k m = .error (.ub msg)
  | _ => False

/-- **Multi-step execution prefix lift for `StateRelWithUnions` (`R-d`)**:
Given any invariant `Inv` refining `StateRelWithUnions body f ctx` that is
closed under `StepRelWithUnionsInv Inv body ctx`, every Anneal execution prefix
`Reaches (mirTree body s) tr u` is matched by finitely many MiniRust steps to a
`StateRelWithUnions`-related state.

**Explicit scope disclosure (conditional simulation schema):**
This theorem is a **conditional simulation schema** parameterized by an
externally supplied invariant triple `(Inv, hinv, hstep)` (instantiated on
concrete exit-only witnesses in `MiniRustSpec.Correspondence.WitnessUnionAssert`),
NOT an unconditional or universal arbitrary-CFG lowering theorem for
union-bearing bodies. -/
theorem reaches_rel_withUnions {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    (Inv : MachineState → Mach → Prop)
    (hinv : ∀ s m, Inv s m → StateRelWithUnions body f ctx s m)
    (hstep : ∀ s m, Inv s m → StepRelWithUnionsInv Inv body ctx s (stepMirFn body s) m)
    {t u : Trusted.ITree.ITree MirEffect MirOutcome}
    {tr : List (Trusted.Effect.Event MirEffect)} (h : Trusted.ITree.Reaches t tr u) :
    ∀ (s : MachineState) (m : Mach), t = mirTree body s → Inv s m →
      ∃ (n : Nat) (s' : MachineState) (m' : Mach), Interp.steps n m = .ok m' ∧
        Inv s' m' ∧ StateRelWithUnions body f ctx s' m' ∧ u = mirTree body s' := by
  induction h with
  | refl t =>
    intro s m ht hi
    exact ⟨0, s, m, rfl, hi, hinv s m hi, ht⟩
  | tau hobs _ ih =>
    intro s m ht hi
    subst ht
    have hsr := hstep s m hi
    rw [mirTree_observe_local] at hobs
    generalize stepMirFn body s = node at hsr hobs
    cases node with
    | ret r => simp [Trusted.ITree.ITreeF.map] at hobs
    | vis i k => simp [Trusted.ITree.ITreeF.map] at hobs
    | tau x =>
      simp only [Trusted.ITree.ITreeF.map, Trusted.ITree.ITreeF.tau.injEq] at hobs
      cases x with
      | running s1 =>
        obtain ⟨k1, m1, _, hm1, hi1⟩ := hsr
        obtain ⟨n, s', m', hsteps, hi', hrel', hu⟩ := ih s1 m1 hobs.symm hi1
        exact ⟨k1 + n, s', m', by rw [steps_add, hm1, ok_bind, hsteps], hi', hrel', hu⟩
      | halted _ => exact False.elim hsr
      | faulted _ => exact False.elim hsr
  | vis hobs hnf o _ ih =>
    intro s m ht hi
    subst ht
    have hsr := hstep s m hi
    rw [mirTree_observe_local] at hobs
    generalize stepMirFn body s = node at hsr hobs
    cases node with
    | ret r => simp [Trusted.ITree.ITreeF.map] at hobs
    | tau x => simp [Trusted.ITree.ITreeF.map] at hobs
    | vis i0 k0 =>
      simp only [Trusted.ITree.ITreeF.map] at hobs
      injection hobs with hi0 hk
      subst hi0
      have hk' := eq_of_heq hk
      subst hk'
      cases i0 with
      | inl a => exact False.elim (hnf trivial)
      | inr b =>
        cases b with
        | inr c => exact False.elim hsr
        | inl ob =>
          obtain ⟨s1, k1, m1, _, hk1, hm1, hi1⟩ := hsr
          cases o
          have ht' : Trusted.ITree.ITree.cofix (stepMirState body) (k0 PUnit.unit) =
              mirTree body s1 := by
            rw [hk1]; rfl
          obtain ⟨n, s', m', hsteps, hi', hrel', hu⟩ := ih s1 m1 ht' hi1
          exact ⟨k1 + n, s', m', by rw [steps_add, hm1, ok_bind, hsteps], hi', hrel', hu⟩

/-- **Whole-execution normal return for `StateRelWithUnions` (`R-d`)**:
If Anneal's semantics of `body` from `s` returns `.normal (v, mem)`, MiniRust
from an `Inv`-related `StateRelWithUnions` state reaches `ReturnRel` after
finitely many steps.

**Explicit scope disclosure (conditional simulation schema):**
Conditional on the supplied `(Inv, hinv, hstep)` witness invariant; instantiated
on concrete exit-only `translateFnWithUnions` witnesses (e.g. `wUnionAutoFn`
`bb2` in `WitnessUnionAssert.lean`), rather than establishing universal
arbitrary-CFG lowering for unions. -/
theorem run_ret_withUnions {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    (Inv : MachineState → Mach → Prop)
    (hinv : ∀ s m, Inv s m → StateRelWithUnions body f ctx s m)
    (hstep : ∀ s m, Inv s m → StepRelWithUnionsInv Inv body ctx s (stepMirFn body s) m)
    (s : MachineState) (m : Mach) (hi : Inv s m)
    {tr : List (Trusted.Effect.Event MirEffect)} {v : Value} {mem : MirSemantics.Memory}
    (hret : Trusted.ITree.ReachesRet (mirTree body s) tr (.normal (v, mem))) :
    ∃ (n : Nat) (s' : MachineState) (mPre m' : Mach),
      Interp.steps n m = .ok m' ∧
      StateRelWithUnions body f ctx s' mPre ∧
      ReturnRel body ctx s' v m' := by
  obtain ⟨u, hreach, hu⟩ := hret
  obtain ⟨n1, s', m1, hsteps1, hi', hrel', rfl⟩ :=
    reaches_rel_withUnions Inv hinv hstep hreach s m rfl hi
  have hsr := hstep s' m1 hi'
  rw [mirTree_observe_local] at hu
  generalize stepMirFn body s' = node at hsr hu
  cases node with
  | tau x => simp [Trusted.ITree.ITreeF.map] at hu
  | vis i k => simp [Trusted.ITree.ITreeF.map] at hu
  | ret r =>
    simp only [Trusted.ITree.ITreeF.map, Trusted.ITree.ITreeF.ret.injEq] at hu
    subst hu
    obtain ⟨k2, m', _, hm', hret'⟩ := hsr
    exact ⟨n1 + k2, s', m1, m', by rw [steps_add, hsteps1, ok_bind, hm'], hrel', hret'⟩

/-- **Whole-execution UB for `StateRelWithUnions` (`R-d`)**:
If Anneal's semantics of `body` from `s` reaches `FaultNow`, MiniRust from an
`Inv`-related `StateRelWithUnions` state stops with `.error (.ub msg)` after
finitely many steps.

**Explicit scope disclosure (conditional simulation schema):**
Conditional on the supplied `(Inv, hinv, hstep)` witness invariant; instantiated
on concrete exit-only `translateFnWithUnions` witnesses (e.g. `wUnionAutoFn`
`bb3` in `WitnessUnionAssert.lean`), rather than establishing universal
arbitrary-CFG lowering for unions. -/
theorem run_ub_withUnions {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    (Inv : MachineState → Mach → Prop)
    (hinv : ∀ s m, Inv s m → StateRelWithUnions body f ctx s m)
    (hstep : ∀ s m, Inv s m → StepRelWithUnionsInv Inv body ctx s (stepMirFn body s) m)
    (s : MachineState) (m : Mach) (hi : Inv s m)
    {tr : List (Trusted.Effect.Event MirEffect)} {u : Trusted.ITree.ITree MirEffect MirOutcome}
    (hreach : Trusted.ITree.Reaches (mirTree body s) tr u)
    (hfault : Trusted.ITree.FaultNow u) :
    ∃ (n : Nat) (msg : String), Interp.steps n m = .error (.ub msg) := by
  obtain ⟨t', i, k, htau, hobs, hfi⟩ := hfault
  obtain ⟨n1, s1, m1, h1, hi1, _, rfl⟩ :=
    reaches_rel_withUnions Inv hinv hstep hreach s m rfl hi
  obtain ⟨n2, s2, m2, h2, hi2, _, rfl⟩ :=
    reaches_rel_withUnions Inv hinv hstep (tauStar_reaches_local htau) s1 m1 rfl hi1
  have hsr := hstep s2 m2 hi2
  rw [mirTree_observe_local] at hobs
  generalize stepMirFn body s2 = node at hsr hobs
  cases node with
  | ret r => simp [Trusted.ITree.ITreeF.map] at hobs
  | tau x => simp [Trusted.ITree.ITreeF.map] at hobs
  | vis i0 k0 =>
    simp only [Trusted.ITree.ITreeF.map] at hobs
    injection hobs with hi0 _
    subst hi0
    cases i0 with
    | inr b =>
      cases b with
      | inl _ => exact False.elim hfi
      | inr _ => exact False.elim hfi
    | inl f0 =>
      cases f0 with
      | fail reason =>
        cases reason with
        | ub =>
          obtain ⟨kStep, msg, _, hkStep⟩ := hsr
          exact ⟨(n1 + n2) + kStep, msg, by rw [steps_add, steps_add, h1, ok_bind, h2, ok_bind, hkStep]⟩
        | unsupported | outOfFuel => exact False.elim hsr

end MiniRustSpec.Correspondence
