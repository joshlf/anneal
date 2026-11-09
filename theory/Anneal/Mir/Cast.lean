/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted.MirAst
import Trusted.MirSemantics
import Trusted.Rustc.V2026_06_01.Layout
import Anneal.BitValidity
import Anneal.MirFuelFree

open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirSemantics.RvalueEvalResult
open Anneal.BitValidity
open Anneal.MirFuelFree

namespace Anneal.Mir.Cast

/-- Page offset modulus for pointer address serialization (64 KiB per allocation). -/
def pageOffsetModulus : Nat := 65536

/-- Address computation for a provenance pointer (`CastKind.pointerExposeProvenance`). -/
def ptrToAddress (p : ProvenancePtr) : Nat :=
  Nat.add (Nat.mul p.allocId pageOffsetModulus) p.offsetBytes

/-- Inverse mapping reconstructing a provenance pointer from an integer address. -/
def addressToPtr (addr : Nat) : ProvenancePtr :=
  { allocId := Nat.div addr pageOffsetModulus, offsetBytes := Nat.mod addr pageOffsetModulus }

/-- Exact roundtrip inversion theorem: reconstructing a pointer from its exposed
integer address recovers the exact allocation ID and offset whenever the offset is
within the 64 KiB page boundary. -/
theorem addressToPtr_ptrToAddress_eq (p : ProvenancePtr) (h_off : p.offsetBytes < pageOffsetModulus) :
    addressToPtr (ptrToAddress p) = p := by
  cases p with
  | mk allocId offsetBytes =>
    dsimp [addressToPtr, ptrToAddress, pageOffsetModulus] at *
    have h_pos : 0 < 65536 := by decide
    have h_div : (allocId * 65536 + offsetBytes) / 65536 = allocId := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ h_pos]
      have h_zero : offsetBytes / 65536 = 0 := Nat.div_eq_of_lt h_off
      rw [h_zero, Nat.zero_add]
    have h_mod : (allocId * 65536 + offsetBytes) % 65536 = offsetBytes := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt h_off
    congr <;> assumption

/-- MiniRust exposed provenance model: a list of exposed allocation identifiers. -/
abbrev ExposedProvenance : Type := List Nat

/-- Provenance exposure predicate: an allocation ID is exposed if it is in the list. -/
def isExposed (prov : Nat) (exposed : ExposedProvenance) : Prop :=
  prov ∈ exposed

/-- Expose operation adding an allocation ID to the exposed provenance list. -/
def exposeProv (prov : Nat) (exposed : ExposedProvenance) : ExposedProvenance :=
  if prov ∈ exposed then exposed else prov :: exposed

/-- Exposing a provenance tag guarantees it is in the exposed set. -/
theorem isExposed_exposeProv (prov : Nat) (exposed : ExposedProvenance) :
    isExposed prov (exposeProv prov exposed) := by
  dsimp [isExposed, exposeProv]
  split
  · next h => exact h
  · next h => exact List.Mem.head _

/-- Exposing preserves previously exposed provenance tags. -/
theorem isExposed_of_isExposed (prov other : Nat) (exposed : ExposedProvenance)
    (h : isExposed other exposed) : isExposed other (exposeProv prov exposed) := by
  dsimp [isExposed, exposeProv] at *
  split
  · exact h
  · exact List.Mem.tail _ h

/-- Semantic correspondence for pointer-to-usize cast:
Evaluating `CastKind.pointerExposeProvenance` on a pointer value produces the
exact machine address scalar computed by `ptrToAddress`. -/
theorem ptr_to_usize_cast_step_correspondence
    (ptrVal : ProvenancePtr)
    (locals locals' : List LocalSlot)
    (mem : Memory)
    (op : Operand)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (h_eval : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals = .ok (.ptr ptrVal 8) locals') :
    (match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
     | .ok (.ptr p _) locs =>
       let addr := Nat.add (Nat.mul p.allocId pageOffsetModulus) p.offsetBytes
       ok (.scalar ⟨addr, 8⟩) locs mem
     | .ok (.scalar sc) locs => ok (.scalar ⟨sc.bits, 8⟩) locs mem
     | .ok _ _ => unsupported
     | .ub => ub
     | .unsupported => unsupported) =
    ok (.scalar ⟨ptrToAddress ptrVal, 8⟩) locals' mem := by
  rw [h_eval]
  dsimp [ptrToAddress, pageOffsetModulus]

/-- Determinism of pointer-to-usize cast evaluation:
Given identical pointer values and memory states, the evaluation results are identical. -/
theorem ptr_to_usize_cast_deterministic
    (p1 p2 : ProvenancePtr)
    (locs1 locs2 : List LocalSlot)
    (mem1 mem2 : Memory)
    (h_ptr : p1 = p2)
    (h_locs : locs1 = locs2)
    (h_mem : mem1 = mem2) :
    ok (.scalar ⟨ptrToAddress p1, 8⟩) locs1 mem1 =
    ok (.scalar ⟨ptrToAddress p2, 8⟩) locs2 mem2 := by
  subst h_ptr h_locs h_mem
  rfl

/-- MiniRust step correspondence: Int-to-pointer cast (`pointerWithExposedProvenance`)
reconstructs the provenance pointer corresponding to `addressToPtr`. -/
theorem int_to_ptr_cast_step_correspondence
    (sc : ScalarInt)
    (locals locals' : List LocalSlot)
    (mem : Memory)
    (op : Operand)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (h_eval : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals = .ok (.scalar sc) locals') :
    (match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
     | .ok (.scalar s) locs =>
       let p : ProvenancePtr := {
         allocId := Nat.div s.bits pageOffsetModulus
         offsetBytes := Nat.mod s.bits pageOffsetModulus
       }
       ok (.ptr p 8) locs mem
     | .ok (.ptr ptrVal sz) locs => ok (.ptr ptrVal sz) locs mem
     | .ok _ _ => unsupported
     | .ub => ub
     | .unsupported => unsupported) =
    ok (.ptr (addressToPtr sc.bits) 8) locals' mem := by
  rw [h_eval]
  dsimp [addressToPtr, pageOffsetModulus]

/-- Full roundtrip correspondence theorem between Anneal MIR and MiniRust:
Casting a pointer `p` to `usize` via `pointerExposeProvenance` and then casting the resulting
address back to a pointer via `pointerWithExposedProvenance` recovers the exact original pointer `p`. -/
theorem ptr_usize_ptr_roundtrip_correspondence
    (p : ProvenancePtr)
    (h_off : p.offsetBytes < pageOffsetModulus) :
    addressToPtr (ptrToAddress p) = p :=
  addressToPtr_ptrToAddress_eq p h_off

/-! ## 1. Pointer Width (`PtrWidth`), Integer Widths (`IntWidth`), and Scalar Descriptors (`ScalarTy`) -/

/-- Target machine pointer width (`4` bytes on 32-bit targets, `8` bytes on 64-bit targets),
matching `anneal_mir::ir::PtrWidth`. -/
inductive PtrWidth : Type where
  /-- 32-bit target pointer width (`4` bytes). -/
  | bits32 : PtrWidth
  /-- 64-bit target pointer width (`8` bytes). -/
  | bits64 : PtrWidth
  deriving DecidableEq, Repr, Inhabited

namespace PtrWidth

/-- Size of a thin pointer (`usize`, `isize`, `*const T`, `&T`) in bytes (`4` or `8`). -/
@[reducible]
def byteSize : PtrWidth → Nat
  | .bits32 => 4
  | .bits64 => 8

/-- Width of a thin pointer in bits (`32` or `64`). -/
@[reducible]
def bitWidth (pw : PtrWidth) : Nat :=
  pw.byteSize * 8

/-- Unsigned modulus `2^(8 * pw.byteSize)` for thin pointers and `usize`/`isize` under `pw`. -/
@[reducible]
def modulus (pw : PtrWidth) : Nat :=
  scalarModulus pw.byteSize

theorem byteSize_pos (pw : PtrWidth) : 0 < pw.byteSize := by
  cases pw <;> decide

end PtrWidth

/-- Integer scalar width descriptor matching `anneal_mir::ir::{IntTy, UintTy}` (including
pointer-sized `isize`/`usize`). -/
inductive IntWidth : Type where
  | w8 : IntWidth
  | w16 : IntWidth
  | w32 : IntWidth
  | w64 : IntWidth
  | w128 : IntWidth
  | wsize : IntWidth
  deriving DecidableEq, Repr, Inhabited

namespace IntWidth

/-- Size in bytes of an integer width under target pointer width `pw`. -/
@[reducible]
def byteSize (pw : PtrWidth) : IntWidth → Nat
  | .w8 => 1
  | .w16 => 2
  | .w32 => 4
  | .w64 => 8
  | .w128 => 16
  | .wsize => pw.byteSize

theorem byteSize_pos (pw : PtrWidth) (w : IntWidth) : 0 < w.byteSize pw := by
  cases w <;> cases pw <;> decide

/-- Convert a `Trusted.MirAst.UintTy` to `IntWidth`. -/
@[reducible]
def ofTrustedUintTy : UintTy → IntWidth
  | .u8 => .w8
  | .u16 => .w16
  | .u32 => .w32
  | .u64 => .w64
  | .u128 => .w128
  | .usize => .wsize

/-- Convert a `Trusted.MirAst.IntTy` to `IntWidth`. -/
@[reducible]
def ofTrustedIntTy : IntTy → IntWidth
  | .i8 => .w8
  | .i16 => .w16
  | .i32 => .w32
  | .i64 => .w64
  | .i128 => .w128
  | .isize => .wsize

end IntWidth

/-- Niche-aware scalar and thin-pointer type descriptor for MIR cast and transmute validation,
modeling `anneal_mir::ir::ScalarTy` and `Ty::is_valid_scalar_bits` (including the non-null
reference niche on `Ty::Ref`). -/
inductive ScalarTy : Type where
  /-- 1-byte boolean with validity niche `bits ≤ 1` (`0` or `1`). -/
  | bool : ScalarTy
  /-- 4-byte Unicode scalar value (`0x0000..=0xD7FF` or `0xE000..=0x10FFFF`). -/
  | char : ScalarTy
  /-- Signed two's-complement integer of width `w`. -/
  | int (w : IntWidth) : ScalarTy
  /-- Unsigned integer of width `w`. -/
  | uint (w : IntWidth) : ScalarTy
  /-- Thin raw pointer (`*const T` / `*mut T`) of byte width `pw.byteSize`. -/
  | rawPtr : ScalarTy
  /-- Thin reference (`&T` / `&mut T`) of byte width `pw.byteSize` with non-null niche (`bits ≠ 0`). -/
  | refPtr : ScalarTy
  deriving DecidableEq, Repr, Inhabited

namespace ScalarTy

abbrev i8 : ScalarTy := .int .w8
abbrev i16 : ScalarTy := .int .w16
abbrev i32 : ScalarTy := .int .w32
abbrev i64 : ScalarTy := .int .w64
abbrev i128 : ScalarTy := .int .w128
abbrev isize : ScalarTy := .int .wsize

abbrev u8 : ScalarTy := .uint .w8
abbrev u16 : ScalarTy := .uint .w16
abbrev u32 : ScalarTy := .uint .w32
abbrev u64 : ScalarTy := .uint .w64
abbrev u128 : ScalarTy := .uint .w128
abbrev usize : ScalarTy := .uint .wsize

/-- Size in bytes of `ty` under target pointer width `pw`. -/
@[reducible]
def sizeBytes (pw : PtrWidth) : ScalarTy → Nat
  | .bool => 1
  | .char => 4
  | .int w => w.byteSize pw
  | .uint w => w.byteSize pw
  | .rawPtr => pw.byteSize
  | .refPtr => pw.byteSize

theorem sizeBytes_pos (pw : PtrWidth) (ty : ScalarTy) : 0 < ty.sizeBytes pw := by
  cases ty with
  | bool | char => cases pw <;> decide
  | int w | uint w => exact IntWidth.byteSize_pos pw w
  | rawPtr | refPtr => exact PtrWidth.byteSize_pos pw

/-- True iff `ty` is a pointer or reference descriptor (`.rawPtr` or `.refPtr`). -/
@[reducible]
def isPtr : ScalarTy → Bool
  | .rawPtr | .refPtr => true
  | .bool | .char | .int _ | .uint _ => false

/-- True iff `ty` is an integer descriptor (`.int _` or `.uint _`). -/
@[reducible]
def isIntegral : ScalarTy → Bool
  | .int _ | .uint _ => true
  | .bool | .char | .rawPtr | .refPtr => false

/-- Decidable bit-validity predicate for `ty` under `pw`, matching
`anneal_mir::ir::Ty::is_valid_scalar_bits`. -/
def isValidBits (pw : PtrWidth) (ty : ScalarTy) (bits : Nat) : Bool :=
  let inRange := Bool.not (Nat.ble (scalarModulus (ty.sizeBytes pw)) bits)
  match ty with
  | .bool => Bool.and inRange (Nat.ble bits 1)
  | .char => Bool.and inRange (isValidCharCode bits)
  | .int _ | .uint _ | .rawPtr => inRange
  | .refPtr => Bool.and inRange (Bool.not (Nat.beq bits 0))

/-- Propositional bit-validity invariant for `ty` under `pw`. -/
def validBits (pw : PtrWidth) (ty : ScalarTy) (bits : Nat) : Prop :=
  bits < scalarModulus (ty.sizeBytes pw) ∧
  match ty with
  | .bool => bits ≤ 1
  | .char => isValidCharCode bits = true
  | .int _ | .uint _ | .rawPtr => True
  | .refPtr => 0 < bits

theorem not_ble_iff_lt (a b : Nat) :
    Bool.not (Nat.ble a b) = true ↔ b < a := by
  constructor
  · intro h
    cases hble : Nat.ble a b with
    | false =>
      have hnot : ¬ (a ≤ b) := by
        intro hle
        have htrue : Nat.ble a b = true := Nat.ble_eq.mpr hle
        rw [hble] at htrue
        contradiction
      omega
    | true =>
      rw [hble] at h
      contradiction
  · intro hlt
    cases hble : Nat.ble a b with
    | false => rfl
    | true =>
      have hle : a ≤ b := Nat.ble_eq.mp hble
      omega

theorem not_beq_zero_iff_pos (bits : Nat) :
    Bool.not (Nat.beq bits 0) = true ↔ 0 < bits := by
  cases bits with
  | zero => decide
  | succ k =>
    constructor
    · intro _
      omega
    · intro _
      rfl

/-- Equivalence between the decidable boolean checker `ScalarTy.isValidBits` and the
propositional invariant `ScalarTy.validBits`. -/
theorem isValidBits_iff_validBits (pw : PtrWidth) (ty : ScalarTy) (bits : Nat) :
    ty.isValidBits pw bits = true ↔ ty.validBits pw bits := by
  unfold isValidBits validBits
  cases ty with
  | bool =>
    simp only [Bool.and_eq_true, not_ble_iff_lt, Nat.ble_eq]
  | char =>
    simp only [Bool.and_eq_true, not_ble_iff_lt]
  | int w =>
    simp only [not_ble_iff_lt, and_true]
  | uint w =>
    simp only [not_ble_iff_lt, and_true]
  | rawPtr =>
    simp only [not_ble_iff_lt, and_true]
  | refPtr =>
    simp only [Bool.and_eq_true, not_ble_iff_lt, not_beq_zero_iff_pos]

instance instDecidableValidBits (pw : PtrWidth) (ty : ScalarTy) (bits : Nat) :
    Decidable (ty.validBits pw bits) :=
  decidable_of_iff (ty.isValidBits pw bits = true) (isValidBits_iff_validBits pw ty bits)

end ScalarTy

/-! ## 2. Byte-Level `ProvenanceFrag` Codec and Same-Size Transmute Operational Model -/

/-- Policy governing pointer-to-integer reinterpretation in `CastKind.transmute`,
matching `anneal_mir::lower::cast::TransmutePolicy`. -/
inductive TransmutePolicy : Type where
  /-- Rejects `Ptr -> Int` transmutes (default). -/
  | rejectPtrToInt : TransmutePolicy
  /-- Permits same-size `Ptr -> Int` transmutes while stripping pointer provenance
      without adding it to `ExposedProvenance`. -/
  | allowPtrToIntStripProvenance : TransmutePolicy
  deriving DecidableEq, Repr, Inhabited

/-- Provenance fragment carried by one byte of an encoded pointer
(`anneal_mir::lower::cast::ProvenanceFrag`): the pointer's allocation provenance
plus the byte's position within the pointer's little-endian encoding. -/
structure ProvenanceFrag : Type where
  allocId : Nat
  position : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Initialized abstract byte in `anneal-mir`'s transmute model
(`anneal_mir::lower::cast::AbstractByte`): an 8-bit data byte paired with an
optional pointer-provenance fragment. -/
structure CastByte : Type where
  data : UInt8
  prov : Option ProvenanceFrag
  deriving DecidableEq, Repr, Inhabited

/-- Translate a `CastByte` into a `Trusted.MirSemantics.AbstractByte`, mapping
`ProvenanceFrag { allocId, position }` to `(allocId, allocId)` (`ProvenancePtr.tag`). -/
def CastByte.toTrustedAbstractByte (b : CastByte) : AbstractByte :=
  .init b.data (b.prov.map (fun f => (f.allocId, f.allocId)))

/-- Encode `numBytes` little-endian bytes of `bits`, tagging byte `i` with
`ProvenanceFrag { allocId, position := startPos + i }` when `optAlloc = some allocId`. -/
def encodeCastBytesAux (bits : Nat) (optAlloc : Option Nat) : Nat → Nat → List CastByte
  | 0, _ => []
  | rem + 1, pos =>
    let frag := optAlloc.map (fun id => { allocId := id, position := pos })
    { data := UInt8.ofNat bits, prov := frag } ::
      encodeCastBytesAux (Nat.div bits 256) optAlloc rem (pos + 1)

/-- Encode `numBytes` little-endian bytes of `bits` starting at fragment position `0`
(`anneal_mir::lower::cast::{encode_int_bytes, encode_ptr_bytes}`). -/
def encodeCastBytes (bits numBytes : Nat) (optAlloc : Option Nat) : List CastByte :=
  encodeCastBytesAux bits optAlloc numBytes 0

/-- Decode a little-endian `List CastByte` into an unsigned bit pattern, ignoring
any provenance fragments (`anneal_mir::lower::cast::decode_int_bytes`). -/
def decodeCastIntBytes : List CastByte → Nat
  | [] => 0
  | b :: rest =>
    Nat.add b.data.toBitVec.toNat (Nat.mul 256 (decodeCastIntBytes rest))

/-- Check that every byte in `bytes` carries `some { allocId, position := pos + i }`
in exact ascending byte order. -/
def checkProvenanceFrags (allocId : Nat) : List CastByte → Nat → Bool
  | [], _ => true
  | b :: rest, pos =>
    match b.prov with
    | some frag =>
      match Bool.and (Nat.beq frag.allocId allocId) (Nat.beq frag.position pos) with
      | true => checkProvenanceFrags allocId rest (pos + 1)
      | false => false
    | none => false

/-- Extract pointer provenance from `bytes` (`anneal_mir::lower::cast::decode_ptr_bytes`):
keeps `some allocId` if and only if `bytes` is non-empty and every byte `idx` carries
`some { allocId, position := idx }`; otherwise (missing, mixed, or shuffled fragments)
returns `none`. -/
def decodeCastPtrProv (bytes : List CastByte) : Option Nat :=
  match bytes with
  | [] => none
  | b0 :: _ =>
    match b0.prov with
    | none => none
    | some frag0 =>
      match checkProvenanceFrags frag0.allocId bytes 0 with
      | true => some frag0.allocId
      | false => none

deriving instance DecidableEq, Repr, Inhabited for ProvenancePtr

/-- Runtime value for cast and transmute evaluation in `Anneal.Mir.Cast`, mirroring
`anneal_mir::lower::cast::TransmuteValue::{Scalar, Ptr}`. -/
inductive CastVal : Type where
  /-- Scalar bit pattern (`bool`, `char`, `int`, `uint`). -/
  | scalar (bits : Nat) : CastVal
  /-- Pointer value carrying `p : ProvenancePtr` (`allocId`, `offsetBytes`) and optional
      provenance tag `prov` (`some p.allocId` when provenance is preserved, `none` when
      provenance is stripped or absent). -/
  | ptr (p : ProvenancePtr) (prov : Option Nat := some p.allocId) : CastVal
  deriving DecidableEq, Repr, Inhabited

/-- Well-typed runtime `CastVal` for `ty : ScalarTy` under pointer width `pw`. -/
def CastVal.WellTyped (pw : PtrWidth) (ty : ScalarTy) : CastVal → Prop
  | .scalar bits =>
    ty.isPtr = false ∧ ty.validBits pw bits
  | .ptr p prov =>
    ty.isPtr = true ∧ ty.validBits pw p.offsetBytes ∧
    ((prov = some p.allocId) ∨ (prov = none ∧ p.allocId = 0))

/-- Decode a thin pointer from `bytes` (`anneal_mir::lower::cast::decode_ptr_bytes`). -/
def decodeCastPtrBytes (bytes : List CastByte) : CastVal :=
  let addr := decodeCastIntBytes bytes
  match decodeCastPtrProv bytes with
  | some allocId => .ptr { allocId := allocId, offsetBytes := addr } (some allocId)
  | none => .ptr { allocId := 0, offsetBytes := addr } none

/-- Result of evaluating a cast or transmute with explicit `ExposedProvenance` state threading. -/
inductive CastOutcome : Type where
  | ok (val : CastVal) (exposed : ExposedProvenance) : CastOutcome
  | ub : CastOutcome
  | unsupported : CastOutcome
  deriving DecidableEq, Repr, Inhabited

/-- Encode a runtime `CastVal` of type `src` under `pw` into its little-endian
`List CastByte` representation, returning `none` if `val` violates `src.isValidBits pw`
or does not match `src`'s runtime value representation. -/
def encodeCastVal
    (pw : PtrWidth)
    (src : ScalarTy)
    (val : CastVal) :
    Option (List CastByte) :=
  match src.isPtr, val with
  | false, .scalar bits =>
    match src.isValidBits pw bits with
    | true => some (encodeCastBytes bits (src.sizeBytes pw) none)
    | false => none
  | true, .ptr p prov =>
    match src.isValidBits pw p.offsetBytes with
    | true => some (encodeCastBytes p.offsetBytes (src.sizeBytes pw) prov)
    | false => none
  | _, _ => none

/-- Decode a `List CastByte` into a `CastVal` of type `dst` under `pw`, enforcing
`dst.isValidBits pw` (including `bool`, `char`, and non-null `refPtr` niches) and
stripping provenance when `dst.isPtr = false`. -/
def decodeCastVal
    (pw : PtrWidth)
    (dst : ScalarTy)
    (bytes : List CastByte) :
    Option CastVal :=
  match dst.isPtr with
  | true =>
    let addr := decodeCastIntBytes bytes
    match dst.isValidBits pw addr with
    | false => none
    | true => some (decodeCastPtrBytes bytes)
  | false =>
    let bits := decodeCastIntBytes bytes
    match dst.isValidBits pw bits with
    | false => none
    | true => some (.scalar bits)

/-- Evaluate a `CastKind.ptrToPtr` cast on a pointer `p` with provenance `prov` under `pw`,
leaving `exposed : ExposedProvenance` unchanged. -/
def evalPtrToPtrCast
    (pw : PtrWidth)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (prov : Option Nat := some p.allocId) :
    CastOutcome :=
  match ScalarTy.rawPtr.isValidBits pw p.offsetBytes with
  | false => .ub
  | true =>
    match prov with
    | some allocId =>
      .ok (.ptr { allocId := allocId, offsetBytes := p.offsetBytes } (some allocId)) exposed
    | none =>
      .ok (.ptr { allocId := 0, offsetBytes := p.offsetBytes } none) exposed

/-- Expose an optional provenance tag: `some allocId` is added to `exposed` via `exposeProv`,
whereas a provenance-free pointer (`none`) leaves `exposed` unchanged. This matches
`anneal_mir::lower::cast::eval_ptr_to_int_with_ptr_width`, which only calls
`tracker.expose(prov)` when `ptr.provenance = Some(prov)` (so the `allocId = 0` placeholder
carried by provenance-free `CastVal.ptr _ none` values is never spuriously exposed). -/
def exposeProvOpt : Option Nat → ExposedProvenance → ExposedProvenance
  | some allocId, exposed => exposeProv allocId exposed
  | none, exposed => exposed

/-- Evaluate a `CastKind.pointerExposeProvenance` (`PtrToInt`) cast on a pointer `p` carrying
provenance `prov` (default `some p.allocId`) to target type `dst` under pointer width `pw`,
matching `anneal_mir::lower::cast::eval_ptr_to_int_with_ptr_width`:
- the integer result is the pointer's address `p.offsetBytes` (`PointerValue::addr`, the very
  address bits that `encodeCastVal` / `evalTransmuteSameSize` encode) reduced modulo the target
  width `scalarModulus (dst.sizeBytes pw)`;
- the provenance `prov` (if present) is exposed via `exposeProvOpt`.

Out-of-range addresses (`p.offsetBytes ≥ pw.modulus`, an ill-typed pointer value) yield `.ub`,
consistently with `encodeCastVal`; on in-range addresses Episode 1's `addr & ptr_width.mask()`
is the identity. Note that `Trusted.MirSemantics`' `CastKind.pointerExposeProvenance` instead
uses the 64 KiB page model `ptrToAddress p` (see `ptr_to_usize_cast_step_correspondence`). -/
def evalPtrToIntExpose
    (pw : PtrWidth)
    (dst : ScalarTy)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (prov : Option Nat := some p.allocId) :
    CastOutcome :=
  match dst.isIntegral with
  | false => .unsupported
  | true =>
    match ScalarTy.rawPtr.isValidBits pw p.offsetBytes with
    | false => .ub
    | true =>
      .ok (.scalar (p.offsetBytes % scalarModulus (dst.sizeBytes pw))) (exposeProvOpt prov exposed)

/-- Decidable membership check for `allocId` in `exposed : ExposedProvenance`. -/
def isExposedBool (allocId : Nat) (exposed : ExposedProvenance) : Bool :=
  decide (allocId ∈ exposed)

theorem isExposedBool_eq_true_iff (allocId : Nat) (exposed : ExposedProvenance) :
    isExposedBool allocId exposed = true ↔ isExposed allocId exposed := by
  unfold isExposedBool isExposed
  exact decide_eq_true_iff

theorem isExposedBool_eq_false_iff (allocId : Nat) (exposed : ExposedProvenance) :
    isExposedBool allocId exposed = false ↔ ¬ isExposed allocId exposed := by
  unfold isExposedBool isExposed
  exact decide_eq_false_iff_not

/-- Evaluate a `CastKind.pointerWithExposedProvenance` (`IntToPtr`) cast from integer
address `addr` to `ScalarTy.rawPtr` under `pw`, matching
`anneal_mir::lower::cast::eval_int_to_ptr_with_ptr_width`: the resulting pointer keeps the
full address `addr` (`PointerValue { addr: addr & mask, provenance: predicted_prov }`), and a
predicted provenance `some allocId` must already be exposed (otherwise `.ub`, Episode 1's
`CastEvalError::UnexposedProvenance`); `none` yields a provenance-free pointer. Out-of-range
addresses (`addr ≥ pw.modulus`) yield `.ub`. -/
def evalIntToPtrExposed
    (pw : PtrWidth)
    (addr : Nat)
    (predictedAllocId : Option Nat)
    (exposed : ExposedProvenance) :
    CastOutcome :=
  match ScalarTy.rawPtr.isValidBits pw addr with
  | false => .ub
  | true =>
    match predictedAllocId with
    | some allocId =>
      match isExposedBool allocId exposed with
      | true => .ok (.ptr { allocId := allocId, offsetBytes := addr } (some allocId)) exposed
      | false => .ub
    | none =>
      .ok (.ptr { allocId := 0, offsetBytes := addr } none) exposed

/-- Source-typed `CastKind.pointerExposeProvenance` (`PtrToInt`) evaluator, matching
`anneal_mir::lower::rvalue::eval_lowered_cast` (`LoweredCast::PtrToInt`):
- `src` must be a pointer or reference descriptor (`src.isPtr = true`: `rawPtr` or `refPtr`),
  and `dst` must be an integral descriptor (`dst.isIntegral = true`), otherwise `.unsupported`;
- `p.offsetBytes` must satisfy `src.isValidBits pw p.offsetBytes` (in particular, a null
  reference `src = .refPtr` with `p.offsetBytes = 0` is rejected with `.ub` *before* any
  provenance is exposed, matching `rvalue.rs:2155-2160`);
- on valid inputs, returns `.ok (.scalar (p.offsetBytes % scalarModulus (dst.sizeBytes pw)))`
  and exposes `prov` via `exposeProvOpt`. -/
def evalPtrToIntExposeTyped
    (pw : PtrWidth)
    (src dst : ScalarTy)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (prov : Option Nat := some p.allocId) :
    CastOutcome :=
  match Bool.and src.isPtr dst.isIntegral with
  | false => .unsupported
  | true =>
    match src.isValidBits pw p.offsetBytes with
    | false => .ub
    | true =>
      .ok (.scalar (p.offsetBytes % scalarModulus (dst.sizeBytes pw))) (exposeProvOpt prov exposed)

/-- Least exposed allocation identifier, or `none` if nothing has been exposed. This is
`BTreeSet::first` on Episode 1's `ExposedProvenanceTracker.exposed : BTreeSet<Provenance>`
(an *ordered set*): it depends only on the set of exposed allocations, not on exposure order
(`leastExposed_congr`). -/
def leastExposed : ExposedProvenance → Option Nat
  | [] => none
  | a :: rest =>
    match leastExposed rest with
    | none => some a
    | some b => some (min a b)

/-- Deterministic provenance selector used by `anneal_mir::lower::rvalue::eval_lowered_cast`
(`LoweredCast::IntToPtr`, `rvalue.rs:2196-2206`): when `pick = true`, predicts the **least**
exposed provenance (`tracker.exposed.first().copied()` on a `BTreeSet`, i.e. `leastExposed`),
and `none` when `exposed = []` or `pick = false`. Note that `exposed.head?` would instead pick
the most recently exposed allocation (`exposeProv` prepends), which diverges from Episode 1
whenever allocations are exposed in non-increasing order. -/
def pickExposedProv (pick : Bool) (exposed : ExposedProvenance) : Option Nat :=
  match pick with
  | false => none
  | true => leastExposed exposed

/-- Deterministic `CastKind.pointerWithExposedProvenance` (`IntToPtr`) evaluator matching
`anneal_mir::lower::rvalue::eval_lowered_cast` (`LoweredCast::IntToPtr`): invokes
`evalIntToPtrExposed` with `pickExposedProv pick exposed`. -/
def evalIntToPtrDeterministic
    (pw : PtrWidth)
    (pick : Bool)
    (addr : Nat)
    (exposed : ExposedProvenance) :
    CastOutcome :=
  evalIntToPtrExposed pw addr (pickExposedProv pick exposed) exposed

/-- Integer-to-address conversion of Episode 1's `LoweredCast::IntToPtr` evaluation
(`rvalue.rs:2190-2194`): an unsigned source is truncated to its own width
(`addr & ut.mask(ptr_width)`), a signed source is **sign-extended** from its own width
(`it.sign_extend(addr, ptr_width) as u128`), and the result is reduced modulo the target pointer
width (`& ptr_width.mask()`). For a signed source with `2 * b ≥ m` (a negative value), the
two's-complement wrap `b - m (mod pw.modulus)` is computed as `(b + pw.modulus * m - m) % pw.modulus`. -/
def intToPtrAddress (pw : PtrWidth) (src : ScalarTy) (bits : Nat) : Nat :=
  match src with
  | .uint w => (bits % scalarModulus (w.byteSize pw)) % pw.modulus
  | .int w =>
    match Nat.blt (2 * (bits % scalarModulus (w.byteSize pw))) (scalarModulus (w.byteSize pw)) with
    | true => (bits % scalarModulus (w.byteSize pw)) % pw.modulus
    | false =>
      (bits % scalarModulus (w.byteSize pw) + pw.modulus * scalarModulus (w.byteSize pw) -
        scalarModulus (w.byteSize pw)) % pw.modulus
  | _ => bits % pw.modulus

/-- Source-typed deterministic `CastKind.pointerWithExposedProvenance` evaluator matching
Episode 1's `eval_lowered_cast` (`LoweredCast::IntToPtr`): requires an integral source
(otherwise `.unsupported`), converts the integer with `intToPtrAddress` (sign- or zero-extension
plus pointer-width masking), and predicts provenance with `pickExposedProv`. -/
def evalIntToPtrTyped
    (pw : PtrWidth)
    (src : ScalarTy)
    (bits : Nat)
    (pick : Bool)
    (exposed : ExposedProvenance) :
    CastOutcome :=
  match src.isIntegral with
  | false => .unsupported
  | true => evalIntToPtrDeterministic pw pick (intToPtrAddress pw src bits) exposed

/-- Full `LoweredCast::PtrToInt` evaluator matching `rvalue.rs:2138-2173`, parameterized by the
`exposeProvenance : Bool` flag (`expose_provenance` in `LoweredCast::PtrToInt`): when
`exposeProvenance = true`, exposes `prov` into `exposed`; when `exposeProvenance = false`, routes
exposure to a suppressed tracker so `exposed` is preserved unchanged. -/
def evalPtrToIntLowered
    (pw : PtrWidth)
    (src dst : ScalarTy)
    (exposeProvenance : Bool)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (prov : Option Nat := some p.allocId) :
    CastOutcome :=
  evalPtrToIntExposeTyped pw src dst p exposed (if exposeProvenance then prov else none)

/-- Whether `dst : ScalarTy` is a valid target of `CastKind.intToInt` (`eval_int_to_int` in
`cast.rs:846-851`): `Int`, `Uint`, or `Char` (`Bool` and pointer targets are rejected with
`TypeMismatch`). -/
def ScalarTy.isIntToIntTarget : ScalarTy → Bool
  | .int _ => true
  | .uint _ => true
  | .char => true
  | .bool => false
  | .rawPtr => false
  | .refPtr => false

/-- Bit-level numeric conversion of Episode 1's `eval_int_to_int` (`cast.rs:853-885`):
signed integer sources sign-extend from `src.sizeBytes pw` and mask modulo
`scalarModulus (dst.sizeBytes pw)`, while unsigned, `bool`, and `char` sources zero-extend
from `src.sizeBytes pw` and mask modulo `scalarModulus (dst.sizeBytes pw)`. -/
def intToIntBits (pw : PtrWidth) (src dst : ScalarTy) (bits : Nat) : Nat :=
  let dstMod := scalarModulus (dst.sizeBytes pw)
  let srcMod := scalarModulus (src.sizeBytes pw)
  let b := bits % srcMod
  match src with
  | .int _ =>
    match Nat.blt (2 * b) srcMod with
    | true => b % dstMod
    | false => (b + dstMod * srcMod - srcMod) % dstMod
  | _ => b % dstMod

/-- Evaluator for `CastKind.intToInt` (`eval_int_to_int` in `cast.rs:840-894` and
`LoweredCast::IntToInt` in `rvalue.rs:2215-2241`):
- requires a non-pointer scalar source (`src.isPtr = false`) and a valid `IntToInt` target
  (`dst.isIntToIntTarget = true`, i.e. `Int`, `Uint`, or `Char`), otherwise `.unsupported`;
- validates `bool` (`bits ≤ 1`) and `char` (`isValidCharCode bits`) source niches (`src.isValidBits pw bits`
  for `bool`/`char`, or any bit pattern masked to `src.sizeBytes pw` for `int`/`uint`);
- computes `res := intToIntBits pw src dst bits` and validates `dst.isValidBits pw res`
  (rejecting non-scalar-value `char` results with `.ub`, matching `cast.rs:887-892`). -/
def evalIntToInt
    (pw : PtrWidth)
    (src dst : ScalarTy)
    (bits : Nat)
    (exposed : ExposedProvenance) :
    CastOutcome :=
  match Bool.and (Bool.not src.isPtr) dst.isIntToIntTarget with
  | false => .unsupported
  | true =>
    let srcOk :=
      match src with
      | .bool | .char => src.isValidBits pw bits
      | _ => true
    match srcOk with
    | false => .ub
    | true =>
      let res := intToIntBits pw src dst bits
      match dst.isValidBits pw res with
      | false => .ub
      | true => .ok (.scalar res) exposed

/-- Evaluate a same-size `CastKind.transmute` from `src` to `dst` under target pointer
width `pw` and `TransmutePolicy` `policy`, threading `exposed : ExposedProvenance`
unchanged (`exposes_provenance = false`). -/
def evalTransmuteSameSize
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (src dst : ScalarTy)
    (val : CastVal)
    (exposed : ExposedProvenance) :
    CastOutcome :=
  match Nat.beq (src.sizeBytes pw) (dst.sizeBytes pw) with
  | false => .unsupported
  | true =>
    match Bool.and src.isPtr (Bool.not dst.isPtr), policy with
    | true, .rejectPtrToInt => .unsupported
    | _, _ =>
      match src.isPtr, val with
      | false, .ptr _ _ => .unsupported
      | true, .scalar _ => .unsupported
      | _, _ =>
        match encodeCastVal pw src val with
        | none => .ub
        | some bytes =>
          match decodeCastVal pw dst bytes with
          | some outVal => .ok outVal exposed
          | none => .ub

/-! ## 3. Byte-Level Codec Round-Trip, Fragment Corruption, and `Trusted` Refinement Lemmas -/

/-- Helper arithmetic lemma: `(UInt8.ofNat bits).toBitVec.toNat = bits % 256`. -/
theorem uint8_ofNat_toNat_eq_mod (bits : Nat) :
    (UInt8.ofNat bits).toBitVec.toNat = bits % 256 := by
  simp [UInt8.ofNat, BitVec.ofNat]

/-- Length of `encodeCastBytesAux bits optAlloc numBytes pos` is `numBytes`. -/
@[simp]
theorem encodeCastBytesAux_length
    (bits : Nat) (optAlloc : Option Nat) (numBytes pos : Nat) :
    (encodeCastBytesAux bits optAlloc numBytes pos).length = numBytes := by
  induction numBytes generalizing bits pos with
  | zero => rfl
  | succ rem ih =>
    simp only [encodeCastBytesAux, List.length_cons, ih]

/-- Length of `encodeCastBytes bits numBytes optAlloc` is `numBytes`. -/
@[simp]
theorem encodeCastBytes_length
    (bits numBytes : Nat) (optAlloc : Option Nat) :
    (encodeCastBytes bits numBytes optAlloc).length = numBytes :=
  encodeCastBytesAux_length bits optAlloc numBytes 0

/-- Decoding `encodeCastBytesAux bits optAlloc numBytes pos` via `decodeCastIntBytes`
recovers `bits` whenever `bits < scalarModulus numBytes`, independent of `optAlloc` and `pos`. -/
theorem decodeCastIntBytes_encodeCastBytesAux
    (numBytes bits pos : Nat) (optAlloc : Option Nat)
    (h_bound : bits < scalarModulus numBytes) :
    decodeCastIntBytes (encodeCastBytesAux bits optAlloc numBytes pos) = bits := by
  induction numBytes generalizing bits pos with
  | zero =>
    have h0 : bits = 0 := by
      simp [scalarModulus] at h_bound
      omega
    subst h0
    rfl
  | succ rem ih =>
    have h_div_bound : Nat.div bits 256 < scalarModulus rem := by
      simp only [scalarModulus, Nat.mul_eq] at h_bound
      have hdiv : bits / 256 < scalarModulus rem := by omega
      exact hdiv
    have h_ih := ih (Nat.div bits 256) (pos + 1) h_div_bound
    unfold encodeCastBytesAux decodeCastIntBytes
    simp only [h_ih, Nat.add_eq, Nat.mul_eq]
    rw [uint8_ofNat_toNat_eq_mod]
    exact Nat.mod_add_div bits 256

/-- Decoding `encodeCastBytes bits numBytes optAlloc` via `decodeCastIntBytes` recovers `bits`
whenever `bits < scalarModulus numBytes`. -/
theorem decodeCastIntBytes_encodeCastBytes
    (numBytes bits : Nat) (optAlloc : Option Nat)
    (h_bound : bits < scalarModulus numBytes) :
    decodeCastIntBytes (encodeCastBytes bits numBytes optAlloc) = bits :=
  decodeCastIntBytes_encodeCastBytesAux numBytes bits 0 optAlloc h_bound

/-- Every byte emitted by `encodeCastBytesAux bits (some allocId) numBytes pos` carries
the matching `ProvenanceFrag { allocId, position := pos + i }`. -/
theorem checkProvenanceFrags_encodeCastBytesAux
    (allocId bits numBytes pos : Nat) :
    checkProvenanceFrags allocId
      (encodeCastBytesAux bits (some allocId) numBytes pos) pos = true := by
  induction numBytes generalizing bits pos with
  | zero => rfl
  | succ rem ih =>
    unfold encodeCastBytesAux checkProvenanceFrags
    simp only [Option.map_some, Nat.beq_refl, Bool.and_self]
    exact ih (Nat.div bits 256) (pos + 1)

/-- Decoding pointer provenance from `encodeCastBytes bits (rem + 1) (some allocId)`
recovers `some allocId`. -/
theorem decodeCastPtrProv_encodeCastBytes_some
    (rem bits allocId : Nat) :
    decodeCastPtrProv (encodeCastBytes bits (rem + 1) (some allocId)) = some allocId := by
  unfold decodeCastPtrProv encodeCastBytes encodeCastBytesAux
  simp only [Option.map_some]
  have h_frags := checkProvenanceFrags_encodeCastBytesAux allocId bits (rem + 1) 0
  unfold encodeCastBytesAux at h_frags
  simp only [Option.map_some] at h_frags
  rw [h_frags]

/-- Decoding pointer provenance from `encodeCastBytes bits numBytes none` yields `none`
(provenance-free integer bytes never fabricate pointer provenance). -/
@[simp]
theorem decodeCastPtrProv_encodeCastBytes_none
    (bits numBytes : Nat) :
    decodeCastPtrProv (encodeCastBytes bits numBytes none) = none := by
  cases numBytes <;> rfl

/-- Decoding a thin pointer from `encodeCastBytes p.offsetBytes (rem + 1) (some p.allocId)`
recovers `.ptr p (some p.allocId)` when `p.offsetBytes < scalarModulus (rem + 1)`. -/
theorem decodeCastPtrBytes_encodeCastBytes_some
    (rem : Nat) (p : ProvenancePtr)
    (h_bound : p.offsetBytes < scalarModulus (rem + 1)) :
    decodeCastPtrBytes (encodeCastBytes p.offsetBytes (rem + 1) (some p.allocId)) =
      .ptr p (some p.allocId) := by
  cases p with
  | mk allocId offsetBytes =>
    unfold decodeCastPtrBytes
    rw [decodeCastIntBytes_encodeCastBytes (rem + 1) offsetBytes (some allocId) h_bound,
        decodeCastPtrProv_encodeCastBytes_some rem offsetBytes allocId]

/-- Decoding a thin pointer from `encodeCastBytes bits numBytes none` produces a pointer
with `allocId = 0`, `offsetBytes = bits`, and `prov = none`. -/
theorem decodeCastPtrBytes_encodeCastBytes_none
    (numBytes bits : Nat)
    (h_bound : bits < scalarModulus numBytes) :
    decodeCastPtrBytes (encodeCastBytes bits numBytes none) =
      .ptr { allocId := 0, offsetBytes := bits } none := by
  unfold decodeCastPtrBytes
  rw [decodeCastIntBytes_encodeCastBytes numBytes bits none h_bound,
      decodeCastPtrProv_encodeCastBytes_none bits numBytes]

/-- Partial overwrite of byte 0 with a provenance-free byte strips provenance (`none`). -/
theorem decodeCastPtrProv_partial_overwrite_head_none
    (d : UInt8) (rest : List CastByte) :
    decodeCastPtrProv ({ data := d, prov := none } :: rest) = none := rfl

/-- Partial overwrite of byte 1 with a provenance-free byte strips provenance (`none`). -/
theorem decodeCastPtrProv_partial_overwrite_second_none
    (b0 : CastByte) (d1 : UInt8) (rest : List CastByte) :
    decodeCastPtrProv (b0 :: { data := d1, prov := none } :: rest) = none := by
  rcases b0 with ⟨d0, none | ⟨allocId, pos0⟩⟩
  · rfl
  · unfold decodeCastPtrProv checkProvenanceFrags
    simp only [Nat.beq_refl, Bool.true_and]
    cases Nat.beq pos0 0 <;> rfl

/-- If byte 0 carries a fragment whose `position ≠ 0` (e.g. shifted/shuffled pointer bytes),
`decodeCastPtrProv` strips provenance (`none`). -/
theorem decodeCastPtrProv_position_mismatch_none
    (d0 : UInt8) (allocId pos0 : Nat) (rest : List CastByte)
    (h_pos : pos0 ≠ 0) :
    decodeCastPtrProv
      ({ data := d0, prov := some { allocId := allocId, position := pos0 } } :: rest) =
      none := by
  have h_beq : Nat.beq pos0 0 = false := by
    cases h : Nat.beq pos0 0 with
    | false => rfl
    | true => exact False.elim (h_pos (Nat.beq_eq.mp h))
  unfold decodeCastPtrProv checkProvenanceFrags
  simp only [Nat.beq_refl, h_beq, Bool.and_false]

/-- If byte 0 carries `allocId1` and byte 1 carries `allocId2 ≠ allocId1` (mixed fragments
from two distinct pointers), `decodeCastPtrProv` strips provenance (`none`). -/
theorem decodeCastPtrProv_allocId_mismatch_none
    (d0 d1 : UInt8) (allocId1 allocId2 pos0 pos1 : Nat) (rest : List CastByte)
    (h_diff : allocId2 ≠ allocId1) :
    decodeCastPtrProv
      ({ data := d0, prov := some { allocId := allocId1, position := pos0 } } ::
       { data := d1, prov := some { allocId := allocId2, position := pos1 } } ::
       rest) = none := by
  have h_beq : Nat.beq allocId2 allocId1 = false := by
    cases h : Nat.beq allocId2 allocId1 with
    | false => rfl
    | true => exact False.elim (h_diff (Nat.beq_eq.mp h))
  unfold decodeCastPtrProv checkProvenanceFrags
  simp only [Nat.beq_refl, Bool.true_and]
  cases Nat.beq pos0 0 with
  | false => rfl
  | true =>
    unfold checkProvenanceFrags
    simp only [h_beq, Bool.false_and]

/-- Exact characterization of `checkProvenanceFrags`: it succeeds iff byte `idx` carries
precisely the fragment `{ allocId, position := pos + idx }`, for every `idx`. -/
theorem checkProvenanceFrags_eq_true_iff (allocId : Nat) (bytes : List CastByte) (pos : Nat) :
    checkProvenanceFrags allocId bytes pos = true ↔
      ∀ (idx : Nat) (h : idx < bytes.length),
        bytes[idx].prov = some { allocId := allocId, position := pos + idx } := by
  induction bytes generalizing pos with
  | nil =>
    constructor
    · intro _ idx h
      exact absurd h (Nat.not_lt_zero _)
    · intro _
      rfl
  | cons x xs ih =>
    constructor
    · intro h_chk idx h_idx
      unfold checkProvenanceFrags at h_chk
      cases h_prov : x.prov with
      | none =>
        rw [h_prov] at h_chk
        contradiction
      | some frag =>
        rw [h_prov] at h_chk
        dsimp only at h_chk
        cases h_and : Bool.and (Nat.beq frag.allocId allocId) (Nat.beq frag.position pos) with
        | false =>
          rw [h_and] at h_chk
          contradiction
        | true =>
          rw [h_and] at h_chk
          have h_rest := (ih (pos + 1)).mp h_chk
          rw [Bool.and_eq_true] at h_and
          have h_a : frag.allocId = allocId := Nat.beq_eq.mp h_and.1
          have h_p : frag.position = pos := Nat.beq_eq.mp h_and.2
          cases idx with
          | zero =>
            simp only [List.getElem_cons_zero, Nat.add_zero]
            rw [h_prov]
            cases frag
            dsimp only at h_a h_p
            rw [h_a, h_p]
          | succ k =>
            simp only [List.getElem_cons_succ]
            have h_k : k < xs.length := by
              simp only [List.length_cons] at h_idx
              omega
            rw [h_rest k h_k, show pos + 1 + k = pos + (k + 1) by omega]
    · intro h_all
      unfold checkProvenanceFrags
      have h0 := h_all 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.add_zero] at h0
      rw [h0]
      dsimp only
      rw [Nat.beq_refl, Nat.beq_refl]
      show checkProvenanceFrags allocId xs (pos + 1) = true
      apply (ih (pos + 1)).mpr
      intro k h_k
      have h_k1 := h_all (k + 1) (by simp only [List.length_cons]; omega)
      simp only [List.getElem_cons_succ] at h_k1
      rw [h_k1, show pos + (k + 1) = pos + 1 + k by omega]

/-- **Exact `decode_ptr` provenance characterization** (MiniRust `decode_ptr` /
`anneal_mir::lower::cast::decode_ptr_bytes`): pointer bytes decode with provenance `allocId`
iff they are non-empty and *every* byte `idx` carries exactly the fragment
`{ allocId, position := idx }`. Any missing, foreign, or shuffled fragment strips provenance. -/
theorem decodeCastPtrProv_eq_some_iff (bytes : List CastByte) (allocId : Nat) :
    decodeCastPtrProv bytes = some allocId ↔
      bytes ≠ [] ∧ ∀ (idx : Nat) (h : idx < bytes.length),
        bytes[idx].prov = some { allocId := allocId, position := idx } := by
  cases bytes with
  | nil =>
    constructor
    · intro h
      exact absurd h (by simp [decodeCastPtrProv])
    · rintro ⟨h_ne, _⟩
      exact absurd rfl h_ne
  | cons b0 rest =>
    constructor
    · intro h
      refine ⟨List.cons_ne_nil _ _, ?_⟩
      unfold decodeCastPtrProv at h
      dsimp only at h
      cases h_p : b0.prov with
      | none =>
        rw [h_p] at h
        contradiction
      | some frag0 =>
        rw [h_p] at h
        dsimp only at h
        cases h_chk : checkProvenanceFrags frag0.allocId (b0 :: rest) 0 with
        | false =>
          rw [h_chk] at h
          contradiction
        | true =>
          rw [h_chk] at h
          have h_eq : frag0.allocId = allocId := Option.some.inj h
          rw [h_eq] at h_chk
          have h_all := (checkProvenanceFrags_eq_true_iff allocId (b0 :: rest) 0).mp h_chk
          intro idx h_idx
          rw [h_all idx h_idx, Nat.zero_add]
    · rintro ⟨_, h_all⟩
      have h0 := h_all 0 (by simp)
      simp only [List.getElem_cons_zero] at h0
      have h_chk : checkProvenanceFrags allocId (b0 :: rest) 0 = true := by
        apply (checkProvenanceFrags_eq_true_iff allocId (b0 :: rest) 0).mpr
        intro idx h_idx
        rw [h_all idx h_idx, Nat.zero_add]
      unfold decodeCastPtrProv
      dsimp only
      rw [h0]
      dsimp only
      rw [h_chk]

/-- Partial overwrite at **any** byte position: if any byte lacks a provenance fragment,
the decoded pointer has no provenance. -/
theorem decodeCastPtrProv_eq_none_of_prov_none
    (bytes : List CastByte) (idx : Nat) (h_idx : idx < bytes.length)
    (h_none : bytes[idx].prov = none) :
    decodeCastPtrProv bytes = none := by
  cases h : decodeCastPtrProv bytes with
  | none => rfl
  | some a =>
    have h_frag := ((decodeCastPtrProv_eq_some_iff bytes a).mp h).2 idx h_idx
    rw [h_none] at h_frag
    contradiction

/-- Mixed fragments at **any** two positions: if two bytes carry fragments of different
allocations, the decoded pointer has no provenance. -/
theorem decodeCastPtrProv_eq_none_of_allocId_ne
    (bytes : List CastByte) (i j : Nat) (h_i : i < bytes.length) (h_j : j < bytes.length)
    (fi fj : ProvenanceFrag)
    (h_fi : bytes[i].prov = some fi) (h_fj : bytes[j].prov = some fj)
    (h_ne : fi.allocId ≠ fj.allocId) :
    decodeCastPtrProv bytes = none := by
  cases h : decodeCastPtrProv bytes with
  | none => rfl
  | some a =>
    have h_all := ((decodeCastPtrProv_eq_some_iff bytes a).mp h).2
    have h_ai := h_all i h_i
    have h_aj := h_all j h_j
    rw [h_fi] at h_ai
    rw [h_fj] at h_aj
    have h1 : fi.allocId = a := by
      cases fi
      injection h_ai with h_ai'
      injection h_ai'
    have h2 : fj.allocId = a := by
      cases fj
      injection h_aj with h_aj'
      injection h_aj'
    exact absurd (h1.trans h2.symm) h_ne

/-- Shuffled fragments at **any** position: if byte `idx` carries a fragment recorded for a
different position, the decoded pointer has no provenance. -/
theorem decodeCastPtrProv_eq_none_of_position_ne
    (bytes : List CastByte) (idx : Nat) (h_idx : idx < bytes.length)
    (f : ProvenanceFrag) (h_f : bytes[idx].prov = some f) (h_ne : f.position ≠ idx) :
    decodeCastPtrProv bytes = none := by
  cases h : decodeCastPtrProv bytes with
  | none => rfl
  | some a =>
    have h_a := ((decodeCastPtrProv_eq_some_iff bytes a).mp h).2 idx h_idx
    rw [h_f] at h_a
    have h_pos : f.position = idx := by
      cases f
      injection h_a with h_a'
      injection h_a'
    exact absurd h_pos h_ne

/-- Concrete partial-overwrite theorem: overwriting byte `i` (for any `i < numBytes`) of an
encoded pointer with a provenance-free data byte (e.g. a `u8` store into the middle of a
stored `*const T`) strips the provenance of the reloaded pointer. -/
theorem decodeCastPtrProv_encodeCastBytes_set_none
    (bits numBytes allocId i : Nat) (d : UInt8) (h_i : i < numBytes) :
    decodeCastPtrProv
      ((encodeCastBytes bits numBytes (some allocId)).set i { data := d, prov := none }) = none :=
  decodeCastPtrProv_eq_none_of_prov_none _ i (by simp [h_i]) (by simp)

/-- Concrete mixed-fragment theorem: overwriting byte `i` of an encoded pointer to `allocId`
(with at least two bytes) with a fragment of a different allocation `allocId'` strips the
provenance of the reloaded pointer, regardless of the fragment's recorded position. -/
theorem decodeCastPtrProv_encodeCastBytes_set_foreign
    (bits numBytes allocId allocId' i pos' : Nat) (d : UInt8)
    (h_i : i < numBytes) (h_two : 2 ≤ numBytes) (h_ne : allocId' ≠ allocId) :
    decodeCastPtrProv
      ((encodeCastBytes bits numBytes (some allocId)).set i
        { data := d, prov := some { allocId := allocId', position := pos' } }) = none := by
  have h_all := (checkProvenanceFrags_eq_true_iff allocId
    (encodeCastBytes bits numBytes (some allocId)) 0).mp
    (checkProvenanceFrags_encodeCastBytesAux allocId bits numBytes 0)
  -- pick a witness byte `j ≠ i` that still carries a fragment of `allocId`
  obtain ⟨j, h_j, h_ji⟩ : ∃ j, j < numBytes ∧ j ≠ i :=
    if h0 : i = 0 then ⟨1, by omega, by omega⟩ else ⟨0, by omega, by omega⟩
  have h_len : ((encodeCastBytes bits numBytes (some allocId)).set i
      { data := d, prov := some { allocId := allocId', position := pos' } }).length = numBytes := by
    simp
  apply decodeCastPtrProv_eq_none_of_allocId_ne _ i j (by omega) (by omega)
    { allocId := allocId', position := pos' } { allocId := allocId, position := j }
  · simp
  · rw [List.getElem_set_ne (by omega)]
    have := h_all j (by simp [h_j])
    rw [Nat.zero_add] at this
    exact this
  · exact h_ne

/-- Every decoded little-endian value is bounded by the byte count. -/
theorem decodeCastIntBytes_lt (bytes : List CastByte) :
    decodeCastIntBytes bytes < scalarModulus bytes.length := by
  induction bytes with
  | nil => exact Nat.zero_lt_one
  | cons b rest ih =>
    have h_b : b.data.toBitVec.toNat < 256 := b.data.toBitVec.isLt
    show b.data.toBitVec.toNat + 256 * decodeCastIntBytes rest < 256 * scalarModulus rest.length
    omega

/-- Transmute-level partial overwrite: reloading the bytes of a stored thin pointer at a raw
pointer type after overwriting any byte `i` with a provenance-free byte yields a
provenance-free pointer (MiniRust `decode_ptr`), never the original provenance. -/
theorem decodeCastVal_rawPtr_partial_overwrite_strips_provenance
    (pw : PtrWidth) (p : ProvenancePtr) (i : Nat) (d : UInt8)
    (h_i : i < pw.byteSize) :
    let bytes := (encodeCastBytes p.offsetBytes pw.byteSize (some p.allocId)).set i
      { data := d, prov := none }
    decodeCastVal pw .rawPtr bytes =
      some (.ptr { allocId := 0, offsetBytes := decodeCastIntBytes bytes } none) := by
  intro bytes
  have h_len : bytes.length = pw.byteSize := by simp [bytes]
  have h_lt : decodeCastIntBytes bytes < scalarModulus pw.byteSize := h_len ▸ decodeCastIntBytes_lt bytes
  have h_valid : ScalarTy.rawPtr.isValidBits pw (decodeCastIntBytes bytes) = true :=
    (ScalarTy.isValidBits_iff_validBits pw .rawPtr _).mpr ⟨h_lt, trivial⟩
  have h_prov : decodeCastPtrProv bytes = none :=
    decodeCastPtrProv_encodeCastBytes_set_none p.offsetBytes pw.byteSize p.allocId i d h_i
  unfold decodeCastVal decodeCastPtrBytes
  dsimp only [ScalarTy.isPtr]
  rw [h_valid]
  dsimp only
  rw [h_prov]

/-- Concrete shuffled-fragment theorem: overwriting byte `i` (`i < numBytes`) of an encoded
pointer with a fragment whose recorded byte position `pos' ≠ i` (even from the *same*
allocation `allocId' = allocId`) strips the provenance of the reloaded pointer. -/
theorem decodeCastPtrProv_encodeCastBytes_set_position_ne
    (bits numBytes allocId allocId' i pos' : Nat) (d : UInt8)
    (h_i : i < numBytes) (h_pos : pos' ≠ i) :
    decodeCastPtrProv
      ((encodeCastBytes bits numBytes (some allocId)).set i
        { data := d, prov := some { allocId := allocId', position := pos' } }) = none :=
  decodeCastPtrProv_eq_none_of_position_ne _ i (by simp [h_i])
    { allocId := allocId', position := pos' } (by simp) h_pos

/-- Transmute-level mixed-fragment overwrite: reloading the bytes of a stored thin pointer at a
raw pointer type after overwriting any byte `i < pw.byteSize` with a fragment of a foreign
allocation `allocId' ≠ p.allocId` yields a provenance-free pointer (`prov = none`). -/
theorem decodeCastVal_rawPtr_foreign_overwrite_strips_provenance
    (pw : PtrWidth) (p : ProvenancePtr) (allocId' i pos' : Nat) (d : UInt8)
    (h_i : i < pw.byteSize) (h_ne : allocId' ≠ p.allocId) :
    let bytes := (encodeCastBytes p.offsetBytes pw.byteSize (some p.allocId)).set i
      { data := d, prov := some { allocId := allocId', position := pos' } }
    decodeCastVal pw .rawPtr bytes =
      some (.ptr { allocId := 0, offsetBytes := decodeCastIntBytes bytes } none) := by
  intro bytes
  have h_len : bytes.length = pw.byteSize := by simp [bytes]
  have h_lt : decodeCastIntBytes bytes < scalarModulus pw.byteSize := h_len ▸ decodeCastIntBytes_lt bytes
  have h_valid : ScalarTy.rawPtr.isValidBits pw (decodeCastIntBytes bytes) = true :=
    (ScalarTy.isValidBits_iff_validBits pw .rawPtr _).mpr ⟨h_lt, trivial⟩
  have h_two : 2 ≤ pw.byteSize := by cases pw <;> decide
  have h_prov : decodeCastPtrProv bytes = none :=
    decodeCastPtrProv_encodeCastBytes_set_foreign p.offsetBytes pw.byteSize p.allocId allocId' i pos'
      d h_i h_two h_ne
  unfold decodeCastVal decodeCastPtrBytes
  dsimp only [ScalarTy.isPtr]
  rw [h_valid]
  dsimp only
  rw [h_prov]

/-- Transmute-level shuffled-fragment overwrite: reloading the bytes of a stored thin pointer at a
raw pointer type after overwriting any byte `i < pw.byteSize` with a fragment whose recorded
position `pos' ≠ i` yields a provenance-free pointer (`prov = none`). -/
theorem decodeCastVal_rawPtr_position_mismatch_strips_provenance
    (pw : PtrWidth) (p : ProvenancePtr) (allocId' i pos' : Nat) (d : UInt8)
    (h_i : i < pw.byteSize) (h_pos : pos' ≠ i) :
    let bytes := (encodeCastBytes p.offsetBytes pw.byteSize (some p.allocId)).set i
      { data := d, prov := some { allocId := allocId', position := pos' } }
    decodeCastVal pw .rawPtr bytes =
      some (.ptr { allocId := 0, offsetBytes := decodeCastIntBytes bytes } none) := by
  intro bytes
  have h_len : bytes.length = pw.byteSize := by simp [bytes]
  have h_lt : decodeCastIntBytes bytes < scalarModulus pw.byteSize := h_len ▸ decodeCastIntBytes_lt bytes
  have h_valid : ScalarTy.rawPtr.isValidBits pw (decodeCastIntBytes bytes) = true :=
    (ScalarTy.isValidBits_iff_validBits pw .rawPtr _).mpr ⟨h_lt, trivial⟩
  have h_prov : decodeCastPtrProv bytes = none :=
    decodeCastPtrProv_encodeCastBytes_set_position_ne p.offsetBytes pw.byteSize p.allocId allocId'
      i pos' d h_i h_pos
  unfold decodeCastVal decodeCastPtrBytes
  dsimp only [ScalarTy.isPtr]
  rw [h_valid]
  dsimp only
  rw [h_prov]

/-- Misaligned pointer slice theorem: if a pointer encoded via `encodeCastBytes` is sliced at a
non-zero byte offset `k + 1 < numBytes` (plus any trailing `suffix` bytes, e.g. from an adjacent
composite field), the resulting slice starts with a fragment of `position = k + 1 ≠ 0` and
therefore decodes with `decodeCastPtrProv = none`. -/
theorem decodeCastPtrProv_drop_succ_encodeCastBytes
    (bits numBytes allocId k : Nat) (suffix : List CastByte)
    (h_k : k + 1 < numBytes) :
    decodeCastPtrProv
      ((encodeCastBytes bits numBytes (some allocId)).drop (k + 1) ++ suffix) = none := by
  have h_all := (checkProvenanceFrags_eq_true_iff allocId
    (encodeCastBytes bits numBytes (some allocId)) 0).mp
    (checkProvenanceFrags_encodeCastBytesAux allocId bits numBytes 0)
  have h_len_drop : 0 < ((encodeCastBytes bits numBytes (some allocId)).drop (k + 1)).length := by
    simp
    omega
  have h_len_app : 0 < ((encodeCastBytes bits numBytes (some allocId)).drop (k + 1) ++ suffix).length := by
    rw [List.length_append]
    omega
  apply decodeCastPtrProv_eq_none_of_position_ne _ 0 h_len_app
    { allocId := allocId, position := k + 1 }
  · rw [List.getElem_append_left h_len_drop, List.getElem_drop]
    have h_elem := h_all (k + 1 + 0) (by simp; omega)
    simpa using h_elem
  · dsimp only
    omega

/-- Exact refinement bridge: erasing per-byte fragment positions via
`CastByte.toTrustedAbstractByte` maps `encodeCastBytesAux` to `Trusted.MirSemantics.encodeLittleEndianBytes`. -/
theorem map_toTrustedAbstractByte_encodeCastBytesAux
    (bits : Nat) (optAlloc : Option Nat) (numBytes pos : Nat) :
    (encodeCastBytesAux bits optAlloc numBytes pos).map CastByte.toTrustedAbstractByte =
      encodeLittleEndianBytes bits numBytes (optAlloc.map (fun id => (id, id))) := by
  induction numBytes generalizing bits pos with
  | zero => rfl
  | succ rem ih =>
    simp only [encodeCastBytesAux, List.map_cons, CastByte.toTrustedAbstractByte,
      Option.map_map, encodeLittleEndianBytes, ih (Nat.div bits 256) (pos + 1)]
    rfl

/-- Exact refinement bridge between `Anneal.Mir.Cast.encodeCastBytes` and
`Trusted.MirSemantics.encodeLittleEndianBytes`. -/
theorem map_toTrustedAbstractByte_encodeCastBytes
    (bits numBytes : Nat) (optAlloc : Option Nat) :
    (encodeCastBytes bits numBytes optAlloc).map CastByte.toTrustedAbstractByte =
      encodeLittleEndianBytes bits numBytes (optAlloc.map (fun id => (id, id))) :=
  map_toTrustedAbstractByte_encodeCastBytesAux bits optAlloc numBytes 0

/-! ## 4. Size-Mismatch Rejection, Provenance Preservation vs. Exposure, and Round-Trip Theorems -/

/-- Size-mismatch rejection theorem: whenever `src.sizeBytes pw ≠ dst.sizeBytes pw`,
`evalTransmuteSameSize` returns `.unsupported`. -/
theorem transmute_size_mismatch_unsupported
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (src dst : ScalarTy)
    (val : CastVal)
    (exposed : ExposedProvenance)
    (h_neq : src.sizeBytes pw ≠ dst.sizeBytes pw) :
    evalTransmuteSameSize pw policy src dst val exposed = .unsupported := by
  have h_beq : Nat.beq (src.sizeBytes pw) (dst.sizeBytes pw) = false := by
    cases h : Nat.beq (src.sizeBytes pw) (dst.sizeBytes pw) with
    | false => rfl
    | true => exact False.elim (h_neq (Nat.beq_eq.mp h))
  unfold evalTransmuteSameSize
  rw [h_beq]

/-- Pointer-width sensitivity: on 32-bit targets (`PtrWidth.bits32`), transmuting between
`u64` (8 bytes) and `rawPtr` or `usize` (4 bytes) is rejected with `.unsupported`, whereas
on 64-bit targets (`PtrWidth.bits64`), `u64` and `usize` have matching 8-byte widths and
transmuting any `bits < scalarModulus 8` succeeds. -/
theorem transmute_u64_ptr_usize_ptrWidth_contrast
    (policy : TransmutePolicy)
    (val : CastVal)
    (bits : Nat)
    (exposed : ExposedProvenance)
    (h_bits : bits < scalarModulus 8) :
    evalTransmuteSameSize .bits32 policy .u64 .rawPtr val exposed = .unsupported ∧
    evalTransmuteSameSize .bits32 policy .rawPtr .u64 val exposed = .unsupported ∧
    evalTransmuteSameSize .bits32 policy .u64 .usize val exposed = .unsupported ∧
    evalTransmuteSameSize .bits32 policy .usize .u64 val exposed = .unsupported ∧
    evalTransmuteSameSize .bits64 policy .u64 .usize (.scalar bits) exposed =
      .ok (.scalar bits) exposed ∧
    evalTransmuteSameSize .bits64 policy .usize .u64 (.scalar bits) exposed =
      .ok (.scalar bits) exposed := by
  have h_valid_u64 : ScalarTy.u64.isValidBits .bits64 bits = true :=
    (ScalarTy.isValidBits_iff_validBits .bits64 .u64 bits).mpr ⟨h_bits, trivial⟩
  have h_valid_usize : ScalarTy.usize.isValidBits .bits64 bits = true :=
    (ScalarTy.isValidBits_iff_validBits .bits64 .usize bits).mpr ⟨h_bits, trivial⟩
  have h_dec := decodeCastIntBytes_encodeCastBytes 8 bits none h_bits
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · unfold evalTransmuteSameSize encodeCastVal decodeCastVal
    dsimp [ScalarTy.sizeBytes, IntWidth.byteSize, PtrWidth.byteSize, ScalarTy.isPtr]
    rw [h_valid_u64]
    dsimp
    rw [h_dec, h_valid_usize]
    cases policy <;> rfl
  · unfold evalTransmuteSameSize encodeCastVal decodeCastVal
    dsimp [ScalarTy.sizeBytes, IntWidth.byteSize, PtrWidth.byteSize, ScalarTy.isPtr]
    rw [h_valid_usize]
    dsimp
    rw [h_dec, h_valid_u64]
    cases policy <;> rfl

/-- Helper: `encodeCastBytes` at `pw.byteSize` decodes via `decodeCastPtrBytes` to the
original pointer under both 32-bit and 64-bit target pointer widths. -/
theorem decodeCastPtrBytes_encodeCastBytes_ptrWidth
    (pw : PtrWidth) (p : ProvenancePtr) (prov : Option Nat)
    (h_bound : p.offsetBytes < scalarModulus pw.byteSize) :
    decodeCastPtrBytes (encodeCastBytes p.offsetBytes pw.byteSize prov) =
      match prov with
      | some allocId => .ptr { allocId := allocId, offsetBytes := p.offsetBytes } (some allocId)
      | none => .ptr { allocId := 0, offsetBytes := p.offsetBytes } none := by
  cases pw <;> cases prov
  · exact decodeCastPtrBytes_encodeCastBytes_none 4 p.offsetBytes h_bound
  · rename_i allocId
    exact decodeCastPtrBytes_encodeCastBytes_some 3 ⟨allocId, p.offsetBytes⟩ h_bound
  · exact decodeCastPtrBytes_encodeCastBytes_none 8 p.offsetBytes h_bound
  · rename_i allocId
    exact decodeCastPtrBytes_encodeCastBytes_some 7 ⟨allocId, p.offsetBytes⟩ h_bound

/-- Same-size `rawPtr -> rawPtr` transmute equals `evalPtrToPtrCast` for every pointer
width `pw`, policy `policy`, pointer `p`, provenance `prov`, and exposed set `exposed`,
preserving `ProvenancePtr` (`allocId` and `offsetBytes`) without modifying `exposed`. -/
theorem transmute_ptr_to_ptr_eq_ptr_to_ptr
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (prov : Option Nat := some p.allocId) :
    evalTransmuteSameSize pw policy .rawPtr .rawPtr (.ptr p prov) exposed =
      evalPtrToPtrCast pw p exposed prov ∧
    (p.offsetBytes < scalarModulus pw.byteSize →
      evalTransmuteSameSize pw policy .rawPtr .rawPtr (.ptr p (some p.allocId)) exposed =
        .ok (.ptr p (some p.allocId)) exposed) := by
  constructor
  · unfold evalTransmuteSameSize evalPtrToPtrCast encodeCastVal decodeCastVal
    have h_sz : Nat.beq (ScalarTy.rawPtr.sizeBytes pw) (ScalarTy.rawPtr.sizeBytes pw) = true :=
      Nat.beq_refl _
    rw [h_sz]
    dsimp [ScalarTy.isPtr]
    cases h_valid : ScalarTy.rawPtr.isValidBits pw p.offsetBytes with
    | false => rfl
    | true =>
      have h_bound : p.offsetBytes < scalarModulus pw.byteSize :=
        ((ScalarTy.isValidBits_iff_validBits pw .rawPtr p.offsetBytes).mp h_valid).1
      dsimp [ScalarTy.sizeBytes]
      rw [decodeCastIntBytes_encodeCastBytes pw.byteSize p.offsetBytes prov h_bound,
          h_valid, decodeCastPtrBytes_encodeCastBytes_ptrWidth pw p prov h_bound]
      cases prov <;> rfl
  · intro h_bound
    have h_valid : ScalarTy.rawPtr.isValidBits pw p.offsetBytes = true :=
      (ScalarTy.isValidBits_iff_validBits pw .rawPtr p.offsetBytes).mpr ⟨h_bound, trivial⟩
    unfold evalTransmuteSameSize encodeCastVal decodeCastVal
    have h_sz : Nat.beq (ScalarTy.rawPtr.sizeBytes pw) (ScalarTy.rawPtr.sizeBytes pw) = true :=
      Nat.beq_refl _
    rw [h_sz]
    dsimp [ScalarTy.isPtr, ScalarTy.sizeBytes]
    rw [h_valid]
    dsimp
    rw [decodeCastIntBytes_encodeCastBytes pw.byteSize p.offsetBytes (some p.allocId) h_bound,
        h_valid, decodeCastPtrBytes_encodeCastBytes_ptrWidth pw p (some p.allocId) h_bound]
    cases p
    rfl

/-- `evalTransmuteSameSize` never modifies the `ExposedProvenance` set (`exposed' = exposed`),
regardless of pointer width, policy, source type, target type, or runtime value. -/
theorem transmute_preserves_exposed_set
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (src dst : ScalarTy)
    (val val' : CastVal)
    (exposed exposed' : ExposedProvenance)
    (h_eval : evalTransmuteSameSize pw policy src dst val exposed = .ok val' exposed') :
    exposed' = exposed := by
  unfold evalTransmuteSameSize at h_eval
  repeat' split at h_eval
  all_goals try contradiction
  injection h_eval with _ h_exp
  exact h_exp.symm

/-- Under `TransmutePolicy.rejectPtrToInt`, any same-size `Ptr -> Int` transmute is rejected
with `.unsupported`. -/
theorem transmute_ptr_to_int_rejected_by_default_policy
    (pw : PtrWidth)
    (src dst : ScalarTy)
    (val : CastVal)
    (exposed : ExposedProvenance)
    (h_src_ptr : src.isPtr = true)
    (h_dst_nonptr : dst.isPtr = false) :
    evalTransmuteSameSize pw .rejectPtrToInt src dst val exposed = .unsupported := by
  unfold evalTransmuteSameSize
  cases Nat.beq (src.sizeBytes pw) (dst.sizeBytes pw)
  · rfl
  · simp [h_src_ptr, h_dst_nonptr]

/-! ### Exposed-provenance `PtrToInt` / `IntToPtr` semantics (Episode 1 fidelity) -/

@[simp]
theorem exposeProvOpt_some (allocId : Nat) (exposed : ExposedProvenance) :
    exposeProvOpt (some allocId) exposed = exposeProv allocId exposed := rfl

@[simp]
theorem exposeProvOpt_none (exposed : ExposedProvenance) :
    exposeProvOpt none exposed = exposed := rfl

/-- Exposing an optional provenance preserves every previously exposed tag. -/
theorem isExposed_exposeProvOpt_of_isExposed (prov : Option Nat) (other : Nat)
    (exposed : ExposedProvenance) (h : isExposed other exposed) :
    isExposed other (exposeProvOpt prov exposed) := by
  cases prov with
  | none => exact h
  | some allocId => exact isExposed_of_isExposed allocId other exposed h

/-- Closed form of `evalPtrToIntExpose` on in-range addresses and integral targets: the
result is `p.offsetBytes % scalarModulus (dst.sizeBytes pw)` and exactly `prov` is exposed. -/
theorem evalPtrToIntExpose_eq
    (pw : PtrWidth)
    (dst : ScalarTy)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (prov : Option Nat)
    (h_int : dst.isIntegral = true)
    (h_off : p.offsetBytes < scalarModulus pw.byteSize) :
    evalPtrToIntExpose pw dst p exposed prov =
      .ok (.scalar (p.offsetBytes % scalarModulus (dst.sizeBytes pw)))
        (exposeProvOpt prov exposed) := by
  have h_valid : ScalarTy.rawPtr.isValidBits pw p.offsetBytes = true :=
    (ScalarTy.isValidBits_iff_validBits pw .rawPtr p.offsetBytes).mpr ⟨h_off, trivial⟩
  unfold evalPtrToIntExpose
  rw [h_int]
  dsimp only
  rw [h_valid]

/-- `evalPtrToIntExpose` exposes exactly the pointer's own provenance `prov`: whenever it
succeeds, the new exposed set is `exposeProvOpt prov exposed`. In particular a provenance-free
pointer (`prov = none`) never modifies `exposed`. -/
theorem evalPtrToIntExpose_exposed_eq
    (pw : PtrWidth)
    (dst : ScalarTy)
    (p : ProvenancePtr)
    (exposed exposed' : ExposedProvenance)
    (prov : Option Nat)
    (v : CastVal)
    (h_eval : evalPtrToIntExpose pw dst p exposed prov = .ok v exposed') :
    exposed' = exposeProvOpt prov exposed := by
  unfold evalPtrToIntExpose at h_eval
  repeat' split at h_eval
  all_goals try contradiction
  injection h_eval with _ h_exp
  exact h_exp.symm

/-- No spurious exposure: casting a provenance-free pointer (`prov = none`, e.g. the result of
an `Int -> Ptr` transmute) to an integer leaves `exposed` unchanged, so the `allocId = 0`
placeholder of provenance-free `CastVal.ptr _ none` values is never exposed. -/
theorem evalPtrToIntExpose_none_preserves_exposed
    (pw : PtrWidth)
    (dst : ScalarTy)
    (p : ProvenancePtr)
    (exposed exposed' : ExposedProvenance)
    (v : CastVal)
    (h_eval : evalPtrToIntExpose pw dst p exposed none = .ok v exposed') :
    exposed' = exposed :=
  evalPtrToIntExpose_exposed_eq pw dst p exposed exposed' none v h_eval

/-- `evalIntToPtrExposed` with an exposed predicted provenance keeps the full address. -/
theorem evalIntToPtrExposed_some_of_isExposed
    (pw : PtrWidth)
    (addr allocId : Nat)
    (exposed : ExposedProvenance)
    (h_addr : addr < scalarModulus pw.byteSize)
    (h_exp : isExposed allocId exposed) :
    evalIntToPtrExposed pw addr (some allocId) exposed =
      .ok (.ptr { allocId := allocId, offsetBytes := addr } (some allocId)) exposed := by
  have h_valid : ScalarTy.rawPtr.isValidBits pw addr = true :=
    (ScalarTy.isValidBits_iff_validBits pw .rawPtr addr).mpr ⟨h_addr, trivial⟩
  have h_true : isExposedBool allocId exposed = true :=
    (isExposedBool_eq_true_iff allocId exposed).mpr h_exp
  unfold evalIntToPtrExposed
  rw [h_valid]
  dsimp only
  rw [h_true]

/-- `evalIntToPtrExposed` with an unexposed predicted provenance is `.ub` for every address. -/
theorem evalIntToPtrExposed_some_of_not_isExposed
    (pw : PtrWidth)
    (addr allocId : Nat)
    (exposed : ExposedProvenance)
    (h_unexp : ¬ isExposed allocId exposed) :
    evalIntToPtrExposed pw addr (some allocId) exposed = .ub := by
  have h_false : isExposedBool allocId exposed = false :=
    (isExposedBool_eq_false_iff allocId exposed).mpr h_unexp
  unfold evalIntToPtrExposed
  cases ScalarTy.rawPtr.isValidBits pw addr with
  | false => rfl
  | true =>
    dsimp only
    rw [h_false]

/-- `evalIntToPtrExposed` without a predicted provenance yields a provenance-free pointer at
the full address `addr`, without modifying `exposed`. -/
theorem evalIntToPtrExposed_none
    (pw : PtrWidth)
    (addr : Nat)
    (exposed : ExposedProvenance)
    (h_addr : addr < scalarModulus pw.byteSize) :
    evalIntToPtrExposed pw addr none exposed =
      .ok (.ptr { allocId := 0, offsetBytes := addr } none) exposed := by
  have h_valid : ScalarTy.rawPtr.isValidBits pw addr = true :=
    (ScalarTy.isValidBits_iff_validBits pw .rawPtr addr).mpr ⟨h_addr, trivial⟩
  unfold evalIntToPtrExposed
  rw [h_valid]

/-- Exposed-provenance round trip (`ptr as usize as *const T`, MiniRust `IntPtrCast`):
`evalPtrToIntExpose` returns the address `p.offsetBytes` and exposes `p.allocId`, after which
`evalIntToPtrExposed` predicting `some p.allocId` reconstructs exactly `p` with its provenance.
`dst` is any integral target wide enough to hold the address (`usize`/`isize`, `u64` on 64-bit
targets, `u128`, ...). -/
theorem ptrToInt_intToPtr_roundtrip
    (pw : PtrWidth)
    (dst : ScalarTy)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (h_int : dst.isIntegral = true)
    (h_off : p.offsetBytes < scalarModulus pw.byteSize)
    (h_fit : p.offsetBytes < scalarModulus (dst.sizeBytes pw)) :
    evalPtrToIntExpose pw dst p exposed =
      .ok (.scalar p.offsetBytes) (exposeProv p.allocId exposed) ∧
    evalIntToPtrExposed pw p.offsetBytes (some p.allocId) (exposeProv p.allocId exposed) =
      .ok (.ptr p (some p.allocId)) (exposeProv p.allocId exposed) := by
  refine ⟨?_, ?_⟩
  · rw [evalPtrToIntExpose_eq pw dst p exposed (some p.allocId) h_int h_off,
        Nat.mod_eq_of_lt h_fit]
    rfl
  · rw [evalIntToPtrExposed_some_of_isExposed pw p.offsetBytes p.allocId
        (exposeProv p.allocId exposed) h_off (isExposed_exposeProv p.allocId exposed)]

/-- General `UCG #286` non-exposure theorem: no same-size transmute (for any pointer width,
policy, source/target types, or value) can make an unexposed allocation reachable through an
exposed-provenance `IntToPtr` cast — after `evalTransmuteSameSize` succeeds, every
`evalIntToPtrExposed` predicting the unexposed `allocId` is `.ub`, at every address. -/
theorem transmute_cannot_enable_exposed_intToPtr
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (src dst : ScalarTy)
    (val val' : CastVal)
    (exposed exposed' : ExposedProvenance)
    (allocId : Nat)
    (h_unexp : ¬ isExposed allocId exposed)
    (h_eval : evalTransmuteSameSize pw policy src dst val exposed = .ok val' exposed') :
    ∀ addr, evalIntToPtrExposed pw addr (some allocId) exposed' = .ub := by
  intro addr
  have h_same : exposed' = exposed :=
    transmute_preserves_exposed_set pw policy src dst val val' exposed exposed' h_eval
  subst h_same
  exact evalIntToPtrExposed_some_of_not_isExposed pw addr allocId exposed' h_unexp

/-- Contrast theorem (`UCG #286` / MiniRust `IntPtrCast` vs `transmute`), for a pointer `p`
with provenance `some p.allocId` and any pointer-sized unsigned target `uint w`:
1. `evalPtrToIntExpose` returns the address `p.offsetBytes` and exposes `p.allocId`, so
   `evalIntToPtrExposed` predicting `some p.allocId` reconstructs exactly `p`;
2. `evalTransmuteSameSize` (even under `TransmutePolicy.allowPtrToIntStripProvenance`) returns
   the *same* integer `p.offsetBytes` but leaves `exposed` untouched, so if
   `¬ isExposed p.allocId exposed`, every `evalIntToPtrExposed` predicting `some p.allocId`
   fails with `.ub`, and the only reconstruction (`none`) is a provenance-free pointer. -/
theorem ptrToInt_vs_transmute_exposure_contrast
    (pw : PtrWidth)
    (w : IntWidth)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (h_w : w.byteSize pw = pw.byteSize)
    (h_off : p.offsetBytes < scalarModulus pw.byteSize) :
    let exposedAfterCast := exposeProv p.allocId exposed
    evalPtrToIntExpose pw (.uint w) p exposed =
      .ok (.scalar p.offsetBytes) exposedAfterCast ∧
    isExposed p.allocId exposedAfterCast ∧
    evalIntToPtrExposed pw p.offsetBytes (some p.allocId) exposedAfterCast =
      .ok (.ptr p (some p.allocId)) exposedAfterCast ∧
    evalTransmuteSameSize pw .allowPtrToIntStripProvenance .rawPtr (.uint w)
        (.ptr p (some p.allocId)) exposed =
      .ok (.scalar p.offsetBytes) exposed ∧
    (¬ isExposed p.allocId exposed →
      ∀ addr, evalIntToPtrExposed pw addr (some p.allocId) exposed = .ub) ∧
    evalIntToPtrExposed pw p.offsetBytes none exposed =
      .ok (.ptr { allocId := 0, offsetBytes := p.offsetBytes } none) exposed := by
  have h_valid_ptr : ScalarTy.rawPtr.isValidBits pw p.offsetBytes = true :=
    (ScalarTy.isValidBits_iff_validBits pw .rawPtr p.offsetBytes).mpr ⟨h_off, trivial⟩
  have h_fit : p.offsetBytes < scalarModulus ((ScalarTy.uint w).sizeBytes pw) := by
    dsimp [ScalarTy.sizeBytes]
    rw [h_w]
    exact h_off
  have h_valid_uint : (ScalarTy.uint w).isValidBits pw p.offsetBytes = true :=
    (ScalarTy.isValidBits_iff_validBits pw (.uint w) p.offsetBytes).mpr ⟨h_fit, trivial⟩
  have h_rt := ptrToInt_intToPtr_roundtrip pw (.uint w) p exposed rfl h_off h_fit
  refine ⟨h_rt.1, isExposed_exposeProv p.allocId exposed, h_rt.2, ?_, ?_,
    evalIntToPtrExposed_none pw p.offsetBytes exposed h_off⟩
  · unfold evalTransmuteSameSize encodeCastVal decodeCastVal
    dsimp [ScalarTy.sizeBytes, ScalarTy.isPtr]
    have h_sz : Nat.beq pw.byteSize (w.byteSize pw) = true := by
      rw [h_w]
      exact Nat.beq_refl _
    rw [h_sz]
    dsimp only
    rw [h_valid_ptr]
    dsimp only
    rw [decodeCastIntBytes_encodeCastBytes pw.byteSize p.offsetBytes (some p.allocId) h_off,
        h_valid_uint]
    rfl
  · intro h_unexp addr
    exact evalIntToPtrExposed_some_of_not_isExposed pw addr p.allocId exposed h_unexp

/-- Regression against Episode 1's `test_end_to_end_ptr_to_int_to_ptr`,
`test_unexposed_provenance_rejected`, and `test_wildcard_provenance_allowed`
(`crates/anneal-mir/tests/cast_tests.rs`): `eval_ptr_to_int` on
`PointerValue::with_provenance(0xbeef_0000, 10, _)` returns `0xbeef_0000` and exposes allocation
`10`; `eval_int_to_ptr(0xbeef_0000, Some(prov))` then reconstructs the identical pointer;
predicting the unexposed allocation `999` is rejected; and a wildcard (`None`) prediction yields
a provenance-free pointer at the same address. -/
theorem episode1_ptr_int_ptr_test_vectors :
    evalPtrToIntExpose .bits64 .usize { allocId := 10, offsetBytes := 0xbeef0000 } [] =
      .ok (.scalar 0xbeef0000) [10] ∧
    evalIntToPtrExposed .bits64 0xbeef0000 (some 10) [10] =
      .ok (.ptr { allocId := 10, offsetBytes := 0xbeef0000 } (some 10)) [10] ∧
    evalIntToPtrExposed .bits64 0x12345678 (some 999) [] = .ub ∧
    evalIntToPtrExposed .bits64 0x12345678 none [] =
      .ok (.ptr { allocId := 0, offsetBytes := 0x12345678 } none) [] ∧
    evalPtrToIntExpose .bits32 .usize { allocId := 0, offsetBytes := 0x41 } [] none =
      .ok (.scalar 0x41) [] ∧
    evalPtrToIntExpose .bits64 .u32 { allocId := 1, offsetBytes := 0x100000005 } [] =
      .ok (.scalar 5) [1] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `evalPtrToIntExposeTyped` specialized to `ScalarTy.rawPtr` is definitionally
`evalPtrToIntExpose`. -/
@[simp]
theorem evalPtrToIntExposeTyped_rawPtr_eq
    (pw : PtrWidth)
    (dst : ScalarTy)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (prov : Option Nat) :
    evalPtrToIntExposeTyped pw .rawPtr dst p exposed prov =
      evalPtrToIntExpose pw dst p exposed prov := rfl

/-- Null-reference rejection in `PtrToInt` (`rvalue.rs:2155-2160`): when the source operand of
`CastKind.pointerExposeProvenance` has reference type (`ScalarTy.refPtr`) and null address
(`offsetBytes = 0`), `evalPtrToIntExposeTyped` faults with `.ub` *without* exposing provenance. -/
theorem evalPtrToIntExposeTyped_refPtr_zero_ub
    (pw : PtrWidth)
    (dst : ScalarTy)
    (allocId : Nat)
    (exposed : ExposedProvenance)
    (prov : Option Nat)
    (h_int : dst.isIntegral = true) :
    evalPtrToIntExposeTyped pw .refPtr dst { allocId := allocId, offsetBytes := 0 } exposed prov =
      .ub := by
  have h_inv : ScalarTy.refPtr.isValidBits pw 0 = false := by
    cases pw <;> rfl
  unfold evalPtrToIntExposeTyped
  rw [h_int, h_inv]
  rfl

/-- Reference-source `PtrToInt -> IntToPtr` round trip
(`test_b2_ptr_to_int_evaluates_reference_sources_accepted_by_lowering` in `rvalue.rs`):
for any non-null reference `p` (`0 < p.offsetBytes < scalarModulus pw.byteSize`) and integral
target `dst` wide enough to hold `p.offsetBytes`, `evalPtrToIntExposeTyped pw .refPtr dst`
evaluates to `.ok (.scalar p.offsetBytes) (exposeProv p.allocId exposed)` and
`evalIntToPtrExposed` reconstructs `.ok (.ptr p (some p.allocId))`. -/
theorem evalPtrToIntExposeTyped_refPtr_roundtrip
    (pw : PtrWidth)
    (dst : ScalarTy)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (h_int : dst.isIntegral = true)
    (h_nonnull : 0 < p.offsetBytes)
    (h_off : p.offsetBytes < scalarModulus pw.byteSize)
    (h_fit : p.offsetBytes < scalarModulus (dst.sizeBytes pw)) :
    evalPtrToIntExposeTyped pw .refPtr dst p exposed =
      .ok (.scalar p.offsetBytes) (exposeProv p.allocId exposed) ∧
    evalIntToPtrExposed pw p.offsetBytes (some p.allocId) (exposeProv p.allocId exposed) =
      .ok (.ptr p (some p.allocId)) (exposeProv p.allocId exposed) := by
  have h_valid_ref : ScalarTy.refPtr.isValidBits pw p.offsetBytes = true :=
    (ScalarTy.isValidBits_iff_validBits pw .refPtr p.offsetBytes).mpr ⟨h_off, h_nonnull⟩
  refine ⟨?_, (ptrToInt_intToPtr_roundtrip pw dst p exposed h_int h_off h_fit).2⟩
  unfold evalPtrToIntExposeTyped
  rw [h_int, h_valid_ref, Nat.mod_eq_of_lt h_fit]
  rfl

/-- `scalarModulus n` is strictly positive for every `n : Nat`. -/
theorem scalarModulus_pos (n : Nat) : 0 < scalarModulus n := by
  induction n with
  | zero => decide
  | succ k ih =>
    change 0 < 256 * scalarModulus k
    omega

/-- `scalarModulus` is monotone: `m ≤ n → scalarModulus m ≤ scalarModulus n`. -/
theorem scalarModulus_mono {m n : Nat} (h : m ≤ n) :
    scalarModulus m ≤ scalarModulus n := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    subst hm
    exact Nat.le_refl _
  | succ k ih =>
    by_cases hmk : m ≤ k
    · have h_ih := ih hmk
      change scalarModulus m ≤ 256 * scalarModulus k
      omega
    · have hm : m = k + 1 := by omega
      subst hm
      exact Nat.le_refl _

/-- Truncating `PtrToInt -> IntToPtr` theorem (`test_eval_ptr_to_int_truncation` in `cast.rs`):
when a pointer `p` is cast to a narrower integral type `dst` (`dst.sizeBytes pw ≤ pw.byteSize`,
e.g. `u8`, `u16`, `u32` on 64-bit targets), `evalPtrToIntExpose` truncates the address to
`p.offsetBytes % scalarModulus (dst.sizeBytes pw)` while *still* exposing `p.allocId`; casting
that truncated integer back via `evalIntToPtrExposed` predicting `some p.allocId` succeeds and
yields `{ allocId := p.allocId, offsetBytes := p.offsetBytes % scalarModulus (dst.sizeBytes pw) }`
(same allocation provenance at the low-order truncated offset). -/
theorem ptrToInt_truncating_exposes_and_reconstructs_low_bits
    (pw : PtrWidth)
    (dst : ScalarTy)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (h_int : dst.isIntegral = true)
    (h_narrow : dst.sizeBytes pw ≤ pw.byteSize)
    (h_off : p.offsetBytes < scalarModulus pw.byteSize) :
    let truncAddr := p.offsetBytes % scalarModulus (dst.sizeBytes pw)
    let exposed' := exposeProv p.allocId exposed
    evalPtrToIntExpose pw dst p exposed = .ok (.scalar truncAddr) exposed' ∧
    evalIntToPtrExposed pw truncAddr (some p.allocId) exposed' =
      .ok (.ptr { allocId := p.allocId, offsetBytes := truncAddr } (some p.allocId)) exposed' := by
  dsimp only
  have h_pos : 0 < scalarModulus (dst.sizeBytes pw) := scalarModulus_pos (dst.sizeBytes pw)
  have h_mod_lt_dst :
      p.offsetBytes % scalarModulus (dst.sizeBytes pw) < scalarModulus (dst.sizeBytes pw) :=
    Nat.mod_lt p.offsetBytes h_pos
  have h_mono : scalarModulus (dst.sizeBytes pw) ≤ scalarModulus pw.byteSize :=
    scalarModulus_mono h_narrow
  have h_mod_lt_pw :
      p.offsetBytes % scalarModulus (dst.sizeBytes pw) < scalarModulus pw.byteSize :=
    Nat.lt_of_lt_of_le h_mod_lt_dst h_mono
  refine ⟨evalPtrToIntExpose_eq pw dst p exposed (some p.allocId) h_int h_off, ?_⟩
  exact evalIntToPtrExposed_some_of_isExposed pw
    (p.offsetBytes % scalarModulus (dst.sizeBytes pw)) p.allocId (exposeProv p.allocId exposed)
    h_mod_lt_pw (isExposed_exposeProv p.allocId exposed)

/-- `leastExposed e = none` exactly when nothing has been exposed. -/
theorem leastExposed_eq_none_iff (e : ExposedProvenance) : leastExposed e = none ↔ e = [] := by
  cases e with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons a rest =>
    constructor
    · intro h
      unfold leastExposed at h
      cases h_r : leastExposed rest with
      | none =>
        rw [h_r] at h
        contradiction
      | some b =>
        rw [h_r] at h
        contradiction
    · intro h
      contradiction

/-- The least exposed allocation is exposed. -/
theorem leastExposed_mem :
    ∀ (e : ExposedProvenance) (a : Nat), leastExposed e = some a → a ∈ e
  | [], a, h => by
    unfold leastExposed at h
    contradiction
  | x :: rest, a, h => by
    unfold leastExposed at h
    cases h_r : leastExposed rest with
    | none =>
      rw [h_r] at h
      injection h with h_eq
      subst h_eq
      exact List.Mem.head _
    | some b =>
      rw [h_r] at h
      injection h with h_eq
      have hb := leastExposed_mem rest b h_r
      rcases Nat.le_total x b with hxb | hbx
      · rw [Nat.min_eq_left hxb] at h_eq
        subst h_eq
        exact List.Mem.head _
      · rw [Nat.min_eq_right hbx] at h_eq
        subst h_eq
        exact List.Mem.tail _ hb

/-- The least exposed allocation is below every exposed allocation. -/
theorem leastExposed_le :
    ∀ (e : ExposedProvenance) (a : Nat), leastExposed e = some a → ∀ b ∈ e, a ≤ b
  | [], a, h => by
    unfold leastExposed at h
    contradiction
  | x :: rest, a, h => by
    intro b hb
    unfold leastExposed at h
    cases h_r : leastExposed rest with
    | none =>
      rw [h_r] at h
      injection h with h_eq
      subst h_eq
      have h_nil : rest = [] := (leastExposed_eq_none_iff rest).mp h_r
      subst h_nil
      cases hb with
      | head => exact Nat.le_refl _
      | tail _ h' => cases h'
    | some c =>
      rw [h_r] at h
      injection h with h_eq
      subst h_eq
      cases hb with
      | head => exact Nat.min_le_left _ _
      | tail _ h' => exact Nat.le_trans (Nat.min_le_right _ _) (leastExposed_le rest c h_r b h')

/-- Set semantics: `leastExposed` depends only on *which* allocations are exposed. -/
theorem leastExposed_congr (e₁ e₂ : ExposedProvenance) (h : ∀ x, x ∈ e₁ ↔ x ∈ e₂) :
    leastExposed e₁ = leastExposed e₂ := by
  cases h1 : leastExposed e₁ with
  | none =>
    have h_nil : e₁ = [] := (leastExposed_eq_none_iff e₁).mp h1
    subst h_nil
    cases e₂ with
    | nil => rfl
    | cons y ys => exact absurd ((h y).mpr (List.Mem.head ys)) (by simp)
  | some a =>
    have ha := leastExposed_mem e₁ a h1
    cases h2 : leastExposed e₂ with
    | none =>
      have h_nil : e₂ = [] := (leastExposed_eq_none_iff e₂).mp h2
      rw [h_nil] at h
      exact absurd ((h a).mp ha) (by simp)
    | some b =>
      have hb := leastExposed_mem e₂ b h2
      have hab := leastExposed_le e₁ a h1 b ((h b).mpr hb)
      have hba := leastExposed_le e₂ b h2 a ((h a).mp ha)
      rw [Nat.le_antisymm hab hba]

/-- Membership in `exposeProv a e`. -/
theorem mem_exposeProv_iff (a x : Nat) (e : ExposedProvenance) :
    x ∈ exposeProv a e ↔ x = a ∨ x ∈ e := by
  unfold exposeProv
  split
  · next h_mem =>
    constructor
    · intro hx
      exact Or.inr hx
    · rintro (rfl | hx)
      · exact h_mem
      · exact hx
  · exact List.mem_cons

/-- Exposure-order independence of Episode 1's deterministic `IntToPtr` prediction: exposing
`a` then `b` or `b` then `a` yields the same predicted provenance (`BTreeSet` semantics). -/
theorem pickExposedProv_exposeProv_comm (pick : Bool) (a b : Nat) (e : ExposedProvenance) :
    pickExposedProv pick (exposeProv a (exposeProv b e)) =
      pickExposedProv pick (exposeProv b (exposeProv a e)) := by
  cases pick with
  | false => rfl
  | true =>
    show leastExposed _ = leastExposed _
    apply leastExposed_congr
    intro x
    rw [mem_exposeProv_iff, mem_exposeProv_iff, mem_exposeProv_iff, mem_exposeProv_iff]
    exact or_left_comm

/-- Soundness of the deterministic provenance picker (`pickExposedProv`): any provenance returned
by `pickExposedProv pick exposed` is guaranteed to be exposed in `exposed`. -/
theorem isExposed_of_pickExposedProv_eq_some
    (pick : Bool)
    (exposed : ExposedProvenance)
    (allocId : Nat)
    (h_pick : pickExposedProv pick exposed = some allocId) :
    isExposed allocId exposed := by
  cases pick with
  | false => contradiction
  | true => exact leastExposed_mem exposed allocId h_pick

/-- Deterministic `IntToPtr` (`evalIntToPtrDeterministic`, matching `rvalue.rs:2202-2210`)
never fails with `UnexposedProvenance`: for any valid address `addr < scalarModulus pw.byteSize`,
it always evaluates to `.ok`, picking the head exposed provenance when `pick = true` and
`exposed` is non-empty, and `none` otherwise. -/
theorem evalIntToPtrDeterministic_eq_ok
    (pw : PtrWidth)
    (pick : Bool)
    (addr : Nat)
    (exposed : ExposedProvenance)
    (h_addr : addr < scalarModulus pw.byteSize) :
    evalIntToPtrDeterministic pw pick addr exposed =
      match pickExposedProv pick exposed with
      | some allocId =>
        .ok (.ptr { allocId := allocId, offsetBytes := addr } (some allocId)) exposed
      | none =>
        .ok (.ptr { allocId := 0, offsetBytes := addr } none) exposed := by
  unfold evalIntToPtrDeterministic
  cases h_pick : pickExposedProv pick exposed with
  | none => exact evalIntToPtrExposed_none pw addr exposed h_addr
  | some allocId =>
    exact evalIntToPtrExposed_some_of_isExposed pw addr allocId exposed h_addr
      (isExposed_of_pickExposedProv_eq_some pick exposed allocId h_pick)

/-- Oracle-free deterministic `PtrToInt -> IntToPtr` round trip from an initially empty exposed
set (`exposed = []`): `evalPtrToIntExpose` exposes `p.allocId` as the unique entry `[p.allocId]`,
after which `evalIntToPtrDeterministic pw true` deterministically selects `some p.allocId` and
reconstructs `.ok (.ptr p (some p.allocId)) [p.allocId]` with no external oracle prediction. -/
theorem ptrToInt_intToPtrDeterministic_roundtrip_from_empty
    (pw : PtrWidth)
    (dst : ScalarTy)
    (p : ProvenancePtr)
    (h_int : dst.isIntegral = true)
    (h_off : p.offsetBytes < scalarModulus pw.byteSize)
    (h_fit : p.offsetBytes < scalarModulus (dst.sizeBytes pw)) :
    evalPtrToIntExpose pw dst p [] = .ok (.scalar p.offsetBytes) [p.allocId] ∧
    evalIntToPtrDeterministic pw true p.offsetBytes [p.allocId] =
      .ok (.ptr p (some p.allocId)) [p.allocId] := by
  refine ⟨(ptrToInt_intToPtr_roundtrip pw dst p [] h_int h_off h_fit).1, ?_⟩
  rw [evalIntToPtrDeterministic_eq_ok pw true _ _ h_off]
  rfl

/-- Episode 1's deterministic `PtrToInt -> IntToPtr` pipeline from an arbitrary exposed set:
the reconstructed pointer keeps the address `p.offsetBytes` but carries the **least** exposed
provenance of `exposeProv p.allocId exposed`, which is `p.allocId` exactly when no smaller
allocation was exposed before. -/
theorem ptrToInt_intToPtrDeterministic_picks_least_exposed
    (pw : PtrWidth)
    (dst : ScalarTy)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (h_int : dst.isIntegral = true)
    (h_off : p.offsetBytes < scalarModulus pw.byteSize)
    (h_fit : p.offsetBytes < scalarModulus (dst.sizeBytes pw)) :
    ∃ least,
      leastExposed (exposeProv p.allocId exposed) = some least ∧
      least ≤ p.allocId ∧
      evalPtrToIntExpose pw dst p exposed =
        .ok (.scalar p.offsetBytes) (exposeProv p.allocId exposed) ∧
      evalIntToPtrDeterministic pw true p.offsetBytes (exposeProv p.allocId exposed) =
        .ok (.ptr { allocId := least, offsetBytes := p.offsetBytes } (some least))
          (exposeProv p.allocId exposed) ∧
      (least = p.allocId ↔ ∀ b ∈ exposed, p.allocId ≤ b) := by
  have h_mem : p.allocId ∈ exposeProv p.allocId exposed := isExposed_exposeProv p.allocId exposed
  cases h_least : leastExposed (exposeProv p.allocId exposed) with
  | none =>
    have h_nil := (leastExposed_eq_none_iff _).mp h_least
    rw [h_nil] at h_mem
    exact absurd h_mem (by simp)
  | some least =>
    have h_le := leastExposed_le _ least h_least
    have h_lmem := leastExposed_mem _ least h_least
    refine ⟨least, rfl, h_le p.allocId h_mem,
      (ptrToInt_intToPtr_roundtrip pw dst p exposed h_int h_off h_fit).1, ?_, ?_⟩
    · rw [evalIntToPtrDeterministic_eq_ok pw true _ _ h_off]
      show (match leastExposed (exposeProv p.allocId exposed) with
            | some allocId =>
              CastOutcome.ok (.ptr { allocId := allocId, offsetBytes := p.offsetBytes } (some allocId))
                (exposeProv p.allocId exposed)
            | none =>
              CastOutcome.ok (.ptr { allocId := 0, offsetBytes := p.offsetBytes } none)
                (exposeProv p.allocId exposed)) = _
      rw [h_least]
    · constructor
      · intro h_eq b hb
        rw [← h_eq]
        exact h_le b (isExposed_of_isExposed p.allocId b exposed hb)
      · intro h_min
        rcases (mem_exposeProv_iff p.allocId least exposed).mp h_lmem with h_l | h_l
        · exact h_l
        · exact Nat.le_antisymm (h_le p.allocId h_mem) (h_min least h_l)

/-- Regression vectors for Episode 1's `BTreeSet::first` prediction (`rvalue.rs:2196-2206`):
after exposing allocation `3` and then `5`, `IntToPtr` predicts the least provenance `3` (a
`head?`-based selector would wrongly pick the most recent `5`); and after exposing `1`, a
`PtrToInt -> IntToPtr` round trip of a pointer into allocation `7` reconstructs the address with
provenance `1`, not `7`, exactly as Episode 1's evaluator does. -/
theorem episode1_intToPtr_least_exposed_vectors :
    exposeProv 5 (exposeProv 3 []) = [5, 3] ∧
    evalIntToPtrDeterministic .bits64 true 0x40 (exposeProv 5 (exposeProv 3 [])) =
      .ok (.ptr { allocId := 3, offsetBytes := 0x40 } (some 3)) [5, 3] ∧
    evalPtrToIntExpose .bits64 .usize { allocId := 7, offsetBytes := 0x40 } [1] =
      .ok (.scalar 0x40) [7, 1] ∧
    evalIntToPtrDeterministic .bits64 true 0x40 [7, 1] =
      .ok (.ptr { allocId := 1, offsetBytes := 0x40 } (some 1)) [7, 1] := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- `intToPtrAddress` always yields an in-range pointer address. -/
theorem intToPtrAddress_lt (pw : PtrWidth) (src : ScalarTy) (bits : Nat) :
    intToPtrAddress pw src bits < scalarModulus pw.byteSize := by
  have h_pos : 0 < scalarModulus pw.byteSize := scalarModulus_pos pw.byteSize
  unfold intToPtrAddress
  cases src with
  | uint w => exact Nat.mod_lt _ h_pos
  | int w =>
    dsimp only
    split
    · exact Nat.mod_lt _ h_pos
    · exact Nat.mod_lt _ h_pos
  | bool => exact Nat.mod_lt _ h_pos
  | char => exact Nat.mod_lt _ h_pos
  | rawPtr => exact Nat.mod_lt _ h_pos
  | refPtr => exact Nat.mod_lt _ h_pos

/-- Zero-extension: an in-range unsigned source no wider than a pointer keeps its value. -/
theorem intToPtrAddress_uint_of_lt (pw : PtrWidth) (w : IntWidth) (bits : Nat)
    (h_narrow : w.byteSize pw ≤ pw.byteSize)
    (h_bits : bits < scalarModulus (w.byteSize pw)) :
    intToPtrAddress pw (.uint w) bits = bits := by
  have h_bits_pw : bits < scalarModulus pw.byteSize :=
    Nat.lt_of_lt_of_le h_bits (scalarModulus_mono h_narrow)
  show (bits % scalarModulus (w.byteSize pw)) % scalarModulus pw.byteSize = bits
  rw [Nat.mod_eq_of_lt h_bits, Nat.mod_eq_of_lt h_bits_pw]

/-- A non-negative in-range signed source no wider than a pointer keeps its value. -/
theorem intToPtrAddress_int_of_nonneg (pw : PtrWidth) (w : IntWidth) (bits : Nat)
    (h_narrow : w.byteSize pw ≤ pw.byteSize)
    (h_bits : bits < scalarModulus (w.byteSize pw))
    (h_nonneg : 2 * bits < scalarModulus (w.byteSize pw)) :
    intToPtrAddress pw (.int w) bits = bits := by
  have h_bits_pw : bits < scalarModulus pw.byteSize :=
    Nat.lt_of_lt_of_le h_bits (scalarModulus_mono h_narrow)
  have h_blt : Nat.blt (2 * bits) (scalarModulus (w.byteSize pw)) = true := Nat.blt_eq.mpr h_nonneg
  show (match Nat.blt (2 * (bits % scalarModulus (w.byteSize pw))) (scalarModulus (w.byteSize pw)) with
        | true => (bits % scalarModulus (w.byteSize pw)) % scalarModulus pw.byteSize
        | false =>
          (bits % scalarModulus (w.byteSize pw) +
              scalarModulus pw.byteSize * scalarModulus (w.byteSize pw) -
            scalarModulus (w.byteSize pw)) % scalarModulus pw.byteSize) = bits
  rw [Nat.mod_eq_of_lt h_bits, h_blt]
  exact Nat.mod_eq_of_lt h_bits_pw

/-- **Sign extension**: a negative in-range signed source (`2 * bits ≥ m`) no wider than a
pointer is sign-extended to the pointer width, i.e. its address is `bits + pw.modulus - m`
(e.g. `(-1i32) as *const T` is `usize::MAX`, not `0xFFFF_FFFF`). -/
theorem intToPtrAddress_int_of_neg (pw : PtrWidth) (w : IntWidth) (bits : Nat)
    (h_narrow : w.byteSize pw ≤ pw.byteSize)
    (h_bits : bits < scalarModulus (w.byteSize pw))
    (h_neg : scalarModulus (w.byteSize pw) ≤ 2 * bits) :
    intToPtrAddress pw (.int w) bits =
      bits + scalarModulus pw.byteSize - scalarModulus (w.byteSize pw) := by
  have h_mono : scalarModulus (w.byteSize pw) ≤ scalarModulus pw.byteSize := scalarModulus_mono h_narrow
  have h_blt : Nat.blt (2 * bits) (scalarModulus (w.byteSize pw)) = false := by
    cases h : Nat.blt (2 * bits) (scalarModulus (w.byteSize pw)) with
    | false => rfl
    | true => exact absurd (Nat.blt_eq.mp h) (by omega)
  show (match Nat.blt (2 * (bits % scalarModulus (w.byteSize pw))) (scalarModulus (w.byteSize pw)) with
        | true => (bits % scalarModulus (w.byteSize pw)) % scalarModulus pw.byteSize
        | false =>
          (bits % scalarModulus (w.byteSize pw) +
              scalarModulus pw.byteSize * scalarModulus (w.byteSize pw) -
            scalarModulus (w.byteSize pw)) % scalarModulus pw.byteSize) = _
  rw [Nat.mod_eq_of_lt h_bits, h_blt]
  dsimp only
  have h_m_pos : 0 < scalarModulus (w.byteSize pw) := scalarModulus_pos _
  obtain ⟨k, hk⟩ : ∃ k, scalarModulus (w.byteSize pw) = k + 1 :=
    ⟨scalarModulus (w.byteSize pw) - 1, by omega⟩
  rw [hk] at h_bits h_mono h_neg ⊢
  generalize scalarModulus pw.byteSize = M at h_mono ⊢
  have h_split : bits + M * (k + 1) - (k + 1) = (bits + M - (k + 1)) + M * k := by
    rw [Nat.mul_succ]
    generalize M * k = MK
    omega
  rw [h_split, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- For pointer-sized integral sources (`usize`/`isize`, or `u64`/`i64` on 64-bit targets) every
in-range bit pattern is its own address, including the upper half for signed sources. -/
theorem intToPtrAddress_ptr_sized (pw : PtrWidth) (src : ScalarTy) (bits : Nat)
    (h_int : src.isIntegral = true)
    (h_sz : src.sizeBytes pw = pw.byteSize)
    (h_bits : bits < scalarModulus pw.byteSize) :
    intToPtrAddress pw src bits = bits := by
  cases src with
  | uint w =>
    have h_w : w.byteSize pw = pw.byteSize := h_sz
    exact intToPtrAddress_uint_of_lt pw w bits (Nat.le_of_eq h_w) (h_w ▸ h_bits)
  | int w =>
    have h_w : w.byteSize pw = pw.byteSize := h_sz
    by_cases h_nn : 2 * bits < scalarModulus (w.byteSize pw)
    · exact intToPtrAddress_int_of_nonneg pw w bits (Nat.le_of_eq h_w) (h_w ▸ h_bits) h_nn
    · rw [intToPtrAddress_int_of_neg pw w bits (Nat.le_of_eq h_w) (h_w ▸ h_bits) (by omega), h_w]
      omega
  | bool => contradiction
  | char => contradiction
  | rawPtr => contradiction
  | refPtr => contradiction

/-- Source-typed `IntToPtr` never faults on integral sources: it yields a pointer at
`intToPtrAddress pw src bits` with the predicted provenance. -/
theorem evalIntToPtrTyped_eq_ok
    (pw : PtrWidth) (src : ScalarTy) (bits : Nat) (pick : Bool) (exposed : ExposedProvenance)
    (h_int : src.isIntegral = true) :
    evalIntToPtrTyped pw src bits pick exposed =
      match pickExposedProv pick exposed with
      | some allocId =>
        .ok (.ptr { allocId := allocId, offsetBytes := intToPtrAddress pw src bits }
          (some allocId)) exposed
      | none =>
        .ok (.ptr { allocId := 0, offsetBytes := intToPtrAddress pw src bits } none) exposed := by
  unfold evalIntToPtrTyped
  rw [h_int]
  exact evalIntToPtrDeterministic_eq_ok pw pick _ exposed (intToPtrAddress_lt pw src bits)

/-- Regression vectors for Episode 1's `IntToPtr` address conversion (`rvalue.rs:2190-2194`):
sign extension of signed sources versus zero extension of unsigned sources, and truncation to
the target pointer width. -/
theorem episode1_intToPtr_address_vectors :
    intToPtrAddress .bits64 .i32 0xFFFFFFFF = 0xFFFFFFFFFFFFFFFF ∧
    intToPtrAddress .bits64 .u32 0xFFFFFFFF = 0xFFFFFFFF ∧
    intToPtrAddress .bits64 .i8 0x80 = 0xFFFFFFFFFFFFFF80 ∧
    intToPtrAddress .bits64 .isize 0xFFFFFFFFFFFFFFFF = 0xFFFFFFFFFFFFFFFF ∧
    intToPtrAddress .bits32 .i64 0x100000005 = 5 ∧
    intToPtrAddress .bits32 .i16 0xFFFE = 0xFFFFFFFE ∧
    evalIntToPtrTyped .bits64 .i32 0xFFFFFFFF false [] =
      .ok (.ptr { allocId := 0, offsetBytes := 0xFFFFFFFFFFFFFFFF } none) [] ∧
    evalIntToPtrTyped .bits64 .bool 1 true [] = .unsupported := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Multiplicative homomorphism of `scalarModulus`: `256^(a + b) = 256^a * 256^b`. -/
theorem scalarModulus_add (a b : Nat) :
    scalarModulus (a + b) = scalarModulus a * scalarModulus b := by
  induction b with
  | zero =>
    change scalarModulus a = scalarModulus a * 1
    omega
  | succ k ih =>
    change 256 * scalarModulus (a + k) = scalarModulus a * (256 * scalarModulus k)
    rw [ih, ← Nat.mul_assoc, Nat.mul_comm 256 (scalarModulus a), Nat.mul_assoc]

/-- Double-modulo absorption for nested byte widths `a ≤ b`:
`(bits % scalarModulus b) % scalarModulus a = bits % scalarModulus a`. -/
theorem mod_scalarModulus_of_le {a b : Nat} (bits : Nat) (h : a ≤ b) :
    (bits % scalarModulus b) % scalarModulus a = bits % scalarModulus a := by
  have h_eq : b = a + (b - a) := by omega
  rw [h_eq, scalarModulus_add a (b - a)]
  exact Nat.mod_mul_right_mod bits (scalarModulus a) (scalarModulus (b - a))

/-- Truncation of wider signed or unsigned integer sources (`pw.byteSize ≤ src.sizeBytes pw`,
such as `i64`/`u64`/`i128`/`u128` on 32-bit targets or `i128`/`u128` on 64-bit targets) in
`intToPtrAddress`: regardless of sign bit (`2 * b < m` or `2 * b ≥ m`), `intToPtrAddress`
reduces to `bits % scalarModulus pw.byteSize`. -/
theorem intToPtrAddress_of_ge_ptrWidth
    (pw : PtrWidth)
    (src : ScalarTy)
    (bits : Nat)
    (h_wide : pw.byteSize ≤ src.sizeBytes pw) :
    intToPtrAddress pw src bits = bits % scalarModulus pw.byteSize := by
  cases src with
  | uint w =>
    have h_le : pw.byteSize ≤ w.byteSize pw := h_wide
    exact mod_scalarModulus_of_le bits h_le
  | int w =>
    have h_le : pw.byteSize ≤ w.byteSize pw := h_wide
    unfold intToPtrAddress
    dsimp only [PtrWidth.modulus]
    split
    · exact mod_scalarModulus_of_le bits h_le
    · have h_eq : w.byteSize pw = pw.byteSize + (w.byteSize pw - pw.byteSize) := by omega
      have h_mul : scalarModulus (w.byteSize pw) =
          scalarModulus pw.byteSize * scalarModulus (w.byteSize pw - pw.byteSize) := by
        conv => lhs; rw [h_eq]
        exact scalarModulus_add pw.byteSize (w.byteSize pw - pw.byteSize)
      have h_pos_pw : 0 < scalarModulus pw.byteSize := scalarModulus_pos pw.byteSize
      obtain ⟨k, hk⟩ : ∃ k, scalarModulus pw.byteSize = k + 1 :=
        ⟨scalarModulus pw.byteSize - 1, by omega⟩
      have h_sub :
          bits % scalarModulus (w.byteSize pw) +
              scalarModulus pw.byteSize * scalarModulus (w.byteSize pw) -
            scalarModulus (w.byteSize pw) =
          bits % scalarModulus (w.byteSize pw) +
            scalarModulus pw.byteSize * (scalarModulus (w.byteSize pw - pw.byteSize) * k) := by
        rw [h_mul]
        generalize bits % (scalarModulus pw.byteSize * scalarModulus (w.byteSize pw - pw.byteSize)) = rem
        generalize scalarModulus (w.byteSize pw - pw.byteSize) = D
        rw [hk]
        have h_expand : (k + 1) * ((k + 1) * D) = (k + 1) * (D * k) + (k + 1) * D := by
          rw [← Nat.mul_add, ← Nat.mul_succ, Nat.mul_comm (k + 1) D]
        rw [h_expand]
        omega
      rw [h_sub, Nat.add_mul_mod_self_left]
      exact mod_scalarModulus_of_le bits h_le
  | bool => rfl
  | char => rfl
  | rawPtr => rfl
  | refPtr => rfl

/-- When the integral source is at least as wide as a pointer (`pw.byteSize ≤ src.sizeBytes pw`),
`evalIntToPtrTyped` truncates `bits` modulo `scalarModulus pw.byteSize` for both signed and
unsigned sources. -/
theorem evalIntToPtrTyped_of_ge_ptrWidth
    (pw : PtrWidth)
    (src : ScalarTy)
    (bits : Nat)
    (pick : Bool)
    (exposed : ExposedProvenance)
    (h_int : src.isIntegral = true)
    (h_wide : pw.byteSize ≤ src.sizeBytes pw) :
    evalIntToPtrTyped pw src bits pick exposed =
      evalIntToPtrDeterministic pw pick (bits % scalarModulus pw.byteSize) exposed := by
  unfold evalIntToPtrTyped
  rw [h_int, intToPtrAddress_of_ge_ptrWidth pw src bits h_wide]

/-- Type-safety of `decodeCastVal`: any value decoded by `decodeCastVal pw dst bytes` satisfies
`CastVal.WellTyped pw dst`. -/
theorem decodeCastVal_wellTyped
    (pw : PtrWidth)
    (dst : ScalarTy)
    (bytes : List CastByte)
    (val : CastVal)
    (h_dec : decodeCastVal pw dst bytes = some val) :
    CastVal.WellTyped pw dst val := by
  unfold decodeCastVal at h_dec
  cases h_ptr : dst.isPtr with
  | false =>
    rw [h_ptr] at h_dec
    dsimp only at h_dec
    cases h_v : dst.isValidBits pw (decodeCastIntBytes bytes) with
    | false =>
      rw [h_v] at h_dec
      contradiction
    | true =>
      rw [h_v] at h_dec
      injection h_dec with h_val
      subst h_val
      exact ⟨h_ptr, (ScalarTy.isValidBits_iff_validBits pw dst _).mp h_v⟩
  | true =>
    rw [h_ptr] at h_dec
    dsimp only at h_dec
    cases h_v : dst.isValidBits pw (decodeCastIntBytes bytes) with
    | false =>
      rw [h_v] at h_dec
      contradiction
    | true =>
      rw [h_v] at h_dec
      injection h_dec with h_val
      subst h_val
      unfold decodeCastPtrBytes
      have h_valid_prop := (ScalarTy.isValidBits_iff_validBits pw dst _).mp h_v
      cases decodeCastPtrProv bytes with
      | none =>
        exact ⟨h_ptr, h_valid_prop, Or.inr ⟨rfl, rfl⟩⟩
      | some allocId =>
        exact ⟨h_ptr, h_valid_prop, Or.inl rfl⟩

/-- Type-safety of `evalTransmuteSameSize`: whenever `evalTransmuteSameSize` returns
`.ok val' exposed'`, the output value `val'` is well-typed for the target descriptor `dst`
(`CastVal.WellTyped pw dst val'`). -/
theorem evalTransmuteSameSize_wellTyped
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (src dst : ScalarTy)
    (val val' : CastVal)
    (exposed exposed' : ExposedProvenance)
    (h_eval : evalTransmuteSameSize pw policy src dst val exposed = .ok val' exposed') :
    CastVal.WellTyped pw dst val' := by
  unfold evalTransmuteSameSize at h_eval
  repeat' split at h_eval
  all_goals try contradiction
  injection h_eval with h_v _
  subst h_v
  exact decodeCastVal_wellTyped pw dst _ _ ‹_›

/-- Type-safety of `evalPtrToPtrCast`: any `.ok val' exposed'` result of `evalPtrToPtrCast`
satisfies `CastVal.WellTyped pw .rawPtr val'`. -/
theorem evalPtrToPtrCast_wellTyped
    (pw : PtrWidth)
    (p : ProvenancePtr)
    (exposed exposed' : ExposedProvenance)
    (prov : Option Nat)
    (val' : CastVal)
    (h_eval : evalPtrToPtrCast pw p exposed prov = .ok val' exposed') :
    CastVal.WellTyped pw .rawPtr val' := by
  unfold evalPtrToPtrCast at h_eval
  cases h_v : ScalarTy.rawPtr.isValidBits pw p.offsetBytes with
  | false =>
    rw [h_v] at h_eval
    contradiction
  | true =>
    rw [h_v] at h_eval
    have h_vp := (ScalarTy.isValidBits_iff_validBits pw .rawPtr p.offsetBytes).mp h_v
    cases prov with
    | none =>
      dsimp only at h_eval
      injection h_eval with h_val _
      subst h_val
      exact ⟨rfl, h_vp, Or.inr ⟨rfl, rfl⟩⟩
    | some allocId =>
      dsimp only at h_eval
      injection h_eval with h_val _
      subst h_val
      exact ⟨rfl, h_vp, Or.inl rfl⟩

/-- Type-safety of `evalIntToPtrExposed`: any `.ok val' exposed'` result of `evalIntToPtrExposed`
satisfies `CastVal.WellTyped pw .rawPtr val'`. -/
theorem evalIntToPtrExposed_wellTyped
    (pw : PtrWidth)
    (addr : Nat)
    (predicted : Option Nat)
    (exposed exposed' : ExposedProvenance)
    (val' : CastVal)
    (h_eval : evalIntToPtrExposed pw addr predicted exposed = .ok val' exposed') :
    CastVal.WellTyped pw .rawPtr val' := by
  unfold evalIntToPtrExposed at h_eval
  cases h_v : ScalarTy.rawPtr.isValidBits pw addr with
  | false =>
    rw [h_v] at h_eval
    contradiction
  | true =>
    rw [h_v] at h_eval
    have h_vp := (ScalarTy.isValidBits_iff_validBits pw .rawPtr addr).mp h_v
    cases predicted with
    | none =>
      dsimp only at h_eval
      injection h_eval with h_val _
      subst h_val
      exact ⟨rfl, h_vp, Or.inr ⟨rfl, rfl⟩⟩
    | some allocId =>
      dsimp only at h_eval
      cases h_exp : isExposedBool allocId exposed with
      | false =>
        rw [h_exp] at h_eval
        contradiction
      | true =>
        rw [h_exp] at h_eval
        injection h_eval with h_val _
        subst h_val
        exact ⟨rfl, h_vp, Or.inl rfl⟩

/-- Helper: any integral `ScalarTy` (`int` or `uint`) with `bits < scalarModulus (ty.sizeBytes pw)`
satisfies `ty.isValidBits pw bits = true`. -/
theorem ScalarTy.isValidBits_of_isIntegral
    (pw : PtrWidth)
    (ty : ScalarTy)
    (bits : Nat)
    (h_int : ty.isIntegral = true)
    (h_bits : bits < scalarModulus (ty.sizeBytes pw)) :
    ty.isValidBits pw bits = true := by
  apply (ScalarTy.isValidBits_iff_validBits pw ty bits).mpr
  cases ty with
  | bool => contradiction
  | char => contradiction
  | int w => exact ⟨h_bits, trivial⟩
  | uint w => exact ⟨h_bits, trivial⟩
  | rawPtr => contradiction
  | refPtr => contradiction

/-- Type-safety of `evalPtrToIntExpose`: any `.ok val' exposed'` result of `evalPtrToIntExpose`
satisfies `CastVal.WellTyped pw dst val'`. -/
theorem evalPtrToIntExpose_wellTyped
    (pw : PtrWidth)
    (dst : ScalarTy)
    (p : ProvenancePtr)
    (exposed exposed' : ExposedProvenance)
    (prov : Option Nat)
    (val' : CastVal)
    (h_eval : evalPtrToIntExpose pw dst p exposed prov = .ok val' exposed') :
    CastVal.WellTyped pw dst val' := by
  unfold evalPtrToIntExpose at h_eval
  cases h_int : dst.isIntegral with
  | false =>
    rw [h_int] at h_eval
    contradiction
  | true =>
    rw [h_int] at h_eval
    dsimp only at h_eval
    cases h_v : ScalarTy.rawPtr.isValidBits pw p.offsetBytes with
    | false =>
      rw [h_v] at h_eval
      contradiction
    | true =>
      rw [h_v] at h_eval
      injection h_eval with h_val _
      subst h_val
      have h_nonptr : dst.isPtr = false := by
        cases dst <;> simp [ScalarTy.isIntegral, ScalarTy.isPtr] at h_int ⊢
      have h_mod_lt :
          p.offsetBytes % scalarModulus (dst.sizeBytes pw) < scalarModulus (dst.sizeBytes pw) :=
        Nat.mod_lt p.offsetBytes (scalarModulus_pos (dst.sizeBytes pw))
      have h_valid_dst := ScalarTy.isValidBits_of_isIntegral pw dst _ h_int h_mod_lt
      exact ⟨h_nonptr, (ScalarTy.isValidBits_iff_validBits pw dst _).mp h_valid_dst⟩

/-- Type-safety of the source-typed deterministic `IntToPtr` evaluator `evalIntToPtrTyped`. -/
theorem evalIntToPtrTyped_wellTyped
    (pw : PtrWidth)
    (src : ScalarTy)
    (bits : Nat)
    (pick : Bool)
    (exposed exposed' : ExposedProvenance)
    (val' : CastVal)
    (h_eval : evalIntToPtrTyped pw src bits pick exposed = .ok val' exposed') :
    CastVal.WellTyped pw .rawPtr val' := by
  unfold evalIntToPtrTyped at h_eval
  cases h_int : src.isIntegral with
  | false =>
    rw [h_int] at h_eval
    contradiction
  | true =>
    rw [h_int] at h_eval
    exact evalIntToPtrExposed_wellTyped pw _ _ exposed exposed' val' h_eval

/-- Type-safety of `evalPtrToIntExposeTyped`: any `.ok val' exposed'` result of
`evalPtrToIntExposeTyped` satisfies `CastVal.WellTyped pw dst val'`. -/
theorem evalPtrToIntExposeTyped_wellTyped
    (pw : PtrWidth)
    (src dst : ScalarTy)
    (p : ProvenancePtr)
    (exposed exposed' : ExposedProvenance)
    (prov : Option Nat)
    (val' : CastVal)
    (h_eval : evalPtrToIntExposeTyped pw src dst p exposed prov = .ok val' exposed') :
    CastVal.WellTyped pw dst val' := by
  unfold evalPtrToIntExposeTyped at h_eval
  cases h_src : src.isPtr with
  | false =>
    rw [h_src] at h_eval
    contradiction
  | true =>
    rw [h_src] at h_eval
    cases h_int : dst.isIntegral with
    | false =>
      rw [h_int] at h_eval
      contradiction
    | true =>
      rw [h_int] at h_eval
      dsimp only [Bool.and] at h_eval
      cases h_v : src.isValidBits pw p.offsetBytes with
      | false =>
        rw [h_v] at h_eval
        contradiction
      | true =>
        rw [h_v] at h_eval
        injection h_eval with h_val _
        subst h_val
        have h_nonptr : dst.isPtr = false := by
          cases dst <;> simp [ScalarTy.isIntegral, ScalarTy.isPtr] at h_int ⊢
        have h_mod_lt :
            p.offsetBytes % scalarModulus (dst.sizeBytes pw) < scalarModulus (dst.sizeBytes pw) :=
          Nat.mod_lt p.offsetBytes (scalarModulus_pos (dst.sizeBytes pw))
        have h_valid_dst := ScalarTy.isValidBits_of_isIntegral pw dst _ h_int h_mod_lt
        exact ⟨h_nonptr, (ScalarTy.isValidBits_iff_validBits pw dst _).mp h_valid_dst⟩

/-- When `exposeProvenance = true`, `evalPtrToIntLowered` coincides with `evalPtrToIntExposeTyped`. -/
@[simp]
theorem evalPtrToIntLowered_true_eq
    (pw : PtrWidth)
    (src dst : ScalarTy)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (prov : Option Nat) :
    evalPtrToIntLowered pw src dst true p exposed prov =
      evalPtrToIntExposeTyped pw src dst p exposed prov := rfl

/-- When `exposeProvenance = false` (`rvalue.rs:2161-2166`), `evalPtrToIntLowered` suppresses
provenance exposure and preserves `exposed` unchanged (`exposed' = exposed`). -/
theorem evalPtrToIntLowered_false_preserves_exposed
    (pw : PtrWidth)
    (src dst : ScalarTy)
    (p : ProvenancePtr)
    (exposed exposed' : ExposedProvenance)
    (prov : Option Nat)
    (val' : CastVal)
    (h_eval : evalPtrToIntLowered pw src dst false p exposed prov = .ok val' exposed') :
    exposed' = exposed := by
  unfold evalPtrToIntLowered evalPtrToIntExposeTyped at h_eval
  repeat' split at h_eval
  all_goals try contradiction
  injection h_eval with _ h_exp
  exact h_exp.symm

/-- Type-safety of `evalPtrToIntLowered`. -/
theorem evalPtrToIntLowered_wellTyped
    (pw : PtrWidth)
    (src dst : ScalarTy)
    (exposeProvenance : Bool)
    (p : ProvenancePtr)
    (exposed exposed' : ExposedProvenance)
    (prov : Option Nat)
    (val' : CastVal)
    (h_eval : evalPtrToIntLowered pw src dst exposeProvenance p exposed prov = .ok val' exposed') :
    CastVal.WellTyped pw dst val' :=
  evalPtrToIntExposeTyped_wellTyped pw src dst p exposed exposed' _ val' h_eval

/-- `intToIntBits` always produces a value strictly below `scalarModulus (dst.sizeBytes pw)`. -/
theorem intToIntBits_lt (pw : PtrWidth) (src dst : ScalarTy) (bits : Nat) :
    intToIntBits pw src dst bits < scalarModulus (dst.sizeBytes pw) := by
  have h_pos : 0 < scalarModulus (dst.sizeBytes pw) := scalarModulus_pos (dst.sizeBytes pw)
  unfold intToIntBits
  cases src with
  | int w =>
    dsimp only
    split
    · exact Nat.mod_lt _ h_pos
    · exact Nat.mod_lt _ h_pos
  | uint w => exact Nat.mod_lt _ h_pos
  | bool => exact Nat.mod_lt _ h_pos
  | char => exact Nat.mod_lt _ h_pos
  | rawPtr => exact Nat.mod_lt _ h_pos
  | refPtr => exact Nat.mod_lt _ h_pos

/-- Type-safety of `evalIntToInt`: any `.ok val' exposed'` result of `evalIntToInt` satisfies
`CastVal.WellTyped pw dst val'`. -/
theorem evalIntToInt_wellTyped
    (pw : PtrWidth)
    (src dst : ScalarTy)
    (bits : Nat)
    (exposed exposed' : ExposedProvenance)
    (val' : CastVal)
    (h_eval : evalIntToInt pw src dst bits exposed = .ok val' exposed') :
    CastVal.WellTyped pw dst val' := by
  unfold evalIntToInt at h_eval
  cases h_gate : Bool.and (Bool.not src.isPtr) dst.isIntToIntTarget with
  | false =>
    rw [h_gate] at h_eval
    contradiction
  | true =>
    rw [h_gate] at h_eval
    dsimp only at h_eval
    have h_dst_target : dst.isIntToIntTarget = true := (Bool.and_eq_true _ _).mp h_gate |>.2
    have h_dst_nonptr : dst.isPtr = false := by
      cases dst <;> simp [ScalarTy.isIntToIntTarget, ScalarTy.isPtr] at h_dst_target ⊢
    split at h_eval
    · contradiction
    · cases h_dv : dst.isValidBits pw (intToIntBits pw src dst bits) with
      | false =>
        rw [h_dv] at h_eval
        contradiction
      | true =>
        rw [h_dv] at h_eval
        injection h_eval with h_val _
        subst h_val
        exact ⟨h_dst_nonptr, (ScalarTy.isValidBits_iff_validBits pw dst _).mp h_dv⟩

/-- Whenever `src` and `dst` have equal byte widths (`src.sizeBytes pw = dst.sizeBytes pw`) and
`bits < scalarModulus (src.sizeBytes pw)`, `intToIntBits` is the identity (`= bits`), whether
`src` is signed (including negative two's-complement values) or unsigned. -/
theorem intToIntBits_of_sizeBytes_eq
    (pw : PtrWidth)
    (src dst : ScalarTy)
    (bits : Nat)
    (h_sz : src.sizeBytes pw = dst.sizeBytes pw)
    (h_bits : bits < scalarModulus (src.sizeBytes pw)) :
    intToIntBits pw src dst bits = bits := by
  unfold intToIntBits
  dsimp only
  rw [← h_sz, Nat.mod_eq_of_lt h_bits]
  cases src with
  | int w =>
    dsimp only
    split
    · exact Nat.mod_eq_of_lt h_bits
    · have h_pos : 0 < scalarModulus ((ScalarTy.int w).sizeBytes pw) := scalarModulus_pos _
      obtain ⟨k, hk⟩ : ∃ k, scalarModulus ((ScalarTy.int w).sizeBytes pw) = k + 1 :=
        ⟨scalarModulus ((ScalarTy.int w).sizeBytes pw) - 1, by omega⟩
      rw [hk] at h_bits ⊢
      have h_split : bits + (k + 1) * (k + 1) - (k + 1) = bits + (k + 1) * k := by
        rw [Nat.mul_succ]
        omega
      rw [h_split, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h_bits]
  | uint w => exact Nat.mod_eq_of_lt h_bits
  | bool => exact Nat.mod_eq_of_lt h_bits
  | char => exact Nat.mod_eq_of_lt h_bits
  | rawPtr => exact Nat.mod_eq_of_lt h_bits
  | refPtr => exact Nat.mod_eq_of_lt h_bits

/-- Transmuting an integer to `ScalarTy.rawPtr` yields a pointer with `Option.none` provenance
(`allocId = 0`, `offsetBytes = bits`, `prov = none`) without modifying `exposed`. -/
theorem transmute_int_to_rawPtr_strips_provenance
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (src : ScalarTy)
    (bits : Nat)
    (exposed : ExposedProvenance)
    (h_int : src.isIntegral = true)
    (h_sz : src.sizeBytes pw = pw.byteSize)
    (h_bits : bits < scalarModulus pw.byteSize) :
    evalTransmuteSameSize pw policy src .rawPtr (.scalar bits) exposed =
      .ok (.ptr { allocId := 0, offsetBytes := bits } none) exposed := by
  have h_nonptr : src.isPtr = false := by
    cases src <;> simp [ScalarTy.isIntegral, ScalarTy.isPtr] at h_int ⊢
  have h_src_valid : src.isValidBits pw bits = true :=
    ScalarTy.isValidBits_of_isIntegral pw src bits h_int (h_sz ▸ h_bits)
  have h_dst_valid : ScalarTy.rawPtr.isValidBits pw bits = true :=
    (ScalarTy.isValidBits_iff_validBits pw .rawPtr bits).mpr ⟨h_bits, trivial⟩
  have h_beq_sz : Nat.beq (src.sizeBytes pw) (ScalarTy.rawPtr.sizeBytes pw) = true := by
    change Nat.beq (src.sizeBytes pw) pw.byteSize = true
    rw [h_sz]
    exact Nat.beq_refl _
  unfold evalTransmuteSameSize encodeCastVal decodeCastVal
  rw [h_beq_sz, h_nonptr]
  dsimp [ScalarTy.isPtr]
  rw [h_src_valid]
  dsimp only
  rw [h_sz, decodeCastIntBytes_encodeCastBytes pw.byteSize bits none h_bits,
      h_dst_valid, decodeCastPtrBytes_encodeCastBytes_none pw.byteSize bits h_bits]
  cases policy <;> rfl

/-- Transmuting `0` (null address) from an integer or raw pointer into `ScalarTy.refPtr`
produces immediate undefined behavior (`.ub`), whereas non-zero addresses succeed. -/
theorem transmute_zero_to_refPtr_ub
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (src : ScalarTy)
    (allocId : Nat)
    (prov : Option Nat)
    (exposed : ExposedProvenance)
    (h_int : src.isIntegral = true)
    (h_sz : src.sizeBytes pw = pw.byteSize) :
    evalTransmuteSameSize pw policy src .refPtr (.scalar 0) exposed = .ub ∧
    evalTransmuteSameSize pw policy .rawPtr .refPtr
        (.ptr { allocId := allocId, offsetBytes := 0 } prov) exposed = .ub := by
  have h_zero_lt : 0 < scalarModulus pw.byteSize := by
    cases pw <;> decide
  have h_nonptr : src.isPtr = false := by
    cases src <;> simp [ScalarTy.isIntegral, ScalarTy.isPtr] at h_int ⊢
  have h_src_valid : src.isValidBits pw 0 = true :=
    ScalarTy.isValidBits_of_isIntegral pw src 0 h_int (h_sz ▸ h_zero_lt)
  have h_raw_valid : ScalarTy.rawPtr.isValidBits pw 0 = true :=
    (ScalarTy.isValidBits_iff_validBits pw .rawPtr 0).mpr ⟨h_zero_lt, trivial⟩
  have h_ref_invalid : ScalarTy.refPtr.isValidBits pw 0 = false := by
    cases pw <;> rfl
  have h_beq_sz : Nat.beq (src.sizeBytes pw) (ScalarTy.refPtr.sizeBytes pw) = true := by
    change Nat.beq (src.sizeBytes pw) pw.byteSize = true
    rw [h_sz]
    exact Nat.beq_refl _
  have h_beq_raw : Nat.beq (ScalarTy.rawPtr.sizeBytes pw) (ScalarTy.refPtr.sizeBytes pw) = true :=
    Nat.beq_refl _
  constructor
  · unfold evalTransmuteSameSize encodeCastVal decodeCastVal
    rw [h_beq_sz, h_nonptr]
    dsimp [ScalarTy.isPtr]
    rw [h_src_valid]
    dsimp only
    rw [h_sz, decodeCastIntBytes_encodeCastBytes pw.byteSize 0 none h_zero_lt, h_ref_invalid]
    cases policy <;> rfl
  · unfold evalTransmuteSameSize encodeCastVal decodeCastVal
    rw [h_beq_raw]
    dsimp [ScalarTy.isPtr, ScalarTy.sizeBytes]
    rw [h_raw_valid]
    dsimp only
    rw [decodeCastIntBytes_encodeCastBytes pw.byteSize 0 prov h_zero_lt, h_ref_invalid]
    cases policy <;> rfl

/-- Identity theorem (`T.decode(T.encode(v)) = v`): for any well-typed `CastVal` of `ty : ScalarTy`,
`evalTransmuteSameSize pw policy ty ty val exposed = .ok val exposed`. -/
theorem transmute_same_ty_id
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (ty : ScalarTy)
    (val : CastVal)
    (exposed : ExposedProvenance)
    (h_wt : CastVal.WellTyped pw ty val) :
    evalTransmuteSameSize pw policy ty ty val exposed = .ok val exposed := by
  have h_sz : Nat.beq (ty.sizeBytes pw) (ty.sizeBytes pw) = true := Nat.beq_refl _
  cases val with
  | scalar bits =>
    rcases h_wt with ⟨h_nonptr, h_valid_prop⟩
    have h_valid : ty.isValidBits pw bits = true :=
      (ScalarTy.isValidBits_iff_validBits pw ty bits).mpr h_valid_prop
    have h_bound : bits < scalarModulus (ty.sizeBytes pw) := h_valid_prop.1
    unfold evalTransmuteSameSize encodeCastVal decodeCastVal
    rw [h_sz, h_nonptr]
    dsimp only
    rw [h_valid]
    dsimp only
    rw [decodeCastIntBytes_encodeCastBytes (ty.sizeBytes pw) bits none h_bound, h_valid]
    cases policy <;> rfl
  | ptr p prov =>
    rcases h_wt with ⟨h_ptr, h_valid_prop, h_prov⟩
    have h_valid : ty.isValidBits pw p.offsetBytes = true :=
      (ScalarTy.isValidBits_iff_validBits pw ty p.offsetBytes).mpr h_valid_prop
    have h_ty_sz : ty.sizeBytes pw = pw.byteSize := by
      cases ty <;> simp [ScalarTy.isPtr, ScalarTy.sizeBytes] at h_ptr ⊢
    have h_bound : p.offsetBytes < scalarModulus pw.byteSize := by
      have hb := h_valid_prop.1
      rw [h_ty_sz] at hb
      exact hb
    unfold evalTransmuteSameSize encodeCastVal decodeCastVal
    rw [h_sz, h_ptr]
    dsimp only
    rw [h_valid]
    dsimp only
    rw [h_ty_sz, decodeCastIntBytes_encodeCastBytes pw.byteSize p.offsetBytes prov h_bound,
        h_valid, decodeCastPtrBytes_encodeCastBytes_ptrWidth pw p prov h_bound]
    rcases h_prov with h_some | ⟨h_none, h_zero⟩
    · subst h_some
      cases p
      cases policy <;> rfl
    · subst h_none
      cases p with
      | mk allocId offsetBytes =>
        dsimp at h_zero
        subst h_zero
        cases policy <;> rfl

/-- Target idempotence of `evalTransmuteSameSize`: if `evalTransmuteSameSize` from `src` to `dst`
succeeds with `.ok val' exposed'`, then transmuting `val'` from `dst` to `dst` is the identity
(`.ok val' exposed'`). -/
theorem evalTransmuteSameSize_idempotent_target
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (src dst : ScalarTy)
    (val val' : CastVal)
    (exposed exposed' : ExposedProvenance)
    (h_eval : evalTransmuteSameSize pw policy src dst val exposed = .ok val' exposed') :
    evalTransmuteSameSize pw policy dst dst val' exposed' = .ok val' exposed' :=
  transmute_same_ty_id pw policy dst val' exposed'
    (evalTransmuteSameSize_wellTyped pw policy src dst val val' exposed exposed' h_eval)

/-- Same-width integer transmute round-trip theorem: for any two integer types `ty1`, `ty2`
(`int` or `uint`) with `ty1.sizeBytes pw = ty2.sizeBytes pw` and valid `bits < scalarModulus (ty1.sizeBytes pw)`,
transmuting `ty1 -> ty2` yields `.ok (.scalar bits) exposed`, and transmuting back `ty2 -> ty1`
recovers the exact original scalar `.ok (.scalar bits) exposed`. -/
theorem transmute_int_roundtrip_same_width
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (ty1 ty2 : ScalarTy)
    (bits : Nat)
    (exposed : ExposedProvenance)
    (h_int1 : ty1.isIntegral = true)
    (h_int2 : ty2.isIntegral = true)
    (h_sz : ty1.sizeBytes pw = ty2.sizeBytes pw)
    (h_bits : bits < scalarModulus (ty1.sizeBytes pw)) :
    evalTransmuteSameSize pw policy ty1 ty2 (.scalar bits) exposed =
      .ok (.scalar bits) exposed ∧
    evalTransmuteSameSize pw policy ty2 ty1 (.scalar bits) exposed =
      .ok (.scalar bits) exposed := by
  have h_nonptr1 : ty1.isPtr = false := by
    cases ty1 <;> simp [ScalarTy.isIntegral, ScalarTy.isPtr] at h_int1 ⊢
  have h_nonptr2 : ty2.isPtr = false := by
    cases ty2 <;> simp [ScalarTy.isIntegral, ScalarTy.isPtr] at h_int2 ⊢
  have h_valid1 : ty1.isValidBits pw bits = true :=
    ScalarTy.isValidBits_of_isIntegral pw ty1 bits h_int1 h_bits
  have h_bits2 : bits < scalarModulus (ty2.sizeBytes pw) := h_sz ▸ h_bits
  have h_valid2 : ty2.isValidBits pw bits = true :=
    ScalarTy.isValidBits_of_isIntegral pw ty2 bits h_int2 h_bits2
  have h_beq12 : Nat.beq (ty1.sizeBytes pw) (ty2.sizeBytes pw) = true := by
    rw [h_sz]; exact Nat.beq_refl _
  have h_beq21 : Nat.beq (ty2.sizeBytes pw) (ty1.sizeBytes pw) = true := by
    rw [h_sz]; exact Nat.beq_refl _
  constructor
  · unfold evalTransmuteSameSize encodeCastVal decodeCastVal
    rw [h_beq12, h_nonptr1, h_nonptr2]
    dsimp only
    rw [h_valid1]
    dsimp only
    rw [decodeCastIntBytes_encodeCastBytes (ty1.sizeBytes pw) bits none h_bits, h_valid2]
    cases policy <;> rfl
  · unfold evalTransmuteSameSize encodeCastVal decodeCastVal
    rw [h_beq21, h_nonptr2, h_nonptr1]
    dsimp only
    rw [h_valid2]
    dsimp only
    rw [decodeCastIntBytes_encodeCastBytes (ty2.sizeBytes pw) bits none h_bits2, h_valid1]
    cases policy <;> rfl

/-- Specialization of `transmute_int_roundtrip_same_width` for signed/unsigned integer pairs
(`ScalarTy.int w` <-> `ScalarTy.uint w`) of the same `IntWidth` `w`. -/
theorem transmute_int_to_int_roundtrip
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (w : IntWidth)
    (bits : Nat)
    (exposed : ExposedProvenance)
    (h_bits : bits < scalarModulus (w.byteSize pw)) :
    evalTransmuteSameSize pw policy (.int w) (.uint w) (.scalar bits) exposed =
      .ok (.scalar bits) exposed ∧
    evalTransmuteSameSize pw policy (.uint w) (.int w) (.scalar bits) exposed =
      .ok (.scalar bits) exposed :=
  transmute_int_roundtrip_same_width pw policy (.int w) (.uint w) bits exposed rfl rfl rfl h_bits

/-- Raw-pointer round-trip theorem: transmuting `rawPtr -> rawPtr` and then `rawPtr -> rawPtr`
recovers the exact original pointer and provenance without modifying `exposed`. -/
theorem transmute_rawPtr_roundtrip
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (h_off : p.offsetBytes < scalarModulus pw.byteSize) :
    evalTransmuteSameSize pw policy .rawPtr .rawPtr (.ptr p (some p.allocId)) exposed =
      .ok (.ptr p (some p.allocId)) exposed ∧
    (match evalTransmuteSameSize pw policy .rawPtr .rawPtr (.ptr p (some p.allocId)) exposed with
     | .ok v' exp' => evalTransmuteSameSize pw policy .rawPtr .rawPtr v' exp'
     | other => other) = .ok (.ptr p (some p.allocId)) exposed := by
  have h_step := (transmute_ptr_to_ptr_eq_ptr_to_ptr pw policy p exposed).2 h_off
  refine ⟨h_step, ?_⟩
  rw [h_step]
  exact h_step

/-! ### Closed forms of `evalTransmuteSameSize` by source/target class -/

namespace ScalarTy

/-- Pointer descriptors are exactly `pw.byteSize` bytes wide. -/
theorem sizeBytes_of_isPtr (pw : PtrWidth) (ty : ScalarTy) (h_ptr : ty.isPtr = true) :
    ty.sizeBytes pw = pw.byteSize := by
  cases ty <;> first | rfl | contradiction

/-- Integral descriptors are not pointer descriptors. -/
theorem isPtr_eq_false_of_isIntegral (ty : ScalarTy) (h_int : ty.isIntegral = true) :
    ty.isPtr = false := by
  cases ty <;> first | rfl | contradiction

end ScalarTy

/-- Closed form of Anneal's same-size transmute between non-pointer scalars: after encoding a
valid source value, the result is decided solely by the target's niche `dst.isValidBits pw`. -/
theorem evalTransmuteSameSize_nonPtr_scalar_eq
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (src dst : ScalarTy)
    (bits : Nat)
    (exposed : ExposedProvenance)
    (h_src : src.isPtr = false)
    (h_dst : dst.isPtr = false)
    (h_sz : src.sizeBytes pw = dst.sizeBytes pw)
    (h_valid : src.validBits pw bits) :
    evalTransmuteSameSize pw policy src dst (.scalar bits) exposed =
      match dst.isValidBits pw bits with
      | true => .ok (.scalar bits) exposed
      | false => .ub := by
  have h_beq : Nat.beq (src.sizeBytes pw) (dst.sizeBytes pw) = true := by
    rw [h_sz]
    exact Nat.beq_refl _
  have h_src_valid : src.isValidBits pw bits = true :=
    (ScalarTy.isValidBits_iff_validBits pw src bits).mpr h_valid
  have h_bound : bits < scalarModulus (src.sizeBytes pw) := h_valid.1
  unfold evalTransmuteSameSize encodeCastVal decodeCastVal
  rw [h_beq, h_src, h_dst]
  dsimp only
  rw [h_src_valid]
  dsimp only
  rw [decodeCastIntBytes_encodeCastBytes (src.sizeBytes pw) bits none h_bound]
  cases dst.isValidBits pw bits <;> cases policy <;> rfl

/-- Closed form of Anneal's `Ptr -> Ptr` transmute (`rawPtr`/`refPtr` in either position) on a
provenance-carrying pointer: provenance and address are preserved unless the target niche
(`refPtr` non-null) rejects the address. -/
theorem evalTransmuteSameSize_ptr_to_ptr_some
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (src dst : ScalarTy)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (h_src : src.isPtr = true)
    (h_dst : dst.isPtr = true)
    (h_src_valid : src.validBits pw p.offsetBytes) :
    evalTransmuteSameSize pw policy src dst (.ptr p (some p.allocId)) exposed =
      match dst.isValidBits pw p.offsetBytes with
      | true => .ok (.ptr p (some p.allocId)) exposed
      | false => .ub := by
  have h_src_sz := ScalarTy.sizeBytes_of_isPtr pw src h_src
  have h_dst_sz := ScalarTy.sizeBytes_of_isPtr pw dst h_dst
  have h_beq : Nat.beq (src.sizeBytes pw) (dst.sizeBytes pw) = true := by
    rw [h_src_sz, h_dst_sz]
    exact Nat.beq_refl _
  have h_sv : src.isValidBits pw p.offsetBytes = true :=
    (ScalarTy.isValidBits_iff_validBits pw src p.offsetBytes).mpr h_src_valid
  have h_bound : p.offsetBytes < scalarModulus pw.byteSize := h_src_sz ▸ h_src_valid.1
  unfold evalTransmuteSameSize encodeCastVal decodeCastVal
  rw [h_beq, h_src, h_dst]
  dsimp only
  rw [h_sv]
  dsimp only
  rw [h_src_sz, decodeCastIntBytes_encodeCastBytes pw.byteSize p.offsetBytes (some p.allocId) h_bound,
    decodeCastPtrBytes_encodeCastBytes_ptrWidth pw p (some p.allocId) h_bound]
  cases p
  cases dst.isValidBits pw _ <;> cases policy <;> rfl

/-- Closed form of Anneal's `Ptr -> Ptr` transmute (`rawPtr`/`refPtr` in either position) on a
**provenance-free** pointer `.ptr p none` (such as a pointer produced by an `Int -> Ptr` transmute
or a partially overwritten pointer): the address `p.offsetBytes` is preserved with `allocId = 0`
and `prov = none` unless the target niche (`refPtr` non-null) rejects the address. -/
theorem evalTransmuteSameSize_ptr_to_ptr_none
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (src dst : ScalarTy)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (h_src : src.isPtr = true)
    (h_dst : dst.isPtr = true)
    (h_src_valid : src.validBits pw p.offsetBytes) :
    evalTransmuteSameSize pw policy src dst (.ptr p none) exposed =
      match dst.isValidBits pw p.offsetBytes with
      | true => .ok (.ptr { allocId := 0, offsetBytes := p.offsetBytes } none) exposed
      | false => .ub := by
  have h_src_sz := ScalarTy.sizeBytes_of_isPtr pw src h_src
  have h_dst_sz := ScalarTy.sizeBytes_of_isPtr pw dst h_dst
  have h_beq : Nat.beq (src.sizeBytes pw) (dst.sizeBytes pw) = true := by
    rw [h_src_sz, h_dst_sz]
    exact Nat.beq_refl _
  have h_sv : src.isValidBits pw p.offsetBytes = true :=
    (ScalarTy.isValidBits_iff_validBits pw src p.offsetBytes).mpr h_src_valid
  have h_bound : p.offsetBytes < scalarModulus pw.byteSize := h_src_sz ▸ h_src_valid.1
  unfold evalTransmuteSameSize encodeCastVal decodeCastVal
  rw [h_beq, h_src, h_dst]
  dsimp only
  rw [h_sv]
  dsimp only
  rw [h_src_sz, decodeCastIntBytes_encodeCastBytes pw.byteSize p.offsetBytes none h_bound,
    decodeCastPtrBytes_encodeCastBytes_none pw.byteSize p.offsetBytes h_bound]
  cases dst.isValidBits pw _ <;> cases policy <;> rfl

/-- Chaining an `Int -> rawPtr` transmute with a subsequent `rawPtr -> dst` (`dst.isPtr = true`)
transmute preserves the provenance-free pointer `{ allocId := 0, offsetBytes := bits }` with
`prov = none` when `dst.isValidBits pw bits = true`, and faults with `.ub` when `dst = .refPtr`
and `bits = 0`. -/
theorem transmute_int_to_rawPtr_to_ptr_chain
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (src dst : ScalarTy)
    (bits : Nat)
    (exposed : ExposedProvenance)
    (h_int : src.isIntegral = true)
    (h_sz : src.sizeBytes pw = pw.byteSize)
    (h_dst : dst.isPtr = true)
    (h_bits : bits < scalarModulus pw.byteSize) :
    (match evalTransmuteSameSize pw policy src .rawPtr (.scalar bits) exposed with
     | .ok v' exp' => evalTransmuteSameSize pw policy .rawPtr dst v' exp'
     | other => other) =
      match dst.isValidBits pw bits with
      | true => .ok (.ptr { allocId := 0, offsetBytes := bits } none) exposed
      | false => .ub := by
  rw [transmute_int_to_rawPtr_strips_provenance pw policy src bits exposed h_int h_sz h_bits]
  exact evalTransmuteSameSize_ptr_to_ptr_none pw policy .rawPtr dst
    { allocId := 0, offsetBytes := bits } exposed rfl h_dst ⟨h_bits, trivial⟩

/-- Closed form of Anneal's `Int -> Ptr` transmute: a provenance-free pointer at address `bits`
unless the target niche (`refPtr` non-null) rejects it. -/
theorem evalTransmuteSameSize_int_to_ptr_eq
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (src dst : ScalarTy)
    (bits : Nat)
    (exposed : ExposedProvenance)
    (h_src : src.isPtr = false)
    (h_dst : dst.isPtr = true)
    (h_sz : src.sizeBytes pw = dst.sizeBytes pw)
    (h_valid : src.validBits pw bits) :
    evalTransmuteSameSize pw policy src dst (.scalar bits) exposed =
      match dst.isValidBits pw bits with
      | true => .ok (.ptr { allocId := 0, offsetBytes := bits } none) exposed
      | false => .ub := by
  have h_beq : Nat.beq (src.sizeBytes pw) (dst.sizeBytes pw) = true := by
    rw [h_sz]
    exact Nat.beq_refl _
  have h_sv : src.isValidBits pw bits = true :=
    (ScalarTy.isValidBits_iff_validBits pw src bits).mpr h_valid
  have h_bound : bits < scalarModulus (src.sizeBytes pw) := h_valid.1
  unfold evalTransmuteSameSize encodeCastVal decodeCastVal
  rw [h_beq, h_src, h_dst]
  dsimp only
  rw [h_sv]
  dsimp only
  rw [decodeCastIntBytes_encodeCastBytes (src.sizeBytes pw) bits none h_bound,
    decodeCastPtrBytes_encodeCastBytes_none (src.sizeBytes pw) bits h_bound]
  cases dst.isValidBits pw bits <;> cases policy <;> rfl

/-- Closed form of Anneal's `Ptr -> Int` transmute under
`TransmutePolicy.allowPtrToIntStripProvenance`: the address bits `p.offsetBytes` with provenance
stripped, subject to the target niche. -/
theorem evalTransmuteSameSize_ptr_to_nonPtr_allow_eq
    (pw : PtrWidth)
    (src dst : ScalarTy)
    (p : ProvenancePtr)
    (prov : Option Nat)
    (exposed : ExposedProvenance)
    (h_src : src.isPtr = true)
    (h_dst : dst.isPtr = false)
    (h_sz : src.sizeBytes pw = dst.sizeBytes pw)
    (h_src_valid : src.validBits pw p.offsetBytes) :
    evalTransmuteSameSize pw .allowPtrToIntStripProvenance src dst (.ptr p prov) exposed =
      match dst.isValidBits pw p.offsetBytes with
      | true => .ok (.scalar p.offsetBytes) exposed
      | false => .ub := by
  have h_beq : Nat.beq (src.sizeBytes pw) (dst.sizeBytes pw) = true := by
    rw [h_sz]
    exact Nat.beq_refl _
  have h_sv : src.isValidBits pw p.offsetBytes = true :=
    (ScalarTy.isValidBits_iff_validBits pw src p.offsetBytes).mpr h_src_valid
  have h_bound : p.offsetBytes < scalarModulus (src.sizeBytes pw) := h_src_valid.1
  unfold evalTransmuteSameSize encodeCastVal decodeCastVal
  rw [h_beq, h_src, h_dst]
  dsimp only
  rw [h_sv]
  dsimp only
  rw [decodeCastIntBytes_encodeCastBytes (src.sizeBytes pw) p.offsetBytes prov h_bound]
  cases dst.isValidBits pw p.offsetBytes <;> rfl

/-- **Episode 1 evaluator pipeline** (`eval_lowered_cast`: `LoweredCast::PtrToInt` followed by
`LoweredCast::IntToPtr` with `pick_exposed_provenance = true`) for any pointer or reference source
and any pointer-sized integral intermediate (`usize`/`isize`, `u64`/`i64` on 64-bit targets):
`PtrToInt` returns the address and exposes `p.allocId`; `IntToPtr` (sign-extension included)
recovers the address exactly and predicts the **least** exposed provenance, which is `p.allocId`
iff no smaller allocation had been exposed. -/
theorem ptrToIntTyped_intToPtrTyped_pipeline
    (pw : PtrWidth)
    (src dst : ScalarTy)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (h_src : src.isPtr = true)
    (h_int : dst.isIntegral = true)
    (h_sz : dst.sizeBytes pw = pw.byteSize)
    (h_valid : src.validBits pw p.offsetBytes) :
    ∃ least,
      leastExposed (exposeProv p.allocId exposed) = some least ∧
      evalPtrToIntExposeTyped pw src dst p exposed =
        .ok (.scalar p.offsetBytes) (exposeProv p.allocId exposed) ∧
      evalIntToPtrTyped pw dst p.offsetBytes true (exposeProv p.allocId exposed) =
        .ok (.ptr { allocId := least, offsetBytes := p.offsetBytes } (some least))
          (exposeProv p.allocId exposed) ∧
      (least = p.allocId ↔ ∀ b ∈ exposed, p.allocId ≤ b) := by
  have h_off : p.offsetBytes < scalarModulus pw.byteSize := by
    have hb := h_valid.1
    rw [ScalarTy.sizeBytes_of_isPtr pw src h_src] at hb
    exact hb
  have h_fit : p.offsetBytes < scalarModulus (dst.sizeBytes pw) := by
    rw [h_sz]
    exact h_off
  obtain ⟨least, h_least, _, _, h_det, h_iff⟩ :=
    ptrToInt_intToPtrDeterministic_picks_least_exposed pw dst p exposed h_int h_off h_fit
  have h_sv : src.isValidBits pw p.offsetBytes = true :=
    (ScalarTy.isValidBits_iff_validBits pw src p.offsetBytes).mpr h_valid
  refine ⟨least, h_least, ?_, ?_, h_iff⟩
  · unfold evalPtrToIntExposeTyped
    rw [h_src, h_int, h_sv, Nat.mod_eq_of_lt h_fit]
    rfl
  · unfold evalIntToPtrTyped
    rw [h_int]
    dsimp only
    rw [intToPtrAddress_ptr_sized pw dst p.offsetBytes h_int h_sz h_off]
    exact h_det

/-- Equivalence of `LoweredCast::PtrToInt` with `expose_provenance = false` (`rvalue.rs:2161-2168`)
and opt-in `Ptr -> Int` transmute (`TransmutePolicy.allowPtrToIntStripProvenance`) for any pointer
or reference source `src` (`src.isPtr = true`) and pointer-sized integral target `dst`
(`dst.isIntegral = true`, `dst.sizeBytes pw = pw.byteSize`): both validate `src.isValidBits pw p.offsetBytes`
(rejecting null `&T` with `.ub`) and return `.ok (.scalar p.offsetBytes) exposed` without
modifying `exposed`. -/
theorem evalPtrToIntLowered_false_eq_transmute_allow
    (pw : PtrWidth)
    (src dst : ScalarTy)
    (p : ProvenancePtr)
    (prov : Option Nat)
    (exposed : ExposedProvenance)
    (h_src : src.isPtr = true)
    (h_int : dst.isIntegral = true)
    (h_sz : dst.sizeBytes pw = pw.byteSize) :
    evalPtrToIntLowered pw src dst false p exposed prov =
      evalTransmuteSameSize pw .allowPtrToIntStripProvenance src dst (.ptr p prov) exposed := by
  have h_src_sz := ScalarTy.sizeBytes_of_isPtr pw src h_src
  have h_dst_np := ScalarTy.isPtr_eq_false_of_isIntegral dst h_int
  have h_beq : Nat.beq (src.sizeBytes pw) (dst.sizeBytes pw) = true := by
    rw [h_src_sz, h_sz]
    exact Nat.beq_refl _
  cases h_sv : src.isValidBits pw p.offsetBytes with
  | false =>
    unfold evalPtrToIntLowered evalPtrToIntExposeTyped evalTransmuteSameSize encodeCastVal
    rw [h_src, h_int, h_dst_np, h_beq]
    dsimp only
    rw [h_sv]
    rfl
  | true =>
    have h_valid := (ScalarTy.isValidBits_iff_validBits pw src p.offsetBytes).mp h_sv
    have h_off : p.offsetBytes < scalarModulus pw.byteSize := h_src_sz ▸ h_valid.1
    have h_fit : p.offsetBytes < scalarModulus (dst.sizeBytes pw) := h_sz ▸ h_off
    have h_dv : dst.isValidBits pw p.offsetBytes = true :=
      ScalarTy.isValidBits_of_isIntegral pw dst p.offsetBytes h_int h_fit
    rw [evalTransmuteSameSize_ptr_to_nonPtr_allow_eq pw src dst p prov exposed h_src h_dst_np
      (h_src_sz.trans h_sz.symm) h_valid, h_dv]
    unfold evalPtrToIntLowered evalPtrToIntExposeTyped
    rw [h_src, h_int, h_sv, Nat.mod_eq_of_lt h_fit]
    rfl

/-- Same-width `IntToInt` vs `Transmute` equivalence: for any two integral types `src`, `dst`
(`src.isIntegral = true`, `dst.isIntegral = true`) of the same byte width
(`src.sizeBytes pw = dst.sizeBytes pw`) and any valid `bits < scalarModulus (src.sizeBytes pw)`,
`evalIntToInt pw src dst bits exposed` and `evalTransmuteSameSize pw policy src dst (.scalar bits) exposed`
both evaluate to `.ok (.scalar bits) exposed`. -/
theorem evalIntToInt_eq_transmute_of_same_width_integral
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (src dst : ScalarTy)
    (bits : Nat)
    (exposed : ExposedProvenance)
    (h_int1 : src.isIntegral = true)
    (h_int2 : dst.isIntegral = true)
    (h_sz : src.sizeBytes pw = dst.sizeBytes pw)
    (h_bits : bits < scalarModulus (src.sizeBytes pw)) :
    evalIntToInt pw src dst bits exposed = .ok (.scalar bits) exposed ∧
    evalTransmuteSameSize pw policy src dst (.scalar bits) exposed = .ok (.scalar bits) exposed ∧
    evalIntToInt pw src dst bits exposed =
      evalTransmuteSameSize pw policy src dst (.scalar bits) exposed := by
  have h_tr := (transmute_int_roundtrip_same_width pw policy src dst bits exposed
    h_int1 h_int2 h_sz h_bits).1
  have h_dst_target : dst.isIntToIntTarget = true := by
    cases dst <;> simp [ScalarTy.isIntegral, ScalarTy.isIntToIntTarget] at h_int2 ⊢
  have h_bits_dst : bits < scalarModulus (dst.sizeBytes pw) := h_sz ▸ h_bits
  have h_dv : dst.isValidBits pw bits = true :=
    ScalarTy.isValidBits_of_isIntegral pw dst bits h_int2 h_bits_dst
  have h_i2i_bits := intToIntBits_of_sizeBytes_eq pw src dst bits h_sz h_bits
  have h_i2i : evalIntToInt pw src dst bits exposed = .ok (.scalar bits) exposed := by
    cases src <;> first
      | contradiction
      | (unfold evalIntToInt; rw [h_dst_target]; dsimp only [ScalarTy.isPtr, Bool.not, Bool.and];
         rw [h_i2i_bits, h_dv])
  exact ⟨h_i2i, h_tr, h_i2i.trans h_tr.symm⟩

/-- Transmute round trip through an integer loses provenance (UCG `#286`): the default policy
rejects `rawPtr -> uint w`; under the opt-in policy, `rawPtr -> uint w -> rawPtr` (pointer-sized
`w`) recovers the address `p.offsetBytes` but only as a provenance-free pointer (`prov = none`),
never the original provenance-carrying `p`. -/
theorem transmute_ptr_int_ptr_roundtrip_strips_provenance
    (pw : PtrWidth)
    (w : IntWidth)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (h_w : w.byteSize pw = pw.byteSize)
    (h_off : p.offsetBytes < scalarModulus pw.byteSize) :
    evalTransmuteSameSize pw .rejectPtrToInt .rawPtr (.uint w) (.ptr p (some p.allocId)) exposed =
      .unsupported ∧
    evalTransmuteSameSize pw .allowPtrToIntStripProvenance .rawPtr (.uint w)
        (.ptr p (some p.allocId)) exposed = .ok (.scalar p.offsetBytes) exposed ∧
    evalTransmuteSameSize pw .allowPtrToIntStripProvenance (.uint w) .rawPtr
        (.scalar p.offsetBytes) exposed =
      .ok (.ptr { allocId := 0, offsetBytes := p.offsetBytes } none) exposed ∧
    (.ok (.ptr { allocId := 0, offsetBytes := p.offsetBytes } none) exposed : CastOutcome) ≠
      .ok (.ptr p (some p.allocId)) exposed := by
  have h_fit : p.offsetBytes < scalarModulus ((ScalarTy.uint w).sizeBytes pw) := by
    show p.offsetBytes < scalarModulus (w.byteSize pw)
    rw [h_w]
    exact h_off
  have h_valid_uint : (ScalarTy.uint w).isValidBits pw p.offsetBytes = true :=
    (ScalarTy.isValidBits_iff_validBits pw (.uint w) p.offsetBytes).mpr ⟨h_fit, trivial⟩
  refine ⟨transmute_ptr_to_int_rejected_by_default_policy pw .rawPtr (.uint w) _ exposed rfl rfl,
    ?_, ?_, ?_⟩
  · rw [evalTransmuteSameSize_ptr_to_nonPtr_allow_eq pw .rawPtr (.uint w) p (some p.allocId) exposed
      rfl rfl h_w.symm ⟨h_off, trivial⟩, h_valid_uint]
  · exact transmute_int_to_rawPtr_strips_provenance pw .allowPtrToIntStripProvenance (.uint w)
      p.offsetBytes exposed rfl h_w h_off
  · intro h
    injection h with h_val _
    injection h_val with _ h_prov
    contradiction

/-- Pointer-width sensitivity of `rawPtr <-> integer` transmutes (`PtrWidth.bits32` vs
`PtrWidth.bits64`): `u32 <-> rawPtr` is a valid same-size transmute on 32-bit targets but a size
mismatch (`.unsupported`) on 64-bit targets, and `u64 <-> rawPtr` is the reverse; valid
`Int -> Ptr` directions never fabricate provenance, and valid `Ptr -> Int` directions return the
address only under the opt-in policy. -/
theorem transmute_rawPtr_int_ptrWidth_contrast
    (policy : TransmutePolicy)
    (p : ProvenancePtr)
    (bits : Nat)
    (exposed : ExposedProvenance)
    (h32 : bits < scalarModulus 4)
    (h64 : bits < scalarModulus 8)
    (h_off32 : p.offsetBytes < scalarModulus 4)
    (h_off64 : p.offsetBytes < scalarModulus 8) :
    evalTransmuteSameSize .bits32 policy .u32 .rawPtr (.scalar bits) exposed =
      .ok (.ptr { allocId := 0, offsetBytes := bits } none) exposed ∧
    evalTransmuteSameSize .bits64 policy .u32 .rawPtr (.scalar bits) exposed = .unsupported ∧
    evalTransmuteSameSize .bits64 policy .u64 .rawPtr (.scalar bits) exposed =
      .ok (.ptr { allocId := 0, offsetBytes := bits } none) exposed ∧
    evalTransmuteSameSize .bits32 policy .u64 .rawPtr (.scalar bits) exposed = .unsupported ∧
    evalTransmuteSameSize .bits32 .allowPtrToIntStripProvenance .rawPtr .u32
        (.ptr p (some p.allocId)) exposed = .ok (.scalar p.offsetBytes) exposed ∧
    evalTransmuteSameSize .bits64 .allowPtrToIntStripProvenance .rawPtr .u32
        (.ptr p (some p.allocId)) exposed = .unsupported ∧
    evalTransmuteSameSize .bits64 .allowPtrToIntStripProvenance .rawPtr .u64
        (.ptr p (some p.allocId)) exposed = .ok (.scalar p.offsetBytes) exposed ∧
    evalTransmuteSameSize .bits64 .rejectPtrToInt .rawPtr .u64
        (.ptr p (some p.allocId)) exposed = .unsupported := by
  refine ⟨transmute_int_to_rawPtr_strips_provenance .bits32 policy .u32 bits exposed rfl rfl h32,
    transmute_size_mismatch_unsupported .bits64 policy .u32 .rawPtr _ exposed (by decide),
    transmute_int_to_rawPtr_strips_provenance .bits64 policy .u64 bits exposed rfl rfl h64,
    transmute_size_mismatch_unsupported .bits32 policy .u64 .rawPtr _ exposed (by decide),
    ?_, transmute_size_mismatch_unsupported .bits64 _ .rawPtr .u32 _ exposed (by decide), ?_,
    transmute_ptr_to_int_rejected_by_default_policy .bits64 .rawPtr .u64 _ exposed rfl rfl⟩
  · have h_v : ScalarTy.u32.isValidBits .bits32 p.offsetBytes = true :=
      (ScalarTy.isValidBits_iff_validBits .bits32 .u32 p.offsetBytes).mpr ⟨h_off32, trivial⟩
    rw [evalTransmuteSameSize_ptr_to_nonPtr_allow_eq .bits32 .rawPtr .u32 p (some p.allocId) exposed
      rfl rfl rfl ⟨h_off32, trivial⟩, h_v]
  · have h_v : ScalarTy.u64.isValidBits .bits64 p.offsetBytes = true :=
      (ScalarTy.isValidBits_iff_validBits .bits64 .u64 p.offsetBytes).mpr ⟨h_off64, trivial⟩
    rw [evalTransmuteSameSize_ptr_to_nonPtr_allow_eq .bits64 .rawPtr .u64 p (some p.allocId) exposed
      rfl rfl rfl ⟨h_off64, trivial⟩, h_v]

/-!
## 5. Niche-Constrained Validity (`bool` and `char`) & Surrogate Boundary Theorems
-/

/-- Exact arithmetic characterization of `Trusted.MirSemantics.isValidCharCode` (`true` case). -/
theorem isValidCharCode_iff (code : Nat) :
    isValidCharCode code = true ↔ (code < 55296 ∨ (57344 ≤ code ∧ code ≤ 1114111)) := by
  unfold isValidCharCode
  simp only [Bool.or_eq_true, Bool.and_eq_true, ScalarTy.not_ble_iff_lt, Nat.ble_eq]

/-- Exact arithmetic characterization of `Trusted.MirSemantics.isValidCharCode` (`false` case). -/
theorem isValidCharCode_eq_false_iff (code : Nat) :
    isValidCharCode code = false ↔ ((55296 ≤ code ∧ code ≤ 57343) ∨ 1114111 < code) := by
  rw [← Bool.not_eq_true, isValidCharCode_iff]
  omega

/-- Helper evaluating `evalTransmuteSameSize` from a 1-byte integral type (`u8` or `i8`) to `bool`. -/
theorem evalTransmuteSameSize_int1_to_bool
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (src : ScalarTy)
    (bits : Nat)
    (exposed : ExposedProvenance)
    (h_int : src.isIntegral = true)
    (h_sz : src.sizeBytes pw = 1)
    (h_bits : bits < 256) :
    evalTransmuteSameSize pw policy src .bool (.scalar bits) exposed =
      if bits ≤ 1 then .ok (.scalar bits) exposed else .ub := by
  have h_mod1 : scalarModulus 1 = 256 := rfl
  have h_bound : bits < scalarModulus 1 := h_mod1.symm ▸ h_bits
  have h_nonptr : src.isPtr = false := by
    cases src <;> simp [ScalarTy.isIntegral, ScalarTy.isPtr] at h_int ⊢
  have h_src_valid : src.isValidBits pw bits = true :=
    ScalarTy.isValidBits_of_isIntegral pw src bits h_int (h_sz ▸ h_bound)
  have h_beq_sz : Nat.beq (src.sizeBytes pw) (ScalarTy.bool.sizeBytes pw) = true := by
    change Nat.beq (src.sizeBytes pw) 1 = true
    rw [h_sz]
    rfl
  unfold evalTransmuteSameSize encodeCastVal decodeCastVal
  rw [h_beq_sz, h_nonptr]
  dsimp [ScalarTy.isPtr]
  rw [h_src_valid]
  dsimp only
  rw [h_sz, decodeCastIntBytes_encodeCastBytes 1 bits none h_bound]
  by_cases h_le : bits ≤ 1
  · have h_bool_valid : ScalarTy.bool.isValidBits pw bits = true :=
      (ScalarTy.isValidBits_iff_validBits pw .bool bits).mpr ⟨h_bound, h_le⟩
    rw [h_bool_valid]
    simp only [h_le, ↓reduceIte]
    cases policy <;> rfl
  · have h_bool_invalid : ScalarTy.bool.isValidBits pw bits = false := by
      apply Bool.eq_false_iff.mpr
      intro h_v
      exact h_le ((ScalarTy.isValidBits_iff_validBits pw .bool bits).mp h_v).2
    rw [h_bool_invalid]
    simp only [h_le, ↓reduceIte]
    cases policy <;> rfl

/-- Niche-constrained `bool` validity theorem: transmuting a 1-byte integer (`u8` or `i8`) with
`bits < 256` into `ScalarTy.bool` succeeds (`.ok (.scalar bits) exposed`) iff `bits ≤ 1`
(equivalently `bits = 0 ∨ bits = 1`), and returns `.ub` iff `2 ≤ bits`. -/
theorem transmute_bool_valid_iff
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (bits : Nat)
    (exposed : ExposedProvenance)
    (h_bits : bits < 256) :
    (evalTransmuteSameSize pw policy .u8 .bool (.scalar bits) exposed =
      .ok (.scalar bits) exposed ↔ bits ≤ 1) ∧
    (evalTransmuteSameSize pw policy .u8 .bool (.scalar bits) exposed =
      .ok (.scalar bits) exposed ↔ (bits = 0 ∨ bits = 1)) ∧
    (evalTransmuteSameSize pw policy .u8 .bool (.scalar bits) exposed = .ub ↔ 2 ≤ bits) ∧
    (evalTransmuteSameSize pw policy .i8 .bool (.scalar bits) exposed =
      .ok (.scalar bits) exposed ↔ bits ≤ 1) ∧
    (evalTransmuteSameSize pw policy .i8 .bool (.scalar bits) exposed = .ub ↔ 2 ≤ bits) := by
  have h_u8 := evalTransmuteSameSize_int1_to_bool pw policy .u8 bits exposed rfl rfl h_bits
  have h_i8 := evalTransmuteSameSize_int1_to_bool pw policy .i8 bits exposed rfl rfl h_bits
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h_u8]
    by_cases h_le : bits ≤ 1 <;> simp [h_le]
  · rw [h_u8]
    by_cases h_le : bits ≤ 1
    · simp only [h_le, ↓reduceIte, true_iff]
      omega
    · simp only [h_le, ↓reduceIte, reduceCtorEq, false_iff]
      omega
  · rw [h_u8]
    by_cases h_le : bits ≤ 1
    · simp only [h_le, ↓reduceIte, reduceCtorEq, false_iff]
      omega
    · simp only [h_le, ↓reduceIte, true_iff]
      omega
  · rw [h_i8]
    by_cases h_le : bits ≤ 1 <;> simp [h_le]
  · rw [h_i8]
    by_cases h_le : bits ≤ 1
    · simp only [h_le, ↓reduceIte, reduceCtorEq, false_iff]
      omega
    · simp only [h_le, ↓reduceIte, true_iff]
      omega

/-- Helper evaluating `evalTransmuteSameSize` from a 4-byte integral type (`u32` or `i32`) to `char`. -/
theorem evalTransmuteSameSize_int4_to_char
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (src : ScalarTy)
    (bits : Nat)
    (exposed : ExposedProvenance)
    (h_int : src.isIntegral = true)
    (h_sz : src.sizeBytes pw = 4)
    (h_bits : bits < scalarModulus 4) :
    evalTransmuteSameSize pw policy src .char (.scalar bits) exposed =
      if isValidCharCode bits = true then .ok (.scalar bits) exposed else .ub := by
  have h_nonptr : src.isPtr = false := by
    cases src <;> simp [ScalarTy.isIntegral, ScalarTy.isPtr] at h_int ⊢
  have h_src_valid : src.isValidBits pw bits = true :=
    ScalarTy.isValidBits_of_isIntegral pw src bits h_int (h_sz ▸ h_bits)
  have h_beq_sz : Nat.beq (src.sizeBytes pw) (ScalarTy.char.sizeBytes pw) = true := by
    change Nat.beq (src.sizeBytes pw) 4 = true
    rw [h_sz]
    rfl
  unfold evalTransmuteSameSize encodeCastVal decodeCastVal
  rw [h_beq_sz, h_nonptr]
  dsimp [ScalarTy.isPtr]
  rw [h_src_valid]
  dsimp only
  rw [h_sz, decodeCastIntBytes_encodeCastBytes 4 bits none h_bits]
  cases h_c : isValidCharCode bits
  · have h_char_invalid : ScalarTy.char.isValidBits pw bits = false := by
      apply Bool.eq_false_iff.mpr
      intro h_v
      have hc := ((ScalarTy.isValidBits_iff_validBits pw .char bits).mp h_v).2
      rw [h_c] at hc
      contradiction
    rw [h_char_invalid]
    dsimp only
    cases policy <;> rfl
  · have h_char_valid : ScalarTy.char.isValidBits pw bits = true :=
      (ScalarTy.isValidBits_iff_validBits pw .char bits).mpr ⟨h_bits, h_c⟩
    rw [h_char_valid]
    dsimp only
    cases policy <;> rfl

/-- Niche-constrained `char` validity theorem: transmuting a 4-byte integer (`u32` or `i32`) with
`bits < scalarModulus 4` (`2^32`) into `ScalarTy.char` succeeds (`.ok (.scalar bits) exposed`) iff
`bits < 55296 ∨ (57344 ≤ bits ∧ bits ≤ 1114111)`, and returns `.ub` on UTF-16 surrogates
(`55296 ≤ bits ∧ bits ≤ 57343`) or above Unicode max (`1114111 < bits`). -/
theorem transmute_char_valid_iff
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (bits : Nat)
    (exposed : ExposedProvenance)
    (h_bits : bits < scalarModulus 4) :
    (evalTransmuteSameSize pw policy .u32 .char (.scalar bits) exposed =
      .ok (.scalar bits) exposed ↔ (bits < 55296 ∨ (57344 ≤ bits ∧ bits ≤ 1114111))) ∧
    (evalTransmuteSameSize pw policy .u32 .char (.scalar bits) exposed = .ub ↔
      ((55296 ≤ bits ∧ bits ≤ 57343) ∨ 1114111 < bits)) ∧
    (evalTransmuteSameSize pw policy .i32 .char (.scalar bits) exposed =
      .ok (.scalar bits) exposed ↔ (bits < 55296 ∨ (57344 ≤ bits ∧ bits ≤ 1114111))) ∧
    (evalTransmuteSameSize pw policy .i32 .char (.scalar bits) exposed = .ub ↔
      ((55296 ≤ bits ∧ bits ≤ 57343) ∨ 1114111 < bits)) := by
  have h_u32 := evalTransmuteSameSize_int4_to_char pw policy .u32 bits exposed rfl rfl h_bits
  have h_i32 := evalTransmuteSameSize_int4_to_char pw policy .i32 bits exposed rfl rfl h_bits
  rw [← isValidCharCode_iff bits, ← isValidCharCode_eq_false_iff bits]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_u32]
    cases h_c : isValidCharCode bits <;> simp
  · rw [h_u32]
    cases h_c : isValidCharCode bits <;> simp
  · rw [h_i32]
    cases h_c : isValidCharCode bits <;> simp
  · rw [h_i32]
    cases h_c : isValidCharCode bits <;> simp

/-- Combined niche-constrained validity range theorem for `bool` and `char`. -/
theorem transmute_bool_char_valid_range_iff
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (b8 b32 : Nat)
    (exposed : ExposedProvenance)
    (h8 : b8 < 256)
    (h32 : b32 < scalarModulus 4) :
    (evalTransmuteSameSize pw policy .u8 .bool (.scalar b8) exposed =
      .ok (.scalar b8) exposed ↔ b8 ≤ 1) ∧
    (evalTransmuteSameSize pw policy .u32 .char (.scalar b32) exposed =
      .ok (.scalar b32) exposed ↔ (b32 < 55296 ∨ (57344 ≤ b32 ∧ b32 ≤ 1114111))) :=
  ⟨(transmute_bool_valid_iff pw policy b8 exposed h8).1,
   (transmute_char_valid_iff pw policy b32 exposed h32).1⟩

/-- On 4-byte integral sources (`src.isIntegral = true`, `src.sizeBytes pw = 4`, e.g. `u32`, `i32`,
or `usize`/`isize` on 32-bit targets), `evalIntToInt pw src .char bits exposed` and
`evalTransmuteSameSize pw policy src .char (.scalar bits) exposed` coincide identically for all
`bits < scalarModulus 4`: both validate `isValidCharCode bits` (`test_b1_eval_int_to_int_validates_char_targets`),
succeeding iff `bits < 55296 ∨ (57344 ≤ bits ∧ bits ≤ 1114111)` and returning `.ub` on UTF-16
surrogates (`55296..=57343`) or above Unicode max (`> 1114111`). -/
theorem evalIntToInt_int4_to_char_eq_transmute
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (src : ScalarTy)
    (bits : Nat)
    (exposed : ExposedProvenance)
    (h_int : src.isIntegral = true)
    (h_sz : src.sizeBytes pw = 4)
    (h_bits : bits < scalarModulus 4) :
    evalIntToInt pw src .char bits exposed =
      evalTransmuteSameSize pw policy src .char (.scalar bits) exposed ∧
    (evalIntToInt pw src .char bits exposed = .ok (.scalar bits) exposed ↔
      (bits < 55296 ∨ (57344 ≤ bits ∧ bits ≤ 1114111))) ∧
    (evalIntToInt pw src .char bits exposed = .ub ↔
      ((55296 ≤ bits ∧ bits ≤ 57343) ∨ 1114111 < bits)) := by
  have h_src_np := ScalarTy.isPtr_eq_false_of_isIntegral src h_int
  have h_sz_eq : src.sizeBytes pw = ScalarTy.char.sizeBytes pw := h_sz
  have h_bits_src : bits < scalarModulus (src.sizeBytes pw) := h_sz ▸ h_bits
  have h_i2i_bits := intToIntBits_of_sizeBytes_eq pw src .char bits h_sz_eq h_bits_src
  have h_sv : src.validBits pw bits :=
    (ScalarTy.isValidBits_iff_validBits pw src bits).mp
      (ScalarTy.isValidBits_of_isIntegral pw src bits h_int h_bits_src)
  have h_tr := evalTransmuteSameSize_nonPtr_scalar_eq pw policy src .char bits exposed
    h_src_np rfl h_sz_eq h_sv
  have h_i2i :
      evalIntToInt pw src .char bits exposed =
        match ScalarTy.char.isValidBits pw bits with
        | true => .ok (.scalar bits) exposed
        | false => .ub := by
    cases src <;> first
      | contradiction
      | (unfold evalIntToInt;
         dsimp only [ScalarTy.isPtr, ScalarTy.isIntToIntTarget, Bool.not, Bool.and];
         rw [h_i2i_bits];
         cases ScalarTy.char.isValidBits pw bits <;> rfl)
  refine ⟨h_i2i.trans h_tr.symm, ?_, ?_⟩
  · rw [h_i2i, ← isValidCharCode_iff bits]
    cases h_c : isValidCharCode bits
    · have h_cv : ScalarTy.char.isValidBits pw bits = false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        have hc := ((ScalarTy.isValidBits_iff_validBits pw .char bits).mp ht).2
        rw [h_c] at hc
        contradiction
      rw [h_cv]
      simp
    · have h_cv : ScalarTy.char.isValidBits pw bits = true :=
        (ScalarTy.isValidBits_iff_validBits pw .char bits).mpr ⟨h_bits, h_c⟩
      rw [h_cv]
      simp
  · rw [h_i2i, ← isValidCharCode_eq_false_iff bits]
    cases h_c : isValidCharCode bits
    · have h_cv : ScalarTy.char.isValidBits pw bits = false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        have hc := ((ScalarTy.isValidBits_iff_validBits pw .char bits).mp ht).2
        rw [h_c] at hc
        contradiction
      rw [h_cv]
      simp
    · have h_cv : ScalarTy.char.isValidBits pw bits = true :=
        (ScalarTy.isValidBits_iff_validBits pw .char bits).mpr ⟨h_bits, h_c⟩
      rw [h_cv]
      simp

/-- Cross-width `IntToInt` vs `Transmute` contrast for `u8 -> char`: every `u8` (`bits < 256`)
is below the UTF-16 surrogate threshold `55296`, so `evalIntToInt pw .u8 .char bits exposed`
always succeeds with `.ok (.scalar bits) exposed`, whereas `evalTransmuteSameSize` rejects
`u8 -> char` with `.unsupported` (size mismatch `1 ≠ 4`). -/
theorem evalIntToInt_u8_to_char_vs_transmute_contrast
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (bits : Nat)
    (exposed : ExposedProvenance)
    (h_bits : bits < 256) :
    evalIntToInt pw .u8 .char bits exposed = .ok (.scalar bits) exposed ∧
    evalTransmuteSameSize pw policy .u8 .char (.scalar bits) exposed = .unsupported := by
  have h_ne : ScalarTy.u8.sizeBytes pw ≠ ScalarTy.char.sizeBytes pw := by
    cases pw <;> decide
  refine ⟨?_, transmute_size_mismatch_unsupported pw policy .u8 .char _ exposed h_ne⟩
  have h_bits4 : bits < scalarModulus 4 := by
    change bits < 4294967296
    omega
  have h_char : isValidCharCode bits = true :=
    (isValidCharCode_iff bits).mpr (Or.inl (by omega))
  have h_cv : ScalarTy.char.isValidBits pw bits = true :=
    (ScalarTy.isValidBits_iff_validBits pw .char bits).mpr ⟨h_bits4, h_char⟩
  unfold evalIntToInt intToIntBits
  dsimp only [ScalarTy.isPtr, ScalarTy.isIntToIntTarget, Bool.not, Bool.and,
    ScalarTy.sizeBytes, IntWidth.byteSize]
  have h_mod1 : scalarModulus 1 = 256 := rfl
  rw [h_mod1, Nat.mod_eq_of_lt h_bits, Nat.mod_eq_of_lt h_bits4, h_cv]

/-- Explicit boundary verification for UTF-16 surrogate endpoints (`55295 = 0xD7FF`,
`55296 = 0xD800`, `57343 = 0xDFFF`, `57344 = 0xE000`), Unicode max (`1114111 = 0x10FFFF`,
`1114112 = 0x110000`), and 32-bit `rawPtr -> char` surrogate rejection. -/
theorem transmute_char_surrogate_and_max_boundaries
    (pw : PtrWidth)
    (policy : TransmutePolicy)
    (allocId : Nat)
    (exposed : ExposedProvenance) :
    evalTransmuteSameSize pw policy .u32 .char (.scalar 55295) exposed =
      .ok (.scalar 55295) exposed ∧
    evalTransmuteSameSize pw policy .u32 .char (.scalar 55296) exposed = .ub ∧
    evalTransmuteSameSize pw policy .u32 .char (.scalar 57343) exposed = .ub ∧
    evalTransmuteSameSize pw policy .u32 .char (.scalar 57344) exposed =
      .ok (.scalar 57344) exposed ∧
    evalTransmuteSameSize pw policy .u32 .char (.scalar 1114111) exposed =
      .ok (.scalar 1114111) exposed ∧
    evalTransmuteSameSize pw policy .u32 .char (.scalar 1114112) exposed = .ub ∧
    evalTransmuteSameSize .bits32 .allowPtrToIntStripProvenance .rawPtr .char
      (.ptr { allocId := allocId, offsetBytes := 55296 } (some allocId)) exposed = .ub := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases pw <;> cases policy <;> rfl
  · cases pw <;> cases policy <;> rfl
  · cases pw <;> cases policy <;> rfl
  · cases pw <;> cases policy <;> rfl
  · cases pw <;> cases policy <;> rfl
  · cases pw <;> cases policy <;> rfl
  · unfold evalTransmuteSameSize encodeCastVal decodeCastVal
    simp only [ScalarTy.sizeBytes, PtrWidth.byteSize, ScalarTy.isPtr, Bool.and_self, Bool.not_false]
    rw [show ScalarTy.isValidBits .bits32 .rawPtr 55296 = true from rfl]
    dsimp only
    rw [decodeCastIntBytes_encodeCastBytes 4 55296 (some allocId) (by decide)]
    rfl

/-! ### Niche validity vs. `rustc`'s layout-level `WrappingRange` (`wrappingRangeContains`) -/

/-- Anneal's `bool` niche coincides with `rustc`'s `bool` scalar layout
`valid_range: 0..=1` (`Trusted.MirSemantics.wrappingRangeContains`). -/
theorem ScalarTy.validBits_bool_iff_wrappingRangeContains (pw : PtrWidth) (bits : Nat) :
    ScalarTy.bool.validBits pw bits ↔ wrappingRangeContains ⟨0, 1⟩ bits = true := by
  have h : wrappingRangeContains ⟨0, 1⟩ bits = Nat.ble bits 1 := by
    show Bool.and (Nat.ble 0 bits) (Nat.ble bits 1) = Nat.ble bits 1
    rw [Nat.ble_eq.mpr (Nat.zero_le bits)]
    rfl
  rw [h, Nat.ble_eq]
  constructor
  · intro hv
    exact hv.2
  · intro hle
    exact ⟨show bits < 256 by omega, hle⟩

/-- Anneal's non-null reference niche coincides with `rustc`'s thin-pointer scalar layout for
`&T`, `valid_range: 1..=(2^(8 * pw.byteSize) - 1)`. -/
theorem ScalarTy.validBits_refPtr_iff_wrappingRangeContains (pw : PtrWidth) (bits : Nat) :
    ScalarTy.refPtr.validBits pw bits ↔
      wrappingRangeContains ⟨1, pw.modulus - 1⟩ bits = true := by
  have hM : 256 ≤ pw.modulus := by
    cases pw <;> decide
  have h_ble : Nat.ble 1 (pw.modulus - 1) = true := Nat.ble_eq.mpr (by omega)
  have h : wrappingRangeContains ⟨1, pw.modulus - 1⟩ bits =
      Bool.and (Nat.ble 1 bits) (Nat.ble bits (pw.modulus - 1)) := by
    show (match Nat.ble 1 (pw.modulus - 1) with
          | true => Bool.and (Nat.ble 1 bits) (Nat.ble bits (pw.modulus - 1))
          | false => Bool.or (Nat.ble 1 bits) (Nat.ble bits (pw.modulus - 1))) = _
    rw [h_ble]
  rw [h, Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq]
  show (bits < pw.modulus ∧ 0 < bits) ↔ _
  omega

/-- Anneal's integer and raw-pointer validity is exactly the full layout range
`valid_range: 0..=(2^(8 * size) - 1)`. -/
theorem ScalarTy.validBits_full_iff_wrappingRangeContains (pw : PtrWidth) (ty : ScalarTy)
    (h_ty : ty = .rawPtr ∨ ty.isIntegral = true) (bits : Nat) :
    ty.validBits pw bits ↔
      wrappingRangeContains ⟨0, scalarModulus (ty.sizeBytes pw) - 1⟩ bits = true := by
  have hM : 0 < scalarModulus (ty.sizeBytes pw) := by
    have h_pos := ScalarTy.sizeBytes_pos pw ty
    generalize ty.sizeBytes pw = n at h_pos ⊢
    induction n with
    | zero => exact Nat.zero_lt_one
    | succ k ih =>
      show 0 < 256 * scalarModulus k
      cases k with
      | zero => decide
      | succ j => have := ih (Nat.succ_pos j); omega
  have h : wrappingRangeContains ⟨0, scalarModulus (ty.sizeBytes pw) - 1⟩ bits =
      Bool.and (Nat.ble 0 bits) (Nat.ble bits (scalarModulus (ty.sizeBytes pw) - 1)) := by
    show (match Nat.ble 0 (scalarModulus (ty.sizeBytes pw) - 1) with
          | true => Bool.and (Nat.ble 0 bits) (Nat.ble bits (scalarModulus (ty.sizeBytes pw) - 1))
          | false => Bool.or (Nat.ble 0 bits) (Nat.ble bits (scalarModulus (ty.sizeBytes pw) - 1))) = _
    rw [Nat.ble_eq.mpr (Nat.zero_le _)]
  have h_snd : ty.validBits pw bits ↔ bits < scalarModulus (ty.sizeBytes pw) := by
    rcases h_ty with h_raw | h_int
    · subst h_raw
      exact ⟨fun hv => hv.1, fun hb => ⟨hb, trivial⟩⟩
    · cases ty with
      | int w => exact ⟨fun hv => hv.1, fun hb => ⟨hb, trivial⟩⟩
      | uint w => exact ⟨fun hv => hv.1, fun hb => ⟨hb, trivial⟩⟩
      | bool => contradiction
      | char => contradiction
      | rawPtr => contradiction
      | refPtr => contradiction
  rw [h_snd, h, Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq]
  omega

/-- `char` validity is **strictly stronger** than its layout niche: `rustc`'s `char` scalar
layout only records `valid_range: 0..=0x10FFFF`, so the UTF-16 surrogate gap
`0xD800..=0xDFFF` is invisible to `wrappingRangeContains` and must be enforced separately via
`isValidCharCode` (as both Anneal's `ScalarTy.validBits` and `Trusted.decodeValueFromBytes` do). -/
theorem ScalarTy.validBits_char_iff_wrappingRangeContains (pw : PtrWidth) (bits : Nat) :
    (ScalarTy.char.validBits pw bits ↔
      (wrappingRangeContains ⟨0, 1114111⟩ bits = true ∧ ¬ (55296 ≤ bits ∧ bits ≤ 57343))) ∧
    wrappingRangeContains ⟨0, 1114111⟩ 55296 = true ∧
    ¬ ScalarTy.char.validBits pw 55296 := by
  have h : wrappingRangeContains ⟨0, 1114111⟩ bits = Nat.ble bits 1114111 := by
    show Bool.and (Nat.ble 0 bits) (Nat.ble bits 1114111) = Nat.ble bits 1114111
    rw [Nat.ble_eq.mpr (Nat.zero_le bits)]
    rfl
  refine ⟨?_, rfl, ?_⟩
  · rw [h, Nat.ble_eq]
    constructor
    · intro hv
      have h_c := (isValidCharCode_iff bits).mp hv.2
      omega
    · intro hb
      refine ⟨?_, (isValidCharCode_iff bits).mpr (by omega)⟩
      show bits < 4294967296
      omega
  · intro hv
    have h_c := (isValidCharCode_iff 55296).mp hv.2
    omega

/-!
## 6. Direct `Trusted.MirSemantics` Bridge & `evalByteCast` Correspondence Theorems
-/

/-- One-step equation for `encodeLittleEndianBytes` on `rem + 1`. -/
theorem trusted_encodeLittleEndianBytes_succ
    (bits rem : Nat) (prov : Option (Nat × Nat)) :
    encodeLittleEndianBytes bits (rem + 1) prov =
      .init (UInt8.ofNat bits) prov :: encodeLittleEndianBytes (Nat.div bits 256) rem prov := rfl

/-- One-step equation for `decodeLittleEndianBytes` on `.init b prov :: rest`. -/
theorem trusted_decodeLittleEndianBytes_init_cons
    (b : UInt8) (prov : Option (Nat × Nat)) (rest : List AbstractByte) :
    decodeLittleEndianBytes (.init b prov :: rest) =
      match decodeLittleEndianBytes rest with
      | .some (highBits, restProv) =>
        .some (Nat.add b.toBitVec.toNat (Nat.mul 256 highBits), mergeByteProvenance prov restProv)
      | .none => .none := rfl

/-- `Trusted.Sequence.length` of `encodeLittleEndianBytes bits numBytes prov` is `numBytes`. -/
@[simp]
theorem trusted_length_encodeLittleEndianBytes
    (bits numBytes : Nat) (prov : Option (Nat × Nat)) :
    Trusted.Sequence.length (encodeLittleEndianBytes bits numBytes prov) = numBytes := by
  induction numBytes generalizing bits with
  | zero => rfl
  | succ rem ih =>
    rw [trusted_encodeLittleEndianBytes_succ]
    change Nat.succ (Trusted.Sequence.length (encodeLittleEndianBytes (Nat.div bits 256) rem prov)) = rem + 1
    rw [ih (Nat.div bits 256)]

/-- `mergeByteProvenance prov .none = prov`. -/
@[simp]
theorem trusted_mergeByteProvenance_none_right (prov : Option (Nat × Nat)) :
    mergeByteProvenance prov .none = prov := by
  cases prov <;> rfl

/-- `mergeByteProvenance prov prov = prov`. -/
@[simp]
theorem trusted_mergeByteProvenance_self (prov : Option (Nat × Nat)) :
    mergeByteProvenance prov prov = prov := by
  cases prov <;> rfl

/-- Decoding `encodeLittleEndianBytes bits (numBytes + 1) prov` via `decodeLittleEndianBytes`
recovers `.some (bits, prov)` whenever `bits < scalarModulus (numBytes + 1)`. -/
theorem trusted_decodeLittleEndianBytes_encodeLittleEndianBytes
    (numBytes bits : Nat)
    (prov : Option (Nat × Nat))
    (h_bits : bits < scalarModulus (numBytes + 1)) :
    decodeLittleEndianBytes (encodeLittleEndianBytes bits (numBytes + 1) prov) =
      .some (bits, prov) := by
  induction numBytes generalizing bits with
  | zero =>
    have h_mod1 : scalarModulus 1 = 256 := rfl
    have h_lt256 : bits < 256 := h_mod1 ▸ h_bits
    rw [trusted_encodeLittleEndianBytes_succ,
        show encodeLittleEndianBytes (Nat.div bits 256) 0 prov = [] from rfl,
        trusted_decodeLittleEndianBytes_init_cons,
        show decodeLittleEndianBytes [] = .some (0, .none) from rfl]
    dsimp only
    rw [trusted_mergeByteProvenance_none_right, uint8_ofNat_toNat_eq_mod]
    simp only [Nat.add_eq, Nat.mul_eq, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt h_lt256]
  | succ rem ih =>
    have h_div : Nat.div bits 256 < scalarModulus (rem + 1) := by
      change bits < 256 * scalarModulus (rem + 1) at h_bits
      have h_d : bits / 256 < scalarModulus (rem + 1) := by omega
      exact h_d
    rw [trusted_encodeLittleEndianBytes_succ, trusted_decodeLittleEndianBytes_init_cons,
        ih (Nat.div bits 256) h_div]
    dsimp only
    rw [trusted_mergeByteProvenance_self, uint8_ofNat_toNat_eq_mod]
    congr 1
    congr 1
    change bits % 256 + 256 * (bits / 256) = bits
    exact Nat.mod_add_div bits 256

/-- General `Trusted.MirSemantics` scalar byte round-trip: for any `bits` and `rem : Nat` with
`bits < scalarModulus (rem + 1)`, `encodeScalarBytes ⟨bits, rem + 1⟩ prov` succeeds and
`decodeScalarBytes` recovers `.some (⟨bits, rem + 1⟩, prov)`. -/
theorem trusted_decodeScalarBytes_encodeScalarBytes
    (rem bits : Nat)
    (prov : Option (Nat × Nat))
    (signed : Bool)
    (h_bits : bits < scalarModulus (rem + 1)) :
    encodeScalarBytes ⟨bits, rem + 1⟩ prov =
      .some (encodeLittleEndianBytes bits (rem + 1) prov) ∧
    decodeScalarBytes (encodeLittleEndianBytes bits (rem + 1) prov) signed =
      .some (⟨bits, rem + 1⟩, prov) := by
  refine ⟨rfl, ?_⟩
  have h_red :
      decodeScalarBytes (encodeLittleEndianBytes bits (rem + 1) prov) signed =
        match decodeLittleEndianBytes (encodeLittleEndianBytes bits (rem + 1) prov) with
        | some (b, p) => some (⟨b, rem + 1⟩, p)
        | none => none := by
    unfold decodeScalarBytes
    rw [trusted_length_encodeLittleEndianBytes]
    rfl
  rw [h_red, trusted_decodeLittleEndianBytes_encodeLittleEndianBytes rem bits prov h_bits]

/-- Direct `Trusted.MirSemantics` correspondence for `decodeValueFromBytes` at `RigidTy.bool`:
decoding `[.init b prov]` at `{ kind := .bool, layoutIdx := lIdx }` (with `fuel + 1`)
returns `.some (.scalar ⟨b.toBitVec.toNat, 1⟩)` iff `b.toBitVec.toNat ≤ 1`, and `.none` iff
`2 ≤ b.toBitVec.toNat`. -/
theorem trusted_decodeValueFromBytes_bool_iff
    (fuel : Nat)
    (layouts : LayoutTable)
    (lIdx : Nat)
    (b : UInt8)
    (prov : Option (Nat × Nat)) :
    (decodeValueFromBytes (fuel + 1) layouts { kind := .bool, layoutIdx := lIdx }
        [.init b prov] =
      .some (.scalar ⟨b.toBitVec.toNat, 1⟩) ↔ b.toBitVec.toNat ≤ 1) ∧
    (decodeValueFromBytes (fuel + 1) layouts { kind := .bool, layoutIdx := lIdx }
        [.init b prov] = .none ↔ 2 ≤ b.toBitVec.toNat) := by
  unfold decodeValueFromBytes
  dsimp only
  generalize hn : b.toBitVec.toNat = n
  cases n with
  | zero =>
    dsimp only
    refine ⟨⟨fun _ => by omega, fun _ => rfl⟩, ⟨fun h => (nomatch h), fun _ => by omega⟩⟩
  | succ m =>
    cases m with
    | zero =>
      dsimp only
      refine ⟨⟨fun _ => by omega, fun _ => rfl⟩, ⟨fun h => (nomatch h), fun _ => by omega⟩⟩
    | succ k =>
      have h_beq0 : Nat.beq (k + 2) 0 = false := rfl
      have h_beq1 : Nat.beq (k + 2) 1 = false := rfl
      rw [h_beq0, h_beq1]
      dsimp only
      refine ⟨⟨fun h => (nomatch h), fun _ => by omega⟩, ⟨fun _ => by omega, fun _ => rfl⟩⟩

/-- Direct `Trusted.MirSemantics` correspondence for `decodeValueFromBytes` at `RigidTy.char`:
decoding 4 initialized little-endian bytes `bs` (`Trusted.Sequence.length bs = 4` and
`decodeScalarBytes bs false = .some (sv, prov)`) at `{ kind := .char, layoutIdx := lIdx }`
(with `fuel + 1`) returns `.some (.scalar sv)` iff `isValidCharCode sv.bits = true`, and
`.none` iff `isValidCharCode sv.bits = false` (equivalently UTF-16 surrogates or `> 0x10FFFF`). -/
theorem trusted_decodeValueFromBytes_char_iff
    (fuel : Nat)
    (layouts : LayoutTable)
    (lIdx : Nat)
    (bs : List AbstractByte)
    (sv : ScalarVal)
    (prov : Option (Nat × Nat))
    (h_len : Trusted.Sequence.length bs = 4)
    (h_dec : decodeScalarBytes bs false = .some (sv, prov)) :
    (decodeValueFromBytes (fuel + 1) layouts { kind := .char, layoutIdx := lIdx } bs =
      .some (.scalar sv) ↔ isValidCharCode sv.bits = true) ∧
    (decodeValueFromBytes (fuel + 1) layouts { kind := .char, layoutIdx := lIdx } bs =
      .some (.scalar sv) ↔ (sv.bits < 55296 ∨ (57344 ≤ sv.bits ∧ sv.bits ≤ 1114111))) ∧
    (decodeValueFromBytes (fuel + 1) layouts { kind := .char, layoutIdx := lIdx } bs =
      .none ↔ isValidCharCode sv.bits = false) := by
  have h_beq_len : Nat.beq (Trusted.Sequence.length bs) 4 = true := by
    rw [h_len]; rfl
  have h_red :
      decodeValueFromBytes (fuel + 1) layouts { kind := .char, layoutIdx := lIdx } bs =
        (match isValidCharCode sv.bits with
         | true => .some (.scalar sv)
         | false => .none : Option Value) := by
    change
      (match Nat.beq (Trusted.Sequence.length bs) 4 with
       | false => .none
       | true =>
         match decodeScalarBytes bs false with
         | .some (s, _) =>
           match isValidCharCode s.bits with
           | true => .some (.scalar s)
           | false => .none
         | .none => .none : Option Value) =
      (match isValidCharCode sv.bits with
       | true => .some (.scalar sv)
       | false => .none : Option Value)
    rw [h_beq_len]
    dsimp only
    rw [h_dec]
  rw [h_red, ← isValidCharCode_iff sv.bits]
  cases h_valid : isValidCharCode sv.bits <;> simp

/-- Thin-pointee predicate mirroring the `isWide` test of `Trusted.MirSemantics`
(`encodeValueToBytes`, `decodeValueFromBytes`, `rigidTyKindByteSize`): pointers to `[T]`,
`str`, and `dyn Trait` are 16-byte wide pointers, every other pointee yields an 8-byte thin
pointer. -/
@[reducible]
def isThinPointee : RigidTy → Bool
  | .slice _ => false
  | .str => false
  | .dynamic _ => false
  | _ => true

/-- `rigidTyKindByteSize` of a thin raw pointer is `8`. -/
theorem trusted_rigidTyKindByteSize_thin_rawPtr
    (m : Mutability) (pointee : RigidTy) (h_thin : isThinPointee pointee = true) :
    rigidTyKindByteSize (.rawPtr m pointee) = some 8 := by
  cases pointee <;> first | rfl | simp [isThinPointee] at h_thin

/-- `rigidTyKindByteSize` of a thin reference is `8`. -/
theorem trusted_rigidTyKindByteSize_thin_ref
    (m : Mutability) (pointee : RigidTy) (h_thin : isThinPointee pointee = true) :
    rigidTyKindByteSize (.ref m pointee) = some 8 := by
  cases pointee <;> first | rfl | simp [isThinPointee] at h_thin

/-- `rigidTyByteSize` of a thin raw pointer is `8`. -/
theorem trusted_rigidTyByteSize_thin_rawPtr
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy) (lIdx : Nat)
    (h_thin : isThinPointee pointee = true) :
    rigidTyByteSize layouts { kind := .rawPtr m pointee, layoutIdx := lIdx } = some 8 := by
  unfold rigidTyByteSize
  rw [trusted_rigidTyKindByteSize_thin_rawPtr m pointee h_thin]

/-- `rigidTyByteSize` of a thin reference is `8`. -/
theorem trusted_rigidTyByteSize_thin_ref
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy) (lIdx : Nat)
    (h_thin : isThinPointee pointee = true) :
    rigidTyByteSize layouts { kind := .ref m pointee, layoutIdx := lIdx } = some 8 := by
  unfold rigidTyByteSize
  rw [trusted_rigidTyKindByteSize_thin_ref m pointee h_thin]

/-- `encodeValueToBytes` of a thin pointer `.ptr p 8` at any thin raw-pointer type attaches
provenance `(p.allocId, p.tag)` to all 8 little-endian offset bytes. -/
theorem trusted_encodeValueToBytes_thin_rawPtr
    (fuel : Nat) (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy) (lIdx : Nat)
    (p : ProvenancePtr) (h_thin : isThinPointee pointee = true) :
    encodeValueToBytes (fuel + 1) layouts { kind := .rawPtr m pointee, layoutIdx := lIdx }
        (.ptr p 8) =
      some (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) := by
  cases pointee <;> first | rfl | simp [isThinPointee] at h_thin

/-- `encodeValueToBytes` of a thin pointer `.ptr p 8` at any thin reference type attaches
provenance `(p.allocId, p.tag)` to all 8 little-endian offset bytes. -/
theorem trusted_encodeValueToBytes_thin_ref
    (fuel : Nat) (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy) (lIdx : Nat)
    (p : ProvenancePtr) (h_thin : isThinPointee pointee = true) :
    encodeValueToBytes (fuel + 1) layouts { kind := .ref m pointee, layoutIdx := lIdx }
        (.ptr p 8) =
      some (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) := by
  cases pointee <;> first | rfl | simp [isThinPointee] at h_thin

/-- Canonical thin branch of `decodeValueFromBytes` at `.rawPtr m pointee` (any thin pointee). -/
theorem trusted_decodeValueFromBytes_thin_rawPtr_eq
    (fuel : Nat) (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy) (lIdx : Nat)
    (bs : List AbstractByte) (h_thin : isThinPointee pointee = true) :
    decodeValueFromBytes (fuel + 1) layouts { kind := .rawPtr m pointee, layoutIdx := lIdx } bs =
      (match Nat.beq (Trusted.Sequence.length bs) 8 with
       | false => .none
       | true =>
         match decodeScalarBytes bs false with
         | .some (sv, prov) =>
           match prov with
           | .some (allocId, _) => .some (.ptr { allocId := allocId, offsetBytes := sv.bits } 8)
           | .none =>
             .some (.ptr { allocId := Nat.div sv.bits 65536, offsetBytes := Nat.mod sv.bits 65536 } 8)
         | .none => .none : Option Value) := by
  cases pointee <;> first | rfl | simp [isThinPointee] at h_thin

/-- Canonical thin branch of `decodeValueFromBytes` at `.ref m pointee` (any thin pointee),
including `Trusted`'s null check on provenance-free bytes. -/
theorem trusted_decodeValueFromBytes_thin_ref_eq
    (fuel : Nat) (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy) (lIdx : Nat)
    (bs : List AbstractByte) (h_thin : isThinPointee pointee = true) :
    decodeValueFromBytes (fuel + 1) layouts { kind := .ref m pointee, layoutIdx := lIdx } bs =
      (match Nat.beq (Trusted.Sequence.length bs) 8 with
       | false => .none
       | true =>
         match decodeScalarBytes bs false with
         | .some (sv, prov) =>
           match prov with
           | .some (allocId, _) => .some (.ptr { allocId := allocId, offsetBytes := sv.bits } 8)
           | .none =>
             match Nat.beq sv.bits 0 with
             | true => .none
             | false =>
               .some (.ptr { allocId := Nat.div sv.bits 65536, offsetBytes := Nat.mod sv.bits 65536 } 8)
         | .none => .none : Option Value) := by
  cases pointee <;> first | rfl | simp [isThinPointee] at h_thin

/-- `decodeValueFromBytes` at any thin raw-pointer type on an 8-byte sequence `bs` whose scalar
decoding carries provenance `(p.allocId, p.tag)` returns `.some (.ptr p 8)`. -/
theorem trusted_decodeValueFromBytes_thin_rawPtr
    (fuel : Nat)
    (layouts : LayoutTable)
    (m : Mutability)
    (pointee : RigidTy)
    (lIdx : Nat)
    (bs : List AbstractByte)
    (p : ProvenancePtr)
    (h_thin : isThinPointee pointee = true)
    (h_len : Trusted.Sequence.length bs = 8)
    (h_dec : decodeScalarBytes bs false = .some (⟨p.offsetBytes, 8⟩, .some (p.allocId, p.tag))) :
    decodeValueFromBytes (fuel + 1) layouts { kind := .rawPtr m pointee, layoutIdx := lIdx } bs =
      .some (.ptr p 8) := by
  have h_beq_len : Nat.beq (Trusted.Sequence.length bs) 8 = true := by
    rw [h_len]; rfl
  rw [trusted_decodeValueFromBytes_thin_rawPtr_eq fuel layouts m pointee lIdx bs h_thin, h_beq_len]
  dsimp only
  rw [h_dec]

/-- `decodeValueFromBytes` at any thin raw-pointer type on provenance-free 8-byte data `bits`
returns `Trusted`'s 64 KiB page-model reconstruction `.ptr (addressToPtr bits) 8`, i.e. it
fabricates allocation `bits / 65536` from the integer (cf. `int_to_ptr_cast_step_correspondence`). -/
theorem trusted_decodeValueFromBytes_thin_rawPtr_no_prov
    (fuel : Nat)
    (layouts : LayoutTable)
    (m : Mutability)
    (pointee : RigidTy)
    (lIdx : Nat)
    (bs : List AbstractByte)
    (bits : Nat)
    (h_thin : isThinPointee pointee = true)
    (h_len : Trusted.Sequence.length bs = 8)
    (h_dec : decodeScalarBytes bs false = .some (⟨bits, 8⟩, .none)) :
    decodeValueFromBytes (fuel + 1) layouts { kind := .rawPtr m pointee, layoutIdx := lIdx } bs =
      .some (.ptr (addressToPtr bits) 8) := by
  have h_beq_len : Nat.beq (Trusted.Sequence.length bs) 8 = true := by
    rw [h_len]; rfl
  rw [trusted_decodeValueFromBytes_thin_rawPtr_eq fuel layouts m pointee lIdx bs h_thin, h_beq_len]
  dsimp only
  rw [h_dec]
  rfl

/-- `decodeValueFromBytes` at any thin reference type on an 8-byte sequence `bs` whose scalar
decoding carries provenance `(p.allocId, p.tag)` returns `.some (.ptr p 8)` — note that
`Trusted` performs *no* null check on provenance-carrying bytes (even when `p.offsetBytes = 0`). -/
theorem trusted_decodeValueFromBytes_thin_ref
    (fuel : Nat)
    (layouts : LayoutTable)
    (m : Mutability)
    (pointee : RigidTy)
    (lIdx : Nat)
    (bs : List AbstractByte)
    (p : ProvenancePtr)
    (h_thin : isThinPointee pointee = true)
    (h_len : Trusted.Sequence.length bs = 8)
    (h_dec : decodeScalarBytes bs false = .some (⟨p.offsetBytes, 8⟩, .some (p.allocId, p.tag))) :
    decodeValueFromBytes (fuel + 1) layouts { kind := .ref m pointee, layoutIdx := lIdx } bs =
      .some (.ptr p 8) := by
  have h_beq_len : Nat.beq (Trusted.Sequence.length bs) 8 = true := by
    rw [h_len]; rfl
  rw [trusted_decodeValueFromBytes_thin_ref_eq fuel layouts m pointee lIdx bs h_thin, h_beq_len]
  dsimp only
  rw [h_dec]

/-- `decodeValueFromBytes` at any thin reference type on provenance-free 8-byte data `bits`
rejects the null address (`bits = 0`) and otherwise returns the page-model pointer
`.ptr (addressToPtr bits) 8`. -/
theorem trusted_decodeValueFromBytes_thin_ref_no_prov
    (fuel : Nat)
    (layouts : LayoutTable)
    (m : Mutability)
    (pointee : RigidTy)
    (lIdx : Nat)
    (bs : List AbstractByte)
    (bits : Nat)
    (h_thin : isThinPointee pointee = true)
    (h_len : Trusted.Sequence.length bs = 8)
    (h_dec : decodeScalarBytes bs false = .some (⟨bits, 8⟩, .none)) :
    decodeValueFromBytes (fuel + 1) layouts { kind := .ref m pointee, layoutIdx := lIdx } bs =
      (match Nat.beq bits 0 with
       | true => .none
       | false => .some (.ptr (addressToPtr bits) 8) : Option Value) := by
  have h_beq_len : Nat.beq (Trusted.Sequence.length bs) 8 = true := by
    rw [h_len]; rfl
  rw [trusted_decodeValueFromBytes_thin_ref_eq fuel layouts m pointee lIdx bs h_thin, h_beq_len]
  dsimp only
  rw [h_dec]
  rfl

/-- General `n`-byte `Trusted` scalar decoding of `encodeLittleEndianBytes` (`0 < n`). -/
theorem trusted_decodeScalarBytes_encodeLittleEndianBytes
    (n bits : Nat)
    (prov : Option (Nat × Nat))
    (signed : Bool)
    (h_pos : 0 < n)
    (h_bits : bits < scalarModulus n) :
    decodeScalarBytes (encodeLittleEndianBytes bits n prov) signed = .some (⟨bits, n⟩, prov) := by
  obtain ⟨rem, rfl⟩ : ∃ rem, n = rem + 1 := ⟨n - 1, by omega⟩
  exact (trusted_decodeScalarBytes_encodeScalarBytes rem bits prov signed h_bits).2

/-- Step-level reduction of `Trusted.MirSemantics.evalByteCast` once the operand value, the
operand type, and both layout sizes are known. -/
theorem trusted_evalByteCast_eq
    (locals locals' : List LocalSlot)
    (op : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (v : Value)
    (srcTy dstTy : Ty)
    (srcSize dstSize : Nat)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok v locals')
    (h_dst_sz : rigidTyByteSize layouts dstTy = some dstSize)
    (h_ty : operandTy localDecls layouts op = some srcTy)
    (h_src_sz : rigidTyByteSize layouts srcTy = some srcSize) :
    evalByteCast locals op dstTy mem localDecls layouts =
      match Nat.beq srcSize dstSize with
      | false => .unsupported
      | true =>
        match (match encodeValueToBytes defaultCodecFuel layouts srcTy v with
               | .some bs => .some bs
               | .none => encodeUntypedValueToBytes defaultCodecFuel v :
               Option (List AbstractByte)) with
        | .none => .ub
        | .some bs =>
          match Nat.beq (Trusted.Sequence.length bs) dstSize with
          | false => .ub
          | true =>
            match decodeValueFromBytes defaultCodecFuel layouts dstTy bs with
            | .some v' => .ok v' locals' mem
            | .none => .ub := by
  unfold evalByteCast
  rw [h_op]
  dsimp only
  rw [h_dst_sz]
  dsimp only
  rw [h_ty]
  dsimp only
  rw [h_src_sz]
  rfl

/-- `Trusted.MirSemantics.evalByteCast` returns `.unsupported` on a layout-size mismatch. -/
theorem trusted_evalByteCast_size_mismatch
    (locals locals' : List LocalSlot)
    (op : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (v : Value)
    (srcTy dstTy : Ty)
    (srcSize dstSize : Nat)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok v locals')
    (h_dst_sz : rigidTyByteSize layouts dstTy = some dstSize)
    (h_ty : operandTy localDecls layouts op = some srcTy)
    (h_src_sz : rigidTyByteSize layouts srcTy = some srcSize)
    (h_ne : srcSize ≠ dstSize) :
    evalByteCast locals op dstTy mem localDecls layouts = .unsupported := by
  have h_beq : Nat.beq srcSize dstSize = false := by
    cases h : Nat.beq srcSize dstSize with
    | false => rfl
    | true => exact False.elim (h_ne (Nat.beq_eq.mp h))
  rw [trusted_evalByteCast_eq locals locals' op mem localDecls layouts v srcTy dstTy srcSize dstSize
    h_op h_dst_sz h_ty h_src_sz, h_beq]

/-- `Trusted.MirSemantics.evalByteCast` on a same-size transmute whose typed encoding
succeeds with `bs` (of the destination length) is exactly `decodeValueFromBytes` at `dstTy`. -/
theorem trusted_evalByteCast_of_encode
    (locals locals' : List LocalSlot)
    (op : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (v : Value)
    (srcTy dstTy : Ty)
    (size : Nat)
    (bs : List AbstractByte)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok v locals')
    (h_dst_sz : rigidTyByteSize layouts dstTy = some size)
    (h_ty : operandTy localDecls layouts op = some srcTy)
    (h_src_sz : rigidTyByteSize layouts srcTy = some size)
    (h_enc : encodeValueToBytes defaultCodecFuel layouts srcTy v = some bs)
    (h_len : Trusted.Sequence.length bs = size) :
    evalByteCast locals op dstTy mem localDecls layouts =
      match decodeValueFromBytes defaultCodecFuel layouts dstTy bs with
      | .some v' => .ok v' locals' mem
      | .none => .ub := by
  have h_len_beq : Nat.beq (Trusted.Sequence.length bs) size = true := by
    rw [h_len]
    exact Nat.beq_refl _
  rw [trusted_evalByteCast_eq locals locals' op mem localDecls layouts v srcTy dstTy size size
    h_op h_dst_sz h_ty h_src_sz, Nat.beq_refl, h_enc]
  dsimp only
  rw [h_len_beq]

/-- Direct `Trusted.MirSemantics` step-level correspondence for `evalByteCast` (`CastKind.transmute`)
from `u8` to `bool`: transmuting a 1-byte unsigned integer `bits < 256` to `bool` returns
`.ok (.scalar ⟨bits, 1⟩) locals' mem` iff `bits ≤ 1`, and returns `.ub` iff `2 ≤ bits`. -/
theorem trusted_evalByteCast_u8_to_bool_iff
    (locals locals' : List LocalSlot)
    (op : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcLIdx dstLIdx : Nat)
    (bits : Nat)
    (h_bits : bits < 256)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar ⟨bits, 1⟩) locals')
    (h_ty : operandTy localDecls layouts op =
      .some { kind := .uint .u8, layoutIdx := srcLIdx }) :
    let targetTy : Ty := { kind := .bool, layoutIdx := dstLIdx }
    (evalByteCast locals op targetTy mem localDecls layouts =
      ok (.scalar ⟨bits, 1⟩) locals' mem ↔ bits ≤ 1) ∧
    (evalByteCast locals op targetTy mem localDecls layouts = ub ↔ 2 ≤ bits) := by
  dsimp only
  have h_red :
      evalByteCast locals op { kind := .bool, layoutIdx := dstLIdx } mem localDecls layouts =
        match decodeValueFromBytes 8 layouts { kind := .bool, layoutIdx := dstLIdx }
            [.init (UInt8.ofNat bits) none] with
        | some v' => ok v' locals' mem
        | none => ub := by
    unfold evalByteCast
    rw [h_op, h_ty]
    rfl
  rw [h_red]
  have h_u8_toNat : (UInt8.ofNat bits).toBitVec.toNat = bits := by
    rw [uint8_ofNat_toNat_eq_mod, Nat.mod_eq_of_lt h_bits]
  have h_bool := trusted_decodeValueFromBytes_bool_iff 7 layouts dstLIdx (UInt8.ofNat bits) none
  rw [h_u8_toNat] at h_bool
  cases h_dec : decodeValueFromBytes 8 layouts { kind := .bool, layoutIdx := dstLIdx }
      [.init (UInt8.ofNat bits) none] with
  | none =>
    rw [h_dec] at h_bool
    have h_ge2 : 2 ≤ bits := h_bool.2.mp rfl
    dsimp only
    refine ⟨⟨fun h => (nomatch h), fun _ => by omega⟩, ⟨fun _ => h_ge2, fun _ => rfl⟩⟩
  | some v' =>
    rw [h_dec] at h_bool
    have h_le1 : bits ≤ 1 := by
      have h_not_ge2 : ¬ (2 ≤ bits) := by
        intro h_ge2
        have h_none := h_bool.2.mpr h_ge2
        nomatch h_none
      omega
    have hv' : v' = .scalar ⟨bits, 1⟩ := by
      have h_some := h_bool.1.mpr h_le1
      injection h_some
    subst hv'
    dsimp only
    refine ⟨⟨fun _ => h_le1, fun _ => rfl⟩, ⟨fun h => (nomatch h), fun _ => by omega⟩⟩

/-- Direct `Trusted.MirSemantics` step-level correspondence for `evalByteCast` (`CastKind.transmute`)
from `u32` to `char`: transmuting a 4-byte unsigned integer `bits < scalarModulus 4` (`2^32`)
to `char` returns `.ok (.scalar ⟨bits, 4⟩) locals' mem` iff `bits < 55296 ∨ (57344 ≤ bits ∧ bits ≤ 1114111)`,
and returns `.ub` iff `(55296 ≤ bits ∧ bits ≤ 57343) ∨ 1114111 < bits`. -/
theorem trusted_evalByteCast_u32_to_char_iff
    (locals locals' : List LocalSlot)
    (op : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcLIdx dstLIdx : Nat)
    (bits : Nat)
    (h_bits : bits < scalarModulus 4)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar ⟨bits, 4⟩) locals')
    (h_ty : operandTy localDecls layouts op =
      .some { kind := .uint .u32, layoutIdx := srcLIdx }) :
    let targetTy : Ty := { kind := .char, layoutIdx := dstLIdx }
    (evalByteCast locals op targetTy mem localDecls layouts =
      ok (.scalar ⟨bits, 4⟩) locals' mem ↔
        (bits < 55296 ∨ (57344 ≤ bits ∧ bits ≤ 1114111))) ∧
    (evalByteCast locals op targetTy mem localDecls layouts = ub ↔
        ((55296 ≤ bits ∧ bits ≤ 57343) ∨ 1114111 < bits)) := by
  dsimp only
  have h_red :
      evalByteCast locals op { kind := .char, layoutIdx := dstLIdx } mem localDecls layouts =
        match decodeValueFromBytes 8 layouts { kind := .char, layoutIdx := dstLIdx }
            (encodeLittleEndianBytes bits 4 none) with
        | some v' => ok v' locals' mem
        | none => ub := by
    unfold evalByteCast
    rw [h_op, h_ty]
    rfl
  rw [h_red]
  have h_len : Trusted.Sequence.length (encodeLittleEndianBytes bits 4 none) = 4 :=
    trusted_length_encodeLittleEndianBytes bits 4 none
  have h_dec_sc : decodeScalarBytes (encodeLittleEndianBytes bits 4 none) false =
      some (⟨bits, 4⟩, none) :=
    (trusted_decodeScalarBytes_encodeScalarBytes 3 bits none false h_bits).2
  have h_char := trusted_decodeValueFromBytes_char_iff 7 layouts dstLIdx
    (encodeLittleEndianBytes bits 4 none) ⟨bits, 4⟩ none h_len h_dec_sc
  rw [← isValidCharCode_iff bits, ← isValidCharCode_eq_false_iff bits]
  cases h_c : isValidCharCode bits
  · have h_none : decodeValueFromBytes 8 layouts { kind := .char, layoutIdx := dstLIdx }
        (encodeLittleEndianBytes bits 4 none) = none := h_char.2.2.mpr h_c
    rw [h_none]
    simp
  · have h_some : decodeValueFromBytes 8 layouts { kind := .char, layoutIdx := dstLIdx }
        (encodeLittleEndianBytes bits 4 none) = .some (.scalar ⟨bits, 4⟩) := h_char.1.mpr h_c
    rw [h_some]
    simp

/-- Direct `Trusted.MirSemantics` step-level correspondence for `evalByteCast` (`CastKind.transmute`)
from any thin raw pointer to any thin reference (`*const T` / `*mut T` -> `&U` / `&mut U`, for
all thin pointees `T`, `U`): `p` (allocation and offset) is preserved (`ok (.ptr p 8) locals' mem`),
because `p`'s provenance tag `.some (p.allocId, p.tag)` is carried through all 8
`AbstractByte.init` elements. -/
theorem trusted_evalByteCast_thin_rawPtr_to_ref_preserves_provenance
    (locals locals' : List LocalSlot)
    (op : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (m1 m2 : Mutability)
    (pt1 pt2 : RigidTy)
    (srcLIdx dstLIdx : Nat)
    (p : ProvenancePtr)
    (h_thin1 : isThinPointee pt1 = true)
    (h_thin2 : isThinPointee pt2 = true)
    (h_off : p.offsetBytes < scalarModulus 8)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.ptr p 8) locals')
    (h_ty : operandTy localDecls layouts op =
      .some { kind := .rawPtr m1 pt1, layoutIdx := srcLIdx }) :
    evalByteCast locals op { kind := .ref m2 pt2, layoutIdx := dstLIdx }
      mem localDecls layouts = ok (.ptr p 8) locals' mem := by
  have h_len := trusted_length_encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))
  have h_dec_sc := trusted_decodeScalarBytes_encodeLittleEndianBytes 8 p.offsetBytes
    (some (p.allocId, p.tag)) false (by decide) h_off
  rw [trusted_evalByteCast_of_encode locals locals' op mem localDecls layouts (.ptr p 8)
      { kind := .rawPtr m1 pt1, layoutIdx := srcLIdx } { kind := .ref m2 pt2, layoutIdx := dstLIdx }
      8 _ h_op (trusted_rigidTyByteSize_thin_ref layouts m2 pt2 dstLIdx h_thin2) h_ty
      (trusted_rigidTyByteSize_thin_rawPtr layouts m1 pt1 srcLIdx h_thin1)
      (trusted_encodeValueToBytes_thin_rawPtr 15 layouts m1 pt1 srcLIdx p h_thin1) h_len,
    show defaultCodecFuel = 15 + 1 from rfl,
    trusted_decodeValueFromBytes_thin_ref 15 layouts m2 pt2 dstLIdx _ p h_thin2 h_len h_dec_sc]

/-- Direct `Trusted.MirSemantics` step-level correspondence for `evalByteCast` (`CastKind.transmute`)
from `u64` (`0`) to any thin reference `&T`: transmuting a provenance-free zero integer
`.scalar ⟨0, 8⟩` into `{ kind := .ref m pointee, layoutIdx := dstLIdx }` produces `ub`
(null reference is invalid). -/
theorem trusted_evalByteCast_u64_zero_to_ref_ub
    (locals locals' : List LocalSlot)
    (op : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (m : Mutability)
    (pointee : RigidTy)
    (srcLIdx dstLIdx : Nat)
    (h_thin : isThinPointee pointee = true)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar ⟨0, 8⟩) locals')
    (h_ty : operandTy localDecls layouts op =
      .some { kind := .uint .u64, layoutIdx := srcLIdx }) :
    evalByteCast locals op { kind := .ref m pointee, layoutIdx := dstLIdx }
      mem localDecls layouts = ub := by
  have h_len := trusted_length_encodeLittleEndianBytes 0 8 none
  have h_dec_sc := trusted_decodeScalarBytes_encodeLittleEndianBytes 8 0 none false
    (by decide) (by decide)
  rw [trusted_evalByteCast_of_encode locals locals' op mem localDecls layouts (.scalar ⟨0, 8⟩)
      { kind := .uint .u64, layoutIdx := srcLIdx } { kind := .ref m pointee, layoutIdx := dstLIdx }
      8 (encodeLittleEndianBytes 0 8 none) h_op
      (trusted_rigidTyByteSize_thin_ref layouts m pointee dstLIdx h_thin) h_ty rfl rfl h_len,
    show defaultCodecFuel = 15 + 1 from rfl,
    trusted_decodeValueFromBytes_thin_ref_no_prov 15 layouts m pointee dstLIdx _ 0 h_thin h_len
      h_dec_sc]

/-- Direct `Trusted.MirSemantics` correspondence theorem for thin `rawPtr` provenance
preservation across `encodeValueToBytes`, `decodeValueFromBytes`, `evalByteCast`, and
`evalRvalue (.cast .transmute ...)`, for **all** thin pointees `pt1`, `pt2` and mutabilities:
1. Encoding a thin pointer `.ptr p 8` (with `p.offsetBytes < scalarModulus 8`) at
   `{ kind := .rawPtr m1 pt1, layoutIdx := srcLIdx }` via `encodeValueToBytes` and decoding at
   `{ kind := .rawPtr m2 pt2, layoutIdx := dstLIdx }` via `decodeValueFromBytes` recovers
   `.some (.ptr p 8)` (preserving both `p.allocId` and `p.offsetBytes`).
2. Step-level `evalByteCast` and `evalRvalue (.cast .transmute op targetTy)` evaluate to
   `ok (.ptr p 8) locals' mem`. -/
theorem trusted_evalByteCast_thin_rawPtr_preserves_provenance
    (fuel : Nat)
    (locals locals' : List LocalSlot)
    (op : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (m1 m2 : Mutability)
    (pt1 pt2 : RigidTy)
    (srcLIdx dstLIdx : Nat)
    (p : ProvenancePtr)
    (h_thin1 : isThinPointee pt1 = true)
    (h_thin2 : isThinPointee pt2 = true)
    (h_off : p.offsetBytes < scalarModulus 8)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.ptr p 8) locals')
    (h_ty : operandTy localDecls layouts op =
      .some { kind := .rawPtr m1 pt1, layoutIdx := srcLIdx }) :
    let srcTy : Ty := { kind := .rawPtr m1 pt1, layoutIdx := srcLIdx }
    let dstTy : Ty := { kind := .rawPtr m2 pt2, layoutIdx := dstLIdx }
    (match encodeValueToBytes (fuel + 1) layouts srcTy (.ptr p 8) with
     | .some bs => decodeValueFromBytes (fuel + 1) layouts dstTy bs
     | .none => .none) = .some (.ptr p 8) ∧
    evalByteCast locals op dstTy mem localDecls layouts =
      ok (.ptr p 8) locals' mem ∧
    evalRvalue locals (.cast .transmute op dstTy) mem localDecls layouts =
      ok (.ptr p 8) locals' mem := by
  dsimp only
  have h_len := trusted_length_encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))
  have h_dec_sc := trusted_decodeScalarBytes_encodeLittleEndianBytes 8 p.offsetBytes
    (some (p.allocId, p.tag)) false (by decide) h_off
  have h_codec :
      (match encodeValueToBytes (fuel + 1) layouts
          { kind := .rawPtr m1 pt1, layoutIdx := srcLIdx } (.ptr p 8) with
       | some bs =>
         decodeValueFromBytes (fuel + 1) layouts { kind := .rawPtr m2 pt2, layoutIdx := dstLIdx } bs
       | none => none) = .some (.ptr p 8) := by
    rw [trusted_encodeValueToBytes_thin_rawPtr fuel layouts m1 pt1 srcLIdx p h_thin1]
    exact trusted_decodeValueFromBytes_thin_rawPtr fuel layouts m2 pt2 dstLIdx _ p h_thin2 h_len
      h_dec_sc
  have h_byteCast :
      evalByteCast locals op { kind := .rawPtr m2 pt2, layoutIdx := dstLIdx }
        mem localDecls layouts = ok (.ptr p 8) locals' mem := by
    rw [trusted_evalByteCast_of_encode locals locals' op mem localDecls layouts (.ptr p 8)
        { kind := .rawPtr m1 pt1, layoutIdx := srcLIdx }
        { kind := .rawPtr m2 pt2, layoutIdx := dstLIdx }
        8 _ h_op (trusted_rigidTyByteSize_thin_rawPtr layouts m2 pt2 dstLIdx h_thin2) h_ty
        (trusted_rigidTyByteSize_thin_rawPtr layouts m1 pt1 srcLIdx h_thin1)
        (trusted_encodeValueToBytes_thin_rawPtr 15 layouts m1 pt1 srcLIdx p h_thin1) h_len,
      show defaultCodecFuel = 15 + 1 from rfl,
      trusted_decodeValueFromBytes_thin_rawPtr 15 layouts m2 pt2 dstLIdx _ p h_thin2 h_len h_dec_sc]
  refine ⟨h_codec, h_byteCast, ?_⟩
  unfold evalRvalue
  exact h_byteCast

/-- Anneal's `bool` niche agrees with `Trusted.MirSemantics.decodeScalarLayoutBytes` on
`rustc`'s `bool` scalar layout `Scalar::Initialized { value: Int(I8, false), valid_range: 0..=1 }`. -/
theorem trusted_decodeScalarLayoutBytes_bool_layout (pw : PtrWidth) (bits : Nat)
    (h_bits : bits < 256) :
    decodeScalarLayoutBytes (.initialized (.int 8 false) ⟨0, 1⟩)
        (encodeLittleEndianBytes bits 1 none) =
      match ScalarTy.bool.isValidBits pw bits with
      | true => some (.scalar ⟨bits, 1⟩)
      | false => none := by
  have h_len := trusted_length_encodeLittleEndianBytes bits 1 none
  have h_dec := (trusted_decodeScalarBytes_encodeScalarBytes 0 bits none false h_bits).2
  have h_beq : Nat.beq (Trusted.Sequence.length (encodeLittleEndianBytes bits 1 none)) 1 = true := by
    rw [h_len]
    rfl
  have h_red : decodeScalarLayoutBytes (.initialized (.int 8 false) ⟨0, 1⟩)
      (encodeLittleEndianBytes bits 1 none) =
      (match Nat.beq (Trusted.Sequence.length (encodeLittleEndianBytes bits 1 none)) 1 with
       | false => .none
       | true =>
         match decodeScalarBytes (encodeLittleEndianBytes bits 1 none) false with
         | .none => .none
         | .some (sv, _) =>
           match wrappingRangeContains ⟨0, 1⟩ sv.bits with
           | false => .none
           | true => .some (.scalar sv) : Option Value) := rfl
  rw [h_red, h_beq]
  dsimp only
  rw [h_dec]
  dsimp only
  cases h_w : wrappingRangeContains ⟨0, 1⟩ bits
  · have h_v : ScalarTy.bool.isValidBits pw bits = false := by
      apply Bool.eq_false_iff.mpr
      intro h_t
      have := (ScalarTy.validBits_bool_iff_wrappingRangeContains pw bits).mp
        ((ScalarTy.isValidBits_iff_validBits pw .bool bits).mp h_t)
      rw [h_w] at this
      contradiction
    rw [h_v]
  · have h_v : ScalarTy.bool.isValidBits pw bits = true :=
      (ScalarTy.isValidBits_iff_validBits pw .bool bits).mpr
        ((ScalarTy.validBits_bool_iff_wrappingRangeContains pw bits).mpr h_w)
    rw [h_v]

/-!
## 7. Model-to-`Trusted` Refinement: `evalTransmuteSameSize` vs. `Trusted.MirSemantics.evalByteCast`

The theorems of Sections 4–5 characterize Anneal's own transmute model `evalTransmuteSameSize`;
this section proves that the model *agrees* with `Trusted.MirSemantics.evalByteCast`
(`Rvalue.cast .transmute`) on 64-bit targets (`PtrWidth.bits64`, the only width modeled by
`Trusted`), and isolates the exact points where `Trusted` is more permissive.
-/

namespace IntWidth

/-- Inverse of `IntWidth.ofTrustedUintTy`. -/
@[reducible]
def toTrustedUintTy : IntWidth → UintTy
  | .w8 => .u8
  | .w16 => .u16
  | .w32 => .u32
  | .w64 => .u64
  | .w128 => .u128
  | .wsize => .usize

/-- Inverse of `IntWidth.ofTrustedIntTy`. -/
@[reducible]
def toTrustedIntTy : IntWidth → IntTy
  | .w8 => .i8
  | .w16 => .i16
  | .w32 => .i32
  | .w64 => .i64
  | .w128 => .i128
  | .wsize => .isize

theorem ofTrustedUintTy_toTrustedUintTy (w : IntWidth) :
    ofTrustedUintTy w.toTrustedUintTy = w := by
  cases w <;> rfl

theorem ofTrustedIntTy_toTrustedIntTy (w : IntWidth) :
    ofTrustedIntTy w.toTrustedIntTy = w := by
  cases w <;> rfl

/-- `Trusted.MirSemantics.intCastTargetBytes` agrees with `IntWidth.byteSize .bits64`. -/
theorem intCastTargetBytes_uint (w : IntWidth) :
    intCastTargetBytes (.uint w.toTrustedUintTy) = some (w.byteSize .bits64) := by
  cases w <;> rfl

/-- `Trusted.MirSemantics.intCastTargetBytes` agrees with `IntWidth.byteSize .bits64`. -/
theorem intCastTargetBytes_int (w : IntWidth) :
    intCastTargetBytes (.int w.toTrustedIntTy) = some (w.byteSize .bits64) := by
  cases w <;> rfl

end IntWidth

namespace ScalarTy

/-- `Trusted.MirAst.RigidTy` image of a scalar descriptor; pointer descriptors use mutability
`m` and pointee `pointee` (`rawPtr ↦ *m pointee`, `refPtr ↦ &m pointee`). -/
@[reducible]
def toTrustedRigidTy (m : Mutability) (pointee : RigidTy) : ScalarTy → RigidTy
  | .bool => .bool
  | .char => .char
  | .int w => .int w.toTrustedIntTy
  | .uint w => .uint w.toTrustedUintTy
  | .rawPtr => .rawPtr m pointee
  | .refPtr => .ref m pointee

/-- `Trusted.MirSemantics.rigidTyKindByteSize` agrees with `ScalarTy.sizeBytes .bits64` on
every non-pointer scalar descriptor. -/
theorem rigidTyKindByteSize_toTrustedRigidTy_of_not_isPtr
    (m : Mutability) (pointee : RigidTy) (ty : ScalarTy) (h_ty : ty.isPtr = false) :
    rigidTyKindByteSize (ty.toTrustedRigidTy m pointee) = some (ty.sizeBytes .bits64) := by
  cases ty with
  | bool => rfl
  | char => rfl
  | int w => cases w <;> rfl
  | uint w => cases w <;> rfl
  | rawPtr => contradiction
  | refPtr => contradiction

/-- `Trusted.MirSemantics.rigidTyKindByteSize` agrees with `ScalarTy.sizeBytes .bits64` on
every scalar descriptor whose pointee (for pointer descriptors) is thin. -/
theorem rigidTyKindByteSize_toTrustedRigidTy
    (m : Mutability) (pointee : RigidTy) (ty : ScalarTy)
    (h_thin : isThinPointee pointee = true) :
    rigidTyKindByteSize (ty.toTrustedRigidTy m pointee) = some (ty.sizeBytes .bits64) := by
  cases ty with
  | bool => rfl
  | char => rfl
  | int w => cases w <;> rfl
  | uint w => cases w <;> rfl
  | rawPtr => cases pointee <;> first | rfl | simp [isThinPointee] at h_thin
  | refPtr => cases pointee <;> first | rfl | simp [isThinPointee] at h_thin

/-- `Trusted.MirSemantics.rigidTyByteSize` agrees with `ScalarTy.sizeBytes .bits64`. -/
theorem rigidTyByteSize_toTrustedRigidTy
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy) (ty : ScalarTy) (lIdx : Nat)
    (h_thin : isThinPointee pointee = true) :
    rigidTyByteSize layouts { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx } =
      some (ty.sizeBytes .bits64) := by
  unfold rigidTyByteSize
  rw [rigidTyKindByteSize_toTrustedRigidTy m pointee ty h_thin]

/-- `Trusted.MirSemantics.rigidTyByteSize` agrees with `ScalarTy.sizeBytes .bits64` on
non-pointer scalar descriptors. -/
theorem rigidTyByteSize_toTrustedRigidTy_of_not_isPtr
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy) (ty : ScalarTy) (lIdx : Nat)
    (h_ty : ty.isPtr = false) :
    rigidTyByteSize layouts { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx } =
      some (ty.sizeBytes .bits64) := by
  unfold rigidTyByteSize
  rw [rigidTyKindByteSize_toTrustedRigidTy_of_not_isPtr m pointee ty h_ty]

end ScalarTy

/-- `Trusted.MirSemantics.Value` image of a `CastVal` of type `ty` under `pw`: scalars carry
their byte width; provenance-carrying pointers map to `.ptr { allocId, offsetBytes }`; and
provenance-free pointers map to `Trusted`'s 64 KiB page-model reconstruction
`.ptr (addressToPtr addr)` (what `decodeValueFromBytes` produces from provenance-free bytes). -/
def CastVal.toTrustedValue (pw : PtrWidth) (ty : ScalarTy) : CastVal → Value
  | .scalar bits => .scalar ⟨bits, ty.sizeBytes pw⟩
  | .ptr p (some allocId) =>
    .ptr { allocId := allocId, offsetBytes := p.offsetBytes } pw.byteSize
  | .ptr p none => .ptr (addressToPtr p.offsetBytes) pw.byteSize

/-- `Trusted.MirSemantics.RvalueEvalResult` image of a `CastOutcome` of target type `dst`
(dropping `ExposedProvenance`, which `Trusted` does not track). -/
def CastOutcome.toTrustedResult (pw : PtrWidth) (dst : ScalarTy) (locals : List LocalSlot)
    (mem : Memory) : CastOutcome → RvalueEvalResult
  | .ok v _ => .ok (v.toTrustedValue pw dst) locals mem
  | .ub => .ub
  | .unsupported => .unsupported

/-- `Trusted.MirSemantics.encodeValueToBytes` on a valid non-pointer scalar of type `src`
(`bool`, `char`, `int`, `uint`) at `PtrWidth.bits64` yields exactly
`encodeLittleEndianBytes bits (src.sizeBytes .bits64) none`, the `Trusted` image of Anneal's
`encodeCastBytes bits (src.sizeBytes .bits64) none` (`map_toTrustedAbstractByte_encodeCastBytes`). -/
theorem trusted_encodeValueToBytes_scalar
    (fuel : Nat)
    (layouts : LayoutTable)
    (m : Mutability)
    (pointee : RigidTy)
    (src : ScalarTy)
    (lIdx bits : Nat)
    (h_src : src.isPtr = false)
    (h_valid : src.validBits .bits64 bits) :
    encodeValueToBytes (fuel + 1) layouts { kind := src.toTrustedRigidTy m pointee, layoutIdx := lIdx }
        (.scalar ⟨bits, src.sizeBytes .bits64⟩) =
      some (encodeLittleEndianBytes bits (src.sizeBytes .bits64) none) := by
  cases src with
  | bool =>
    have h_le : bits ≤ 1 := h_valid.2
    have h01 : bits = 0 ∨ bits = 1 := by omega
    rcases h01 with h0 | h1
    · subst h0
      rfl
    · subst h1
      rfl
  | char =>
    have h_c : isValidCharCode bits = true := h_valid.2
    have h_red :
        encodeValueToBytes (fuel + 1) layouts { kind := .char, layoutIdx := lIdx }
            (.scalar ⟨bits, 4⟩) =
          (match isValidCharCode bits with
           | true => some (encodeLittleEndianBytes bits 4 none)
           | false => none) := rfl
    change encodeValueToBytes (fuel + 1) layouts { kind := .char, layoutIdx := lIdx }
        (.scalar ⟨bits, 4⟩) = some (encodeLittleEndianBytes bits 4 none)
    rw [h_red, h_c]
  | int w => cases w <;> rfl
  | uint w => cases w <;> rfl
  | rawPtr => contradiction
  | refPtr => contradiction

/-- `Trusted.MirSemantics.decodeValueFromBytes` at `RigidTy.int iw` on bytes whose scalar
decoding is `sv`. -/
theorem trusted_decodeValueFromBytes_int_of_decodeScalarBytes
    (fuel : Nat)
    (layouts : LayoutTable)
    (iw : IntTy)
    (lIdx n : Nat)
    (bs : List AbstractByte)
    (sv : ScalarVal)
    (prov : Option (Nat × Nat))
    (h_n : intCastTargetBytes (.int iw) = some n)
    (h_len : Trusted.Sequence.length bs = n)
    (h_dec : decodeScalarBytes bs true = some (sv, prov)) :
    decodeValueFromBytes (fuel + 1) layouts { kind := .int iw, layoutIdx := lIdx } bs =
      some (.scalar sv) := by
  have h_beq : Nat.beq (Trusted.Sequence.length bs) n = true := by
    rw [h_len]
    exact Nat.beq_refl _
  change
    (match intCastTargetBytes (.int iw) with
     | .some expectedBytes =>
       match Nat.beq (Trusted.Sequence.length bs) expectedBytes with
       | false => .none
       | true =>
         match decodeScalarBytes bs true with
         | .some (sv, _) => .some (.scalar sv)
         | .none => .none
     | .none => .none : Option Value) = _
  rw [h_n]
  dsimp only
  rw [h_beq]
  dsimp only
  rw [h_dec]

/-- `Trusted.MirSemantics.decodeValueFromBytes` at `RigidTy.uint uw` on bytes whose scalar
decoding is `sv`. -/
theorem trusted_decodeValueFromBytes_uint_of_decodeScalarBytes
    (fuel : Nat)
    (layouts : LayoutTable)
    (uw : UintTy)
    (lIdx n : Nat)
    (bs : List AbstractByte)
    (sv : ScalarVal)
    (prov : Option (Nat × Nat))
    (h_n : intCastTargetBytes (.uint uw) = some n)
    (h_len : Trusted.Sequence.length bs = n)
    (h_dec : decodeScalarBytes bs false = some (sv, prov)) :
    decodeValueFromBytes (fuel + 1) layouts { kind := .uint uw, layoutIdx := lIdx } bs =
      some (.scalar sv) := by
  have h_beq : Nat.beq (Trusted.Sequence.length bs) n = true := by
    rw [h_len]
    exact Nat.beq_refl _
  change
    (match intCastTargetBytes (.uint uw) with
     | .some expectedBytes =>
       match Nat.beq (Trusted.Sequence.length bs) expectedBytes with
       | false => .none
       | true =>
         match decodeScalarBytes bs false with
         | .some (sv, _) => .some (.scalar sv)
         | .none => .none
     | .none => .none : Option Value) = _
  rw [h_n]
  dsimp only
  rw [h_beq]
  dsimp only
  rw [h_dec]

/-- `Trusted.MirSemantics.decodeValueFromBytes` at a non-pointer scalar type `dst` on the
encoding of `bits` succeeds (with `.scalar ⟨bits, dst.sizeBytes .bits64⟩`) exactly when Anneal's
`ScalarTy.isValidBits .bits64 dst bits` holds — i.e. `Trusted`'s `bool` / `char` validity checks
coincide with Anneal's niche model. -/
theorem trusted_decodeValueFromBytes_scalar
    (fuel : Nat)
    (layouts : LayoutTable)
    (m : Mutability)
    (pointee : RigidTy)
    (dst : ScalarTy)
    (lIdx bits : Nat)
    (h_dst : dst.isPtr = false)
    (h_bits : bits < scalarModulus (dst.sizeBytes .bits64)) :
    decodeValueFromBytes (fuel + 1) layouts { kind := dst.toTrustedRigidTy m pointee, layoutIdx := lIdx }
        (encodeLittleEndianBytes bits (dst.sizeBytes .bits64) none) =
      match dst.isValidBits .bits64 bits with
      | true => some (.scalar ⟨bits, dst.sizeBytes .bits64⟩)
      | false => none := by
  have h_len : Trusted.Sequence.length (encodeLittleEndianBytes bits (dst.sizeBytes .bits64) none) =
      dst.sizeBytes .bits64 :=
    trusted_length_encodeLittleEndianBytes bits _ none
  have h_dec : ∀ signed : Bool,
      decodeScalarBytes (encodeLittleEndianBytes bits (dst.sizeBytes .bits64) none) signed =
        some (⟨bits, dst.sizeBytes .bits64⟩, none) := fun signed =>
    trusted_decodeScalarBytes_encodeLittleEndianBytes _ bits none signed
      (ScalarTy.sizeBytes_pos .bits64 dst) h_bits
  cases dst with
  | bool =>
    have h256 : bits < 256 := h_bits
    have h_toNat : (UInt8.ofNat bits).toBitVec.toNat = bits := by
      rw [uint8_ofNat_toNat_eq_mod, Nat.mod_eq_of_lt h256]
    have h_iff := trusted_decodeValueFromBytes_bool_iff fuel layouts lIdx (UInt8.ofNat bits) none
    rw [h_toNat] at h_iff
    change decodeValueFromBytes (fuel + 1) layouts { kind := .bool, layoutIdx := lIdx }
        [.init (UInt8.ofNat bits) none] = _
    by_cases h_le : bits ≤ 1
    · have h_v : ScalarTy.bool.isValidBits .bits64 bits = true :=
        (ScalarTy.isValidBits_iff_validBits .bits64 .bool bits).mpr ⟨h_bits, h_le⟩
      rw [h_v]
      exact h_iff.1.mpr h_le
    · have h_v : ScalarTy.bool.isValidBits .bits64 bits = false := by
        apply Bool.eq_false_iff.mpr
        intro h_t
        exact h_le ((ScalarTy.isValidBits_iff_validBits .bits64 .bool bits).mp h_t).2
      rw [h_v]
      exact h_iff.2.mpr (by omega)
  | char =>
    have h_char := trusted_decodeValueFromBytes_char_iff fuel layouts lIdx
      (encodeLittleEndianBytes bits 4 none) ⟨bits, 4⟩ none h_len (h_dec false)
    change decodeValueFromBytes (fuel + 1) layouts { kind := .char, layoutIdx := lIdx }
        (encodeLittleEndianBytes bits 4 none) = _
    cases h_c : isValidCharCode bits
    · have h_v : ScalarTy.char.isValidBits .bits64 bits = false := by
        apply Bool.eq_false_iff.mpr
        intro h_t
        have hc := ((ScalarTy.isValidBits_iff_validBits .bits64 .char bits).mp h_t).2
        rw [h_c] at hc
        contradiction
      rw [h_v]
      exact h_char.2.2.mpr h_c
    · have h_v : ScalarTy.char.isValidBits .bits64 bits = true :=
        (ScalarTy.isValidBits_iff_validBits .bits64 .char bits).mpr ⟨h_bits, h_c⟩
      rw [h_v]
      exact h_char.1.mpr h_c
  | int w =>
    have h_v : (ScalarTy.int w).isValidBits .bits64 bits = true :=
      (ScalarTy.isValidBits_iff_validBits .bits64 (.int w) bits).mpr ⟨h_bits, trivial⟩
    rw [h_v]
    exact trusted_decodeValueFromBytes_int_of_decodeScalarBytes fuel layouts w.toTrustedIntTy lIdx
      (w.byteSize .bits64) _ ⟨bits, w.byteSize .bits64⟩ none (IntWidth.intCastTargetBytes_int w)
      h_len (h_dec true)
  | uint w =>
    have h_v : (ScalarTy.uint w).isValidBits .bits64 bits = true :=
      (ScalarTy.isValidBits_iff_validBits .bits64 (.uint w) bits).mpr ⟨h_bits, trivial⟩
    rw [h_v]
    exact trusted_decodeValueFromBytes_uint_of_decodeScalarBytes fuel layouts w.toTrustedUintTy lIdx
      (w.byteSize .bits64) _ ⟨bits, w.byteSize .bits64⟩ none (IntWidth.intCastTargetBytes_uint w)
      h_len (h_dec false)
  | rawPtr => contradiction
  | refPtr => contradiction

/-- **Scalar transmute refinement theorem.** For every pair of non-pointer scalar types
`src`, `dst` (`bool`, `char`, `i8..i128`/`isize`, `u8..u128`/`usize`), every policy, and every
valid source value, `Trusted.MirSemantics.evalByteCast` (`Rvalue.cast .transmute`) on 64-bit
targets computes *exactly* the `Trusted` image of Anneal's `evalTransmuteSameSize`: identical
`.unsupported` on size mismatch, identical `.ub` on target niche violations (`bool ∉ {0, 1}`,
`char` surrogates / `> 0x10FFFF`), and identical results otherwise. This subsumes `u8 -> bool`,
`u32 -> char`, `bool -> u8`, `char -> u32`, and all `int <-> uint` transmutes. -/
theorem trusted_evalByteCast_scalar_transmute_correspondence
    (policy : TransmutePolicy)
    (src dst : ScalarTy)
    (m1 m2 : Mutability)
    (pt1 pt2 : RigidTy)
    (bits : Nat)
    (exposed : ExposedProvenance)
    (locals locals' : List LocalSlot)
    (op : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcLIdx dstLIdx : Nat)
    (h_src : src.isPtr = false)
    (h_dst : dst.isPtr = false)
    (h_valid : src.validBits .bits64 bits)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar ⟨bits, src.sizeBytes .bits64⟩) locals')
    (h_ty : operandTy localDecls layouts op =
      .some { kind := src.toTrustedRigidTy m1 pt1, layoutIdx := srcLIdx }) :
    evalByteCast locals op { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx }
        mem localDecls layouts =
      CastOutcome.toTrustedResult .bits64 dst locals' mem
        (evalTransmuteSameSize .bits64 policy src dst (.scalar bits) exposed) := by
  have h_dst_sz := ScalarTy.rigidTyByteSize_toTrustedRigidTy_of_not_isPtr layouts m2 pt2 dst
    dstLIdx h_dst
  have h_src_sz := ScalarTy.rigidTyByteSize_toTrustedRigidTy_of_not_isPtr layouts m1 pt1 src
    srcLIdx h_src
  by_cases h_sz : src.sizeBytes .bits64 = dst.sizeBytes .bits64
  · have h_enc := trusted_encodeValueToBytes_scalar 15 layouts m1 pt1 src srcLIdx bits h_src h_valid
    rw [h_sz] at h_src_sz
    have h_len : Trusted.Sequence.length (encodeLittleEndianBytes bits (src.sizeBytes .bits64) none) =
        dst.sizeBytes .bits64 := by
      rw [trusted_length_encodeLittleEndianBytes bits _ none, h_sz]
    have h_bits_dst : bits < scalarModulus (dst.sizeBytes .bits64) := h_sz ▸ h_valid.1
    rw [trusted_evalByteCast_of_encode locals locals' op mem localDecls layouts _ _ _ _ _
      h_op h_dst_sz h_ty h_src_sz h_enc h_len, h_sz, show defaultCodecFuel = 15 + 1 from rfl,
      trusted_decodeValueFromBytes_scalar 15 layouts m2 pt2 dst dstLIdx bits h_dst h_bits_dst,
      evalTransmuteSameSize_nonPtr_scalar_eq .bits64 policy src dst bits exposed h_src h_dst h_sz
        h_valid]
    cases dst.isValidBits .bits64 bits <;> rfl
  · rw [trusted_evalByteCast_size_mismatch locals locals' op mem localDecls layouts _ _ _ _ _
      h_op h_dst_sz h_ty h_src_sz h_sz,
      transmute_size_mismatch_unsupported .bits64 policy src dst (.scalar bits) exposed h_sz]
    rfl


/-- `Trusted.MirSemantics.evalByteCast` step-level correspondence between same-width signed and
unsigned integers (`iN <-> uN`, including `isize <-> usize`), in both directions: transmuting
`⟨bits, n⟩` returns the identical scalar `⟨bits, n⟩`, exactly as Anneal's
`transmute_int_to_int_roundtrip`, so composing the two steps is the identity. -/
theorem trusted_evalByteCast_int_uint_roundtrip
    (w : IntWidth)
    (bits : Nat)
    (locals₁ locals₁' locals₂ locals₂' : List LocalSlot)
    (op₁ op₂ : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (intLIdx uintLIdx : Nat)
    (h_bits : bits < scalarModulus (w.byteSize .bits64))
    (h_op₁ : evalOperand locals₁ op₁ mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar ⟨bits, w.byteSize .bits64⟩) locals₁')
    (h_ty₁ : operandTy localDecls layouts op₁ =
      .some { kind := .int w.toTrustedIntTy, layoutIdx := intLIdx })
    (h_op₂ : evalOperand locals₂ op₂ mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar ⟨bits, w.byteSize .bits64⟩) locals₂')
    (h_ty₂ : operandTy localDecls layouts op₂ =
      .some { kind := .uint w.toTrustedUintTy, layoutIdx := uintLIdx }) :
    evalByteCast locals₁ op₁ { kind := .uint w.toTrustedUintTy, layoutIdx := uintLIdx }
        mem localDecls layouts = ok (.scalar ⟨bits, w.byteSize .bits64⟩) locals₁' mem ∧
    evalByteCast locals₂ op₂ { kind := .int w.toTrustedIntTy, layoutIdx := intLIdx }
        mem localDecls layouts = ok (.scalar ⟨bits, w.byteSize .bits64⟩) locals₂' mem := by
  have h_rt := transmute_int_to_int_roundtrip .bits64 .rejectPtrToInt w bits [] h_bits
  refine ⟨?_, ?_⟩
  · rw [trusted_evalByteCast_scalar_transmute_correspondence .rejectPtrToInt (.int w) (.uint w)
      .not .not .bool .bool bits [] locals₁ locals₁' op₁ mem localDecls layouts intLIdx uintLIdx
      rfl rfl ⟨h_bits, trivial⟩ h_op₁ h_ty₁, h_rt.1]
    rfl
  · rw [trusted_evalByteCast_scalar_transmute_correspondence .rejectPtrToInt (.uint w) (.int w)
      .not .not .bool .bool bits [] locals₂ locals₂' op₂ mem localDecls layouts uintLIdx intLIdx
      rfl rfl ⟨h_bits, trivial⟩ h_op₂ h_ty₂, h_rt.2]
    rfl

/-- `Trusted` encoding of a thin pointer at the image of any pointer descriptor. -/
theorem trusted_encodeValueToBytes_thin_ptrTy
    (fuel : Nat) (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy) (ty : ScalarTy)
    (lIdx : Nat) (p : ProvenancePtr)
    (h_ptr : ty.isPtr = true) (h_thin : isThinPointee pointee = true) :
    encodeValueToBytes (fuel + 1) layouts { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx }
        (.ptr p 8) =
      some (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) := by
  cases ty with
  | rawPtr => exact trusted_encodeValueToBytes_thin_rawPtr fuel layouts m pointee lIdx p h_thin
  | refPtr => exact trusted_encodeValueToBytes_thin_ref fuel layouts m pointee lIdx p h_thin
  | bool => contradiction
  | char => contradiction
  | int w => contradiction
  | uint w => contradiction

/-- `Trusted` decoding of provenance-carrying thin-pointer bytes at the image of any pointer
descriptor. -/
theorem trusted_decodeValueFromBytes_thin_ptrTy
    (fuel : Nat) (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy) (ty : ScalarTy)
    (lIdx : Nat) (bs : List AbstractByte) (p : ProvenancePtr)
    (h_ptr : ty.isPtr = true) (h_thin : isThinPointee pointee = true)
    (h_len : Trusted.Sequence.length bs = 8)
    (h_dec : decodeScalarBytes bs false = .some (⟨p.offsetBytes, 8⟩, .some (p.allocId, p.tag))) :
    decodeValueFromBytes (fuel + 1) layouts { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx }
        bs = .some (.ptr p 8) := by
  cases ty with
  | rawPtr =>
    exact trusted_decodeValueFromBytes_thin_rawPtr fuel layouts m pointee lIdx bs p h_thin h_len h_dec
  | refPtr =>
    exact trusted_decodeValueFromBytes_thin_ref fuel layouts m pointee lIdx bs p h_thin h_len h_dec
  | bool => contradiction
  | char => contradiction
  | int w => contradiction
  | uint w => contradiction

/-- `Trusted` decoding of provenance-free 8-byte data `bits` at the image of any pointer
descriptor: it succeeds (with the page-model pointer `addressToPtr bits`) exactly when Anneal's
`ScalarTy.isValidBits .bits64 ty bits` holds (`refPtr` rejects the null address). -/
theorem trusted_decodeValueFromBytes_thin_ptrTy_no_prov
    (fuel : Nat) (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy) (ty : ScalarTy)
    (lIdx : Nat) (bs : List AbstractByte) (bits : Nat)
    (h_ptr : ty.isPtr = true) (h_thin : isThinPointee pointee = true)
    (h_bits : bits < scalarModulus 8)
    (h_len : Trusted.Sequence.length bs = 8)
    (h_dec : decodeScalarBytes bs false = .some (⟨bits, 8⟩, .none)) :
    decodeValueFromBytes (fuel + 1) layouts { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx }
        bs =
      match ty.isValidBits .bits64 bits with
      | true => .some (.ptr (addressToPtr bits) 8)
      | false => .none := by
  cases ty with
  | rawPtr =>
    have h_v : ScalarTy.rawPtr.isValidBits .bits64 bits = true :=
      (ScalarTy.isValidBits_iff_validBits .bits64 .rawPtr bits).mpr ⟨h_bits, trivial⟩
    rw [h_v]
    exact trusted_decodeValueFromBytes_thin_rawPtr_no_prov fuel layouts m pointee lIdx bs bits h_thin
      h_len h_dec
  | refPtr =>
    rw [trusted_decodeValueFromBytes_thin_ref_no_prov fuel layouts m pointee lIdx bs bits h_thin h_len
      h_dec]
    cases bits with
    | zero => rfl
    | succ k =>
      have h_v : ScalarTy.refPtr.isValidBits .bits64 (k + 1) = true :=
        (ScalarTy.isValidBits_iff_validBits .bits64 .refPtr (k + 1)).mpr ⟨h_bits, by omega⟩
      rw [h_v]
      rfl
  | bool => contradiction
  | char => contradiction
  | int w => contradiction
  | uint w => contradiction

/-- `Trusted` decoding at the image of an integral descriptor ignores byte provenance. -/
theorem trusted_decodeValueFromBytes_integral
    (fuel : Nat) (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy) (dst : ScalarTy)
    (lIdx : Nat) (bs : List AbstractByte) (sv : ScalarVal) (prov : Option (Nat × Nat))
    (h_int : dst.isIntegral = true)
    (h_len : Trusted.Sequence.length bs = dst.sizeBytes .bits64)
    (h_dec : ∀ signed : Bool, decodeScalarBytes bs signed = .some (sv, prov)) :
    decodeValueFromBytes (fuel + 1) layouts { kind := dst.toTrustedRigidTy m pointee, layoutIdx := lIdx }
        bs = .some (.scalar sv) := by
  cases dst with
  | int w =>
    exact trusted_decodeValueFromBytes_int_of_decodeScalarBytes fuel layouts w.toTrustedIntTy lIdx
      (w.byteSize .bits64) bs sv prov (IntWidth.intCastTargetBytes_int w) h_len (h_dec true)
  | uint w =>
    exact trusted_decodeValueFromBytes_uint_of_decodeScalarBytes fuel layouts w.toTrustedUintTy lIdx
      (w.byteSize .bits64) bs sv prov (IntWidth.intCastTargetBytes_uint w) h_len (h_dec false)
  | bool => contradiction
  | char => contradiction
  | rawPtr => contradiction
  | refPtr => contradiction

/-- **Thin-pointer transmute refinement theorem.** For every pair of pointer descriptors
`src, dst ∈ {rawPtr, refPtr}`, all thin pointees, every policy, and every provenance-carrying
pointer `p` valid for both types, Anneal's `evalTransmuteSameSize` preserves `p` and its
provenance and `Trusted.MirSemantics.evalByteCast` returns exactly the same pointer
(`ok (.ptr p 8)`, the `Trusted` image of Anneal's result). -/
theorem trusted_evalByteCast_thin_ptr_transmute_correspondence
    (policy : TransmutePolicy)
    (src dst : ScalarTy)
    (m1 m2 : Mutability)
    (pt1 pt2 : RigidTy)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (locals locals' : List LocalSlot)
    (op : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcLIdx dstLIdx : Nat)
    (h_src : src.isPtr = true)
    (h_dst : dst.isPtr = true)
    (h_thin1 : isThinPointee pt1 = true)
    (h_thin2 : isThinPointee pt2 = true)
    (h_src_valid : src.validBits .bits64 p.offsetBytes)
    (h_dst_valid : dst.validBits .bits64 p.offsetBytes)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.ptr p 8) locals')
    (h_ty : operandTy localDecls layouts op =
      .some { kind := src.toTrustedRigidTy m1 pt1, layoutIdx := srcLIdx }) :
    evalTransmuteSameSize .bits64 policy src dst (.ptr p (some p.allocId)) exposed =
      .ok (.ptr p (some p.allocId)) exposed ∧
    evalByteCast locals op { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx }
        mem localDecls layouts = ok (.ptr p 8) locals' mem ∧
    evalByteCast locals op { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx }
        mem localDecls layouts =
      CastOutcome.toTrustedResult .bits64 dst locals' mem
        (evalTransmuteSameSize .bits64 policy src dst (.ptr p (some p.allocId)) exposed) := by
  have h_dv : dst.isValidBits .bits64 p.offsetBytes = true :=
    (ScalarTy.isValidBits_iff_validBits .bits64 dst p.offsetBytes).mpr h_dst_valid
  have h_anneal : evalTransmuteSameSize .bits64 policy src dst (.ptr p (some p.allocId)) exposed =
      .ok (.ptr p (some p.allocId)) exposed := by
    rw [evalTransmuteSameSize_ptr_to_ptr_some .bits64 policy src dst p exposed h_src h_dst
      h_src_valid, h_dv]
  have h_off : p.offsetBytes < scalarModulus 8 := by
    have hb := h_src_valid.1
    rw [ScalarTy.sizeBytes_of_isPtr .bits64 src h_src] at hb
    exact hb
  have h_src_sz : rigidTyByteSize layouts { kind := src.toTrustedRigidTy m1 pt1, layoutIdx := srcLIdx } =
      some 8 := by
    rw [ScalarTy.rigidTyByteSize_toTrustedRigidTy layouts m1 pt1 src srcLIdx h_thin1,
      ScalarTy.sizeBytes_of_isPtr .bits64 src h_src]
  have h_dst_sz : rigidTyByteSize layouts { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx } =
      some 8 := by
    rw [ScalarTy.rigidTyByteSize_toTrustedRigidTy layouts m2 pt2 dst dstLIdx h_thin2,
      ScalarTy.sizeBytes_of_isPtr .bits64 dst h_dst]
  have h_len := trusted_length_encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))
  have h_dec_sc := trusted_decodeScalarBytes_encodeLittleEndianBytes 8 p.offsetBytes
    (some (p.allocId, p.tag)) false (by decide) h_off
  have h_trusted : evalByteCast locals op { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx }
      mem localDecls layouts = ok (.ptr p 8) locals' mem := by
    rw [trusted_evalByteCast_of_encode locals locals' op mem localDecls layouts (.ptr p 8) _ _ 8 _
        h_op h_dst_sz h_ty h_src_sz
        (trusted_encodeValueToBytes_thin_ptrTy 15 layouts m1 pt1 src srcLIdx p h_src h_thin1) h_len,
      show defaultCodecFuel = 15 + 1 from rfl,
      trusted_decodeValueFromBytes_thin_ptrTy 15 layouts m2 pt2 dst dstLIdx _ p h_dst h_thin2 h_len
        h_dec_sc]
  refine ⟨h_anneal, h_trusted, ?_⟩
  rw [h_trusted, h_anneal]
  rfl

/-- **`Int -> Ptr` transmute refinement theorem.** For every 8-byte integral source (`u64`,
`i64`, `usize`, `isize` on 64-bit targets), every pointer target (`rawPtr` / `refPtr`, any thin
pointee), and every policy, `Trusted.MirSemantics.evalByteCast` computes exactly the `Trusted`
image of Anneal's result: identical `.ub` on the null reference, and otherwise Anneal's
provenance-free pointer `.ptr ⟨0, bits⟩ none` maps to `Trusted`'s page-model pointer
`.ptr (addressToPtr bits) 8`. -/
theorem trusted_evalByteCast_int_to_thin_ptr_transmute_correspondence
    (policy : TransmutePolicy)
    (src dst : ScalarTy)
    (m1 m2 : Mutability)
    (pt1 pt2 : RigidTy)
    (bits : Nat)
    (exposed : ExposedProvenance)
    (locals locals' : List LocalSlot)
    (op : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcLIdx dstLIdx : Nat)
    (h_int : src.isIntegral = true)
    (h_sz : src.sizeBytes .bits64 = 8)
    (h_dst : dst.isPtr = true)
    (h_thin2 : isThinPointee pt2 = true)
    (h_bits : bits < scalarModulus 8)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar ⟨bits, src.sizeBytes .bits64⟩) locals')
    (h_ty : operandTy localDecls layouts op =
      .some { kind := src.toTrustedRigidTy m1 pt1, layoutIdx := srcLIdx }) :
    evalByteCast locals op { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx }
        mem localDecls layouts =
      CastOutcome.toTrustedResult .bits64 dst locals' mem
        (evalTransmuteSameSize .bits64 policy src dst (.scalar bits) exposed) := by
  have h_src_np := ScalarTy.isPtr_eq_false_of_isIntegral src h_int
  have h_valid : src.validBits .bits64 bits :=
    (ScalarTy.isValidBits_iff_validBits .bits64 src bits).mp
      (ScalarTy.isValidBits_of_isIntegral .bits64 src bits h_int (h_sz ▸ h_bits))
  have h_dst_sz8 := ScalarTy.sizeBytes_of_isPtr .bits64 dst h_dst
  have h_szeq : src.sizeBytes .bits64 = dst.sizeBytes .bits64 := by
    rw [h_sz, h_dst_sz8]
  have h_enc := trusted_encodeValueToBytes_scalar 15 layouts m1 pt1 src srcLIdx bits h_src_np h_valid
  have h_src_sz : rigidTyByteSize layouts { kind := src.toTrustedRigidTy m1 pt1, layoutIdx := srcLIdx } =
      some 8 := by
    rw [ScalarTy.rigidTyByteSize_toTrustedRigidTy_of_not_isPtr layouts m1 pt1 src srcLIdx h_src_np,
      h_sz]
  have h_dst_sz : rigidTyByteSize layouts { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx } =
      some 8 := by
    rw [ScalarTy.rigidTyByteSize_toTrustedRigidTy layouts m2 pt2 dst dstLIdx h_thin2, h_dst_sz8]
  have h_len : Trusted.Sequence.length (encodeLittleEndianBytes bits (src.sizeBytes .bits64) none) =
      8 := by
    rw [trusted_length_encodeLittleEndianBytes bits _ none, h_sz]
  have h_dec_sc := trusted_decodeScalarBytes_encodeLittleEndianBytes 8 bits none false
    (by decide) h_bits
  have h_len8 := trusted_length_encodeLittleEndianBytes bits 8 none
  rw [trusted_evalByteCast_of_encode locals locals' op mem localDecls layouts _ _ _ 8 _
      h_op h_dst_sz h_ty h_src_sz h_enc h_len, h_sz, show defaultCodecFuel = 15 + 1 from rfl,
    trusted_decodeValueFromBytes_thin_ptrTy_no_prov 15 layouts m2 pt2 dst dstLIdx _ bits h_dst h_thin2
      h_bits h_len8 h_dec_sc,
    evalTransmuteSameSize_int_to_ptr_eq .bits64 policy src dst bits exposed h_src_np h_dst h_szeq
      h_valid]
  cases dst.isValidBits .bits64 bits <;> rfl

/-- **`Ptr -> Int` transmute refinement theorem.** For every pointer source (`rawPtr` /
`refPtr`, any thin pointee) and every 8-byte integral target, Anneal's default policy rejects
the transmute (`.unsupported`), its opt-in `allowPtrToIntStripProvenance` policy returns the
address bits `p.offsetBytes` with provenance stripped, and `Trusted.MirSemantics.evalByteCast`
(which has no `Ptr -> Int` policy) computes exactly the `Trusted` image of the opt-in result. -/
theorem trusted_evalByteCast_thin_ptr_to_int_transmute_correspondence
    (src dst : ScalarTy)
    (m1 m2 : Mutability)
    (pt1 pt2 : RigidTy)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (locals locals' : List LocalSlot)
    (op : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcLIdx dstLIdx : Nat)
    (h_src : src.isPtr = true)
    (h_thin1 : isThinPointee pt1 = true)
    (h_int : dst.isIntegral = true)
    (h_sz : dst.sizeBytes .bits64 = 8)
    (h_src_valid : src.validBits .bits64 p.offsetBytes)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.ptr p 8) locals')
    (h_ty : operandTy localDecls layouts op =
      .some { kind := src.toTrustedRigidTy m1 pt1, layoutIdx := srcLIdx }) :
    evalTransmuteSameSize .bits64 .rejectPtrToInt src dst (.ptr p (some p.allocId)) exposed =
      .unsupported ∧
    evalTransmuteSameSize .bits64 .allowPtrToIntStripProvenance src dst
        (.ptr p (some p.allocId)) exposed = .ok (.scalar p.offsetBytes) exposed ∧
    evalByteCast locals op { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx }
        mem localDecls layouts = ok (.scalar ⟨p.offsetBytes, 8⟩) locals' mem ∧
    evalByteCast locals op { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx }
        mem localDecls layouts =
      CastOutcome.toTrustedResult .bits64 dst locals' mem
        (evalTransmuteSameSize .bits64 .allowPtrToIntStripProvenance src dst
          (.ptr p (some p.allocId)) exposed) := by
  have h_dst_np := ScalarTy.isPtr_eq_false_of_isIntegral dst h_int
  have h_src_sz8 := ScalarTy.sizeBytes_of_isPtr .bits64 src h_src
  have h_szeq : src.sizeBytes .bits64 = dst.sizeBytes .bits64 := by
    rw [h_src_sz8, h_sz]
  have h_off : p.offsetBytes < scalarModulus 8 := by
    have hb := h_src_valid.1
    rw [h_src_sz8] at hb
    exact hb
  have h_dv : dst.isValidBits .bits64 p.offsetBytes = true :=
    ScalarTy.isValidBits_of_isIntegral .bits64 dst p.offsetBytes h_int (h_sz ▸ h_off)
  have h_allow : evalTransmuteSameSize .bits64 .allowPtrToIntStripProvenance src dst
      (.ptr p (some p.allocId)) exposed = .ok (.scalar p.offsetBytes) exposed := by
    rw [evalTransmuteSameSize_ptr_to_nonPtr_allow_eq .bits64 src dst p (some p.allocId) exposed
      h_src h_dst_np h_szeq h_src_valid, h_dv]
  have h_src_sz : rigidTyByteSize layouts { kind := src.toTrustedRigidTy m1 pt1, layoutIdx := srcLIdx } =
      some 8 := by
    rw [ScalarTy.rigidTyByteSize_toTrustedRigidTy layouts m1 pt1 src srcLIdx h_thin1, h_src_sz8]
  have h_dst_sz : rigidTyByteSize layouts { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx } =
      some 8 := by
    rw [ScalarTy.rigidTyByteSize_toTrustedRigidTy_of_not_isPtr layouts m2 pt2 dst dstLIdx h_dst_np,
      h_sz]
  have h_len := trusted_length_encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))
  have h_len_dst : Trusted.Sequence.length
      (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) = dst.sizeBytes .bits64 := by
    rw [h_len, h_sz]
  have h_trusted : evalByteCast locals op { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx }
      mem localDecls layouts = ok (.scalar ⟨p.offsetBytes, 8⟩) locals' mem := by
    rw [trusted_evalByteCast_of_encode locals locals' op mem localDecls layouts (.ptr p 8) _ _ 8 _
        h_op h_dst_sz h_ty h_src_sz
        (trusted_encodeValueToBytes_thin_ptrTy 15 layouts m1 pt1 src srcLIdx p h_src h_thin1) h_len,
      show defaultCodecFuel = 15 + 1 from rfl,
      trusted_decodeValueFromBytes_integral 15 layouts m2 pt2 dst dstLIdx _ ⟨p.offsetBytes, 8⟩
        (some (p.allocId, p.tag)) h_int h_len_dst
        (fun signed => trusted_decodeScalarBytes_encodeLittleEndianBytes 8 p.offsetBytes
          (some (p.allocId, p.tag)) signed (by decide) h_off)]
  refine ⟨transmute_ptr_to_int_rejected_by_default_policy .bits64 src dst _ exposed h_src h_dst_np,
    h_allow, h_trusted, ?_⟩
  rw [h_trusted, h_allow]
  show ok (.scalar ⟨p.offsetBytes, 8⟩) locals' mem =
    ok (.scalar ⟨p.offsetBytes, dst.sizeBytes .bits64⟩) locals' mem
  rw [h_sz]

/-- **Divergence (null-offset provenance pointer as a reference).** `Trusted`'s
`decodeValueFromBytes` only null-checks *provenance-free* reference bytes (consistent with its
64 KiB page model, where `⟨allocId, 0⟩` has address `allocId * 65536`), so `evalByteCast`
accepts a provenance-carrying zero-offset raw pointer as a `&T`. Anneal's Episode 1 model,
where `offsetBytes` *is* the address (`PointerValue::addr`), rejects it as a null reference
(`.ub`). Anneal is therefore strictly more conservative here (a sound over-approximation of
`Trusted`'s undefined behavior). -/
theorem trusted_evalByteCast_null_offset_ref_divergence
    (policy : TransmutePolicy)
    (m1 m2 : Mutability)
    (pt1 pt2 : RigidTy)
    (allocId : Nat)
    (exposed : ExposedProvenance)
    (locals locals' : List LocalSlot)
    (op : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcLIdx dstLIdx : Nat)
    (h_thin1 : isThinPointee pt1 = true)
    (h_thin2 : isThinPointee pt2 = true)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.ptr { allocId := allocId, offsetBytes := 0 } 8) locals')
    (h_ty : operandTy localDecls layouts op =
      .some { kind := .rawPtr m1 pt1, layoutIdx := srcLIdx }) :
    evalTransmuteSameSize .bits64 policy .rawPtr .refPtr
        (.ptr { allocId := allocId, offsetBytes := 0 } (some allocId)) exposed = .ub ∧
    evalByteCast locals op { kind := .ref m2 pt2, layoutIdx := dstLIdx } mem localDecls layouts =
      ok (.ptr { allocId := allocId, offsetBytes := 0 } 8) locals' mem := by
  refine ⟨?_, ?_⟩
  · rw [evalTransmuteSameSize_ptr_to_ptr_some .bits64 policy .rawPtr .refPtr
      { allocId := allocId, offsetBytes := 0 } exposed rfl rfl
      ⟨show (0 : Nat) < scalarModulus 8 by decide, trivial⟩]
    rfl
  · exact trusted_evalByteCast_thin_rawPtr_to_ref_preserves_provenance locals locals' op mem
      localDecls layouts m1 m2 pt1 pt2 srcLIdx dstLIdx { allocId := allocId, offsetBytes := 0 }
      h_thin1 h_thin2 (show (0 : Nat) < scalarModulus 8 by decide) h_op h_ty

/-- **`Trusted` finding: transmute `Int -> *T` fabricates provenance.** On an 8-byte integral
operand, `Trusted`'s `Rvalue.cast .transmute` to a thin raw pointer coincides *exactly* with
`Rvalue.cast .pointerWithExposedProvenance` (`ptr::with_exposed_provenance`): both reconstruct
allocation `bits / 65536` from the integer (page model), and neither checks that this allocation
was ever exposed. Anneal's model instead yields a provenance-free pointer (`prov = none`), as
required by MiniRust / UCG `#286` (transmuting an integer to a pointer never creates provenance). -/
theorem trusted_transmute_int_to_rawPtr_eq_pointerWithExposedProvenance
    (policy : TransmutePolicy)
    (src : ScalarTy)
    (m1 m2 : Mutability)
    (pt1 pt2 : RigidTy)
    (bits : Nat)
    (exposed : ExposedProvenance)
    (locals locals' : List LocalSlot)
    (op : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcLIdx dstLIdx : Nat)
    (h_int : src.isIntegral = true)
    (h_sz : src.sizeBytes .bits64 = 8)
    (h_thin2 : isThinPointee pt2 = true)
    (h_bits : bits < scalarModulus 8)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar ⟨bits, src.sizeBytes .bits64⟩) locals')
    (h_ty : operandTy localDecls layouts op =
      .some { kind := src.toTrustedRigidTy m1 pt1, layoutIdx := srcLIdx }) :
    let dstTy : Ty := { kind := .rawPtr m2 pt2, layoutIdx := dstLIdx }
    evalRvalue locals (.cast .transmute op dstTy) mem localDecls layouts =
      ok (.ptr (addressToPtr bits) 8) locals' mem ∧
    evalRvalue locals (.cast .transmute op dstTy) mem localDecls layouts =
      evalRvalue locals (.cast .pointerWithExposedProvenance op dstTy) mem localDecls layouts ∧
    evalTransmuteSameSize .bits64 policy src .rawPtr (.scalar bits) exposed =
      .ok (.ptr { allocId := 0, offsetBytes := bits } none) exposed := by
  dsimp only
  have h_bc := trusted_evalByteCast_int_to_thin_ptr_transmute_correspondence policy src .rawPtr
    m1 m2 pt1 pt2 bits exposed locals locals' op mem localDecls layouts srcLIdx dstLIdx h_int h_sz rfl
    h_thin2 h_bits h_op h_ty
  have h_src_np := ScalarTy.isPtr_eq_false_of_isIntegral src h_int
  have h_valid : src.validBits .bits64 bits :=
    (ScalarTy.isValidBits_iff_validBits .bits64 src bits).mp
      (ScalarTy.isValidBits_of_isIntegral .bits64 src bits h_int (h_sz ▸ h_bits))
  have h_rv : ScalarTy.rawPtr.isValidBits .bits64 bits = true :=
    (ScalarTy.isValidBits_iff_validBits .bits64 .rawPtr bits).mpr ⟨h_bits, trivial⟩
  have h_anneal : evalTransmuteSameSize .bits64 policy src .rawPtr (.scalar bits) exposed =
      .ok (.ptr { allocId := 0, offsetBytes := bits } none) exposed := by
    rw [evalTransmuteSameSize_int_to_ptr_eq .bits64 policy src .rawPtr bits exposed h_src_np rfl
      h_sz h_valid, h_rv]
  rw [h_anneal] at h_bc
  have h_transmute : evalRvalue locals (.cast .transmute op { kind := .rawPtr m2 pt2, layoutIdx := dstLIdx })
      mem localDecls layouts = ok (.ptr (addressToPtr bits) 8) locals' mem := by
    unfold evalRvalue
    exact h_bc
  have h_expose : evalRvalue locals
      (.cast .pointerWithExposedProvenance op { kind := .rawPtr m2 pt2, layoutIdx := dstLIdx })
      mem localDecls layouts = ok (.ptr (addressToPtr bits) 8) locals' mem := by
    unfold evalRvalue
    exact int_to_ptr_cast_step_correspondence ⟨bits, src.sizeBytes .bits64⟩ locals locals' mem op
      layouts h_op
  exact ⟨h_transmute, h_transmute.trans h_expose.symm, h_anneal⟩


/-- **Address-model bridge for `PtrToInt`.** `Trusted`'s `Rvalue.cast .pointerExposeProvenance`
returns the 64 KiB page-model address `ptrToAddress p = p.allocId * 65536 + p.offsetBytes`
(`ptr_to_usize_cast_step_correspondence`), whereas Anneal's `evalPtrToIntExpose` follows
Episode 1 (`eval_ptr_to_int`: the integer is `PointerValue::addr`, i.e. `p.offsetBytes`, the same
bits that both `Trusted.encodeValueToBytes` and Anneal's `encodeCastVal` store for a pointer).
The two address models coincide exactly on allocation `0`. -/
theorem trusted_pointerExposeProvenance_address_model_bridge
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (locals locals' : List LocalSlot)
    (op : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : Ty)
    (h_off : p.offsetBytes < scalarModulus 8)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.ptr p 8) locals') :
    evalRvalue locals (.cast .pointerExposeProvenance op ty) mem localDecls layouts =
      ok (.scalar ⟨ptrToAddress p, 8⟩) locals' mem ∧
    evalPtrToIntExpose .bits64 .usize p exposed =
      .ok (.scalar p.offsetBytes) (exposeProv p.allocId exposed) ∧
    (ptrToAddress p = p.offsetBytes ↔ p.allocId = 0) := by
  refine ⟨?_, (ptrToInt_intToPtr_roundtrip .bits64 .usize p exposed rfl h_off h_off).1, ?_⟩
  · unfold evalRvalue
    exact ptr_to_usize_cast_step_correspondence p locals locals' mem op layouts h_op
  · show p.allocId * 65536 + p.offsetBytes = p.offsetBytes ↔ p.allocId = 0
    constructor
    · intro h
      have h0 : p.allocId * 65536 = 0 :=
        Nat.add_right_cancel (h.trans (Nat.zero_add p.offsetBytes).symm)
      exact (Nat.mul_eq_zero.mp h0).resolve_right (by decide)
    · intro h
      rw [h, Nat.zero_mul, Nat.zero_add]

/-- `Trusted.MirSemantics.mergeByteProvenance` always retains `some pv` on the left, regardless
of the right-hand provenance `restProv` (even when `restProv = none` or carries a different
allocation!). -/
@[simp]
theorem trusted_mergeByteProvenance_some_left
    (pv : Nat × Nat) (restProv : Option (Nat × Nat)) :
    mergeByteProvenance (some pv) restProv = some pv := by
  cases restProv <;> rfl

/-- **Divergence (partial pointer overwrite provenance retention in `Trusted` vs. MiniRust
fragment stripping in Anneal).** Because `Trusted.MirSemantics.mergeByteProvenance` retains the
first non-`none` byte provenance (`trusted_mergeByteProvenance_some_left`), overwriting byte `1`
(or any non-zero byte) of an 8-byte encoded pointer with a provenance-free byte `.init d none`
*still* decodes in `Trusted.MirSemantics.decodeValueFromBytes` at `{ kind := .rawPtr m pt, .. }`
to a pointer carrying `allocId = p.allocId`. By contrast, Anneal's `decodeCastVal` (mirroring
MiniRust `decode_ptr` and Episode 1's `decode_ptr_bytes`) checks all `pw.byteSize` provenance
fragments (`checkProvenanceFrags`) and strips provenance (`prov = none`, `allocId = 0`) whenever
any byte `i < pw.byteSize` is overwritten. -/
theorem trusted_vs_anneal_partial_overwrite_provenance_divergence
    (fuel : Nat)
    (layouts : LayoutTable)
    (m : Mutability)
    (pt : RigidTy)
    (lIdx : Nat)
    (p : ProvenancePtr)
    (d : UInt8)
    (h_thin : isThinPointee pt = true) :
    let trustedOverwritten :=
      (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))).set 1 (.init d none)
    let annealOverwritten :=
      (encodeCastBytes p.offsetBytes 8 (some p.allocId)).set 1 { data := d, prov := none }
    (∃ newOffset,
      decodeValueFromBytes (fuel + 1) layouts { kind := .rawPtr m pt, layoutIdx := lIdx }
          trustedOverwritten =
        .some (.ptr { allocId := p.allocId, offsetBytes := newOffset } 8)) ∧
    decodeCastVal .bits64 .rawPtr annealOverwritten =
      some (.ptr { allocId := 0, offsetBytes := decodeCastIntBytes annealOverwritten } none) := by
  intro trustedOverwritten annealOverwritten
  refine ⟨?_, decodeCastVal_rawPtr_partial_overwrite_strips_provenance .bits64 p 1 d (by decide)⟩
  have h_len_tail :
      Trusted.Sequence.length (encodeLittleEndianBytes ((p.offsetBytes / 256) / 256) 6
        (some (p.allocId, p.tag))) = 6 :=
    trusted_length_encodeLittleEndianBytes _ 6 _
  have h_bound_tail : (p.offsetBytes / 256) / 256 % scalarModulus 6 < scalarModulus 6 :=
    Nat.mod_lt _ (scalarModulus_pos 6)
  have h_dec_tail :
      ∃ highBits restProv,
        decodeLittleEndianBytes (encodeLittleEndianBytes ((p.offsetBytes / 256) / 256) 6
          (some (p.allocId, p.tag))) = .some (highBits, restProv) := by
    generalize (p.offsetBytes / 256) / 256 = x
    refine ⟨(x % 256) + 256 * ((x / 256 % 256) + 256 * ((x / 256 / 256 % 256) +
      256 * ((x / 256 / 256 / 256 % 256) + 256 * ((x / 256 / 256 / 256 / 256 % 256) +
        256 * ((x / 256 / 256 / 256 / 256 / 256 % 256) + 256 * 0))))),
      some (p.allocId, p.tag), ?_⟩
    rfl
  rcases h_dec_tail with ⟨highBits, restProv, h_tail⟩
  let b0 := UInt8.ofNat p.offsetBytes
  let newOffset := b0.toBitVec.toNat + 256 * (d.toBitVec.toNat + 256 * highBits)
  refine ⟨newOffset, ?_⟩
  have h_over_eq :
      trustedOverwritten =
        .init b0 (some (p.allocId, p.tag)) ::
        .init d none ::
        encodeLittleEndianBytes ((p.offsetBytes / 256) / 256) 6 (some (p.allocId, p.tag)) := rfl
  have h_len8 : Trusted.Sequence.length trustedOverwritten = 8 := by
    rw [h_over_eq]
    change Nat.succ (Nat.succ (Trusted.Sequence.length _)) = 8
    rw [h_len_tail]
  have h_dle :
      decodeLittleEndianBytes trustedOverwritten =
        .some (newOffset, some (p.allocId, p.tag)) := by
    rw [h_over_eq, trusted_decodeLittleEndianBytes_init_cons,
      trusted_decodeLittleEndianBytes_init_cons, h_tail]
    dsimp only
    rw [trusted_mergeByteProvenance_some_left]
    rfl
  have h_dsc :
      decodeScalarBytes trustedOverwritten false =
        .some (⟨newOffset, 8⟩, some (p.allocId, p.tag)) := by
    unfold decodeScalarBytes
    rw [h_len8, h_dle]
  have h_beq8 : Nat.beq (Trusted.Sequence.length trustedOverwritten) 8 = true := by
    rw [h_len8]
    rfl
  rw [trusted_decodeValueFromBytes_thin_rawPtr_eq fuel layouts m pt lIdx trustedOverwritten h_thin,
    h_beq8]
  dsimp only
  rw [h_dsc]

/-- Step-level correspondence in `Trusted.MirSemantics` between `Rvalue.cast .transmute` and
`Rvalue.cast .ptrToPtr` on any thin pointer source (`rawPtr` or `refPtr`) and thin raw-pointer
target (`*const U` / `*mut U`) when `lookupBorrow mem.borrows p.tag = none`: both evaluate to
`ok (.ptr p 8) locals' mem`. -/
theorem trusted_transmute_thin_rawPtr_eq_ptrToPtr_cast
    (src : ScalarTy)
    (m1 m2 : Mutability)
    (pt1 pt2 : RigidTy)
    (p : ProvenancePtr)
    (locals locals' : List LocalSlot)
    (op : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcLIdx dstLIdx : Nat)
    (h_src : src.isPtr = true)
    (h_thin1 : isThinPointee pt1 = true)
    (h_thin2 : isThinPointee pt2 = true)
    (h_src_valid : src.validBits .bits64 p.offsetBytes)
    (h_lookup : lookupBorrow mem.borrows p.tag = none)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.ptr p 8) locals')
    (h_ty : operandTy localDecls layouts op =
      .some { kind := src.toTrustedRigidTy m1 pt1, layoutIdx := srcLIdx }) :
    let dstTy : Ty := { kind := .rawPtr m2 pt2, layoutIdx := dstLIdx }
    evalRvalue locals (.cast .transmute op dstTy) mem localDecls layouts =
      ok (.ptr p 8) locals' mem ∧
    evalRvalue locals (.cast .ptrToPtr op dstTy) mem localDecls layouts =
      ok (.ptr p 8) locals' mem ∧
    evalRvalue locals (.cast .transmute op dstTy) mem localDecls layouts =
      evalRvalue locals (.cast .ptrToPtr op dstTy) mem localDecls layouts := by
  dsimp only
  have h_off : p.offsetBytes < scalarModulus 8 := by
    have hb := h_src_valid.1
    rw [ScalarTy.sizeBytes_of_isPtr .bits64 src h_src] at hb
    exact hb
  have h_bc := (trusted_evalByteCast_thin_ptr_transmute_correspondence .rejectPtrToInt src .rawPtr
    m1 m2 pt1 pt2 p [] locals locals' op mem localDecls layouts srcLIdx dstLIdx h_src rfl h_thin1
    h_thin2 h_src_valid ⟨h_off, trivial⟩ h_op h_ty).2.1
  have h_transmute :
      evalRvalue locals (.cast .transmute op { kind := .rawPtr m2 pt2, layoutIdx := dstLIdx })
        mem localDecls layouts = ok (.ptr p 8) locals' mem := h_bc
  have h_ptrToPtr :
      evalRvalue locals (.cast .ptrToPtr op { kind := .rawPtr m2 pt2, layoutIdx := dstLIdx })
        mem localDecls layouts = ok (.ptr p 8) locals' mem := by
    dsimp only [evalRvalue]
    rw [h_op]
    dsimp only
    rw [h_lookup]
    cases pt2 <;> try (simp [isThinPointee] at h_thin2)
    all_goals
      dsimp only
      split <;> first | contradiction | rfl
  exact ⟨h_transmute, h_ptrToPtr, h_transmute.trans h_ptrToPtr.symm⟩

/-- In `Trusted.MirSemantics`, `Rvalue.cast .transmute` and `Rvalue.cast .subtype` share the
exact same `evalByteCast` evaluator and are definitionally equal for all arguments. -/
theorem trusted_transmute_eq_subtype_cast
    (locals : List LocalSlot)
    (op : Operand)
    (dstTy : Ty)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    evalRvalue locals (.cast .transmute op dstTy) mem localDecls layouts =
      evalRvalue locals (.cast .subtype op dstTy) mem localDecls layouts := rfl


/-- **Size-mismatch refinement theorem.** For every pair of scalar descriptors (pointers with
thin pointees included) whose 64-bit sizes differ — e.g. `bool`/`char`/`u32` vs. any thin
pointer, or `u8` vs. `u16` — both Anneal's `evalTransmuteSameSize` and
`Trusted.MirSemantics.evalByteCast` reject the transmute with `.unsupported`, for *every*
operand value and policy. Together with the scalar, thin-pointer, `Int -> Ptr`, and `Ptr -> Int`
refinement theorems this covers every descriptor pair, leaving only provenance-free pointer
*sources* (which `Trusted.Value` cannot represent) and the documented divergences. -/
theorem trusted_evalByteCast_size_mismatch_transmute_correspondence
    (policy : TransmutePolicy)
    (src dst : ScalarTy)
    (m1 m2 : Mutability)
    (pt1 pt2 : RigidTy)
    (val : CastVal)
    (v : Value)
    (exposed : ExposedProvenance)
    (locals locals' : List LocalSlot)
    (op : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcLIdx dstLIdx : Nat)
    (h_thin1 : isThinPointee pt1 = true)
    (h_thin2 : isThinPointee pt2 = true)
    (h_ne : src.sizeBytes .bits64 ≠ dst.sizeBytes .bits64)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok v locals')
    (h_ty : operandTy localDecls layouts op =
      .some { kind := src.toTrustedRigidTy m1 pt1, layoutIdx := srcLIdx }) :
    evalByteCast locals op { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx }
        mem localDecls layouts = .unsupported ∧
    evalTransmuteSameSize .bits64 policy src dst val exposed = .unsupported ∧
    evalByteCast locals op { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx }
        mem localDecls layouts =
      CastOutcome.toTrustedResult .bits64 dst locals' mem
        (evalTransmuteSameSize .bits64 policy src dst val exposed) := by
  have h_trusted := trusted_evalByteCast_size_mismatch locals locals' op mem localDecls layouts v
    _ _ _ _ h_op (ScalarTy.rigidTyByteSize_toTrustedRigidTy layouts m2 pt2 dst dstLIdx h_thin2) h_ty
    (ScalarTy.rigidTyByteSize_toTrustedRigidTy layouts m1 pt1 src srcLIdx h_thin1) h_ne
  have h_anneal := transmute_size_mismatch_unsupported .bits64 policy src dst val exposed h_ne
  refine ⟨h_trusted, h_anneal, ?_⟩
  rw [h_trusted, h_anneal]
  rfl

/-- **Divergence (provenance forging by a foreign first byte).** `Trusted`'s byte-provenance
merge (`mergeByteProvenance`) keeps the provenance of the *first* byte that carries one, so
overwriting byte `0` of a stored pointer to `p.allocId` with a byte carrying another pointer's
provenance `(q.allocId, q.tag)` makes `Trusted.decodeValueFromBytes` produce a pointer **into
`q.allocId`** whose address is built mostly from `p`'s bytes. Anneal's MiniRust-faithful
`decodeCastVal` (`decodeCastPtrProv_eq_some_iff`) instead strips provenance entirely. -/
theorem trusted_vs_anneal_foreign_first_byte_provenance_forging
    (fuel : Nat)
    (layouts : LayoutTable)
    (m : Mutability)
    (pt : RigidTy)
    (lIdx : Nat)
    (p q : ProvenancePtr)
    (d : UInt8)
    (h_thin : isThinPointee pt = true)
    (h_off : p.offsetBytes < scalarModulus 8)
    (h_ne : q.allocId ≠ p.allocId) :
    let trustedForged :=
      (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))).set 0
        (.init d (some (q.allocId, q.tag)))
    let annealForged :=
      (encodeCastBytes p.offsetBytes 8 (some p.allocId)).set 0
        { data := d, prov := some { allocId := q.allocId, position := 0 } }
    decodeValueFromBytes (fuel + 1) layouts { kind := .rawPtr m pt, layoutIdx := lIdx }
        trustedForged =
      .some (.ptr { allocId := q.allocId,
                    offsetBytes := d.toBitVec.toNat + 256 * (p.offsetBytes / 256) } 8) ∧
    decodeCastVal .bits64 .rawPtr annealForged =
      some (.ptr { allocId := 0, offsetBytes := decodeCastIntBytes annealForged } none) := by
  intro trustedForged annealForged
  refine ⟨?_, decodeCastVal_rawPtr_foreign_overwrite_strips_provenance .bits64 p q.allocId 0 0 d
    (by decide) h_ne⟩
  have h_eq : trustedForged =
      .init d (some (q.allocId, q.tag)) ::
        encodeLittleEndianBytes (Nat.div p.offsetBytes 256) 7 (some (p.allocId, p.tag)) := rfl
  have h_tail_bound : Nat.div p.offsetBytes 256 < scalarModulus (6 + 1) := by
    change p.offsetBytes < 256 * scalarModulus 7 at h_off
    show p.offsetBytes / 256 < scalarModulus 7
    omega
  have h_tail := trusted_decodeLittleEndianBytes_encodeLittleEndianBytes 6 (Nat.div p.offsetBytes 256)
    (some (p.allocId, p.tag)) h_tail_bound
  have h_len : Trusted.Sequence.length trustedForged = 8 := by
    rw [h_eq]
    change Nat.succ (Trusted.Sequence.length
      (encodeLittleEndianBytes (Nat.div p.offsetBytes 256) 7 (some (p.allocId, p.tag)))) = 8
    rw [trusted_length_encodeLittleEndianBytes]
  have h_dle : decodeLittleEndianBytes trustedForged =
      .some (d.toBitVec.toNat + 256 * (p.offsetBytes / 256), some (q.allocId, q.tag)) := by
    rw [h_eq, trusted_decodeLittleEndianBytes_init_cons, h_tail]
    rfl
  have h_dsc : decodeScalarBytes trustedForged false =
      .some (⟨d.toBitVec.toNat + 256 * (p.offsetBytes / 256), 8⟩, some (q.allocId, q.tag)) := by
    unfold decodeScalarBytes
    rw [h_len, h_dle]
  have h_beq8 : Nat.beq (Trusted.Sequence.length trustedForged) 8 = true := by
    rw [h_len]
    rfl
  rw [trusted_decodeValueFromBytes_thin_rawPtr_eq fuel layouts m pt lIdx trustedForged h_thin, h_beq8]
  dsimp only
  rw [h_dsc]

/-- `Trusted.MirSemantics.mergeByteProvenance` falls back to its right argument when the left byte
carries no provenance (`none`). -/
@[simp] theorem trusted_mergeByteProvenance_none_left (p : Option (Nat × Nat)) :
    mergeByteProvenance none p = p := by
  cases p <;> rfl

/-- **Divergence (provenance retention under head-byte provenance-free overwrite).** Even when
byte `0` of an 8-byte encoded pointer is overwritten with a provenance-free integer byte
(`.init d none`), `Trusted.MirSemantics.mergeByteProvenance none p₂ = p₂` inherits `(p.allocId, p.tag)`
from bytes `1..7` and `Trusted.decodeValueFromBytes` still reconstructs a pointer into `p.allocId`.
Anneal's MiniRust-faithful `decodeCastVal` (`decodeCastVal_rawPtr_partial_overwrite_strips_provenance`)
instead strips provenance because byte `0` has `prov = none`. -/
theorem trusted_vs_anneal_head_none_overwrite_provenance_divergence
    (fuel : Nat)
    (layouts : LayoutTable)
    (m : Mutability)
    (pt : RigidTy)
    (lIdx : Nat)
    (p : ProvenancePtr)
    (d : UInt8)
    (h_thin : isThinPointee pt = true)
    (h_off : p.offsetBytes < scalarModulus 8) :
    let trustedCorrupted :=
      (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))).set 0 (.init d none)
    let annealCorrupted :=
      (encodeCastBytes p.offsetBytes 8 (some p.allocId)).set 0 { data := d, prov := none }
    decodeValueFromBytes (fuel + 1) layouts { kind := .rawPtr m pt, layoutIdx := lIdx }
        trustedCorrupted =
      .some (.ptr { allocId := p.allocId,
                    offsetBytes := d.toBitVec.toNat + 256 * (p.offsetBytes / 256) } 8) ∧
    decodeCastVal .bits64 .rawPtr annealCorrupted =
      some (.ptr { allocId := 0, offsetBytes := decodeCastIntBytes annealCorrupted } none) := by
  intro trustedCorrupted annealCorrupted
  refine ⟨?_, decodeCastVal_rawPtr_partial_overwrite_strips_provenance .bits64 p 0 d (by decide)⟩
  have h_eq : trustedCorrupted =
      .init d none ::
        encodeLittleEndianBytes (Nat.div p.offsetBytes 256) 7 (some (p.allocId, p.tag)) := rfl
  have h_tail_bound : Nat.div p.offsetBytes 256 < scalarModulus (6 + 1) := by
    change p.offsetBytes < 256 * scalarModulus 7 at h_off
    show p.offsetBytes / 256 < scalarModulus 7
    omega
  have h_tail := trusted_decodeLittleEndianBytes_encodeLittleEndianBytes 6 (Nat.div p.offsetBytes 256)
    (some (p.allocId, p.tag)) h_tail_bound
  have h_len : Trusted.Sequence.length trustedCorrupted = 8 := by
    rw [h_eq]
    change Nat.succ (Trusted.Sequence.length
      (encodeLittleEndianBytes (Nat.div p.offsetBytes 256) 7 (some (p.allocId, p.tag)))) = 8
    rw [trusted_length_encodeLittleEndianBytes]
  have h_dle : decodeLittleEndianBytes trustedCorrupted =
      .some (d.toBitVec.toNat + 256 * (p.offsetBytes / 256), some (p.allocId, p.tag)) := by
    rw [h_eq, trusted_decodeLittleEndianBytes_init_cons, h_tail]
    rfl
  have h_dsc : decodeScalarBytes trustedCorrupted false =
      .some (⟨d.toBitVec.toNat + 256 * (p.offsetBytes / 256), 8⟩, some (p.allocId, p.tag)) := by
    unfold decodeScalarBytes
    rw [h_len, h_dle]
  have h_beq8 : Nat.beq (Trusted.Sequence.length trustedCorrupted) 8 = true := by
    rw [h_len]
    rfl
  rw [trusted_decodeValueFromBytes_thin_rawPtr_eq fuel layouts m pt lIdx trustedCorrupted h_thin, h_beq8]
  dsimp only
  rw [h_dsc]

/-!
## 8. `Anneal.BitValidity` & `zerocopy` Trait Bridge (`ScalarLayout.validRange`, `ProvenanceFrag`, `evalTransmuteSameSize`, and `evalByteCast`)
-/

namespace ScalarTy

/-- `Trusted` `PrimitiveKind` corresponding to `ty : ScalarTy` under target pointer width `pw`. -/
@[reducible]
def toPrimitiveKind (pw : PtrWidth) : ScalarTy → PrimitiveKind
  | .bool => .int 8 false
  | .char => .int 32 false
  | .int w => .int (w.byteSize pw * 8) true
  | .uint w => .int (w.byteSize pw * 8) false
  | .rawPtr => .pointer 0
  | .refPtr => .pointer 0

/-- `rustc` `WrappingRange` (`Scalar::Initialized::valid_range`) for `ty : ScalarTy` under `pw`. -/
@[reducible]
def toValidRange (pw : PtrWidth) : ScalarTy → WrappingRange
  | .bool => ⟨0, 1⟩
  | .char => ⟨0, 1114111⟩
  | .int w => ⟨0, scalarModulus (w.byteSize pw) - 1⟩
  | .uint w => ⟨0, scalarModulus (w.byteSize pw) - 1⟩
  | .rawPtr => ⟨0, pw.modulus - 1⟩
  | .refPtr => ⟨1, pw.modulus - 1⟩

/-- `Trusted` `ScalarLayout` descriptor (`Scalar::Initialized`) for `ty : ScalarTy` under `pw`. -/
@[reducible]
def toScalarLayout (pw : PtrWidth) (ty : ScalarTy) : ScalarLayout :=
  .initialized (ty.toPrimitiveKind pw) (ty.toValidRange pw)

/-- On 64-bit targets, `scalarLayoutByteWidth (ty.toScalarLayout .bits64)` agrees with `ty.sizeBytes .bits64`. -/
@[simp]
theorem scalarLayoutByteWidth_toScalarLayout_bits64 (ty : ScalarTy) :
    scalarLayoutByteWidth (ty.toScalarLayout .bits64) = some (ty.sizeBytes .bits64) := by
  cases ty with
  | bool | char | rawPtr | refPtr => rfl
  | int w | uint w => cases w <;> rfl

end ScalarTy

/--
**Scalar validity equivalence (`ScalarTy.isValidBits` ↔ `ScalarLayout.validRange`).**
Across all six `ScalarTy` constructors (`.bool`, `.char`, `.int`, `.uint`, `.rawPtr`, `.refPtr`),
`ty.isValidBits pw bits = true` holds if and only if `bits` lies in `rustc`'s layout range
`wrappingRangeContains (ty.toValidRange pw) bits = true` and (when `ty = .char`) `bits` is outside
the UTF-16 surrogate gap `0xD800..=0xDFFF` (`55296..=57343`).
-/
theorem scalarTy_isValidBits_iff_scalarLayout_validRange
    (pw : PtrWidth) (ty : ScalarTy) (bits : Nat) :
    ty.isValidBits pw bits = true ↔
      (wrappingRangeContains (ty.toValidRange pw) bits = true ∧
       (ty = .char → ¬ (55296 ≤ bits ∧ bits ≤ 57343))) := by
  rw [ScalarTy.isValidBits_iff_validBits]
  cases ty with
  | bool =>
    rw [ScalarTy.validBits_bool_iff_wrappingRangeContains pw bits]
    simp [ScalarTy.toValidRange]
  | char =>
    rw [(ScalarTy.validBits_char_iff_wrappingRangeContains pw bits).1]
    simp [ScalarTy.toValidRange]
  | int w =>
    rw [ScalarTy.validBits_full_iff_wrappingRangeContains pw (.int w) (Or.inr rfl) bits]
    simp [ScalarTy.toValidRange, ScalarTy.sizeBytes]
  | uint w =>
    rw [ScalarTy.validBits_full_iff_wrappingRangeContains pw (.uint w) (Or.inr rfl) bits]
    simp [ScalarTy.toValidRange, ScalarTy.sizeBytes]
  | rawPtr =>
    rw [ScalarTy.validBits_full_iff_wrappingRangeContains pw .rawPtr (Or.inl rfl) bits]
    simp [ScalarTy.toValidRange, ScalarTy.sizeBytes, PtrWidth.modulus]
  | refPtr =>
    rw [ScalarTy.validBits_refPtr_iff_wrappingRangeContains pw bits]
    simp [ScalarTy.toValidRange]

/-- Alias of `scalarTy_isValidBits_iff_scalarLayout_validRange`. -/
theorem scalarTy_isValidBits_iff_validRange
    (pw : PtrWidth) (ty : ScalarTy) (bits : Nat) :
    ty.isValidBits pw bits = true ↔
      (wrappingRangeContains (ty.toValidRange pw) bits = true ∧
       (ty = .char → ¬ (55296 ≤ bits ∧ bits ≤ 57343))) :=
  scalarTy_isValidBits_iff_scalarLayout_validRange pw ty bits

/-- For every `ty ≠ .char`, `ty.isValidBits pw bits` coincides identically with `wrappingRangeContains (ty.toValidRange pw) bits`. -/
theorem scalarTy_isValidBits_iff_validRange_of_ne_char
    (pw : PtrWidth) (ty : ScalarTy) (bits : Nat) (h_ne : ty ≠ .char) :
    ty.isValidBits pw bits = true ↔
      wrappingRangeContains (ty.toValidRange pw) bits = true := by
  rw [scalarTy_isValidBits_iff_scalarLayout_validRange pw ty bits]
  exact ⟨fun h => h.1, fun h => ⟨h, fun h_eq => False.elim (h_ne h_eq)⟩⟩

/--
Direct agreement between `ScalarTy.isValidBits .bits64`, `decodeScalarLayoutBytes (ty.toScalarLayout .bits64)`,
and `decodeValueFromBytes` for every non-`char` non-pointer scalar descriptor on 64-bit targets.
-/
theorem decodeScalarLayoutBytes_toScalarLayout_bits64_of_ne_char
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy) (ty : ScalarTy)
    (lIdx bits : Nat)
    (h_np : ty.isPtr = false)
    (h_ne : ty ≠ .char)
    (h_bits : bits < scalarModulus (ty.sizeBytes .bits64)) :
    decodeScalarLayoutBytes (ty.toScalarLayout .bits64)
        (encodeLittleEndianBytes bits (ty.sizeBytes .bits64) none) =
      (match ty.isValidBits .bits64 bits with
       | true => some (.scalar ⟨bits, ty.sizeBytes .bits64⟩)
       | false => none) ∧
    decodeScalarLayoutBytes (ty.toScalarLayout .bits64)
        (encodeLittleEndianBytes bits (ty.sizeBytes .bits64) none) =
      decodeValueFromBytes defaultCodecFuel layouts
        { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx }
        (encodeLittleEndianBytes bits (ty.sizeBytes .bits64) none) := by
  have h_len :
      Trusted.Sequence.length (encodeLittleEndianBytes bits (ty.sizeBytes .bits64) none) =
        ty.sizeBytes .bits64 :=
    trusted_length_encodeLittleEndianBytes bits _ none
  have h_beq :
      Nat.beq (Trusted.Sequence.length (encodeLittleEndianBytes bits (ty.sizeBytes .bits64) none))
        (ty.sizeBytes .bits64) = true := by
    rw [h_len]; exact Nat.beq_refl _
  have h_dec :
      decodeScalarBytes (encodeLittleEndianBytes bits (ty.sizeBytes .bits64) none) false =
        some (⟨bits, ty.sizeBytes .bits64⟩, none) :=
    trusted_decodeScalarBytes_encodeLittleEndianBytes _ bits none false
      (ScalarTy.sizeBytes_pos .bits64 ty) h_bits
  have h_sl :
      decodeScalarLayoutBytes (ty.toScalarLayout .bits64)
          (encodeLittleEndianBytes bits (ty.sizeBytes .bits64) none) =
        match ty.isValidBits .bits64 bits with
        | true => some (.scalar ⟨bits, ty.sizeBytes .bits64⟩)
        | false => none := by
    unfold decodeScalarLayoutBytes
    rw [ScalarTy.scalarLayoutByteWidth_toScalarLayout_bits64 ty]
    dsimp only [ScalarTy.toScalarLayout]
    rw [h_beq]
    dsimp only
    rw [h_dec]
    dsimp only
    have h_iff := scalarTy_isValidBits_iff_validRange_of_ne_char .bits64 ty bits h_ne
    cases h_w : wrappingRangeContains (ty.toValidRange .bits64) bits
    · have h_f : ty.isValidBits .bits64 bits = false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        rw [h_iff.mp ht] at h_w
        nomatch h_w
      rw [h_f]
    · have h_t : ty.isValidBits .bits64 bits = true := h_iff.mpr h_w
      rw [h_t]
      cases ty <;> first | contradiction | rfl
  refine ⟨h_sl, ?_⟩
  rw [h_sl, show defaultCodecFuel = 15 + 1 from rfl,
      trusted_decodeValueFromBytes_scalar 15 layouts m pointee ty lIdx bits h_np h_bits]

/-- On 64-bit targets every scalar descriptor has a non-zero byte width. -/
theorem ScalarTy.sizeBytes_bits64_beq_zero (ty : ScalarTy) :
    Nat.beq (ty.sizeBytes .bits64) 0 = false := by
  cases ty with
  | bool | char | rawPtr | refPtr => rfl
  | int w | uint w => cases w <;> rfl

/--
`rustc`-layout decoding agreement for **every** scalar descriptor on 64-bit
targets: the `Trusted` scalar-layout decoder at `ty.toScalarLayout .bits64`
accepts the encoding of an in-range bit pattern (carrying any byte provenance
`prov`) exactly when the bit pattern lies in `ty.toValidRange .bits64`.
-/
theorem decodeScalarLayoutBytes_toScalarLayout_bits64_some_iff
    (ty : ScalarTy) (bits : Nat) (prov : Option (Nat × Nat))
    (h_bits : bits < scalarModulus (ty.sizeBytes .bits64)) :
    (∃ v, decodeScalarLayoutBytes (ty.toScalarLayout .bits64)
        (encodeLittleEndianBytes bits (ty.sizeBytes .bits64) prov) = some v) ↔
      wrappingRangeContains (ty.toValidRange .bits64) bits = true :=
  decodeScalarLayoutBytes_initialized_encode_some_iff (ty.toPrimitiveKind .bits64)
    (ty.toValidRange .bits64) (ty.sizeBytes .bits64) bits prov
    (ScalarTy.scalarLayoutByteWidth_toScalarLayout_bits64 ty)
    (ScalarTy.sizeBytes_bits64_beq_zero ty) h_bits

/--
For every non-`char` descriptor (`bool`, `int`, `uint`, `rawPtr`, and `refPtr`),
the scalar-layout decoder on 64-bit targets accepts exactly the bit patterns
accepted by `ScalarTy.isValidBits`, whatever byte provenance the encoding
carries. In particular the `refPtr` layout `⟨1, 2^64 - 1⟩` rejects the null
address even on provenance-carrying bytes, in agreement with Anneal's address
model; `Trusted.decodeValueFromBytes` at `RigidTy.ref` instead accepts a
provenance-carrying zero offset (`trusted_evalByteCast_null_offset_ref_divergence`).
-/
theorem decodeScalarLayoutBytes_toScalarLayout_bits64_some_iff_isValidBits
    (ty : ScalarTy) (bits : Nat) (prov : Option (Nat × Nat))
    (h_ne : ty ≠ .char)
    (h_bits : bits < scalarModulus (ty.sizeBytes .bits64)) :
    (∃ v, decodeScalarLayoutBytes (ty.toScalarLayout .bits64)
        (encodeLittleEndianBytes bits (ty.sizeBytes .bits64) prov) = some v) ↔
      ty.isValidBits .bits64 bits = true := by
  rw [decodeScalarLayoutBytes_toScalarLayout_bits64_some_iff ty bits prov h_bits,
    scalarTy_isValidBits_iff_validRange_of_ne_char .bits64 ty bits h_ne]

/--
Exact value-level characterization of `decodeScalarLayoutBytes (ty.toScalarLayout .bits64)`
for pointer scalar descriptors (`ty.isPtr = true`, i.e., `rawPtr` and `refPtr`) on any
8-byte encoding `encodeLittleEndianBytes bits 8 prov`:
- `rawPtr` always decodes to `some (.ptr ... 8)` (`{ allocId, offsetBytes := bits }` when
  `prov = some (allocId, _)`, or `addressToPtr bits` when `prov = none`).
- `refPtr` decodes to `some (.ptr ... 8)` iff `0 < bits` (`ty.isValidBits .bits64 bits = true`),
  and returns `none` when `bits = 0`.
-/
theorem decodeScalarLayoutBytes_toScalarLayout_bits64_ptr_eq
    (ty : ScalarTy) (bits : Nat) (prov : Option (Nat × Nat))
    (h_ptr : ty.isPtr = true)
    (h_bits : bits < scalarModulus (ty.sizeBytes .bits64)) :
    decodeScalarLayoutBytes (ty.toScalarLayout .bits64)
        (encodeLittleEndianBytes bits (ty.sizeBytes .bits64) prov) =
      match ty.isValidBits .bits64 bits with
      | true =>
        some (.ptr
          (match prov with
           | some (allocId, _) => { allocId := allocId, offsetBytes := bits }
           | none => addressToPtr bits)
          8)
      | false => none := by
  have hSz8 : ty.sizeBytes .bits64 = 8 := ScalarTy.sizeBytes_of_isPtr .bits64 ty h_ptr
  have hBits8 : bits < scalarModulus 8 := hSz8 ▸ h_bits
  have hLen :
      Trusted.Sequence.length (encodeLittleEndianBytes bits (ty.sizeBytes .bits64) prov) =
        ty.sizeBytes .bits64 :=
    trusted_length_encodeLittleEndianBytes bits _ prov
  have hBeq :
      Nat.beq (Trusted.Sequence.length (encodeLittleEndianBytes bits (ty.sizeBytes .bits64) prov))
        (ty.sizeBytes .bits64) = true := by
    rw [hLen]; exact Nat.beq_refl _
  have hDec :
      decodeScalarBytes (encodeLittleEndianBytes bits (ty.sizeBytes .bits64) prov) false =
        some (⟨bits, ty.sizeBytes .bits64⟩, prov) :=
    trusted_decodeScalarBytes_encodeLittleEndianBytes _ bits prov false
      (ScalarTy.sizeBytes_pos .bits64 ty) h_bits
  have hNe : ty ≠ .char := by
    intro hC; subst hC; nomatch h_ptr
  have hIff := scalarTy_isValidBits_iff_validRange_of_ne_char .bits64 ty bits hNe
  unfold decodeScalarLayoutBytes
  rw [ScalarTy.scalarLayoutByteWidth_toScalarLayout_bits64 ty]
  dsimp only [ScalarTy.toScalarLayout]
  rw [hBeq]
  dsimp only
  rw [hDec]
  dsimp only
  cases hW : wrappingRangeContains (ty.toValidRange .bits64) bits
  · have hF : ty.isValidBits .bits64 bits = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      rw [hIff.mp ht] at hW
      nomatch hW
    rw [hF]
  · have hT : ty.isValidBits .bits64 bits = true := hIff.mpr hW
    rw [hT]
    cases ty <;> first | contradiction | (cases prov <;> rfl)

/--
Unified value-level agreement between `decodeScalarLayoutBytes (ty.toScalarLayout .bits64)`
and `decodeValueFromBytes` on provenance-free bytes (`prov = none`) for **all** `ty ≠ .char`
(both non-pointer scalars `bool`, `int`, `uint` AND pointer descriptors `rawPtr`, `refPtr`
with thin pointees).
-/
theorem decodeScalarLayoutBytes_toScalarLayout_bits64_eq_decodeValueFromBytes_of_ne_char
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (ty : ScalarTy) (lIdx bits : Nat)
    (h_ne : ty ≠ .char)
    (h_thin : ty.isPtr = true → isThinPointee pointee = true)
    (h_bits : bits < scalarModulus (ty.sizeBytes .bits64)) :
    decodeScalarLayoutBytes (ty.toScalarLayout .bits64)
        (encodeLittleEndianBytes bits (ty.sizeBytes .bits64) none) =
      decodeValueFromBytes defaultCodecFuel layouts
        { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx }
        (encodeLittleEndianBytes bits (ty.sizeBytes .bits64) none) := by
  cases hPtr : ty.isPtr
  · exact (decodeScalarLayoutBytes_toScalarLayout_bits64_of_ne_char layouts m pointee ty lIdx bits
      hPtr h_ne h_bits).2
  · have hThin := h_thin hPtr
    have hSz8 : ty.sizeBytes .bits64 = 8 := ScalarTy.sizeBytes_of_isPtr .bits64 ty hPtr
    have hBits8 : bits < scalarModulus 8 := hSz8 ▸ h_bits
    rw [decodeScalarLayoutBytes_toScalarLayout_bits64_ptr_eq ty bits none hPtr h_bits,
        hSz8, show defaultCodecFuel = 15 + 1 from rfl,
        trusted_decodeValueFromBytes_thin_ptrTy_no_prov 15 layouts m pointee ty lIdx _ bits
          hPtr hThin hBits8 (trusted_length_encodeLittleEndianBytes bits 8 none)
          (trusted_decodeScalarBytes_encodeLittleEndianBytes 8 bits none false (by decide) hBits8)]

/--
**Divergence (`char` surrogate gap).** `rustc`'s `char` scalar layout records
only `valid_range: 0..=0x10FFFF`, so on 64-bit targets the scalar-layout
decoder at `ScalarTy.char.toScalarLayout .bits64` accepts a 4-byte candidate
iff it is a valid `char` **or** a UTF-16 surrogate in `0xD800..=0xDFFF`.
`ScalarTy.isValidBits` and `Trusted.decodeValueFromBytes` at `RigidTy.char`
both reject surrogates; the surrogate `0xD800` (`55296`) witnesses the gap.
-/
theorem decodeScalarLayoutBytes_char_layout_surrogate_divergence
    (layouts : LayoutTable) (lIdx : LayoutIdx) (bits : Nat) (prov : Option (Nat × Nat))
    (h_bits : bits < scalarModulus 4) :
    ((∃ v, decodeScalarLayoutBytes (ScalarTy.char.toScalarLayout .bits64)
        (encodeLittleEndianBytes bits 4 prov) = some v) ↔
      (ScalarTy.char.isValidBits .bits64 bits = true ∨ (55296 ≤ bits ∧ bits ≤ 57343))) ∧
    decodeScalarLayoutBytes (ScalarTy.char.toScalarLayout .bits64)
        (encodeLittleEndianBytes 55296 4 none) = some (.scalar ⟨55296, 4⟩) ∧
    ScalarTy.char.isValidBits .bits64 55296 = false ∧
    decodeValueFromBytes defaultCodecFuel layouts { kind := .char, layoutIdx := lIdx }
        (encodeLittleEndianBytes 55296 4 none) = none := by
  refine ⟨?_, rfl, rfl, rfl⟩
  rw [decodeScalarLayoutBytes_toScalarLayout_bits64_some_iff .char bits prov h_bits,
    scalarTy_isValidBits_iff_scalarLayout_validRange .bits64 .char bits]
  have hW : wrappingRangeContains (ScalarTy.char.toValidRange .bits64) bits = true ↔
      bits ≤ 1114111 := by
    rw [show ScalarTy.char.toValidRange .bits64 = ⟨0, 1114111⟩ from rfl,
      wrappingRangeContains_zero_max_iff]
  rw [hW]
  constructor
  · intro hLe
    by_cases hSur : 55296 ≤ bits ∧ bits ≤ 57343
    · exact Or.inr hSur
    · exact Or.inl ⟨hLe, fun _ => hSur⟩
  · rintro (⟨hLe, _⟩ | ⟨_, hHi⟩)
    · exact hLe
    · omega

/-! ### 8.2 `ProvenanceFrag` Codec & `BitValidity` Byte-Sequence Bridge -/

/-- Translating any `List CastByte` via `CastByte.toTrustedAbstractByte` produces a fully initialized `AbstractByte` list. -/
@[simp]
theorem allBytesInitialized_map_toTrustedAbstractByte (bs : List CastByte) :
    allBytesInitialized (bs.map CastByte.toTrustedAbstractByte) = true := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    unfold List.map CastByte.toTrustedAbstractByte
    exact ih

/-- Whenever `encodeCastVal pw src val = some cBytes`, `cBytes` has exact length `src.sizeBytes pw` and its `Trusted` image is fully initialized. -/
theorem encodeCastVal_length_and_init
    (pw : PtrWidth) (src : ScalarTy) (val : CastVal) (cBytes : List CastByte)
    (hEnc : encodeCastVal pw src val = some cBytes) :
    cBytes.length = src.sizeBytes pw ∧
    allBytesInitialized (cBytes.map CastByte.toTrustedAbstractByte) = true := by
  refine ⟨?_, allBytesInitialized_map_toTrustedAbstractByte cBytes⟩
  unfold encodeCastVal at hEnc
  cases hPtr : src.isPtr <;> rw [hPtr] at hEnc
  · cases val with
    | ptr _ _ => nomatch hEnc
    | scalar bits =>
      dsimp only at hEnc
      cases hV : src.isValidBits pw bits <;> rw [hV] at hEnc
      · nomatch hEnc
      · injection hEnc with hEq
        subst hEq
        exact encodeCastBytes_length bits (src.sizeBytes pw) none
  · cases val with
    | scalar _ => nomatch hEnc
    | ptr p prov =>
      dsimp only at hEnc
      cases hV : src.isValidBits pw p.offsetBytes <;> rw [hV] at hEnc
      · nomatch hEnc
      · injection hEnc with hEq
        subst hEq
        exact encodeCastBytes_length p.offsetBytes (src.sizeBytes pw) prov

/--
Exact `ProvenanceFrag` / `checkProvenanceFrags` characterization on `encodeCastVal`:
when `encodeCastVal pw src val = some cBytes`:
1. `checkProvenanceFrags allocId cBytes 0 = true` iff `src.isPtr = true ∧ ∃ p, val = .ptr p (some allocId)`.
2. `decodeCastPtrProv cBytes = some allocId` iff `src.isPtr = true ∧ ∃ p, val = .ptr p (some allocId)`.
3. `decodeCastPtrProv cBytes = none` iff `src.isPtr = false ∨ ∃ p, val = .ptr p none`.
-/
theorem encodeCastVal_checkProvenanceFrags_iff
    (pw : PtrWidth) (src : ScalarTy) (val : CastVal) (cBytes : List CastByte)
    (allocId : Nat)
    (hEnc : encodeCastVal pw src val = some cBytes) :
    (checkProvenanceFrags allocId cBytes 0 = true ↔
      (src.isPtr = true ∧ ∃ p, val = .ptr p (some allocId))) ∧
    (decodeCastPtrProv cBytes = some allocId ↔
      (src.isPtr = true ∧ ∃ p, val = .ptr p (some allocId))) ∧
    (decodeCastPtrProv cBytes = none ↔
      (src.isPtr = false ∨ ∃ p, val = .ptr p none)) := by
  have hPos : 0 < src.sizeBytes pw := ScalarTy.sizeBytes_pos pw src
  obtain ⟨rem, hRem⟩ : ∃ rem, src.sizeBytes pw = rem + 1 := ⟨src.sizeBytes pw - 1, by omega⟩
  unfold encodeCastVal at hEnc
  cases hPtr : src.isPtr <;> rw [hPtr] at hEnc
  · cases val with
    | ptr _ _ => nomatch hEnc
    | scalar bits =>
      dsimp only at hEnc
      cases hValid : src.isValidBits pw bits <;> rw [hValid] at hEnc
      · nomatch hEnc
      · injection hEnc with hEq
        subst hEq
        have hFragFalse : checkProvenanceFrags allocId (encodeCastBytes bits (src.sizeBytes pw) none) 0 = false := by
          rw [hRem]
          rfl
        have hProvNone : decodeCastPtrProv (encodeCastBytes bits (src.sizeBytes pw) none) = none :=
          decodeCastPtrProv_encodeCastBytes_none bits (src.sizeBytes pw)
        rw [hFragFalse, hProvNone]
        simp
  · cases val with
    | scalar _ => nomatch hEnc
    | ptr p prov =>
      dsimp only at hEnc
      cases hValid : src.isValidBits pw p.offsetBytes <;> rw [hValid] at hEnc
      · nomatch hEnc
      · injection hEnc with hEq
        subst hEq
        cases prov with
        | none =>
          have hFragFalse : checkProvenanceFrags allocId (encodeCastBytes p.offsetBytes (src.sizeBytes pw) none) 0 = false := by
            rw [hRem]
            rfl
          have hProvNone : decodeCastPtrProv (encodeCastBytes p.offsetBytes (src.sizeBytes pw) none) = none :=
            decodeCastPtrProv_encodeCastBytes_none p.offsetBytes (src.sizeBytes pw)
          rw [hFragFalse, hProvNone]
          simp
        | some a =>
          have hProvSome :
              decodeCastPtrProv (encodeCastBytes p.offsetBytes (src.sizeBytes pw) (some a)) = some a := by
            rw [hRem]
            exact decodeCastPtrProv_encodeCastBytes_some rem p.offsetBytes a
          have hFragIff :
              checkProvenanceFrags allocId (encodeCastBytes p.offsetBytes (src.sizeBytes pw) (some a)) 0 = true ↔
                a = allocId := by
            constructor
            · intro hChk
              rw [hRem] at hChk
              unfold encodeCastBytes encodeCastBytesAux checkProvenanceFrags at hChk
              dsimp only [Option.map, Nat.beq_refl, Bool.and_true] at hChk
              cases hBeqA : Nat.beq a allocId <;> rw [hBeqA] at hChk
              · nomatch hChk
              · exact Nat.beq_eq.mp hBeqA
            · intro hEqA
              subst hEqA
              exact checkProvenanceFrags_encodeCastBytesAux a p.offsetBytes (src.sizeBytes pw) 0
          rw [hProvSome, hFragIff]
          refine ⟨?_, ?_, ?_⟩
          · simp [eq_comm]
          · simp
          · simp

/--
**`encodeCastVal_preserved_of_isIntoBytes`**:
Whenever `encodeCastVal pw src val = some cBytes`:
1. `cBytes` has length `src.sizeBytes pw` and its `Trusted` image `cBytes.map CastByte.toTrustedAbstractByte` satisfies `allBytesInitialized = true`.
2. On 64-bit targets (`pw = .bits64`) for any non-pointer scalar `src` (`src.isPtr = false`; every such `src` satisfies `IsIntoBytes`, see `scalarTy_isIntoBytes_of_not_isPtr`), `encodeValueToBytes` on `val.toTrustedValue .bits64 src` produces `some (cBytes.map CastByte.toTrustedAbstractByte)` and `ByteSeqValid ... .Initialized` holds.
3. For any `dstTy : Ty` satisfying `IsFromBytes layouts dstTy` of the same byte size `src.sizeBytes pw`, `cBytes.map CastByte.toTrustedAbstractByte` satisfies `ByteSeqValid layouts dstTy .BitValid` (decoding to `some v'`).
4. On 64-bit targets with a thin pointee, the same `encodeValueToBytes` agreement and `ByteSeqValid ... .Initialized` hold for pointer sources carrying provenance (`val = .ptr p (some a)`). Provenance-free pointer sources are excluded: `CastVal.toTrustedValue` maps them to `Trusted`'s 64 KiB page-model pointer `addressToPtr p.offsetBytes`, whose `Trusted` encoding carries a reconstructed provenance and only the in-page offset.
-/
theorem encodeCastVal_preserved_of_isIntoBytes
    (pw : PtrWidth) (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (src : ScalarTy) (srcLIdx : LayoutIdx) (val : CastVal) (cBytes : List CastByte)
    (hEnc : encodeCastVal pw src val = some cBytes) :
    let tBytes := cBytes.map CastByte.toTrustedAbstractByte
    cBytes.length = src.sizeBytes pw ∧
    allBytesInitialized tBytes = true ∧
    (pw = .bits64 → src.isPtr = false →
      encodeValueToBytes defaultCodecFuel layouts
        { kind := src.toTrustedRigidTy m pointee, layoutIdx := srcLIdx }
        (val.toTrustedValue .bits64 src) = some tBytes ∧
      ByteSeqValid layouts
        { kind := src.toTrustedRigidTy m pointee, layoutIdx := srcLIdx }
        .Initialized tBytes) ∧
    (∀ (dstTy : Ty),
      IsFromBytes layouts dstTy →
      rigidTyByteSize layouts dstTy = some (src.sizeBytes pw) →
      ByteSeqValid layouts dstTy .BitValid tBytes) ∧
    (pw = .bits64 → isThinPointee pointee = true → ∀ p a, val = .ptr p (some a) →
      encodeValueToBytes defaultCodecFuel layouts
        { kind := src.toTrustedRigidTy m pointee, layoutIdx := srcLIdx }
        (val.toTrustedValue .bits64 src) = some tBytes ∧
      ByteSeqValid layouts
        { kind := src.toTrustedRigidTy m pointee, layoutIdx := srcLIdx }
        .Initialized tBytes) := by
  intro tBytes
  have ⟨hLen, hInit⟩ := encodeCastVal_length_and_init pw src val cBytes hEnc
  have hTLen : Trusted.Sequence.length tBytes = src.sizeBytes pw := by
    simp [tBytes, Trusted.Sequence.length, hLen]
  refine ⟨hLen, hInit, ?_, ?_, ?_⟩
  · intro hPw hNp
    subst hPw
    unfold encodeCastVal at hEnc
    rw [hNp] at hEnc
    cases val with
    | ptr _ _ => nomatch hEnc
    | scalar bits =>
      dsimp only at hEnc
      cases hValidB : src.isValidBits .bits64 bits <;> rw [hValidB] at hEnc
      · nomatch hEnc
      · injection hEnc with hEq
        subst hEq
        have hValid : src.validBits .bits64 bits :=
          (ScalarTy.isValidBits_iff_validBits .bits64 src bits).mp hValidB
        have hTEnc :=
          trusted_encodeValueToBytes_scalar 15 layouts m pointee src srcLIdx bits hNp hValid
        have hMap :
            tBytes = encodeLittleEndianBytes bits (src.sizeBytes .bits64) none := by
          unfold tBytes
          rw [map_toTrustedAbstractByte_encodeCastBytes]
          rfl
        refine ⟨?_, ?_⟩
        · rw [hMap]
          exact hTEnc
        · refine ⟨src.sizeBytes .bits64,
            ScalarTy.rigidTyByteSize_toTrustedRigidTy_of_not_isPtr layouts m pointee src srcLIdx hNp,
            hTLen, hInit⟩
  · intro dstTy hFrom hDstSz
    rcases hFrom with ⟨szDst, hSzDst, hDecProps⟩
    rw [hDstSz] at hSzDst
    injection hSzDst with hSzEq
    subst hSzEq
    rcases hDecProps tBytes hTLen hInit with ⟨v', hV'⟩
    exact ⟨src.sizeBytes pw, v', hDstSz, hTLen, hV'⟩
  · intro hPw hThin p a hVal
    subst hPw
    subst hVal
    unfold encodeCastVal at hEnc
    cases hPtr : src.isPtr <;> rw [hPtr] at hEnc
    · nomatch hEnc
    · dsimp only at hEnc
      cases hV : src.isValidBits .bits64 p.offsetBytes <;> rw [hV] at hEnc
      · nomatch hEnc
      · injection hEnc with hEq
        have hSz8 := ScalarTy.sizeBytes_of_isPtr .bits64 src hPtr
        have hMap : tBytes = encodeLittleEndianBytes p.offsetBytes 8 (some (a, a)) := by
          show cBytes.map CastByte.toTrustedAbstractByte = _
          rw [← hEq, map_toTrustedAbstractByte_encodeCastBytes, hSz8]
          rfl
        have hTEnc := trusted_encodeValueToBytes_thin_ptrTy 15 layouts m pointee src srcLIdx
          { allocId := a, offsetBytes := p.offsetBytes } hPtr hThin
        refine ⟨?_, ?_⟩
        · rw [hMap]
          exact hTEnc
        · refine ⟨8, ?_, ?_, ?_⟩
          · rw [ScalarTy.rigidTyByteSize_toTrustedRigidTy layouts m pointee src srcLIdx hThin, hSz8]
          · rw [hMap]
            exact trusted_length_encodeLittleEndianBytes _ _ _
          · simp only [hMap]

/-- Provenance-free decoding: whenever `decodeCastPtrProv bytes = none` (missing,
foreign, or shuffled fragments), `decodeCastVal` at any target is decided by
`dst.isValidBits` alone and never produces provenance (pointer targets get
`allocId = 0` and `prov = none`). -/
theorem decodeCastVal_of_decodeCastPtrProv_none
    (pw : PtrWidth) (dst : ScalarTy) (bytes : List CastByte)
    (h_prov : decodeCastPtrProv bytes = none) :
    decodeCastVal pw dst bytes =
      match dst.isValidBits pw (decodeCastIntBytes bytes) with
      | false => none
      | true =>
        some (if dst.isPtr then .ptr { allocId := 0, offsetBytes := decodeCastIntBytes bytes } none
              else .scalar (decodeCastIntBytes bytes)) := by
  unfold decodeCastVal decodeCastPtrBytes
  cases hp : dst.isPtr <;> cases hv : dst.isValidBits pw (decodeCastIntBytes bytes) <;>
    simp [h_prov, hv]

/--
**Overwrite bridge (`ProvenanceFrag` stripping vs. `BitValidity` invariants).**
Let `encodeCastVal pw src val = some cBytes`, and overwrite any byte
`i < cBytes.length` with a byte `b` that either carries no provenance fragment,
or carries a fragment of an allocation other than the one `val` points into.
Then:
1. the overwritten bytes keep the exact length `src.sizeBytes pw` and their
   `Trusted` image stays fully initialized, so it is `ByteSeqValid .Initialized`
   at every type of that byte size and `ByteSeqValid .BitValid` at every
   same-sized `IsFromBytes` type;
2. `decodeCastPtrProv` strips provenance (`none`);
3. `decodeCastVal` at any target `dst` returns a provenance-free value decided
   only by `dst.isValidBits pw` on the overwritten address bits.
-/
theorem encodeCastVal_overwrite_strips_provenance_preserves_bitValidity
    (pw : PtrWidth) (layouts : LayoutTable) (src dst : ScalarTy) (val : CastVal)
    (cBytes : List CastByte) (i : Nat) (b : CastByte)
    (hEnc : encodeCastVal pw src val = some cBytes)
    (h_i : i < cBytes.length)
    (h_b : b.prov = none ∨
      ∃ f p a, b.prov = some f ∧ val = .ptr p (some a) ∧ f.allocId ≠ a) :
    let bytes := cBytes.set i b
    let tBytes := bytes.map CastByte.toTrustedAbstractByte
    bytes.length = src.sizeBytes pw ∧
    allBytesInitialized tBytes = true ∧
    (∀ ty : Ty, rigidTyByteSize layouts ty = some (src.sizeBytes pw) →
      ByteSeqValid layouts ty .Initialized tBytes) ∧
    (∀ ty : Ty, IsFromBytes layouts ty → rigidTyByteSize layouts ty = some (src.sizeBytes pw) →
      ByteSeqValid layouts ty .BitValid tBytes) ∧
    decodeCastPtrProv bytes = none ∧
    decodeCastVal pw dst bytes =
      match dst.isValidBits pw (decodeCastIntBytes bytes) with
      | false => none
      | true =>
        some (if dst.isPtr then .ptr { allocId := 0, offsetBytes := decodeCastIntBytes bytes } none
              else .scalar (decodeCastIntBytes bytes)) := by
  intro bytes tBytes
  have hLen0 := (encodeCastVal_length_and_init pw src val cBytes hEnc).1
  have hLen : bytes.length = src.sizeBytes pw := by
    simp only [bytes, List.length_set, hLen0]
  have hInit : allBytesInitialized tBytes = true :=
    allBytesInitialized_map_toTrustedAbstractByte bytes
  have hTLen : Trusted.Sequence.length tBytes = src.sizeBytes pw := by
    simp [tBytes, Trusted.Sequence.length, hLen]
  have hProv : decodeCastPtrProv bytes = none := by
    rcases h_b with hNone | ⟨f, p, a, hSome, hVal, hNe⟩
    · exact decodeCastPtrProv_eq_none_of_prov_none bytes i (by simp [bytes, h_i])
        (by simp [bytes, hNone])
    · subst hVal
      unfold encodeCastVal at hEnc
      cases hPtr : src.isPtr <;> rw [hPtr] at hEnc
      · nomatch hEnc
      · dsimp only at hEnc
        cases hV : src.isValidBits pw p.offsetBytes <;> rw [hV] at hEnc
        · nomatch hEnc
        · injection hEnc with hEq
          have hTwo : 2 ≤ src.sizeBytes pw := by
            rw [ScalarTy.sizeBytes_of_isPtr pw src hPtr]
            cases pw <;> decide
          have hI : i < src.sizeBytes pw := by
            rw [← hEq] at h_i
            simpa using h_i
          rcases b with ⟨d, bp⟩
          rcases f with ⟨fa, fpos⟩
          dsimp only at hSome hNe
          subst hSome
          show decodeCastPtrProv
            (cBytes.set i { data := d, prov := some { allocId := fa, position := fpos } }) = none
          rw [← hEq]
          exact decodeCastPtrProv_encodeCastBytes_set_foreign p.offsetBytes (src.sizeBytes pw) a fa
            i fpos d hI hTwo hNe
  refine ⟨hLen, hInit, ?_, ?_, hProv, decodeCastVal_of_decodeCastPtrProv_none pw dst bytes hProv⟩
  · intro ty hSz
    exact ⟨src.sizeBytes pw, hSz, hTLen, hInit⟩
  · intro ty hFrom hSz
    rcases hFrom with ⟨szDst, hSzDst, hDecProps⟩
    rw [hSz] at hSzDst
    injection hSzDst with hSzEq
    subst hSzEq
    rcases hDecProps tBytes hTLen hInit with ⟨v', hV'⟩
    exact ⟨src.sizeBytes pw, v', hSz, hTLen, hV'⟩

/-! ### 8.3 `zerocopy` Traits ↔ `evalTransmuteSameSize` & `Trusted.MirSemantics.evalByteCast` Soundness -/

/-- Every non-pointer `ScalarTy` satisfies `checkBaseIntoBytesKind` and `checkIntoBytes`. -/
theorem scalarTy_checkIntoBytes_of_not_isPtr
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (ty : ScalarTy) (lIdx : LayoutIdx) (h_np : ty.isPtr = false) :
    checkBaseIntoBytesKind (ty.toTrustedRigidTy m pointee) = true ∧
    checkIntoBytes layouts { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx } = true := by
  cases ty <;> first | contradiction | exact ⟨rfl, rfl⟩

/-- Exact characterization of `checkIntoBytes` on `ScalarTy.toTrustedRigidTy`: it holds iff `ty.isPtr = false`. -/
theorem scalarTy_checkIntoBytes_iff_not_isPtr
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (ty : ScalarTy) (lIdx : LayoutIdx) :
    checkIntoBytes layouts { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx } = true ↔
      ty.isPtr = false := by
  cases ty <;> simp [checkIntoBytes, checkBaseIntoBytesKind, ScalarTy.isPtr]

/-- Every non-pointer `ScalarTy` (`bool`, `char`, `int w`, `uint w`) satisfies `IsIntoBytes`. -/
theorem scalarTy_isIntoBytes_of_not_isPtr
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (ty : ScalarTy) (lIdx : LayoutIdx) (h_np : ty.isPtr = false) :
    IsIntoBytes layouts { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx } :=
  checkIntoBytes_sound layouts _ (scalarTy_checkIntoBytes_of_not_isPtr layouts m pointee ty lIdx h_np).2

private theorem encodeValueToBytes_thin_ptr_eq
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (ty : ScalarTy) (lIdx : LayoutIdx) (v : Value)
    (hPtr : ty.isPtr = true) (h_thin : isThinPointee pointee = true) :
    encodeValueToBytes defaultCodecFuel layouts
        { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx } v =
      match false, v with
      | false, .ptr p 8 =>
        encodeScalarBytes ⟨p.offsetBytes, 8⟩ (.some (p.allocId, p.tag))
      | false, .scalar sv =>
        match Nat.beq sv.sizeBytes 8 with
        | true => encodeScalarBytes sv .none
        | false => .none
      | true, .aggregate 0 (.ptr p 8 :: .scalar metaSc :: .nil) =>
        match
          encodeScalarBytes ⟨p.offsetBytes, 8⟩ (.some (p.allocId, p.tag)),
          encodeScalarBytes ⟨metaSc.bits, 8⟩ .none
        with
        | .some b1, .some b2 => .some (appendAbstractBytes b1 b2)
        | _, _ => .none
      | _, _ => .none := by
  cases ty <;>
    first
    | contradiction
    | (cases pointee <;> first | rfl | simp [isThinPointee] at h_thin)

private theorem encodeValueToBytes_wide_ptr_eq
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (ty : ScalarTy) (lIdx : LayoutIdx) (v : Value)
    (hPtr : ty.isPtr = true) (h_wide : isThinPointee pointee = false) :
    encodeValueToBytes defaultCodecFuel layouts
        { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx } v =
      match true, v with
      | false, .ptr p 8 =>
        encodeScalarBytes ⟨p.offsetBytes, 8⟩ (.some (p.allocId, p.tag))
      | false, .scalar sv =>
        match Nat.beq sv.sizeBytes 8 with
        | true => encodeScalarBytes sv .none
        | false => .none
      | true, .aggregate 0 (.ptr p 8 :: .scalar metaSc :: .nil) =>
        match
          encodeScalarBytes ⟨p.offsetBytes, 8⟩ (.some (p.allocId, p.tag)),
          encodeScalarBytes ⟨metaSc.bits, 8⟩ .none
        with
        | .some b1, .some b2 => .some (appendAbstractBytes b1 b2)
        | _, _ => .none
      | _, _ => .none := by
  cases ty <;>
    first
    | contradiction
    | (cases pointee <;> first | rfl | simp [isThinPointee] at h_wide)

private theorem rigidTyByteSize_wide_ptr_eq
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (ty : ScalarTy) (lIdx : LayoutIdx)
    (hPtr : ty.isPtr = true) (h_wide : isThinPointee pointee = false) :
    rigidTyByteSize layouts { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx } =
      some 16 := by
  cases ty <;>
    first
    | contradiction
    | (cases pointee <;> first | rfl | simp [isThinPointee] at h_wide)

/--
Every `ScalarTy` with a thin pointee (including `.rawPtr` and `.refPtr`) satisfies
the semantic predicate `IsIntoBytes` in `Trusted`.

Model note: `IsIntoBytes` only requires every encoding to be fully initialized
and of the right length. Encoded pointer bytes are initialized but carry
provenance, so this does **not** mean that pointers may soundly be reinterpreted
as integers; `zerocopy` does not implement `IntoBytes` for pointers, and the
decidable certificate `checkIntoBytes` accordingly rejects every pointer
descriptor (`scalarTy_checkIntoBytes_iff_not_isPtr`).
-/
theorem scalarTy_isIntoBytes_of_thin
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (ty : ScalarTy) (lIdx : LayoutIdx) (h_thin : isThinPointee pointee = true) :
    IsIntoBytes layouts { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx } := by
  cases hPtr : ty.isPtr
  · exact scalarTy_isIntoBytes_of_not_isPtr layouts m pointee ty lIdx hPtr
  · refine ⟨8, ?_, ?_⟩
    · rw [ScalarTy.rigidTyByteSize_toTrustedRigidTy layouts m pointee ty lIdx h_thin,
          ScalarTy.sizeBytes_of_isPtr .bits64 ty hPtr]
    · intro v bs hEnc
      rw [encodeValueToBytes_thin_ptr_eq layouts m pointee ty lIdx v hPtr h_thin] at hEnc
      cases v with
      | scalar sv =>
        dsimp only at hEnc
        cases h8 : Nat.beq sv.sizeBytes 8 <;> rw [h8] at hEnc
        · nomatch hEnc
        · have hSz8 : sv.sizeBytes = 8 := Nat.eq_of_beq_eq_true h8
          have ⟨hLen, hInit⟩ := encodeScalarBytes_length_and_init sv none bs hEnc
          exact ⟨hSz8 ▸ hLen, hInit⟩
      | ptr p sz =>
        cases sz with
        | zero => nomatch hEnc
        | succ k =>
          match k with
          | 7 =>
            exact encodeScalarBytes_length_and_init ⟨p.offsetBytes, 8⟩ (some (p.allocId, p.tag)) bs hEnc
          | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 8 => nomatch hEnc
      | unit => nomatch hEnc
      | aggregate varIdx fs =>
        match varIdx, fs with
        | 0, .ptr _ 8 :: .scalar _ :: .nil => nomatch hEnc
        | _, _ => nomatch hEnc

/--
Unconditional `IsIntoBytes` for **every** `ScalarTy.toTrustedRigidTy m pointee` across all
pointees (both 8-byte thin pointers and 16-byte wide pointers `.slice _`, `.str`, `.dynamic _`).
-/
theorem scalarTy_isIntoBytes
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (ty : ScalarTy) (lIdx : LayoutIdx) :
    IsIntoBytes layouts { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx } := by
  cases hThin : isThinPointee pointee
  · cases hPtr : ty.isPtr
    · exact scalarTy_isIntoBytes_of_not_isPtr layouts m pointee ty lIdx hPtr
    · refine ⟨16, rigidTyByteSize_wide_ptr_eq layouts m pointee ty lIdx hPtr hThin, ?_⟩
      intro v bs hEnc
      rw [encodeValueToBytes_wide_ptr_eq layouts m pointee ty lIdx v hPtr hThin] at hEnc
      split at hEnc
      · contradiction
      · contradiction
      · rename_i p metaSc _
        cases hB1 : encodeScalarBytes ⟨p.offsetBytes, 8⟩ (some (p.allocId, p.tag)) <;>
          rw [hB1] at hEnc
        · nomatch hEnc
        case some b1 =>
          cases hB2 : encodeScalarBytes ⟨metaSc.bits, 8⟩ none <;> rw [hB2] at hEnc
          · nomatch hEnc
          case some b2 =>
            injection hEnc with hBs
            subst hBs
            rw [appendAbstractBytes_eq_append]
            have ⟨hL1, hI1⟩ :=
              encodeScalarBytes_length_and_init ⟨p.offsetBytes, 8⟩ (some (p.allocId, p.tag)) b1 hB1
            have ⟨hL2, hI2⟩ :=
              encodeScalarBytes_length_and_init ⟨metaSc.bits, 8⟩ none b2 hB2
            dsimp only at hL1 hL2
            refine ⟨?_, allBytesInitialized_append hI1 hI2⟩
            simp [Trusted.Sequence.length] at hL1 hL2 ⊢
            omega
      · nomatch hEnc
  · exact scalarTy_isIntoBytes_of_thin layouts m pointee ty lIdx hThin

/-- Exact characterization of `checkFromBytes` on `ScalarTy.toTrustedRigidTy`: it holds iff `ty.isIntegral = true`. -/
theorem scalarTy_checkFromBytes_iff_isIntegral
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (ty : ScalarTy) (lIdx : LayoutIdx) :
    checkFromBytes layouts { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx } = true ↔
      ty.isIntegral = true := by
  cases ty <;> simp [checkFromBytes, checkBaseFromBytesKind, ScalarTy.isIntegral]

/-- Every integral `ScalarTy` (`int w` or `uint w`) satisfies `IsFromBytes`. -/
theorem scalarTy_isFromBytes_of_isIntegral
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (ty : ScalarTy) (lIdx : LayoutIdx) (h_int : ty.isIntegral = true) :
    IsFromBytes layouts { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx } :=
  checkFromBytes_sound layouts _ ((scalarTy_checkFromBytes_iff_isIntegral layouts m pointee ty lIdx).mpr h_int)

/-- A thin raw pointer `.rawPtr m pointee` satisfies `IsFromBytes` in `Trusted` (`decodeValueFromBytes` decodes any 8 initialized bytes). -/
theorem thin_rawPtr_isFromBytes
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (lIdx : LayoutIdx) (h_thin : isThinPointee pointee = true) :
    IsFromBytes layouts { kind := .rawPtr m pointee, layoutIdx := lIdx } := by
  refine ⟨8, trusted_rigidTyByteSize_thin_rawPtr layouts m pointee lIdx h_thin, ?_⟩
  intro bs hLen hInit
  have hNz : Nat.beq (Trusted.Sequence.length bs) 0 = false := by
    rw [hLen]; rfl
  rcases decodeScalarBytes_of_allBytesInitialized bs false hNz hInit with ⟨sv, prov, hDec⟩
  have hBeq8 : Nat.beq (Trusted.Sequence.length bs) 8 = true := by
    rw [hLen]; rfl
  rw [show defaultCodecFuel = 15 + 1 from rfl,
      trusted_decodeValueFromBytes_thin_rawPtr_eq 15 layouts m pointee lIdx bs h_thin,
      hBeq8]
  dsimp only
  rw [hDec]
  cases prov <;> exact ⟨_, rfl⟩

private theorem decodeValueFromBytes_wide_rawPtr_eq
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (lIdx : LayoutIdx) (bs : List AbstractByte)
    (h_wide : isThinPointee pointee = false) :
    decodeValueFromBytes defaultCodecFuel layouts { kind := .rawPtr m pointee, layoutIdx := lIdx } bs =
      match Nat.beq (Trusted.Sequence.length bs) 16 with
      | false => .none
      | true =>
        let dataBytes := takeAbstractBytes 8 bs
        let metaBytes := dropAbstractBytes 8 bs
        match decodeScalarBytes dataBytes false, decodeScalarBytes metaBytes false with
        | .some (dataSv, prov), .some (metaSv, _) =>
          let ptrVal : ProvenancePtr :=
            match prov with
            | .some (allocId, _) => { allocId := allocId, offsetBytes := dataSv.bits }
            | .none =>
              { allocId := Nat.div dataSv.bits 65536, offsetBytes := Nat.mod dataSv.bits 65536 }
          .some (.aggregate 0 (.ptr ptrVal 8 :: .scalar metaSv :: .nil))
        | _, _ => .none := by
  cases pointee <;> first | rfl | simp [isThinPointee] at h_wide

/-- A wide raw pointer `.rawPtr m pointee` (`isThinPointee pointee = false`) satisfies `IsFromBytes` in `Trusted` (`decodeValueFromBytes` decodes any 16 initialized bytes). -/
theorem wide_rawPtr_isFromBytes
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (lIdx : LayoutIdx) (h_wide : isThinPointee pointee = false) :
    IsFromBytes layouts { kind := .rawPtr m pointee, layoutIdx := lIdx } := by
  refine ⟨16, rigidTyByteSize_wide_ptr_eq layouts m pointee .rawPtr lIdx rfl h_wide, ?_⟩
  intro bs hLen hInit
  have hBeq16 : Nat.beq (Trusted.Sequence.length bs) 16 = true := by
    rw [hLen]; rfl
  have hTakeLen : Trusted.Sequence.length (bs.take 8) = 8 := by
    simp [Trusted.Sequence.length, List.length_take] at hLen ⊢
    omega
  have hDropLen : Trusted.Sequence.length (bs.drop 8) = 8 := by
    simp [Trusted.Sequence.length, List.length_drop] at hLen ⊢
    omega
  have hTakeNz : Nat.beq (Trusted.Sequence.length (bs.take 8)) 0 = false := by
    rw [hTakeLen]; rfl
  have hDropNz : Nat.beq (Trusted.Sequence.length (bs.drop 8)) 0 = false := by
    rw [hDropLen]; rfl
  rcases decodeScalarBytes_of_allBytesInitialized (bs.take 8) false hTakeNz
    (allBytesInitialized_take 8 hInit) with ⟨dataSv, prov, hDataDec⟩
  rcases decodeScalarBytes_of_allBytesInitialized (bs.drop 8) false hDropNz
    (allBytesInitialized_drop 8 hInit) with ⟨metaSv, metaProv, hMetaDec⟩
  rw [decodeValueFromBytes_wide_rawPtr_eq layouts m pointee lIdx bs h_wide, hBeq16]
  dsimp only
  rw [takeAbstractBytes_eq_take, dropAbstractBytes_eq_drop, hDataDec, hMetaDec]
  dsimp only
  exact ⟨_, rfl⟩

/-- Every raw pointer `.rawPtr m pointee` (thin or wide) satisfies `IsFromBytes` in `Trusted`. -/
theorem rawPtr_isFromBytes
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (lIdx : LayoutIdx) :
    IsFromBytes layouts { kind := .rawPtr m pointee, layoutIdx := lIdx } := by
  cases hThin : isThinPointee pointee
  · exact wide_rawPtr_isFromBytes layouts m pointee lIdx hThin
  · exact thin_rawPtr_isFromBytes layouts m pointee lIdx hThin

/-- Reference types `.ref m pointee` never satisfy `IsFromBytes` (for any pointee, thin or wide), because all-zero bytes violate the non-null reference niche. -/
theorem ref_not_isFromBytes
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (lIdx : LayoutIdx) :
    ¬ IsFromBytes layouts { kind := .ref m pointee, layoutIdx := lIdx } := by
  rintro ⟨sz, hSz, hDec⟩
  cases pointee <;>
    (injection hSz with hSzEq;
     subst hSzEq;
     rcases hDec _ (length_zeroInitBytes _) (allBytesInitialized_zeroInitBytes _) with ⟨v, hv⟩;
     nomatch hv)

/-- Reference types `.ref m pointee` never satisfy `IsFromZeros`. -/
theorem ref_not_isFromZeros
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (lIdx : LayoutIdx) :
    ¬ IsFromZeros layouts { kind := .ref m pointee, layoutIdx := lIdx } := by
  rintro ⟨sz, v, hSz, hv⟩
  cases pointee <;>
    (injection hSz with hSzEq;
     subst hSzEq;
     nomatch hv)

/-- Among non-pointer `ScalarTy`s, `IsFromBytes` holds if and only if `ty.isIntegral = true`. -/
theorem scalarTy_isFromBytes_iff_of_not_isPtr
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (ty : ScalarTy) (lIdx : LayoutIdx) (h_np : ty.isPtr = false) :
    IsFromBytes layouts { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx } ↔
      ty.isIntegral = true := by
  constructor
  · intro hFrom
    cases ty with
    | int _ | uint _ => rfl
    | bool => exact False.elim (bool_not_isFromBytes layouts lIdx hFrom)
    | char => exact False.elim (char_not_isFromBytes layouts lIdx hFrom)
    | rawPtr | refPtr => contradiction
  · exact scalarTy_isFromBytes_of_isIntegral layouts m pointee ty lIdx

/-- Unconditional `IsFromBytes` characterization across **all** `ScalarTy`s and **all** pointees (thin or wide): `IsFromBytes` holds in `Trusted` iff `ty.isIntegral = true ∨ ty = .rawPtr`. -/
theorem scalarTy_isFromBytes_iff
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (ty : ScalarTy) (lIdx : LayoutIdx) :
    IsFromBytes layouts { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx } ↔
      (ty.isIntegral = true ∨ ty = .rawPtr) := by
  constructor
  · intro hFrom
    cases ty with
    | int _ | uint _ => exact Or.inl rfl
    | rawPtr => exact Or.inr rfl
    | bool => exact False.elim (bool_not_isFromBytes layouts lIdx hFrom)
    | char => exact False.elim (char_not_isFromBytes layouts lIdx hFrom)
    | refPtr => exact False.elim (ref_not_isFromBytes layouts m pointee lIdx hFrom)
  · rintro (hInt | rfl)
    · exact scalarTy_isFromBytes_of_isIntegral layouts m pointee ty lIdx hInt
    · exact rawPtr_isFromBytes layouts m pointee lIdx

/-- Across all `ScalarTy`s with a thin pointee, `IsFromBytes` holds in `Trusted` iff `ty.isIntegral = true ∨ ty = .rawPtr`. -/
theorem scalarTy_isFromBytes_iff_of_thin
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (ty : ScalarTy) (lIdx : LayoutIdx) (_h_thin : isThinPointee pointee = true) :
    IsFromBytes layouts { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx } ↔
      (ty.isIntegral = true ∨ ty = .rawPtr) :=
  scalarTy_isFromBytes_iff layouts m pointee ty lIdx

/-- Unconditional `IsFromZeros` characterization across **all** `ScalarTy`s and **all** pointees (thin or wide): `IsFromZeros` holds in `Trusted` iff `ty ≠ .refPtr`. -/
theorem scalarTy_isFromZeros_iff
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (ty : ScalarTy) (lIdx : LayoutIdx) :
    IsFromZeros layouts { kind := ty.toTrustedRigidTy m pointee, layoutIdx := lIdx } ↔
      ty ≠ .refPtr := by
  constructor
  · intro hFz hEq
    subst hEq
    exact ref_not_isFromZeros layouts m pointee lIdx hFz
  · intro hNe
    cases ty with
    | bool => exact bool_isFromZeros layouts lIdx
    | char => exact char_isFromZeros layouts lIdx
    | int w =>
      exact isFromBytes_implies_isFromZeros layouts _
        (scalarTy_isFromBytes_of_isIntegral layouts m pointee (.int w) lIdx rfl)
    | uint w =>
      exact isFromBytes_implies_isFromZeros layouts _
        (scalarTy_isFromBytes_of_isIntegral layouts m pointee (.uint w) lIdx rfl)
    | rawPtr =>
      exact isFromBytes_implies_isFromZeros layouts _
        (rawPtr_isFromBytes layouts m pointee lIdx)
    | refPtr => exact absurd rfl hNe

/-- Any `dst : ScalarTy` whose `Trusted` image satisfies `IsFromBytes` accepts all bit patterns `< scalarModulus (dst.sizeBytes pw)`. -/
theorem scalarTy_isValidBits_of_isFromBytes
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (dst : ScalarTy) (lIdx : LayoutIdx) (pw : PtrWidth) (bits : Nat)
    (hFrom : IsFromBytes layouts { kind := dst.toTrustedRigidTy m pointee, layoutIdx := lIdx })
    (hBits : bits < scalarModulus (dst.sizeBytes pw)) :
    dst.isValidBits pw bits = true := by
  cases dst with
  | int w => exact (ScalarTy.isValidBits_iff_validBits pw (.int w) bits).mpr ⟨hBits, trivial⟩
  | uint w => exact (ScalarTy.isValidBits_iff_validBits pw (.uint w) bits).mpr ⟨hBits, trivial⟩
  | rawPtr => exact (ScalarTy.isValidBits_iff_validBits pw .rawPtr bits).mpr ⟨hBits, trivial⟩
  | bool => exact False.elim (bool_not_isFromBytes layouts lIdx hFrom)
  | char => exact False.elim (char_not_isFromBytes layouts lIdx hFrom)
  | refPtr => exact False.elim (ref_not_isFromBytes layouts m pointee lIdx hFrom)

/-- On page 0 (`allocId = 0` and `offsetBytes < 65536`), `addressToPtr p.offsetBytes = p`. -/
theorem addressToPtr_eq_of_lt_pageOffsetModulus
    (p : ProvenancePtr)
    (hAlloc : p.allocId = 0)
    (hLt : p.offsetBytes < 65536) :
    addressToPtr p.offsetBytes = p := by
  rcases p with ⟨allocId, offsetBytes⟩
  dsimp only at hAlloc hLt
  subst hAlloc
  unfold addressToPtr pageOffsetModulus
  dsimp only
  have hDiv : Nat.div offsetBytes 65536 = 0 := Nat.div_eq_of_lt hLt
  have hMod : Nat.mod offsetBytes 65536 = offsetBytes := Nat.mod_eq_of_lt hLt
  rw [hDiv, hMod]

/--
`Trusted` refinement half of `evalTransmuteSameSize_ok_of_into_from_bytes`: on
64-bit targets with thin pointees, for every well-typed source value (including
provenance-bearing pointers and page-0 provenance-free pointers with
`p.offsetBytes < 65536`, where `addressToPtr p.offsetBytes = p`) and every
same-sized `IsFromBytes` destination, `Trusted.MirSemantics.evalByteCast`
computes exactly the `Trusted` image of Anneal's `evalTransmuteSameSize`.
The bound on provenance-free pointers is necessary: `Trusted.Value` represents
them through the 64 KiB page model (`addressToPtr`), so beyond page `0` a
`Ptr -> Int` transmute returns the in-page offset instead of the full address
(`trusted_evalByteCast_provFree_ptr_to_int_page_divergence`).
-/
theorem evalTransmuteSameSize_into_from_bytes_trusted_agreement
    (policy : TransmutePolicy) (layouts : LayoutTable) (m1 m2 : Mutability) (pt1 pt2 : RigidTy)
    (src dst : ScalarTy) (srcLIdx dstLIdx : LayoutIdx) (val : CastVal)
    (exposed : ExposedProvenance)
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl)
    (hFrom : IsFromBytes layouts { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx })
    (hSz : src.sizeBytes .bits64 = dst.sizeBytes .bits64)
    (hPol : src.isPtr = true → dst.isPtr = false → policy = .allowPtrToIntStripProvenance)
    (hWt : CastVal.WellTyped .bits64 src val)
    (hProvVal : ∀ p, val = .ptr p none → p.offsetBytes < 65536)
    (hThin1 : isThinPointee pt1 = true) (hThin2 : isThinPointee pt2 = true)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (val.toTrustedValue .bits64 src) locals')
    (hTy : operandTy localDecls layouts op =
      some { kind := src.toTrustedRigidTy m1 pt1, layoutIdx := srcLIdx }) :
    evalByteCast locals op { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx }
        mem localDecls layouts =
      CastOutcome.toTrustedResult .bits64 dst locals' mem
        (evalTransmuteSameSize .bits64 policy src dst val exposed) := by
  cases val with
  | scalar bits =>
    rcases hWt with ⟨hSrcNp, hSrcValid⟩
    cases hDstPtr : dst.isPtr
    · exact trusted_evalByteCast_scalar_transmute_correspondence policy src dst m1 m2 pt1 pt2 bits
        exposed locals locals' op mem localDecls layouts srcLIdx dstLIdx hSrcNp hDstPtr hSrcValid
        hOp hTy
    · have hSz8 : src.sizeBytes .bits64 = 8 := by
        rw [hSz, ScalarTy.sizeBytes_of_isPtr .bits64 dst hDstPtr]
      have hInt : src.isIntegral = true := by
        cases src with
        | int _ | uint _ => rfl
        | bool | char => exact absurd hSz8 (by decide)
        | rawPtr | refPtr => exact absurd hSrcNp (by decide)
      have hBits8 : bits < scalarModulus 8 := hSz8 ▸ hSrcValid.1
      exact trusted_evalByteCast_int_to_thin_ptr_transmute_correspondence policy src dst m1 m2 pt1
        pt2 bits exposed locals locals' op mem localDecls layouts srcLIdx dstLIdx hInt hSz8 hDstPtr
        hThin2 hBits8 hOp hTy
  | ptr p prov =>
    rcases hWt with ⟨hSrcPtr, hSrcValid, hProv⟩
    rcases hProv with rfl | ⟨rfl, hZeroAlloc⟩
    · have hOp' : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
          .ok (.ptr p 8) locals' := hOp
      cases hDstPtr : dst.isPtr
      · have hPolicy := hPol hSrcPtr hDstPtr
        subst hPolicy
        have hDstInt : dst.isIntegral = true :=
          (scalarTy_isFromBytes_iff_of_not_isPtr layouts m2 pt2 dst dstLIdx hDstPtr).mp hFrom
        have hSz8 : dst.sizeBytes .bits64 = 8 := by
          rw [← hSz, ScalarTy.sizeBytes_of_isPtr .bits64 src hSrcPtr]
        exact (trusted_evalByteCast_thin_ptr_to_int_transmute_correspondence src dst m1 m2 pt1 pt2 p
          exposed locals locals' op mem localDecls layouts srcLIdx dstLIdx hSrcPtr hThin1 hDstInt
          hSz8 hSrcValid hOp' hTy).2.2.2
      · have hDstValid : dst.validBits .bits64 p.offsetBytes := by
          have hB : p.offsetBytes < scalarModulus (dst.sizeBytes .bits64) := hSz ▸ hSrcValid.1
          exact (ScalarTy.isValidBits_iff_validBits .bits64 dst p.offsetBytes).mp
            (scalarTy_isValidBits_of_isFromBytes layouts m2 pt2 dst dstLIdx .bits64 p.offsetBytes
              hFrom hB)
        exact (trusted_evalByteCast_thin_ptr_transmute_correspondence policy src dst m1 m2 pt1 pt2 p
          exposed locals locals' op mem localDecls layouts srcLIdx dstLIdx hSrcPtr hDstPtr hThin1
          hThin2 hSrcValid hDstValid hOp' hTy).2.2
    · have hLt65536 := hProvVal p rfl
      have hAddrEq : addressToPtr p.offsetBytes = p :=
        addressToPtr_eq_of_lt_pageOffsetModulus p hZeroAlloc hLt65536
      have hOp' : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
          .ok (.ptr p 8) locals' := by
        change evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
          .ok (.ptr (addressToPtr p.offsetBytes) 8) locals' at hOp
        rw [hAddrEq] at hOp
        exact hOp
      have hB : p.offsetBytes < scalarModulus (dst.sizeBytes .bits64) := hSz ▸ hSrcValid.1
      have hDstValidB : dst.isValidBits .bits64 p.offsetBytes = true :=
        scalarTy_isValidBits_of_isFromBytes layouts m2 pt2 dst dstLIdx .bits64 p.offsetBytes hFrom hB
      have hDstValid : dst.validBits .bits64 p.offsetBytes :=
        (ScalarTy.isValidBits_iff_validBits .bits64 dst p.offsetBytes).mp hDstValidB
      cases hDstPtr : dst.isPtr
      · have hPolicy := hPol hSrcPtr hDstPtr
        subst hPolicy
        have hDstInt : dst.isIntegral = true :=
          (scalarTy_isFromBytes_iff_of_not_isPtr layouts m2 pt2 dst dstLIdx hDstPtr).mp hFrom
        have hSz8 : dst.sizeBytes .bits64 = 8 := by
          rw [← hSz, ScalarTy.sizeBytes_of_isPtr .bits64 src hSrcPtr]
        have hTrusted := (trusted_evalByteCast_thin_ptr_to_int_transmute_correspondence src dst m1 m2
          pt1 pt2 p exposed locals locals' op mem localDecls layouts srcLIdx dstLIdx hSrcPtr hThin1
          hDstInt hSz8 hSrcValid hOp' hTy).2.2.1
        rw [hTrusted,
            evalTransmuteSameSize_ptr_to_nonPtr_allow_eq .bits64 src dst p none exposed hSrcPtr hDstPtr
              hSz hSrcValid,
            hDstValidB]
        show ok (.scalar ⟨p.offsetBytes, 8⟩) locals' mem =
          ok (.scalar ⟨p.offsetBytes, dst.sizeBytes .bits64⟩) locals' mem
        rw [hSz8]
      · have hTrusted := (trusted_evalByteCast_thin_ptr_transmute_correspondence policy src dst m1 m2
          pt1 pt2 p exposed locals locals' op mem localDecls layouts srcLIdx dstLIdx hSrcPtr hDstPtr
          hThin1 hThin2 hSrcValid hDstValid hOp' hTy).2.1
        rw [hTrusted,
            evalTransmuteSameSize_ptr_to_ptr_none .bits64 policy src dst p exposed hSrcPtr hDstPtr
              hSrcValid,
            hDstValidB]
        show ok (.ptr p 8) locals' mem = ok (.ptr (addressToPtr p.offsetBytes) 8) locals' mem
        rw [hAddrEq]

/--
**Divergence (provenance-free pointers beyond page `0`).** `CastVal.toTrustedValue`
maps the provenance-free pointer `.ptr ⟨0, 65536⟩ none` to `Trusted`'s page-model
pointer `.ptr (addressToPtr 65536) 8 = .ptr ⟨1, 0⟩ 8`. Anneal's opt-in `Ptr -> Int`
transmute returns the full address `65536`, whereas `Trusted.MirSemantics.evalByteCast`
on that image returns the in-page offset `0`. So the page-`0` bound in
`evalTransmuteSameSize_into_from_bytes_trusted_agreement` cannot be dropped.
-/
theorem trusted_evalByteCast_provFree_ptr_to_int_page_divergence
    (dst : ScalarTy) (m1 m2 : Mutability) (pt1 pt2 : RigidTy)
    (exposed : ExposedProvenance)
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcLIdx dstLIdx : Nat)
    (h_thin1 : isThinPointee pt1 = true)
    (h_int : dst.isIntegral = true) (h_sz : dst.sizeBytes .bits64 = 8)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok ((CastVal.ptr { allocId := 0, offsetBytes := 65536 } none).toTrustedValue .bits64
        .rawPtr) locals')
    (h_ty : operandTy localDecls layouts op =
      some { kind := .rawPtr m1 pt1, layoutIdx := srcLIdx }) :
    CastVal.WellTyped .bits64 .rawPtr (.ptr { allocId := 0, offsetBytes := 65536 } none) ∧
    evalTransmuteSameSize .bits64 .allowPtrToIntStripProvenance .rawPtr dst
        (.ptr { allocId := 0, offsetBytes := 65536 } none) exposed =
      .ok (.scalar 65536) exposed ∧
    evalByteCast locals op { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx }
        mem localDecls layouts = ok (.scalar ⟨0, 8⟩) locals' mem ∧
    evalByteCast locals op { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx }
        mem localDecls layouts ≠
      CastOutcome.toTrustedResult .bits64 dst locals' mem
        (evalTransmuteSameSize .bits64 .allowPtrToIntStripProvenance .rawPtr dst
          (.ptr { allocId := 0, offsetBytes := 65536 } none) exposed) := by
  have hValid : ScalarTy.rawPtr.validBits .bits64 65536 := ⟨by decide, trivial⟩
  have hWt : CastVal.WellTyped .bits64 .rawPtr (.ptr { allocId := 0, offsetBytes := 65536 } none) :=
    ⟨rfl, hValid, Or.inr ⟨rfl, rfl⟩⟩
  have hDstNp := ScalarTy.isPtr_eq_false_of_isIntegral dst h_int
  have hSzEq : ScalarTy.rawPtr.sizeBytes .bits64 = dst.sizeBytes .bits64 := by rw [h_sz]
  have hDstValid : dst.isValidBits .bits64 65536 = true :=
    ScalarTy.isValidBits_of_isIntegral .bits64 dst 65536 h_int (by rw [h_sz]; decide)
  have hAnneal : evalTransmuteSameSize .bits64 .allowPtrToIntStripProvenance .rawPtr dst
      (.ptr { allocId := 0, offsetBytes := 65536 } none) exposed = .ok (.scalar 65536) exposed := by
    rw [evalTransmuteSameSize_ptr_to_nonPtr_allow_eq .bits64 .rawPtr dst _ none exposed rfl hDstNp
      hSzEq hValid, hDstValid]
  have hOp' : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.ptr { allocId := 1, offsetBytes := 0 } 8) locals' := h_op
  have hTrusted := (trusted_evalByteCast_thin_ptr_to_int_transmute_correspondence .rawPtr dst m1 m2
    pt1 pt2 { allocId := 1, offsetBytes := 0 } exposed locals locals' op mem localDecls layouts
    srcLIdx dstLIdx rfl h_thin1 h_int h_sz ⟨by decide, trivial⟩ hOp' h_ty).2.2.1
  refine ⟨hWt, hAnneal, hTrusted, ?_⟩
  rw [hTrusted, hAnneal]
  intro h
  injection h with h1
  injection h1 with h2
  injection h2 with h3
  exact absurd h3 (by decide)

/--
**`evalTransmuteSameSize_ok_of_into_from_bytes`**:
If `src` and `dst` have matching byte sizes (`src.sizeBytes pw = dst.sizeBytes pw`),
`src` satisfies `IsIntoBytes`, and `dst` satisfies `IsFromBytes`, then for every
well-typed `val : CastVal` (under `policy = .allowPtrToIntStripProvenance` when
`src.isPtr = true ∧ dst.isPtr = false`):
1. `evalTransmuteSameSize` succeeds with `.ok outVal exposed` where
   `CastVal.WellTyped pw dst outVal`;
2. when `src.isPtr = false ∧ dst.isPtr = false` and `val = .scalar bits`, the result is
   `.ok (.scalar bits) exposed`;
3. on 64-bit targets with thin pointees, whenever the operand evaluates to the `Trusted`
   image `val.toTrustedValue .bits64 src` (with `p.offsetBytes < 65536` when `val = .ptr p none`),
   `Trusted.MirSemantics.evalByteCast` succeeds with exactly the `Trusted` image of the same
   `outVal` (no undefined behavior), see
   `evalTransmuteSameSize_into_from_bytes_trusted_agreement`.

The `IsIntoBytes` hypothesis mirrors the `zerocopy::transmute!` interface. It holds for every
`ScalarTy` image (`scalarTy_isIntoBytes`), so the conclusions depend only on the `IsFromBytes`
destination.
-/
theorem evalTransmuteSameSize_ok_of_into_from_bytes
    (pw : PtrWidth) (policy : TransmutePolicy)
    (layouts : LayoutTable) (m1 m2 : Mutability) (pt1 pt2 : RigidTy)
    (src dst : ScalarTy) (srcLIdx dstLIdx : LayoutIdx)
    (val : CastVal) (exposed : ExposedProvenance)
    (_hInto : IsIntoBytes layouts { kind := src.toTrustedRigidTy m1 pt1, layoutIdx := srcLIdx })
    (hFrom : IsFromBytes layouts { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx })
    (hSz : src.sizeBytes pw = dst.sizeBytes pw)
    (hPol : src.isPtr = true → dst.isPtr = false → policy = .allowPtrToIntStripProvenance)
    (hWt : CastVal.WellTyped pw src val) :
    (∃ outVal,
      evalTransmuteSameSize pw policy src dst val exposed = .ok outVal exposed ∧
      CastVal.WellTyped pw dst outVal) ∧
    (∀ bits,
      src.isPtr = false →
      dst.isPtr = false →
      val = .scalar bits →
      evalTransmuteSameSize pw policy src dst (.scalar bits) exposed =
        .ok (.scalar bits) exposed) ∧
    (pw = .bits64 → isThinPointee pt1 = true → isThinPointee pt2 = true →
      (∀ p, val = .ptr p none → p.offsetBytes < 65536) →
      ∀ (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
        (localDecls : List LocalDecl),
        evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
          .ok (val.toTrustedValue .bits64 src) locals' →
        operandTy localDecls layouts op =
          some { kind := src.toTrustedRigidTy m1 pt1, layoutIdx := srcLIdx } →
        ∃ outVal,
          evalTransmuteSameSize .bits64 policy src dst val exposed = .ok outVal exposed ∧
          evalByteCast locals op { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx }
              mem localDecls layouts =
            ok (outVal.toTrustedValue .bits64 dst) locals' mem) := by
  have h1 : ∃ outVal,
      evalTransmuteSameSize pw policy src dst val exposed = .ok outVal exposed ∧
      CastVal.WellTyped pw dst outVal := by
      cases val with
      | scalar bits =>
        rcases hWt with ⟨hSrcNp, hSrcValid⟩
        have hBitsDst : bits < scalarModulus (dst.sizeBytes pw) := hSz ▸ hSrcValid.1
        have hDstValidB : dst.isValidBits pw bits = true :=
          scalarTy_isValidBits_of_isFromBytes layouts m2 pt2 dst dstLIdx pw bits hFrom hBitsDst
        have hDstValid : dst.validBits pw bits :=
          (ScalarTy.isValidBits_iff_validBits pw dst bits).mp hDstValidB
        cases hDstPtr : dst.isPtr
        · refine ⟨.scalar bits, ?_, ⟨hDstPtr, hDstValid⟩⟩
          rw [evalTransmuteSameSize_nonPtr_scalar_eq pw policy src dst bits exposed hSrcNp hDstPtr hSz hSrcValid,
              hDstValidB]
        · refine ⟨.ptr { allocId := 0, offsetBytes := bits } none, ?_, ⟨hDstPtr, hDstValid, Or.inr ⟨rfl, rfl⟩⟩⟩
          rw [evalTransmuteSameSize_int_to_ptr_eq pw policy src dst bits exposed hSrcNp hDstPtr hSz hSrcValid,
              hDstValidB]
      | ptr p prov =>
        rcases hWt with ⟨hSrcPtr, hSrcValid, hProv⟩
        have hBitsDst : p.offsetBytes < scalarModulus (dst.sizeBytes pw) := hSz ▸ hSrcValid.1
        have hDstValidB : dst.isValidBits pw p.offsetBytes = true :=
          scalarTy_isValidBits_of_isFromBytes layouts m2 pt2 dst dstLIdx pw p.offsetBytes hFrom hBitsDst
        have hDstValid : dst.validBits pw p.offsetBytes :=
          (ScalarTy.isValidBits_iff_validBits pw dst p.offsetBytes).mp hDstValidB
        cases hDstPtr : dst.isPtr
        · have hPolicy := hPol hSrcPtr hDstPtr
          subst hPolicy
          refine ⟨.scalar p.offsetBytes, ?_, ⟨hDstPtr, hDstValid⟩⟩
          rw [evalTransmuteSameSize_ptr_to_nonPtr_allow_eq pw src dst p prov exposed hSrcPtr hDstPtr hSz hSrcValid,
              hDstValidB]
        · rcases hProv with rfl | ⟨rfl, hZeroAlloc⟩
          · refine ⟨.ptr p (some p.allocId), ?_, ⟨hDstPtr, hDstValid, Or.inl rfl⟩⟩
            rw [evalTransmuteSameSize_ptr_to_ptr_some pw policy src dst p exposed hSrcPtr hDstPtr hSrcValid,
                hDstValidB]
          · refine ⟨.ptr { allocId := 0, offsetBytes := p.offsetBytes } none, ?_,
              ⟨hDstPtr, hDstValid, Or.inr ⟨rfl, rfl⟩⟩⟩
            rw [evalTransmuteSameSize_ptr_to_ptr_none pw policy src dst p exposed hSrcPtr hDstPtr hSrcValid,
                hDstValidB]
  have h2 : ∀ bits,
      src.isPtr = false →
      dst.isPtr = false →
      val = .scalar bits →
      evalTransmuteSameSize pw policy src dst (.scalar bits) exposed =
        .ok (.scalar bits) exposed := by
      intro bits hSrcNp hDstNp hValEq
      subst hValEq
      rcases hWt with ⟨_, hSrcValid⟩
      have hBitsDst : bits < scalarModulus (dst.sizeBytes pw) := hSz ▸ hSrcValid.1
      have hDstValidB : dst.isValidBits pw bits = true :=
        scalarTy_isValidBits_of_isFromBytes layouts m2 pt2 dst dstLIdx pw bits hFrom hBitsDst
      rw [evalTransmuteSameSize_nonPtr_scalar_eq pw policy src dst bits exposed hSrcNp hDstNp hSz hSrcValid,
          hDstValidB]
  refine ⟨h1, h2, ?_⟩
  intro hPw hThin1 hThin2 hProvVal locals locals' op mem localDecls hOp hTy
  subst hPw
  rcases h1 with ⟨outVal, hEq, _⟩
  refine ⟨outVal, hEq, ?_⟩
  rw [evalTransmuteSameSize_into_from_bytes_trusted_agreement policy layouts m1 m2 pt1 pt2 src dst
    srcLIdx dstLIdx val exposed locals locals' op mem localDecls hFrom hSz hPol hWt hProvVal hThin1
    hThin2 hOp hTy, hEq]
  rfl

/--
**`evalTransmuteSameSize_ok_of_checkIntoFromBytes`**:
Decidable-certificate corollary of `evalTransmuteSameSize_ok_of_into_from_bytes`:
whenever `checkIntoBytes` holds for `src` and `checkFromBytes` holds for `dst` with
`src.sizeBytes pw = dst.sizeBytes pw`, transmuting any valid scalar `bits` of type `src`
always succeeds with `.ok (.scalar bits) exposed` under every `TransmutePolicy`, and
on 64-bit targets `Trusted.MirSemantics.evalByteCast` evaluates to
`ok (.scalar ⟨bits, dst.sizeBytes .bits64⟩) locals' mem`.
-/
theorem evalTransmuteSameSize_ok_of_checkIntoFromBytes
    (pw : PtrWidth) (policy : TransmutePolicy)
    (layouts : LayoutTable) (m1 m2 : Mutability) (pt1 pt2 : RigidTy)
    (src dst : ScalarTy) (srcLIdx dstLIdx : LayoutIdx)
    (bits : Nat) (exposed : ExposedProvenance)
    (hCheckInto : checkIntoBytes layouts { kind := src.toTrustedRigidTy m1 pt1, layoutIdx := srcLIdx } = true)
    (hCheckFrom : checkFromBytes layouts { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx } = true)
    (hSz : src.sizeBytes pw = dst.sizeBytes pw)
    (hValid : src.validBits pw bits) :
    evalTransmuteSameSize pw policy src dst (.scalar bits) exposed =
      .ok (.scalar bits) exposed ∧
    CastVal.WellTyped pw dst (.scalar bits) ∧
    (pw = .bits64 →
      ∀ (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
        (localDecls : List LocalDecl),
        evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
          .ok (.scalar ⟨bits, src.sizeBytes .bits64⟩) locals' →
        operandTy localDecls layouts op =
          some { kind := src.toTrustedRigidTy m1 pt1, layoutIdx := srcLIdx } →
        evalByteCast locals op { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx }
            mem localDecls layouts =
          ok (.scalar ⟨bits, dst.sizeBytes .bits64⟩) locals' mem) := by
  have hSrcNp : src.isPtr = false :=
    (scalarTy_checkIntoBytes_iff_not_isPtr layouts m1 pt1 src srcLIdx).mp hCheckInto
  have hDstInt : dst.isIntegral = true :=
    (scalarTy_checkFromBytes_iff_isIntegral layouts m2 pt2 dst dstLIdx).mp hCheckFrom
  have hDstNp : dst.isPtr = false := ScalarTy.isPtr_eq_false_of_isIntegral dst hDstInt
  have hInto := checkIntoBytes_sound layouts _ hCheckInto
  have hFrom := checkFromBytes_sound layouts _ hCheckFrom
  have hMain := evalTransmuteSameSize_ok_of_into_from_bytes pw policy layouts m1 m2 pt1 pt2
    src dst srcLIdx dstLIdx (.scalar bits) exposed hInto hFrom hSz
    (fun hPtr _ => by rw [hSrcNp] at hPtr; contradiction)
    ⟨hSrcNp, hValid⟩
  have hEq := hMain.2.1 bits hSrcNp hDstNp rfl
  rcases hMain.1 with ⟨outVal, hOutEq, hOutWt⟩
  rw [hEq] at hOutEq
  injection hOutEq with hValEq _
  subst hValEq
  refine ⟨hEq, hOutWt, ?_⟩
  intro hPw locals locals' op mem localDecls hOp hTy
  subst hPw
  rw [trusted_evalByteCast_scalar_transmute_correspondence policy src dst m1 m2 pt1 pt2 bits exposed
    locals locals' op mem localDecls layouts srcLIdx dstLIdx hSrcNp hDstNp hValid hOp hTy, hEq]
  rfl

/--
**`evalByteCast_ok_of_into_from_bytes`**:
General `Ty`-level soundness of `Trusted.MirSemantics.evalByteCast` (`Rvalue.cast .transmute`)
for arbitrary types (including scalars, homogeneous arrays `[T; N]`, and contiguous structs):
if `srcTy` satisfies `IsIntoBytes layouts srcTy`, `dstTy` satisfies `IsFromBytes layouts dstTy`,
and `rigidTyByteSize layouts srcTy = rigidTyByteSize layouts dstTy`, then whenever `op` evaluates
to a value `v` of type `srcTy` that encodes to `some bs`, `evalByteCast` and `evalRvalue (.cast .transmute op dstTy)`
succeed without undefined behavior (`ok v' locals' mem`).
-/
theorem evalByteCast_ok_of_into_from_bytes
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcTy dstTy : Ty) (v : Value) (bs : List AbstractByte)
    (hInto : IsIntoBytes layouts srcTy)
    (hFrom : IsFromBytes layouts dstTy)
    (hSizeEq : rigidTyByteSize layouts srcTy = rigidTyByteSize layouts dstTy)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals = .ok v locals')
    (hTy : operandTy localDecls layouts op = some srcTy)
    (hEnc : encodeValueToBytes defaultCodecFuel layouts srcTy v = some bs) :
    ∃ v',
      decodeValueFromBytes defaultCodecFuel layouts dstTy bs = some v' ∧
      evalByteCast locals op dstTy mem localDecls layouts = ok v' locals' mem ∧
      evalRvalue locals (.cast .transmute op dstTy) mem localDecls layouts = ok v' locals' mem := by
  rcases transmute_sound_of_into_from_bytes layouts srcTy dstTy hInto hFrom hSizeEq v bs hEnc
    with ⟨v', hDec⟩
  rcases hInto with ⟨szSrc, hSzSrc, hEncProps⟩
  rcases hFrom with ⟨szDst, hSzDst, _⟩
  have hSzEq : szSrc = szDst := by
    rw [hSzSrc, hSzDst] at hSizeEq
    exact Option.some.inj hSizeEq
  subst hSzEq
  have ⟨hLen, _⟩ := hEncProps v bs hEnc
  have hBeqSz : Nat.beq szSrc szSrc = true := Nat.beq_refl _
  have hBeqLen : Nat.beq (Trusted.Sequence.length bs) szSrc = true := by
    rw [hLen]; exact Nat.beq_refl _
  have hBc : evalByteCast locals op dstTy mem localDecls layouts = ok v' locals' mem := by
    rw [trusted_evalByteCast_eq locals locals' op mem localDecls layouts v srcTy dstTy szSrc szSrc
        hOp hSzDst hTy hSzSrc,
      hBeqSz, hEnc]
    dsimp only
    rw [hBeqLen, hDec]
  exact ⟨v', hDec, hBc, hBc⟩

/--
**`evalByteCast_ok_of_checkIntoFromBytes`**:
Decidable-certificate corollary of `evalByteCast_ok_of_into_from_bytes` discharging
`Trusted.MirSemantics.evalByteCast` directly from `checkIntoBytes layouts srcTy = true`
and `checkFromBytes layouts dstTy = true`.
-/
theorem evalByteCast_ok_of_checkIntoFromBytes
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcTy dstTy : Ty) (v : Value) (bs : List AbstractByte)
    (hCheckInto : checkIntoBytes layouts srcTy = true)
    (hCheckFrom : checkFromBytes layouts dstTy = true)
    (hSizeEq : rigidTyByteSize layouts srcTy = rigidTyByteSize layouts dstTy)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals = .ok v locals')
    (hTy : operandTy localDecls layouts op = some srcTy)
    (hEnc : encodeValueToBytes defaultCodecFuel layouts srcTy v = some bs) :
    ∃ v',
      decodeValueFromBytes defaultCodecFuel layouts dstTy bs = some v' ∧
      evalByteCast locals op dstTy mem localDecls layouts = ok v' locals' mem ∧
      evalRvalue locals (.cast .transmute op dstTy) mem localDecls layouts = ok v' locals' mem :=
  evalByteCast_ok_of_into_from_bytes locals locals' op mem localDecls layouts srcTy dstTy v bs
    (checkIntoBytes_sound layouts srcTy hCheckInto)
    (checkFromBytes_sound layouts dstTy hCheckFrom)
    hSizeEq hOp hTy hEnc

/-! ### 8.4 `IsTryFromBytes` & Candidate Validation (`try_transmute` Bridge) -/

/--
**`tryTransmute_valid_iff_decodeCastVal_some`**:
Whenever `src` and `dst` have equal byte widths (`src.sizeBytes pw = dst.sizeBytes pw`),
`encodeCastVal pw src val = some cBytes`, and `policy` permits `Ptr -> Int` when
`src.isPtr = true ∧ dst.isPtr = false`:
1. `evalTransmuteSameSize pw policy src dst val exposed` reduces directly to matching on `decodeCastVal pw dst cBytes`.
2. `evalTransmuteSameSize` succeeds (`.ok outVal exposed`) iff `decodeCastVal pw dst cBytes = some outVal`.
3. `evalTransmuteSameSize` returns `.ub` iff `decodeCastVal pw dst cBytes = none`.
-/
theorem tryTransmute_valid_iff_decodeCastVal_some
    (pw : PtrWidth) (policy : TransmutePolicy)
    (src dst : ScalarTy) (val : CastVal) (cBytes : List CastByte)
    (exposed : ExposedProvenance)
    (hSz : src.sizeBytes pw = dst.sizeBytes pw)
    (hPol : src.isPtr = true → dst.isPtr = false → policy = .allowPtrToIntStripProvenance)
    (hEnc : encodeCastVal pw src val = some cBytes) :
    evalTransmuteSameSize pw policy src dst val exposed =
      (match decodeCastVal pw dst cBytes with
       | some outVal => .ok outVal exposed
       | none => .ub) ∧
    (∀ outVal,
      evalTransmuteSameSize pw policy src dst val exposed = .ok outVal exposed ↔
        decodeCastVal pw dst cBytes = some outVal) ∧
    (evalTransmuteSameSize pw policy src dst val exposed = .ub ↔
      decodeCastVal pw dst cBytes = none) := by
  have hBeqSz : Nat.beq (src.sizeBytes pw) (dst.sizeBytes pw) = true := by
    rw [hSz]; exact Nat.beq_refl _
  have hRed :
      evalTransmuteSameSize pw policy src dst val exposed =
        (match decodeCastVal pw dst cBytes with
         | some outVal => .ok outVal exposed
         | none => .ub) := by
    unfold evalTransmuteSameSize
    rw [hBeqSz]
    dsimp only
    cases hSrcPtr : src.isPtr <;> cases hDstPtr : dst.isPtr
    · cases val with
      | ptr _ _ => unfold encodeCastVal at hEnc; rw [hSrcPtr] at hEnc; nomatch hEnc
      | scalar bits =>
        dsimp only [Bool.and, Bool.not]
        rw [hEnc]
    · cases val with
      | ptr _ _ => unfold encodeCastVal at hEnc; rw [hSrcPtr] at hEnc; nomatch hEnc
      | scalar bits =>
        dsimp only [Bool.and, Bool.not]
        rw [hEnc]
    · have hAllow := hPol hSrcPtr hDstPtr
      subst hAllow
      cases val with
      | scalar _ => unfold encodeCastVal at hEnc; rw [hSrcPtr] at hEnc; nomatch hEnc
      | ptr p prov =>
        dsimp only [Bool.and, Bool.not]
        rw [hEnc]
    · cases val with
      | scalar _ => unfold encodeCastVal at hEnc; rw [hSrcPtr] at hEnc; nomatch hEnc
      | ptr p prov =>
        dsimp only [Bool.and, Bool.not]
        rw [hEnc]
  refine ⟨hRed, ?_, ?_⟩
  · intro outVal
    rw [hRed]
    cases decodeCastVal pw dst cBytes <;> simp
  · rw [hRed]
    cases decodeCastVal pw dst cBytes <;> simp

/--
**`tryTransmute_valid_iff_isValidBits`**:
For any non-pointer source `src` (`src.isPtr = false`) and destination `dst` of equal
byte width (`src.sizeBytes pw = dst.sizeBytes pw`) on a valid source bit pattern
`src.validBits pw bits`:
1. `evalTransmuteSameSize` succeeds iff `dst.isValidBits pw bits = true`.
2. `decodeCastVal pw dst (encodeCastBytes bits (src.sizeBytes pw) none)` succeeds iff `dst.isValidBits pw bits = true`.
3. `evalTransmuteSameSize` faults with `.ub` iff `dst.isValidBits pw bits = false`.
4. On 64-bit targets (`pw = .bits64`) when `dst.isPtr = false`, `decodeValueFromBytes` on `encodeLittleEndianBytes bits (src.sizeBytes .bits64) none` succeeds iff `dst.isValidBits .bits64 bits = true`.
5. On 64-bit targets when `dst` is a pointer descriptor with a thin pointee, the same `decodeValueFromBytes` candidate validation holds (`refPtr` rejects only the null address, `rawPtr` accepts every candidate).
-/
theorem tryTransmute_valid_iff_isValidBits
    (pw : PtrWidth) (policy : TransmutePolicy)
    (layouts : LayoutTable) (m2 : Mutability) (pt2 : RigidTy) (dstLIdx : LayoutIdx)
    (src dst : ScalarTy) (bits : Nat) (exposed : ExposedProvenance)
    (hSrcNp : src.isPtr = false)
    (hSz : src.sizeBytes pw = dst.sizeBytes pw)
    (hValid : src.validBits pw bits) :
    ((∃ outVal, evalTransmuteSameSize pw policy src dst (.scalar bits) exposed = .ok outVal exposed) ↔
      dst.isValidBits pw bits = true) ∧
    ((∃ outVal, decodeCastVal pw dst (encodeCastBytes bits (src.sizeBytes pw) none) = some outVal) ↔
      dst.isValidBits pw bits = true) ∧
    (evalTransmuteSameSize pw policy src dst (.scalar bits) exposed = .ub ↔
      dst.isValidBits pw bits = false) ∧
    (pw = .bits64 → dst.isPtr = false →
      ((∃ v',
          decodeValueFromBytes defaultCodecFuel layouts
            { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx }
            (encodeLittleEndianBytes bits (src.sizeBytes .bits64) none) = some v') ↔
        dst.isValidBits .bits64 bits = true)) ∧
    (pw = .bits64 → dst.isPtr = true → isThinPointee pt2 = true →
      ((∃ v',
          decodeValueFromBytes defaultCodecFuel layouts
            { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx }
            (encodeLittleEndianBytes bits (src.sizeBytes .bits64) none) = some v') ↔
        dst.isValidBits .bits64 bits = true)) := by
  have hSrcValidB : src.isValidBits pw bits = true :=
    (ScalarTy.isValidBits_iff_validBits pw src bits).mpr hValid
  have hEnc :
      encodeCastVal pw src (.scalar bits) =
        some (encodeCastBytes bits (src.sizeBytes pw) none) := by
    unfold encodeCastVal
    rw [hSrcNp]
    dsimp only
    rw [hSrcValidB]
  have hDecCast :
      decodeCastVal pw dst (encodeCastBytes bits (src.sizeBytes pw) none) =
        match dst.isValidBits pw bits with
        | false => none
        | true =>
          some (if dst.isPtr then decodeCastPtrBytes (encodeCastBytes bits (src.sizeBytes pw) none)
                else .scalar bits) := by
    unfold decodeCastVal
    dsimp only
    rw [decodeCastIntBytes_encodeCastBytes (src.sizeBytes pw) bits none hValid.1]
    cases dst.isPtr <;> cases dst.isValidBits pw bits <;> rfl
  have ⟨hRed, _, hUbIff⟩ :=
    tryTransmute_valid_iff_decodeCastVal_some pw policy src dst (.scalar bits)
      (encodeCastBytes bits (src.sizeBytes pw) none) exposed hSz
      (fun hPtr _ => by rw [hSrcNp] at hPtr; contradiction) hEnc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hRed, hDecCast]
    cases dst.isValidBits pw bits <;> simp
  · rw [hDecCast]
    cases dst.isValidBits pw bits <;> simp
  · rw [hUbIff, hDecCast]
    cases dst.isValidBits pw bits <;> simp
  · intro hPw hDstNp
    subst hPw
    have hBitsDst : bits < scalarModulus (dst.sizeBytes .bits64) := hSz ▸ hValid.1
    rw [hSz, show defaultCodecFuel = 15 + 1 from rfl,
        trusted_decodeValueFromBytes_scalar 15 layouts m2 pt2 dst dstLIdx bits hDstNp hBitsDst]
    cases dst.isValidBits .bits64 bits <;> simp
  · intro hPw hDstPtr hThin2
    subst hPw
    have hSz8 : src.sizeBytes .bits64 = 8 := by
      rw [hSz, ScalarTy.sizeBytes_of_isPtr .bits64 dst hDstPtr]
    have hBits8 : bits < scalarModulus 8 := hSz8 ▸ hValid.1
    rw [hSz8, show defaultCodecFuel = 15 + 1 from rfl,
      trusted_decodeValueFromBytes_thin_ptrTy_no_prov 15 layouts m2 pt2 dst dstLIdx _ bits hDstPtr
        hThin2 hBits8 (trusted_length_encodeLittleEndianBytes bits 8 none)
        (trusted_decodeScalarBytes_encodeLittleEndianBytes 8 bits none false (by decide) hBits8)]
    cases dst.isValidBits .bits64 bits <;> simp

/--
Every non-pointer `dst : ScalarTy` (`bool`, `char`, `int w`, `uint w`) satisfies
`IsTryFromBytes` with validity predicate `dst.validBits .bits64 bits`.
-/
theorem scalarTy_isTryFromBytes_validBits
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (dst : ScalarTy) (lIdx : LayoutIdx)
    (hDstNp : dst.isPtr = false) :
    IsTryFromBytes layouts { kind := dst.toTrustedRigidTy m pointee, layoutIdx := lIdx }
      (fun v => ∃ bits, dst.validBits .bits64 bits ∧ v = .scalar ⟨bits, dst.sizeBytes .bits64⟩) := by
  refine ⟨dst.sizeBytes .bits64,
    ScalarTy.rigidTyByteSize_toTrustedRigidTy_of_not_isPtr layouts m pointee dst lIdx hDstNp, ?_⟩
  intro bs v hDec
  cases dst with
  | bool =>
    rcases bool_isTryFromBytes layouts lIdx with ⟨_, _, hBoolTry⟩
    rcases hBoolTry bs v hDec with ⟨bits, hLe, rfl⟩
    have hLt : bits < scalarModulus (ScalarTy.bool.sizeBytes .bits64) := by
      change bits < 256
      omega
    exact ⟨bits, ⟨hLt, hLe⟩, rfl⟩
  | char =>
    rcases char_isTryFromBytes layouts lIdx with ⟨_, _, hCharTry⟩
    rcases hCharTry bs v hDec with ⟨bits, hChar, rfl⟩
    have hLt : bits < scalarModulus 4 := by
      have hc := (isValidCharCode_iff bits).mp hChar
      change bits < 4294967296
      omega
    exact ⟨bits, ⟨hLt, hChar⟩, rfl⟩
  | int w =>
    unfold defaultCodecFuel decodeValueFromBytes at hDec
    dsimp only [ScalarTy.toTrustedRigidTy] at hDec
    rw [IntWidth.intCastTargetBytes_int w] at hDec
    dsimp only at hDec
    cases hLen : Nat.beq (Trusted.Sequence.length bs) (w.byteSize .bits64) <;> rw [hLen] at hDec
    · nomatch hDec
    · dsimp only at hDec
      cases hSc : decodeScalarBytes bs true <;> rw [hSc] at hDec
      · nomatch hDec
      case some pair =>
        rcases pair with ⟨sv, prov⟩
        injection hDec with hV
        have hBsLen : Trusted.Sequence.length bs = w.byteSize .bits64 := Nat.eq_of_beq_eq_true hLen
        have ⟨hSvSz, hSvLt⟩ := decodeScalarBytes_bits_lt bs true sv prov hSc
        rw [hBsLen] at hSvSz hSvLt
        rcases sv with ⟨bits, sz⟩
        dsimp only at hSvSz hSvLt
        subst hSvSz
        exact ⟨bits, ⟨hSvLt, trivial⟩, hV.symm⟩
  | uint w =>
    unfold defaultCodecFuel decodeValueFromBytes at hDec
    dsimp only [ScalarTy.toTrustedRigidTy] at hDec
    rw [IntWidth.intCastTargetBytes_uint w] at hDec
    dsimp only at hDec
    cases hLen : Nat.beq (Trusted.Sequence.length bs) (w.byteSize .bits64) <;> rw [hLen] at hDec
    · nomatch hDec
    · dsimp only at hDec
      cases hSc : decodeScalarBytes bs false <;> rw [hSc] at hDec
      · nomatch hDec
      case some pair =>
        rcases pair with ⟨sv, prov⟩
        injection hDec with hV
        have hBsLen : Trusted.Sequence.length bs = w.byteSize .bits64 := Nat.eq_of_beq_eq_true hLen
        have ⟨hSvSz, hSvLt⟩ := decodeScalarBytes_bits_lt bs false sv prov hSc
        rw [hBsLen] at hSvSz hSvLt
        rcases sv with ⟨bits, sz⟩
        dsimp only at hSvSz hSvLt
        subst hSvSz
        exact ⟨bits, ⟨hSvLt, trivial⟩, hV.symm⟩
  | rawPtr | refPtr => contradiction

/--
Every thin raw pointer `.rawPtr m pointee` (`isThinPointee pointee = true`) satisfies
`IsTryFromBytes` with the exact value-level image of `Trusted`'s decoder: a thin
pointer value `.ptr p 8` whose offset is below `scalarModulus 8`
(`ScalarTy.rawPtr.validBits .bits64 p.offsetBytes`).
-/
theorem thin_rawPtr_isTryFromBytes
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (lIdx : LayoutIdx) (hThin : isThinPointee pointee = true) :
    IsTryFromBytes layouts { kind := .rawPtr m pointee, layoutIdx := lIdx }
      (fun v => ∃ p : ProvenancePtr, v = .ptr p 8 ∧ p.offsetBytes < scalarModulus 8) := by
  refine ⟨8, trusted_rigidTyByteSize_thin_rawPtr layouts m pointee lIdx hThin, ?_⟩
  intro bs v hDec
  rw [show defaultCodecFuel = 15 + 1 from rfl,
      trusted_decodeValueFromBytes_thin_rawPtr_eq 15 layouts m pointee lIdx bs hThin] at hDec
  cases hLen : Nat.beq (Trusted.Sequence.length bs) 8 <;> rw [hLen] at hDec
  · nomatch hDec
  · dsimp only at hDec
    cases hSc : decodeScalarBytes bs false <;> rw [hSc] at hDec
    · nomatch hDec
    case some pair =>
      rcases pair with ⟨sv, prov⟩
      dsimp only at hDec
      have hBsLen : Trusted.Sequence.length bs = 8 := Nat.eq_of_beq_eq_true hLen
      have ⟨_, hSvLt⟩ := decodeScalarBytes_bits_lt bs false sv prov hSc
      rw [hBsLen] at hSvLt
      cases prov with
      | none =>
        injection hDec with hV
        refine ⟨addressToPtr sv.bits, hV.symm, ?_⟩
        show sv.bits % 65536 < scalarModulus 8
        have hMod : sv.bits % 65536 < 65536 := Nat.mod_lt _ (by decide)
        have h8 : (65536 : Nat) < scalarModulus 8 := by decide
        omega
      | some ap =>
        rcases ap with ⟨allocId, tag⟩
        injection hDec with hV
        exact ⟨{ allocId := allocId, offsetBytes := sv.bits }, hV.symm, hSvLt⟩

/--
Every thin reference `.ref m pointee` (`isThinPointee pointee = true`) satisfies
`IsTryFromBytes` with the exact value-level image of `Trusted`'s decoder: a thin
pointer value `.ptr p 8` whose offset is below `scalarModulus 8`.

The non-null niche of `&T` constrains provenance-free *byte sequences*, not decoded
values: on provenance-free bytes the decoder rejects address `0`
(`trusted_decodeValueFromBytes_thin_ptrTy_no_prov`), but it also accepts
provenance-carrying bytes with offset `0`. So every validity predicate for `&T`
must hold at a null-offset pointer `.ptr ⟨a, 0⟩ 8`
(`thin_refPtr_isTryFromBytes_admits_null_offset`).
-/
theorem thin_refPtr_isTryFromBytes
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (lIdx : LayoutIdx) (hThin : isThinPointee pointee = true) :
    IsTryFromBytes layouts { kind := .ref m pointee, layoutIdx := lIdx }
      (fun v => ∃ p : ProvenancePtr, v = .ptr p 8 ∧ p.offsetBytes < scalarModulus 8) := by
  refine ⟨8, trusted_rigidTyByteSize_thin_ref layouts m pointee lIdx hThin, ?_⟩
  intro bs v hDec
  rw [show defaultCodecFuel = 15 + 1 from rfl,
      trusted_decodeValueFromBytes_thin_ref_eq 15 layouts m pointee lIdx bs hThin] at hDec
  cases hLen : Nat.beq (Trusted.Sequence.length bs) 8 <;> rw [hLen] at hDec
  · nomatch hDec
  · dsimp only at hDec
    cases hSc : decodeScalarBytes bs false <;> rw [hSc] at hDec
    · nomatch hDec
    case some pair =>
      rcases pair with ⟨sv, prov⟩
      dsimp only at hDec
      have hBsLen : Trusted.Sequence.length bs = 8 := Nat.eq_of_beq_eq_true hLen
      have ⟨_, hSvLt⟩ := decodeScalarBytes_bits_lt bs false sv prov hSc
      rw [hBsLen] at hSvLt
      cases prov with
      | none =>
        dsimp only at hDec
        cases hZero : Nat.beq sv.bits 0 <;> rw [hZero] at hDec
        · injection hDec with hV
          refine ⟨addressToPtr sv.bits, hV.symm, ?_⟩
          show sv.bits % 65536 < scalarModulus 8
          have hMod : sv.bits % 65536 < 65536 := Nat.mod_lt _ (by decide)
          have h8 : (65536 : Nat) < scalarModulus 8 := by decide
          omega
        · nomatch hDec
      | some ap =>
        rcases ap with ⟨allocId, tag⟩
        injection hDec with hV
        exact ⟨{ allocId := allocId, offsetBytes := sv.bits }, hV.symm, hSvLt⟩

/--
**Exactness of the thin-pointer `IsTryFromBytes` value predicate (`thin_ptrTy_decode_image_iff`).**
For any thin pointer descriptor `dst` (`dst.isPtr = true`, `isThinPointee pointee = true`),
a runtime value `v` is in the image of `decodeValueFromBytes` at `{ kind := dst.toTrustedRigidTy m pointee, layoutIdx := lIdx }`
**if and only if** `∃ p : ProvenancePtr, v = .ptr p 8 ∧ p.offsetBytes < scalarModulus 8`.
In particular, the predicate in `thin_rawPtr_isTryFromBytes` and `thin_refPtr_isTryFromBytes`
is the exact (strongest possible) value-level `IsTryFromBytes` invariant.
-/
theorem thin_ptrTy_decode_image_iff
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (dst : ScalarTy) (lIdx : LayoutIdx) (v : Value)
    (hPtr : dst.isPtr = true) (hThin : isThinPointee pointee = true) :
    (∃ bs,
      decodeValueFromBytes defaultCodecFuel layouts
        { kind := dst.toTrustedRigidTy m pointee, layoutIdx := lIdx } bs = some v) ↔
      (∃ p : ProvenancePtr, v = .ptr p 8 ∧ p.offsetBytes < scalarModulus 8) := by
  constructor
  · rintro ⟨bs, hDec⟩
    cases dst with
    | rawPtr =>
      rcases thin_rawPtr_isTryFromBytes layouts m pointee lIdx hThin with ⟨_, _, hTry⟩
      exact hTry bs v hDec
    | refPtr =>
      rcases thin_refPtr_isTryFromBytes layouts m pointee lIdx hThin with ⟨_, _, hTry⟩
      exact hTry bs v hDec
    | bool | char | int _ | uint _ => contradiction
  · rintro ⟨p, rfl, hOff⟩
    refine ⟨encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag)), ?_⟩
    rw [show defaultCodecFuel = 15 + 1 from rfl]
    exact trusted_decodeValueFromBytes_thin_ptrTy 15 layouts m pointee dst lIdx _ p hPtr hThin
      (trusted_length_encodeLittleEndianBytes p.offsetBytes 8 _)
      (trusted_decodeScalarBytes_encodeLittleEndianBytes 8 p.offsetBytes
        (some (p.allocId, p.tag)) false (by decide) hOff)

/--
**Divergence (null-offset references are admitted at the value level).**
`Trusted`'s decoder at a thin reference type null-checks only provenance-free
bytes. The provenance-carrying encoding of offset `0` in allocation `a` decodes to
the null-offset pointer `.ptr ⟨a, 0⟩ 8`, so every `IsTryFromBytes` validity
predicate for `&T` holds at that value. Anneal's address model rejects such a
pointer as a null reference (`trusted_evalByteCast_null_offset_ref_divergence`).
-/
theorem thin_refPtr_isTryFromBytes_admits_null_offset
    (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (lIdx : LayoutIdx) (a : Nat) (hThin : isThinPointee pointee = true) :
    decodeValueFromBytes defaultCodecFuel layouts { kind := .ref m pointee, layoutIdx := lIdx }
        (encodeLittleEndianBytes 0 8 (some (a, a))) =
      some (.ptr { allocId := a, offsetBytes := 0 } 8) ∧
    ∀ validPred : Value → Prop,
      IsTryFromBytes layouts { kind := .ref m pointee, layoutIdx := lIdx } validPred →
      validPred (.ptr { allocId := a, offsetBytes := 0 } 8) := by
  have hDec : decodeValueFromBytes defaultCodecFuel layouts
      { kind := .ref m pointee, layoutIdx := lIdx }
      (encodeLittleEndianBytes 0 8 (some (a, a))) =
        some (.ptr { allocId := a, offsetBytes := 0 } 8) := by
    rw [show defaultCodecFuel = 15 + 1 from rfl]
    exact trusted_decodeValueFromBytes_thin_ref 15 layouts m pointee lIdx _
      { allocId := a, offsetBytes := 0 } hThin
      (trusted_length_encodeLittleEndianBytes 0 8 _)
      (trusted_decodeScalarBytes_encodeLittleEndianBytes 8 0 (some (a, a)) false (by decide)
        (by decide))
  refine ⟨hDec, ?_⟩
  rintro validPred ⟨_, _, hPred⟩
  exact hPred _ _ hDec

/--
**`try_transmute` and the `IsTryFromBytes` validity predicate.** For a
non-pointer source and destination of equal width on 64-bit targets and a valid
source bit pattern, the destination satisfies `IsTryFromBytes` with the predicate
of `scalarTy_isTryFromBytes_validBits`. Anneal's `evalTransmuteSameSize` succeeds
iff `Trusted` decodes the candidate bytes at the destination to a value
satisfying that predicate, and any decoded value is exactly
`.scalar ⟨bits, dst.sizeBytes .bits64⟩`.
-/
theorem tryTransmute_valid_iff_isTryFromBytes_validPred
    (policy : TransmutePolicy)
    (layouts : LayoutTable) (m2 : Mutability) (pt2 : RigidTy) (dstLIdx : LayoutIdx)
    (src dst : ScalarTy) (bits : Nat) (exposed : ExposedProvenance)
    (hSrcNp : src.isPtr = false) (hDstNp : dst.isPtr = false)
    (hSz : src.sizeBytes .bits64 = dst.sizeBytes .bits64)
    (hValid : src.validBits .bits64 bits) :
    let dstTy : Ty := { kind := dst.toTrustedRigidTy m2 pt2, layoutIdx := dstLIdx }
    IsTryFromBytes layouts dstTy
      (fun v => ∃ b, dst.validBits .bits64 b ∧ v = .scalar ⟨b, dst.sizeBytes .bits64⟩) ∧
    ((∃ outVal,
        evalTransmuteSameSize .bits64 policy src dst (.scalar bits) exposed = .ok outVal exposed) ↔
      ∃ v,
        decodeValueFromBytes defaultCodecFuel layouts dstTy
          (encodeLittleEndianBytes bits (src.sizeBytes .bits64) none) = some v ∧
        ∃ b, dst.validBits .bits64 b ∧ v = .scalar ⟨b, dst.sizeBytes .bits64⟩) ∧
    (∀ v,
      decodeValueFromBytes defaultCodecFuel layouts dstTy
          (encodeLittleEndianBytes bits (src.sizeBytes .bits64) none) = some v →
      v = .scalar ⟨bits, dst.sizeBytes .bits64⟩) := by
  intro dstTy
  have hTry := scalarTy_isTryFromBytes_validBits layouts m2 pt2 dst dstLIdx hDstNp
  have hMain := tryTransmute_valid_iff_isValidBits .bits64 policy layouts m2 pt2 dstLIdx src dst bits
    exposed hSrcNp hSz hValid
  have hBitsDst : bits < scalarModulus (dst.sizeBytes .bits64) := hSz ▸ hValid.1
  have hDecEq : decodeValueFromBytes defaultCodecFuel layouts dstTy
      (encodeLittleEndianBytes bits (src.sizeBytes .bits64) none) =
        match dst.isValidBits .bits64 bits with
        | true => some (.scalar ⟨bits, dst.sizeBytes .bits64⟩)
        | false => none := by
    rw [hSz, show defaultCodecFuel = 15 + 1 from rfl]
    exact trusted_decodeValueFromBytes_scalar 15 layouts m2 pt2 dst dstLIdx bits hDstNp hBitsDst
  refine ⟨hTry, ?_, ?_⟩
  · rw [hMain.1]
    constructor
    · intro hV
      refine ⟨.scalar ⟨bits, dst.sizeBytes .bits64⟩, ?_, bits,
        (ScalarTy.isValidBits_iff_validBits .bits64 dst bits).mp hV, rfl⟩
      rw [hDecEq, hV]
    · rintro ⟨v, hDec, _⟩
      rw [hDecEq] at hDec
      cases hV : dst.isValidBits .bits64 bits
      · rw [hV] at hDec; nomatch hDec
      · rfl
  · intro v hDec
    rw [hDecEq] at hDec
    cases hV : dst.isValidBits .bits64 bits
    · rw [hV] at hDec; nomatch hDec
    · rw [hV] at hDec
      injection hDec with hEq
      exact hEq.symm

/--
**`try_transmute` instantiation for `u8 -> bool`**:
Unifies `evalTransmuteSameSize`, `ScalarTy.bool.isValidBits`, `ScalarLayout` `wrappingRangeContains ⟨0, 1⟩`,
`decodeScalarLayoutBytes`, and `decodeValueFromBytes` for candidate `u8` bit patterns `bits < 256`.
-/
theorem tryTransmute_u8_to_bool_iff
    (pw : PtrWidth) (policy : TransmutePolicy)
    (layouts : LayoutTable) (lIdx : LayoutIdx)
    (bits : Nat) (exposed : ExposedProvenance)
    (hBits : bits < 256) :
    (evalTransmuteSameSize pw policy .u8 .bool (.scalar bits) exposed =
      .ok (.scalar bits) exposed ↔ ScalarTy.bool.isValidBits pw bits = true) ∧
    (ScalarTy.bool.isValidBits pw bits = true ↔
      wrappingRangeContains (ScalarTy.bool.toValidRange pw) bits = true) ∧
    (ScalarTy.bool.isValidBits pw bits = true ↔ bits ≤ 1) ∧
    (evalTransmuteSameSize pw policy .u8 .bool (.scalar bits) exposed = .ub ↔ 2 ≤ bits) ∧
    ((∃ v',
        decodeValueFromBytes defaultCodecFuel layouts
          { kind := .bool, layoutIdx := lIdx }
          ((encodeCastBytes bits 1 none).map CastByte.toTrustedAbstractByte) = some v') ↔
      bits ≤ 1) := by
  have hValidU864 : ScalarTy.u8.validBits .bits64 bits := ⟨hBits, trivial⟩
  have hTry64 := tryTransmute_valid_iff_isValidBits .bits64 policy layouts .not .bool lIdx
    .u8 .bool bits exposed rfl rfl hValidU864
  have hBoolIff := transmute_bool_valid_iff pw policy bits exposed hBits
  have hRangeIff := scalarTy_isValidBits_iff_validRange_of_ne_char pw .bool bits (by decide)
  have hLeIff : ScalarTy.bool.isValidBits pw bits = true ↔ bits ≤ 1 := by
    rw [ScalarTy.isValidBits_iff_validBits]
    exact ⟨fun h => h.2, fun h => ⟨hBits, h⟩⟩
  refine ⟨?_, hRangeIff, hLeIff, hBoolIff.2.2.1, ?_⟩
  · rw [hBoolIff.1, hLeIff]
  · rw [map_toTrustedAbstractByte_encodeCastBytes]
    dsimp only [Option.map]
    have hDec := hTry64.2.2.2.1 rfl rfl
    rw [hDec, ScalarTy.isValidBits_iff_validBits]
    exact ⟨fun h => h.2, fun h => ⟨hBits, h⟩⟩

/--
**`try_transmute` instantiation for `u32 -> char`**:
Unifies `evalTransmuteSameSize`, `ScalarTy.char.isValidBits`, `isValidCharCode`,
`ScalarLayout` `wrappingRangeContains ⟨0, 1114111⟩` minus the UTF-16 surrogate gap
`55296..=57343`, and `decodeValueFromBytes` for candidate `u32` bit patterns `bits < scalarModulus 4`.
-/
theorem tryTransmute_u32_to_char_iff
    (pw : PtrWidth) (policy : TransmutePolicy)
    (layouts : LayoutTable) (lIdx : LayoutIdx)
    (bits : Nat) (exposed : ExposedProvenance)
    (hBits : bits < scalarModulus 4) :
    (evalTransmuteSameSize pw policy .u32 .char (.scalar bits) exposed =
      .ok (.scalar bits) exposed ↔ ScalarTy.char.isValidBits pw bits = true) ∧
    (ScalarTy.char.isValidBits pw bits = true ↔ isValidCharCode bits = true) ∧
    (ScalarTy.char.isValidBits pw bits = true ↔
      (wrappingRangeContains (ScalarTy.char.toValidRange pw) bits = true ∧
       ¬ (55296 ≤ bits ∧ bits ≤ 57343))) ∧
    (evalTransmuteSameSize pw policy .u32 .char (.scalar bits) exposed = .ub ↔
      ((55296 ≤ bits ∧ bits ≤ 57343) ∨ 1114111 < bits)) ∧
    ((∃ v',
        decodeValueFromBytes defaultCodecFuel layouts
          { kind := .char, layoutIdx := lIdx }
          ((encodeCastBytes bits 4 none).map CastByte.toTrustedAbstractByte) = some v') ↔
      isValidCharCode bits = true) := by
  have hValidU3264 : ScalarTy.u32.validBits .bits64 bits := ⟨hBits, trivial⟩
  have hTry64 := tryTransmute_valid_iff_isValidBits .bits64 policy layouts .not .bool lIdx
    .u32 .char bits exposed rfl rfl hValidU3264
  have hCharIff := transmute_char_valid_iff pw policy bits exposed hBits
  have hCodeIff : ScalarTy.char.isValidBits pw bits = true ↔ isValidCharCode bits = true := by
    rw [ScalarTy.isValidBits_iff_validBits]
    exact ⟨fun h => h.2, fun h => ⟨hBits, h⟩⟩
  have hRangeIff :
      ScalarTy.char.isValidBits pw bits = true ↔
        (wrappingRangeContains (ScalarTy.char.toValidRange pw) bits = true ∧
         ¬ (55296 ≤ bits ∧ bits ≤ 57343)) := by
    rw [scalarTy_isValidBits_iff_scalarLayout_validRange pw .char bits]
    simp
  refine ⟨?_, hCodeIff, hRangeIff, hCharIff.2.1, ?_⟩
  · rw [hCharIff.1, ← isValidCharCode_iff bits, hCodeIff]
  · rw [map_toTrustedAbstractByte_encodeCastBytes]
    dsimp only [Option.map]
    have hDec := hTry64.2.2.2.1 rfl rfl
    rw [hDec, ScalarTy.isValidBits_iff_validBits]
    exact ⟨fun h => h.2, fun h => ⟨hBits, h⟩⟩

/--
**`try_transmute` instantiation for `#[repr(u8)]` contiguous enum `ScalarLayout.validRange`**:
For any 1-byte `.primitive` ADT `enumTy` with `ScalarLayout.initialized (.int 8 false) ⟨0, maxTag⟩`
and any candidate `u8` bit pattern `bits < 256`:
1. `decodeValueFromBytes` on the encoded `u8` bytes returns `some (.scalar ⟨bits, 1⟩)` iff `wrappingRangeContains ⟨0, maxTag⟩ bits = true` (equivalently `bits ≤ maxTag`), and `none` iff `maxTag < bits`.
2. Step-level `evalByteCast` from `u8` to `enumTy` evaluates to `ok (.scalar ⟨bits, 1⟩) locals' mem` iff `bits ≤ maxTag`, and `ub` iff `maxTag < bits`.
-/
theorem tryTransmute_repr_u8_enum_validRange_iff
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (defPath : DefPath) (args : List RigidTy) (srcLIdx enumLIdx : LayoutIdx)
    (l : TypeLayout) (variantIdx maxTag bits : Nat)
    (hBits : bits < 256)
    (hLookup : LayoutTable.lookup layouts enumLIdx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hSz1 : l.size.bytes = 1)
    (hRepr : l.backendRepr = .scalar (.initialized (.int 8 false) ⟨0, maxTag⟩))
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar ⟨bits, 1⟩) locals')
    (hTy : operandTy localDecls layouts op =
      some { kind := .uint .u8, layoutIdx := srcLIdx }) :
    let enumTy : Ty := { kind := .adt defPath args, layoutIdx := enumLIdx }
    let tBytes := (encodeCastBytes bits 1 none).map CastByte.toTrustedAbstractByte
    (decodeValueFromBytes defaultCodecFuel layouts enumTy tBytes =
      some (.scalar ⟨bits, 1⟩) ↔ wrappingRangeContains ⟨0, maxTag⟩ bits = true) ∧
    (decodeValueFromBytes defaultCodecFuel layouts enumTy tBytes =
      some (.scalar ⟨bits, 1⟩) ↔ bits ≤ maxTag) ∧
    (decodeValueFromBytes defaultCodecFuel layouts enumTy tBytes = none ↔ maxTag < bits) ∧
    (evalByteCast locals op enumTy mem localDecls layouts =
      ok (.scalar ⟨bits, 1⟩) locals' mem ↔ bits ≤ maxTag) ∧
    (evalByteCast locals op enumTy mem localDecls layouts = ub ↔ maxTag < bits) := by
  intro enumTy tBytes
  have hMap : tBytes = encodeLittleEndianBytes bits 1 none := by
    unfold tBytes
    rw [map_toTrustedAbstractByte_encodeCastBytes]
    rfl
  have hNz : Nat.beq l.size.bytes 0 = false := by rw [hSz1]; rfl
  have hWidth : primitiveKindByteWidth (.int 8 false) = some l.size.bytes := by
    rw [hSz1]
  have hLen1 : Trusted.Sequence.length (encodeLittleEndianBytes bits 1 none) = l.size.bytes := by
    rw [trusted_length_encodeLittleEndianBytes, hSz1]
  have hBeqLen : Nat.beq (Trusted.Sequence.length (encodeLittleEndianBytes bits 1 none)) l.size.bytes = true := by
    rw [hLen1]; exact Nat.beq_refl _
  have hDecSc : decodeScalarBytes (encodeLittleEndianBytes bits 1 none) false =
      some (⟨bits, 1⟩, none) :=
    trusted_decodeScalarBytes_encodeLittleEndianBytes 1 bits none false (by decide) hBits
  have hDecEq :
      decodeValueFromBytes defaultCodecFuel layouts enumTy tBytes =
        match wrappingRangeContains ⟨0, maxTag⟩ bits with
        | true => some (.scalar ⟨bits, 1⟩)
        | false => none := by
    rw [hMap, show defaultCodecFuel = 15 + 1 from rfl,
        decodeValueFromBytes_adt_primitive_scalarLayout 15 layouts defPath args enumLIdx l variantIdx
          (.initialized (.int 8 false) ⟨0, maxTag⟩) hLookup hInhab hVar hFields hRepr hNz hWidth,
        decodeScalarLayoutBytes_initialized_int_eq 8 false ⟨0, maxTag⟩ l.size.bytes _ hWidth,
        hBeqLen]
    dsimp only
    rw [hDecSc]
    dsimp only
    cases wrappingRangeContains ⟨0, maxTag⟩ bits <;> rfl
  have hEnumSz : rigidTyByteSize layouts enumTy = some 1 := by
    simp [enumTy, rigidTyByteSize, hLookup, hSz1]
  have hU8Sz : rigidTyByteSize layouts { kind := .uint .u8, layoutIdx := srcLIdx } = some 1 := rfl
  have hU8Enc :
      encodeValueToBytes defaultCodecFuel layouts { kind := .uint .u8, layoutIdx := srcLIdx }
        (.scalar ⟨bits, 1⟩) = some (encodeLittleEndianBytes bits 1 none) := rfl
  have hBcEq :
      evalByteCast locals op enumTy mem localDecls layouts =
        match wrappingRangeContains ⟨0, maxTag⟩ bits with
        | true => ok (.scalar ⟨bits, 1⟩) locals' mem
        | false => ub := by
    rw [trusted_evalByteCast_eq locals locals' op mem localDecls layouts (.scalar ⟨bits, 1⟩)
          { kind := .uint .u8, layoutIdx := srcLIdx } enumTy 1 1 hOp hEnumSz hTy hU8Sz,
        hU8Enc]
    dsimp only
    rw [← hMap, hDecEq]
    cases wrappingRangeContains ⟨0, maxTag⟩ bits <;> rfl
  have hWRange := wrappingRangeContains_zero_max_iff maxTag bits
  rw [hDecEq, hBcEq]
  cases hW : wrappingRangeContains ⟨0, maxTag⟩ bits
  · have hGt : maxTag < bits := by
      have : ¬ (bits ≤ maxTag) := fun hLe => by
        rw [hWRange.mpr hLe] at hW; nomatch hW
      omega
    refine ⟨by simp, ?_, ?_, ?_, ?_⟩ <;> simp [hGt, show ¬ (bits ≤ maxTag) by omega]
  · have hLe : bits ≤ maxTag := hWRange.mp hW
    refine ⟨by simp, ?_, ?_, ?_, ?_⟩ <;> simp [hLe, show ¬ (maxTag < bits) by omega]

/--
**`try_transmute` instantiation for `NonZero*` (`⟨1, scalarModulus sz - 1⟩`) niche validation**:
1. At the `ScalarTy.refPtr` level: transmuting a pointer-sized integer `bits < pw.modulus` to `refPtr` succeeds iff `wrappingRangeContains ⟨1, pw.modulus - 1⟩ bits = true` (equivalently `0 < bits`), and rejects `0` with `.ub`.
2. At the `.primitive` ADT `NonZero*` layout level (`ScalarLayout.initialized (.int (8 * sz) signed) ⟨1, scalarModulus sz - 1⟩`): decoding the encoded bytes of `bits < scalarModulus sz` succeeds iff `0 < bits` and returns `none` iff `bits = 0`.
-/
theorem tryTransmute_nonZero_niche_iff
    (pw : PtrWidth) (policy : TransmutePolicy)
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (nonZeroLIdx : LayoutIdx)
    (l : TypeLayout) (variantIdx sz : Nat) (signed : Bool)
    (w : IntWidth) (bits ptrBits : Nat) (exposed : ExposedProvenance)
    (hW : w.byteSize pw = pw.byteSize)
    (hPtrBits : ptrBits < pw.modulus)
    (hSzPos : 0 < sz)
    (hBits : bits < scalarModulus sz)
    (hLookup : LayoutTable.lookup layouts nonZeroLIdx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hLSz : l.size.bytes = sz)
    (hRepr :
      l.backendRepr =
        .scalar (.initialized (.int (8 * sz) signed) ⟨1, scalarModulus sz - 1⟩)) :
    let nonZeroTy : Ty := { kind := .adt defPath args, layoutIdx := nonZeroLIdx }
    let tBytes := (encodeCastBytes bits sz none).map CastByte.toTrustedAbstractByte
    (evalTransmuteSameSize pw policy (.uint w) .refPtr (.scalar ptrBits) exposed =
      .ok (.ptr { allocId := 0, offsetBytes := ptrBits } none) exposed ↔
        wrappingRangeContains ⟨1, pw.modulus - 1⟩ ptrBits = true) ∧
    (evalTransmuteSameSize pw policy (.uint w) .refPtr (.scalar ptrBits) exposed =
      .ok (.ptr { allocId := 0, offsetBytes := ptrBits } none) exposed ↔
        0 < ptrBits) ∧
    (evalTransmuteSameSize pw policy (.uint w) .refPtr (.scalar ptrBits) exposed = .ub ↔
      ptrBits = 0) ∧
    (decodeValueFromBytes defaultCodecFuel layouts nonZeroTy tBytes =
      some (.scalar ⟨bits, sz⟩) ↔
        wrappingRangeContains ⟨1, scalarModulus sz - 1⟩ bits = true) ∧
    (decodeValueFromBytes defaultCodecFuel layouts nonZeroTy tBytes =
      some (.scalar ⟨bits, sz⟩) ↔ 0 < bits) ∧
    (decodeValueFromBytes defaultCodecFuel layouts nonZeroTy tBytes = none ↔ bits = 0) := by
  intro nonZeroTy tBytes
  have hValidUint : (ScalarTy.uint w).validBits pw ptrBits := by
    refine ⟨?_, trivial⟩
    show ptrBits < scalarModulus (w.byteSize pw)
    rw [hW]
    exact hPtrBits
  have hIntToPtr :=
    evalTransmuteSameSize_int_to_ptr_eq pw policy (.uint w) .refPtr ptrBits exposed
      rfl rfl hW hValidUint
  have hRefIff :
      ScalarTy.refPtr.isValidBits pw ptrBits = true ↔
        wrappingRangeContains ⟨1, pw.modulus - 1⟩ ptrBits = true := by
    rw [ScalarTy.isValidBits_iff_validBits,
        ScalarTy.validBits_refPtr_iff_wrappingRangeContains pw ptrBits]
  have hRefPosIff :
      ScalarTy.refPtr.isValidBits pw ptrBits = true ↔ 0 < ptrBits := by
    rw [ScalarTy.isValidBits_iff_validBits]
    exact ⟨fun h => h.2, fun h => ⟨hPtrBits, h⟩⟩
  have hMap : tBytes = encodeLittleEndianBytes bits sz none := by
    unfold tBytes
    rw [map_toTrustedAbstractByte_encodeCastBytes]
    rfl
  have hNz : Nat.beq l.size.bytes 0 = false := by
    rw [hLSz]
    cases sz with
    | zero => omega
    | succ _ => rfl
  have hWidth : primitiveKindByteWidth (.int (8 * sz) signed) = some l.size.bytes := by
    unfold primitiveKindByteWidth
    dsimp only
    rw [hLSz]
    have hBeq0 : Nat.beq (8 * sz) 0 = false := by
      cases sz with
      | zero => omega
      | succ _ => rfl
    rw [hBeq0]
    dsimp only
    congr 1
    change (8 * sz) / 8 = sz
    omega
  have hLenSz : Trusted.Sequence.length (encodeLittleEndianBytes bits sz none) = l.size.bytes := by
    rw [trusted_length_encodeLittleEndianBytes, hLSz]
  have hBeqLen : Nat.beq (Trusted.Sequence.length (encodeLittleEndianBytes bits sz none)) l.size.bytes = true := by
    rw [hLenSz]; exact Nat.beq_refl _
  have hDecSc : decodeScalarBytes (encodeLittleEndianBytes bits sz none) false =
      some (⟨bits, sz⟩, none) :=
    trusted_decodeScalarBytes_encodeLittleEndianBytes sz bits none false hSzPos hBits
  have hDecEq :
      decodeValueFromBytes defaultCodecFuel layouts nonZeroTy tBytes =
        match wrappingRangeContains ⟨1, scalarModulus sz - 1⟩ bits with
        | true => some (.scalar ⟨bits, sz⟩)
        | false => none := by
    rw [hMap, show defaultCodecFuel = 15 + 1 from rfl,
        decodeValueFromBytes_adt_primitive_scalarLayout 15 layouts defPath args nonZeroLIdx l variantIdx
          (.initialized (.int (8 * sz) signed) ⟨1, scalarModulus sz - 1⟩) hLookup hInhab hVar hFields hRepr hNz hWidth,
        decodeScalarLayoutBytes_initialized_int_eq (8 * sz) signed ⟨1, scalarModulus sz - 1⟩ l.size.bytes _ hWidth,
        hBeqLen]
    dsimp only
    rw [hDecSc]
    dsimp only
    cases wrappingRangeContains ⟨1, scalarModulus sz - 1⟩ bits <;> rfl
  have hNzRangeIff := wrappingRangeContains_nonZeroRange_iff hSzPos bits
  rw [hIntToPtr, hDecEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hRefIff]
    cases ScalarTy.refPtr.isValidBits pw ptrBits <;> simp
  · rw [← hRefPosIff]
    cases ScalarTy.refPtr.isValidBits pw ptrBits <;> simp
  · cases hRv : ScalarTy.refPtr.isValidBits pw ptrBits
    · have hZero : ptrBits = 0 := by
        have hNotPos : ¬ (0 < ptrBits) := fun hp => by
          rw [hRefPosIff.mpr hp] at hRv; nomatch hRv
        omega
      simp [hZero]
    · have hPos : 0 < ptrBits := hRefPosIff.mp hRv
      simp [show ptrBits ≠ 0 by omega]
  · cases wrappingRangeContains ⟨1, scalarModulus sz - 1⟩ bits <;> simp
  · cases hW : wrappingRangeContains ⟨1, scalarModulus sz - 1⟩ bits
    · have hNotPos : ¬ (0 < bits) := fun hp => by
        rw [hNzRangeIff.mpr ⟨hp, hBits⟩] at hW; nomatch hW
      simp [hNotPos]
    · have hPos : 0 < bits := (hNzRangeIff.mp hW).1
      simp [hPos]
  · cases hW : wrappingRangeContains ⟨1, scalarModulus sz - 1⟩ bits
    · have hZero : bits = 0 := by
        have hNotPos : ¬ (0 < bits) := fun hp => by
          rw [hNzRangeIff.mpr ⟨hp, hBits⟩] at hW; nomatch hW
        omega
      simp [hZero]
    · have hPos : 0 < bits := (hNzRangeIff.mp hW).1
      simp [show bits ≠ 0 by omega]

/--
**`try_transmute` into a `.primitive` scalar-layout ADT at the `Trusted` step level.** Let the
destination `.adt` have an inhabited single-variant `.primitive` layout whose backend
representation is `ScalarLayout.initialized (.int bitsWidth signed) validRange` (a fieldless
`#[repr(Int)]` enum tag range, a bounded integer, or a `NonZero*` niche), and let the operand be a
valid non-pointer scalar of type `src` with the same byte width. Then decoding the operand's bytes
at the ADT, and `Trusted.MirSemantics.evalByteCast`, both succeed exactly when
`wrappingRangeContains validRange bits = true` (producing `.scalar ⟨bits, src.sizeBytes .bits64⟩`);
otherwise decoding returns `none` and `evalByteCast` is `ub`. Wrapping ranges (`start > end`) are
covered as well.
-/
theorem tryTransmute_adt_primitive_scalarLayout_eq
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (m : Mutability) (pointee : RigidTy) (src : ScalarTy) (srcLIdx : LayoutIdx)
    (defPath : DefPath) (args : List RigidTy) (dstLIdx : LayoutIdx)
    (l : TypeLayout) (variantIdx bitsWidth bits : Nat) (signed : Bool)
    (validRange : WrappingRange)
    (hSrcNp : src.isPtr = false)
    (hValid : src.validBits .bits64 bits)
    (hLookup : LayoutTable.lookup layouts dstLIdx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hRepr : l.backendRepr = .scalar (.initialized (.int bitsWidth signed) validRange))
    (hLSz : l.size.bytes = src.sizeBytes .bits64)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar ⟨bits, src.sizeBytes .bits64⟩) locals')
    (hTy : operandTy localDecls layouts op =
      some { kind := src.toTrustedRigidTy m pointee, layoutIdx := srcLIdx }) :
    let dstTy : Ty := { kind := .adt defPath args, layoutIdx := dstLIdx }
    decodeValueFromBytes defaultCodecFuel layouts dstTy
        (encodeLittleEndianBytes bits (src.sizeBytes .bits64) none) =
      (match wrappingRangeContains validRange bits with
       | true => some (.scalar ⟨bits, src.sizeBytes .bits64⟩)
       | false => none) ∧
    evalByteCast locals op dstTy mem localDecls layouts =
      (match wrappingRangeContains validRange bits with
       | true => ok (.scalar ⟨bits, src.sizeBytes .bits64⟩) locals' mem
       | false => ub) := by
  intro dstTy
  have hNz : Nat.beq l.size.bytes 0 = false := by
    rw [hLSz]
    exact ScalarTy.sizeBytes_bits64_beq_zero src
  have hBits : bits < scalarModulus l.size.bytes := hLSz ▸ hValid.1
  have hDec :
      decodeValueFromBytes defaultCodecFuel layouts dstTy
          (encodeLittleEndianBytes bits (src.sizeBytes .bits64) none) =
        (match wrappingRangeContains validRange bits with
         | true => some (.scalar ⟨bits, src.sizeBytes .bits64⟩)
         | false => none) := by
    have h := adt_primitive_scalarLayout_decode_encode_eq layouts defPath args dstLIdx l variantIdx
      bitsWidth signed validRange hLookup hInhab hVar hFields hRepr hNz hWidth bits none hBits
    rw [hLSz] at h
    exact h
  have hDstSz : rigidTyByteSize layouts dstTy = some (src.sizeBytes .bits64) := by
    simp [dstTy, rigidTyByteSize, hLookup, hLSz]
  have hSrcSz := ScalarTy.rigidTyByteSize_toTrustedRigidTy_of_not_isPtr layouts m pointee src
    srcLIdx hSrcNp
  have hEnc := trusted_encodeValueToBytes_scalar 15 layouts m pointee src srcLIdx bits hSrcNp hValid
  refine ⟨hDec, ?_⟩
  rw [trusted_evalByteCast_of_encode locals locals' op mem localDecls layouts _ _ dstTy _ _
    hOp hDstSz hTy hSrcSz hEnc (trusted_length_encodeLittleEndianBytes bits _ none), hDec]
  cases wrappingRangeContains validRange bits <;> rfl

/--
**`NonZero*` niche validation at the `Trusted` step level.** Transmuting a valid same-width
non-pointer scalar into a `.primitive` `NonZero*` layout
(`validRange = ⟨1, scalarModulus sz - 1⟩`) with `Trusted.MirSemantics.evalByteCast` succeeds with
the unchanged bit pattern iff `0 < bits`, and is `ub` iff `bits = 0`.
-/
theorem tryTransmute_nonZero_evalByteCast_iff
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (m : Mutability) (pointee : RigidTy) (src : ScalarTy) (srcLIdx : LayoutIdx)
    (defPath : DefPath) (args : List RigidTy) (dstLIdx : LayoutIdx)
    (l : TypeLayout) (variantIdx bitsWidth bits : Nat) (signed : Bool)
    (hSrcNp : src.isPtr = false)
    (hValid : src.validBits .bits64 bits)
    (hLookup : LayoutTable.lookup layouts dstLIdx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hRepr :
      l.backendRepr =
        .scalar (.initialized (.int bitsWidth signed) ⟨1, scalarModulus l.size.bytes - 1⟩))
    (hLSz : l.size.bytes = src.sizeBytes .bits64)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar ⟨bits, src.sizeBytes .bits64⟩) locals')
    (hTy : operandTy localDecls layouts op =
      some { kind := src.toTrustedRigidTy m pointee, layoutIdx := srcLIdx }) :
    let dstTy : Ty := { kind := .adt defPath args, layoutIdx := dstLIdx }
    (evalByteCast locals op dstTy mem localDecls layouts =
      ok (.scalar ⟨bits, src.sizeBytes .bits64⟩) locals' mem ↔ 0 < bits) ∧
    (evalByteCast locals op dstTy mem localDecls layouts = ub ↔ bits = 0) := by
  intro dstTy
  have hBc := (tryTransmute_adt_primitive_scalarLayout_eq locals locals' op mem localDecls layouts
    m pointee src srcLIdx defPath args dstLIdx l variantIdx bitsWidth bits signed
    ⟨1, scalarModulus l.size.bytes - 1⟩ hSrcNp hValid hLookup hInhab hVar hFields hRepr hLSz hWidth
    hOp hTy).2
  have hPos : 0 < l.size.bytes := by
    rw [hLSz]
    exact ScalarTy.sizeBytes_pos .bits64 src
  have hBits : bits < scalarModulus l.size.bytes := hLSz ▸ hValid.1
  have hIff := wrappingRangeContains_nonZeroRange_iff hPos bits
  rw [hBc]
  cases hW : wrappingRangeContains ⟨1, scalarModulus l.size.bytes - 1⟩ bits
  · have hZero : bits = 0 := by
      have hNot : ¬ (0 < bits) := fun hp => by
        rw [hIff.mpr ⟨hp, hBits⟩] at hW
        nomatch hW
      omega
    subst hZero
    simp
  · have hPosB : 0 < bits := (hIff.mp hW).1
    simp [hPosB, show bits ≠ 0 by omega]

/--
**Contiguous enum-tag validation at the `Trusted` step level.** Transmuting a valid same-width
non-pointer scalar into a `.primitive` scalar-layout ADT with a non-wrapping tag range
`⟨lo, hi⟩` (`lo ≤ hi`, e.g. a fieldless `#[repr(u8)]` enum whose discriminants are `lo..=hi`) with
`Trusted.MirSemantics.evalByteCast` succeeds iff `lo ≤ bits ≤ hi`, and is `ub` iff
`bits < lo ∨ hi < bits`.
-/
theorem tryTransmute_enumRange_evalByteCast_iff
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (m : Mutability) (pointee : RigidTy) (src : ScalarTy) (srcLIdx : LayoutIdx)
    (defPath : DefPath) (args : List RigidTy) (dstLIdx : LayoutIdx)
    (l : TypeLayout) (variantIdx bitsWidth bits lo hi : Nat) (signed : Bool)
    (hLe : lo ≤ hi)
    (hSrcNp : src.isPtr = false)
    (hValid : src.validBits .bits64 bits)
    (hLookup : LayoutTable.lookup layouts dstLIdx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hRepr : l.backendRepr = .scalar (.initialized (.int bitsWidth signed) ⟨lo, hi⟩))
    (hLSz : l.size.bytes = src.sizeBytes .bits64)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar ⟨bits, src.sizeBytes .bits64⟩) locals')
    (hTy : operandTy localDecls layouts op =
      some { kind := src.toTrustedRigidTy m pointee, layoutIdx := srcLIdx }) :
    let dstTy : Ty := { kind := .adt defPath args, layoutIdx := dstLIdx }
    (evalByteCast locals op dstTy mem localDecls layouts =
      ok (.scalar ⟨bits, src.sizeBytes .bits64⟩) locals' mem ↔ (lo ≤ bits ∧ bits ≤ hi)) ∧
    (evalByteCast locals op dstTy mem localDecls layouts = ub ↔ (bits < lo ∨ hi < bits)) := by
  intro dstTy
  have hBc := (tryTransmute_adt_primitive_scalarLayout_eq locals locals' op mem localDecls layouts
    m pointee src srcLIdx defPath args dstLIdx l variantIdx bitsWidth bits signed ⟨lo, hi⟩ hSrcNp
    hValid hLookup hInhab hVar hFields hRepr hLSz hWidth hOp hTy).2
  have hIff := wrappingRangeContains_nonwrapping_iff (v := bits) hLe
  rw [hBc]
  cases hW : wrappingRangeContains ⟨lo, hi⟩ bits
  · have hOut : ¬ (lo ≤ bits ∧ bits ≤ hi) := fun h => by
      rw [hIff.mpr h] at hW
      nomatch hW
    simp only [reduceCtorEq, false_iff, true_iff]
    exact ⟨hOut, by omega⟩
  · have hIn := hIff.mp hW
    simp only [reduceCtorEq, true_iff, false_iff]
    exact ⟨hIn, by omega⟩

/--
**`try_transmute` into a single-field scalar-wrapper newtype ADT (`FieldsShape.arbitrary [⟨0⟩]`) at the `Trusted` step level.**
For a scalar-niche wrapper decoded on the backend scalar path (`.adt defPath []` with
`l.fieldLayouts = []`), both `decodeValueFromBytes` and `Trusted.MirSemantics.evalByteCast`
succeed (producing `.aggregate variantIdx [.scalar ⟨bits, src.sizeBytes .bits64⟩]`) iff
`wrappingRangeContains validRange bits = true`, and otherwise return `none` / `ub`. A
monomorphized generic wrapper such as `NonZero<u32>` (type arguments `[u32]`) is decoded at its
type argument instead, where `Trusted` does not enforce the niche
(`adt_generic_nonZero_typeArg_path_niche_unenforced`).
-/
theorem tryTransmute_adt_newtype_scalarLayout_eq
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (m : Mutability) (pointee : RigidTy) (src : ScalarTy) (srcLIdx : LayoutIdx)
    (defPath : DefPath) (dstLIdx : LayoutIdx)
    (l : TypeLayout) (variantIdx bitsWidth bits : Nat) (memoryOrder : List Nat) (signed : Bool)
    (validRange : WrappingRange)
    (hSrcNp : src.isPtr = false)
    (hValid : src.validBits .bits64 bits)
    (hLookup : LayoutTable.lookup layouts dstLIdx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hNoFieldLayouts : l.fieldLayouts = [])
    (hRepr : l.backendRepr = .scalar (.initialized (.int bitsWidth signed) validRange))
    (hLSz : l.size.bytes = src.sizeBytes .bits64)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar ⟨bits, src.sizeBytes .bits64⟩) locals')
    (hTy : operandTy localDecls layouts op =
      some { kind := src.toTrustedRigidTy m pointee, layoutIdx := srcLIdx }) :
    let dstTy : Ty := { kind := .adt defPath [], layoutIdx := dstLIdx }
    decodeValueFromBytes defaultCodecFuel layouts dstTy
        (encodeLittleEndianBytes bits (src.sizeBytes .bits64) none) =
      (match wrappingRangeContains validRange bits with
       | true => some (.aggregate variantIdx [.scalar ⟨bits, src.sizeBytes .bits64⟩])
       | false => none) ∧
    evalByteCast locals op dstTy mem localDecls layouts =
      (match wrappingRangeContains validRange bits with
       | true => ok (.aggregate variantIdx [.scalar ⟨bits, src.sizeBytes .bits64⟩]) locals' mem
       | false => ub) := by
  intro dstTy
  have hNz : Nat.beq l.size.bytes 0 = false := by
    rw [hLSz]
    exact ScalarTy.sizeBytes_bits64_beq_zero src
  have hBits : bits < scalarModulus l.size.bytes := hLSz ▸ hValid.1
  have hDec :
      decodeValueFromBytes defaultCodecFuel layouts dstTy
          (encodeLittleEndianBytes bits (src.sizeBytes .bits64) none) =
        (match wrappingRangeContains validRange bits with
         | true => some (.aggregate variantIdx [.scalar ⟨bits, src.sizeBytes .bits64⟩])
         | false => none) := by
    have h := adt_newtype_scalarLayout_decode_encode_eq layouts defPath dstLIdx l variantIdx
      bitsWidth memoryOrder signed validRange hLookup hInhab hVar hFields hNoFieldLayouts
      hRepr hNz hWidth bits none hBits
    rw [hLSz] at h
    exact h
  have hDstSz : rigidTyByteSize layouts dstTy = some (src.sizeBytes .bits64) := by
    simp [dstTy, rigidTyByteSize, hLookup, hLSz]
  have hSrcSz := ScalarTy.rigidTyByteSize_toTrustedRigidTy_of_not_isPtr layouts m pointee src
    srcLIdx hSrcNp
  have hEnc := trusted_encodeValueToBytes_scalar 15 layouts m pointee src srcLIdx bits hSrcNp hValid
  refine ⟨hDec, ?_⟩
  rw [trusted_evalByteCast_of_encode locals locals' op mem localDecls layouts _ _ dstTy _ _
    hOp hDstSz hTy hSrcSz hEnc (trusted_length_encodeLittleEndianBytes bits _ none), hDec]
  cases wrappingRangeContains validRange bits <;> rfl

/--
**`NonZero*` single-field newtype (`FieldsShape.arbitrary [⟨0⟩]`) niche validation at the `Trusted` step level.**
Transmuting a valid same-width non-pointer scalar into a `NonZero*`-style newtype layout
(`validRange = ⟨1, scalarModulus l.size.bytes - 1⟩`) decoded on the backend scalar path
(`.adt defPath []`, `l.fieldLayouts = []`) with `Trusted.MirSemantics.evalByteCast`
succeeds with `ok (.aggregate variantIdx [.scalar ⟨bits, src.sizeBytes .bits64⟩]) locals' mem`
iff `0 < bits`, and is `ub` iff `bits = 0`. On the type-argument path of a generic wrapper the
niche is not enforced (`adt_generic_nonZero_typeArg_path_niche_unenforced`).
-/
theorem tryTransmute_adt_newtype_nonZero_evalByteCast_iff
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (m : Mutability) (pointee : RigidTy) (src : ScalarTy) (srcLIdx : LayoutIdx)
    (defPath : DefPath) (dstLIdx : LayoutIdx)
    (l : TypeLayout) (variantIdx bitsWidth bits : Nat) (memoryOrder : List Nat) (signed : Bool)
    (hSrcNp : src.isPtr = false)
    (hValid : src.validBits .bits64 bits)
    (hLookup : LayoutTable.lookup layouts dstLIdx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hNoFieldLayouts : l.fieldLayouts = [])
    (hRepr :
      l.backendRepr =
        .scalar (.initialized (.int bitsWidth signed) ⟨1, scalarModulus l.size.bytes - 1⟩))
    (hLSz : l.size.bytes = src.sizeBytes .bits64)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar ⟨bits, src.sizeBytes .bits64⟩) locals')
    (hTy : operandTy localDecls layouts op =
      some { kind := src.toTrustedRigidTy m pointee, layoutIdx := srcLIdx }) :
    let dstTy : Ty := { kind := .adt defPath [], layoutIdx := dstLIdx }
    (evalByteCast locals op dstTy mem localDecls layouts =
      ok (.aggregate variantIdx [.scalar ⟨bits, src.sizeBytes .bits64⟩]) locals' mem ↔ 0 < bits) ∧
    (evalByteCast locals op dstTy mem localDecls layouts = ub ↔ bits = 0) := by
  intro dstTy
  have hBc := (tryTransmute_adt_newtype_scalarLayout_eq locals locals' op mem localDecls layouts
    m pointee src srcLIdx defPath dstLIdx l variantIdx bitsWidth bits memoryOrder signed
    ⟨1, scalarModulus l.size.bytes - 1⟩ hSrcNp hValid hLookup hInhab hVar hFields hNoFieldLayouts
    hRepr hLSz hWidth hOp hTy).2
  have hPos : 0 < l.size.bytes := by
    rw [hLSz]
    exact ScalarTy.sizeBytes_pos .bits64 src
  have hBits : bits < scalarModulus l.size.bytes := hLSz ▸ hValid.1
  have hIff := wrappingRangeContains_nonZeroRange_iff hPos bits
  rw [hBc]
  cases hW : wrappingRangeContains ⟨1, scalarModulus l.size.bytes - 1⟩ bits
  · have hZero : bits = 0 := by
      have hNot : ¬ (0 < bits) := fun hp => by
        rw [hIff.mpr ⟨hp, hBits⟩] at hW
        nomatch hW
      omega
    subst hZero
    simp
  · have hPosB : 0 < bits := (hIff.mp hW).1
    simp [hPosB, show bits ≠ 0 by omega]

/--
**`try_transmute` into a multi-variant fieldless `#[repr(Int)]` / `#[repr(u8)]` enum ADT (`VariantsShape.multiple`) at the `Trusted` step level.**
For the layout shape of multi-variant fieldless enums (`l.variants = .multiple (.initialized (.int bitsWidth signed) validRange) 0 variantShapes`, `l.fields = .arbitrary [⟨0⟩] memoryOrder`) whose in-range tags all index fieldless variants (`hFieldless`):
both `decodeValueFromBytes` and `Trusted.MirSemantics.evalByteCast` succeed (producing `.aggregate bits []`)
iff `wrappingRangeContains validRange bits = true`, and otherwise return `none` / `ub`. Because `Trusted`
uses the tag value as the variant index, `hFieldless` holds for real `rustc` layouts only when the
discriminants are the variant indices `0..n-1` (`adt_multiple_enum_explicit_discriminant_divergence`).
-/
theorem tryTransmute_adt_multiple_enum_scalarLayout_eq
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (m : Mutability) (pointee : RigidTy) (src : ScalarTy) (srcLIdx : LayoutIdx)
    (defPath : DefPath) (args : List RigidTy) (dstLIdx : LayoutIdx)
    (l : TypeLayout) (bitsWidth bits : Nat) (signed : Bool)
    (validRange : WrappingRange) (variantShapes : List FieldsShape) (memoryOrder : List Nat)
    (hSrcNp : src.isPtr = false)
    (hValid : src.validBits .bits64 bits)
    (hLookup : LayoutTable.lookup layouts dstLIdx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .multiple (.initialized (.int bitsWidth signed) validRange) 0 variantShapes)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hLSz : l.size.bytes = src.sizeBytes .bits64)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes)
    (hFieldless :
      ∀ tag < scalarModulus l.size.bytes,
        wrappingRangeContains validRange tag = true →
        ∃ varMemOrder, Trusted.Sequence.get? variantShapes tag = some (.arbitrary [] varMemOrder))
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar ⟨bits, src.sizeBytes .bits64⟩) locals')
    (hTy : operandTy localDecls layouts op =
      some { kind := src.toTrustedRigidTy m pointee, layoutIdx := srcLIdx }) :
    let dstTy : Ty := { kind := .adt defPath args, layoutIdx := dstLIdx }
    decodeValueFromBytes defaultCodecFuel layouts dstTy
        (encodeLittleEndianBytes bits (src.sizeBytes .bits64) none) =
      (match wrappingRangeContains validRange bits with
       | true => some (.aggregate bits [])
       | false => none) ∧
    evalByteCast locals op dstTy mem localDecls layouts =
      (match wrappingRangeContains validRange bits with
       | true => ok (.aggregate bits []) locals' mem
       | false => ub) := by
  intro dstTy
  have hNz : Nat.beq l.size.bytes 0 = false := by
    rw [hLSz]
    exact ScalarTy.sizeBytes_bits64_beq_zero src
  have hBits : bits < scalarModulus l.size.bytes := hLSz ▸ hValid.1
  have hDec :
      decodeValueFromBytes defaultCodecFuel layouts dstTy
          (encodeLittleEndianBytes bits (src.sizeBytes .bits64) none) =
        (match wrappingRangeContains validRange bits with
         | true => some (.aggregate bits [])
         | false => none) := by
    have h := adt_multiple_enum_scalarLayout_decode_encode_eq layouts defPath args dstLIdx l
      bitsWidth signed validRange variantShapes memoryOrder hLookup hInhab hVar hFields hNz hWidth
      hFieldless bits none hBits
    rw [hLSz] at h
    exact h
  have hDstSz : rigidTyByteSize layouts dstTy = some (src.sizeBytes .bits64) := by
    simp [dstTy, rigidTyByteSize, hLookup, hLSz]
  have hSrcSz := ScalarTy.rigidTyByteSize_toTrustedRigidTy_of_not_isPtr layouts m pointee src
    srcLIdx hSrcNp
  have hEnc := trusted_encodeValueToBytes_scalar 15 layouts m pointee src srcLIdx bits hSrcNp hValid
  refine ⟨hDec, ?_⟩
  rw [trusted_evalByteCast_of_encode locals locals' op mem localDecls layouts _ _ dstTy _ _
    hOp hDstSz hTy hSrcSz hEnc (trusted_length_encodeLittleEndianBytes bits _ none), hDec]
  cases wrappingRangeContains validRange bits <;> rfl

/--
**Multi-variant `#[repr(u8)]` / `#[repr(Int)]` contiguous enum-tag validation (`VariantsShape.multiple`) at the `Trusted` step level.**
Transmuting a valid same-width non-pointer scalar into a multi-variant fieldless enum with tag range `⟨lo, hi⟩` (`lo ≤ hi`)
succeeds with `ok (.aggregate bits []) locals' mem` iff `lo ≤ bits ∧ bits ≤ hi`, and returns `ub` iff `bits < lo ∨ hi < bits`.
For real `rustc` layouts, `hFieldless` (every tag in `lo..=hi` indexes a fieldless variant) requires the
discriminants to be the variant indices, i.e. `lo = 0` and `hi = n - 1`
(`adt_multiple_enum_explicit_discriminant_divergence`).
-/
theorem tryTransmute_adt_multiple_enumRange_evalByteCast_iff
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (m : Mutability) (pointee : RigidTy) (src : ScalarTy) (srcLIdx : LayoutIdx)
    (defPath : DefPath) (args : List RigidTy) (dstLIdx : LayoutIdx)
    (l : TypeLayout) (bitsWidth bits lo hi : Nat) (signed : Bool)
    (variantShapes : List FieldsShape) (memoryOrder : List Nat)
    (hLe : lo ≤ hi)
    (hSrcNp : src.isPtr = false)
    (hValid : src.validBits .bits64 bits)
    (hLookup : LayoutTable.lookup layouts dstLIdx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .multiple (.initialized (.int bitsWidth signed) ⟨lo, hi⟩) 0 variantShapes)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hLSz : l.size.bytes = src.sizeBytes .bits64)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes)
    (hFieldless :
      ∀ tag < scalarModulus l.size.bytes,
        wrappingRangeContains ⟨lo, hi⟩ tag = true →
        ∃ varMemOrder, Trusted.Sequence.get? variantShapes tag = some (.arbitrary [] varMemOrder))
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar ⟨bits, src.sizeBytes .bits64⟩) locals')
    (hTy : operandTy localDecls layouts op =
      some { kind := src.toTrustedRigidTy m pointee, layoutIdx := srcLIdx }) :
    let dstTy : Ty := { kind := .adt defPath args, layoutIdx := dstLIdx }
    (evalByteCast locals op dstTy mem localDecls layouts =
      ok (.aggregate bits []) locals' mem ↔ (lo ≤ bits ∧ bits ≤ hi)) ∧
    (evalByteCast locals op dstTy mem localDecls layouts = ub ↔ (bits < lo ∨ hi < bits)) := by
  intro dstTy
  have hBc := (tryTransmute_adt_multiple_enum_scalarLayout_eq locals locals' op mem localDecls layouts
    m pointee src srcLIdx defPath args dstLIdx l bitsWidth bits signed ⟨lo, hi⟩ variantShapes
    memoryOrder hSrcNp hValid hLookup hInhab hVar hFields hLSz hWidth hFieldless hOp hTy).2
  have hIff := wrappingRangeContains_nonwrapping_iff (v := bits) hLe
  rw [hBc]
  cases hW : wrappingRangeContains ⟨lo, hi⟩ bits
  · have hOut : ¬ (lo ≤ bits ∧ bits ≤ hi) := fun h => by
      rw [hIff.mpr h] at hW
      nomatch hW
    simp only [reduceCtorEq, false_iff, true_iff]
    exact ⟨hOut, by omega⟩
  · have hIn := hIff.mp hW
    simp only [reduceCtorEq, true_iff, false_iff]
    exact ⟨hIn, by omega⟩

/--
**Concrete `try_transmute` instantiation for multi-variant `#[repr(u8)]` contiguous enums (`VariantsShape.multiple`).**
For any 1-byte multi-variant `#[repr(u8)]` enum `enumTy` with `ScalarLayout.initialized (.int 8 false) ⟨0, maxTag⟩`
whose tags `0..=maxTag` index fieldless variants `.arbitrary [] _` in `variantShapes`, and any candidate
`u8` bit pattern `bits < 256`:
1. `decodeValueFromBytes` on the encoded `u8` bytes returns `some (.aggregate bits [])` iff `wrappingRangeContains ⟨0, maxTag⟩ bits = true` (equivalently `bits ≤ maxTag`), and `none` iff `maxTag < bits`.
2. Step-level `evalByteCast` from `u8` to `enumTy` evaluates to `ok (.aggregate bits []) locals' mem` iff `bits ≤ maxTag`, and `ub` iff `maxTag < bits`.
-/
theorem tryTransmute_repr_u8_multiple_enum_validRange_iff
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (defPath : DefPath) (args : List RigidTy) (srcLIdx enumLIdx : LayoutIdx)
    (l : TypeLayout) (maxTag bits : Nat)
    (variantShapes : List FieldsShape) (memoryOrder : List Nat)
    (hBits : bits < 256)
    (hLookup : LayoutTable.lookup layouts enumLIdx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .multiple (.initialized (.int 8 false) ⟨0, maxTag⟩) 0 variantShapes)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hSz1 : l.size.bytes = 1)
    (hFieldless :
      ∀ tag < 256,
        wrappingRangeContains ⟨0, maxTag⟩ tag = true →
        ∃ varMemOrder, Trusted.Sequence.get? variantShapes tag = some (.arbitrary [] varMemOrder))
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar ⟨bits, 1⟩) locals')
    (hTy : operandTy localDecls layouts op =
      some { kind := .uint .u8, layoutIdx := srcLIdx }) :
    let enumTy : Ty := { kind := .adt defPath args, layoutIdx := enumLIdx }
    let tBytes := (encodeCastBytes bits 1 none).map CastByte.toTrustedAbstractByte
    (decodeValueFromBytes defaultCodecFuel layouts enumTy tBytes =
      some (.aggregate bits []) ↔ wrappingRangeContains ⟨0, maxTag⟩ bits = true) ∧
    (decodeValueFromBytes defaultCodecFuel layouts enumTy tBytes =
      some (.aggregate bits []) ↔ bits ≤ maxTag) ∧
    (decodeValueFromBytes defaultCodecFuel layouts enumTy tBytes = none ↔ maxTag < bits) ∧
    (evalByteCast locals op enumTy mem localDecls layouts =
      ok (.aggregate bits []) locals' mem ↔ bits ≤ maxTag) ∧
    (evalByteCast locals op enumTy mem localDecls layouts = ub ↔ maxTag < bits) := by
  intro enumTy tBytes
  have hMap : tBytes = encodeLittleEndianBytes bits 1 none := by
    unfold tBytes
    rw [map_toTrustedAbstractByte_encodeCastBytes]
    rfl
  have hValidU8 : ScalarTy.u8.validBits .bits64 bits := ⟨hBits, trivial⟩
  have hWidth : primitiveKindByteWidth (.int 8 false) = some l.size.bytes := by
    rw [hSz1]
  have hFieldless' :
      ∀ tag < scalarModulus l.size.bytes,
        wrappingRangeContains ⟨0, maxTag⟩ tag = true →
        ∃ varMemOrder, Trusted.Sequence.get? variantShapes tag = some (.arbitrary [] varMemOrder) := by
    intro tag hTagLt hIn
    rw [hSz1] at hTagLt
    exact hFieldless tag hTagLt hIn
  have ⟨hDecEq, hBcEq⟩ := tryTransmute_adt_multiple_enum_scalarLayout_eq
    locals locals' op mem localDecls layouts .not .bool .u8 srcLIdx defPath args enumLIdx l
    8 bits false ⟨0, maxTag⟩ variantShapes memoryOrder rfl hValidU8 hLookup hInhab hVar hFields
    hSz1 hWidth hFieldless' hOp hTy
  have hWRange := wrappingRangeContains_zero_max_iff maxTag bits
  rw [hMap, hDecEq, hBcEq]
  cases hW : wrappingRangeContains ⟨0, maxTag⟩ bits
  · have hGt : maxTag < bits := by
      have : ¬ (bits ≤ maxTag) := fun hLe => by
        rw [hWRange.mpr hLe] at hW; nomatch hW
      omega
    refine ⟨by simp, ?_, ?_, ?_, ?_⟩ <;> simp [hGt, show ¬ (bits ≤ maxTag) by omega]
  · have hLe : bits ≤ maxTag := hWRange.mp hW
    refine ⟨by simp, ?_, ?_, ?_, ?_⟩ <;> simp [hLe, show ¬ (maxTag < bits) by omega]

/--
**`try_transmute` on the `l.fieldLayouts` single-field wrapper path at the `Trusted` step level.**
When a single-field `.adt defPath args` (`args.length ≠ 1`, in particular `args = []`) has
`l.fields = .arbitrary [⟨0⟩] memoryOrder` and `l.fieldLayouts = [fIdx]` where the inner field layout
`fl` at `fIdx` is a `.primitive` scalar-niche layout (`ScalarLayout.initialized (.int bitsWidth signed) validRange`),
both `decodeValueFromBytes` and `Trusted.MirSemantics.evalByteCast` enforce `validRange`
(producing `.aggregate variantIdx [.scalar ⟨bits, src.sizeBytes .bits64⟩]` iff `wrappingRangeContains validRange bits = true`,
and `none` / `ub` otherwise).
-/
theorem tryTransmute_adt_fieldLayout_inner_primitive_scalarLayout_eq
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (m : Mutability) (pointee : RigidTy) (src : ScalarTy) (srcLIdx : LayoutIdx)
    (defPath : DefPath) (args : List RigidTy) (dstLIdx fIdx : LayoutIdx)
    (l fl : TypeLayout) (variantIdx innerVarIdx bitsWidth bits : Nat) (memoryOrder : List Nat)
    (signed : Bool) (validRange : WrappingRange)
    (hArgsNe1 : Nat.beq (Trusted.Sequence.length args) 1 = false)
    (hSrcNp : src.isPtr = false)
    (hValid : src.validBits .bits64 bits)
    (hLookup : LayoutTable.lookup layouts dstLIdx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hFieldLayouts : l.fieldLayouts = [fIdx])
    (hFLookup : LayoutTable.lookup layouts fIdx = some fl)
    (hFInhab : fl.isUninhabited = false)
    (hFVar : fl.variants = .single innerVarIdx)
    (hFFields : fl.fields = .primitive)
    (hFSz : fl.size.bytes = l.size.bytes)
    (hFRepr : fl.backendRepr = .scalar (.initialized (.int bitsWidth signed) validRange))
    (hLSz : l.size.bytes = src.sizeBytes .bits64)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar ⟨bits, src.sizeBytes .bits64⟩) locals')
    (hTy : operandTy localDecls layouts op =
      some { kind := src.toTrustedRigidTy m pointee, layoutIdx := srcLIdx }) :
    let dstTy : Ty := { kind := .adt defPath args, layoutIdx := dstLIdx }
    decodeValueFromBytes defaultCodecFuel layouts dstTy
        (encodeLittleEndianBytes bits (src.sizeBytes .bits64) none) =
      (match wrappingRangeContains validRange bits with
       | true => some (.aggregate variantIdx [.scalar ⟨bits, src.sizeBytes .bits64⟩])
       | false => none) ∧
    evalByteCast locals op dstTy mem localDecls layouts =
      (match wrappingRangeContains validRange bits with
       | true => ok (.aggregate variantIdx [.scalar ⟨bits, src.sizeBytes .bits64⟩]) locals' mem
       | false => ub) := by
  intro dstTy
  have hNz : Nat.beq l.size.bytes 0 = false := by
    rw [hLSz]
    exact ScalarTy.sizeBytes_bits64_beq_zero src
  have hBits : bits < scalarModulus l.size.bytes := hLSz ▸ hValid.1
  have hDec :
      decodeValueFromBytes defaultCodecFuel layouts dstTy
          (encodeLittleEndianBytes bits (src.sizeBytes .bits64) none) =
        (match wrappingRangeContains validRange bits with
         | true => some (.aggregate variantIdx [.scalar ⟨bits, src.sizeBytes .bits64⟩])
         | false => none) := by
    have h := adt_fieldLayout_path_inner_primitive_scalarLayout_decode_encode_eq
      layouts defPath args dstLIdx fIdx l fl variantIdx innerVarIdx bitsWidth memoryOrder signed
      validRange hArgsNe1 hLookup hInhab hVar hFields hFieldLayouts hFLookup hFInhab hFVar hFFields
      hFSz hFRepr hNz hWidth bits none hBits
    rw [hLSz] at h
    exact h
  have hDstSz : rigidTyByteSize layouts dstTy = some (src.sizeBytes .bits64) := by
    simp [dstTy, rigidTyByteSize, hLookup, hLSz]
  have hSrcSz := ScalarTy.rigidTyByteSize_toTrustedRigidTy_of_not_isPtr layouts m pointee src
    srcLIdx hSrcNp
  have hEnc := trusted_encodeValueToBytes_scalar 15 layouts m pointee src srcLIdx bits hSrcNp hValid
  refine ⟨hDec, ?_⟩
  rw [trusted_evalByteCast_of_encode locals locals' op mem localDecls layouts _ _ dstTy _ _
    hOp hDstSz hTy hSrcSz hEnc (trusted_length_encodeLittleEndianBytes bits _ none), hDec]
  cases wrappingRangeContains validRange bits <;> rfl

/--
**General `Ty`-level `try_transmute` soundness (`evalByteCast_tryTransmute_of_into_tryFrom_bytes`).**
For any `srcTy` satisfying `IsIntoBytes layouts srcTy` and any `dstTy` satisfying
`IsTryFromBytes layouts dstTy validPred` of the same byte size (`rigidTyByteSize layouts srcTy = rigidTyByteSize layouts dstTy`):
whenever `op` evaluates to `v` of type `srcTy` with encoding `encodeValueToBytes defaultCodecFuel layouts srcTy v = some bs`:
1. `evalByteCast locals op dstTy mem localDecls layouts` reduces directly to matching on `decodeValueFromBytes defaultCodecFuel layouts dstTy bs`.
2. Whenever `decodeValueFromBytes defaultCodecFuel layouts dstTy bs = some v'`, `evalByteCast` succeeds with `ok v' locals' mem` AND `validPred v'` holds.
3. `evalByteCast` returns `ub` iff `decodeValueFromBytes defaultCodecFuel layouts dstTy bs = none`.
-/
theorem evalByteCast_tryTransmute_of_into_tryFrom_bytes
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcTy dstTy : Ty) (validPred : Value → Prop)
    (v : Value) (bs : List AbstractByte)
    (hInto : IsIntoBytes layouts srcTy)
    (hTryFrom : IsTryFromBytes layouts dstTy validPred)
    (hSizeEq : rigidTyByteSize layouts srcTy = rigidTyByteSize layouts dstTy)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals = .ok v locals')
    (hTy : operandTy localDecls layouts op = some srcTy)
    (hEnc : encodeValueToBytes defaultCodecFuel layouts srcTy v = some bs) :
    evalByteCast locals op dstTy mem localDecls layouts =
      (match decodeValueFromBytes defaultCodecFuel layouts dstTy bs with
       | some v' => ok v' locals' mem
       | none => ub) ∧
    (∀ v',
      decodeValueFromBytes defaultCodecFuel layouts dstTy bs = some v' →
      evalByteCast locals op dstTy mem localDecls layouts = ok v' locals' mem ∧
      validPred v') ∧
    (evalByteCast locals op dstTy mem localDecls layouts = ub ↔
      decodeValueFromBytes defaultCodecFuel layouts dstTy bs = none) := by
  rcases hInto with ⟨szSrc, hSzSrc, hEncProps⟩
  rcases hTryFrom with ⟨szDst, hSzDst, hTryProps⟩
  have hSzEq : szSrc = szDst := by
    rw [hSzSrc, hSzDst] at hSizeEq
    exact Option.some.inj hSizeEq
  subst hSzEq
  have ⟨hLen, _⟩ := hEncProps v bs hEnc
  have hRed := trusted_evalByteCast_of_encode locals locals' op mem localDecls layouts v srcTy
    dstTy szSrc bs hOp hSzDst hTy hSzSrc hEnc hLen
  refine ⟨hRed, ?_, ?_⟩
  · intro v' hDec
    refine ⟨?_, hTryProps bs v' hDec⟩
    rw [hRed, hDec]
  · rw [hRed]
    cases decodeValueFromBytes defaultCodecFuel layouts dstTy bs <;> simp

/--
**Decidable-certificate corollary (`evalByteCast_tryTransmute_of_checkInto_tryFrom_bytes`).**
Discharges the `IsIntoBytes` source obligation of `evalByteCast_tryTransmute_of_into_tryFrom_bytes`
from `checkIntoBytes layouts srcTy = true`.
-/
theorem evalByteCast_tryTransmute_of_checkInto_tryFrom_bytes
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcTy dstTy : Ty) (validPred : Value → Prop)
    (v : Value) (bs : List AbstractByte)
    (hCheckInto : checkIntoBytes layouts srcTy = true)
    (hTryFrom : IsTryFromBytes layouts dstTy validPred)
    (hSizeEq : rigidTyByteSize layouts srcTy = rigidTyByteSize layouts dstTy)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals = .ok v locals')
    (hTy : operandTy localDecls layouts op = some srcTy)
    (hEnc : encodeValueToBytes defaultCodecFuel layouts srcTy v = some bs) :
    evalByteCast locals op dstTy mem localDecls layouts =
      (match decodeValueFromBytes defaultCodecFuel layouts dstTy bs with
       | some v' => ok v' locals' mem
       | none => ub) ∧
    (∀ v',
      decodeValueFromBytes defaultCodecFuel layouts dstTy bs = some v' →
      evalByteCast locals op dstTy mem localDecls layouts = ok v' locals' mem ∧
      validPred v') ∧
    (evalByteCast locals op dstTy mem localDecls layouts = ub ↔
      decodeValueFromBytes defaultCodecFuel layouts dstTy bs = none) :=
  evalByteCast_tryTransmute_of_into_tryFrom_bytes locals locals' op mem localDecls layouts
    srcTy dstTy validPred v bs (checkIntoBytes_sound layouts srcTy hCheckInto)
    hTryFrom hSizeEq hOp hTy hEnc

/--
**Safe `IntoBytes -> FromBytes` transmute from a `.primitive` ADT into a same-width integral scalar (`evalByteCast_adt_primitive_to_scalar_ok`).**
Transmuting any `.scalar ⟨bits, dst.sizeBytes .bits64⟩` (`bits < scalarModulus (dst.sizeBytes .bits64)`)
of an inhabited single-variant `.primitive` ADT into a same-width integral scalar `dst`
(`dst.isIntegral = true`) via `Trusted.MirSemantics.evalByteCast` always succeeds and preserves the
bit pattern (`ok (.scalar ⟨bits, dst.sizeBytes .bits64⟩) locals' mem`). The `Trusted` encoder does
not check the source layout's scalar niche, so this holds even for bit patterns outside it. For
captured `NonZero<T>` and enum layouts (`.arbitrary` / `.multiple`), use the general
`evalByteCast_ok_of_into_from_bytes` with the corresponding `IsIntoBytes` theorem.
-/
theorem evalByteCast_adt_primitive_to_scalar_ok
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (defPath : DefPath) (args : List RigidTy) (srcLIdx dstLIdx : LayoutIdx)
    (l : TypeLayout) (variantIdx bits : Nat)
    (m : Mutability) (pointee : RigidTy) (dst : ScalarTy)
    (hDstInt : dst.isIntegral = true)
    (hBits : bits < scalarModulus (dst.sizeBytes .bits64))
    (hLookup : LayoutTable.lookup layouts srcLIdx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hLSz : l.size.bytes = dst.sizeBytes .bits64)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar ⟨bits, dst.sizeBytes .bits64⟩) locals')
    (hTy : operandTy localDecls layouts op =
      some { kind := .adt defPath args, layoutIdx := srcLIdx }) :
    let dstTy : Ty := { kind := dst.toTrustedRigidTy m pointee, layoutIdx := dstLIdx }
    evalByteCast locals op dstTy mem localDecls layouts =
      ok (.scalar ⟨bits, dst.sizeBytes .bits64⟩) locals' mem := by
  intro dstTy
  let srcTy : Ty := { kind := .adt defPath args, layoutIdx := srcLIdx }
  have hDstNp : dst.isPtr = false := ScalarTy.isPtr_eq_false_of_isIntegral dst hDstInt
  have hSrcSz : rigidTyByteSize layouts srcTy = some (dst.sizeBytes .bits64) := by
    simp [srcTy, rigidTyByteSize, hLookup, hLSz]
  have hDstSz : rigidTyByteSize layouts dstTy = some (dst.sizeBytes .bits64) :=
    ScalarTy.rigidTyByteSize_toTrustedRigidTy_of_not_isPtr layouts m pointee dst dstLIdx hDstNp
  have hNz : Nat.beq (dst.sizeBytes .bits64) 0 = false :=
    ScalarTy.sizeBytes_bits64_beq_zero dst
  have hEnc :
      encodeValueToBytes defaultCodecFuel layouts srcTy (.scalar ⟨bits, dst.sizeBytes .bits64⟩) =
        some (encodeLittleEndianBytes bits (dst.sizeBytes .bits64) none) := by
    unfold defaultCodecFuel encodeValueToBytes
    dsimp only [srcTy]
    rw [hLookup]
    dsimp only
    rw [hInhab, hVar, hFields, hLSz]
    dsimp only
    rw [Nat.beq_refl]
    unfold encodeScalarBytes
    dsimp only
    rw [hNz]
  have hValidDst : dst.isValidBits .bits64 bits = true :=
    ScalarTy.isValidBits_of_isIntegral .bits64 dst bits hDstInt hBits
  rw [trusted_evalByteCast_of_encode locals locals' op mem localDecls layouts _ srcTy dstTy _ _
        hOp hDstSz hTy hSrcSz hEnc (trusted_length_encodeLittleEndianBytes bits _ none),
      show defaultCodecFuel = 15 + 1 from rfl,
      trusted_decodeValueFromBytes_scalar 15 layouts m pointee dst dstLIdx bits hDstNp hBits,
      hValidDst]

/--
**Safe `IntoBytes -> FromBytes` transmute from a multi-variant fieldless `#[repr(Int)]` / `#[repr(u8)]` enum (`VariantsShape.multiple`) into a same-width integral scalar (`evalByteCast_adt_multiple_enum_to_scalar_ok`).**
Transmuting `.aggregate varIdx []` (`varIdx < scalarModulus (dst.sizeBytes .bits64)`) of a
fieldless `.multiple` enum (where variant `varIdx` has empty field offsets `.arbitrary [] varMemOrder`)
into a same-width integral scalar `dst` (`dst.isIntegral = true`, e.g. `#[repr(u8)] Enum -> u8`)
via `Trusted.MirSemantics.evalByteCast` succeeds and produces `ok (.scalar ⟨varIdx, dst.sizeBytes .bits64⟩) locals' mem`.
-/
theorem evalByteCast_adt_multiple_enum_to_scalar_ok
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (defPath : DefPath) (args : List RigidTy) (srcLIdx dstLIdx : LayoutIdx)
    (l : TypeLayout) (bitsWidth varIdx : Nat) (signed : Bool) (validRange : WrappingRange)
    (variantShapes : List FieldsShape) (memoryOrder varMemOrder : List Nat)
    (m : Mutability) (pointee : RigidTy) (dst : ScalarTy)
    (hDstInt : dst.isIntegral = true)
    (hVarLt : varIdx < scalarModulus (dst.sizeBytes .bits64))
    (hInRange : wrappingRangeContains validRange varIdx = true)
    (hLookup : LayoutTable.lookup layouts srcLIdx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .multiple (.initialized (.int bitsWidth signed) validRange) 0 variantShapes)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hLSz : l.size.bytes = dst.sizeBytes .bits64)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes)
    (hGetVar : Trusted.Sequence.get? variantShapes varIdx = some (.arbitrary [] varMemOrder))
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.aggregate varIdx []) locals')
    (hTy : operandTy localDecls layouts op =
      some { kind := .adt defPath args, layoutIdx := srcLIdx }) :
    let dstTy : Ty := { kind := dst.toTrustedRigidTy m pointee, layoutIdx := dstLIdx }
    evalByteCast locals op dstTy mem localDecls layouts =
      ok (.scalar ⟨varIdx, dst.sizeBytes .bits64⟩) locals' mem := by
  intro dstTy
  let srcTy : Ty := { kind := .adt defPath args, layoutIdx := srcLIdx }
  have hDstNp : dst.isPtr = false := ScalarTy.isPtr_eq_false_of_isIntegral dst hDstInt
  have hSrcSz : rigidTyByteSize layouts srcTy = some (dst.sizeBytes .bits64) := by
    simp [srcTy, rigidTyByteSize, hLookup, hLSz]
  have hDstSz : rigidTyByteSize layouts dstTy = some (dst.sizeBytes .bits64) :=
    ScalarTy.rigidTyByteSize_toTrustedRigidTy_of_not_isPtr layouts m pointee dst dstLIdx hDstNp
  have hNz : Nat.beq l.size.bytes 0 = false := by
    rw [hLSz]
    exact ScalarTy.sizeBytes_bits64_beq_zero dst
  have hVarLtL : varIdx < scalarModulus l.size.bytes := hLSz ▸ hVarLt
  have hEnc :
      encodeValueToBytes defaultCodecFuel layouts srcTy (.aggregate varIdx []) =
        some (encodeLittleEndianBytes varIdx (dst.sizeBytes .bits64) none) := by
    have hRt := (adt_multiple_enum_encode_decode_roundtrip layouts defPath args srcLIdx l
      bitsWidth varIdx signed validRange variantShapes memoryOrder varMemOrder
      hLookup hInhab hVar hFields hNz hWidth hVarLtL hInRange hGetVar).1
    rw [hLSz] at hRt
    exact hRt
  have hValidDst : dst.isValidBits .bits64 varIdx = true :=
    ScalarTy.isValidBits_of_isIntegral .bits64 dst varIdx hDstInt hVarLt
  rw [trusted_evalByteCast_of_encode locals locals' op mem localDecls layouts _ srcTy dstTy _ _
        hOp hDstSz hTy hSrcSz hEnc (trusted_length_encodeLittleEndianBytes varIdx _ none),
      show defaultCodecFuel = 15 + 1 from rfl,
      trusted_decodeValueFromBytes_scalar 15 layouts m pointee dst dstLIdx varIdx hDstNp hVarLt,
      hValidDst]

/--
**Niche-aware decidable-certificate corollary (`evalByteCast_ok_of_checkIntoFromBytesNicheAware`).**
Discharges `Trusted.MirSemantics.evalByteCast` from `checkIntoBytes layouts srcTy = true`
and `checkFromBytesNicheAware layouts dstTy = true`, guaranteeing both `Trusted`
transmute soundness and absence of any scalar `validRange` niche on `dstTy`'s
backend representation.
-/
theorem evalByteCast_ok_of_checkIntoFromBytesNicheAware
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcTy dstTy : Ty) (v : Value) (bs : List AbstractByte)
    (hCheckInto : checkIntoBytes layouts srcTy = true)
    (hCheckFrom : checkFromBytesNicheAware layouts dstTy = true)
    (hSizeEq : rigidTyByteSize layouts srcTy = rigidTyByteSize layouts dstTy)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals = .ok v locals')
    (hTy : operandTy localDecls layouts op = some srcTy)
    (hEnc : encodeValueToBytes defaultCodecFuel layouts srcTy v = some bs) :
    ∃ v',
      decodeValueFromBytes defaultCodecFuel layouts dstTy bs = some v' ∧
      evalByteCast locals op dstTy mem localDecls layouts = ok v' locals' mem ∧
      evalRvalue locals (.cast .transmute op dstTy) mem localDecls layouts = ok v' locals' mem :=
  evalByteCast_ok_of_into_from_bytes locals locals' op mem localDecls layouts srcTy dstTy v bs
    (checkIntoBytes_sound layouts srcTy hCheckInto)
    (checkFromBytesNicheAware_sound layouts dstTy hCheckFrom)
    hSizeEq hOp hTy hEnc

end Anneal.Mir.Cast
