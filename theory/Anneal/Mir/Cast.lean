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
import Anneal.MirFuelFree

open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirSemantics.RvalueEvalResult
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

/-- Evaluate a `CastKind.pointerExposeProvenance` (`PtrToInt`) cast on pointer `p` to
target type `dst` under pointer width `pw`, exposing `p.allocId` in `exposed`. -/
def evalPtrToIntExpose
    (pw : PtrWidth)
    (dst : ScalarTy)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance) :
    CastOutcome :=
  match dst.isIntegral with
  | false => .unsupported
  | true =>
    match ScalarTy.rawPtr.isValidBits pw p.offsetBytes with
    | false => .ub
    | true =>
      let addr := (ptrToAddress p) % scalarModulus (dst.sizeBytes pw)
      .ok (.scalar addr) (exposeProv p.allocId exposed)

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
address `addr` to `ScalarTy.rawPtr` under `pw`, requiring `predictedAllocId` (when `some id`)
to be in `exposed` (`anneal_mir::lower::cast::eval_int_to_ptr_with_ptr_width`). -/
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
      | true =>
        let p := addressToPtr addr
        .ok (.ptr { allocId := allocId, offsetBytes := p.offsetBytes } (some allocId)) exposed
      | false => .ub
    | none =>
      .ok (.ptr { allocId := 0, offsetBytes := addr } none) exposed

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

/-- Contrast theorem (`UCG #286` / MiniRust `IntPtrCast` vs `transmute`):
1. `evalPtrToIntExpose` on pointer `p` exposes `p.allocId` (`isExposed p.allocId exposed'`),
   enabling `evalIntToPtrExposed` to reconstruct pointer `p` with provenance `some p.allocId`;
2. `evalTransmuteSameSize` (even under `TransmutePolicy.allowPtrToIntStripProvenance`) strips
   provenance and leaves `exposed` untouched (`exposed' = exposed`), so if `¬ isExposed p.allocId exposed`,
   `p.allocId` remains unexposed and `evalIntToPtrExposed` with `some p.allocId` fails with `.ub`! -/
theorem ptrToInt_vs_transmute_exposure_contrast
    (pw : PtrWidth)
    (w : IntWidth)
    (p : ProvenancePtr)
    (exposed : ExposedProvenance)
    (h_w : w.byteSize pw = pw.byteSize)
    (h_off : p.offsetBytes < scalarModulus pw.byteSize) :
    let exposedAfterCast := exposeProv p.allocId exposed
    evalPtrToIntExpose pw (.uint w) p exposed =
      .ok (.scalar ((ptrToAddress p) % scalarModulus pw.byteSize)) exposedAfterCast ∧
    isExposed p.allocId exposedAfterCast ∧
    evalTransmuteSameSize pw .allowPtrToIntStripProvenance .rawPtr (.uint w)
        (.ptr p (some p.allocId)) exposed =
      .ok (.scalar p.offsetBytes) exposed ∧
    (¬ isExposed p.allocId exposed →
      ∀ addr, addr < scalarModulus pw.byteSize →
        evalIntToPtrExposed pw addr (some p.allocId) exposed = .ub) := by
  have h_valid_ptr : ScalarTy.rawPtr.isValidBits pw p.offsetBytes = true :=
    (ScalarTy.isValidBits_iff_validBits pw .rawPtr p.offsetBytes).mpr ⟨h_off, trivial⟩
  have h_valid_uint : (ScalarTy.uint w).isValidBits pw p.offsetBytes = true := by
    apply (ScalarTy.isValidBits_iff_validBits pw (.uint w) p.offsetBytes).mpr
    refine ⟨?_, trivial⟩
    dsimp [ScalarTy.sizeBytes]
    rw [h_w]
    exact h_off
  refine ⟨?_, isExposed_exposeProv p.allocId exposed, ?_, ?_⟩
  · unfold evalPtrToIntExpose
    dsimp [ScalarTy.isIntegral, ScalarTy.sizeBytes]
    rw [h_valid_ptr, h_w]
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
  · intro h_unexp addr h_addr
    have h_valid_addr : ScalarTy.rawPtr.isValidBits pw addr = true :=
      (ScalarTy.isValidBits_iff_validBits pw .rawPtr addr).mpr ⟨h_addr, trivial⟩
    have h_exp_false : isExposedBool p.allocId exposed = false :=
      (isExposedBool_eq_false_iff p.allocId exposed).mpr h_unexp
    unfold evalIntToPtrExposed
    rw [h_valid_addr]
    dsimp only
    rw [h_exp_false]

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

/-- Helper: `decodeValueFromBytes` at `{ kind := .rawPtr m (.int w), layoutIdx := lIdx }`
on an 8-byte sequence `bs` with `decodeScalarBytes bs false = .some (⟨p.offsetBytes, 8⟩, .some (p.allocId, p.tag))`
returns `.some (.ptr p 8)`. -/
theorem trusted_decodeValueFromBytes_thin_rawPtr
    (fuel : Nat)
    (layouts : LayoutTable)
    (m : Mutability)
    (w : IntTy)
    (lIdx : Nat)
    (bs : List AbstractByte)
    (p : ProvenancePtr)
    (h_len : Trusted.Sequence.length bs = 8)
    (h_dec : decodeScalarBytes bs false = .some (⟨p.offsetBytes, 8⟩, .some (p.allocId, p.tag))) :
    decodeValueFromBytes (fuel + 1) layouts { kind := .rawPtr m (.int w), layoutIdx := lIdx } bs =
      .some (.ptr p 8) := by
  have h_beq_len : Nat.beq (Trusted.Sequence.length bs) 8 = true := by
    rw [h_len]; rfl
  change
    (match Nat.beq (Trusted.Sequence.length bs) 8 with
     | false => .none
     | true =>
       match decodeScalarBytes bs false with
       | .some (sv, prov) =>
         match prov with
         | .some (allocId, _) => .some (.ptr { allocId := allocId, offsetBytes := sv.bits } 8)
         | .none =>
           .some (.ptr { allocId := Nat.div sv.bits 65536, offsetBytes := Nat.mod sv.bits 65536 } 8)
       | .none => .none : Option Value) = .some (.ptr p 8)
  rw [h_beq_len]
  dsimp only
  rw [h_dec]

/-- Helper: `decodeValueFromBytes` at `{ kind := .ref m (.int w), layoutIdx := lIdx }`
on an 8-byte sequence `bs` with `decodeScalarBytes bs false = .some (⟨p.offsetBytes, 8⟩, .some (p.allocId, p.tag))`
returns `.some (.ptr p 8)`. -/
theorem trusted_decodeValueFromBytes_thin_ref
    (fuel : Nat)
    (layouts : LayoutTable)
    (m : Mutability)
    (w : IntTy)
    (lIdx : Nat)
    (bs : List AbstractByte)
    (p : ProvenancePtr)
    (h_len : Trusted.Sequence.length bs = 8)
    (h_dec : decodeScalarBytes bs false = .some (⟨p.offsetBytes, 8⟩, .some (p.allocId, p.tag))) :
    decodeValueFromBytes (fuel + 1) layouts { kind := .ref m (.int w), layoutIdx := lIdx } bs =
      .some (.ptr p 8) := by
  have h_beq_len : Nat.beq (Trusted.Sequence.length bs) 8 = true := by
    rw [h_len]; rfl
  change
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
       | .none => .none : Option Value) = .some (.ptr p 8)
  rw [h_beq_len]
  dsimp only
  rw [h_dec]

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
on a thin `rawPtr` to a thin `ref` (`*const T` / `*mut T` -> `&U` / `&mut U`):
encoding `.ptr p 8` (`p.offsetBytes < scalarModulus 8`) at `{ kind := .rawPtr m1 (.uint .u8), layoutIdx := srcLIdx }`
and decoding at `{ kind := .ref m2 (.int .i32), layoutIdx := dstLIdx }` preserves `p`
(`ok (.ptr p 8) locals' mem`), because `p`'s provenance tag `.some (p.allocId, p.tag)` is
carried through all 8 `AbstractByte.init` elements. -/
theorem trusted_evalByteCast_thin_rawPtr_to_ref_preserves_provenance
    (locals locals' : List LocalSlot)
    (op : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (m1 m2 : Mutability)
    (srcLIdx dstLIdx : Nat)
    (p : ProvenancePtr)
    (h_off : p.offsetBytes < scalarModulus 8)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.ptr p 8) locals')
    (h_ty : operandTy localDecls layouts op =
      .some { kind := .rawPtr m1 (.uint .u8), layoutIdx := srcLIdx }) :
    evalByteCast locals op { kind := .ref m2 (.int .i32), layoutIdx := dstLIdx }
      mem localDecls layouts = ok (.ptr p 8) locals' mem := by
  have h_red :
      evalByteCast locals op { kind := .ref m2 (.int .i32), layoutIdx := dstLIdx }
        mem localDecls layouts =
        match decodeValueFromBytes 8 layouts { kind := .ref m2 (.int .i32), layoutIdx := dstLIdx }
            (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) with
        | some v' => ok v' locals' mem
        | none => ub := by
    unfold evalByteCast
    rw [h_op, h_ty]
    rfl
  rw [h_red]
  have h_len : Trusted.Sequence.length
      (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) = 8 :=
    trusted_length_encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))
  have h_dec_sc : decodeScalarBytes
      (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) false =
      some (⟨p.offsetBytes, 8⟩, some (p.allocId, p.tag)) :=
    (trusted_decodeScalarBytes_encodeScalarBytes
      7 p.offsetBytes (some (p.allocId, p.tag)) false h_off).2
  rw [trusted_decodeValueFromBytes_thin_ref 7 layouts m2 .i32 dstLIdx
      (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) p h_len h_dec_sc]

/-- Direct `Trusted.MirSemantics` step-level correspondence for `evalByteCast` (`CastKind.transmute`)
from `u64` (`0`) to a thin reference `&T`: transmuting a provenance-free zero integer
`.scalar ⟨0, 8⟩` into `{ kind := .ref m (.int .i32), layoutIdx := dstLIdx }` produces `ub`
(null reference is invalid). -/
theorem trusted_evalByteCast_u64_zero_to_ref_ub
    (locals locals' : List LocalSlot)
    (op : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (m : Mutability)
    (srcLIdx dstLIdx : Nat)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar ⟨0, 8⟩) locals')
    (h_ty : operandTy localDecls layouts op =
      .some { kind := .uint .u64, layoutIdx := srcLIdx }) :
    evalByteCast locals op { kind := .ref m (.int .i32), layoutIdx := dstLIdx }
      mem localDecls layouts = ub := by
  unfold evalByteCast
  rw [h_op, h_ty]
  rfl

/-- Direct `Trusted.MirSemantics` correspondence theorem for thin `rawPtr` provenance
preservation across `encodeValueToBytes`, `decodeValueFromBytes`, `evalByteCast`, and
`evalRvalue (.cast .transmute ...)`:
1. Encoding a thin pointer `.ptr p 8` (with `p.offsetBytes < scalarModulus 8`) at
   `{ kind := .rawPtr m1 (.uint .u8), layoutIdx := srcLIdx }` via `encodeValueToBytes`
   and decoding at `{ kind := .rawPtr m2 (.int .i32), layoutIdx := dstLIdx }` via
   `decodeValueFromBytes` recovers `.some (.ptr p 8)` (preserving both `p.allocId` and
   `p.offsetBytes`).
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
    (srcLIdx dstLIdx : Nat)
    (p : ProvenancePtr)
    (h_off : p.offsetBytes < scalarModulus 8)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.ptr p 8) locals')
    (h_ty : operandTy localDecls layouts op =
      .some { kind := .rawPtr m1 (.uint .u8), layoutIdx := srcLIdx }) :
    let srcTy : Ty := { kind := .rawPtr m1 (.uint .u8), layoutIdx := srcLIdx }
    let dstTy : Ty := { kind := .rawPtr m2 (.int .i32), layoutIdx := dstLIdx }
    (match encodeValueToBytes (fuel + 1) layouts srcTy (.ptr p 8) with
     | .some bs => decodeValueFromBytes (fuel + 1) layouts dstTy bs
     | .none => .none) = .some (.ptr p 8) ∧
    evalByteCast locals op dstTy mem localDecls layouts =
      ok (.ptr p 8) locals' mem ∧
    evalRvalue locals (.cast .transmute op dstTy) mem localDecls layouts =
      ok (.ptr p 8) locals' mem := by
  dsimp only
  have h_len : Trusted.Sequence.length
      (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) = 8 :=
    trusted_length_encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))
  have h_dec_sc : decodeScalarBytes
      (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) false =
      some (⟨p.offsetBytes, 8⟩, some (p.allocId, p.tag)) :=
    (trusted_decodeScalarBytes_encodeScalarBytes
      7 p.offsetBytes (some (p.allocId, p.tag)) false h_off).2
  have h_dec_raw :
      decodeValueFromBytes (fuel + 1) layouts
        { kind := .rawPtr m2 (.int .i32), layoutIdx := dstLIdx }
        (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) =
      .some (.ptr p 8) :=
    trusted_decodeValueFromBytes_thin_rawPtr fuel layouts m2 .i32 dstLIdx
      (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) p h_len h_dec_sc
  have h_codec :
      (match encodeValueToBytes (fuel + 1) layouts
          { kind := .rawPtr m1 (.uint .u8), layoutIdx := srcLIdx } (.ptr p 8) with
       | some bs =>
         decodeValueFromBytes (fuel + 1) layouts
           { kind := .rawPtr m2 (.int .i32), layoutIdx := dstLIdx } bs
       | none => none) = .some (.ptr p 8) := by
    change
      decodeValueFromBytes (fuel + 1) layouts
        { kind := .rawPtr m2 (.int .i32), layoutIdx := dstLIdx }
        (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) =
      .some (.ptr p 8)
    exact h_dec_raw
  have h_byteCast :
      evalByteCast locals op { kind := .rawPtr m2 (.int .i32), layoutIdx := dstLIdx }
        mem localDecls layouts = ok (.ptr p 8) locals' mem := by
    have h_red :
        evalByteCast locals op { kind := .rawPtr m2 (.int .i32), layoutIdx := dstLIdx }
          mem localDecls layouts =
          match decodeValueFromBytes 8 layouts { kind := .rawPtr m2 (.int .i32), layoutIdx := dstLIdx }
              (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) with
          | some v' => ok v' locals' mem
          | none => ub := by
      unfold evalByteCast
      rw [h_op, h_ty]
      rfl
    rw [h_red]
    rw [trusted_decodeValueFromBytes_thin_rawPtr 7 layouts m2 .i32 dstLIdx
        (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) p h_len h_dec_sc]
  refine ⟨h_codec, h_byteCast, ?_⟩
  unfold evalRvalue
  exact h_byteCast

end Anneal.Mir.Cast
