/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.Translate
import Trusted.MirSemantics
import Trusted.VerificationResult

/-!
# `Rvalue.nullaryOp` and `CastKind.fnPtrToPtr` ↔ MiniRust

Symbolic correspondence between Trusted's MIR semantics
(`Trusted.Rustc.V2026_06_01.MirSemantics`, `Places.lean`) and MiniRust (`MiniRustSpec.Interp`, on
`Mach = Machine<BasicMemory>` and on every `Machine M`, in particular
`MachTB = Machine<TreeBorrowsMemory>`) for two MIR constructs that lie outside the translated
fragment (`translateRvalue` returns `none` for both), so that their agreement is stated directly on
the two evaluators rather than through the simulation.

This module imports only `Correspondence.Translate`, `Trusted.MirSemantics`, and
`Trusted.VerificationResult`; it does not import `Anneal.*` or any other correspondence module.

## A. `Rvalue.nullaryOp` (`evalNullaryOp`) ↔ `Type::layout`, tuple field offsets, `ub_checks`

Trusted reads layouts from two sources: primitive sizes and alignments by type constructor
(`rigidTyKindByteSize`, `intrinsicRigidTyKindAlign`), and, for tuples and ADTs, the `TypeLayout` of
a *local declaration of the same kind* (`findDeclLayoutForRigidTy`), with a structural fallback for
layout-free tuples. `minimize` reads `rustc`'s layout of the type itself, which `translateTy` takes
from the `ty.layoutIdx` entry (or from the fixed ABI of `core::cmp::Ordering`, `(Int, bool)`, and
`Box<T>`). `DeclLayoutCoherent` states that the two sources agree for an aggregate type (it is
vacuous for every other type, `declLayoutCoherent_of_nonAggregate`, and follows from the raw table
fact that the declaration scan finds the `ty.layoutIdx` entry,
`declLayoutCoherent_of_same_entry`).

* **A0** `evalNullaryOp_sizeOf_eq`, `evalNullaryOp_alignOf_eq`, `evalNullaryOp_offsetOf_eq`
  (normal forms), `evalNullaryOp_ne_ub` (never UB), `evalNullaryOp_ok_state` (state unchanged).
* **A1 `SizeOf`** `translateTy_layout_agrees` (key lemma), `nullaryOp_sizeOf_minirust_layout`,
  `nullaryOp_sizeOf_ok_iff`, `nullaryOp_sizeOf_unsupported_iff`: for every translated type,
  Trusted returns `sz` iff MiniRust's `Type::layout` is `Sized(sz, _)` and `sz ≤ isize::MAX`
  (`Target::valid_size`), and is `.unsupported` exactly otherwise.
* **A2 `AlignOf`** `nullaryOp_alignOf_minirust_layout`, `nullaryOp_alignOf_ok_iff`: the same
  against the alignment of `Type::layout` (a power of two below `2^64`).
* **A3 `OffsetOf`** `nullaryOp_offsetOf_field_minirust` (single field = the MiniRust tuple field
  offset `sized_fields[i].0`, `mrFieldOffset?`), `nullaryOp_offsetOf_path_minirust` (nested paths
  = the sum of the nested MiniRust offsets, `mrPathOffset?`),
  `nullaryOp_offsetOf_field_out_of_range`, `nullaryOp_offsetOf_variant_ne_zero_unsupported`.
* **A4 `UbChecks`** `nullaryOp_ubChecks_ok_iff`, `nullaryOp_ubChecks_nonBool_unsupported`,
  `nullaryOp_ubChecks_minirust`, `ubChecks_minirustM`, `ubChecks_agrees_iff_session_flag`.
* **A5 `ContractChecks`** `nullaryOp_contractChecks_unsupported`,
  `nullaryOp_contractChecks_minirust_contrast`.

Divergences, proved as named theorems: `sizeOf_divergence_size_not_multiple_of_align` and
`sizeOf_divergence_layoutIdx_ignored` (on layout tables that are not coherent the two sizes
differ: Trusted reads a declaration's layout and never `argTy.layoutIdx`, and does not round the
recorded size up to the alignment), `sizeOf_unsupported_without_decl` (an ADT that is not the type
of any local is `.unsupported` in Trusted although MiniRust has a layout),
`ubChecks_agrees_iff_session_flag` (Trusted models `ub_checks = true` only), and
`nullaryOp_contractChecks_minirust_contrast` (`minimize` resolves the contract-check flag to a
session constant; Trusted fails closed).

## B. `CastKind.fnPtrToPtr` (`evalFnPtrToPtr`) ↔ `Transmute` from `PtrType::FnPtr`

`minimize` translates `FnPtrToPtr` to `build::transmute(operand, ty)` with operand type
`Type::Ptr(PtrType::FnPtr)` and, for a thin raw-pointer target, target type
`Type::Ptr(PtrType::Raw { meta_kind: None })` (`translateTy_thinRawPtr`).

* **B1 MiniRust** `evalUnOp_fnPtrToPtr_ok` / `evalUnOpM_fnPtrToPtr_ok` (the transmute returns the
  same pointer: address, provenance, no metadata), `_oob_specPanic`, `_wide_specPanic`,
  `_ok_iff` (two-sided against `check_value` at `FnPtr`), `checkValue_fnPtr_ok_iff`,
  `fnFromPtr_thin_eq`, `fnFromPtr_unregistered_ub`, `fnFromPtr_wide_ub`,
  `fnFromPtr_after_fnPtrToPtr`, each on `Mach` and (suffix `M`) on every `Machine M`.
* **B2 Trusted** `evalRvalue_fnPtrToPtr_ok_iff` (two-sided), `evalRvalue_fnPtrToPtr_ptr_ok_iff`,
  `evalRvalue_fnPtrToPtr_ptr_ub_iff`, `evalRvalue_fnPtrToPtr_unsupported_iff`, and the `.ub`
  corollaries `_nonPtr_ub`, `_borrowed_ub`, `_unregistered_ub`, `_nonThinTarget_ub`.
* **B3 relation** `FnPtrRel`, `fnPtrToPtr_preserves_FnPtrRel` (and `_mach`),
  `FnPtrRel.trusted_cast_ok`, `FnPtrRel.minirust_cast_ok`, `FnPtrRel.fnFromPtrM_eq`,
  `trusted_ub_not_FnPtrRel`, `borrowed_not_FnPtrRel`.
* **B4 witnesses** `wit_trusted_reify`, `wit_trusted_fnPtrToPtr_ok`, `wit_mach_lockstep`,
  `wit_machTB_lockstep`, `wit_FnPtrRel`, `wit_lockstep_preserved`, `wit_trusted_borrowed_ub`,
  `wit_minirust_data_pointer`, `wit_fnPtrToPtr_body_reachRet`.

Divergence, proved as `fnPtrToPtr_data_pointer_divergence`: Trusted raises UB *at the cast* when
the operand is not a registered function pointer (a borrow-backed data pointer); MiniRust's
transmute succeeds on every in-bounds thin pointer and raises UB only when the pointer is used as
a function (`Machine::fn_from_ptr`). The two agree on `.ok` and every Trusted `.ub` operand is
unrelated to any MiniRust function pointer, but there is no cast-level UB parity.
-/

namespace MiniRustSpec.Correspondence.NullaryFnPtrBridge

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp
open Trusted.Sequence

/-! ## Shared helpers -/

private theorem okBind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

private theorem errorBind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    ((Except.error e : Except ε α) >>= f) = .error e := rfl

private theorem pureOk {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

private theorem ifPos {c : Prop} [Decidable c] {α : Type} {t e : α} (h : c) :
    (if c then t else e) = t := by
  simp [h]

private theorem ifNeg {c : Prop} [Decidable c] {α : Type} {t e : α} (h : ¬ c) :
    (if c then t else e) = e := by
  simp [h]

private theorem expectSize_sized (sz : Size) (al : Align) (msg : String) :
    LayoutStrategy.expect_size (.Sized sz al) msg = .ok sz := rfl

private theorem expectAlign_sized (sz : Size) (al : Align) (msg : String) :
    LayoutStrategy.expect_align (.Sized sz al) msg = .ok al := rfl

private theorem ensureElseUb_true (msg : String) : ensureElseUb true msg = .ok () := rfl

private theorem ensureElseUb_false (msg : String) :
    ensureElseUb false msg = .error (.ub msg) := rfl

private theorem size_ne_self_ite {α : Type} (s : Size) (t e : α) :
    (if s ≠ s then t else e) = e := by
  split
  · next h => exact absurd rfl h
  · rfl

private theorem leBytes_length (u k : Nat) : (leBytes u k).length = k := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]

private theorem leValue_leBytes (u k : Nat) : leValue (leBytes u k) = u % 256 ^ k := by
  induction k generalizing u with
  | zero => simp [leBytes, leValue, Nat.mod_one]
  | succ k ih =>
    simp only [leBytes, leValue, ih, UInt8.toNat_ofNat']
    have e1 : u % 256 % 2 ^ 8 = u % 256 := Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))
    rw [e1, show (256 : Nat) ^ (k + 1) = 256 * 256 ^ k by rw [Nat.pow_succ, Nat.mul_comm],
      Nat.mod_mul]

private theorem two_pow_ptrBits :
    (2 : Int) ^ Size.bits x86_64.PTR_SIZE = 18446744073709551616 := by
  decide

/-! ## B. `CastKind.fnPtrToPtr` -/

/-! ### B1. MiniRust: `Transmute` from `PtrType::FnPtr` to `PtrType::Raw { meta_kind: None }` -/

/-- `Int::in_bounds(Unsigned, PTR_SIZE)` on `x86_64`: the address lies in `[0, 2^64)`. -/
theorem inBounds_usize_iff (i : Int) :
    inBounds i .Unsigned x86_64.PTR_SIZE = true ↔ 0 ≤ i ∧ i < 18446744073709551616 := by
  simp only [inBounds, two_pow_ptrBits, Bool.and_eq_true, decide_eq_true_eq]

private theorem encode_usize (addr : Int)
    (h : inBounds addr .Unsigned x86_64.PTR_SIZE = true) :
    Endianness.encode x86_64.ENDIANNESS .Unsigned x86_64.PTR_SIZE addr =
      some (leBytes addr.toNat 8) := by
  have hb := (inBounds_usize_iff addr).mp h
  have hmod : (addr % (2 : Int) ^ Size.bits x86_64.PTR_SIZE).toNat = addr.toNat := by
    rw [two_pow_ptrBits, Int.emod_eq_of_lt hb.1 hb.2]
  unfold Endianness.encode
  simp only [h, ↓reduceIte, hmod]
  rfl

private theorem encode_usize_oob (addr : Int)
    (h : inBounds addr .Unsigned x86_64.PTR_SIZE = false) :
    Endianness.encode x86_64.ENDIANNESS .Unsigned x86_64.PTR_SIZE addr = none := by
  unfold Endianness.encode
  rw [h]
  rfl

private theorem decode_usize (addr : Int)
    (h : inBounds addr .Unsigned x86_64.PTR_SIZE = true) :
    Endianness.decode x86_64.ENDIANNESS .Unsigned (leBytes addr.toNat 8) = addr := by
  have hb := (inBounds_usize_iff addr).mp h
  have h256 : addr.toNat < 256 ^ 8 := by
    have : (256 : Nat) ^ 8 = 18446744073709551616 := by decide
    omega
  simp only [Endianness.decode, x86_64.ENDIANNESS, leValue_leBytes, Nat.mod_eq_of_lt h256]
  omega

/-! #### `Mach` (`BasicMemory`) -/

private theorem encodePtrBytes_data (prov : Option Prov) (i : Nat) (data : List UInt8) :
    (encodePtrBytes prov i data).mapM AbstractByte.data = some data := by
  induction data generalizing i with
  | nil => rfl
  | cons b rest ih => simp [encodePtrBytes, AbstractByte.data, ih]

private theorem encodePtrBytes_length (prov : Option Prov) (i : Nat) (data : List UInt8) :
    (encodePtrBytes prov i data).length = data.length := by
  induction data generalizing i with
  | nil => rfl
  | cons b rest ih => simp [encodePtrBytes, ih]

private theorem decodePtrProvenance_encode (prov : Option Prov) (i : Nat) (data : List UInt8) :
    decodePtrProvenance i prov (encodePtrBytes prov i data) = prov := by
  induction data generalizing i with
  | nil => rfl
  | cons b rest ih =>
    cases prov with
    | none => simp [encodePtrBytes, decodePtrProvenance, AbstractByte.provenance_frag, ih]
    | some p => simp [encodePtrBytes, decodePtrProvenance, AbstractByte.provenance_frag, ih]

private theorem firstProvenance_encodePtrBytes (prov : Option Prov) (b : UInt8)
    (rest : List UInt8) :
    firstProvenance (encodePtrBytes prov 0 (b :: rest)) = prov := by
  cases prov <;> simp [encodePtrBytes, firstProvenance, AbstractByte.provenance_frag]

/-- `encode_ptr` of an in-bounds thin pointer: the eight little-endian address bytes, each
carrying the fragment of the pointer's provenance at its own position. -/
theorem encodePtr_inBounds (ptr : Ptr)
    (h : inBounds ptr.addr .Unsigned x86_64.PTR_SIZE = true) :
    encodePtr ptr = .ok (encodePtrBytes ptr.provenance 0 (leBytes ptr.addr.toNat 8)) := by
  unfold encodePtr
  rw [encode_usize ptr.addr h]
  rfl

/-- `encode_ptr` of an out-of-bounds address is a spec panic (`Endianness::encode(..).unwrap()`),
never UB: `check_ptr` rejects such pointers before any encode. -/
theorem encodePtr_outOfBounds (ptr : Ptr)
    (h : inBounds ptr.addr .Unsigned x86_64.PTR_SIZE = false) :
    encodePtr ptr =
      .error (.specPanic "M::T::ENDIANNESS.encode(Unsigned, M::T::PTR_SIZE, ptr.addr).unwrap()") := by
  unfold encodePtr
  rw [encode_usize_oob ptr.addr h]
  rfl

/-- `decode_ptr` reads back exactly the pointer `encode_ptr` wrote: same address, same
provenance. -/
theorem decodePtr_encodePtrBytes (addr : Int)
    (h : inBounds addr .Unsigned x86_64.PTR_SIZE = true) (prov : Option Prov) :
    decodePtr (encodePtrBytes prov 0 (leBytes addr.toNat 8)) =
      .ok (some { addr := addr, provenance := prov }) := by
  have hdata := encodePtrBytes_data prov 0 (leBytes addr.toNat 8)
  have hval := decode_usize addr h
  have hlen : (encodePtrBytes prov 0 (leBytes addr.toNat 8)).length = x86_64.PTR_SIZE.bytes := by
    rw [encodePtrBytes_length, leBytes_length]
    rfl
  have hfirst : firstProvenance (encodePtrBytes prov 0 (leBytes addr.toNat 8)) = prov := by
    have hcons : leBytes addr.toNat 8 =
        UInt8.ofNat (addr.toNat % 256) :: leBytes (addr.toNat / 256) 7 := rfl
    rw [hcons]
    exact firstProvenance_encodePtrBytes prov _ _
  unfold decodePtr
  simp only [hlen, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [hfirst, hdata]
  simp only [hval, decodePtrProvenance_encode]
  rfl

theorem layout_fnPtr : Interp.Type.layout (.Ptr .FnPtr) = .ok (.Sized ⟨8⟩ ⟨8⟩) := rfl

theorem layout_thinRawPtr : Interp.Type.layout (.Ptr (.Raw .None)) = .ok (.Sized ⟨8⟩ ⟨8⟩) := rfl

/-- `Machine::check_value` at `PtrType::FnPtr` (and at any raw-pointer type without metadata)
only checks the address bound and the absence of metadata: it is `Ok` exactly on in-bounds thin
pointers. In particular MiniRust does **not** require a `FnPtr` value to point to a function. -/
theorem checkValue_fnPtr_ok_iff (m? : Option Mach) (p : Gen.Pointer Prov) :
    checkValue (.Ptr p) (.Ptr .FnPtr) m? = .ok () ↔
      inBounds p.thin_pointer.addr .Unsigned x86_64.PTR_SIZE = true ∧ p.metadata = none := by
  rcases p with ⟨thin, md⟩
  cases hb : inBounds thin.addr .Unsigned x86_64.PTR_SIZE <;> rcases md with _ | (n | vp) <;>
    simp [checkValue, checkPtr, hb, ensureElseUb, checkPtrMetadata, PtrType.meta_kind,
      PtrType.safe_pointee, ub, okBind, errorBind, pureOk]

/-- An out-of-bounds address is UB at `PtrType::FnPtr` (`"Value::Ptr: pointer out-of-bounds"`). -/
theorem checkValue_fnPtr_oob_ub (m? : Option Mach) (p : Gen.Pointer Prov)
    (h : inBounds p.thin_pointer.addr .Unsigned x86_64.PTR_SIZE = false) :
    checkValue (.Ptr p) (.Ptr .FnPtr) m? = .error (.ub "Value::Ptr: pointer out-of-bounds") := by
  simp [checkValue, checkPtr, h, ensureElseUb, ub, errorBind]

/-- A wide (metadata-carrying) pointer is UB at `PtrType::FnPtr`
(`"Value::Ptr: invalid metadata"`). -/
theorem checkValue_fnPtr_wide_ub (m? : Option Mach) (thin : Ptr) (md : Gen.PointerMeta Prov)
    (h : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true) :
    checkValue (.Ptr ⟨thin, some md⟩) (.Ptr .FnPtr) m? =
      .error (.ub "Value::Ptr: invalid metadata") := by
  cases md <;>
    simp [checkValue, checkPtr, h, ensureElseUb, checkPtrMetadata, PtrType.meta_kind, ub,
      okBind, errorBind, pureOk]

private theorem checkValue_thinRaw_ok (m? : Option Mach) (thin : Ptr)
    (h : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true) :
    checkValue (.Ptr ⟨thin, none⟩) (.Ptr (.Raw .None)) m? = .ok () := by
  simp [checkValue, checkPtr, h, ensureElseUb, checkPtrMetadata, PtrType.meta_kind,
    PtrType.safe_pointee, okBind, pureOk]

private theorem encode_fnPtr (thin : Ptr) :
    Interp.Type.encode (.Ptr .FnPtr) (.Ptr ⟨thin, none⟩) = encodePtr thin := by
  simp only [Interp.Type.encode, PtrType.as_wide_pair, PtrType.meta_kind]
  rfl

private theorem encode_fnPtr_wide (thin : Ptr) (md : Gen.PointerMeta Prov) :
    Interp.Type.encode (.Ptr .FnPtr) (.Ptr ⟨thin, some md⟩) =
      .error (.specPanic "assertion failed: ptr_type and value have mismatching metadata") := by
  simp only [Interp.Type.encode, PtrType.as_wide_pair, PtrType.meta_kind]
  rfl

private theorem decode_thinRaw (bytes : List Byte) :
    Interp.Type.decode (.Ptr (.Raw .None)) bytes =
      (decodePtr bytes >>= fun r =>
        match r with
        | some ptr => pure (some (.Ptr (ThinPointer.widen ptr none)))
        | none => pure none) := by
  simp only [Interp.Type.decode, PtrType.as_wide_pair, PtrType.meta_kind]
  rfl

/-- **MiniRust `Machine::transmute` from `FnPtr` to a thin raw pointer (`Mach`)**: every in-bounds
thin pointer value is returned unchanged — same address, same provenance, no metadata. -/
theorem transmute_fnPtr_thinRaw_ok (m? : Option Mach) (addr : Int) (prov : Option Prov)
    (h : inBounds addr .Unsigned x86_64.PTR_SIZE = true) :
    transmute (.Ptr ⟨⟨addr, prov⟩, none⟩) (.Ptr .FnPtr) (.Ptr (.Raw .None)) m? =
      .ok (.Ptr ⟨⟨addr, prov⟩, none⟩) := by
  unfold transmute
  rw [layout_fnPtr, okBind, expectSize_sized, okBind, layout_thinRawPtr, okBind,
    expectSize_sized, okBind, size_ne_self_ite, encode_fnPtr,
    encodePtr_inBounds ⟨addr, prov⟩ h, okBind, decode_thinRaw,
    decodePtr_encodePtrBytes addr h prov, okBind]
  dsimp only []
  show (checkValue (.Ptr ⟨⟨addr, prov⟩, none⟩) (.Ptr (.Raw .None)) m? >>= fun _ => _) = _
  rw [checkValue_thinRaw_ok m? ⟨addr, prov⟩ h]
  rfl

/-- **B1 (`Mach`)**: `minimize` translates `CastKind::FnPtrToPtr` to
`build::transmute(operand, ty)` (`tooling/minimize/src/rvalue.rs`, lines 325-331 at the pinned
commit:
> "smir::CastKind::Transmute
>  | smir::CastKind::FnPtrToPtr
>  | smir::CastKind::PointerCoercion(smir::PointerCoercion::UnsafeFnPointer) => {
>      let operand = self.translate_operand_smir(operand, span);
>      let ty = self.translate_ty_smir(*cast_ty, span);
>      build::transmute(operand, ty)
>  }"
), with `rs::TyKind::FnPtr(..) => Type::Ptr(PtrType::FnPtr)` (`ty.rs`, line 238) as the operand
type and `Type::Ptr(PtrType::Raw { meta_kind: None })` as the thin raw-pointer target type.
Evaluating that `UnOp::Cast(CastOp::Transmute(..))` on any in-bounds thin pointer value returns the
**same** pointer value (address and provenance preserved, metadata `none`) at the thin raw-pointer
type, with or without a machine. -/
theorem evalUnOp_fnPtrToPtr_ok (m? : Option Mach) (addr : Int) (prov : Option Prov)
    (h : inBounds addr .Unsigned x86_64.PTR_SIZE = true) :
    evalUnOp (.Cast (.Transmute (.Ptr (.Raw .None))))
        (.Ptr ⟨⟨addr, prov⟩, none⟩, .Ptr .FnPtr) m? =
      .ok (.Ptr ⟨⟨addr, prov⟩, none⟩, .Ptr (.Raw .None)) := by
  unfold evalUnOp evalCastOp
  dsimp only []
  rw [layout_fnPtr, okBind, expectSize_sized, okBind, layout_thinRawPtr, okBind,
    expectSize_sized, okBind, size_ne_self_ite, transmute_fnPtr_thinRaw_ok m? addr prov h, okBind]
  rfl

/-- **B1 (`Mach`), out-of-bounds address**: the cast of a pointer value whose address is outside
`[0, 2^64)` is a *spec panic* (`encode_ptr`'s `unwrap`), not UB: such a value is not well formed at
`PtrType::FnPtr` (`checkValue_fnPtr_oob_ub`), so a well-formed MiniRust program never reaches it. -/
theorem evalUnOp_fnPtrToPtr_oob_specPanic (m? : Option Mach) (addr : Int) (prov : Option Prov)
    (h : inBounds addr .Unsigned x86_64.PTR_SIZE = false) :
    evalUnOp (.Cast (.Transmute (.Ptr (.Raw .None))))
        (.Ptr ⟨⟨addr, prov⟩, none⟩, .Ptr .FnPtr) m? =
      .error
        (.specPanic "M::T::ENDIANNESS.encode(Unsigned, M::T::PTR_SIZE, ptr.addr).unwrap()") := by
  unfold evalUnOp evalCastOp
  dsimp only []
  rw [layout_fnPtr, okBind, expectSize_sized, okBind, layout_thinRawPtr, okBind,
    expectSize_sized, okBind, size_ne_self_ite]
  unfold transmute
  rw [layout_fnPtr, okBind, expectSize_sized, okBind, layout_thinRawPtr, okBind,
    expectSize_sized, okBind, size_ne_self_ite, encode_fnPtr,
    encodePtr_outOfBounds ⟨addr, prov⟩ h]
  rfl

/-- **B1 (`Mach`), wide pointer**: the cast of a metadata-carrying pointer value is a *spec panic*
(`Type::encode`'s metadata assertion), not UB: such a value is not well formed at `PtrType::FnPtr`
(`checkValue_fnPtr_wide_ub`). -/
theorem evalUnOp_fnPtrToPtr_wide_specPanic (m? : Option Mach) (thin : Ptr)
    (md : Gen.PointerMeta Prov) :
    evalUnOp (.Cast (.Transmute (.Ptr (.Raw .None)))) (.Ptr ⟨thin, some md⟩, .Ptr .FnPtr) m? =
      .error (.specPanic "assertion failed: ptr_type and value have mismatching metadata") := by
  unfold evalUnOp evalCastOp
  dsimp only []
  rw [layout_fnPtr, okBind, expectSize_sized, okBind, layout_thinRawPtr, okBind,
    expectSize_sized, okBind, size_ne_self_ite]
  unfold transmute
  rw [layout_fnPtr, okBind, expectSize_sized, okBind, layout_thinRawPtr, okBind,
    expectSize_sized, okBind, size_ne_self_ite, encode_fnPtr_wide]
  rfl

/-- **B1 (`Mach`), two-sided**: on a pointer value, the `FnPtr → thin raw pointer` transmute
succeeds exactly on the values that are well formed at `PtrType::FnPtr` (in-bounds address, no
metadata), and then returns the operand itself. -/
theorem evalUnOp_fnPtrToPtr_ok_iff (m? : Option Mach) (p : Gen.Pointer Prov)
    (r : Val × Gen.Type) :
    evalUnOp (.Cast (.Transmute (.Ptr (.Raw .None)))) (.Ptr p, .Ptr .FnPtr) m? = .ok r ↔
      checkValue (.Ptr p) (.Ptr .FnPtr) m? = .ok () ∧ r = (.Ptr p, .Ptr (.Raw .None)) := by
  rcases p with ⟨⟨addr, prov⟩, md⟩
  rw [checkValue_fnPtr_ok_iff]
  cases md with
  | some md =>
    rw [evalUnOp_fnPtrToPtr_wide_specPanic]
    constructor
    · intro h; cases h
    · rintro ⟨⟨_, h⟩, _⟩; cases h
  | none =>
    cases hb : inBounds addr .Unsigned x86_64.PTR_SIZE with
    | false =>
      rw [evalUnOp_fnPtrToPtr_oob_specPanic m? addr prov hb]
      constructor
      · intro h; cases h
      · rintro ⟨⟨h, _⟩, _⟩; cases h
    | true =>
      rw [evalUnOp_fnPtrToPtr_ok m? addr prov hb]
      constructor
      · intro h; cases h; exact ⟨⟨rfl, rfl⟩, rfl⟩
      · rintro ⟨_, rfl⟩; rfl

/-- `Machine::fn_from_ptr` on a thin pointer value (`Mach`): the first `fn_ptrs` entry holding
exactly this pointer names the function; a pointer that is not a registered function pointer is
UB `"invalid pointer for function lookup"`. -/
theorem fnFromPtr_thin_eq (m : Mach) (thin : Ptr) :
    fnFromPtr m (.Ptr ⟨thin, none⟩) =
      match m.fn_ptrs.entries.find? (fun (e : Gen.FnName × Ptr) => decide (e.2 = thin)) with
      | some e => mapIndex m.prog.functions e.1 "self.prog.functions[func_name]"
      | none => .error (.ub "invalid pointer for function lookup") := by
  simp only [fnFromPtr]
  split
  · next h => simp at h
  · cases List.find? (fun (e : Gen.FnName × Ptr) => decide (e.2 = thin)) m.fn_ptrs.entries with
    | none => rfl
    | some e => rfl

/-- A thin pointer that is **not** registered in `fn_ptrs` (e.g. any pointer to stack or global
*data*) is rejected by `Machine::fn_from_ptr` with UB (`Mach`). -/
theorem fnFromPtr_unregistered_ub (m : Mach) (thin : Ptr)
    (h : ∀ e ∈ m.fn_ptrs.entries, e.2 ≠ thin) :
    fnFromPtr m (.Ptr ⟨thin, none⟩) = .error (.ub "invalid pointer for function lookup") := by
  rw [fnFromPtr_thin_eq]
  have hnone : m.fn_ptrs.entries.find? (fun (e : Gen.FnName × Ptr) => decide (e.2 = thin)) =
      none := by
    rw [List.find?_eq_none]
    intro e he
    simpa using h e he
  rw [hnone]

/-- A wide pointer is rejected by `Machine::fn_from_ptr` with the same UB (`Mach`). -/
theorem fnFromPtr_wide_ub (m : Mach) (thin : Ptr) (md : Gen.PointerMeta Prov) :
    fnFromPtr m (.Ptr ⟨thin, some md⟩) = .error (.ub "invalid pointer for function lookup") := by
  simp [fnFromPtr, ub]

/-- **B1 (`Mach`)**: `fn_from_ptr` resolves the same function from the pointer after the
`FnPtr → thin raw pointer` cast as before it (the cast result, read back at `FnPtr`, is the same
`Value::Ptr`). -/
theorem fnFromPtr_after_fnPtrToPtr (m : Mach) (m? : Option Mach) (p : Gen.Pointer Prov)
    (r : Val × Gen.Type)
    (h : evalUnOp (.Cast (.Transmute (.Ptr (.Raw .None)))) (.Ptr p, .Ptr .FnPtr) m? = .ok r) :
    fnFromPtr m r.1 = fnFromPtr m (.Ptr p) := by
  rw [((evalUnOp_fnPtrToPtr_ok_iff m? p r).mp h).2]

/-! #### Every `Machine M` (in particular `MachTB`, `TreeBorrowsMemory`) -/

section Poly

variable {M : Type} [Gen.Memory M] [MemoryOps M]

omit [MemoryOps M] in
private theorem encodePtrBytesM_data (prov : Option (Gen.Memory.Provenance M)) (i : Nat)
    (data : List UInt8) :
    (encodePtrBytesM (M := M) prov i data).mapM AbstractByte.dataM = some data := by
  induction data generalizing i with
  | nil => rfl
  | cons b rest ih => simp [encodePtrBytesM, AbstractByte.dataM, ih]

omit [MemoryOps M] in
private theorem encodePtrBytesM_length (prov : Option (Gen.Memory.Provenance M)) (i : Nat)
    (data : List UInt8) :
    (encodePtrBytesM (M := M) prov i data).length = data.length := by
  induction data generalizing i with
  | nil => rfl
  | cons b rest ih => simp [encodePtrBytesM, ih]

private theorem decodePtrProvenanceM_encode (prov : Option (Gen.Memory.Provenance M)) (i : Nat)
    (data : List UInt8) :
    decodePtrProvenanceM (M := M) i prov (encodePtrBytesM (M := M) prov i data) = prov := by
  induction data generalizing i with
  | nil => rfl
  | cons b rest ih =>
    cases prov with
    | none => simp [encodePtrBytesM, decodePtrProvenanceM, AbstractByte.provenance_fragM, ih]
    | some p => simp [encodePtrBytesM, decodePtrProvenanceM, AbstractByte.provenance_fragM, ih]

omit [MemoryOps M] in
private theorem firstProvenanceM_encodePtrBytesM (prov : Option (Gen.Memory.Provenance M))
    (b : UInt8) (rest : List UInt8) :
    firstProvenanceM (M := M) (encodePtrBytesM (M := M) prov 0 (b :: rest)) = prov := by
  cases prov <;> simp [encodePtrBytesM, firstProvenanceM, AbstractByte.provenance_fragM]

omit [MemoryOps M] in
/-- Polymorphic `encode_ptr` of an in-bounds thin pointer; see `encodePtr_inBounds`. -/
theorem encodePtrM_inBounds (ptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (h : inBounds ptr.addr .Unsigned x86_64.PTR_SIZE = true) :
    encodePtrM (M := M) ptr =
      .ok (encodePtrBytesM (M := M) ptr.provenance 0 (leBytes ptr.addr.toNat 8)) := by
  unfold encodePtrM
  rw [encode_usize ptr.addr h]
  rfl

omit [MemoryOps M] in
/-- Polymorphic `encode_ptr` of an out-of-bounds address; see `encodePtr_outOfBounds`. -/
theorem encodePtrM_outOfBounds (ptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (h : inBounds ptr.addr .Unsigned x86_64.PTR_SIZE = false) :
    encodePtrM (M := M) ptr =
      .error (.specPanic "M::T::ENDIANNESS.encode(Unsigned, M::T::PTR_SIZE, ptr.addr).unwrap()") := by
  unfold encodePtrM
  rw [encode_usize_oob ptr.addr h]
  rfl

/-- Polymorphic `decode_ptr` ∘ `encode_ptr` round trip; see `decodePtr_encodePtrBytes`. -/
theorem decodePtrM_encodePtrBytesM (addr : Int)
    (h : inBounds addr .Unsigned x86_64.PTR_SIZE = true)
    (prov : Option (Gen.Memory.Provenance M)) :
    decodePtrM (M := M) (encodePtrBytesM (M := M) prov 0 (leBytes addr.toNat 8)) =
      .ok (some { addr := addr, provenance := prov }) := by
  have hdata := encodePtrBytesM_data (M := M) prov 0 (leBytes addr.toNat 8)
  have hval := decode_usize addr h
  have hlen : (encodePtrBytesM (M := M) prov 0 (leBytes addr.toNat 8)).length =
      x86_64.PTR_SIZE.bytes := by
    rw [encodePtrBytesM_length, leBytes_length]
    rfl
  have hfirst : firstProvenanceM (M := M)
      (encodePtrBytesM (M := M) prov 0 (leBytes addr.toNat 8)) = prov := by
    have hcons : leBytes addr.toNat 8 =
        UInt8.ofNat (addr.toNat % 256) :: leBytes (addr.toNat / 256) 7 := rfl
    rw [hcons]
    exact firstProvenanceM_encodePtrBytesM prov _ _
  unfold decodePtrM
  simp only [hlen, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [hfirst, hdata]
  simp only [hval, decodePtrProvenanceM_encode]
  rfl

/-- Polymorphic `Machine::check_value` at `PtrType::FnPtr`; see `checkValue_fnPtr_ok_iff`. -/
theorem checkValueM_fnPtr_ok_iff (m? : Option (Gen.Machine M))
    (p : Gen.Pointer (Gen.Memory.Provenance M)) :
    checkValueM (M := M) (.Ptr p) (.Ptr .FnPtr) m? = .ok () ↔
      inBounds p.thin_pointer.addr .Unsigned x86_64.PTR_SIZE = true ∧ p.metadata = none := by
  rcases p with ⟨thin, md⟩
  cases hb : inBounds thin.addr .Unsigned x86_64.PTR_SIZE <;> rcases md with _ | (n | vp) <;>
    simp [checkValueM, checkPtrM, hb, ensureElseUb, checkPtrMetadataM, PtrType.meta_kind,
      PtrType.safe_pointee, ub, okBind, errorBind, pureOk]

/-- Polymorphic out-of-bounds UB at `PtrType::FnPtr`; see `checkValue_fnPtr_oob_ub`. -/
theorem checkValueM_fnPtr_oob_ub (m? : Option (Gen.Machine M))
    (p : Gen.Pointer (Gen.Memory.Provenance M))
    (h : inBounds p.thin_pointer.addr .Unsigned x86_64.PTR_SIZE = false) :
    checkValueM (M := M) (.Ptr p) (.Ptr .FnPtr) m? =
      .error (.ub "Value::Ptr: pointer out-of-bounds") := by
  simp [checkValueM, checkPtrM, h, ensureElseUb, ub, errorBind]

/-- Polymorphic wide-pointer UB at `PtrType::FnPtr`; see `checkValue_fnPtr_wide_ub`. -/
theorem checkValueM_fnPtr_wide_ub (m? : Option (Gen.Machine M))
    (thin : Gen.ThinPointer (Gen.Memory.Provenance M))
    (md : Gen.PointerMeta (Gen.Memory.Provenance M))
    (h : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true) :
    checkValueM (M := M) (.Ptr ⟨thin, some md⟩) (.Ptr .FnPtr) m? =
      .error (.ub "Value::Ptr: invalid metadata") := by
  cases md <;>
    simp [checkValueM, checkPtrM, h, ensureElseUb, checkPtrMetadataM, PtrType.meta_kind, ub,
      okBind, errorBind, pureOk]

private theorem checkValueM_thinRaw_ok (m? : Option (Gen.Machine M))
    (thin : Gen.ThinPointer (Gen.Memory.Provenance M))
    (h : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true) :
    checkValueM (M := M) (.Ptr ⟨thin, none⟩) (.Ptr (.Raw .None)) m? = .ok () := by
  simp [checkValueM, checkPtrM, h, ensureElseUb, checkPtrMetadataM, PtrType.meta_kind,
    PtrType.safe_pointee, okBind, pureOk]

omit [MemoryOps M] in
private theorem encodeM_fnPtr (thin : Gen.ThinPointer (Gen.Memory.Provenance M)) :
    Interp.Type.encodeM (M := M) (.Ptr .FnPtr) (.Ptr ⟨thin, none⟩) = encodePtrM (M := M) thin := by
  simp only [Interp.Type.encodeM, PtrType.as_wide_pair, PtrType.meta_kind]
  rfl

omit [MemoryOps M] in
private theorem encodeM_fnPtr_wide (thin : Gen.ThinPointer (Gen.Memory.Provenance M))
    (md : Gen.PointerMeta (Gen.Memory.Provenance M)) :
    Interp.Type.encodeM (M := M) (.Ptr .FnPtr) (.Ptr ⟨thin, some md⟩) =
      .error (.specPanic "assertion failed: ptr_type and value have mismatching metadata") := by
  simp only [Interp.Type.encodeM, PtrType.as_wide_pair, PtrType.meta_kind]
  rfl

private theorem decodeM_thinRaw (bytes : List (Gen.AbstractByte (Gen.Memory.Provenance M))) :
    Interp.Type.decodeM (M := M) (.Ptr (.Raw .None)) bytes =
      (decodePtrM (M := M) bytes >>= fun r =>
        match r with
        | some ptr => pure (some (.Ptr (ThinPointer.widen ptr none)))
        | none => pure none) := by
  simp only [Interp.Type.decodeM, PtrType.as_wide_pair, PtrType.meta_kind]
  rfl

/-- Polymorphic `Machine::transmute` from `FnPtr` to a thin raw pointer; see
`transmute_fnPtr_thinRaw_ok`. -/
theorem transmuteM_fnPtr_thinRaw_ok (m? : Option (Gen.Machine M)) (addr : Int)
    (prov : Option (Gen.Memory.Provenance M))
    (h : inBounds addr .Unsigned x86_64.PTR_SIZE = true) :
    transmuteM (M := M) (.Ptr ⟨⟨addr, prov⟩, none⟩) (.Ptr .FnPtr) (.Ptr (.Raw .None)) m? =
      .ok (.Ptr ⟨⟨addr, prov⟩, none⟩) := by
  unfold transmuteM
  rw [layout_fnPtr, okBind, expectSize_sized, okBind, layout_thinRawPtr, okBind,
    expectSize_sized, okBind, size_ne_self_ite, encodeM_fnPtr,
    encodePtrM_inBounds (M := M) ⟨addr, prov⟩ h, okBind, decodeM_thinRaw,
    decodePtrM_encodePtrBytesM addr h prov, okBind]
  dsimp only []
  show (checkValueM (M := M) (.Ptr ⟨⟨addr, prov⟩, none⟩) (.Ptr (.Raw .None)) m? >>=
    fun _ => _) = _
  rw [checkValueM_thinRaw_ok m? ⟨addr, prov⟩ h]
  rfl

/-- **B1 (every `Machine M`, in particular `MachTB`)**: the `FnPtr → thin raw pointer` transmute
that `minimize` emits for `CastKind::FnPtrToPtr` returns the **same** pointer value (address and
provenance preserved, metadata `none`) on any in-bounds thin pointer value; see
`evalUnOp_fnPtrToPtr_ok`. -/
theorem evalUnOpM_fnPtrToPtr_ok (m? : Option (Gen.Machine M)) (addr : Int)
    (prov : Option (Gen.Memory.Provenance M))
    (h : inBounds addr .Unsigned x86_64.PTR_SIZE = true) :
    evalUnOpM (M := M) (.Cast (.Transmute (.Ptr (.Raw .None))))
        (.Ptr ⟨⟨addr, prov⟩, none⟩, .Ptr .FnPtr) m? =
      .ok (.Ptr ⟨⟨addr, prov⟩, none⟩, .Ptr (.Raw .None)) := by
  unfold evalUnOpM evalCastOpM
  dsimp only []
  rw [layout_fnPtr, okBind, expectSize_sized, okBind, layout_thinRawPtr, okBind,
    expectSize_sized, okBind, size_ne_self_ite, transmuteM_fnPtr_thinRaw_ok m? addr prov h,
    okBind]
  rfl

/-- **B1 (every `Machine M`), out-of-bounds address**: a spec panic, not UB; see
`evalUnOp_fnPtrToPtr_oob_specPanic`. -/
theorem evalUnOpM_fnPtrToPtr_oob_specPanic (m? : Option (Gen.Machine M)) (addr : Int)
    (prov : Option (Gen.Memory.Provenance M))
    (h : inBounds addr .Unsigned x86_64.PTR_SIZE = false) :
    evalUnOpM (M := M) (.Cast (.Transmute (.Ptr (.Raw .None))))
        (.Ptr ⟨⟨addr, prov⟩, none⟩, .Ptr .FnPtr) m? =
      .error
        (.specPanic "M::T::ENDIANNESS.encode(Unsigned, M::T::PTR_SIZE, ptr.addr).unwrap()") := by
  unfold evalUnOpM evalCastOpM
  dsimp only []
  rw [layout_fnPtr, okBind, expectSize_sized, okBind, layout_thinRawPtr, okBind,
    expectSize_sized, okBind, size_ne_self_ite]
  unfold transmuteM
  rw [layout_fnPtr, okBind, expectSize_sized, okBind, layout_thinRawPtr, okBind,
    expectSize_sized, okBind, size_ne_self_ite, encodeM_fnPtr,
    encodePtrM_outOfBounds (M := M) ⟨addr, prov⟩ h]
  rfl

/-- **B1 (every `Machine M`), wide pointer**: a spec panic, not UB; see
`evalUnOp_fnPtrToPtr_wide_specPanic`. -/
theorem evalUnOpM_fnPtrToPtr_wide_specPanic (m? : Option (Gen.Machine M))
    (thin : Gen.ThinPointer (Gen.Memory.Provenance M))
    (md : Gen.PointerMeta (Gen.Memory.Provenance M)) :
    evalUnOpM (M := M) (.Cast (.Transmute (.Ptr (.Raw .None))))
        (.Ptr ⟨thin, some md⟩, .Ptr .FnPtr) m? =
      .error (.specPanic "assertion failed: ptr_type and value have mismatching metadata") := by
  unfold evalUnOpM evalCastOpM
  dsimp only []
  rw [layout_fnPtr, okBind, expectSize_sized, okBind, layout_thinRawPtr, okBind,
    expectSize_sized, okBind, size_ne_self_ite]
  unfold transmuteM
  rw [layout_fnPtr, okBind, expectSize_sized, okBind, layout_thinRawPtr, okBind,
    expectSize_sized, okBind, size_ne_self_ite, encodeM_fnPtr_wide]
  rfl

/-- **B1 (every `Machine M`), two-sided**: the transmute succeeds exactly on the values that are
well formed at `PtrType::FnPtr`, and then returns the operand itself; see
`evalUnOp_fnPtrToPtr_ok_iff`. -/
theorem evalUnOpM_fnPtrToPtr_ok_iff (m? : Option (Gen.Machine M))
    (p : Gen.Pointer (Gen.Memory.Provenance M)) (r : Gen.Value M × Gen.Type) :
    evalUnOpM (M := M) (.Cast (.Transmute (.Ptr (.Raw .None)))) (.Ptr p, .Ptr .FnPtr) m? =
        .ok r ↔
      checkValueM (M := M) (.Ptr p) (.Ptr .FnPtr) m? = .ok () ∧
        r = (.Ptr p, .Ptr (.Raw .None)) := by
  rcases p with ⟨⟨addr, prov⟩, md⟩
  rw [checkValueM_fnPtr_ok_iff]
  cases md with
  | some md =>
    rw [evalUnOpM_fnPtrToPtr_wide_specPanic]
    constructor
    · intro h; cases h
    · rintro ⟨⟨_, h⟩, _⟩; cases h
  | none =>
    cases hb : inBounds addr .Unsigned x86_64.PTR_SIZE with
    | false =>
      rw [evalUnOpM_fnPtrToPtr_oob_specPanic m? addr prov hb]
      constructor
      · intro h; cases h
      · rintro ⟨⟨h, _⟩, _⟩; cases h
    | true =>
      rw [evalUnOpM_fnPtrToPtr_ok m? addr prov hb]
      constructor
      · intro h; cases h; exact ⟨⟨rfl, rfl⟩, rfl⟩
      · rintro ⟨_, rfl⟩; rfl

/-- Polymorphic `Machine::fn_from_ptr` on a thin pointer value; see `fnFromPtr_thin_eq`. -/
theorem fnFromPtrM_thin_eq (m : Gen.Machine M)
    (thin : Gen.ThinPointer (Gen.Memory.Provenance M)) :
    fnFromPtrM (M := M) m (.Ptr ⟨thin, none⟩) =
      match m.fn_ptrs.entries.find?
          (fun (e : Gen.FnName × Gen.ThinPointer (Gen.Memory.Provenance M)) =>
            decide (e.2 = thin)) with
      | some e => mapIndex m.prog.functions e.1 "self.prog.functions[func_name]"
      | none => .error (.ub "invalid pointer for function lookup") := by
  simp only [fnFromPtrM]
  split
  · next h => simp at h
  · cases List.find?
        (fun (e : Gen.FnName × Gen.ThinPointer (Gen.Memory.Provenance M)) => decide (e.2 = thin))
        m.fn_ptrs.entries with
    | none => rfl
    | some e => rfl

/-- A thin pointer that is not registered in `fn_ptrs` is rejected by `Machine::fn_from_ptr` with
UB on every machine (in particular `MachTB`); see `fnFromPtr_unregistered_ub`. -/
theorem fnFromPtrM_unregistered_ub (m : Gen.Machine M)
    (thin : Gen.ThinPointer (Gen.Memory.Provenance M))
    (h : ∀ e ∈ m.fn_ptrs.entries, e.2 ≠ thin) :
    fnFromPtrM (M := M) m (.Ptr ⟨thin, none⟩) =
      .error (.ub "invalid pointer for function lookup") := by
  rw [fnFromPtrM_thin_eq]
  have hnone : m.fn_ptrs.entries.find?
      (fun (e : Gen.FnName × Gen.ThinPointer (Gen.Memory.Provenance M)) =>
        decide (e.2 = thin)) = none := by
    rw [List.find?_eq_none]
    intro e he
    simpa using h e he
  rw [hnone]

/-- A wide pointer is rejected by `Machine::fn_from_ptr` with the same UB on every machine; see
`fnFromPtr_wide_ub`. -/
theorem fnFromPtrM_wide_ub (m : Gen.Machine M) (thin : Gen.ThinPointer (Gen.Memory.Provenance M))
    (md : Gen.PointerMeta (Gen.Memory.Provenance M)) :
    fnFromPtrM (M := M) m (.Ptr ⟨thin, some md⟩) =
      .error (.ub "invalid pointer for function lookup") := by
  simp [fnFromPtrM, ub]

/-- **B1 (every `Machine M`)**: `fn_from_ptr` resolves the same function after the cast as before
it; see `fnFromPtr_after_fnPtrToPtr`. -/
theorem fnFromPtrM_after_fnPtrToPtr (m : Gen.Machine M) (m? : Option (Gen.Machine M))
    (p : Gen.Pointer (Gen.Memory.Provenance M)) (r : Gen.Value M × Gen.Type)
    (h : evalUnOpM (M := M) (.Cast (.Transmute (.Ptr (.Raw .None)))) (.Ptr p, .Ptr .FnPtr) m? =
      .ok r) :
    fnFromPtrM (M := M) m r.1 = fnFromPtrM (M := M) m (.Ptr p) := by
  rw [((evalUnOpM_fnPtrToPtr_ok_iff m? p r).mp h).2]

end Poly

/-- **B1 (`MachTB`)**: `evalUnOpM_fnPtrToPtr_ok` at `M := TreeBorrowsMemory<x86_64>`. -/
theorem evalUnOpTB_fnPtrToPtr_ok (m? : Option MachTB) (addr : Int)
    (prov : Option (Gen.Memory.Provenance TBM))
    (h : inBounds addr .Unsigned x86_64.PTR_SIZE = true) :
    evalUnOpM (M := TBM) (.Cast (.Transmute (.Ptr (.Raw .None))))
        (.Ptr ⟨⟨addr, prov⟩, none⟩, .Ptr .FnPtr) m? =
      .ok (.Ptr ⟨⟨addr, prov⟩, none⟩, .Ptr (.Raw .None)) :=
  evalUnOpM_fnPtrToPtr_ok m? addr prov h

/-- **B1 (`Mach` via the polymorphic interpreter)**: `evalUnOpM_fnPtrToPtr_ok` at
`M := BasicMemory<x86_64>`. -/
theorem evalUnOpBM_fnPtrToPtr_ok (m? : Option Mach) (addr : Int) (prov : Option Prov)
    (h : inBounds addr .Unsigned x86_64.PTR_SIZE = true) :
    evalUnOpM (M := BM) (.Cast (.Transmute (.Ptr (.Raw .None))))
        (.Ptr ⟨⟨addr, prov⟩, none⟩, .Ptr .FnPtr) m? =
      .ok (.Ptr ⟨⟨addr, prov⟩, none⟩, .Ptr (.Raw .None)) :=
  evalUnOpM_fnPtrToPtr_ok m? addr prov h

/-! ### B2. Trusted: `evalFnPtrToPtr` (`evalRvalue (.cast .fnPtrToPtr op targetTy)`) -/

/-- Source-type check of `evalFnPtrToPtr` (verbatim): the operand's static type is unknown, or it
is a `fn` pointer type whose ABI is not `rustIntrinsic`. -/
def fnPtrSrcTyValid (srcTyOpt : Option Ty) : Bool :=
  match srcTyOpt with
  | .none => true
  | .some { kind := .fnPtr _ _ _ srcAbi, .. } => Bool.not (callConvEq srcAbi .rustIntrinsic)
  | .some _ => false

/-- Function-pointer registry check of `evalFnPtrToPtr` (verbatim): with an empty `mem.fnPtrs`
table the allocation must lie in the synthetic function-pointer range (`isFnPtrAllocId`);
otherwise it must be registered, and its recorded signature (if any) must be a `fn` pointer type
whose ABI is not `rustIntrinsic`. -/
def fnPtrRegistered (mem : Memory) (allocId : Nat) : Bool :=
  match mem.fnPtrs with
  | .nil => isFnPtrAllocId allocId
  | _ :: _ =>
    match lookupFnPtr mem.fnPtrs allocId with
    | .some entry =>
      match entry.fnSig with
      | .none => true
      | .some (.fnPtr _ _ _ sigAbi) => Bool.not (callConvEq sigAbi .rustIntrinsic)
      | .some _ => false
    | .none => false

/-- Pointer-value check of `evalFnPtrToPtr` (verbatim): pointer-sized (`8` bytes), at offset `0`,
not backed by a stack/global borrow (`lookupBorrow mem.borrows p.tag = none`), and registered as a
function pointer (`fnPtrRegistered`). -/
def fnPtrValueValid (mem : Memory) (p : ProvenancePtr) (sz : Nat) : Bool :=
  Bool.and (Nat.beq sz 8)
    (Bool.and (Nat.beq p.offsetBytes 0)
      (match lookupBorrow mem.borrows p.tag with
       | .some _ => false
       | .none => fnPtrRegistered mem p.allocId))

/-- Structural reading of `fnPtrValueValid`. -/
theorem fnPtrValueValid_eq_true_iff (mem : Memory) (p : ProvenancePtr) (sz : Nat) :
    fnPtrValueValid mem p sz = true ↔
      sz = 8 ∧ p.offsetBytes = 0 ∧ lookupBorrow mem.borrows p.tag = none ∧
        fnPtrRegistered mem p.allocId = true := by
  unfold fnPtrValueValid
  cases hB : lookupBorrow mem.borrows p.tag <;>
    simp [Bool.and_eq_true]

/-- `evalFnPtrToPtr` on an operand that evaluates to a pointer value: the three verbatim checks
decide between `.ok` (the same pointer, pointer-sized, frame and memory unchanged) and `.ub`. -/
theorem evalFnPtrToPtr_ptr_eq (locals locals' : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (p : ProvenancePtr) (sz : Nat)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr p sz) locals') :
    evalRvalue locals (.cast .fnPtrToPtr op targetTy) mem localDecls layouts =
      match Bool.and (isThinRawPtrTy targetTy)
          (Bool.and (fnPtrSrcTyValid (operandTy localDecls layouts op))
            (fnPtrValueValid mem p sz)) with
      | true => .ok (.ptr p 8) locals' mem
      | false => .ub := by
  show evalFnPtrToPtr locals op targetTy mem localDecls layouts = _
  unfold evalFnPtrToPtr
  rw [hOp] <;> rfl

/-- **B2 (Trusted, `.ok`)**: on a function-pointer operand value `.ptr p sz`, `FnPtrToPtr` succeeds
iff the target is a *thin* raw pointer, the source type is a non-intrinsic `fn` pointer (or
unknown), and `p` is a pointer-sized, offset-`0`, non-borrow-backed registered function pointer;
it then returns the **same** pointer (allocation identity and offset preserved) at pointer size,
leaving the frame and memory unchanged. -/
theorem evalRvalue_fnPtrToPtr_ptr_ok_iff (locals locals' : List LocalSlot) (op : Operand)
    (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (p : ProvenancePtr) (sz : Nat)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr p sz) locals')
    (v : Value) (locals'' : List LocalSlot) (mem'' : Memory) :
    evalRvalue locals (.cast .fnPtrToPtr op targetTy) mem localDecls layouts =
        .ok v locals'' mem'' ↔
      (v = .ptr p 8 ∧ locals'' = locals' ∧ mem'' = mem) ∧
        isThinRawPtrTy targetTy = true ∧
        fnPtrSrcTyValid (operandTy localDecls layouts op) = true ∧
        fnPtrValueValid mem p sz = true := by
  rw [evalFnPtrToPtr_ptr_eq locals locals' op targetTy mem localDecls layouts p sz hOp]
  cases h1 : isThinRawPtrTy targetTy <;>
    cases h2 : fnPtrSrcTyValid (operandTy localDecls layouts op) <;>
    cases h3 : fnPtrValueValid mem p sz <;>
    simp [eq_comm]

/-- **B2 (Trusted, `.ub`)**: on a pointer operand value, every violated check is `.ub` (never
`.unsupported`). -/
theorem evalRvalue_fnPtrToPtr_ptr_ub_iff (locals locals' : List LocalSlot) (op : Operand)
    (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (p : ProvenancePtr) (sz : Nat)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr p sz) locals') :
    evalRvalue locals (.cast .fnPtrToPtr op targetTy) mem localDecls layouts = .ub ↔
      ¬ (isThinRawPtrTy targetTy = true ∧
        fnPtrSrcTyValid (operandTy localDecls layouts op) = true ∧
        fnPtrValueValid mem p sz = true) := by
  rw [evalFnPtrToPtr_ptr_eq locals locals' op targetTy mem localDecls layouts p sz hOp]
  cases h1 : isThinRawPtrTy targetTy <;>
    cases h2 : fnPtrSrcTyValid (operandTy localDecls layouts op) <;>
    cases h3 : fnPtrValueValid mem p sz <;>
    simp

/-- **B2 (Trusted, non-pointer operand)**: an operand that evaluates to anything other than a
`Value.ptr` (a scalar address, an aggregate such as a wide pointer, a ZST, an uninitialized value)
is `.ub`. -/
theorem evalRvalue_fnPtrToPtr_nonPtr_ub (locals locals' : List LocalSlot) (op : Operand)
    (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (v : Value)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok v locals')
    (hNotPtr : ∀ p sz, v ≠ .ptr p sz) :
    evalRvalue locals (.cast .fnPtrToPtr op targetTy) mem localDecls layouts = .ub := by
  show evalFnPtrToPtr locals op targetTy mem localDecls layouts = _
  unfold evalFnPtrToPtr
  rw [hOp]
  cases v with
  | ptr p sz => exact absurd rfl (hNotPtr p sz)
  | _ => rfl

/-- **B2 (Trusted, operand failure)**: `FnPtrToPtr` is `.unsupported` exactly when loading the
operand is, and it propagates an operand `.ub`. -/
theorem evalRvalue_fnPtrToPtr_unsupported_iff (locals : List LocalSlot) (op : Operand)
    (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) :
    evalRvalue locals (.cast .fnPtrToPtr op targetTy) mem localDecls layouts = .unsupported ↔
      evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
        mem.callStack = .unsupported := by
  show evalFnPtrToPtr locals op targetTy mem localDecls layouts = _ ↔ _
  unfold evalFnPtrToPtr
  cases hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
    mem.callStack with
  | ub => simp
  | unsupported => simp
  | ok v locals' =>
    cases v with
    | ptr p sz =>
      dsimp only
      split <;> simp
    | _ => simp

/-- **B2 (Trusted, two-sided `.ok`)**: `FnPtrToPtr` returns `.ok` exactly when the operand
evaluates to a pointer value passing the three checks; the result is that same pointer. -/
theorem evalRvalue_fnPtrToPtr_ok_iff (locals : List LocalSlot) (op : Operand)
    (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (v : Value) (locals' : List LocalSlot) (mem' : Memory) :
    evalRvalue locals (.cast .fnPtrToPtr op targetTy) mem localDecls layouts =
        .ok v locals' mem' ↔
      ∃ p sz,
        evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
          mem.callStack = .ok (.ptr p sz) locals' ∧
        v = .ptr p 8 ∧ mem' = mem ∧
        isThinRawPtrTy targetTy = true ∧
        fnPtrSrcTyValid (operandTy localDecls layouts op) = true ∧
        fnPtrValueValid mem p sz = true := by
  constructor
  · intro h
    cases hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack with
    | ub =>
      exfalso
      have : evalFnPtrToPtr locals op targetTy mem localDecls layouts = .ub := by
        unfold evalFnPtrToPtr; rw [hOp]
      exact absurd (h.symm.trans this) (by intro h'; cases h')
    | unsupported =>
      exfalso
      have := (evalRvalue_fnPtrToPtr_unsupported_iff locals op targetTy mem localDecls layouts).mpr
        hOp
      exact absurd (h.symm.trans this) (by intro h'; cases h')
    | ok v0 locals0 =>
      cases v0 with
      | ptr p sz =>
        obtain ⟨⟨hv, hl, hm⟩, h1, h2, h3⟩ :=
          (evalRvalue_fnPtrToPtr_ptr_ok_iff locals locals0 op targetTy mem localDecls layouts p sz
            hOp v locals' mem').mp h
        subst hl
        exact ⟨p, sz, rfl, hv, hm, h1, h2, h3⟩
      | _ =>
        exfalso
        have := evalRvalue_fnPtrToPtr_nonPtr_ub locals locals0 op targetTy mem localDecls layouts _
          hOp (by intro p sz h'; cases h')
        exact absurd (h.symm.trans this) (by intro h'; cases h')
  · rintro ⟨p, sz, hOp, hv, hm, h1, h2, h3⟩
    exact (evalRvalue_fnPtrToPtr_ptr_ok_iff locals locals' op targetTy mem localDecls layouts p sz
      hOp v locals' mem').mpr ⟨⟨hv, rfl, hm⟩, h1, h2, h3⟩

/-- **B2 (Trusted, borrow-backed data pointer)**: a pointer whose tag is a live entry of the borrow
table — the value of `&raw const x`, `&x`, or a reborrow of stack or global *data* — is not a
function pointer: `FnPtrToPtr` on it is `.ub`. -/
theorem evalRvalue_fnPtrToPtr_borrowed_ub (locals locals' : List LocalSlot) (op : Operand)
    (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (p : ProvenancePtr) (sz : Nat) (entry : BorrowEntry)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr p sz) locals')
    (hB : lookupBorrow mem.borrows p.tag = some entry) :
    evalRvalue locals (.cast .fnPtrToPtr op targetTy) mem localDecls layouts = .ub := by
  rw [evalRvalue_fnPtrToPtr_ptr_ub_iff locals locals' op targetTy mem localDecls layouts p sz hOp]
  rintro ⟨_, _, h3⟩
  rw [fnPtrValueValid_eq_true_iff, hB] at h3
  exact absurd h3.2.2.1 (by intro h'; cases h')

/-- **B2 (Trusted, unregistered pointer)**: a pointer that is not a registered function pointer
(for instance a provenance pointer into a global *data* allocation) is `.ub`. -/
theorem evalRvalue_fnPtrToPtr_unregistered_ub (locals locals' : List LocalSlot) (op : Operand)
    (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (p : ProvenancePtr) (sz : Nat)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr p sz) locals')
    (hR : fnPtrRegistered mem p.allocId = false) :
    evalRvalue locals (.cast .fnPtrToPtr op targetTy) mem localDecls layouts = .ub := by
  rw [evalRvalue_fnPtrToPtr_ptr_ub_iff locals locals' op targetTy mem localDecls layouts p sz hOp]
  rintro ⟨_, _, h3⟩
  rw [fnPtrValueValid_eq_true_iff, hR] at h3
  exact absurd h3.2.2.2 (by intro h'; cases h')

/-- **B2 (Trusted, non-thin-raw-pointer target)**: a wide raw pointer (`*const [T]`, `*const str`,
`*const dyn Trait`), a reference, or any non-pointer target type is `.ub`. -/
theorem evalRvalue_fnPtrToPtr_nonThinTarget_ub (locals locals' : List LocalSlot) (op : Operand)
    (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (p : ProvenancePtr) (sz : Nat)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr p sz) locals')
    (hT : isThinRawPtrTy targetTy = false) :
    evalRvalue locals (.cast .fnPtrToPtr op targetTy) mem localDecls layouts = .ub := by
  rw [evalRvalue_fnPtrToPtr_ptr_ub_iff locals locals' op targetTy mem localDecls layouts p sz hOp]
  rintro ⟨h1, _, _⟩
  rw [hT] at h1
  cases h1

/-- Trusted's thin-raw-pointer target types are exactly the ones `minimize` translates to
`Type::Ptr(PtrType::Raw { meta_kind: PointerMetaKind::None })`: whenever a thin raw pointer type
is in the translated fragment at all, its MiniRust type is the transmute target of B1. -/
theorem translateTy_thinRawPtr (layouts : Layout.LayoutTable) (ty : Ty) (mrTy : Gen.Type)
    (hThin : isThinRawPtrTy ty = true) (hTr : translateTy layouts ty = some mrTy) :
    mrTy = .Ptr (.Raw .None) := by
  rcases ty with ⟨k, idx⟩
  cases k <;> simp [isThinRawPtrTy] at hThin
  case rawPtr m pointee =>
    have hT : translateTy layouts ⟨.rawPtr m pointee, idx⟩ =
        (rawPtrMetaKind pointee).map (fun k => Gen.Type.Ptr (.Raw k)) := by
      simp only [translateTy, scalarTypeOf, isBoolTy, isOrderingTy, intBoolTupleOf, intTypeOf,
        intTyBytes, arrayTypeOf, tupleTypeOf, rawPtrTypeOf, rawPtrMetaOf, refTypeOf, boxTypeOf]
      cases rawPtrMetaKind pointee <;> simp
    rw [hT] at hTr
    cases pointee <;> simp at hThin <;> simp [rawPtrMetaKind] at hTr <;>
      first
      | exact hTr.symm
      | exact hTr.2.symm
      | exact hTr.1.symm

/-! ### B3. A value relation tying the two casts together -/

/-- **Function-pointer value relation.** `FnPtrRel fnMap mem m tv mv` relates a Trusted value `tv`
and a MiniRust value `mv` (on any machine `m : Machine M`) that denote the *same function
pointer*:

* `tv = .ptr p 8` is a pointer-sized, offset-`0`, non-borrow-backed pointer whose allocation
  `p.allocId` is registered in `mem.fnPtrs` (entry `entry`, the function `entry.defPath`) with a
  non-intrinsic signature — exactly the pointers `evalFnPtrToPtr` accepts on a non-empty
  function-pointer table;
* `mv = Value::Ptr(thin.widen(None))`, where `thin = m.fn_ptrs[f]` is the in-bounds address
  (with the provenance `Machine::new` allocated) of the MiniRust function `f` that the program
  function table `fnMap` (`fnNameMap`, the naming `translateProg` uses) assigns to
  `entry.defPath`.

Trusted function pointers carry allocation-identity provenance (the function's synthetic
`AllocId`, offset `0`) and no integer address; MiniRust function pointers carry the address and
provenance of the function's allocation. The relation therefore matches them through the
function they name. -/
def FnPtrRel {M : Type} [Gen.Memory M] (fnMap : FnMap) (mem : Memory) (m : Gen.Machine M)
    (tv : Value) (mv : Gen.Value M) : Prop :=
  ∃ (p : ProvenancePtr) (entry : FnPtrEntry) (f : Gen.FnName)
    (thin : Gen.ThinPointer (Gen.Memory.Provenance M)),
    tv = .ptr p 8 ∧ p.offsetBytes = 0 ∧ lookupBorrow mem.borrows p.tag = none ∧
      lookupFnPtr mem.fnPtrs p.allocId = some entry ∧
      fnPtrRegistered mem p.allocId = true ∧
      lookupFnName fnMap entry.defPath = some f ∧
      mapGet m.fn_ptrs f = some thin ∧
      inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true ∧
      mv = .Ptr ⟨thin, none⟩

section Rel

variable {M : Type} [Gen.Memory M]

/-- **B3 (Trusted side, `.ok`)**: on a related operand value, with a thin raw-pointer target and a
non-intrinsic `fn`-pointer (or unknown) source type, Trusted's `FnPtrToPtr` succeeds and returns
the operand value itself, leaving frame and memory unchanged. -/
theorem FnPtrRel.trusted_cast_ok {fnMap : FnMap} {mem : Memory} {m : Gen.Machine M} {tv : Value}
    {mv : Gen.Value M} (hRel : FnPtrRel fnMap mem m tv mv)
    (locals locals' : List LocalSlot) (op : Operand) (targetTy : Ty)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok tv locals')
    (hT : isThinRawPtrTy targetTy = true)
    (hS : fnPtrSrcTyValid (operandTy localDecls layouts op) = true) :
    evalRvalue locals (.cast .fnPtrToPtr op targetTy) mem localDecls layouts =
      .ok tv locals' mem := by
  obtain ⟨p, entry, f, thin, rfl, hoff, hB, _, hR, _, _, _, _⟩ := hRel
  exact (evalRvalue_fnPtrToPtr_ptr_ok_iff locals locals' op targetTy mem localDecls layouts p 8
    hOp _ _ _).mpr
    ⟨⟨rfl, rfl, rfl⟩, hT, hS, (fnPtrValueValid_eq_true_iff mem p 8).mpr ⟨rfl, hoff, hB, hR⟩⟩

/-- **B3 (Trusted `.ub` ⟹ unrelated)**: if Trusted's `FnPtrToPtr` is `.ub` on an operand value
`tv` although the target is a thin raw pointer and the source type is a non-intrinsic `fn`
pointer, then `tv` is related to **no** MiniRust function pointer (on no machine). -/
theorem trusted_ub_not_FnPtrRel (fnMap : FnMap) (mem : Memory) (m : Gen.Machine M) (tv : Value)
    (locals locals' : List LocalSlot) (op : Operand) (targetTy : Ty)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok tv locals')
    (hT : isThinRawPtrTy targetTy = true)
    (hS : fnPtrSrcTyValid (operandTy localDecls layouts op) = true)
    (hUb : evalRvalue locals (.cast .fnPtrToPtr op targetTy) mem localDecls layouts = .ub) :
    ∀ mv : Gen.Value M, ¬ FnPtrRel fnMap mem m tv mv := by
  intro mv hRel
  have h := hRel.trusted_cast_ok locals locals' op targetTy localDecls layouts hOp hT hS
  rw [hUb] at h
  cases h

/-- A borrow-backed pointer (the value of `&raw const x`) is related to no MiniRust function
pointer. -/
theorem borrowed_not_FnPtrRel (fnMap : FnMap) (mem : Memory) (m : Gen.Machine M)
    (p : ProvenancePtr) (sz : Nat) (entry : BorrowEntry)
    (hB : lookupBorrow mem.borrows p.tag = some entry) :
    ∀ mv : Gen.Value M, ¬ FnPtrRel fnMap mem m (.ptr p sz) mv := by
  rintro mv ⟨p', _, _, _, hv, _, hB', _⟩
  cases hv
  rw [hB] at hB'
  cases hB'

variable [MemoryOps M]

/-- **B3 (MiniRust side, `.ok`, every `Machine M`)**: on a related operand value, the
`FnPtr → thin raw pointer` transmute succeeds and returns the operand value itself. -/
theorem FnPtrRel.minirust_cast_ok {fnMap : FnMap} {mem : Memory} {m : Gen.Machine M}
    {tv : Value} {mv : Gen.Value M} (hRel : FnPtrRel fnMap mem m tv mv)
    (m? : Option (Gen.Machine M)) :
    evalUnOpM (M := M) (.Cast (.Transmute (.Ptr (.Raw .None)))) (mv, .Ptr .FnPtr) m? =
      .ok (mv, .Ptr (.Raw .None)) := by
  obtain ⟨_, _, _, ⟨addr, prov⟩, _, _, _, _, _, _, _, hIn, rfl⟩ := hRel
  exact evalUnOpM_fnPtrToPtr_ok m? addr prov hIn

/-- **B3 (preservation, every `Machine M`, in particular `Mach` and `MachTB`)**: the cast
preserves the function-pointer relation. If the operand values are related, then Trusted's
`evalRvalue (.cast .fnPtrToPtr ..)` and MiniRust's `Transmute` both succeed, and their results are
related again (to the same function). -/
theorem fnPtrToPtr_preserves_FnPtrRel {fnMap : FnMap} {mem : Memory} {m : Gen.Machine M}
    {tv : Value} {mv : Gen.Value M} (hRel : FnPtrRel fnMap mem m tv mv)
    (locals locals' : List LocalSlot) (op : Operand) (targetTy : Ty)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok tv locals')
    (hT : isThinRawPtrTy targetTy = true)
    (hS : fnPtrSrcTyValid (operandTy localDecls layouts op) = true) :
    ∃ (tv' : Value) (mv' : Gen.Value M),
      evalRvalue locals (.cast .fnPtrToPtr op targetTy) mem localDecls layouts =
        .ok tv' locals' mem ∧
      evalUnOpM (M := M) (.Cast (.Transmute (.Ptr (.Raw .None)))) (mv, .Ptr .FnPtr) (some m) =
        .ok (mv', .Ptr (.Raw .None)) ∧
      FnPtrRel fnMap mem m tv' mv' :=
  ⟨tv, mv, hRel.trusted_cast_ok locals locals' op targetTy localDecls layouts hOp hT hS,
    hRel.minirust_cast_ok (some m), hRel⟩

/-- **B3 (function lookup under the relation)**: `Machine::fn_from_ptr` never rejects a related
MiniRust value with UB: it resolves a function name registered for exactly this pointer. When
distinct functions have distinct pointers (as `Machine::new` allocates them), that function is the
one the Trusted function-pointer entry names. -/
theorem FnPtrRel.fnFromPtrM_eq {fnMap : FnMap} {mem : Memory} {m : Gen.Machine M}
    {tv : Value} {mv : Gen.Value M} (hRel : FnPtrRel fnMap mem m tv mv)
    (hInj : ∀ e₁ ∈ m.fn_ptrs.entries, ∀ e₂ ∈ m.fn_ptrs.entries, e₁.2 = e₂.2 → e₁.1 = e₂.1) :
    ∃ (p : ProvenancePtr) (entry : FnPtrEntry) (f : Gen.FnName),
      tv = .ptr p 8 ∧ lookupFnPtr mem.fnPtrs p.allocId = some entry ∧
        lookupFnName fnMap entry.defPath = some f ∧
        fnFromPtrM (M := M) m mv =
          mapIndex m.prog.functions f "self.prog.functions[func_name]" := by
  obtain ⟨p, entry, f, thin, rfl, _, _, hL, _, hN, hG, _, rfl⟩ := hRel
  refine ⟨p, entry, f, rfl, hL, hN, ?_⟩
  rw [fnFromPtrM_thin_eq]
  unfold mapGet at hG
  cases hf : m.fn_ptrs.entries.find? (fun e => decide (e.1 = f)) with
  | none => rw [hf] at hG; cases hG
  | some e0 =>
    rw [hf] at hG
    have he0 : e0.2 = thin := by simpa using hG
    have hmem0 := List.mem_of_find?_eq_some hf
    have hf0 : e0.1 = f := by simpa using List.find?_some hf
    cases hfind : m.fn_ptrs.entries.find?
        (fun (e : Gen.FnName × Gen.ThinPointer (Gen.Memory.Provenance M)) =>
          decide (e.2 = thin)) with
    | none =>
      exfalso
      rw [List.find?_eq_none] at hfind
      exact hfind e0 hmem0 (by simpa using he0)
    | some e1 =>
      have hmem1 := List.mem_of_find?_eq_some hfind
      have h1 : e1.2 = thin := by simpa using List.find?_some hfind
      have h2 : e1.1 = f := (hInj e1 hmem1 e0 hmem0 (h1.trans he0.symm)).trans hf0
      dsimp only
      rw [h2]

end Rel

/-- **B3 (preservation, `Mach` with the `BasicMemory`-specific interpreter `evalUnOp`)**. -/
theorem fnPtrToPtr_preserves_FnPtrRel_mach {fnMap : FnMap} {mem : Memory} {m : Mach}
    {tv : Value} {mv : Val} (hRel : FnPtrRel (M := BM) fnMap mem m tv mv)
    (locals locals' : List LocalSlot) (op : Operand) (targetTy : Ty)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok tv locals')
    (hT : isThinRawPtrTy targetTy = true)
    (hS : fnPtrSrcTyValid (operandTy localDecls layouts op) = true) :
    ∃ (tv' : Value) (mv' : Val),
      evalRvalue locals (.cast .fnPtrToPtr op targetTy) mem localDecls layouts =
        .ok tv' locals' mem ∧
      evalUnOp (.Cast (.Transmute (.Ptr (.Raw .None)))) (mv, .Ptr .FnPtr) (some m) =
        .ok (mv', .Ptr (.Raw .None)) ∧
      FnPtrRel (M := BM) fnMap mem m tv' mv' := by
  refine ⟨tv, mv, hRel.trusted_cast_ok locals locals' op targetTy localDecls layouts hOp hT hS,
    ?_, hRel⟩
  obtain ⟨_, _, _, ⟨addr, prov⟩, _, _, _, _, _, _, _, hIn, rfl⟩ := hRel
  exact evalUnOp_fnPtrToPtr_ok (some m) addr prov hIn

/-- **B3 (divergence: where the UB is raised)**. Trusted enforces "a `fn` pointer value points to
a function" *at the cast*: `FnPtrToPtr` on a borrow-backed data pointer is `.ub`
(`evalRvalue_fnPtrToPtr_borrowed_ub`). MiniRust does **not**: `check_value` at `PtrType::FnPtr`
only bounds the address, so the transmute that `minimize` emits **succeeds** on *every* in-bounds
thin pointer, including a data pointer that is not a function pointer; MiniRust raises the UB
only when the pointer is used as a function (`Machine::fn_from_ptr`, `"invalid pointer for
function lookup"`). The two semantics therefore agree on `.ok` (`fnPtrToPtr_preserves_FnPtrRel`),
and every Trusted `.ub` operand is unrelated to any MiniRust function pointer
(`trusted_ub_not_FnPtrRel`), but there is no cast-level UB parity: Trusted is strictly stricter
at the cast. -/
theorem fnPtrToPtr_data_pointer_divergence
    (locals locals' : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (p : ProvenancePtr) (sz : Nat) (entry : BorrowEntry)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr p sz) locals')
    (hB : lookupBorrow mem.borrows p.tag = some entry)
    {M : Type} [Gen.Memory M] [MemoryOps M] (m : Gen.Machine M)
    (thin : Gen.ThinPointer (Gen.Memory.Provenance M))
    (hIn : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hData : ∀ e ∈ m.fn_ptrs.entries, e.2 ≠ thin) :
    evalRvalue locals (.cast .fnPtrToPtr op targetTy) mem localDecls layouts = .ub ∧
      evalUnOpM (M := M) (.Cast (.Transmute (.Ptr (.Raw .None))))
          (.Ptr ⟨thin, none⟩, .Ptr .FnPtr) (some m) =
        .ok (.Ptr ⟨thin, none⟩, .Ptr (.Raw .None)) ∧
      fnFromPtrM (M := M) m (.Ptr ⟨thin, none⟩) =
        .error (.ub "invalid pointer for function lookup") :=
  ⟨evalRvalue_fnPtrToPtr_borrowed_ub locals locals' op targetTy mem localDecls layouts p sz entry
      hOp hB,
    evalUnOpM_fnPtrToPtr_ok (some m) thin.addr thin.provenance hIn,
    fnFromPtrM_unregistered_ub m thin hData⟩

/-! ### B4. Concrete lockstep witnesses

`fn callee()` is reified to a function pointer and cast to `*const ()`:
```text
_1 = callee as fn() (PointerCoercion(ReifyFnPointer));
_0 = move _1 as *const () (FnPtrToPtr);
```
next to the MiniRust expression `minimize` produces for it,
`build::transmute(build::fn_ptr(callee), <*const ()>::get_type())`, on a concrete `Mach`
(`BasicMemory`) and a concrete `MachTB` (`TreeBorrowsMemory`). -/

/-- `fn()`. -/
def wFnSig : RigidTy := .fnPtr [] (.tuple []) .safe .rust

/-- `fn()` as a `Ty`. -/
def wFnPtrTy : Ty := { kind := wFnSig, layoutIdx := 0 }

/-- `*const ()`. -/
def wRawUnitTy : Ty := { kind := .rawPtr .not (.tuple []), layoutIdx := 0 }

/-- `u32`. -/
def wU32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }

/-- `_0 : *const ()`, `_1 : fn()`, `_2 : u32`. -/
def wDecls : List LocalDecl := [
  { mutability := .mut, ty := wRawUnitTy, debugName := none },
  { mutability := .mut, ty := wFnPtrTy, debugName := none },
  { mutability := .mut, ty := wU32Ty, debugName := none }]

/-- A 64-bit little-endian layout table without entries. -/
def wLayouts : Layout.LayoutTable := { pointerBits := 64, isLittleEndian := true, entries := [] }

/-- The function item `bridge::callee` (a zero-sized constant of type `FnDef`). -/
def wFnItem : Operand :=
  .constant { ty := { kind := .fnDef "bridge::callee" [], layoutIdx := 0 }, val := .zeroSized }

/-- Frame before the reification: `_2 = 7_u32`. -/
def wLocals0 : List LocalSlot := [.uninit, .uninit, .init (.scalar ⟨7, 4⟩)]

/-- The function-pointer table entry `ReifyFnPointer` interns for `bridge::callee`. -/
def wFnEntry : FnPtrEntry :=
  { allocId := 65536, defPath := "bridge::callee", typeArgs := [], fnSig := some wFnSig }

/-- Memory after the reification. -/
def wMem1 : Memory := { emptyMemory with fnPtrs := [wFnEntry] }

/-- Frame after `_1 = callee as fn()`. -/
def wLocals1 : List LocalSlot :=
  [.uninit, .init (.ptr ⟨65536, 0⟩ 8), .init (.scalar ⟨7, 4⟩)]

/-- `copy _1`. -/
def wCopy1 : Operand := .copy { local_ := 1, projection := [] }

/-- **B4 (Trusted, reify)**: `callee as fn()` interns `bridge::callee` at the first synthetic
function-pointer allocation and returns the pointer `(65536, 0)`. -/
theorem wit_trusted_reify :
    evalRvalue wLocals0 (.cast (.pointerCoercion "ReifyFnPointer") wFnItem wFnPtrTy) emptyMemory
        wDecls wLayouts =
      .ok (.ptr ⟨65536, 0⟩ 8) wLocals0 wMem1 := rfl

/-- **B4 (Trusted, cast)**: `_1 as *const ()` returns the same pointer `(65536, 0)`; frame and
memory are unchanged. -/
theorem wit_trusted_fnPtrToPtr_ok :
    evalRvalue wLocals1 (.cast .fnPtrToPtr wCopy1 wRawUnitTy) wMem1 wDecls wLayouts =
      .ok (.ptr ⟨65536, 0⟩ 8) wLocals1 wMem1 :=
  (evalRvalue_fnPtrToPtr_ptr_ok_iff wLocals1 wLocals1 wCopy1 wRawUnitTy wMem1 wDecls wLayouts
    ⟨65536, 0⟩ 8 rfl _ _ _).mpr ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- **B4 (Trusted, wide target)**: `_1 as *const [u32]` is `.ub`. -/
theorem wit_trusted_fnPtrToPtr_wideTarget_ub :
    evalRvalue wLocals1
        (.cast .fnPtrToPtr wCopy1 { kind := .rawPtr .not (.slice (.uint .u32)), layoutIdx := 0 })
        wMem1 wDecls wLayouts = .ub :=
  evalRvalue_fnPtrToPtr_nonThinTarget_ub wLocals1 wLocals1 wCopy1 _ wMem1 wDecls wLayouts
    ⟨65536, 0⟩ 8 rfl rfl

/-- The MiniRust name of `bridge::callee`: `FnName(0)`. -/
def wFnName : Gen.FnName := fnName 0

/-- The program function table (`fnNameMap`) of the witness. -/
def wFnMap : FnMap := [("bridge::callee", (wFnName, .Rust))]

/-- A MiniRust function standing for `callee` (its body is irrelevant to the cast). -/
def wFn : Gen.Function :=
  { locals := ⟨[]⟩, args := [], ret := localName 0, calling_convention := .Rust, blocks := ⟨[]⟩,
    start := bbName 0, implicit_writes := false }

/-- The witness program. -/
def wProg : Gen.Program :=
  { functions := ⟨[(wFnName, wFn)]⟩, start := wFnName, globals := ⟨[]⟩, traits := ⟨[]⟩,
    vtables := ⟨[]⟩ }

/-- The function pointer of `callee` on `BasicMemory`: address `4096`, provenance `AllocId(0)`. -/
def wFnThin : Ptr := { addr := 4096, provenance := some (⟨0⟩, ()) }

/-- A `BasicMemory` machine whose `fn_ptrs` registers `callee` at `wFnThin`. -/
def wMach : Mach :=
  { prog := wProg, mem := ⟨⟨[], ⟨⟩⟩, []⟩, intptrcast := ⟨⟨[]⟩⟩, threads := [], active_thread := 0,
    synchronized_threads := ⟨[]⟩, locks := [], global_ptrs := ⟨[]⟩,
    fn_ptrs := ⟨[(wFnName, wFnThin)]⟩, vtable_ptrs := ⟨[]⟩, stdout := ⟨[]⟩, stderr := ⟨[]⟩ }

/-- The function pointer of `callee` on `TreeBorrowsMemory`: address `4096`, provenance
`(AllocId(0), [])` (the root of the allocation's borrow tree). -/
def wFnThinTB : Gen.ThinPointer (Gen.Memory.Provenance TBM) :=
  { addr := 4096, provenance := some (⟨0⟩, []) }

/-- A `TreeBorrowsMemory` machine whose `fn_ptrs` registers `callee` at `wFnThinTB`. -/
def wMachTB : MachTB :=
  { prog := wProg, mem := ⟨⟨⟨false⟩, ⟨[], ⟨⟩⟩⟩, []⟩, intptrcast := ⟨⟨[]⟩⟩, threads := [],
    active_thread := 0, synchronized_threads := ⟨[]⟩, locks := [], global_ptrs := ⟨[]⟩,
    fn_ptrs := ⟨[(wFnName, wFnThinTB)]⟩, vtable_ptrs := ⟨[]⟩, stdout := ⟨[]⟩, stderr := ⟨[]⟩ }

/-- **B4 (`Mach`)**: `Constant::FnPointer(callee)` evaluates to `fn_ptrs[callee]`, the transmute
to the thin raw pointer type returns that same pointer, the whole expression `minimize` emits
evaluates to it without changing the machine, and `fn_from_ptr` still resolves `callee` from the
cast result. -/
theorem wit_mach_lockstep :
    evalConstant wMach (.FnPointer wFnName) = .ok (.Ptr ⟨wFnThin, none⟩) ∧
      evalUnOp (.Cast (.Transmute (.Ptr (.Raw .None)))) (.Ptr ⟨wFnThin, none⟩, .Ptr .FnPtr)
          (some wMach) =
        .ok (.Ptr ⟨wFnThin, none⟩, .Ptr (.Raw .None)) ∧
      evalValue wMach (.UnOp (.Cast (.Transmute (.Ptr (.Raw .None)))) (fnPtrExpr wFnName)) =
        .ok ((.Ptr ⟨wFnThin, none⟩, .Ptr (.Raw .None)), wMach) ∧
      fnFromPtr wMach (.Ptr ⟨wFnThin, none⟩) = .ok wFn :=
  ⟨rfl, evalUnOp_fnPtrToPtr_ok (some wMach) 4096 _ (by decide), rfl, rfl⟩

/-- **B4 (`MachTB`)**: the same lockstep on `TreeBorrowsMemory`. -/
theorem wit_machTB_lockstep :
    evalConstantM wMachTB (.FnPointer wFnName) = .ok (.Ptr ⟨wFnThinTB, none⟩) ∧
      evalUnOpM (M := TBM) (.Cast (.Transmute (.Ptr (.Raw .None))))
          (.Ptr ⟨wFnThinTB, none⟩, .Ptr .FnPtr) (some wMachTB) =
        .ok (.Ptr ⟨wFnThinTB, none⟩, .Ptr (.Raw .None)) ∧
      fnFromPtrM wMachTB (.Ptr ⟨wFnThinTB, none⟩) = .ok wFn :=
  ⟨rfl, evalUnOpM_fnPtrToPtr_ok (some wMachTB) 4096 _ (by decide), rfl⟩

/-- **B4 (relation witness)**: the Trusted pointer `(65536, 0)` and the MiniRust pointers
`wFnThin` / `wFnThinTB` are related function pointers (`FnPtrRel` is inhabited on both memory
models), so `fnPtrToPtr_preserves_FnPtrRel` applies to this very cast. -/
theorem wit_FnPtrRel :
    FnPtrRel (M := BM) wFnMap wMem1 wMach (.ptr ⟨65536, 0⟩ 8) (.Ptr ⟨wFnThin, none⟩) ∧
      FnPtrRel (M := TBM) wFnMap wMem1 wMachTB (.ptr ⟨65536, 0⟩ 8) (.Ptr ⟨wFnThinTB, none⟩) :=
  ⟨⟨⟨65536, 0⟩, wFnEntry, wFnName, wFnThin, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩,
    ⟨⟨65536, 0⟩, wFnEntry, wFnName, wFnThinTB, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩⟩

/-- **B4 (lockstep through the relation)**: instantiating `fnPtrToPtr_preserves_FnPtrRel` on the
witness: both casts succeed and the results are related again, on `Mach` and on `MachTB`. -/
theorem wit_lockstep_preserved :
    (∃ tv' mv',
      evalRvalue wLocals1 (.cast .fnPtrToPtr wCopy1 wRawUnitTy) wMem1 wDecls wLayouts =
        .ok tv' wLocals1 wMem1 ∧
      evalUnOp (.Cast (.Transmute (.Ptr (.Raw .None)))) (.Ptr ⟨wFnThin, none⟩, .Ptr .FnPtr)
          (some wMach) = .ok (mv', .Ptr (.Raw .None)) ∧
      FnPtrRel (M := BM) wFnMap wMem1 wMach tv' mv') ∧
    (∃ tv' mv',
      evalRvalue wLocals1 (.cast .fnPtrToPtr wCopy1 wRawUnitTy) wMem1 wDecls wLayouts =
        .ok tv' wLocals1 wMem1 ∧
      evalUnOpM (M := TBM) (.Cast (.Transmute (.Ptr (.Raw .None))))
          (.Ptr ⟨wFnThinTB, none⟩, .Ptr .FnPtr) (some wMachTB) = .ok (mv', .Ptr (.Raw .None)) ∧
      FnPtrRel (M := TBM) wFnMap wMem1 wMachTB tv' mv') :=
  ⟨fnPtrToPtr_preserves_FnPtrRel_mach wit_FnPtrRel.1 wLocals1 wLocals1 wCopy1 wRawUnitTy wDecls
      wLayouts rfl rfl rfl,
    fnPtrToPtr_preserves_FnPtrRel wit_FnPtrRel.2 wLocals1 wLocals1 wCopy1 wRawUnitTy wDecls
      wLayouts rfl rfl rfl⟩

/-- Frame in which the `fn()` local `_1` holds the value of `&raw const _2` (as after a
transmute of the data pointer to `fn()`). -/
def wLocalsB : List LocalSlot := [.uninit, .init (.ptr ⟨1, 0⟩ 8), .init (.scalar ⟨7, 4⟩)]

/-- **B4 (Trusted, stack-borrowed data pointer)**: `&raw const _2` evaluates to the borrow-backed
pointer `(1, 0)` (tag `1` is a live borrow-table entry for `_2`), and `FnPtrToPtr` on a `fn()`
local holding that pointer is `.ub`. -/
theorem wit_trusted_borrowed_ub :
    ∃ (mem' : Memory) (e : BorrowEntry),
      evalRvalue wLocals0 (.rawPtr .not { local_ := 2, projection := [] }) emptyMemory wDecls
          wLayouts = .ok (.ptr ⟨1, 0⟩ 8) wLocals0 mem' ∧
      lookupBorrow mem'.borrows (ProvenancePtr.tag ⟨1, 0⟩) = some e ∧
      evalRvalue wLocalsB (.cast .fnPtrToPtr wCopy1 wRawUnitTy) mem' wDecls wLayouts = .ub := by
  refine ⟨_, _, rfl, rfl, ?_⟩
  exact evalRvalue_fnPtrToPtr_borrowed_ub wLocalsB wLocalsB wCopy1 wRawUnitTy _ wDecls wLayouts
    ⟨1, 0⟩ 8 _ rfl rfl

/-- Frame in which the `fn()` local `_1` holds a pointer into the synthetic function-pointer
range that no `ReifyFnPointer` ever interned. -/
def wLocalsE : List LocalSlot := [.uninit, .init (.ptr ⟨70000, 0⟩ 8), .init (.scalar ⟨7, 4⟩)]

/-- **B4 (the relation is not complete for Trusted `.ok`)**. With an *empty* function-pointer
table Trusted accepts every pointer in the synthetic function-pointer range
(`isFnPtrAllocId`), even one that no reification produced: the cast is `.ok`, yet the pointer
names no function and is related to no MiniRust function pointer. So `FnPtrRel` gives
"related ⟹ both casts succeed" and "Trusted `.ub` ⟹ unrelated", but not
"Trusted `.ok` ⟹ related". -/
theorem wit_trusted_empty_table_accepts_unregistered {M : Type} [Gen.Memory M] (fnMap : FnMap)
    (m : Gen.Machine M) :
    evalRvalue wLocalsE (.cast .fnPtrToPtr wCopy1 wRawUnitTy) emptyMemory wDecls wLayouts =
        .ok (.ptr ⟨70000, 0⟩ 8) wLocalsE emptyMemory ∧
      ∀ mv : Gen.Value M, ¬ FnPtrRel fnMap emptyMemory m (.ptr ⟨70000, 0⟩ 8) mv := by
  refine ⟨(evalRvalue_fnPtrToPtr_ptr_ok_iff wLocalsE wLocalsE wCopy1 wRawUnitTy emptyMemory wDecls
    wLayouts ⟨70000, 0⟩ 8 rfl _ _ _).mpr ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩, ?_⟩
  rintro mv ⟨p, entry, _, _, hv, _, _, hL, _⟩
  cases hv
  cases hL

/-- A MiniRust pointer to stack *data* on `BasicMemory` (the address of a local's allocation). -/
def wDataThin : Ptr := { addr := 128, provenance := some (⟨1⟩, ()) }

/-- A MiniRust pointer to stack *data* on `TreeBorrowsMemory`. -/
def wDataThinTB : Gen.ThinPointer (Gen.Memory.Provenance TBM) :=
  { addr := 128, provenance := some (⟨1⟩, []) }

/-- **B4 (MiniRust, data pointer)**: on both machines the transmute of a data pointer at
`PtrType::FnPtr` *succeeds* (the divergence of `fnPtrToPtr_data_pointer_divergence`), and
`fn_from_ptr` rejects the pointer with UB `"invalid pointer for function lookup"`. -/
theorem wit_minirust_data_pointer :
    (evalUnOp (.Cast (.Transmute (.Ptr (.Raw .None)))) (.Ptr ⟨wDataThin, none⟩, .Ptr .FnPtr)
          (some wMach) = .ok (.Ptr ⟨wDataThin, none⟩, .Ptr (.Raw .None)) ∧
      fnFromPtr wMach (.Ptr ⟨wDataThin, none⟩) =
        .error (.ub "invalid pointer for function lookup")) ∧
    (evalUnOpM (M := TBM) (.Cast (.Transmute (.Ptr (.Raw .None))))
          (.Ptr ⟨wDataThinTB, none⟩, .Ptr .FnPtr) (some wMachTB) =
        .ok (.Ptr ⟨wDataThinTB, none⟩, .Ptr (.Raw .None)) ∧
      fnFromPtrM wMachTB (.Ptr ⟨wDataThinTB, none⟩) =
        .error (.ub "invalid pointer for function lookup")) :=
  ⟨⟨evalUnOp_fnPtrToPtr_ok (some wMach) 128 _ (by decide), rfl⟩,
    ⟨evalUnOpM_fnPtrToPtr_ok (some wMachTB) 128 _ (by decide), rfl⟩⟩

/-- **B4 (translation of the target type)**: `*const ()` translates to MiniRust's thin raw
pointer type, the transmute target used throughout B1. -/
theorem wit_translateTy_rawUnit :
    isThinRawPtrTy wRawUnitTy = true ∧ translateTy wLayouts wRawUnitTy = some (.Ptr (.Raw .None)) :=
  ⟨rfl, rfl⟩

/-! ## A. `Rvalue.nullaryOp` -/

/-! ### A0. Trusted `evalNullaryOp`: normal forms -/

/-- Trusted's `isize::MAX` object-size bound for the layout table's pointer width:
`scalarModulus ptrBytes / 2 - 1` (the `maxObjSize` of `evalNullaryOp`). -/
def maxObjSize (layouts : Layout.LayoutTable) : Nat :=
  Nat.sub (Nat.div (scalarModulus (layoutPointerBytes layouts)) 2) 1

/-- On a 64-bit layout table, pointers are 8 bytes wide. -/
theorem layoutPointerBytes_of_64 (layouts : Layout.LayoutTable) (h : layouts.pointerBits = 64) :
    layoutPointerBytes layouts = 8 := by
  unfold layoutPointerBytes
  rw [h]

/-- On a 64-bit layout table, Trusted's object-size bound is `isize::MAX = 2^63 - 1`. -/
theorem maxObjSize_of_64 (layouts : Layout.LayoutTable) (h : layouts.pointerBits = 64) :
    maxObjSize layouts = 9223372036854775807 := by
  unfold maxObjSize
  rw [layoutPointerBytes_of_64 layouts h]
  decide

/-- MiniRust's `Target::valid_size` on `x86_64` (`size.bytes().in_bounds(Signed, PTR_SIZE)`) is
the same `isize::MAX = 2^63 - 1` bound. -/
theorem valid_size_iff (sz : Nat) :
    x86_64.valid_size ⟨sz⟩ = true ↔ sz ≤ 9223372036854775807 := by
  have h : (2 : Int) ^ (Size.bits x86_64.PTR_SIZE - 1) = 9223372036854775808 := by decide
  simp only [x86_64.valid_size, inBounds, h, Bool.and_eq_true, decide_eq_true_eq]
  omega

private theorem bool_match_eq_ite {α : Type} (b : Bool) (p : Prop) [Decidable p]
    (h : b = true ↔ p) (t e : α) :
    (match (generalizing := false) b with
      | true => t
      | false => e) = if p then t else e := by
  cases b with
  | true =>
    have hp : p := h.mp rfl
    simp [hp]
  | false =>
    have hp : ¬ p := fun hp => by have := h.mpr hp; cases this
    simp [hp]

private theorem ble_iff (a b : Nat) : Nat.ble a b = true ↔ a ≤ b :=
  ⟨Nat.le_of_ble_eq_true, Nat.ble_eq_true_of_le⟩

/-- **A1 (Trusted, normal form)**: `SizeOf(T)` is the `usize` scalar
`intrinsicRigidTyByteSize T` when that size is resolved and at most `isize::MAX`, and
`.unsupported` otherwise; it never touches the frame or memory. -/
theorem evalNullaryOp_sizeOf_eq (locals : List LocalSlot) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) :
    evalNullaryOp locals .sizeOf ty mem localDecls layouts =
      match intrinsicRigidTyByteSize localDecls layouts ty.kind with
      | some sz =>
        if sz ≤ maxObjSize layouts then
          .ok (.scalar ⟨sz, layoutPointerBytes layouts⟩) locals mem
        else .unsupported
      | none => .unsupported := by
  have h : evalNullaryOp locals .sizeOf ty mem localDecls layouts =
      match intrinsicRigidTyByteSize localDecls layouts ty.kind with
      | some sz =>
        (match Nat.ble sz (maxObjSize layouts) with
          | true => .ok (.scalar ⟨sz, layoutPointerBytes layouts⟩) locals mem
          | false => .unsupported)
      | none => .unsupported := rfl
  rw [h]
  cases intrinsicRigidTyByteSize localDecls layouts ty.kind with
  | none => rfl
  | some sz => exact bool_match_eq_ite _ (sz ≤ maxObjSize layouts) (ble_iff _ _) _ _

/-- **A2 (Trusted, normal form)**: `AlignOf(T)` is the `usize` scalar `intrinsicRigidTyAlign T`
when the size is resolved and at most `isize::MAX` and the alignment is a power of two below
`2^(8 * ptrBytes)`, and `.unsupported` otherwise. -/
theorem evalNullaryOp_alignOf_eq (locals : List LocalSlot) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) :
    evalNullaryOp locals .alignOf ty mem localDecls layouts =
      match intrinsicRigidTyByteSize localDecls layouts ty.kind,
        intrinsicRigidTyAlign localDecls layouts ty.kind with
      | some sz, some al =>
        if sz ≤ maxObjSize layouts ∧ Layout.Align.isPowerOfTwoBytes ⟨al⟩ = true ∧
            al < scalarModulus (layoutPointerBytes layouts) then
          .ok (.scalar ⟨al, layoutPointerBytes layouts⟩) locals mem
        else .unsupported
      | _, _ => .unsupported := by
  have h : evalNullaryOp locals .alignOf ty mem localDecls layouts =
      match intrinsicRigidTyByteSize localDecls layouts ty.kind,
        intrinsicRigidTyAlign localDecls layouts ty.kind with
      | some sz, some al =>
        (match Bool.and (Nat.ble sz (maxObjSize layouts))
            (Bool.and (Layout.Align.isPowerOfTwoBytes ⟨al⟩)
              (Nat.blt al (scalarModulus (layoutPointerBytes layouts)))) with
          | true => .ok (.scalar ⟨al, layoutPointerBytes layouts⟩) locals mem
          | false => .unsupported)
      | _, _ => .unsupported := rfl
  rw [h]
  cases intrinsicRigidTyByteSize localDecls layouts ty.kind with
  | none => rfl
  | some sz =>
    cases intrinsicRigidTyAlign localDecls layouts ty.kind with
    | none => rfl
    | some al =>
      refine bool_match_eq_ite _ (sz ≤ maxObjSize layouts ∧
        Layout.Align.isPowerOfTwoBytes ⟨al⟩ = true ∧
        al < scalarModulus (layoutPointerBytes layouts)) ?_ _ _
      rw [Bool.and_eq_true, Bool.and_eq_true]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨Nat.le_of_ble_eq_true h1, h2, Nat.le_of_ble_eq_true h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨Nat.ble_eq_true_of_le h1, h2, Nat.ble_eq_true_of_le h3⟩

/-- **A3 (Trusted, normal form)**: `OffsetOf(T, fields)` is the `usize` scalar
`resolveOffsetOfPath .. fields` when the size of `T` is resolved and at most `isize::MAX`, the
path resolves, and the offset is at most the size; `.unsupported` otherwise. -/
theorem evalNullaryOp_offsetOf_eq (locals : List LocalSlot) (fields : List (VariantIdx × FieldIdx))
    (ty : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) :
    evalNullaryOp locals (.offsetOf fields) ty mem localDecls layouts =
      match intrinsicRigidTyByteSize localDecls layouts ty.kind,
        resolveOffsetOfPath layouts (intrinsicRigidTyByteSize localDecls layouts)
          (intrinsicRigidTyAlign localDecls layouts) (findDeclLayoutForRigidTy localDecls layouts)
          (some ty.kind) (findDeclLayoutForRigidTy localDecls layouts ty.kind) fields with
      | some sz, some off =>
        if sz ≤ maxObjSize layouts ∧ off ≤ sz then
          .ok (.scalar ⟨off, layoutPointerBytes layouts⟩) locals mem
        else .unsupported
      | _, _ => .unsupported := by
  have h : evalNullaryOp locals (.offsetOf fields) ty mem localDecls layouts =
      match intrinsicRigidTyByteSize localDecls layouts ty.kind with
      | some sz =>
        (match resolveOffsetOfPath layouts (intrinsicRigidTyByteSize localDecls layouts)
            (intrinsicRigidTyAlign localDecls layouts)
            (findDeclLayoutForRigidTy localDecls layouts)
            (some ty.kind) (findDeclLayoutForRigidTy localDecls layouts ty.kind) fields with
          | some off =>
            (match Bool.and (Nat.ble sz (maxObjSize layouts)) (Nat.ble off sz) with
              | true => .ok (.scalar ⟨off, layoutPointerBytes layouts⟩) locals mem
              | false => .unsupported)
          | none => .unsupported)
      | none => .unsupported := rfl
  rw [h]
  cases intrinsicRigidTyByteSize localDecls layouts ty.kind with
  | none => rfl
  | some sz =>
    cases resolveOffsetOfPath layouts (intrinsicRigidTyByteSize localDecls layouts)
        (intrinsicRigidTyAlign localDecls layouts) (findDeclLayoutForRigidTy localDecls layouts)
        (some ty.kind) (findDeclLayoutForRigidTy localDecls layouts ty.kind) fields with
    | none => rfl
    | some off =>
      refine bool_match_eq_ite _ (sz ≤ maxObjSize layouts ∧ off ≤ sz) ?_ _ _
      rw [Bool.and_eq_true]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨Nat.ble_eq_true_of_le h1, Nat.ble_eq_true_of_le h2⟩

/-- **A (Trusted, no UB)**: `Rvalue.nullaryOp` is never undefined behavior — every unresolved
layout, out-of-range field, non-`bool` `UbChecks`, and `ContractChecks` fails closed with
`.unsupported`. -/
theorem evalNullaryOp_ne_ub (locals : List LocalSlot) (op : NullOp) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) :
    evalNullaryOp locals op ty mem localDecls layouts ≠ .ub := by
  cases op with
  | sizeOf =>
    rw [evalNullaryOp_sizeOf_eq]
    split
    · split <;> (intro h; cases h)
    · intro h; cases h
  | alignOf =>
    rw [evalNullaryOp_alignOf_eq]
    split
    · split <;> (intro h; cases h)
    · intro h; cases h
  | offsetOf fields =>
    rw [evalNullaryOp_offsetOf_eq]
    split
    · split <;> (intro h; cases h)
    · intro h; cases h
  | ubChecks =>
    unfold evalNullaryOp
    dsimp only
    split <;> (intro h; cases h)
  | contractChecks => intro h; cases h

/-- **A (Trusted, state)**: a successful `Rvalue.nullaryOp` returns the frame and the memory
unchanged. -/
theorem evalNullaryOp_ok_state (locals : List LocalSlot) (op : NullOp) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) (v : Value)
    (locals' : List LocalSlot) (mem' : Memory)
    (h : evalNullaryOp locals op ty mem localDecls layouts = .ok v locals' mem') :
    locals' = locals ∧ mem' = mem := by
  cases op with
  | sizeOf =>
    rw [evalNullaryOp_sizeOf_eq] at h
    split at h
    · split at h <;> cases h
      exact ⟨rfl, rfl⟩
    · cases h
  | alignOf =>
    rw [evalNullaryOp_alignOf_eq] at h
    split at h
    · split at h <;> cases h
      exact ⟨rfl, rfl⟩
    · cases h
  | offsetOf fields =>
    rw [evalNullaryOp_offsetOf_eq] at h
    split at h
    · split at h <;> cases h
      exact ⟨rfl, rfl⟩
    · cases h
  | ubChecks =>
    unfold evalNullaryOp at h
    dsimp only at h
    split at h <;> cases h
    exact ⟨rfl, rfl⟩
  | contractChecks => cases h

/-! ### A1/A2. `SizeOf` / `AlignOf` ↔ MiniRust `Type::layout` -/

private theorem align_to_eq_self (size align : Nat) (h : size % align = 0) :
    Size.align_to ⟨size⟩ ⟨align⟩ = ⟨size⟩ := by
  unfold Size.align_to
  congr 1
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero h
  rcases Nat.eq_zero_or_pos align with h0 | hpos
  · subst h0
    simp
  · have h1 : align * q + align - 1 = align * q + (align - 1) := by omega
    rw [h1, Nat.mul_add_div hpos, Nat.div_eq_of_lt (by omega), Nat.add_zero, Nat.mul_comm]

private theorem mulInt_ofNat (n c : Nat) : Size.mulInt ⟨n⟩ (Int.ofNat c) = .ok ⟨n * c⟩ := by
  have h0 : (0 : Int) ≤ (n : Int) * (c : Int) :=
    Int.mul_nonneg (Int.natCast_nonneg n) (Int.natCast_nonneg c)
  have h1 : ((n : Int) * (c : Int)).toNat = n * c := by
    have : (n : Int) * (c : Int) = ((n * c : Nat) : Int) := by push_cast; rfl
    rw [this, Int.toNat_natCast]
  show (match Size.from_bytes ((n : Int) * (c : Int)) with
    | some sz => pure sz
    | none => specPanic "Size * Int: negative byte count") = _
  unfold Size.from_bytes
  simp only [h0, ↓reduceIte, h1]
  rfl

/-- Integer types: Trusted's primitive size and alignment are MiniRust's `Type::Int` layout
(`int_type.size`, `int_type.align::<x86_64>()`), for every declaration list and layout table. -/
theorem layout_int_agrees {k : RigidTy} {s : Signedness} {n : Nat}
    (h : intTyBytes k = some (s, n)) (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) :
    intrinsicRigidTyByteSize localDecls layouts k = some n ∧
      intrinsicRigidTyAlign localDecls layouts k = some n ∧
      Interp.Type.layout (.Int ⟨s, ⟨n⟩⟩) = .ok (.Sized ⟨n⟩ ⟨n⟩) := by
  cases k with
  | uint u => cases u <;> cases h <;> exact ⟨rfl, rfl, rfl⟩
  | int i => cases i <;> cases h <;> exact ⟨rfl, rfl, rfl⟩
  | _ => simp [intTyBytes] at h

/-- Integer arrays `[Int; c]`: Trusted's `elemSize * c` and element alignment are MiniRust's
`Type::Array` layout (`elem.size * count`, `elem.align`). -/
theorem layout_intArray_agrees {ek : RigidTy} {s : Signedness} {n : Nat}
    (h : intTyBytes ek = some (s, n)) (c : Nat) (localDecls : List LocalDecl)
    (layouts : Layout.LayoutTable) :
    intrinsicRigidTyByteSize localDecls layouts (.array ek c) = some (n * c) ∧
      intrinsicRigidTyAlign localDecls layouts (.array ek c) = some n ∧
      Interp.Type.layout (.Array (.Int ⟨s, ⟨n⟩⟩) (Int.ofNat c)) = .ok (.Sized ⟨n * c⟩ ⟨n⟩) := by
  have hL := (layout_int_agrees h localDecls layouts).2.2
  have hMr : Interp.Type.layout (.Array (.Int ⟨s, ⟨n⟩⟩) (Int.ofNat c)) =
      .ok (.Sized ⟨n * c⟩ ⟨n⟩) := by
    simp only [Interp.Type.layout] at hL ⊢
    rw [hL, okBind, expectSize_sized, okBind, expectAlign_sized, okBind, mulInt_ofNat, okBind]
    rfl
  refine ⟨?_, ?_, hMr⟩
  · cases ek with
    | uint u => cases u <;> cases h <;> rfl
    | int i => cases i <;> cases h <;> rfl
    | _ => simp [intTyBytes] at h
  · cases ek with
    | uint u => cases u <;> cases h <;> rfl
    | int i => cases i <;> cases h <;> rfl
    | _ => simp [intTyBytes] at h

/-- Raw pointers: Trusted's `8` (thin) / `16` (slice, `str`) bytes at alignment `8` are MiniRust's
`Type::Ptr(PtrType::Raw { meta_kind })` layout (`PTR_SIZE` or `2 * PTR_SIZE`, `PTR_ALIGN`). -/
theorem layout_rawPtr_agrees {pointee : RigidTy} {mk : Gen.PointerMetaKind}
    (h : rawPtrMetaKind pointee = some mk) (m : MirAst.Mutability) (localDecls : List LocalDecl)
    (layouts : Layout.LayoutTable) :
    ∃ sz, intrinsicRigidTyByteSize localDecls layouts (.rawPtr m pointee) = some sz ∧
      intrinsicRigidTyAlign localDecls layouts (.rawPtr m pointee) = some 8 ∧
      Interp.Type.layout (.Ptr (.Raw mk)) = .ok (.Sized ⟨sz⟩ ⟨8⟩) := by
  cases pointee <;> simp [rawPtrMetaKind] at h <;>
    first
    | (subst h; exact ⟨8, rfl, rfl, rfl⟩)
    | (subst h; exact ⟨16, rfl, rfl, rfl⟩)
    | (obtain ⟨_, h⟩ := h; subst h; exact ⟨8, rfl, rfl, rfl⟩)
    | (obtain ⟨_, h⟩ := h; subst h; exact ⟨16, rfl, rfl, rfl⟩)

private theorem pointeeInfo_meta_kind_none :
    ∀ (fuel : Nat) (pointee : RigidTy) (info : Gen.PointeeInfo),
      pointeeInfoOfRigidTyAux fuel pointee = some info →
      LayoutStrategy.meta_kind info.layout = .None := by
  intro fuel
  induction fuel with
  | zero => intro pointee info h; simp [pointeeInfoOfRigidTyAux] at h
  | succ n ih =>
    intro pointee info h
    unfold pointeeInfoOfRigidTyAux at h
    split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · split at h
        · cases h
        · split at h
          · cases hin : pointeeInfoOfRigidTyAux n _ with
            | none => rw [hin] at h; cases h
            | some ii =>
              rw [hin] at h
              dsimp only [bind, Option.bind] at h
              split at h
              · cases h; rfl
              · cases h
          · split at h
            · split at h
              · cases h; rfl
              · cases h
            · cases h
      · cases h; rfl
      · cases h; rfl
      · cases h; rfl
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨⟨_, _⟩, _, rfl⟩ := h
        rfl
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨⟨_, _⟩, _, rfl⟩ := h
        rfl
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨⟨_, _⟩, _, rfl⟩ := h
        rfl
      · split at h
        · cases h; rfl
        · cases h
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨_, _, rfl⟩ := h
        rfl
      · cases h

/-- References: Trusted's `8` bytes at alignment `8` are MiniRust's `Type::Ptr(PtrType::Ref ..)`
layout for every reference type of the fragment (their pointees are sized, so the pointer is
thin). -/
theorem layout_ref_agrees {ty : Ty} {t : Gen.Type} (h : refTypeOf ty = some t)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) :
    intrinsicRigidTyByteSize localDecls layouts ty.kind = some 8 ∧
      intrinsicRigidTyAlign localDecls layouts ty.kind = some 8 ∧
      Interp.Type.layout t = .ok (.Sized ⟨8⟩ ⟨8⟩) := by
  rcases ty with ⟨k, idx⟩
  cases k <;> try (simp [refTypeOf] at h; done)
  case ref m pointee =>
    have hMr : Interp.Type.layout t = .ok (.Sized ⟨8⟩ ⟨8⟩) := by
      unfold refTypeOf at h
      dsimp only at h
      split at h
      · cases h
        rfl
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨info, hinfo, rfl⟩ := h
        have hmk := pointeeInfo_meta_kind_none _ _ _ hinfo
        simp only [Interp.Type.layout, PtrType.meta_kind, hmk, ↓reduceIte]
        rfl
    refine ⟨?_, ?_, hMr⟩
    · cases pointee <;>
        first
        | rfl
        | (simp [refTypeOf, intTyBytes, pointeeInfoOfRigidTy, pointeeInfoOfRigidTyAux] at h; done)
    · rfl

/-- `Box<T>`: MiniRust's `Type::Ptr(PtrType::Box ..)` layout is a thin pointer (`8` bytes at
alignment `8`) for every `Box` type of the fragment. -/
theorem layout_box_minirust {ty : Ty} {t : Gen.Type} (h : boxTypeOf ty = some t) :
    Interp.Type.layout t = .ok (.Sized ⟨8⟩ ⟨8⟩) := by
  rcases ty with ⟨k, idx⟩
  unfold boxTypeOf at h
  dsimp only at h
  split at h
  · split at h
    · rw [Option.map_eq_some_iff] at h
      obtain ⟨info, hinfo, rfl⟩ := h
      have hmk := pointeeInfo_meta_kind_none _ _ _ hinfo
      simp only [Interp.Type.layout, PtrType.meta_kind, hmk, ↓reduceIte]
      rfl
    · cases h
  · cases h

/-- Tuples and single-variant structs: MiniRust's layout of `build::tuple_ty(fields, size, align)`
is `(size.align_to(align), align)` (`TupleHeadLayout::head_size_and_align`). -/
theorem layout_tupleSpec (fields : List (Nat × TupleSpec)) (size align : Nat) :
    Interp.Type.layout (TupleSpec.tuple fields size align).toMiniRustTy =
      .ok (.Sized (Size.align_to ⟨size⟩ ⟨align⟩) ⟨align⟩) := by
  simp only [TupleSpec.toMiniRustTy, Interp.Type.layout, TupleHeadLayout.head_size_and_align]
  rfl

/-- `(Int, bool)` tuples: MiniRust's layout of `IntType::with_overflow`. -/
theorem layout_intBoolTuple (it : Gen.IntType) :
    Interp.Type.layout (intBoolTupleTy it) =
      .ok (.Sized (Size.align_to ⟨it.size.bytes + it.size.bytes⟩ ⟨it.size.bytes⟩)
        ⟨it.size.bytes⟩) := by
  simp only [intBoolTupleTy, Interp.Type.layout, TupleHeadLayout.head_size_and_align]
  rfl

/-- `core::cmp::Ordering`: MiniRust's layout of the translated `repr(i8)` enum is `(1, 1)`. -/
theorem layout_ordering : Interp.Type.layout orderingTy = .ok (.Sized ⟨1⟩ ⟨1⟩) := rfl

/-- **Normal form of `translateTy`**: the type translation tries, in this order, `bool`,
`core::cmp::Ordering`, `(Int, bool)`, the integer types, integer arrays, tuples and single-variant
structs (from the `ty.layoutIdx` entry), raw pointers, references, and `Box`. -/
theorem translateTy_eq (layouts : Layout.LayoutTable) (ty : Ty) :
    translateTy layouts ty =
      if isBoolTy ty then some .Bool
      else if isOrderingTy ty then some orderingTy
      else
        match intBoolTupleOf ty with
        | some it => some (intBoolTupleTy it)
        | none =>
          match intTypeOf ty with
          | some it => some (.Int it)
          | none =>
            match arrayTypeOf ty with
            | some (elemIt, count) => some (.Array (.Int elemIt) (Int.ofNat count))
            | none =>
              match tupleTypeOf layouts ty with
              | some (fields, size, align) =>
                some (TupleSpec.tuple fields size align).toMiniRustTy
              | none =>
                match rawPtrTypeOf ty with
                | some t => some t
                | none =>
                  match refTypeOf ty with
                  | some t => some t
                  | none => boxTypeOf ty := by
  unfold translateTy scalarTypeOf
  cases hB : isBoolTy ty with
  | true => rfl
  | false =>
    cases hO : isOrderingTy ty with
    | true => rfl
    | false =>
      cases hIB : intBoolTupleOf ty with
      | some it => rfl
      | none =>
        cases hI : intTypeOf ty with
        | some it => rfl
        | none => rfl

/-- The size and alignment `minimize` reads off `rustc`'s layout for the *aggregate* kinds of the
translated fragment (tuples and ADTs): the fixed ABI of `core::cmp::Ordering` (`repr(i8)`:
`(1, 1)`), of `(Int, bool)` (`IntType::with_overflow`: `(2 * n, n)`), and of `Box<T>` (a thin
pointer: `(8, 8)`), and otherwise the size and alignment recorded in the `ty.layoutIdx` entry of
the layout table (`tuple_from_layout` / `translate_non_enum_adt`). `none` for every other kind
(primitives, arrays, pointers), whose layouts neither side reads from the table. -/
def aggLayoutOf (layouts : Layout.LayoutTable) (ty : Ty) : Option (Nat × Nat) :=
  if isOrderingTy ty then some (1, 1)
  else
    match intBoolTupleOf ty with
    | some it => some (it.size.bytes + it.size.bytes, it.size.bytes)
    | none =>
      match tupleTypeOf layouts ty with
      | some (_, size, align) => some (size, align)
      | none => (boxTypeOf ty).map (fun _ => (8, 8))

/-- **Declaration-layout coherence.** For an aggregate type (tuple or ADT), Trusted never computes
a layout from `ty.layoutIdx`: `intrinsicRigidTyByteSize` / `intrinsicRigidTyAlign` scan
`localDecls` for a local of the same kind and read *that* local's `TypeLayout`
(`findDeclLayoutForRigidTy`), falling back to a structural size for layout-free tuples.
`minimize` instead reads the layout of the type itself (`aggLayoutOf`). `rustc`'s `layout_of` is a
function of the type, so in captured MIR both sources agree; this predicate states that
agreement, together with `rustc`'s invariant that a size is a multiple of the alignment:

for the `(size, align)` that `minimize` reads for `ty`, Trusted's layout queries resolve exactly
that size and alignment, and `size % align = 0`.

It holds trivially (vacuous antecedent) for every non-aggregate type, and
`declLayoutCoherent_of_same_entry` derives it for tuples and structs from the raw table fact that
the declaration scan finds the `ty.layoutIdx` entry. -/
def DeclLayoutCoherent (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) (ty : Ty) :
    Prop :=
  ∀ size align, aggLayoutOf layouts ty = some (size, align) →
    intrinsicRigidTyByteSize localDecls layouts ty.kind = some size ∧
      intrinsicRigidTyAlign localDecls layouts ty.kind = some align ∧
      size % align = 0

private theorem isBoolTy_kind {ty : Ty} (h : isBoolTy ty = true) : ty.kind = .bool := by
  rcases ty with ⟨k, idx⟩
  cases k <;> simp [isBoolTy] at h
  rfl

private theorem intTypeOf_eq_some {ty : Ty} {it : Gen.IntType} (h : intTypeOf ty = some it) :
    intTyBytes ty.kind = some (it.signed, it.size.bytes) := by
  unfold intTypeOf at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨s, n⟩, hk, rfl⟩ := h
  exact hk

private theorem arrayTypeOf_eq_some {ty : Ty} {it : Gen.IntType} {c : Nat}
    (h : arrayTypeOf ty = some (it, c)) :
    ∃ ek, ty.kind = .array ek c ∧ intTyBytes ek = some (it.signed, it.size.bytes) := by
  rcases ty with ⟨k, idx⟩
  cases k <;> try (simp [arrayTypeOf] at h; done)
  case array ek c' =>
    unfold arrayTypeOf at h
    dsimp only at h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨⟨s, n⟩, hk, he⟩ := h
    cases he
    exact ⟨ek, rfl, hk⟩

private theorem rawPtrTypeOf_eq_some {ty : Ty} {t : Gen.Type} (h : rawPtrTypeOf ty = some t) :
    ∃ m pointee mk, ty.kind = .rawPtr m pointee ∧ rawPtrMetaKind pointee = some mk ∧
      t = .Ptr (.Raw mk) := by
  rcases ty with ⟨k, idx⟩
  cases k <;> try (simp [rawPtrTypeOf, rawPtrMetaOf] at h; done)
  case rawPtr m pointee =>
    unfold rawPtrTypeOf rawPtrMetaOf at h
    dsimp only at h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨mk, hk, rfl⟩ := h
    exact ⟨m, pointee, mk, rfl, hk, rfl⟩

/-- **A1/A2 (key lemma)**: for every type of the translated fragment
(`translateTy layouts ty = some mrTy`) whose declaration layout is coherent, Trusted's layout
queries resolve a size and an alignment, and MiniRust's `Type::layout` of the translated type is
`LayoutStrategy::Sized` with **exactly that size and alignment**. -/
theorem translateTy_layout_agrees (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (ty : Ty) (mrTy : Gen.Type) (hTr : translateTy layouts ty = some mrTy)
    (hDecl : DeclLayoutCoherent localDecls layouts ty) :
    ∃ sz al,
      intrinsicRigidTyByteSize localDecls layouts ty.kind = some sz ∧
        intrinsicRigidTyAlign localDecls layouts ty.kind = some al ∧
        Interp.Type.layout mrTy = .ok (.Sized ⟨sz⟩ ⟨al⟩) := by
  rw [translateTy_eq] at hTr
  by_cases hB : isBoolTy ty = true
  · simp only [hB] at hTr
    cases hTr
    rw [isBoolTy_kind hB]
    exact ⟨1, 1, rfl, rfl, rfl⟩
  · simp only [hB] at hTr
    by_cases hO : isOrderingTy ty = true
    · simp only [hO] at hTr
      cases hTr
      obtain ⟨h1, h2, _⟩ := hDecl 1 1 (by simp [aggLayoutOf, hO])
      exact ⟨1, 1, h1, h2, layout_ordering⟩
    · simp only [hO] at hTr
      cases hIB : intBoolTupleOf ty with
      | some it =>
        rw [hIB] at hTr
        cases hTr
        obtain ⟨h1, h2, h3⟩ := hDecl (it.size.bytes + it.size.bytes) it.size.bytes
          (by simp [aggLayoutOf, hO, hIB])
        exact ⟨_, _, h1, h2, by rw [layout_intBoolTuple, align_to_eq_self _ _ h3]⟩
      | none =>
        rw [hIB] at hTr
        cases hI : intTypeOf ty with
        | some it =>
          rw [hI] at hTr
          cases hTr
          obtain ⟨h1, h2, h3⟩ := layout_int_agrees (intTypeOf_eq_some hI) localDecls layouts
          exact ⟨_, _, h1, h2, h3⟩
        | none =>
          rw [hI] at hTr
          cases hA : arrayTypeOf ty with
          | some r =>
            rcases r with ⟨elemIt, count⟩
            rw [hA] at hTr
            cases hTr
            obtain ⟨ek, hk, hek⟩ := arrayTypeOf_eq_some hA
            rw [hk]
            obtain ⟨h1, h2, h3⟩ := layout_intArray_agrees hek count localDecls layouts
            exact ⟨_, _, h1, h2, h3⟩
          | none =>
            rw [hA] at hTr
            cases hT : tupleTypeOf layouts ty with
            | some r =>
              rcases r with ⟨fields, size, align⟩
              rw [hT] at hTr
              cases hTr
              obtain ⟨h1, h2, h3⟩ := hDecl size align (by simp [aggLayoutOf, hO, hIB, hT])
              exact ⟨_, _, h1, h2, by rw [layout_tupleSpec, align_to_eq_self _ _ h3]⟩
            | none =>
              rw [hT] at hTr
              cases hR : rawPtrTypeOf ty with
              | some t =>
                rw [hR] at hTr
                cases hTr
                obtain ⟨m, pointee, mk, hk, hmk, rfl⟩ := rawPtrTypeOf_eq_some hR
                rw [hk]
                obtain ⟨sz, h1, h2, h3⟩ := layout_rawPtr_agrees hmk m localDecls layouts
                exact ⟨_, _, h1, h2, h3⟩
              | none =>
                rw [hR] at hTr
                cases hRef : refTypeOf ty with
                | some t =>
                  rw [hRef] at hTr
                  cases hTr
                  obtain ⟨h1, h2, h3⟩ := layout_ref_agrees hRef localDecls layouts
                  exact ⟨_, _, h1, h2, h3⟩
                | none =>
                  rw [hRef] at hTr
                  have hBox : boxTypeOf ty = some mrTy := hTr
                  obtain ⟨h1, h2, _⟩ := hDecl 8 8 (by simp [aggLayoutOf, hO, hIB, hT, hBox])
                  exact ⟨_, _, h1, h2, layout_box_minirust hBox⟩

/-- **A1 (`SizeOf`, two-sided normal form)**. For every type of the translated fragment
(`translateTy layouts ty = some mrTy`) with a coherent declaration layout, on a 64-bit layout
table: MiniRust's `Type::layout` of the translated type is `Sized(sz, al)`, and Trusted's
`Rvalue.nullaryOp .sizeOf` returns **exactly that size** `sz` as an 8-byte `usize` scalar (frame
and memory unchanged) when `sz` is a valid object size for the target (`Target::valid_size`:
`sz ≤ isize::MAX`), and fails closed with `.unsupported` — never a wrong size, never `.ub` —
otherwise. -/
theorem nullaryOp_sizeOf_minirust_layout (locals : List LocalSlot) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) (mrTy : Gen.Type)
    (hPtr : layouts.pointerBits = 64) (hTr : translateTy layouts ty = some mrTy)
    (hDecl : DeclLayoutCoherent localDecls layouts ty) :
    ∃ sz al,
      Interp.Type.layout mrTy = .ok (.Sized ⟨sz⟩ ⟨al⟩) ∧
        evalRvalue locals (.nullaryOp .sizeOf ty) mem localDecls layouts =
          if x86_64.valid_size ⟨sz⟩ = true then .ok (.scalar ⟨sz, 8⟩) locals mem
          else .unsupported := by
  obtain ⟨sz, al, hS, _, hL⟩ := translateTy_layout_agrees localDecls layouts ty mrTy hTr hDecl
  refine ⟨sz, al, hL, ?_⟩
  show evalNullaryOp locals .sizeOf ty mem localDecls layouts = _
  rw [evalNullaryOp_sizeOf_eq, hS]
  dsimp only
  rw [maxObjSize_of_64 layouts hPtr, layoutPointerBytes_of_64 layouts hPtr]
  by_cases h : sz ≤ 9223372036854775807
  · simp [h, (valid_size_iff sz).mpr h]
  · have hv : ¬ x86_64.valid_size ⟨sz⟩ = true := fun hv => h ((valid_size_iff sz).mp hv)
    simp [h, hv]

/-- **A1 (`SizeOf`, `.ok` iff)**: Trusted returns the `usize` scalar `sz` exactly when MiniRust's
`Type::layout` of the translated type is `Sized(sz, _)` and `sz ≤ isize::MAX`. -/
theorem nullaryOp_sizeOf_ok_iff (locals : List LocalSlot) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) (mrTy : Gen.Type)
    (hPtr : layouts.pointerBits = 64) (hTr : translateTy layouts ty = some mrTy)
    (hDecl : DeclLayoutCoherent localDecls layouts ty) (sz : Nat) :
    evalRvalue locals (.nullaryOp .sizeOf ty) mem localDecls layouts =
        .ok (.scalar ⟨sz, 8⟩) locals mem ↔
      (∃ al, Interp.Type.layout mrTy = .ok (.Sized ⟨sz⟩ al)) ∧
        x86_64.valid_size ⟨sz⟩ = true := by
  obtain ⟨sz0, al0, hL, hE⟩ :=
    nullaryOp_sizeOf_minirust_layout locals ty mem localDecls layouts mrTy hPtr hTr hDecl
  rw [hE]
  constructor
  · intro h
    by_cases hv : x86_64.valid_size ⟨sz0⟩ = true
    · rw [ifPos hv] at h
      cases h
      exact ⟨⟨_, hL⟩, hv⟩
    · rw [ifNeg hv] at h
      cases h
  · rintro ⟨⟨al, hL'⟩, hv⟩
    rw [hL] at hL'
    cases hL'
    rw [ifPos hv]

/-- **A1 (`SizeOf`, `.unsupported` iff)**: Trusted fails closed exactly when the MiniRust size
exceeds `isize::MAX` (a type MiniRust's well-formedness check rejects). -/
theorem nullaryOp_sizeOf_unsupported_iff (locals : List LocalSlot) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) (mrTy : Gen.Type)
    (hPtr : layouts.pointerBits = 64) (hTr : translateTy layouts ty = some mrTy)
    (hDecl : DeclLayoutCoherent localDecls layouts ty) :
    evalRvalue locals (.nullaryOp .sizeOf ty) mem localDecls layouts = .unsupported ↔
      ∃ sz al, Interp.Type.layout mrTy = .ok (.Sized ⟨sz⟩ al) ∧
        x86_64.valid_size ⟨sz⟩ = false := by
  obtain ⟨sz0, al0, hL, hE⟩ :=
    nullaryOp_sizeOf_minirust_layout locals ty mem localDecls layouts mrTy hPtr hTr hDecl
  rw [hE]
  constructor
  · intro h
    by_cases hv : x86_64.valid_size ⟨sz0⟩ = true
    · rw [ifPos hv] at h
      cases h
    · exact ⟨sz0, _, hL, by simpa using hv⟩
  · rintro ⟨sz, al, hL', hv⟩
    rw [hL] at hL'
    cases hL'
    rw [ifNeg (by rw [hv]; decide)]

/-- **A2 (`AlignOf`, two-sided normal form)**. Under the hypotheses of A1: MiniRust's
`Type::layout` of the translated type is `Sized(sz, al)`, and Trusted's `Rvalue.nullaryOp
.alignOf` returns **exactly that alignment** `al` as an 8-byte `usize` scalar when the size is a
valid object size and `al` is a power of two below `2^64` (the invariant of MiniRust's `Align`),
and fails closed with `.unsupported` otherwise. -/
theorem nullaryOp_alignOf_minirust_layout (locals : List LocalSlot) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) (mrTy : Gen.Type)
    (hPtr : layouts.pointerBits = 64) (hTr : translateTy layouts ty = some mrTy)
    (hDecl : DeclLayoutCoherent localDecls layouts ty) :
    ∃ sz al,
      Interp.Type.layout mrTy = .ok (.Sized ⟨sz⟩ ⟨al⟩) ∧
        evalRvalue locals (.nullaryOp .alignOf ty) mem localDecls layouts =
          if x86_64.valid_size ⟨sz⟩ = true ∧ Layout.Align.isPowerOfTwoBytes ⟨al⟩ = true ∧
              al < 18446744073709551616 then
            .ok (.scalar ⟨al, 8⟩) locals mem
          else .unsupported := by
  obtain ⟨sz, al, hS, hA, hL⟩ := translateTy_layout_agrees localDecls layouts ty mrTy hTr hDecl
  refine ⟨sz, al, hL, ?_⟩
  show evalNullaryOp locals .alignOf ty mem localDecls layouts = _
  rw [evalNullaryOp_alignOf_eq, hS, hA]
  dsimp only
  rw [maxObjSize_of_64 layouts hPtr, layoutPointerBytes_of_64 layouts hPtr]
  have hMod : scalarModulus 8 = 18446744073709551616 := by decide
  rw [hMod]
  by_cases h : sz ≤ 9223372036854775807
  · simp [h, (valid_size_iff sz).mpr h]
  · have hv : ¬ x86_64.valid_size ⟨sz⟩ = true := fun hv => h ((valid_size_iff sz).mp hv)
    simp [h, hv]

/-- **A2 (`AlignOf`, `.ok` iff)**: Trusted returns the `usize` scalar `al` exactly when MiniRust's
`Type::layout` of the translated type is `Sized(sz, al)` with a valid size and `al` a power of two
below `2^64`. -/
theorem nullaryOp_alignOf_ok_iff (locals : List LocalSlot) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) (mrTy : Gen.Type)
    (hPtr : layouts.pointerBits = 64) (hTr : translateTy layouts ty = some mrTy)
    (hDecl : DeclLayoutCoherent localDecls layouts ty) (al : Nat) :
    evalRvalue locals (.nullaryOp .alignOf ty) mem localDecls layouts =
        .ok (.scalar ⟨al, 8⟩) locals mem ↔
      ∃ sz, Interp.Type.layout mrTy = .ok (.Sized ⟨sz⟩ ⟨al⟩) ∧
        x86_64.valid_size ⟨sz⟩ = true ∧ Layout.Align.isPowerOfTwoBytes ⟨al⟩ = true ∧
        al < 18446744073709551616 := by
  obtain ⟨sz0, al0, hL, hE⟩ :=
    nullaryOp_alignOf_minirust_layout locals ty mem localDecls layouts mrTy hPtr hTr hDecl
  rw [hE]
  constructor
  · intro h
    split at h
    · next hc =>
      cases h
      exact ⟨sz0, hL, hc⟩
    · cases h
  · rintro ⟨sz, hL', hc⟩
    rw [hL] at hL'
    cases hL'
    rw [ifPos hc]

/-- Declaration-layout coherence is vacuous outside the aggregate kinds: for every type whose
kind is neither a tuple nor an ADT (`bool`, the integers, arrays, raw pointers, references),
neither Trusted nor `minimize` reads the layout table, and A1/A2 hold unconditionally. -/
theorem declLayoutCoherent_of_nonAggregate (localDecls : List LocalDecl)
    (layouts : Layout.LayoutTable) (ty : Ty)
    (hT : ∀ ks, ty.kind ≠ .tuple ks) (hA : ∀ p args, ty.kind ≠ .adt p args) :
    DeclLayoutCoherent localDecls layouts ty := by
  intro size align h
  exfalso
  rcases ty with ⟨k, idx⟩
  cases k <;>
    first
    | exact absurd rfl (hT _)
    | exact absurd rfl (hA _ _)
    | simp [aggLayoutOf, isOrderingTy, intBoolTupleOf, tupleTypeOf, boxTypeOf] at h

/-! ### A3. `OffsetOf` ↔ MiniRust tuple field byte offsets -/

/-- The byte offset MiniRust's `PlaceExpr::Field` adds for field `i` of a tuple type: the offset
component of `sized_fields[i]` (`spec/lang/step/expressions.md`:
> "let (offset, field_ty) = match ty {
>      Type::Tuple { sized_fields, unsized_field, sized_head_layout } => {
>          if field >= 0 && field < sized_fields.len() {
>              sized_fields[field]
>          }"
), `none` when the type is not a tuple or has no sized field `i`. -/
def mrFieldOffset? (mrTy : Gen.Type) (i : Nat) : Option Nat :=
  match mrTy with
  | .Tuple sizedFields _ _ => sizedFields[i]?.map (fun f => f.1.bytes)
  | _ => none

/-- `mrFieldOffset?` is the offset that the interpreter's field lookup
(`listIndex sized_fields field`, the `(offset, field_ty)` of `evalPlace` at `PlaceExpr.Field`)
returns. -/
theorem mrFieldOffset_eq_some_iff (fs : List (Gen.Offset × Gen.Type)) (h : Gen.TupleHeadLayout)
    (u : Option Gen.Type) (i off : Nat) :
    mrFieldOffset? (.Tuple fs h u) i = some off ↔
      ∃ fty, listIndex fs (i : Int) "sized_fields[field]" = .ok (⟨off⟩, fty) := by
  have h0 : (0 : Int) ≤ (i : Int) := Int.natCast_nonneg i
  simp only [mrFieldOffset?, listIndex, h0, ↓reduceIte, Int.toNat_natCast]
  cases hf : fs[i]? with
  | none => simp [specPanic]
  | some f =>
    rcases f with ⟨⟨o⟩, fty⟩
    simp only [Option.map_some, Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨fty, rfl⟩
    · rintro ⟨fty', h'⟩
      cases h'
      rfl

/-- The nested field byte offset in MiniRust: the sum of the `sized_fields` offsets along a field
path (each `PlaceExpr::Field` hop adds its field's offset to the place pointer). -/
def mrPathOffset? : Gen.Type → List Nat → Option Nat
  | _, [] => some 0
  | .Tuple sizedFields _ _, i :: rest =>
    match sizedFields[i]? with
    | some (off, fieldTy) => (mrPathOffset? fieldTy rest).map (fun tail => off.bytes + tail)
    | none => none
  | _, _ :: _ => none

/-- A single-field path is the field offset. -/
theorem mrPathOffset_single (mrTy : Gen.Type) (i : Nat) :
    mrPathOffset? mrTy [i] = mrFieldOffset? mrTy i := by
  cases mrTy <;> simp [mrPathOffset?, mrFieldOffset?]
  case Tuple fs h u =>
    cases fs[i]? with
    | none => rfl
    | some f => rcases f with ⟨off, fty⟩; simp

private theorem fieldsToMiniRust_getElem? :
    ∀ (fields : List (Nat × TupleSpec)) (i : Nat),
      (TupleSpec.fieldsToMiniRust fields)[i]? =
        fields[i]?.map (fun f => ((⟨f.1⟩ : Gen.Offset), f.2.toMiniRustTy))
  | [], i => by simp [TupleSpec.fieldsToMiniRust]
  | (off, s) :: rest, 0 => by simp [TupleSpec.fieldsToMiniRust]
  | (off, s) :: rest, i + 1 => by
    simp only [TupleSpec.fieldsToMiniRust, List.getElem?_cons_succ]
    exact fieldsToMiniRust_getElem? rest i

private theorem tailD_getElem? {α : Type} (l : List α) (i : Nat) :
    (l.tailD [])[i]? = l[i + 1]? := by
  cases l <;> simp [List.tailD]

/-- The fields `specOfFieldList` extracts sit at the recorded `FieldsShape.arbitrary` offsets:
field `i` of the MiniRust tuple has offset `offsets[i]` and the spec of field kind `fks[i]` at the
field-layout index `fls[i]` (index `0` when the layout records none). -/
private theorem specOfFieldList_getElem? (layouts : Layout.LayoutTable) :
    ∀ (offsets : List Layout.Size) (fks : List RigidTy) (fls : List Nat)
      (fields : List (Nat × TupleSpec)),
      specOfFieldList layouts offsets fks fls = some fields →
      fields.length = offsets.length ∧
      ∀ (i : Nat) (o : Nat) (s : TupleSpec), fields[i]? = some (o, s) →
        ∃ off fk, offsets[i]? = some off ∧ o = off.bytes ∧ fks[i]? = some fk ∧
          specOfRigidTy layouts fk (fls[i]?.getD 0) = some s
  | [], [], fls, fields, h => by
    simp only [specOfFieldList] at h
    cases h
    exact ⟨rfl, fun i o s hi => by simp at hi⟩
  | [], _ :: _, fls, fields, h => by simp [specOfFieldList] at h
  | _ :: _, [], fls, fields, h => by simp [specOfFieldList] at h
  | off :: offs, fk :: fks, fls, fields, h => by
    simp only [specOfFieldList] at h
    cases hs : specOfRigidTy layouts fk (fls.head?.getD 0) with
    | none => rw [hs] at h; cases h
    | some fSpec =>
      rw [hs] at h
      cases hr : specOfFieldList layouts offs fks (fls.tailD []) with
      | none => rw [hr] at h; cases h
      | some restF =>
        rw [hr] at h
        cases h
        obtain ⟨hlen, hget⟩ := specOfFieldList_getElem? layouts offs fks (fls.tailD []) restF hr
        refine ⟨by simp [hlen], ?_⟩
        intro i o s hi
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
          obtain ⟨rfl, rfl⟩ := hi
          refine ⟨off, fk, rfl, rfl, rfl, ?_⟩
          cases fls <;> exact hs
        | succ j =>
          simp only [List.getElem?_cons_succ] at hi
          obtain ⟨off', fk', h1, h2, h3, h4⟩ := hget j o s hi
          refine ⟨off', fk', by simpa using h1, h2, by simpa using h3, ?_⟩
          rw [tailD_getElem?] at h4
          exact h4

/-- Inversion of `specOfRigidTy` at a tuple/struct spec: the `layoutIdx` entry is a single-variant
(`VariantsShape.single 0`) `FieldsShape.arbitrary` layout whose size and alignment are the spec's,
and whose field offsets `specOfFieldList` turned into the spec's fields. -/
private theorem specOfRigidTy_tuple_inv {layouts : Layout.LayoutTable} {k : RigidTy} {idx : Nat}
    {fields : List (Nat × TupleSpec)} {size align : Nat}
    (h : specOfRigidTy layouts k idx = some (.tuple fields size align)) :
    ∃ (l : Layout.TypeLayout) (offsets : List Layout.Size) (mi : List Nat) (fks : List RigidTy),
      Layout.LayoutTable.lookup layouts idx = some l ∧ l.variants = .single 0 ∧
        l.fields = .arbitrary offsets mi ∧ size = l.size.bytes ∧ align = l.align.bytes ∧
        (k = .tuple fks ∨ ∃ p, k = .adt p fks) ∧
        specOfFieldList layouts offsets fks l.fieldLayouts = some fields := by
  cases k with
  | tuple fks =>
    simp only [specOfRigidTy] at h
    cases hl : Layout.LayoutTable.lookup layouts idx with
    | none => rw [hl] at h; cases h
    | some l =>
      rw [hl] at h
      simp only [Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · split at h
        · cases hs : specOfFieldList layouts _ fks l.fieldLayouts with
          | none => rw [hs] at h; cases h
          | some fs =>
            rw [hs] at h
            cases h
            exact ⟨l, _, _, fks, rfl, by assumption, by assumption, rfl, rfl, Or.inl rfl, hs⟩
        · cases h
      · cases h
  | adt p fks =>
    simp only [specOfRigidTy] at h
    cases hl : Layout.LayoutTable.lookup layouts idx with
    | none => rw [hl] at h; cases h
    | some l =>
      rw [hl] at h
      simp only [Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · split at h
        · cases hs : specOfFieldList layouts _ fks l.fieldLayouts with
          | none => rw [hs] at h; cases h
          | some fs =>
            rw [hs] at h
            cases h
            exact ⟨l, _, _, fks, rfl, by assumption, by assumption, rfl, rfl, Or.inr ⟨p, rfl⟩, hs⟩
        · cases h
      · cases h
  | uint w => cases w <;> simp [specOfRigidTy, intTyBytes] at h
  | int w => cases w <;> simp [specOfRigidTy, intTyBytes] at h
  | _ => simp [specOfRigidTy] at h

/-- The kind `resolveOffsetOfPath` tracks for field `i` of variant `0`: the field kind of a tuple
(`RigidTy.tuple` records its field kinds; an ADT kind does not). -/
private def childKindOf (kindOpt : Option RigidTy) (i : Nat) : Option RigidTy :=
  match kindOpt with
  | some (.tuple ks) => ks[i]?
  | _ => none

private theorem resolveOffsetOfPath_cons_some (layouts : Layout.LayoutTable)
    (sF aF : RigidTy → Option Nat) (lo : RigidTy → Option Layout.TypeLayout)
    (kindOpt : Option RigidTy) (l : Layout.TypeLayout) (v i : Nat)
    (rest : List (VariantIdx × FieldIdx)) :
    resolveOffsetOfPath layouts sF aF lo kindOpt (some l) ((v, i) :: rest) =
      match layoutVariantFieldOffset? l v i with
      | none => none
      | some stepOff =>
        match resolveOffsetOfPath layouts sF aF lo
            (match kindOpt, Nat.beq v 0 with
              | some (.tuple ks), true => get? ks i
              | _, _ => none)
            (match l.variants, get? l.fieldLayouts i with
              | .single _, some flIdx => Layout.LayoutTable.lookup layouts flIdx
              | _, _ =>
                match (match kindOpt, Nat.beq v 0 with
                  | some (.tuple ks), true => get? ks i
                  | _, _ => none) with
                | some ck => lo ck
                | none => none) rest with
        | some tailOff => some (Nat.add stepOff tailOff)
        | none => none := by
  rcases kindOpt with _ | k
  · rfl
  · cases k <;> rfl

private theorem resolveOffsetOfPath_single0_step (layouts : Layout.LayoutTable)
    (sF aF : RigidTy → Option Nat) (lo : RigidTy → Option Layout.TypeLayout)
    (kindOpt : Option RigidTy) (l : Layout.TypeLayout) (offsets : List Layout.Size)
    (mi : List Nat) (hv : l.variants = .single 0) (hf : l.fields = .arbitrary offsets mi)
    (i : Nat) (rest : List (VariantIdx × FieldIdx)) :
    resolveOffsetOfPath layouts sF aF lo kindOpt (some l) ((0, i) :: rest) =
      match offsets[i]? with
      | none => none
      | some off =>
        match resolveOffsetOfPath layouts sF aF lo (childKindOf kindOpt i)
            (match l.fieldLayouts[i]? with
              | some flIdx => Layout.LayoutTable.lookup layouts flIdx
              | none => (childKindOf kindOpt i).bind lo) rest with
        | some tail => some (off.bytes + tail)
        | none => none := by
  have hstep : layoutVariantFieldOffset? l 0 i = offsets[i]?.map (fun o => o.bytes) := by
    unfold layoutVariantFieldOffset?
    rw [hv, hf]
    show (match offsets[i]? with
      | some off => some off.bytes
      | none => none) = _
    cases offsets[i]? <;> rfl
  have hunfold : resolveOffsetOfPath layouts sF aF lo kindOpt (some l) ((0, i) :: rest) =
      match layoutVariantFieldOffset? l 0 i with
      | none => none
      | some stepOff =>
        match resolveOffsetOfPath layouts sF aF lo (childKindOf kindOpt i)
            (match l.variants, l.fieldLayouts[i]? with
              | .single _, some flIdx => Layout.LayoutTable.lookup layouts flIdx
              | _, _ =>
                match childKindOf kindOpt i with
                | some ck => lo ck
                | none => none) rest with
        | some tailOff => some (Nat.add stepOff tailOff)
        | none => none := by
    rw [resolveOffsetOfPath_cons_some]
    rcases kindOpt with _ | k
    · rfl
    · cases k <;> rfl
  rw [hunfold, hstep, hv]
  cases offsets[i]? with
  | none => rfl
  | some off =>
    cases l.fieldLayouts[i]? with
    | none =>
      cases hck : childKindOf kindOpt i <;> rfl
    | some flIdx => rfl

private theorem resolveOffsetOfPath_nil (layouts : Layout.LayoutTable)
    (sF aF : RigidTy → Option Nat) (lo : RigidTy → Option Layout.TypeLayout)
    (kindOpt : Option RigidTy) (layoutOpt : Option Layout.TypeLayout) :
    resolveOffsetOfPath layouts sF aF lo kindOpt layoutOpt [] = some 0 := by
  rw [resolveOffsetOfPath]

private theorem resolveOffsetOfPath_step_none (layouts : Layout.LayoutTable)
    (sF aF : RigidTy → Option Nat) (lo : RigidTy → Option Layout.TypeLayout)
    (kindOpt : Option RigidTy) (l : Layout.TypeLayout) (v i : Nat)
    (rest : List (VariantIdx × FieldIdx))
    (h : layoutVariantFieldOffset? l v i = none) :
    resolveOffsetOfPath layouts sF aF lo kindOpt (some l) ((v, i) :: rest) = none := by
  rw [resolveOffsetOfPath_cons_some, h]

private theorem specOfFieldList_offsets {layouts : Layout.LayoutTable}
    {offsets : List Layout.Size} {fks : List RigidTy} {fls : List Nat}
    {fields : List (Nat × TupleSpec)}
    (h : specOfFieldList layouts offsets fks fls = some fields) (i : Nat) :
    fields[i]?.map (fun f => f.1) = offsets[i]?.map (fun o => o.bytes) := by
  obtain ⟨hlen, hget⟩ := specOfFieldList_getElem? layouts offsets fks fls fields h
  cases hf : fields[i]? with
  | none =>
    have h1 : fields.length ≤ i := List.getElem?_eq_none_iff.mp hf
    have h2 : offsets[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [h2]
    rfl
  | some f =>
    rcases f with ⟨o, s⟩
    obtain ⟨off, fk, h1, h2, _, _⟩ := hget i o s hf
    rw [h1, h2]
    rfl

private theorem tupleTypeOf_inv {layouts : Layout.LayoutTable} {ty : Ty}
    {fields : List (Nat × TupleSpec)} {size align : Nat}
    (h : tupleTypeOf layouts ty = some (fields, size, align)) :
    isOrderingTy ty = false ∧ intBoolTupleOf ty = none ∧
      specOfRigidTy layouts ty.kind ty.layoutIdx = some (.tuple fields size align) := by
  unfold tupleTypeOf at h
  split at h
  · cases h
  · next hc =>
    have hc' : isOrderingTy ty = false ∧ intBoolTupleOf ty = none := by
      simpa [Bool.or_eq_true] using hc
    refine ⟨hc'.1, hc'.2, ?_⟩
    rcases ty with ⟨k, idx⟩
    cases k <;> try (simp at h; done)
    all_goals
      dsimp only at h ⊢
      split at h
      · cases h
        assumption
      · cases h

/-- Trusted's `offset_of!` resolution of a single field `(0, i)` against a single-variant
`FieldsShape.arbitrary` layout is the recorded field offset `offsets[i]`; an out-of-range field
does not resolve. -/
theorem resolveOffsetOfPath_field (layouts : Layout.LayoutTable)
    (sF aF : RigidTy → Option Nat) (lo : RigidTy → Option Layout.TypeLayout)
    (kindOpt : Option RigidTy) (l : Layout.TypeLayout) (offsets : List Layout.Size)
    (mi : List Nat) (hv : l.variants = .single 0) (hf : l.fields = .arbitrary offsets mi)
    (i : Nat) :
    resolveOffsetOfPath layouts sF aF lo kindOpt (some l) [(0, i)] =
      offsets[i]?.map (fun o => o.bytes) := by
  rw [resolveOffsetOfPath_single0_step layouts sF aF lo kindOpt l offsets mi hv hf]
  cases offsets[i]? with
  | none => rfl
  | some off =>
    dsimp only
    rw [resolveOffsetOfPath_nil]
    rfl

/-- Trusted's `offset_of!` resolution against a single-variant layout (`VariantsShape.single 0`:
structs, tuples) rejects every path whose first hop names a variant other than `0`. -/
theorem resolveOffsetOfPath_variant_ne_zero (layouts : Layout.LayoutTable)
    (sF aF : RigidTy → Option Nat) (lo : RigidTy → Option Layout.TypeLayout)
    (kindOpt : Option RigidTy) (l : Layout.TypeLayout) (hv : l.variants = .single 0)
    (v i : Nat) (hne : v ≠ 0) (rest : List (VariantIdx × FieldIdx)) :
    resolveOffsetOfPath layouts sF aF lo kindOpt (some l) ((v, i) :: rest) = none := by
  apply resolveOffsetOfPath_step_none
  unfold layoutVariantFieldOffset?
  rw [hv]
  cases v with
  | zero => exact absurd rfl hne
  | succ n => rfl

/-- The MiniRust field offsets of a translated tuple/struct type are the recorded
`FieldsShape.arbitrary` offsets of its `layoutIdx` entry. -/
theorem mrFieldOffset_tupleSpec {layouts : Layout.LayoutTable} {offsets : List Layout.Size}
    {fks : List RigidTy} {fls : List Nat} {fields : List (Nat × TupleSpec)}
    (h : specOfFieldList layouts offsets fks fls = some fields) (size align i : Nat) :
    mrFieldOffset? (TupleSpec.tuple fields size align).toMiniRustTy i =
      offsets[i]?.map (fun o => o.bytes) := by
  simp only [TupleSpec.toMiniRustTy, mrFieldOffset?, fieldsToMiniRust_getElem?, Option.map_map]
  rw [← specOfFieldList_offsets h i]
  rfl

/-- **A3 (`OffsetOf`, single field, two-sided normal form)**. For a tuple or single-variant
struct type of the translated fragment (`tupleTypeOf layouts ty = some (fields, size, align)`)
whose declaration layout is coherent and is the `ty.layoutIdx` entry itself, on a 64-bit layout
table: Trusted's `Rvalue.nullaryOp (.offsetOf [(0, i)])` returns — as an 8-byte `usize` scalar,
frame and memory unchanged — **exactly the byte offset of field `i` of the translated MiniRust
tuple type** (`sized_fields[i].0`, what `PlaceExpr::Field` adds to the place pointer), provided
the type has a valid size and the offset lies within it; it is `.unsupported` (never a wrong
offset, never `.ub`) when the field does not exist in the MiniRust type or the bound fails. -/
theorem nullaryOp_offsetOf_field_minirust (locals : List LocalSlot) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (fields : List (Nat × TupleSpec)) (size align : Nat)
    (hPtr : layouts.pointerBits = 64)
    (hT : tupleTypeOf layouts ty = some (fields, size, align))
    (hDecl : DeclLayoutCoherent localDecls layouts ty)
    (hEntry : findDeclLayoutForRigidTy localDecls layouts ty.kind =
      Layout.LayoutTable.lookup layouts ty.layoutIdx)
    (i : Nat) :
    evalRvalue locals (.nullaryOp (.offsetOf [(0, i)]) ty) mem localDecls layouts =
      match mrFieldOffset? (TupleSpec.tuple fields size align).toMiniRustTy i with
      | some off =>
        if x86_64.valid_size ⟨size⟩ = true ∧ off ≤ size then
          .ok (.scalar ⟨off, 8⟩) locals mem
        else .unsupported
      | none => .unsupported := by
  obtain ⟨hO, hIB, hSpec⟩ := tupleTypeOf_inv hT
  obtain ⟨hSz, _, _⟩ := hDecl size align (by simp [aggLayoutOf, hO, hIB, hT])
  obtain ⟨l, offsets, mi, fks, hl, hv, hf, _, _, _, hFL⟩ := specOfRigidTy_tuple_inv hSpec
  show evalNullaryOp locals (.offsetOf [(0, i)]) ty mem localDecls layouts = _
  rw [evalNullaryOp_offsetOf_eq, hSz, hEntry, hl,
    resolveOffsetOfPath_field layouts _ _ _ _ l offsets mi hv hf i,
    mrFieldOffset_tupleSpec hFL size align i,
    maxObjSize_of_64 layouts hPtr, layoutPointerBytes_of_64 layouts hPtr]
  cases offsets[i]? with
  | none => rfl
  | some off =>
    dsimp only [Option.map_some]
    by_cases h : size ≤ 9223372036854775807
    · simp [h, (valid_size_iff size).mpr h]
    · have hvs : ¬ x86_64.valid_size ⟨size⟩ = true := fun hvs => h ((valid_size_iff size).mp hvs)
      simp [h, hvs]

/-- **A3 (`OffsetOf`, out-of-range field)**: a field index that does not exist in the translated
MiniRust tuple type (where `PlaceExpr::Field` is a spec panic, `"field projection to invalid
field"`) is `.unsupported` in Trusted — never UB and never a made-up offset. -/
theorem nullaryOp_offsetOf_field_out_of_range (locals : List LocalSlot) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (fields : List (Nat × TupleSpec)) (size align : Nat)
    (hPtr : layouts.pointerBits = 64)
    (hT : tupleTypeOf layouts ty = some (fields, size, align))
    (hDecl : DeclLayoutCoherent localDecls layouts ty)
    (hEntry : findDeclLayoutForRigidTy localDecls layouts ty.kind =
      Layout.LayoutTable.lookup layouts ty.layoutIdx)
    (i : Nat) (hi : fields.length ≤ i) :
    mrFieldOffset? (TupleSpec.tuple fields size align).toMiniRustTy i = none ∧
      evalRvalue locals (.nullaryOp (.offsetOf [(0, i)]) ty) mem localDecls layouts =
        .unsupported := by
  have hNone : mrFieldOffset? (TupleSpec.tuple fields size align).toMiniRustTy i = none := by
    simp only [TupleSpec.toMiniRustTy, mrFieldOffset?, fieldsToMiniRust_getElem?,
      List.getElem?_eq_none_iff.mpr hi, Option.map_none]
  refine ⟨hNone, ?_⟩
  rw [nullaryOp_offsetOf_field_minirust locals ty mem localDecls layouts fields size align hPtr hT
    hDecl hEntry i, hNone]

/-- **A3 (MiniRust `evalPlaceM`, out-of-range field)**: whenever `mrFieldOffset?` returns `none`
on a sized MiniRust tuple type (no unsized tail), projecting that field in `evalPlaceM` is a
specification panic (`"field projection to non-existing unsized tail"` at `i = fs.length`, or
`"field projection to invalid field"` for `i > fs.length`), on every `Machine M` (in particular
`Mach` and `MachTB`). -/
theorem evalPlaceM_field_out_of_range_specPanic {M : Type} [Gen.Memory M] [MemoryOps M]
    (m m' : Gen.Machine M) (rootExpr : Gen.PlaceExpr) (pl : Gen.Place M)
    (fs : List (Gen.Offset × Gen.Type)) (h : Gen.TupleHeadLayout) (i : Nat)
    (hRoot : evalPlaceM (M := M) m rootExpr = .ok ((pl, .Tuple fs h none), m'))
    (hNone : mrFieldOffset? (.Tuple fs h none) i = none) :
    ∃ msg, evalPlaceM (M := M) m (.Field rootExpr (i : Int)) = .error (.specPanic msg) := by
  have hge : fs.length ≤ i := by
    simp only [mrFieldOffset?, Option.map_eq_none_iff] at hNone
    exact List.getElem?_eq_none_iff.mp hNone
  have hnotlt : ¬ ((0 : Int) ≤ (i : Int) ∧ (i : Int) < (fs.length : Int)) := by omega
  unfold evalPlaceM
  rw [hRoot]
  dsimp only [bind, Except.bind]
  rw [ifNeg hnotlt]
  by_cases heq : (i : Int) = (fs.length : Int)
  · rw [ifPos heq]; exact ⟨_, rfl⟩
  · rw [ifNeg heq]; exact ⟨_, rfl⟩

/-- **A3 (MiniRust `evalPlace` on `Mach`, out-of-range field)**: same specification panic for
the concrete `BasicMemory` interpreter. -/
theorem evalPlace_field_out_of_range_specPanic (m m' : Mach) (rootExpr : Gen.PlaceExpr)
    (pl : Gen.Place BM) (fs : List (Gen.Offset × Gen.Type)) (h : Gen.TupleHeadLayout) (i : Nat)
    (hRoot : evalPlace m rootExpr = .ok ((pl, .Tuple fs h none), m'))
    (hNone : mrFieldOffset? (.Tuple fs h none) i = none) :
    ∃ msg, evalPlace m (.Field rootExpr (i : Int)) = .error (.specPanic msg) := by
  have hge : fs.length ≤ i := by
    simp only [mrFieldOffset?, Option.map_eq_none_iff] at hNone
    exact List.getElem?_eq_none_iff.mp hNone
  have hnotlt : ¬ ((0 : Int) ≤ (i : Int) ∧ (i : Int) < (fs.length : Int)) := by omega
  unfold evalPlace
  rw [hRoot]
  dsimp only [bind, Except.bind]
  rw [ifNeg hnotlt]
  by_cases heq : (i : Int) = (fs.length : Int)
  · rw [ifPos heq]; exact ⟨_, rfl⟩
  · rw [ifNeg heq]; exact ⟨_, rfl⟩

/-- **A3 (`OffsetOf` out-of-range ↔ MiniRust `evalPlaceM` specPanic)**: for a translated tuple or
struct type, an out-of-range field index `i ≥ fields.length` yields `.unsupported` in Trusted and
a specification panic in MiniRust's `evalPlaceM` (on every `Machine M`). -/
theorem nullaryOp_offsetOf_out_of_range_matches_evalPlaceM
    {M : Type} [Gen.Memory M] [MemoryOps M]
    (locals : List LocalSlot) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (fields : List (Nat × TupleSpec)) (size align : Nat)
    (hPtr : layouts.pointerBits = 64)
    (hT : tupleTypeOf layouts ty = some (fields, size, align))
    (hDecl : DeclLayoutCoherent localDecls layouts ty)
    (hEntry : findDeclLayoutForRigidTy localDecls layouts ty.kind =
      Layout.LayoutTable.lookup layouts ty.layoutIdx)
    (i : Nat) (hi : fields.length ≤ i)
    (m m' : Gen.Machine M) (rootExpr : Gen.PlaceExpr) (pl : Gen.Place M)
    (hRoot : evalPlaceM (M := M) m rootExpr =
      .ok ((pl, (TupleSpec.tuple fields size align).toMiniRustTy), m')) :
    evalRvalue locals (.nullaryOp (.offsetOf [(0, i)]) ty) mem localDecls layouts = .unsupported ∧
      ∃ msg, evalPlaceM (M := M) m (.Field rootExpr (i : Int)) = .error (.specPanic msg) := by
  obtain ⟨hNone, hUnsup⟩ :=
    nullaryOp_offsetOf_field_out_of_range locals ty mem localDecls layouts fields size align
      hPtr hT hDecl hEntry i hi
  exact ⟨hUnsup,
    evalPlaceM_field_out_of_range_specPanic m m' rootExpr pl _ _ i hRoot hNone⟩

/-- **A3 (`OffsetOf`, enum-variant paths)**: the tuple and struct types of the translated fragment
have a single variant, so every path whose first hop names a variant other than `0` is
`.unsupported` in Trusted. (Trusted's evaluator does resolve variant fields of multi-variant enum
layouts, `VariantsShape.multiple`, but `translateTy` translates no enum with fields: the only
translated enum, `core::cmp::Ordering`, has field-less variants, so MiniRust has no such field
offset to compare against.) -/
theorem nullaryOp_offsetOf_variant_ne_zero_unsupported (locals : List LocalSlot) (ty : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (fields : List (Nat × TupleSpec)) (size align : Nat)
    (hT : tupleTypeOf layouts ty = some (fields, size, align))
    (hEntry : findDeclLayoutForRigidTy localDecls layouts ty.kind =
      Layout.LayoutTable.lookup layouts ty.layoutIdx)
    (v i : Nat) (hne : v ≠ 0) (rest : List (VariantIdx × FieldIdx)) :
    evalRvalue locals (.nullaryOp (.offsetOf ((v, i) :: rest)) ty) mem localDecls layouts =
      .unsupported := by
  obtain ⟨_, _, hSpec⟩ := tupleTypeOf_inv hT
  obtain ⟨l, offsets, mi, fks, hl, hv, _, _, _, _, _⟩ := specOfRigidTy_tuple_inv hSpec
  show evalNullaryOp locals (.offsetOf ((v, i) :: rest)) ty mem localDecls layouts = _
  rw [evalNullaryOp_offsetOf_eq, hEntry, hl,
    resolveOffsetOfPath_variant_ne_zero layouts _ _ _ _ l hv v i hne rest]
  cases intrinsicRigidTyByteSize localDecls layouts ty.kind <;> rfl

/-- Every aggregate (`FieldsShape.arbitrary`) entry of the layout table records one field-layout
index per field, as `rustc-capture` emits them. Under this table invariant `specOfFieldList` (which
defaults a missing field-layout index to `0`) and Trusted's `resolveOffsetOfPath` (which falls back
to the declaration layout of the field kind) read the same child layout at every hop. -/
def FieldLayoutsRecorded (layouts : Layout.LayoutTable) : Prop :=
  ∀ l ∈ layouts.entries, ∀ offsets mi, l.fields = .arbitrary offsets mi →
    l.fieldLayouts.length = offsets.length

/-- **A3 (nested paths, symbolic)**: along any field path that exists in the translated MiniRust
type, Trusted's `resolveOffsetOfPath` (started at the type's `layoutIdx` entry) resolves the path
to the **sum of the nested MiniRust field offsets** (`mrPathOffset?`). -/
theorem resolveOffsetOfPath_spec_path (layouts : Layout.LayoutTable)
    (sF aF : RigidTy → Option Nat) (lo : RigidTy → Option Layout.TypeLayout)
    (hRec : FieldLayoutsRecorded layouts) :
    ∀ (path : List Nat) (k : RigidTy) (kindOpt : Option RigidTy) (idx : Nat) (spec : TupleSpec)
      (off : Nat),
      specOfRigidTy layouts k idx = some spec →
      mrPathOffset? spec.toMiniRustTy path = some off →
      resolveOffsetOfPath layouts sF aF lo kindOpt (Layout.LayoutTable.lookup layouts idx)
          (path.map (fun i => ((0 : VariantIdx), (i : FieldIdx)))) = some off := by
  intro path
  induction path with
  | nil =>
    intro k kindOpt idx spec off _ hP
    rw [mrPathOffset?] at hP
    cases hP
    exact resolveOffsetOfPath_nil layouts sF aF lo kindOpt _
  | cons i rest ih =>
    intro k kindOpt idx spec off hSpec hP
    cases spec with
    | scalar it => simp [TupleSpec.toMiniRustTy, mrPathOffset?] at hP
    | tuple fields size align =>
      obtain ⟨l, offsets, mi, fks, hl, hv, hf, _, _, _, hFL⟩ := specOfRigidTy_tuple_inv hSpec
      simp only [TupleSpec.toMiniRustTy, mrPathOffset?, fieldsToMiniRust_getElem?] at hP
      cases hfi : fields[i]? with
      | none => rw [hfi] at hP; cases hP
      | some f =>
        rcases f with ⟨o, s⟩
        rw [hfi] at hP
        simp only [Option.map_some] at hP
        cases hTail : mrPathOffset? s.toMiniRustTy rest with
        | none => rw [hTail] at hP; cases hP
        | some tail =>
          rw [hTail] at hP
          cases hP
          obtain ⟨hlen, hget⟩ := specOfFieldList_getElem? layouts offsets fks l.fieldLayouts fields hFL
          obtain ⟨off', fk, hoff, ho, _, hs⟩ := hget i o s hfi
          have hmem : l ∈ layouts.entries := List.mem_of_getElem? hl
          have hflLen := hRec l hmem offsets mi hf
          have hi : i < offsets.length := by
            rcases Nat.lt_or_ge i offsets.length with h | h
            · exact h
            · rw [List.getElem?_eq_none_iff.mpr h] at hoff
              cases hoff
          have hfl : l.fieldLayouts[i]? = some l.fieldLayouts[i] :=
            List.getElem?_eq_getElem (by omega)
          rw [hfl] at hs
          simp only [Option.getD_some] at hs
          rw [List.map_cons, hl,
            resolveOffsetOfPath_single0_step layouts sF aF lo kindOpt l offsets mi hv hf, hoff]
          dsimp only
          rw [hfl]
          dsimp only
          rw [ih fk (childKindOf kindOpt i) _ s tail hs hTail, ho]

/-- **A3 (`OffsetOf`, nested paths)**. Under the hypotheses of the single-field theorem and the
`FieldLayoutsRecorded` table invariant: for every nested field path that exists in the translated
MiniRust type, Trusted's `Rvalue.nullaryOp (.offsetOf ..)` returns the **sum of the nested
MiniRust field offsets** (within the size bound), and `.unsupported` when the bound fails. -/
theorem nullaryOp_offsetOf_path_minirust (locals : List LocalSlot) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (fields : List (Nat × TupleSpec)) (size align : Nat)
    (hPtr : layouts.pointerBits = 64) (hRec : FieldLayoutsRecorded layouts)
    (hT : tupleTypeOf layouts ty = some (fields, size, align))
    (hDecl : DeclLayoutCoherent localDecls layouts ty)
    (hEntry : findDeclLayoutForRigidTy localDecls layouts ty.kind =
      Layout.LayoutTable.lookup layouts ty.layoutIdx)
    (path : List Nat) (off : Nat)
    (hPath : mrPathOffset? (TupleSpec.tuple fields size align).toMiniRustTy path = some off) :
    evalRvalue locals
        (.nullaryOp (.offsetOf (path.map (fun i => ((0 : VariantIdx), (i : FieldIdx))))) ty) mem
        localDecls layouts =
      if x86_64.valid_size ⟨size⟩ = true ∧ off ≤ size then .ok (.scalar ⟨off, 8⟩) locals mem
      else .unsupported := by
  obtain ⟨hO, hIB, hSpec⟩ := tupleTypeOf_inv hT
  obtain ⟨hSz, _, _⟩ := hDecl size align (by simp [aggLayoutOf, hO, hIB, hT])
  show evalNullaryOp locals (.offsetOf (path.map (fun i => ((0 : VariantIdx), (i : FieldIdx)))))
    ty mem localDecls layouts = _
  rw [evalNullaryOp_offsetOf_eq, hSz, hEntry,
    resolveOffsetOfPath_spec_path layouts _ _ _ hRec path ty.kind (some ty.kind) ty.layoutIdx _
      off hSpec hPath,
    maxObjSize_of_64 layouts hPtr, layoutPointerBytes_of_64 layouts hPtr]
  dsimp only
  by_cases h : size ≤ 9223372036854775807
  · simp [h, (valid_size_iff size).mpr h]
  · have hvs : ¬ x86_64.valid_size ⟨size⟩ = true := fun hvs => h ((valid_size_iff size).mp hvs)
    simp [h, hvs]

/-- Every scalar leaf reachable in `(idx, spec)` under `layouts` records
`VariantsShape.single 0` and `FieldsShape.primitive` when `LayoutTable.lookup layouts idx`
succeeds, as `rustc-capture` emits for primitive integer types. Together with
`FieldLayoutsRecorded`, this makes nested-path `offset_of!` resolution exact in both directions
(both `some off` and `none`). -/
inductive ScalarLeavesPrimitive (layouts : Layout.LayoutTable) : Nat → TupleSpec → Prop
  | scalar (idx : Nat) (it : Gen.IntType) :
      (∀ l, Layout.LayoutTable.lookup layouts idx = some l →
        l.variants = .single 0 ∧ l.fields = .primitive) →
      ScalarLeavesPrimitive layouts idx (.scalar it)
  | tuple (idx : Nat) (fields : List (Nat × TupleSpec)) (size align : Nat) :
      (∀ l, Layout.LayoutTable.lookup layouts idx = some l →
        ∀ (i : Nat) (o : Nat) (s : TupleSpec), fields[i]? = some (o, s) →
          ScalarLeavesPrimitive layouts (l.fieldLayouts[i]?.getD 0) s) →
      ScalarLeavesPrimitive layouts idx (.tuple fields size align)

private theorem specOfRigidTy_scalar_not_tuple {layouts : Layout.LayoutTable} {k : RigidTy}
    {idx : Nat} {it : Gen.IntType} (h : specOfRigidTy layouts k idx = some (.scalar it)) :
    ∀ ks, k ≠ .tuple ks := by
  intro ks hEq
  subst hEq
  simp only [specOfRigidTy] at h
  cases hl : Layout.LayoutTable.lookup layouts idx with
  | none => rw [hl] at h; cases h
  | some l =>
    rw [hl] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · split at h
      · cases hs : specOfFieldList layouts _ ks l.fieldLayouts with
        | none => rw [hs] at h; cases h
        | some fs => rw [hs] at h; cases h
      · cases h
    · cases h

/-- **A3 (nested paths, two-sided `resolveOffsetOfPath` equality)**: under `FieldLayoutsRecorded`
and `ScalarLeavesPrimitive`, Trusted's `resolveOffsetOfPath` matches MiniRust's `mrPathOffset?`
for **every** field path `path : List Nat` — agreeing on both `some off` and `none` (out-of-range
field index or descending into a scalar leaf). -/
theorem resolveOffsetOfPath_spec_path_eq (layouts : Layout.LayoutTable)
    (sF aF : RigidTy → Option Nat) (lo : RigidTy → Option Layout.TypeLayout)
    (hRec : FieldLayoutsRecorded layouts) :
    ∀ (path : List Nat) (k : RigidTy) (kindOpt : Option RigidTy) (idx : Nat) (spec : TupleSpec),
      (kindOpt = none ∨ kindOpt = some k) →
      specOfRigidTy layouts k idx = some spec →
      ScalarLeavesPrimitive layouts idx spec →
      resolveOffsetOfPath layouts sF aF lo kindOpt (Layout.LayoutTable.lookup layouts idx)
          (path.map (fun i => ((0 : VariantIdx), (i : FieldIdx)))) =
        mrPathOffset? spec.toMiniRustTy path := by
  intro path
  induction path with
  | nil =>
    intro k kindOpt idx spec _ _ _
    rw [List.map_nil, resolveOffsetOfPath_nil, mrPathOffset?]
  | cons i rest ih =>
    intro k kindOpt idx spec hKind hSpec hPrim
    cases spec with
    | scalar it =>
      simp only [TupleSpec.toMiniRustTy, mrPathOffset?, List.map_cons]
      cases hl : Layout.LayoutTable.lookup layouts idx with
      | none =>
        rcases hKind with rfl | rfl
        · rfl
        · have hnt := specOfRigidTy_scalar_not_tuple hSpec
          cases k with
          | tuple ks => exact absurd rfl (hnt ks)
          | _ => rfl
      | some l =>
        cases hPrim with
        | scalar _ _ hP =>
          obtain ⟨hv, hfp⟩ := hP l hl
          apply resolveOffsetOfPath_step_none
          unfold layoutVariantFieldOffset?
          rw [hv, hfp]
    | tuple fields size align =>
      obtain ⟨l, offsets, mi, fks, hl, hv, hf, _, _, hk, hFL⟩ := specOfRigidTy_tuple_inv hSpec
      obtain ⟨hlen, hget⟩ := specOfFieldList_getElem? layouts offsets fks l.fieldLayouts fields hFL
      rw [List.map_cons, hl,
        resolveOffsetOfPath_single0_step layouts sF aF lo kindOpt l offsets mi hv hf]
      simp only [TupleSpec.toMiniRustTy, mrPathOffset?, fieldsToMiniRust_getElem?]
      cases hfi : fields[i]? with
      | none =>
        have hge : fields.length ≤ i := List.getElem?_eq_none_iff.mp hfi
        have hoffNone : offsets[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
        rw [hoffNone]
        rfl
      | some f =>
        rcases f with ⟨o, s⟩
        obtain ⟨off', fk, hoff, ho, hfk, hs⟩ := hget i o s hfi
        have hmem : l ∈ layouts.entries := List.mem_of_getElem? hl
        have hflLen := hRec l hmem offsets mi hf
        have hi : i < offsets.length := by
          rcases Nat.lt_or_ge i offsets.length with h | h
          · exact h
          · rw [List.getElem?_eq_none_iff.mpr h] at hoff; cases hoff
        have hfl : l.fieldLayouts[i]? = some l.fieldLayouts[i] :=
          List.getElem?_eq_getElem (by omega)
        have hPrimChild : ScalarLeavesPrimitive layouts l.fieldLayouts[i] s := by
          cases hPrim with
          | tuple _ _ _ _ hP =>
            have hPc := hP l hl i o s hfi
            rw [hfl, Option.getD_some] at hPc
            exact hPc
        rw [hfl] at hs
        simp only [Option.getD_some] at hs
        have hck : childKindOf kindOpt i = none ∨ childKindOf kindOpt i = some fk := by
          rcases hKind with rfl | rfl
          · exact Or.inl rfl
          · rcases hk with rfl | ⟨p, rfl⟩
            · exact Or.inr hfk
            · exact Or.inl rfl
        rw [hoff]
        dsimp only
        rw [hfl]
        dsimp only
        rw [ih fk (childKindOf kindOpt i) l.fieldLayouts[i] s hck hs hPrimChild, ho]
        cases hmr : mrPathOffset? s.toMiniRustTy rest <;> simp [hmr]

/-- **A3 (`OffsetOf`, nested paths, two-sided)**: under `FieldLayoutsRecorded` and
`ScalarLeavesPrimitive`, Trusted's `Rvalue.nullaryOp (.offsetOf ..)` agrees with MiniRust's
`mrPathOffset?` for **every** path `path : List Nat`: returning `.ok (.scalar ⟨off, 8⟩)` iff
`mrPathOffset? = some off`, `x86_64.valid_size ⟨size⟩ = true`, and `off ≤ size`, and
`.unsupported` otherwise (including every invalid/out-of-range/over-deep path). -/
theorem nullaryOp_offsetOf_path_minirust_two_sided (locals : List LocalSlot) (ty : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (fields : List (Nat × TupleSpec)) (size align : Nat)
    (hPtr : layouts.pointerBits = 64)
    (hRec : FieldLayoutsRecorded layouts)
    (hPrim : ScalarLeavesPrimitive layouts ty.layoutIdx (.tuple fields size align))
    (hT : tupleTypeOf layouts ty = some (fields, size, align))
    (hDecl : DeclLayoutCoherent localDecls layouts ty)
    (hEntry : findDeclLayoutForRigidTy localDecls layouts ty.kind =
      Layout.LayoutTable.lookup layouts ty.layoutIdx)
    (path : List Nat) :
    evalRvalue locals
        (.nullaryOp (.offsetOf (path.map (fun i => ((0 : VariantIdx), (i : FieldIdx))))) ty) mem
        localDecls layouts =
      match mrPathOffset? (TupleSpec.tuple fields size align).toMiniRustTy path with
      | some off =>
        if x86_64.valid_size ⟨size⟩ = true ∧ off ≤ size then .ok (.scalar ⟨off, 8⟩) locals mem
        else .unsupported
      | none => .unsupported := by
  obtain ⟨hO, hIB, hSpec⟩ := tupleTypeOf_inv hT
  obtain ⟨hSz, _, _⟩ := hDecl size align (by simp [aggLayoutOf, hO, hIB, hT])
  show evalNullaryOp locals (.offsetOf (path.map (fun i => ((0 : VariantIdx), (i : FieldIdx)))))
    ty mem localDecls layouts = _
  rw [evalNullaryOp_offsetOf_eq, hSz, hEntry,
    resolveOffsetOfPath_spec_path_eq layouts _ _ _ hRec path ty.kind (some ty.kind)
      ty.layoutIdx _ (Or.inr rfl) hSpec hPrim,
    maxObjSize_of_64 layouts hPtr, layoutPointerBytes_of_64 layouts hPtr]
  cases mrPathOffset? (TupleSpec.tuple fields size align).toMiniRustTy path with
  | none => rfl
  | some off =>
    dsimp only
    by_cases h : size ≤ 9223372036854775807
    · simp [h, (valid_size_iff size).mpr h]
    · have hvs : ¬ x86_64.valid_size ⟨size⟩ = true := fun hvs => h ((valid_size_iff size).mp hvs)
      simp [h, hvs]

/-! ### A1-A3. Declaration-layout coherence from raw layout-table facts -/

private theorem byteSize_tuple_cons_of_findDecl (ld : List LocalDecl) (lt : Layout.LayoutTable)
    (k : RigidTy) (ks : List RigidTy) (l : Layout.TypeLayout)
    (h : findDeclLayoutForRigidTy ld lt (.tuple (k :: ks)) = some l) :
    intrinsicRigidTyByteSize ld lt (.tuple (k :: ks)) = some l.size.bytes := by
  have e : intrinsicRigidTyByteSize ld lt (.tuple (k :: ks)) =
      (match findDeclLayoutForRigidTy ld lt (.tuple (k :: ks)) with
        | some l => some l.size.bytes
        | none =>
          match tupleFieldsByteSum (intrinsicRigidTyByteSizeAux 7 ld lt) (k :: ks),
            intrinsicRigidTyAlignAux 8 ld lt (.tuple (k :: ks)) with
          | some rawBytes, some alignBytes => some (roundUpToAlign rawBytes alignBytes)
          | _, _ => none) := rfl
  rw [e, h]

private theorem align_tuple_cons_of_findDecl (ld : List LocalDecl) (lt : Layout.LayoutTable)
    (k : RigidTy) (ks : List RigidTy) (l : Layout.TypeLayout)
    (h : findDeclLayoutForRigidTy ld lt (.tuple (k :: ks)) = some l)
    (hp : Layout.Align.isPowerOfTwoBytes l.align = true) :
    intrinsicRigidTyAlign ld lt (.tuple (k :: ks)) = some l.align.bytes := by
  have e : intrinsicRigidTyAlign ld lt (.tuple (k :: ks)) =
      (match findDeclLayoutForRigidTy ld lt (.tuple (k :: ks)) with
        | some l =>
          (match Layout.Align.isPowerOfTwoBytes l.align with
            | true => some l.align.bytes
            | false => none)
        | none => tupleFieldsAlign (intrinsicRigidTyAlignAux 7 ld lt) (k :: ks)) := rfl
  rw [e, h]
  dsimp only
  rw [hp]

private theorem byteSize_adt_of_findDecl (ld : List LocalDecl) (lt : Layout.LayoutTable)
    (p : DefPath) (args : List RigidTy) (l : Layout.TypeLayout)
    (h : findDeclLayoutForRigidTy ld lt (.adt p args) = some l) :
    intrinsicRigidTyByteSize ld lt (.adt p args) = some l.size.bytes := by
  have e : intrinsicRigidTyByteSize ld lt (.adt p args) =
      (match findDeclLayoutForRigidTy ld lt (.adt p args) with
        | some l => some l.size.bytes
        | none => none) := rfl
  rw [e, h]

private theorem align_adt_of_findDecl (ld : List LocalDecl) (lt : Layout.LayoutTable)
    (p : DefPath) (args : List RigidTy) (l : Layout.TypeLayout)
    (h : findDeclLayoutForRigidTy ld lt (.adt p args) = some l)
    (hp : Layout.Align.isPowerOfTwoBytes l.align = true) :
    intrinsicRigidTyAlign ld lt (.adt p args) = some l.align.bytes := by
  have e : intrinsicRigidTyAlign ld lt (.adt p args) =
      (match findDeclLayoutForRigidTy ld lt (.adt p args) with
        | some l =>
          (match Layout.Align.isPowerOfTwoBytes l.align with
            | true => some l.align.bytes
            | false => none)
        | none => none) := rfl
  rw [e, h]
  dsimp only
  rw [hp]

/-- **Coherence from the layout table (tuples and structs).** If the declaration scan for the
kind of `ty` resolves to the very entry `ty.layoutIdx` names (a local of this type exists and
`rustc`'s `layout_of` is a function of the type), and that entry is well formed
(`TypeLayout.isWellFormed`: power-of-two alignment, size a multiple of the alignment), then a
non-unit tuple or struct type of the translated fragment has a coherent declaration layout. -/
theorem declLayoutCoherent_of_same_entry (localDecls : List LocalDecl)
    (layouts : Layout.LayoutTable) (ty : Ty) (fields : List (Nat × TupleSpec)) (size align : Nat)
    (hT : tupleTypeOf layouts ty = some (fields, size, align))
    (hNonUnit : ty.kind ≠ .tuple [])
    (hEntry : findDeclLayoutForRigidTy localDecls layouts ty.kind =
      Layout.LayoutTable.lookup layouts ty.layoutIdx)
    (hWf : ∀ l, Layout.LayoutTable.lookup layouts ty.layoutIdx = some l →
      Layout.TypeLayout.isWellFormed l = true) :
    DeclLayoutCoherent localDecls layouts ty := by
  obtain ⟨hO, hIB, hSpec⟩ := tupleTypeOf_inv hT
  obtain ⟨l, offsets, mi, fks, hl, _, _, hsz, hal, hk, _⟩ := specOfRigidTy_tuple_inv hSpec
  have hwf := hWf l hl
  unfold Layout.TypeLayout.isWellFormed Layout.Size.isMultipleOfAlign at hwf
  rw [Bool.and_eq_true, Bool.and_eq_true] at hwf
  obtain ⟨hp, _, hm⟩ := hwf
  have hmod : l.size.bytes % l.align.bytes = 0 := Nat.eq_of_beq_eq_true hm
  have hF : findDeclLayoutForRigidTy localDecls layouts ty.kind = some l := hEntry.trans hl
  intro size' align' hAgg
  have hAgg' : aggLayoutOf layouts ty = some (size, align) := by simp [aggLayoutOf, hO, hIB, hT]
  rw [hAgg'] at hAgg
  cases hAgg
  subst hsz hal
  refine ⟨?_, ?_, hmod⟩
  · rcases hk with hk | ⟨p, hk⟩
    · rw [hk] at hF hNonUnit ⊢
      cases fks with
      | nil => exact absurd rfl hNonUnit
      | cons k ks => exact byteSize_tuple_cons_of_findDecl _ _ _ _ _ hF
    · rw [hk] at hF ⊢
      exact byteSize_adt_of_findDecl _ _ _ _ _ hF
  · rcases hk with hk | ⟨p, hk⟩
    · rw [hk] at hF hNonUnit ⊢
      cases fks with
      | nil => exact absurd rfl hNonUnit
      | cons k ks => exact align_tuple_cons_of_findDecl _ _ _ _ _ hF hp
    · rw [hk] at hF ⊢
      exact align_adt_of_findDecl _ _ _ _ _ hF hp

/-- **Coherence by evaluation.** On a concrete table, declaration-layout coherence reduces to
evaluating the three layout queries. -/
theorem declLayoutCoherent_of_eval {localDecls : List LocalDecl} {layouts : Layout.LayoutTable}
    {ty : Ty} (size align : Nat) (hAgg : aggLayoutOf layouts ty = some (size, align))
    (h1 : intrinsicRigidTyByteSize localDecls layouts ty.kind = some size)
    (h2 : intrinsicRigidTyAlign localDecls layouts ty.kind = some align)
    (h3 : size % align = 0) : DeclLayoutCoherent localDecls layouts ty := by
  intro s a h
  rw [hAgg] at h
  cases h
  exact ⟨h1, h2, h3⟩

/-- `evalRvalue` dispatches `Rvalue.nullaryOp` to `evalNullaryOp`. -/
theorem evalRvalue_nullaryOp_eq (locals : List LocalSlot) (op : NullOp) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) :
    evalRvalue locals (.nullaryOp op ty) mem localDecls layouts =
      evalNullaryOp locals op ty mem localDecls layouts := rfl

/-- **A1/A2 (from MiniRust to Trusted)**: whenever MiniRust's layout of the translated type is
`Sized(sz, al)` with a valid size and a power-of-two alignment below `2^64`, Trusted's `SizeOf`
and `AlignOf` return exactly `sz` and `al`. -/
theorem nullaryOp_sizeOf_alignOf_of_minirust_layout (locals : List LocalSlot) (ty : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : Layout.LayoutTable)
    (mrTy : Gen.Type) (hPtr : layouts.pointerBits = 64)
    (hTr : translateTy layouts ty = some mrTy)
    (hDecl : DeclLayoutCoherent localDecls layouts ty) (sz al : Nat)
    (hL : Interp.Type.layout mrTy = .ok (.Sized ⟨sz⟩ ⟨al⟩))
    (hV : x86_64.valid_size ⟨sz⟩ = true)
    (hP : Layout.Align.isPowerOfTwoBytes ⟨al⟩ = true) (hLt : al < 18446744073709551616) :
    evalRvalue locals (.nullaryOp .sizeOf ty) mem localDecls layouts =
        .ok (.scalar ⟨sz, 8⟩) locals mem ∧
      evalRvalue locals (.nullaryOp .alignOf ty) mem localDecls layouts =
        .ok (.scalar ⟨al, 8⟩) locals mem :=
  ⟨(nullaryOp_sizeOf_ok_iff locals ty mem localDecls layouts mrTy hPtr hTr hDecl sz).mpr
      ⟨⟨_, hL⟩, hV⟩,
    (nullaryOp_alignOf_ok_iff locals ty mem localDecls layouts mrTy hPtr hTr hDecl al).mpr
      ⟨sz, hL, hV, hP, hLt⟩⟩

/-- Every entry of `layouts` has a valid Rust alignment (a power of two below `2^64`), as
guaranteed by `rustc`'s `TypeLayout` construction. -/
def TableAlignWf (layouts : Layout.LayoutTable) : Prop :=
  ∀ l ∈ layouts.entries,
    Layout.Align.isPowerOfTwoBytes l.align = true ∧ l.align.bytes < 18446744073709551616

private theorem intTyBytes_align_wf {k : RigidTy} {s : Signedness} {n : Nat}
    (h : intTyBytes k = some (s, n)) :
    Layout.Align.isPowerOfTwoBytes ⟨n⟩ = true ∧ n < 18446744073709551616 := by
  cases k with
  | uint u => cases u <;> cases h <;> exact ⟨by decide, by decide⟩
  | int i => cases i <;> cases h <;> exact ⟨by decide, by decide⟩
  | _ => simp [intTyBytes] at h

/-- **Alignment well-formedness of translated types**: under `TableAlignWf layouts`, every type in
the translated fragment whose MiniRust layout is `Sized(sz, al)` has a power-of-two alignment
below `2^64`. -/
theorem translateTy_align_wf (layouts : Layout.LayoutTable) (ty : Ty) (mrTy : Gen.Type)
    (sz al : Nat) (hWf : TableAlignWf layouts)
    (hTr : translateTy layouts ty = some mrTy)
    (hL : Interp.Type.layout mrTy = .ok (.Sized ⟨sz⟩ ⟨al⟩)) :
    Layout.Align.isPowerOfTwoBytes ⟨al⟩ = true ∧ al < 18446744073709551616 := by
  rw [translateTy_eq] at hTr
  by_cases hB : isBoolTy ty = true
  · simp only [hB] at hTr; cases hTr; cases hL; exact ⟨by decide, by decide⟩
  · simp only [hB] at hTr
    by_cases hO : isOrderingTy ty = true
    · simp only [hO] at hTr; cases hTr; rw [layout_ordering] at hL; cases hL
      exact ⟨by decide, by decide⟩
    · simp only [hO] at hTr
      cases hIB : intBoolTupleOf ty with
      | some it =>
        rw [hIB] at hTr; cases hTr
        rw [layout_intBoolTuple] at hL; cases hL
        rcases ty with ⟨k, idx⟩
        cases k <;> simp [intBoolTupleOf] at hIB
        case tuple ks =>
          cases ks with
          | nil => simp at hIB
          | cons k1 rest =>
            cases rest with
            | nil => simp at hIB
            | cons k2 rest2 =>
              cases rest2 with
              | cons _ _ => simp at hIB
              | nil =>
                cases k2 <;> simp at hIB
                obtain ⟨a, b, hk, rfl⟩ := hIB
                exact intTyBytes_align_wf hk
      | none =>
        rw [hIB] at hTr
        cases hI : intTypeOf ty with
        | some it =>
          rw [hI] at hTr; cases hTr
          have hk := intTypeOf_eq_some hI
          have hL' := (layout_int_agrees hk [] layouts).2.2
          rw [hL'] at hL; cases hL
          exact intTyBytes_align_wf hk
        | none =>
          rw [hI] at hTr
          cases hA : arrayTypeOf ty with
          | some r =>
            rcases r with ⟨elemIt, count⟩
            rw [hA] at hTr; cases hTr
            obtain ⟨ek, _, hek⟩ := arrayTypeOf_eq_some hA
            have hL' := (layout_intArray_agrees hek count [] layouts).2.2
            rw [hL'] at hL; cases hL
            exact intTyBytes_align_wf hek
          | none =>
            rw [hA] at hTr
            cases hT : tupleTypeOf layouts ty with
            | some r =>
              rcases r with ⟨fields, size, align⟩
              rw [hT] at hTr; cases hTr
              rw [layout_tupleSpec] at hL; cases hL
              obtain ⟨_, _, hSpec⟩ := tupleTypeOf_inv hT
              obtain ⟨l, _, _, _, hl, _, _, _, hal, _, _⟩ := specOfRigidTy_tuple_inv hSpec
              subst hal
              exact hWf l (List.mem_of_getElem? hl)
            | none =>
              rw [hT] at hTr
              cases hR : rawPtrTypeOf ty with
              | some t =>
                rw [hR] at hTr; cases hTr
                obtain ⟨m, pointee, mk, _, hmk, rfl⟩ := rawPtrTypeOf_eq_some hR
                obtain ⟨_, _, _, hL'⟩ := layout_rawPtr_agrees hmk m [] layouts
                rw [hL'] at hL; cases hL
                exact ⟨by decide, by decide⟩
              | none =>
                rw [hR] at hTr
                cases hRef : refTypeOf ty with
                | some t =>
                  rw [hRef] at hTr; cases hTr
                  have hL' := (layout_ref_agrees hRef [] layouts).2.2
                  rw [hL'] at hL; cases hL
                  exact ⟨by decide, by decide⟩
                | none =>
                  rw [hRef] at hTr
                  have hL' := layout_box_minirust hTr
                  rw [hL'] at hL; cases hL
                  exact ⟨by decide, by decide⟩

/-- **A2 (`AlignOf`, clean `.ok` iff under `TableAlignWf`)**: when `layouts` satisfies
`TableAlignWf`, the redundant power-of-two and `< 2^64` side conditions drop out completely —
Trusted's `AlignOf(ty)` returns `al` iff MiniRust's `Type::layout` is `Sized(sz, al)` with a
valid size `sz ≤ isize::MAX`. -/
theorem nullaryOp_alignOf_wf_ok_iff (locals : List LocalSlot) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) (mrTy : Gen.Type)
    (hPtr : layouts.pointerBits = 64) (hWf : TableAlignWf layouts)
    (hTr : translateTy layouts ty = some mrTy)
    (hDecl : DeclLayoutCoherent localDecls layouts ty) (al : Nat) :
    evalRvalue locals (.nullaryOp .alignOf ty) mem localDecls layouts =
        .ok (.scalar ⟨al, 8⟩) locals mem ↔
      ∃ sz, Interp.Type.layout mrTy = .ok (.Sized ⟨sz⟩ ⟨al⟩) ∧
        x86_64.valid_size ⟨sz⟩ = true := by
  rw [nullaryOp_alignOf_ok_iff locals ty mem localDecls layouts mrTy hPtr hTr hDecl al]
  constructor
  · rintro ⟨sz, hL, hV, _, _⟩
    exact ⟨sz, hL, hV⟩
  · rintro ⟨sz, hL, hV⟩
    obtain ⟨hP, hLt⟩ := translateTy_align_wf layouts ty mrTy sz al hWf hTr hL
    exact ⟨sz, hL, hV, hP, hLt⟩

/-! ### A4. `UbChecks` -/

/-- **A4 (Trusted, two-sided)**: `Rvalue.nullaryOp .ubChecks` returns `.ok` exactly at a `bool`
result type, and then it is `true` — the 1-byte scalar `1` — with the frame and the memory
unchanged, in every state. -/
theorem nullaryOp_ubChecks_ok_iff (locals : List LocalSlot) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) (v : Value)
    (locals' : List LocalSlot) (mem' : Memory) :
    evalRvalue locals (.nullaryOp .ubChecks ty) mem localDecls layouts = .ok v locals' mem' ↔
      ty.kind = .bool ∧ v = .scalar ⟨1, 1⟩ ∧ locals' = locals ∧ mem' = mem := by
  rcases ty with ⟨k, idx⟩
  cases k <;>
    first
    | (constructor
       · intro h
         cases h
         exact ⟨rfl, rfl, rfl, rfl⟩
       · rintro ⟨_, rfl, rfl, rfl⟩
         rfl)
    | (constructor
       · intro h
         cases h
       · rintro ⟨h, _⟩
         cases h)

/-- **A4 (Trusted, non-`bool` type)**: at any other result type `UbChecks` fails closed with
`.unsupported` (never UB, never a value). -/
theorem nullaryOp_ubChecks_nonBool_unsupported (locals : List LocalSlot) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) (h : ty.kind ≠ .bool) :
    evalRvalue locals (.nullaryOp .ubChecks ty) mem localDecls layouts = .unsupported := by
  rcases ty with ⟨k, idx⟩
  cases k <;> first | rfl | exact absurd rfl h

/-- **A4 (`UbChecks` ↔ MiniRust, all states)**. `minimize` lowers the runtime-check flag to a
`bool` constant fixed by the compilation session (`tooling/minimize/src/rvalue.rs`, lines 384-393:
> "smir::Operand::RuntimeChecks(check) => {
>      ..
>      let val = match check {
>          smir::RuntimeChecks::UbChecks => sess.ub_checks(),
>          ..
>      };
>      build::const_bool(val)
>  }"
), i.e. `ValueExpr::Constant(Constant::Bool(b), Type::Bool)`. With UB checks enabled
(`sess.ub_checks() = true`, the mode Trusted models), in every Trusted state and on every MiniRust
machine: Trusted returns the scalar `⟨bits, sz⟩ = ⟨1, 1⟩` without touching the state; the type
translates to `Type::Bool`; MiniRust's constant evaluates to `Value::Bool(true)` without changing
the machine; and the two values have the same representation — `Type::Bool` is `sz = 1` byte
wide, and `Type::encode` of `true` is the single initialized byte `bits = 1`. -/
theorem nullaryOp_ubChecks_minirust (locals : List LocalSlot) (idx : LayoutIdx) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) (m : Mach) :
    ∃ bits sz,
      evalRvalue locals (.nullaryOp .ubChecks ⟨.bool, idx⟩) mem localDecls layouts =
          .ok (.scalar ⟨bits, sz⟩) locals mem ∧
        translateTy layouts ⟨.bool, idx⟩ = some .Bool ∧
        evalConstant m (.Bool true) = .ok (.Bool true) ∧
        evalValue m (.Constant (.Bool true) .Bool) = .ok ((.Bool true, .Bool), m) ∧
        Interp.Type.layout .Bool = .ok (.Sized ⟨sz⟩ ⟨1⟩) ∧
        Interp.Type.encode .Bool (.Bool true) = .ok [.Init (UInt8.ofNat bits) none] ∧
        Interp.Type.decode .Bool [.Init (UInt8.ofNat bits) none] = .ok (some (.Bool true)) :=
  ⟨1, 1, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **A4 (every `Machine M`, in particular `MachTB`)**: the MiniRust side of
`nullaryOp_ubChecks_minirust` on the polymorphic interpreter. -/
theorem ubChecks_minirustM {M : Type} [Gen.Memory M] [MemoryOps M] (m : Gen.Machine M) :
    evalConstantM m (.Bool true) = .ok (.Bool true) ∧
      Interp.Type.encodeM (M := M) .Bool (.Bool true) = .ok [.Init 1 none] ∧
      Interp.Type.decodeM (M := M) .Bool [.Init 1 none] = .ok (some (.Bool true)) :=
  ⟨rfl, rfl, rfl⟩

/-- **A4 (session dependence, two-sided)**: Trusted's `UbChecks` value has the representation of
MiniRust's `const_bool(b)` exactly for `b = true`. For a compilation session with UB checks
disabled (`sess.ub_checks() = false`) `minimize` emits `false`, which Trusted — modelling the
UB-checking mode only — does not return. -/
theorem ubChecks_agrees_iff_session_flag (b : Bool) (locals : List LocalSlot) (idx : LayoutIdx)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) :
    (∃ bits,
      evalRvalue locals (.nullaryOp .ubChecks ⟨.bool, idx⟩) mem localDecls layouts =
          .ok (.scalar ⟨bits, 1⟩) locals mem ∧
        Interp.Type.encode .Bool (.Bool b) = .ok [.Init (UInt8.ofNat bits) none]) ↔
      b = true := by
  constructor
  · rintro ⟨bits, h1, h2⟩
    cases h1
    cases b
    · cases h2
    · rfl
  · rintro rfl
    exact ⟨1, rfl, rfl⟩

/-! ### A5. `ContractChecks` -/

/-- **A5 (Trusted, fail-closed)**: `Rvalue.nullaryOp .contractChecks` is `.unsupported` for every
type and in every state — never a value, never UB. -/
theorem nullaryOp_contractChecks_unsupported (locals : List LocalSlot) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) :
    evalRvalue locals (.nullaryOp .contractChecks ty) mem localDecls layouts = .unsupported := rfl

/-- **A5 (contrast with MiniRust)**. MiniRust itself has no contract-check construct; `minimize`
resolves the flag at translation time to `build::const_bool(sess.contract_checks())`
(`tooling/minimize/src/rvalue.rs`, line 389), a `bool` constant that evaluates to a definite value
for either session flag `b`, on every machine. Trusted does not model the session's
contract-check flag and fails closed: its `.unsupported` is sound for both sessions (it never
claims a value that one of them contradicts), but it is not a completeness match — MiniRust is
defined where Trusted is not. The fragment's rvalue translation rejects every
`Rvalue.nullaryOp` (`translateRvalue .. = none`), so no translated program reaches this gap. -/
theorem nullaryOp_contractChecks_minirust_contrast (b : Bool) (locals : List LocalSlot) (ty : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) (m : Mach)
    (targetTy : Option Ty) (op : NullOp) :
    evalRvalue locals (.nullaryOp .contractChecks ty) mem localDecls layouts = .unsupported ∧
      evalValue m (.Constant (.Bool b) .Bool) = .ok ((.Bool b, .Bool), m) ∧
      translateRvalue layouts localDecls targetTy (.nullaryOp op ty) = none :=
  ⟨rfl, rfl, rfl⟩

/-! ### A. Non-vacuity witnesses and divergence witnesses

A concrete 64-bit layout table and declaration list on which every hypothesis of the symbolic
theorems above holds, and concrete tables on which declaration-layout coherence fails and the two
semantics genuinely disagree. -/

private def primLayout (size align : Nat) : Layout.TypeLayout :=
  { size := ⟨size⟩, align := ⟨align⟩, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false, fieldLayouts := [] }

private def structLayout (size align : Nat) (offsets : List Nat) (memoryIndex : List Nat)
    (fieldLayouts : List Nat) : Layout.TypeLayout :=
  { size := ⟨size⟩, align := ⟨align⟩, backendRepr := .memory,
    fields := .arbitrary (offsets.map (fun o => ⟨o⟩)) memoryIndex, variants := .single 0,
    isUninhabited := false, fieldLayouts := fieldLayouts }

/-- `#[repr(C)] struct P { a: u8, b: u32 }` (3 bytes of padding after `a`). -/
def aPKind : RigidTy := .adt "bridge::P" [.uint .u8, .uint .u32]

/-- Witness layout table:
`0`: `u8`; `1`: `u32`; `2`: `u16`;
`3`: `(u8, u32)` — `rustc` reorders the fields (`u32` at offset `0`, `u8` at offset `4`), size `8`,
alignment `4`, 3 bytes of trailing padding;
`4`: `P` — fields at offsets `0` and `4`, size `8`, alignment `4`;
`5`: `(P, u16)` — fields at offsets `0` and `8`, size `12`, alignment `4`. -/
def aLayouts : Layout.LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [primLayout 1 1, primLayout 4 4, primLayout 2 2,
      structLayout 8 4 [4, 0] [1, 0] [0, 1],
      structLayout 8 4 [0, 4] [0, 1] [0, 1],
      structLayout 12 4 [0, 8] [0, 1] [4, 2]] }

/-- `(u8, u32)`. -/
def aTupTy : Ty := { kind := .tuple [.uint .u8, .uint .u32], layoutIdx := 3 }

/-- `P`. -/
def aPTy : Ty := { kind := aPKind, layoutIdx := 4 }

/-- `(P, u16)`. -/
def aOuterTy : Ty := { kind := .tuple [aPKind, .uint .u16], layoutIdx := 5 }

/-- `_0 : usize`, `_1 : (u8, u32)`, `_2 : P`, `_3 : (P, u16)`. -/
def aDecls : List LocalDecl := [
  { mutability := .mut, ty := { kind := .uint .usize, layoutIdx := 0 }, debugName := none },
  { mutability := .mut, ty := aTupTy, debugName := none },
  { mutability := .mut, ty := aPTy, debugName := none },
  { mutability := .mut, ty := aOuterTy, debugName := none }]

/-- MiniRust translation of `(u8, u32)`. -/
def aTupMr : Gen.Type :=
  .Tuple [(⟨4⟩, .Int ⟨.Unsigned, ⟨1⟩⟩), (⟨0⟩, .Int ⟨.Unsigned, ⟨4⟩⟩)] ⟨⟨8⟩, ⟨4⟩, none⟩ none

/-- MiniRust translation of `P`. -/
def aPMr : Gen.Type :=
  .Tuple [(⟨0⟩, .Int ⟨.Unsigned, ⟨1⟩⟩), (⟨4⟩, .Int ⟨.Unsigned, ⟨4⟩⟩)] ⟨⟨8⟩, ⟨4⟩, none⟩ none

/-- MiniRust translation of `(P, u16)`. -/
def aOuterMr : Gen.Type :=
  .Tuple [(⟨0⟩, aPMr), (⟨8⟩, .Int ⟨.Unsigned, ⟨2⟩⟩)] ⟨⟨12⟩, ⟨4⟩, none⟩ none

/-- The aggregate witness types translate to the expected MiniRust tuple types. -/
theorem wit_translateTy_aggregates :
    translateTy aLayouts aTupTy = some aTupMr ∧ translateTy aLayouts aPTy = some aPMr ∧
      translateTy aLayouts aOuterTy = some aOuterMr :=
  ⟨rfl, rfl, rfl⟩

/-- The declaration layouts of the aggregate witness types are coherent, by
`declLayoutCoherent_of_same_entry` (the hypotheses of that theorem are satisfiable). -/
theorem wit_declLayoutCoherent :
    DeclLayoutCoherent aDecls aLayouts aTupTy ∧ DeclLayoutCoherent aDecls aLayouts aPTy ∧
      DeclLayoutCoherent aDecls aLayouts aOuterTy :=
  ⟨declLayoutCoherent_of_same_entry aDecls aLayouts aTupTy _ 8 4 rfl (by intro h; cases h) rfl
      (by intro l h; cases h; rfl),
    declLayoutCoherent_of_same_entry aDecls aLayouts aPTy _ 8 4 rfl (by intro h; cases h) rfl
      (by intro l h; cases h; rfl),
    declLayoutCoherent_of_same_entry aDecls aLayouts aOuterTy _ 12 4 rfl (by intro h; cases h) rfl
      (by intro l h; cases h; rfl)⟩

private theorem aNonAgg (ty : Ty) (hT : ∀ ks, ty.kind ≠ .tuple ks)
    (hA : ∀ p args, ty.kind ≠ .adt p args) : DeclLayoutCoherent aDecls aLayouts ty :=
  declLayoutCoherent_of_nonAggregate aDecls aLayouts ty hT hA

/-- **A1/A2 witness (primitives, pointer, array)**: instantiating
`nullaryOp_sizeOf_alignOf_of_minirust_layout` on `u8`, `u32`, `u64`, `usize`, `bool`, the thin raw
pointer `*const u32`, and the array `[u32; 3]`: Trusted's `SizeOf` / `AlignOf` are the size and
alignment of MiniRust's `Type::layout`. -/
theorem wit_sizeOf_alignOf_primitives :
    (evalRvalue [] (.nullaryOp .sizeOf ⟨.uint .u8, 0⟩) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨1, 8⟩) [] emptyMemory ∧
      evalRvalue [] (.nullaryOp .alignOf ⟨.uint .u8, 0⟩) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨1, 8⟩) [] emptyMemory) ∧
    (evalRvalue [] (.nullaryOp .sizeOf ⟨.uint .u32, 1⟩) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨4, 8⟩) [] emptyMemory ∧
      evalRvalue [] (.nullaryOp .alignOf ⟨.uint .u32, 1⟩) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨4, 8⟩) [] emptyMemory) ∧
    (evalRvalue [] (.nullaryOp .sizeOf ⟨.uint .u64, 0⟩) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨8, 8⟩) [] emptyMemory ∧
      evalRvalue [] (.nullaryOp .alignOf ⟨.uint .u64, 0⟩) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨8, 8⟩) [] emptyMemory) ∧
    (evalRvalue [] (.nullaryOp .sizeOf ⟨.uint .usize, 0⟩) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨8, 8⟩) [] emptyMemory ∧
      evalRvalue [] (.nullaryOp .alignOf ⟨.uint .usize, 0⟩) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨8, 8⟩) [] emptyMemory) ∧
    (evalRvalue [] (.nullaryOp .sizeOf ⟨.bool, 0⟩) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨1, 8⟩) [] emptyMemory ∧
      evalRvalue [] (.nullaryOp .alignOf ⟨.bool, 0⟩) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨1, 8⟩) [] emptyMemory) ∧
    (evalRvalue [] (.nullaryOp .sizeOf ⟨.rawPtr .not (.uint .u32), 0⟩) emptyMemory aDecls
          aLayouts = .ok (.scalar ⟨8, 8⟩) [] emptyMemory ∧
      evalRvalue [] (.nullaryOp .alignOf ⟨.rawPtr .not (.uint .u32), 0⟩) emptyMemory aDecls
          aLayouts = .ok (.scalar ⟨8, 8⟩) [] emptyMemory) ∧
    (evalRvalue [] (.nullaryOp .sizeOf ⟨.array (.uint .u32) 3, 0⟩) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨12, 8⟩) [] emptyMemory ∧
      evalRvalue [] (.nullaryOp .alignOf ⟨.array (.uint .u32) 3, 0⟩) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨4, 8⟩) [] emptyMemory) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact nullaryOp_sizeOf_alignOf_of_minirust_layout [] _ emptyMemory aDecls aLayouts
      (.Int ⟨.Unsigned, ⟨1⟩⟩) rfl rfl
      (aNonAgg _ (by intro ks h; cases h) (by intro p a h; cases h)) 1 1 rfl (by decide)
      (by decide) (by decide)
  · exact nullaryOp_sizeOf_alignOf_of_minirust_layout [] _ emptyMemory aDecls aLayouts
      (.Int ⟨.Unsigned, ⟨4⟩⟩) rfl rfl
      (aNonAgg _ (by intro ks h; cases h) (by intro p a h; cases h)) 4 4 rfl (by decide)
      (by decide) (by decide)
  · exact nullaryOp_sizeOf_alignOf_of_minirust_layout [] _ emptyMemory aDecls aLayouts
      (.Int ⟨.Unsigned, ⟨8⟩⟩) rfl rfl
      (aNonAgg _ (by intro ks h; cases h) (by intro p a h; cases h)) 8 8 rfl (by decide)
      (by decide) (by decide)
  · exact nullaryOp_sizeOf_alignOf_of_minirust_layout [] _ emptyMemory aDecls aLayouts
      (.Int ⟨.Unsigned, ⟨8⟩⟩) rfl rfl
      (aNonAgg _ (by intro ks h; cases h) (by intro p a h; cases h)) 8 8 rfl (by decide)
      (by decide) (by decide)
  · exact nullaryOp_sizeOf_alignOf_of_minirust_layout [] _ emptyMemory aDecls aLayouts
      .Bool rfl rfl
      (aNonAgg _ (by intro ks h; cases h) (by intro p a h; cases h)) 1 1 rfl (by decide)
      (by decide) (by decide)
  · exact nullaryOp_sizeOf_alignOf_of_minirust_layout [] _ emptyMemory aDecls aLayouts
      (.Ptr (.Raw .None)) rfl rfl
      (aNonAgg _ (by intro ks h; cases h) (by intro p a h; cases h)) 8 8 rfl (by decide)
      (by decide) (by decide)
  · exact nullaryOp_sizeOf_alignOf_of_minirust_layout [] _ emptyMemory aDecls aLayouts
      (.Array (.Int ⟨.Unsigned, ⟨4⟩⟩) 3) rfl rfl
      (aNonAgg _ (by intro ks h; cases h) (by intro p a h; cases h)) 12 4 rfl (by decide)
      (by decide) (by decide)

/-- **A1/A2 witness (padded tuple and structs)**: the same instantiation on `(u8, u32)` (size `8`
with 3 bytes of padding, alignment `4`), on `P`, and on the nested `(P, u16)` (size `12`). -/
theorem wit_sizeOf_alignOf_aggregates :
    (evalRvalue [] (.nullaryOp .sizeOf aTupTy) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨8, 8⟩) [] emptyMemory ∧
      evalRvalue [] (.nullaryOp .alignOf aTupTy) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨4, 8⟩) [] emptyMemory) ∧
    (evalRvalue [] (.nullaryOp .sizeOf aPTy) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨8, 8⟩) [] emptyMemory ∧
      evalRvalue [] (.nullaryOp .alignOf aPTy) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨4, 8⟩) [] emptyMemory) ∧
    (evalRvalue [] (.nullaryOp .sizeOf aOuterTy) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨12, 8⟩) [] emptyMemory ∧
      evalRvalue [] (.nullaryOp .alignOf aOuterTy) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨4, 8⟩) [] emptyMemory) :=
  ⟨nullaryOp_sizeOf_alignOf_of_minirust_layout [] aTupTy emptyMemory aDecls aLayouts aTupMr rfl rfl
      wit_declLayoutCoherent.1 8 4 rfl (by decide) (by decide) (by decide),
    nullaryOp_sizeOf_alignOf_of_minirust_layout [] aPTy emptyMemory aDecls aLayouts aPMr rfl rfl
      wit_declLayoutCoherent.2.1 8 4 rfl (by decide) (by decide) (by decide),
    nullaryOp_sizeOf_alignOf_of_minirust_layout [] aOuterTy emptyMemory aDecls aLayouts aOuterMr
      rfl rfl wit_declLayoutCoherent.2.2 12 4 rfl (by decide) (by decide) (by decide)⟩

/-- Layout table for the fixed-ABI aggregates: `0`: `core::cmp::Ordering` (`repr(i8)`: size `1`,
alignment `1`); `1`: `Box<u32>` (a thin pointer: size `8`, alignment `8`). -/
def sLayouts : Layout.LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [primLayout 1 1, primLayout 8 8] }

/-- `core::cmp::Ordering`. -/
def sOrderingTy : Ty := { kind := .adt "core::cmp::Ordering" [], layoutIdx := 0 }

/-- `Box<u32>`. -/
def sBoxTy : Ty := { kind := .adt "alloc::boxed::Box" [.uint .u32], layoutIdx := 1 }

/-- `(u32, bool)` (the result type of a checked `u32` operation). -/
def sIntBoolTy : Ty := { kind := .tuple [.uint .u32, .bool], layoutIdx := 0 }

/-- `_0 : Ordering`, `_1 : Box<u32>` (no local of type `(u32, bool)`). -/
def sDecls : List LocalDecl := [
  { mutability := .mut, ty := sOrderingTy, debugName := none },
  { mutability := .mut, ty := sBoxTy, debugName := none }]

/-- **A1/A2 witness (fixed-ABI aggregates)**: `core::cmp::Ordering` (`(1, 1)`), `Box<u32>`
(`(8, 8)`), and `(u32, bool)` (`(8, 4)`). For `(u32, bool)` no local of that type exists, and
Trusted's *structural* tuple fallback (field sizes summed, rounded up to the maximal field
alignment) agrees with MiniRust's `IntType::with_overflow` layout. -/
theorem wit_sizeOf_alignOf_fixedAbi :
    (evalRvalue [] (.nullaryOp .sizeOf sOrderingTy) emptyMemory sDecls sLayouts =
        .ok (.scalar ⟨1, 8⟩) [] emptyMemory ∧
      evalRvalue [] (.nullaryOp .alignOf sOrderingTy) emptyMemory sDecls sLayouts =
        .ok (.scalar ⟨1, 8⟩) [] emptyMemory) ∧
    (evalRvalue [] (.nullaryOp .sizeOf sBoxTy) emptyMemory sDecls sLayouts =
        .ok (.scalar ⟨8, 8⟩) [] emptyMemory ∧
      evalRvalue [] (.nullaryOp .alignOf sBoxTy) emptyMemory sDecls sLayouts =
        .ok (.scalar ⟨8, 8⟩) [] emptyMemory) ∧
    (evalRvalue [] (.nullaryOp .sizeOf sIntBoolTy) emptyMemory sDecls sLayouts =
        .ok (.scalar ⟨8, 8⟩) [] emptyMemory ∧
      evalRvalue [] (.nullaryOp .alignOf sIntBoolTy) emptyMemory sDecls sLayouts =
        .ok (.scalar ⟨4, 8⟩) [] emptyMemory) :=
  ⟨nullaryOp_sizeOf_alignOf_of_minirust_layout [] sOrderingTy emptyMemory sDecls sLayouts
      orderingTy rfl rfl (declLayoutCoherent_of_eval 1 1 rfl rfl rfl rfl) 1 1 rfl (by decide)
      (by decide) (by decide),
    nullaryOp_sizeOf_alignOf_of_minirust_layout [] sBoxTy emptyMemory sDecls sLayouts
      (.Ptr (.Box (intPointeeInfo ⟨.Unsigned, ⟨4⟩⟩))) rfl rfl
      (declLayoutCoherent_of_eval 8 8 rfl rfl rfl rfl) 8 8 rfl (by decide) (by decide)
      (by decide),
    nullaryOp_sizeOf_alignOf_of_minirust_layout [] sIntBoolTy emptyMemory sDecls sLayouts
      (intBoolTupleTy ⟨.Unsigned, ⟨4⟩⟩) rfl rfl
      (declLayoutCoherent_of_eval 8 4 rfl rfl rfl rfl) 8 4 rfl (by decide) (by decide)
      (by decide)⟩

/-- **A1 witness (`.unsupported`)**: `[u64; 2^61]` has MiniRust layout size `2^64 > isize::MAX`
(an invalid size), and Trusted's `SizeOf` fails closed. -/
theorem wit_sizeOf_oversized_unsupported :
    Interp.Type.layout (.Array (.Int ⟨.Unsigned, ⟨8⟩⟩) 2305843009213693952) =
        .ok (.Sized ⟨18446744073709551616⟩ ⟨8⟩) ∧
      x86_64.valid_size ⟨18446744073709551616⟩ = false ∧
      evalRvalue [] (.nullaryOp .sizeOf ⟨.array (.uint .u64) 2305843009213693952, 0⟩) emptyMemory
          aDecls aLayouts = .unsupported := by
  refine ⟨?_, by decide, ?_⟩
  · exact (layout_intArray_agrees (ek := .uint .u64) (s := .Unsigned) (n := 8) rfl
      2305843009213693952 aDecls aLayouts).2.2
  · exact (nullaryOp_sizeOf_unsupported_iff [] _ emptyMemory aDecls aLayouts
      (.Array (.Int ⟨.Unsigned, ⟨8⟩⟩) 2305843009213693952) rfl rfl
      (aNonAgg _ (by intro ks h; cases h) (by intro p a h; cases h))).mpr
      ⟨18446744073709551616, ⟨8⟩,
        (layout_intArray_agrees (ek := .uint .u64) (s := .Unsigned) (n := 8) rfl
          2305843009213693952 aDecls aLayouts).2.2, by decide⟩

private theorem aFieldLayoutsRecorded : FieldLayoutsRecorded aLayouts := by
  intro l hl offsets mi hf
  simp only [aLayouts, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> cases hf <;> rfl

/-- **A3 witness**: instantiating the `OffsetOf` theorems. `offset_of!((u8, u32), 0) = 4` and
`offset_of!((u8, u32), 1) = 0` (the reordered tuple), `offset_of!(P, a) = 0`,
`offset_of!(P, b) = 4`, `offset_of!((P, u16), 1) = 8`, the nested
`offset_of!((P, u16), 0.b) = 0 + 4`; a non-existent field and a non-zero variant are
`.unsupported`. Each Trusted result is the MiniRust field offset (`mrFieldOffset?`) or nested
offset sum (`mrPathOffset?`). -/
theorem wit_offsetOf :
    (mrFieldOffset? aTupMr 0 = some 4 ∧
      evalRvalue [] (.nullaryOp (.offsetOf [(0, 0)]) aTupTy) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨4, 8⟩) [] emptyMemory) ∧
    (mrFieldOffset? aTupMr 1 = some 0 ∧
      evalRvalue [] (.nullaryOp (.offsetOf [(0, 1)]) aTupTy) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨0, 8⟩) [] emptyMemory) ∧
    (mrFieldOffset? aPMr 0 = some 0 ∧
      evalRvalue [] (.nullaryOp (.offsetOf [(0, 0)]) aPTy) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨0, 8⟩) [] emptyMemory) ∧
    (mrFieldOffset? aPMr 1 = some 4 ∧
      evalRvalue [] (.nullaryOp (.offsetOf [(0, 1)]) aPTy) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨4, 8⟩) [] emptyMemory) ∧
    (mrFieldOffset? aOuterMr 1 = some 8 ∧
      evalRvalue [] (.nullaryOp (.offsetOf [(0, 1)]) aOuterTy) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨8, 8⟩) [] emptyMemory) ∧
    (mrPathOffset? aOuterMr [0, 1] = some 4 ∧
      evalRvalue [] (.nullaryOp (.offsetOf [(0, 0), (0, 1)]) aOuterTy) emptyMemory aDecls
          aLayouts = .ok (.scalar ⟨4, 8⟩) [] emptyMemory) ∧
    (mrFieldOffset? aPMr 2 = none ∧
      evalRvalue [] (.nullaryOp (.offsetOf [(0, 2)]) aPTy) emptyMemory aDecls aLayouts =
        .unsupported) ∧
    evalRvalue [] (.nullaryOp (.offsetOf [(1, 0)]) aPTy) emptyMemory aDecls aLayouts =
      .unsupported := by
  refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ?_, ?_⟩
  · exact (nullaryOp_offsetOf_field_minirust [] aTupTy emptyMemory aDecls aLayouts _ 8 4 rfl rfl
      wit_declLayoutCoherent.1 rfl 0).trans rfl
  · exact (nullaryOp_offsetOf_field_minirust [] aTupTy emptyMemory aDecls aLayouts _ 8 4 rfl rfl
      wit_declLayoutCoherent.1 rfl 1).trans rfl
  · exact (nullaryOp_offsetOf_field_minirust [] aPTy emptyMemory aDecls aLayouts _ 8 4 rfl rfl
      wit_declLayoutCoherent.2.1 rfl 0).trans rfl
  · exact (nullaryOp_offsetOf_field_minirust [] aPTy emptyMemory aDecls aLayouts _ 8 4 rfl rfl
      wit_declLayoutCoherent.2.1 rfl 1).trans rfl
  · exact (nullaryOp_offsetOf_field_minirust [] aOuterTy emptyMemory aDecls aLayouts _ 12 4 rfl rfl
      wit_declLayoutCoherent.2.2 rfl 1).trans rfl
  · exact (nullaryOp_offsetOf_path_minirust [] aOuterTy emptyMemory aDecls aLayouts _ 12 4 rfl
      aFieldLayoutsRecorded rfl wit_declLayoutCoherent.2.2 rfl [0, 1] 4 rfl).trans rfl
  · exact nullaryOp_offsetOf_field_out_of_range [] aPTy emptyMemory aDecls aLayouts _ 8 4 rfl rfl
      wit_declLayoutCoherent.2.1 rfl 2 (by decide)
  · exact nullaryOp_offsetOf_variant_ne_zero_unsupported [] aPTy emptyMemory aDecls aLayouts _ 8 4
      rfl rfl 1 0 (by decide) []

private theorem aOuterScalarLeavesPrimitive :
    ScalarLeavesPrimitive aLayouts aOuterTy.layoutIdx
      (.tuple [(0, .tuple [(0, .scalar ⟨.Unsigned, ⟨1⟩⟩), (4, .scalar ⟨.Unsigned, ⟨4⟩⟩)] 8 4),
               (8, .scalar ⟨.Unsigned, ⟨2⟩⟩)] 12 4) := by
  refine .tuple _ _ _ _ (fun l hl i o s hfi => ?_)
  cases hl
  rcases i with _ | _ | _
  · cases hfi
    refine .tuple _ _ _ _ (fun l' hl' j o' s' hfj => ?_)
    cases hl'
    rcases j with _ | _ | _
    · cases hfj; exact .scalar _ _ (fun ls hls => by cases hls; exact ⟨rfl, rfl⟩)
    · cases hfj; exact .scalar _ _ (fun ls hls => by cases hls; exact ⟨rfl, rfl⟩)
    · cases hfj
  · cases hfi; exact .scalar _ _ (fun ls hls => by cases hls; exact ⟨rfl, rfl⟩)
  · cases hfi

/-- **A3 witness (two-sided nested paths)**: `aOuterTy` (`(P, u16)`) satisfies both
`FieldLayoutsRecorded` and `ScalarLeavesPrimitive`, so `nullaryOp_offsetOf_path_minirust_two_sided`
discharges both valid nested paths (`[0, 1] -> some 4`) and invalid nested paths (`[0, 2]`
out-of-range inside `P`, and `[0, 1, 0]` descending into the scalar `u32` leaf `P.b`, both `none` /
`.unsupported`). -/
theorem wit_offsetOf_path_two_sided :
    FieldLayoutsRecorded aLayouts ∧
    ScalarLeavesPrimitive aLayouts aOuterTy.layoutIdx
      (.tuple [(0, .tuple [(0, .scalar ⟨.Unsigned, ⟨1⟩⟩), (4, .scalar ⟨.Unsigned, ⟨4⟩⟩)] 8 4),
               (8, .scalar ⟨.Unsigned, ⟨2⟩⟩)] 12 4) ∧
    evalRvalue [] (.nullaryOp (.offsetOf [(0, 0), (0, 1)]) aOuterTy) emptyMemory aDecls aLayouts =
      .ok (.scalar ⟨4, 8⟩) [] emptyMemory ∧
    evalRvalue [] (.nullaryOp (.offsetOf [(0, 0), (0, 2)]) aOuterTy) emptyMemory aDecls aLayouts =
      .unsupported ∧
    evalRvalue [] (.nullaryOp (.offsetOf [(0, 0), (0, 1), (0, 0)]) aOuterTy) emptyMemory aDecls
        aLayouts = .unsupported := by
  refine ⟨aFieldLayoutsRecorded, aOuterScalarLeavesPrimitive, ?_, ?_, ?_⟩
  · exact (nullaryOp_offsetOf_path_minirust_two_sided [] aOuterTy emptyMemory aDecls aLayouts _ 12 4
      rfl aFieldLayoutsRecorded aOuterScalarLeavesPrimitive rfl wit_declLayoutCoherent.2.2 rfl
      [0, 1]).trans rfl
  · exact (nullaryOp_offsetOf_path_minirust_two_sided [] aOuterTy emptyMemory aDecls aLayouts _ 12 4
      rfl aFieldLayoutsRecorded aOuterScalarLeavesPrimitive rfl wit_declLayoutCoherent.2.2 rfl
      [0, 2]).trans rfl
  · exact (nullaryOp_offsetOf_path_minirust_two_sided [] aOuterTy emptyMemory aDecls aLayouts _ 12 4
      rfl aFieldLayoutsRecorded aOuterScalarLeavesPrimitive rfl wit_declLayoutCoherent.2.2 rfl
      [0, 1, 0]).trans rfl

/-- **A4/A5 witness**: `UbChecks` at `bool` is `true`, at `u8` it is `.unsupported`;
`ContractChecks` is `.unsupported`. -/
theorem wit_ubChecks_contractChecks :
    evalRvalue [] (.nullaryOp .ubChecks ⟨.bool, 0⟩) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨1, 1⟩) [] emptyMemory ∧
      evalRvalue [] (.nullaryOp .ubChecks ⟨.uint .u8, 0⟩) emptyMemory aDecls aLayouts =
        .unsupported ∧
      evalRvalue [] (.nullaryOp .contractChecks ⟨.bool, 0⟩) emptyMemory aDecls aLayouts =
        .unsupported :=
  ⟨(nullaryOp_ubChecks_ok_iff [] ⟨.bool, 0⟩ emptyMemory aDecls aLayouts _ _ _).mpr
      ⟨rfl, rfl, rfl, rfl⟩,
    nullaryOp_ubChecks_nonBool_unsupported [] ⟨.uint .u8, 0⟩ emptyMemory aDecls aLayouts
      (by intro h; cases h),
    nullaryOp_contractChecks_unsupported [] ⟨.bool, 0⟩ emptyMemory aDecls aLayouts⟩

/-- `#[repr(C)] struct Q { a: u32, b: u8 }`. -/
def dQKind : RigidTy := .adt "bridge::Q" [.uint .u32, .uint .u8]

/-- A layout table that violates `rustc`'s size/alignment invariant: entry `2` gives `Q` size `5`
at alignment `4` (not a multiple; `rustc` computes `8`). Entry `3` is a second, different layout
(size `16`, alignment `8`) for the same kind. -/
def dLayouts : Layout.LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [primLayout 4 4, primLayout 1 1,
      structLayout 5 4 [0, 4] [0, 1] [0, 1],
      structLayout 16 8 [0, 8] [0, 1] [0, 1]] }

/-- `_0 : Q` with layout entry `2`. -/
def dDecls : List LocalDecl := [
  { mutability := .mut, ty := { kind := dQKind, layoutIdx := 2 }, debugName := none }]

/-- **Divergence 1 (size not a multiple of the alignment).** On a layout entry with size `5` and
alignment `4`, Trusted's `SizeOf` returns the recorded size `5`, while MiniRust's
`Type::layout` of the translated tuple type rounds the head up to the alignment
(`TupleHeadLayout::head_size_and_align`) and reports `8`. The `size % align = 0` clause of
`DeclLayoutCoherent` (a `rustc` layout invariant, `TypeLayout.isWellFormed`) is therefore
necessary for A1; this table is not coherent. -/
theorem sizeOf_divergence_size_not_multiple_of_align :
    ∃ mrTy,
      translateTy dLayouts ⟨dQKind, 2⟩ = some mrTy ∧
        Interp.Type.layout mrTy = .ok (.Sized ⟨8⟩ ⟨4⟩) ∧
        evalRvalue [] (.nullaryOp .sizeOf ⟨dQKind, 2⟩) emptyMemory dDecls dLayouts =
          .ok (.scalar ⟨5, 8⟩) [] emptyMemory ∧
        ¬ DeclLayoutCoherent dDecls dLayouts ⟨dQKind, 2⟩ := by
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  intro h
  obtain ⟨_, _, h3⟩ := h 5 4 rfl
  cases h3

/-- **Divergence 2 (Trusted ignores `argTy.layoutIdx`).** Trusted's `SizeOf(T)` never reads the
layout index carried by the rvalue's type: it scans `localDecls` for a local of the same *kind*
and reads that local's layout. If the rvalue's type names a different entry than that local
(entry `3`: size `16`; the local's entry `2`: size `5`), Trusted returns the local's size while
`minimize` translates the type from its own entry. `rustc`'s `layout_of` is a function of the
type, so captured MIR never produces such a table; the first clause of `DeclLayoutCoherent` rules
it out. -/
theorem sizeOf_divergence_layoutIdx_ignored :
    ∃ mrTy,
      translateTy dLayouts ⟨dQKind, 3⟩ = some mrTy ∧
        Interp.Type.layout mrTy = .ok (.Sized ⟨16⟩ ⟨8⟩) ∧
        evalRvalue [] (.nullaryOp .sizeOf ⟨dQKind, 3⟩) emptyMemory dDecls dLayouts =
          .ok (.scalar ⟨5, 8⟩) [] emptyMemory ∧
        ¬ DeclLayoutCoherent dDecls dLayouts ⟨dQKind, 3⟩ := by
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  intro h
  obtain ⟨h1, _, _⟩ := h 16 8 rfl
  cases h1

/-- **Completeness gap (no local of the type).** For an ADT that is not the type of any local,
Trusted has no layout source and `SizeOf` fails closed with `.unsupported`, although the layout
entry of the type exists and MiniRust's layout of the translated type is a valid `(8, 4)`. This is
one-way soundness (never a wrong size, never UB), not two-sided parity. -/
theorem sizeOf_unsupported_without_decl :
    translateTy aLayouts aPTy = some aPMr ∧
      Interp.Type.layout aPMr = .ok (.Sized ⟨8⟩ ⟨4⟩) ∧
      x86_64.valid_size ⟨8⟩ = true ∧
      evalRvalue [] (.nullaryOp .sizeOf aPTy) emptyMemory [] aLayouts = .unsupported ∧
      ¬ DeclLayoutCoherent [] aLayouts aPTy := by
  refine ⟨rfl, rfl, by decide, rfl, ?_⟩
  intro h
  obtain ⟨h1, _, _⟩ := h 8 4 rfl
  cases h1

/-- **Non-vacuity of `TableAlignWf`** (`[adv ep2-A1]`): the witness layout table satisfies the
alignment well-formedness hypothesis of `translateTy_align_wf` and
`nullaryOp_alignOf_wf_ok_iff`. -/
theorem wit_tableAlignWf : TableAlignWf aLayouts := by
  unfold TableAlignWf
  decide +kernel

/-- **`nullaryOp_alignOf_wf_ok_iff` on the witness table** (`[adv ep2-A1]`): its layout-table
hypotheses (`pointerBits = 64`, `TableAlignWf`, `DeclLayoutCoherent`) are discharged for the
padded tuple, so for whatever MiniRust type `translateTy` assigns to it, `AlignOf` returns `al`
exactly when that type's `Type::layout` has alignment `al` and a valid size. -/
theorem wit_alignOf_wf_ok_iff_instance (mrTy : Gen.Type)
    (hTr : translateTy aLayouts aTupTy = some mrTy) (al : Nat) :
    evalRvalue [] (.nullaryOp .alignOf aTupTy) emptyMemory aDecls aLayouts =
        .ok (.scalar ⟨al, 8⟩) [] emptyMemory ↔
      ∃ sz, Interp.Type.layout mrTy = .ok (.Sized ⟨sz⟩ ⟨al⟩) ∧
        x86_64.valid_size ⟨sz⟩ = true :=
  nullaryOp_alignOf_wf_ok_iff [] aTupTy emptyMemory aDecls aLayouts mrTy rfl wit_tableAlignWf hTr
    wit_declLayoutCoherent.1 al

/-! ### End-to-end witnesses on `CapturedMir` bodies

The rvalues above inside whole MIR bodies, run through Trusted's coinductive machine semantics
(`mirCallTree`, `ReachesRet`). -/

private theorem mirTree_observe (body : CapturedMir) (s : MachineState) :
    (mirTree body s).observe =
      (stepMirFn body s).map (Trusted.ITree.ITree.cofix (stepMirState body)) := by
  simp [mirTree, Trusted.ITree.ITree.observe_cofix, stepMirState]

/-- Fuel-bounded run of `stepMirFn` through silent steps to a terminal outcome. -/
private def runN (body : CapturedMir) : Nat → MachineState → Option MirOutcome
  | 0, _ => none
  | fuel + 1, s =>
    match stepMirFn body s with
    | .tau (.running s') => runN body fuel s'
    | .ret o => some o
    | _ => none

private theorem runN_sound (body : CapturedMir) (fuel : Nat) :
    ∀ (s : MachineState) (o : MirOutcome),
      runN body fuel s = some o → Trusted.ITree.ReachesRet (mirTree body s) [] o := by
  induction fuel with
  | zero => intro s o h; simp [runN] at h
  | succ fuel ih =>
    intro s o h
    have hobs := mirTree_observe body s
    simp only [runN] at h
    generalize stepMirFn body s = node at h hobs
    cases node with
    | tau x =>
      cases x with
      | running s' =>
        obtain ⟨u, hr, hu⟩ := ih s' o h
        exact ⟨u, .tau hobs hr, hu⟩
      | halted _ => simp at h
      | faulted _ => simp at h
    | ret o' =>
      simp at h
      subst h
      exact ⟨mirTree body s, .refl _, hobs⟩
    | vis i k => simp at h

/-- The returned value of a normal outcome. -/
private def retVal : MirOutcome → Option Value
  | .normal (v, _) => some v
  | _ => none

private theorem runN_ret_sound (body : CapturedMir) (fuel : Nat) (v : Value)
    (h : (runN body fuel (initMachineState body [])).bind retVal = some v) :
    ∃ mem, Trusted.ITree.ReachesRet (mirCallTree body []) [] (.normal (v, mem)) := by
  cases hr : runN body fuel (initMachineState body []) with
  | none => rw [hr] at h; cases h
  | some o =>
    rw [hr] at h
    cases o with
    | normal vm =>
      rcases vm with ⟨v', mem⟩
      cases h
      exact ⟨mem, runN_sound body fuel _ _ hr⟩
    | _ => cases h

/-- A `Runtime(PostCleanup)` body with one block `stmts; return`. -/
private def witBody (dp : String) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (stmts : List Statement) : CapturedMir :=
  { defPath := dp
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls := decls
    basicBlocks := [
      { statements := stmts
        terminator := { kind := .return_, span := "bridge" }
        isCleanup := false }]
    fnAbi :=
      { args := []
        ret := { layout := primLayout 8 8, mode := .direct }
        conv := .rust
        canUnwind := false }
    layouts := layouts
    allocations := [] }

private def assign0 (rv : Rvalue) : Statement :=
  { kind := .assign { local_ := 0, projection := [] } rv, span := "bridge" }

/-- `fn size_of_p() -> usize { _0 = SizeOf(P); return }`. -/
def aSizeOfBody : CapturedMir :=
  witBody "bridge::size_of_p" aDecls aLayouts [assign0 (.nullaryOp .sizeOf aPTy)]

/-- `fn align_of_p() -> usize { _0 = AlignOf(P); return }`. -/
def aAlignOfBody : CapturedMir :=
  witBody "bridge::align_of_p" aDecls aLayouts [assign0 (.nullaryOp .alignOf aPTy)]

/-- `fn offset_of_outer_0_b() -> usize { _0 = OffsetOf((P, u16), [(0, 0), (0, 1)]); return }`. -/
def aOffsetOfBody : CapturedMir :=
  witBody "bridge::offset_of_outer_0_b" aDecls aLayouts
    [assign0 (.nullaryOp (.offsetOf [(0, 0), (0, 1)]) aOuterTy)]

/-- `bool`. -/
def aBoolTy : Ty := { kind := .bool, layoutIdx := 0 }

/-- `_0 : bool`. -/
def aBoolDecls : List LocalDecl := [{ mutability := .mut, ty := aBoolTy, debugName := none }]

/-- `fn ub_checks() -> bool { _0 = UbChecks(); return }`. -/
def aUbChecksBody : CapturedMir :=
  witBody "bridge::ub_checks" aBoolDecls aLayouts [assign0 (.nullaryOp .ubChecks aBoolTy)]

/-- `fn fn_ptr_addr() -> *const () { StorageLive(_1); _1 = callee as fn();
_0 = copy _1 as *const (); return }`. -/
def wFnPtrToPtrBody : CapturedMir :=
  witBody "bridge::fn_ptr_addr" wDecls wLayouts
    [{ kind := .storageLive 1, span := "bridge" },
     { kind := .assign { local_ := 1, projection := [] }
        (.cast (.pointerCoercion "ReifyFnPointer") wFnItem wFnPtrTy), span := "bridge" },
     assign0 (.cast .fnPtrToPtr wCopy1 wRawUnitTy)]

/-- **End-to-end (A1-A4)**: the bodies return the MiniRust layout facts of the witness types —
`size_of::<P>() = 8`, `align_of::<P>() = 4`, `offset_of!((P, u16), 0.b) = 4` — and
`ub_checks() = true`. -/
theorem wit_nullaryOp_bodies_reachRet :
    (∃ mem, Trusted.ITree.ReachesRet (mirCallTree aSizeOfBody []) []
      (.normal (.scalar ⟨8, 8⟩, mem))) ∧
    (∃ mem, Trusted.ITree.ReachesRet (mirCallTree aAlignOfBody []) []
      (.normal (.scalar ⟨4, 8⟩, mem))) ∧
    (∃ mem, Trusted.ITree.ReachesRet (mirCallTree aOffsetOfBody []) []
      (.normal (.scalar ⟨4, 8⟩, mem))) ∧
    (∃ mem, Trusted.ITree.ReachesRet (mirCallTree aUbChecksBody []) []
      (.normal (.scalar ⟨1, 1⟩, mem))) :=
  ⟨runN_ret_sound aSizeOfBody 4 _ rfl, runN_ret_sound aAlignOfBody 4 _ rfl,
    runN_ret_sound aOffsetOfBody 4 _ rfl, runN_ret_sound aUbChecksBody 4 _ rfl⟩

/-- **End-to-end (B4)**: the reify-then-`FnPtrToPtr` body returns the function pointer
`(65536, 0)` of `bridge::callee`. -/
theorem wit_fnPtrToPtr_body_reachRet :
    ∃ mem, Trusted.ITree.ReachesRet (mirCallTree wFnPtrToPtrBody []) []
      (.normal (.ptr ⟨65536, 0⟩ 8, mem)) :=
  runN_ret_sound wFnPtrToPtrBody 8 _ rfl

/-- Fuel-bounded run of `stepMirFn` through silent steps to a fault node. -/
private def runFaultN (body : CapturedMir) : Nat → MachineState → Option Trusted.Effect.FailureKind
  | 0, _ => none
  | fuel + 1, s =>
    match stepMirFn body s with
    | .tau (.running s') => runFaultN body fuel s'
    | .vis (.inl (.fail fk)) _ => some fk
    | _ => none

private theorem runFaultN_not_noUB (body : CapturedMir) (fuel : Nat) :
    ∀ (s : MachineState) (fk : Trusted.Effect.FailureKind),
      runFaultN body fuel s = some fk → ¬ MirNoUBTree (mirTree body s) := by
  induction fuel with
  | zero => intro s fk h; simp [runFaultN] at h
  | succ fuel ih =>
    intro s fk h hsafe
    have hobs := mirTree_observe body s
    simp only [runFaultN] at h
    generalize hstep : stepMirFn body s = node at h hobs
    cases node with
    | tau x =>
      cases x with
      | running s' =>
        have hsafe' : MirNoUBTree (mirTree body s') := by
          intro tr u hreach
          exact hsafe tr u (.tau hobs hreach)
        exact ih s' fk h hsafe'
      | halted _ => simp at h
      | faulted _ => simp at h
    | ret _ => simp at h
    | vis i k =>
      cases i with
      | inr _ => simp at h
      | inl e =>
        cases e with
        | fail fk' =>
          exact hsafe [] (mirTree body s) (.refl _)
            ⟨mirTree body s, _, _, .refl _, hobs, trivial⟩

/-- `fn fn_ptr_data() -> *const () { StorageLive(_1); StorageLive(_2); _2 = 7u32;
_1 = &raw const _2; _0 = copy _1 as *const (); return }` — casts a stack data pointer via
`CastKind.fnPtrToPtr`. -/
def wFnPtrToPtrDataBody : CapturedMir :=
  witBody "bridge::fn_ptr_data" wDecls wLayouts
    [{ kind := .storageLive 1, span := "bridge" },
     { kind := .storageLive 2, span := "bridge" },
     { kind := .assign { local_ := 2, projection := [] }
        (.use (.constant { ty := wU32Ty, val := .scalar (.int ⟨7, 4⟩) })), span := "bridge" },
     { kind := .assign { local_ := 1, projection := [] }
        (.rawPtr .not { local_ := 2, projection := [] }), span := "bridge" },
     assign0 (.cast .fnPtrToPtr wCopy1 wRawUnitTy)]

/-- **End-to-end (B4 negative UB)**: casting `&raw const x` via `CastKind.fnPtrToPtr` faults
with `.ub` inside `mirCallTree`, refuting `MirNoUBTree`. -/
theorem wit_fnPtrToPtr_data_body_not_noUB :
    runFaultN wFnPtrToPtrDataBody 8 (initMachineState wFnPtrToPtrDataBody []) = some .ub ∧
      ¬ MirNoUBTree (mirCallTree wFnPtrToPtrDataBody []) :=
  ⟨rfl, runFaultN_not_noUB wFnPtrToPtrDataBody 8 _ .ub rfl⟩

/-- **B4 (instantiating `FnPtrRel.fnFromPtrM_eq` and `fnPtrToPtr_data_pointer_divergence`)**:
single-application witnesses exercising both polymorphic theorems on `Mach` and `MachTB`. -/
theorem wit_fnFromPtrM_and_divergence :
    (fnFromPtrM (M := BM) wMach (.Ptr ⟨wFnThin, none⟩) = .ok wFn ∧
      fnFromPtrM (M := TBM) wMachTB (.Ptr ⟨wFnThinTB, none⟩) = .ok wFn) ∧
    (∃ (mem' : Memory),
      evalRvalue wLocalsB (.cast .fnPtrToPtr wCopy1 wRawUnitTy) mem' wDecls wLayouts = .ub ∧
      evalUnOpM (M := TBM) (.Cast (.Transmute (.Ptr (.Raw .None))))
          (.Ptr ⟨wDataThinTB, none⟩, .Ptr .FnPtr) (some wMachTB) =
        .ok (.Ptr ⟨wDataThinTB, none⟩, .Ptr (.Raw .None)) ∧
      fnFromPtrM (M := TBM) wMachTB (.Ptr ⟨wDataThinTB, none⟩) =
        .error (.ub "invalid pointer for function lookup")) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · obtain ⟨p, entry, f, hp, hL, hN, hEq⟩ := wit_FnPtrRel.1.fnFromPtrM_eq (by
      intro e₁ he₁ e₂ he₂ _
      simp [wMach] at he₁ he₂
      rcases he₁ with rfl; rcases he₂ with rfl; rfl)
    cases hp; cases hL; cases hN
    exact hEq
  · obtain ⟨p, entry, f, hp, hL, hN, hEq⟩ := wit_FnPtrRel.2.fnFromPtrM_eq (by
      intro e₁ he₁ e₂ he₂ _
      simp [wMachTB] at he₁ he₂
      rcases he₁ with rfl; rcases he₂ with rfl; rfl)
    cases hp; cases hL; cases hN
    exact hEq
  · obtain ⟨mem', e, _, hB, _⟩ := wit_trusted_borrowed_ub
    refine ⟨mem', fnPtrToPtr_data_pointer_divergence wLocalsB wLocalsB wCopy1 wRawUnitTy mem'
      wDecls wLayouts ⟨1, 0⟩ 8 e rfl hB wMachTB wDataThinTB (by decide) ?_⟩
    intro entry hentry
    simp [wMachTB, wFnThinTB] at hentry
    rcases hentry with rfl
    decide


end MiniRustSpec.Correspondence.NullaryFnPtrBridge
