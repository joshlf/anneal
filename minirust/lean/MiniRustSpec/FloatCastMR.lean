/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.Mir.IeeeFloatCast
import MiniRustSpec.Correspondence.TbWitness

/-!
# Float casts and IEEE-754 bit carriers at the `MiniRustSpec` boundary

Pinned MiniRust (`MiniRustSpec.Gen.Type`, `MiniRustSpec.Gen.CastOp`) has no
floating-point type and no float-cast operator, so `minimize`'s translation
(`MiniRustSpec.Correspondence.Translate`) must reject every MIR construct that
mentions `f16` / `f32` / `f64` / `f128`, while Anneal's trusted semantics
(`Trusted.Rustc.V2026_06_01.MirSemantics`, with the bit-level theory in
`Anneal.Mir.IeeeFloatCast`) executes `CastKind.{floatToInt, intToFloat,
floatToFloat}` and `CastKind.transmute` on `f32` / `f64`. This module pins down
that two-sided boundary and the part of float semantics that MiniRust *can*
represent: IEEE-754 bit patterns carried by `u32` / `i32` / `[u8; 4]`
(`f32::to_bits` / `f32::from_bits`) and `u64` / `i64` / `[u8; 8]`
(`f64::to_bits` / `f64::from_bits`).

1. **Fail-closed translation boundary (§1–§2).** For every `ft : FloatTy` and
   every layout index, `specOfRigidTy`, `intTypeOf`, `scalarTypeOf`,
   `arrayTypeOf`, `tupleTypeOf`, and `translateTy` reject `.float ft` (and
   `[ft; n]`); `operandType` / `translateOperand` reject float locals and float
   constants; `translateRvalue` returns `none` on all three float cast kinds for
   every operand and target type (so a float cast is never miscompiled into
   `CastOp::IntToInt` or `CastOp::Transmute`) and on every transmute *to* a
   float; `translateStatement` and `statementOk` reject every float-cast
   assignment; and `translateLocals` (the pinned translation's local-type map;
   there is no separate `localType`), `translateFn`, `inFragment`, and
   `progInFragment` reject every body with a float local. A negative control
   (`fc_translateRvalue_transmute_from_local`) shows why the local-level
   rejection is needed: `translateRvalue` alone type-erases `transmute::<f32, u32>`.
2. **Anneal's side of the boundary (§3, §7).** `evalRvalue` on the float cast kinds
   computes `evalFloatToIntSaturating` / `evalIntToFloatRoundTiesToEven` /
   `evalFloatToFloatRoundTiesToEven` on initialized `f32` / `f64` scalars,
   propagates `.ub` from an uninitialized source, and fails closed
   (`.unsupported`) on `f16` / `f128`; concrete `stepMirFn` / `runA` witnesses
   run the three cast kinds (and fault on `f16` / uninitialized sources) while
   `translateFn` rejects the same bodies.
3. **Bit-carrier transmutes (§4–§6).** For all bit patterns (signaling NaNs,
   `-0.0`, subnormals, and infinities included), Anneal's `evalByteCast`
   (`Rvalue.cast .transmute`) between `f32` and `u32` / `i32` / `[u8; 4]` and
   between `f64` and `u64` / `i64` / `[u8; 8]` preserves the bits exactly, so
   `from_bits ∘ to_bits` and `to_bits ∘ from_bits` are the identity. Anneal's
   little-endian `encodeLittleEndianBytes` is MiniRust's `Type.encode` image
   byte for byte (`fcByteToMR`), MiniRust's `Interp.transmute` and the
   polymorphic `Interp.transmuteM` (for *every* memory model, in particular
   `BasicMemory` and `TreeBorrowsMemory`) move the carriers between `u32` / `i32`
   and `u64` / `i64` unchanged, and Anneal's signed reading `intValueOfBits` is
   MiniRust's `intFromBits`. Size mismatches (`f32 ↔ u64`, `f64 ↔ u32`),
   uninitialized bytes, and pointer provenance are characterized on both sides:
   Anneal fails closed on a size mismatch where MiniRust's `CastOp::Transmute`
   raises UB; both reject exactly the byte sequences containing an uninitialized
   byte; and Anneal rejects provenance-carrying bytes at every float or integer
   type (the transmute of a pointer to `f64` / `u64` / `i64` is UB), where
   MiniRust's integer decoding silently drops the provenance.
4. **Bit-carrier bridges (§8–§10).** For every source bit pattern, the results of
   `evalFloatToIntSaturating`, `evalIntToFloatRoundTiesToEven`, and
   `evalFloatToFloatRoundTiesToEven` are in-range carriers whose MiniRust
   `Type.encode` / `Type.decode` / `transmute` images are exactly Anneal's
   bytes and denote the mathematically correct value (`floatToIntValue`).
   Symbolic multi-step `stepMirFn` executions (`runA`, kernel-computed with the
   bits left free) of `f32::from_bits(x).to_bits()`, `f32::from_bits(x) as i32`,
   `(x as f64).to_bits()`, and `(f32::from_bits(x) as f64).to_bits()` return
   exactly those carriers free of UB, and the translated carrier body
   `transmute::<u32, i32>` runs under `Interp.steps` (`BasicMemory`) and
   `Interp.stepsTB` (`TreeBorrowsMemory`) to Anneal's bytes.
5. **Strengthened fragment boundaries, layout-parametric transmutes, and signed
   two's-complement carriers (§11).** Characterizes raw pointers vs. safe
   references/boxes to floats (`translateTy`, `rawPtrPointeeOf`, `localDeclOk`),
   whole-function float-cast rejection without float locals (`translateFn`,
   `translateFnWithIntrinsics`, `inFragment`, `progInFragment` across entry and
   callees, witnessed by `fcConstF32CastBody`), layout-table-parametric scalar
   float transmutes (`fc_transmute_float_scalar_any_layouts`), the `f16`/`f128`
   transmute-ok vs. numeric-float-cast-unsupported dichotomy, and the signed
   two's-complement `encodeTwosComplement` ↔ `intValueOfBits` ↔ `intFromBits`
   bijection across `Type.encode` and `transmuteM` (`BasicMemory` + `TreeBorrowsMemory`).
6. **Symbolic MiniRust `[u8; 4]` & `[u8; 8]` byte-array transmutes (§12).**
   Proves symbolic `Type.encode` / `Type.decode` / `Type.encodeM` / `Type.decodeM`
   and bidirectional `transmute` + polymorphic `transmuteM` (`BasicMemory` and
   `TreeBorrowsMemory`) between `u32`/`i32` and `[u8; 4]` (`∀ bits < 2^32`) and
   between `u64`/`i64` and `[u8; 8]` (`∀ bits < 2^64`).
7. **Uninitialized-byte UB, polymorphic size-mismatch UB, and pointer-provenance
   transmute boundaries (§13).** Proves uninitialized-byte `Type.Union → Int`
   transmute UB across `Interp.transmute` and polymorphic `transmuteM`,
   polymorphic `evalCastOpM (.Transmute ...)` size-mismatch UB, and the full
   pointer-provenance transmute matrix across MiniRust (`ptr → u64/i64/[u8; 8]`
   provenance stripping vs. `ptr → *const T` provenance preservation vs.
   `u64 → *const T` provenance-free synthesis, over both `BasicMemory` and
   `TreeBorrowsMemory`) and Anneal (`ptr → [u8; 8]/i64` UB, `ptr → *const u8`
   provenance-preserving `decodePtrBytesNoForge`, `f64 → *const u8` no-forge
   scalar vs. `f64 → &u8` UB, and numeric float-cast `.unsupported`).
8. **Symbolic MiniRust machine executions and the remaining carrier bridges (§14).**
   The library's whole-execution simulation theorem `mirCall_ret` lifts Anneal's
   symbolic runs of the fragment carriers `x as i32` (`u32 → i32`) and
   `x as i64` (`u64 → i64`, under the 8-byte return place of `fcCtx8`) to
   MiniRust `Interp.steps` (`BasicMemory`) executions for *every* bit pattern
   (`fc_sym_mr_carrier_steps`, `fc_sym_mr_carrier64_steps`), ending with Anneal's
   little-endian bytes in the caller's return place; composed with the symbolic
   Anneal float pipelines (`fc_sym_e2e_from_bits_as_i32_machine`,
   `fc_sym_e2e_widen_bits_machine`). Symbolic multi-step bridges for
   `f64::from_bits(x) as i64`, narrowing `(f64::from_bits(x) as f32).to_bits()`, and
   exact `(x as f64).to_bits()` (the carrier decodes to exactly `x`), and the
   reverse `f16` / `f128` transmute directions complete the carrier matrix.
   (`TreeBorrowsMemory` machine runs remain concrete: the library has no
   `Interp.stepsTB` simulation theorem; `transmuteM` over `TreeBorrowsMemory` is
   symbolic throughout.)

Every public theorem is guarded by `#print axioms` at the end of the file.
-/

namespace MiniRustSpec.Correspondence.FloatCastMR

open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp
open MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.Witness
open MiniRustSpec.Correspondence.PointerWitness
open MiniRustSpec.Correspondence.RefWitness

/-! ## 0. Shared building blocks -/

/-- A primitive `n`-byte scalar layout (`FieldsShape::Primitive`, alignment `n`) whose backend
representation is the initialized primitive `p` over the full bit range. -/
def fcPrimLayout (n : Nat) (p : PrimitiveKind) : TypeLayout :=
  { size := { bytes := n }, align := { bytes := n },
    backendRepr := .scalar (.initialized p { start := 0, end_ := 2 ^ (8 * n) - 1 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- The `[u8; n]` layout: `n` one-byte elements at stride `1`, alignment `1`. -/
def fcByteArrayLayout (n : Nat) : TypeLayout :=
  { size := { bytes := n }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .array { bytes := 1 } n, variants := .single 0, isUninhabited := false }

/-- The layout table of every body in this module (`x86_64`: 64-bit pointers, little endian).
Index `0` is never used: `resolveTyWithLocalDecls` treats layout index `0` as unresolved, so
every type below carries its own non-zero index, which makes it a fixed point of
`resolveTyWithLocalDecls` for every list of local declarations. -/
def fcLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [
      fcPrimLayout 4 (.int 32 false),   -- 0: unused
      fcPrimLayout 4 (.float 32),       -- 1: f32
      fcPrimLayout 8 (.float 64),       -- 2: f64
      fcPrimLayout 4 (.int 32 false),   -- 3: u32
      fcPrimLayout 4 (.int 32 true),    -- 4: i32
      fcPrimLayout 8 (.int 64 false),   -- 5: u64
      fcPrimLayout 8 (.int 64 true),    -- 6: i64
      fcPrimLayout 1 (.int 8 false),    -- 7: u8
      fcByteArrayLayout 4,              -- 8: [u8; 4]
      fcByteArrayLayout 8,              -- 9: [u8; 8]
      fcPrimLayout 2 (.float 16),       -- 10: f16
      fcPrimLayout 16 (.float 128),     -- 11: f128
      fcPrimLayout 8 (.pointer 0),      -- 12: *const u8
      fcPrimLayout 2 (.int 16 false),   -- 13: u16
      fcPrimLayout 16 (.int 128 false)] } -- 14: u128

/-- `f32`. -/
def fcF32Ty : Ty := { kind := .float .f32, layoutIdx := 1 }
/-- `f64`. -/
def fcF64Ty : Ty := { kind := .float .f64, layoutIdx := 2 }
/-- `u32`. -/
def fcU32Ty : Ty := { kind := .uint .u32, layoutIdx := 3 }
/-- `i32`. -/
def fcI32Ty : Ty := { kind := .int .i32, layoutIdx := 4 }
/-- `u64`. -/
def fcU64Ty : Ty := { kind := .uint .u64, layoutIdx := 5 }
/-- `i64`. -/
def fcI64Ty : Ty := { kind := .int .i64, layoutIdx := 6 }
/-- `u8`. -/
def fcU8Ty : Ty := { kind := .uint .u8, layoutIdx := 7 }
/-- `[u8; 4]`. -/
def fcBytes4Ty : Ty := { kind := .array (.uint .u8) 4, layoutIdx := 8 }
/-- `[u8; 8]`. -/
def fcBytes8Ty : Ty := { kind := .array (.uint .u8) 8, layoutIdx := 9 }
/-- `f16` (no modeled IEEE-754 format in Anneal). -/
def fcF16Ty : Ty := { kind := .float .f16, layoutIdx := 10 }
/-- `f128` (no modeled IEEE-754 format in Anneal). -/
def fcF128Ty : Ty := { kind := .float .f128, layoutIdx := 11 }

/-- `*const u8` (a thin raw pointer). -/
def fcRawPtrU8Ty : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 12 }

/-- `*const u32` (a thin raw pointer; same pointer layout entry as `fcRawPtrU8Ty`). -/
def fcRawPtrU32Ty : Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 12 }

/-- A mutable local of type `ty`. -/
def fcDecl (ty : Ty) : LocalDecl := { mutability := .mut, ty := ty, debugName := none }

/-- MiniRust `u32`. -/
def fcU32It : Gen.IntType := ⟨.Unsigned, ⟨4⟩⟩
/-- MiniRust `i32`. -/
def fcI32It : Gen.IntType := ⟨.Signed, ⟨4⟩⟩
/-- MiniRust `u64`. -/
def fcU64It : Gen.IntType := ⟨.Unsigned, ⟨8⟩⟩
/-- MiniRust `i64`. -/
def fcI64It : Gen.IntType := ⟨.Signed, ⟨8⟩⟩
/-- MiniRust `u8`. -/
def fcU8It : Gen.IntType := ⟨.Unsigned, ⟨1⟩⟩

/-- Anneal's abstract byte as a MiniRust abstract byte with its provenance erased: `uninit` is
`Uninit`, and `init b _` is the provenance-free `Init b None`. On provenance-free bytes (every
byte of an integer or float encoding) this is a bijection onto provenance-free MiniRust bytes. -/
def fcByteToMR : MirSemantics.AbstractByte → Byte
  | .uninit => .Uninit
  | .init b _ => .Init b none

/-- The `[u8; n]` element values of the `n` little-endian bytes of `bits`. -/
def fcLeByteVals (bits : Nat) : Nat → List Value
  | 0 => []
  | n + 1 => .scalar ⟨bits % 256, 1⟩ :: fcLeByteVals (bits / 256) n

/-- The MiniRust `[u8; n]` element values of the `n` little-endian bytes of `bits`. -/
def fcLeByteValsMR (bits : Nat) : Nat → List Val
  | 0 => []
  | n + 1 => .Int ((bits % 256 : Nat) : Int) :: fcLeByteValsMR (bits / 256) n

/-- The little-endian number denoted by a list of `[u8; n]` element values whose elements are
all one-byte scalars (`none` otherwise). -/
def fcLeValueOfByteVals : List Value → Option Nat
  | [] => some 0
  | .scalar ⟨b, 1⟩ :: rest => (fcLeValueOfByteVals rest).map (fun hi => b + 256 * hi)
  | _ :: _ => none

/-! ## 1. Types and operands: MiniRust has no float type -/

/-- `minimize`'s integer type translation rejects every float type. -/
theorem fc_intTyBytes_float (ft : FloatTy) : intTyBytes (.float ft) = none := rfl

theorem fc_intTypeOf_float (ft : FloatTy) (idx : Nat) : intTypeOf ⟨.float ft, idx⟩ = none := rfl

theorem fc_scalarTypeOf_float (ft : FloatTy) (idx : Nat) :
    scalarTypeOf ⟨.float ft, idx⟩ = none := rfl

theorem fc_arrayTypeOf_float (ft : FloatTy) (idx : Nat) :
    arrayTypeOf ⟨.float ft, idx⟩ = none := rfl

/-- Arrays of floats (`[f32; n]`, `[f64; n]`, ...) have no MiniRust element type either. -/
theorem fc_arrayTypeOf_floatArray (ft : FloatTy) (n idx : Nat) :
    arrayTypeOf ⟨.array (.float ft) n, idx⟩ = none := rfl

/-- `specOfRigidTy` (tuple / struct field layouts) has no float leaf, for every layout table and
layout index. -/
theorem fc_specOfRigidTy_float (layouts : LayoutTable) (ft : FloatTy) (idx : Nat) :
    specOfRigidTy layouts (.float ft) idx = none := by
  simp [specOfRigidTy]

theorem fc_tupleTypeOf_float (layouts : LayoutTable) (ft : FloatTy) (idx : Nat) :
    tupleTypeOf layouts ⟨.float ft, idx⟩ = none := rfl

/-- **`translateTy` rejects every float type** (`f16`, `f32`, `f64`, `f128`), for every layout
table and layout index. -/
theorem fc_translateTy_float (layouts : LayoutTable) (ft : FloatTy) (idx : Nat) :
    translateTy layouts ⟨.float ft, idx⟩ = none := rfl

/-- `translateTy` rejects every float array type `[ft; n]`. -/
theorem fc_translateTy_floatArray (layouts : LayoutTable) (ft : FloatTy) (n idx : Nat) :
    translateTy layouts ⟨.array (.float ft) n, idx⟩ = none := rfl

/-- A float local has no MiniRust operand type. -/
theorem fc_operandType_copy_float (layouts : LayoutTable) (decls : List LocalDecl) (j : Nat)
    (m : MirAst.Mutability) (ft : FloatTy) (idx : Nat) (name : Option String)
    (hd : decls[j]? = some { mutability := m, ty := ⟨.float ft, idx⟩, debugName := name }) :
    operandType layouts decls (.copy ⟨j, []⟩) = none := by
  simp only [operandType, hd]
  rfl

/-- A float constant has no MiniRust operand type. -/
theorem fc_operandType_const_float (layouts : LayoutTable) (decls : List LocalDecl)
    (ft : FloatTy) (idx : Nat) (val : ConstValue) :
    operandType layouts decls (.constant ⟨⟨.float ft, idx⟩, val⟩) = none := rfl

/-- A float constant has no MiniRust translation (its value has no MiniRust integer type). -/
theorem fc_translateOperand_const_float (decls : List LocalDecl) (ft : FloatTy) (idx : Nat)
    (val : ConstValue) :
    translateOperand decls (.constant ⟨⟨.float ft, idx⟩, val⟩) = none := by
  unfold translateOperand
  cases val with
  | scalar s =>
    cases s with
    | int sc => rfl
    | _ => rfl
  | _ => rfl

/-- **`translateLocals` rejects every local list containing a float local.** -/
theorem fc_translateLocals_eq_none_of_float (layouts : LayoutTable) :
    ∀ (i : Nat) (decls : List LocalDecl),
      (∃ d ∈ decls, ∃ (ft : FloatTy) (idx : Nat), d.ty = ⟨.float ft, idx⟩) →
      translateLocals layouts i decls = none := by
  intro i decls h
  induction decls generalizing i with
  | nil => obtain ⟨d, hd, _⟩ := h; simp at hd
  | cons d ds ih =>
    obtain ⟨d', hd', ft, idx, hty⟩ := h
    rcases List.mem_cons.mp hd' with rfl | hmem
    · simp [translateLocals, hty, fc_translateTy_float]
    · have := ih (i + 1) ⟨d', hmem, ft, idx, hty⟩
      simp only [translateLocals]
      cases translateTy layouts d.ty with
      | none => rfl
      | some ty => simp [this]

/-- **`translateFn` rejects every body with a float local** (argument, return place, or
temporary). -/
theorem fc_translateFn_eq_none_of_float (body : CapturedMir)
    (h : ∃ d ∈ body.localDecls, ∃ (ft : FloatTy) (idx : Nat), d.ty = ⟨.float ft, idx⟩) :
    translateFn body = none := by
  have hl := fc_translateLocals_eq_none_of_float body.layouts 0 body.localDecls h
  unfold translateFn
  cases translateCallConv body.fnAbi.conv with
  | none => rfl
  | some c => simp [hl]

/-- **`inFragment` rejects every body with a float local.** -/
theorem fc_inFragment_eq_false_of_float (body : CapturedMir)
    (h : ∃ d ∈ body.localDecls, ∃ (ft : FloatTy) (idx : Nat), d.ty = ⟨.float ft, idx⟩) :
    inFragment body = false := by
  simp [inFragment, fc_translateFn_eq_none_of_float body h]

/-- **`progInFragment` rejects every program whose entry has a float local**: every body of a
fragment program must have scalar-typed locals only (`bodyInProgFragment`). -/
theorem fc_progInFragment_eq_false_of_float (entry : CapturedMir) (callees : List CapturedMir)
    (h : ∃ d ∈ entry.localDecls, ∃ (ft : FloatTy) (idx : Nat), d.ty = ⟨.float ft, idx⟩) :
    progInFragment entry callees = false := by
  obtain ⟨d, hd, ft, idx, hty⟩ := h
  have hbody : bodyInProgFragment (fnNameMap entry callees) callees entry = false := by
    have hall : entry.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = false := by
      cases h : entry.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) with
      | false => rfl
      | true =>
        have := List.all_eq_true.mp h d hd
        simp [hty, fc_scalarTypeOf_float] at this
    simp [bodyInProgFragment, hall]
  simp [progInFragment, hbody]

/-! ## 2. Rvalues and statements: MiniRust has no float cast operator -/

/-- The three numeric float cast kinds (`CastKind::{FloatToInt, IntToFloat, FloatToFloat}`). -/
def fcIsFloatCastKind : CastKind → Bool
  | .floatToInt | .intToFloat | .floatToFloat => true
  | _ => false

theorem fc_translateRvalue_floatToInt (layouts : LayoutTable) (decls : List LocalDecl)
    (targetTy : Option Ty) (op : Operand) (ty : Ty) :
    translateRvalue layouts decls targetTy (.cast .floatToInt op ty) = none := rfl

theorem fc_translateRvalue_intToFloat (layouts : LayoutTable) (decls : List LocalDecl)
    (targetTy : Option Ty) (op : Operand) (ty : Ty) :
    translateRvalue layouts decls targetTy (.cast .intToFloat op ty) = none := rfl

theorem fc_translateRvalue_floatToFloat (layouts : LayoutTable) (decls : List LocalDecl)
    (targetTy : Option Ty) (op : Operand) (ty : Ty) :
    translateRvalue layouts decls targetTy (.cast .floatToFloat op ty) = none := rfl

/-- **`translateRvalue` rejects every float cast**, for every layout table, local list,
destination type, operand, and cast type. -/
theorem fc_translateRvalue_float_cast (layouts : LayoutTable) (decls : List LocalDecl)
    (targetTy : Option Ty) (k : CastKind) (hk : fcIsFloatCastKind k = true) (op : Operand)
    (ty : Ty) :
    translateRvalue layouts decls targetTy (.cast k op ty) = none := by
  cases k <;> first | rfl | simp [fcIsFloatCastKind] at hk

/-- **A float cast is never miscompiled** into MiniRust's `CastOp::IntToInt` or
`CastOp::Transmute` (nor into any other expression). -/
theorem fc_translateRvalue_float_cast_never_intToInt_or_transmute (layouts : LayoutTable)
    (decls : List LocalDecl) (targetTy : Option Ty) (k : CastKind)
    (hk : fcIsFloatCastKind k = true) (op : Operand) (ty : Ty) :
    (∀ (it : Gen.IntType) (e : Gen.ValueExpr),
      translateRvalue layouts decls targetTy (.cast k op ty) ≠ some (.UnOp (.Cast (.IntToInt it)) e)) ∧
    (∀ (T : Gen.Type) (e : Gen.ValueExpr),
      translateRvalue layouts decls targetTy (.cast k op ty) ≠ some (.UnOp (.Cast (.Transmute T)) e)) ∧
    (∀ e : Gen.ValueExpr, translateRvalue layouts decls targetTy (.cast k op ty) ≠ some e) := by
  rw [fc_translateRvalue_float_cast layouts decls targetTy k hk op ty]
  refine ⟨fun _ _ h => ?_, fun _ _ h => ?_, fun _ h => ?_⟩ <;> cases h

/-- `translateRvalue` rejects every transmute *to* a float type. -/
theorem fc_translateRvalue_transmute_to_float (layouts : LayoutTable) (decls : List LocalDecl)
    (targetTy : Option Ty) (op : Operand) (ft : FloatTy) (idx : Nat) :
    translateRvalue layouts decls targetTy (.cast .transmute op ⟨.float ft, idx⟩) = none := by
  simp only [translateRvalue]
  cases translateOperand decls op <;> rfl

/-- Negative control: `translateRvalue` alone does *not* reject `transmute::<f32, u32>(x)`,
because `minimize`'s operand translation is type-erased (`copy _j` is `Load(_j)` whatever the
type of `_j`). The rejection of `f32::to_bits` happens one level up, at the float local itself
(`fc_translateLocals_eq_none_of_float`, `fc_translateFn_eq_none_of_float`). -/
theorem fc_translateRvalue_transmute_from_local (layouts : LayoutTable) (decls : List LocalDecl)
    (targetTy : Option Ty) (j : Nat) :
    translateRvalue layouts decls targetTy (.cast .transmute (.copy ⟨j, []⟩) fcU32Ty) =
      some (.UnOp (.Cast (.Transmute (.Int fcU32It))) (.Load (.Local (localName j)))) := rfl

/-- **`translateStatement` rejects every assignment of a float cast**, to every place. -/
theorem fc_translateStatement_float_cast (decls : List LocalDecl) (dst : Place) (k : CastKind)
    (hk : fcIsFloatCastKind k = true) (op : Operand) (ty : Ty) (span : String)
    (layouts : LayoutTable) :
    translateStatement decls ⟨.assign dst (.cast k op ty), span⟩ layouts = none := by
  simp only [translateStatement, copyRv]
  cases translatePlace decls dst with
  | none => rfl
  | some pe =>
    simp [fc_translateRvalue_float_cast layouts decls (placeMirTy decls dst) k hk (copyOp op) ty]

/-- `translateStatement` rejects every assignment of a transmute to a float type. -/
theorem fc_translateStatement_transmute_to_float (decls : List LocalDecl) (dst : Place)
    (op : Operand) (ft : FloatTy) (idx : Nat) (span : String) (layouts : LayoutTable) :
    translateStatement decls ⟨.assign dst (.cast .transmute op ⟨.float ft, idx⟩), span⟩ layouts =
      none := by
  simp only [translateStatement, copyRv]
  cases translatePlace decls dst with
  | none => rfl
  | some pe =>
    simp [fc_translateRvalue_transmute_to_float layouts decls (placeMirTy decls dst) (copyOp op)]

/-! ## 3. Anneal's side: `evalRvalue` runs float casts on `f32` / `f64` -/

/-- `evalRvalue (.cast .floatToInt op dstTy)` on an initialized `f32` / `f64` operand computes
`evalFloatToIntSaturating` at the operand's static type. -/
theorem fc_evalRvalue_floatToInt_eq
    {locals locals' : List LocalSlot} {op : Operand} {dstTy srcTy : Ty} {mem : Memory}
    {decls : List LocalDecl} {layouts : LayoutTable} {sc : ScalarInt}
    {fmt : IeeeFormat} {tgt : FloatIntTarget}
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
        mem.callStack = .ok (.scalar sc) locals')
    (hSrc : operandTy decls layouts op = .some srcTy)
    (hFmt : ieeeFormatOfTy? srcTy = .some fmt)
    (hTgt : floatIntTargetOfTy? dstTy = .some tgt)
    (hSz : sc.sizeBytes = fmt.byteWidth) :
    evalRvalue locals (.cast .floatToInt op dstTy) mem decls layouts =
      .ok (.scalar (evalFloatToIntSaturating fmt sc.bits tgt (floatPtrWidthOfLayouts layouts)))
        locals' mem := by
  show evalFloatCastRvalue locals .floatToInt op dstTy mem decls layouts = _
  unfold evalFloatCastRvalue
  rw [hOp]
  simp only [evalFloatCast, hSrc, hFmt, hTgt, hSz, Nat.beq_refl]

/-- `evalRvalue (.cast .intToFloat op dstTy)` on an initialized integer operand computes
`evalIntToFloatRoundTiesToEven`. -/
theorem fc_evalRvalue_intToFloat_eq
    {locals locals' : List LocalSlot} {op : Operand} {dstTy srcTy : Ty} {mem : Memory}
    {decls : List LocalDecl} {layouts : LayoutTable} {sc : ScalarInt}
    {fmt : IeeeFormat} {src : FloatIntTarget}
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
        mem.callStack = .ok (.scalar sc) locals')
    (hSrc : operandTy decls layouts op = .some srcTy)
    (hInt : floatIntTargetOfTy? srcTy = .some src)
    (hFmt : ieeeFormatOfTy? dstTy = .some fmt)
    (hSz : sc.sizeBytes * 8 = src.bitWidth (floatPtrWidthOfLayouts layouts)) :
    evalRvalue locals (.cast .intToFloat op dstTy) mem decls layouts =
      .ok (.scalar ⟨evalIntToFloatRoundTiesToEven src.isSigned
          (src.bitWidth (floatPtrWidthOfLayouts layouts)) sc.bits fmt, fmt.byteWidth⟩)
        locals' mem := by
  show evalFloatCastRvalue locals .intToFloat op dstTy mem decls layouts = _
  unfold evalFloatCastRvalue
  rw [hOp]
  simp only [evalFloatCast, hSrc, hFmt, hInt, Nat.mul_eq, hSz, Nat.beq_refl]

/-- `evalRvalue (.cast .floatToFloat op dstTy)` between `f32` / `f64` computes
`evalFloatToFloatRoundTiesToEven`. -/
theorem fc_evalRvalue_floatToFloat_eq
    {locals locals' : List LocalSlot} {op : Operand} {dstTy srcTy : Ty} {mem : Memory}
    {decls : List LocalDecl} {layouts : LayoutTable} {sc : ScalarInt}
    {src dst : IeeeFormat}
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
        mem.callStack = .ok (.scalar sc) locals')
    (hSrc : operandTy decls layouts op = .some srcTy)
    (hSrcFmt : ieeeFormatOfTy? srcTy = .some src)
    (hDstFmt : ieeeFormatOfTy? dstTy = .some dst)
    (hSz : sc.sizeBytes = src.byteWidth) :
    evalRvalue locals (.cast .floatToFloat op dstTy) mem decls layouts =
      .ok (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)
        locals' mem := by
  show evalFloatCastRvalue locals .floatToFloat op dstTy mem decls layouts = _
  unfold evalFloatCastRvalue
  rw [hOp]
  simp only [evalFloatCast, hSrc, hSrcFmt, hDstFmt, hSz, Nat.beq_refl]

/-- **Uninitialized / dead / moved-out sources are UB** for every float cast kind: whenever the
operand read faults with UB, so does the cast. -/
theorem fc_evalRvalue_float_cast_ub
    {locals : List LocalSlot} {op : Operand} {dstTy : Ty} {mem : Memory}
    {decls : List LocalDecl} {layouts : LayoutTable} (k : CastKind)
    (hk : fcIsFloatCastKind k = true)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
        mem.callStack = .ub) :
    evalRvalue locals (.cast k op dstTy) mem decls layouts = .ub := by
  cases k <;> simp [fcIsFloatCastKind] at hk <;>
    · show evalFloatCastRvalue locals _ op dstTy mem decls layouts = _
      unfold evalFloatCastRvalue
      rw [hOp]

/-- **`f16` / `f128` fail closed**: when the float side of a cast has no modeled IEEE-754 format
(`ieeeFormatOfTy? = none`, i.e. `f16`, `f128`, or a non-float type), `evalRvalue` returns
`.unsupported` on every initialized operand, so Anneal never certifies such a cast. -/
theorem fc_evalRvalue_float_cast_unsupported_of_no_format
    {locals locals' : List LocalSlot} {op : Operand} {dstTy srcTy : Ty} {mem : Memory}
    {decls : List LocalDecl} {layouts : LayoutTable} {v : Value}
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
        mem.callStack = .ok v locals')
    (hSrc : operandTy decls layouts op = .some srcTy) :
    (ieeeFormatOfTy? srcTy = .none →
      evalRvalue locals (.cast .floatToInt op dstTy) mem decls layouts = .unsupported ∧
      evalRvalue locals (.cast .floatToFloat op dstTy) mem decls layouts = .unsupported) ∧
    (ieeeFormatOfTy? dstTy = .none →
      evalRvalue locals (.cast .intToFloat op dstTy) mem decls layouts = .unsupported ∧
      evalRvalue locals (.cast .floatToFloat op dstTy) mem decls layouts = .unsupported) := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩ <;>
  · show evalFloatCastRvalue locals _ op dstTy mem decls layouts = _
    unfold evalFloatCastRvalue
    rw [hOp]
    cases v <;> simp [evalFloatCast, hSrc, h] <;> split <;> simp_all

theorem fc_ieeeFormatOfTy_f16 : ieeeFormatOfTy? fcF16Ty = none := rfl
theorem fc_ieeeFormatOfTy_f128 : ieeeFormatOfTy? fcF128Ty = none := rfl
theorem fc_ieeeFormatOfTy_f32 : ieeeFormatOfTy? fcF32Ty = some .binary32 := rfl
theorem fc_ieeeFormatOfTy_f64 : ieeeFormatOfTy? fcF64Ty = some .binary64 := rfl

/-! ## 4. Little-endian bytes: Anneal's encoding is MiniRust's -/

theorem fc_uint8_ofNat_mod (n : Nat) : UInt8.ofNat (n % 256) = UInt8.ofNat n := by
  apply UInt8.toNat_inj.mp
  simp

theorem fc_uint8_ofNat_toNat (n : Nat) : (UInt8.ofNat n).toBitVec.toNat = n % 256 := by
  show (UInt8.ofNat n).toNat = n % 256
  simp

/-- **Anneal's `encodeLittleEndianBytes` is MiniRust's `Type.encode` byte image** (`scalarBytes`),
byte for byte, for every bit pattern, width, signedness, and provenance (which `fcByteToMR`
erases; integer and float encodings carry none). -/
theorem fc_map_encodeLittleEndianBytes (s : Signedness) (prov : Option (Nat × Nat)) :
    ∀ (n bits : Nat), (encodeLittleEndianBytes bits n prov).map fcByteToMR = scalarBytes ⟨s, ⟨n⟩⟩ bits
  | 0, _ => rfl
  | n + 1, bits => by
    have ih := fc_map_encodeLittleEndianBytes s prov n (bits / 256)
    simp only [scalarBytes] at ih ⊢
    show fcByteToMR (.init (UInt8.ofNat bits) prov) ::
        (encodeLittleEndianBytes (bits / 256) n prov).map fcByteToMR =
      (UInt8.ofNat (bits % 256) :: leBytes (bits / 256) n).map (fun b => Gen.AbstractByte.Init b none)
    rw [ih, fc_uint8_ofNat_mod]
    rfl

/-- `Trusted.Sequence.length` of `encodeLittleEndianBytes bits n prov` is `n`. -/
theorem fc_seqLength_encodeLittleEndianBytes (prov : Option (Nat × Nat)) :
    ∀ (n bits : Nat), Trusted.Sequence.length (encodeLittleEndianBytes bits n prov) = n
  | 0, _ => rfl
  | n + 1, bits => by
    show Nat.succ (Trusted.Sequence.length (encodeLittleEndianBytes (bits / 256) n prov)) = n + 1
    rw [fc_seqLength_encodeLittleEndianBytes prov n (bits / 256)]

theorem fc_length_encodeLittleEndianBytes (prov : Option (Nat × Nat)) :
    ∀ (n bits : Nat), (encodeLittleEndianBytes bits n prov).length = n
  | 0, _ => rfl
  | n + 1, bits => by
    show (encodeLittleEndianBytes (bits / 256) n prov).length + 1 = n + 1
    rw [fc_length_encodeLittleEndianBytes prov n (bits / 256)]

theorem fc_mergeByteProvenance_none_right (p : Option (Nat × Nat)) :
    mergeByteProvenance p none = p := by cases p <;> rfl

theorem fc_mergeByteProvenance_self (p : Option (Nat × Nat)) :
    mergeByteProvenance p p = p := by cases p <;> rfl

/-- Anneal's little-endian decoder inverts its encoder on every in-range bit pattern, returning
the encoding's provenance. -/
theorem fc_decodeLittleEndianBytes_encode (prov : Option (Nat × Nat)) :
    ∀ (n bits : Nat), bits < 256 ^ (n + 1) →
      decodeLittleEndianBytes (encodeLittleEndianBytes bits (n + 1) prov) = some (bits, prov)
  | 0, bits, h => by
    show (some (Nat.add (UInt8.ofNat bits).toBitVec.toNat (Nat.mul 256 0),
      mergeByteProvenance prov none)) = some (bits, prov)
    rw [fc_uint8_ofNat_toNat, fc_mergeByteProvenance_none_right,
      Nat.mod_eq_of_lt (by simpa using h)]
    rfl
  | n + 1, bits, h => by
    have hdiv : bits / 256 < 256 ^ (n + 1) := by
      rw [Nat.pow_succ] at h
      exact (Nat.div_lt_iff_lt_mul (by decide)).mpr h
    have ih := fc_decodeLittleEndianBytes_encode prov n (bits / 256) hdiv
    show (match decodeLittleEndianBytes (encodeLittleEndianBytes (bits / 256) (n + 1) prov) with
      | some (highBits, restProv) =>
        some (Nat.add (UInt8.ofNat bits).toBitVec.toNat (Nat.mul 256 highBits),
          mergeByteProvenance prov restProv)
      | none => none) = some (bits, prov)
    rw [ih]
    dsimp only
    rw [fc_uint8_ofNat_toNat, fc_mergeByteProvenance_self]
    simp only [Option.some.injEq, Prod.mk.injEq, and_true]
    exact Nat.mod_add_div bits 256

/-- Anneal's scalar decoder inverts the little-endian encoder on every in-range bit pattern (for
both signedness flags). -/
theorem fc_decodeScalarBytes_encode (prov : Option (Nat × Nat)) (signed : Bool) (n bits : Nat)
    (h : bits < 256 ^ (n + 1)) :
    decodeScalarBytes (encodeLittleEndianBytes bits (n + 1) prov) signed =
      some (⟨bits, n + 1⟩, prov) := by
  unfold decodeScalarBytes
  rw [fc_seqLength_encodeLittleEndianBytes, fc_decodeLittleEndianBytes_encode prov n bits h]
  rfl

theorem fc_abstractBytesHaveProv_encode_none :
    ∀ (n bits : Nat), abstractBytesHaveProv (encodeLittleEndianBytes bits n none) = false
  | 0, _ => rfl
  | n + 1, bits => fc_abstractBytesHaveProv_encode_none n (bits / 256)

theorem fc_abstractBytesHaveProv_encode_some (p : Nat × Nat) (n bits : Nat) :
    abstractBytesHaveProv (encodeLittleEndianBytes bits (n + 1) (some p)) = true := rfl

/-- **Uninitialized bytes, Anneal side**: the little-endian decoder fails exactly on byte
sequences containing an uninitialized byte. -/
theorem fc_decodeLittleEndianBytes_eq_none_iff :
    ∀ bs : List MirSemantics.AbstractByte,
      decodeLittleEndianBytes bs = none ↔ MirSemantics.AbstractByte.uninit ∈ bs
  | [] => by simp [decodeLittleEndianBytes]
  | .uninit :: _ => by simp [decodeLittleEndianBytes]
  | .init b p :: rest => by
    have ih := fc_decodeLittleEndianBytes_eq_none_iff rest
    simp only [decodeLittleEndianBytes, List.mem_cons, reduceCtorEq, false_or]
    cases h : decodeLittleEndianBytes rest with
    | none => simp_all
    | some r => simp_all

/-- **Uninitialized bytes, MiniRust side**: `AbstractByte::data` fails (`try_map` returns `None`)
on the MiniRust image of exactly the same byte sequences. -/
theorem fc_mapM_data_eq_none_iff :
    ∀ bs : List MirSemantics.AbstractByte,
      (bs.map fcByteToMR).mapM AbstractByte.data = none ↔ MirSemantics.AbstractByte.uninit ∈ bs
  | [] => by simp
  | .uninit :: _ => by simp [fcByteToMR, AbstractByte.data]
  | .init b p :: rest => by
    have ih := fc_mapM_data_eq_none_iff rest
    simp only [List.map_cons, fcByteToMR, List.mapM_cons, AbstractByte.data, List.mem_cons,
      reduceCtorEq, false_or]
    cases h : (rest.map fcByteToMR).mapM AbstractByte.data with
    | none => simp_all
    | some r => simp_all

/-- **Uninitialized bytes, both sides**: Anneal's little-endian decoder fails exactly when
MiniRust's integer decoding of the same bytes (`Type.decode (.Int it)`, which a typed load turns
into UB) yields `None`. -/
theorem fc_decode_int_none_iff (it : Gen.IntType) (bs : List MirSemantics.AbstractByte)
    (hlen : bs.length = it.size.bytes) :
    Type.decode (.Int it) (bs.map fcByteToMR) = .ok none ↔ decodeLittleEndianBytes bs = none := by
  rw [fc_decodeLittleEndianBytes_eq_none_iff, ← fc_mapM_data_eq_none_iff]
  obtain ⟨signed, size⟩ := it
  simp only [Type.decode, Type.decodeInt, List.length_map, hlen, ne_eq, not_true_eq_false,
    ↓reduceIte]
  cases (bs.map fcByteToMR).mapM AbstractByte.data <;> simp [pure, Except.pure]

/-! ## 5. Anneal's `transmute` between `f32` / `f64` and their bit carriers -/

/-- Step-level reduction of `evalByteCast` (`Rvalue.cast .transmute`) once the operand value, the
operand type, and the byte sizes of both types are known (any layout table). -/
theorem fc_evalByteCast_eq
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory) (decls : List LocalDecl)
    (layouts : LayoutTable) (v : Value) (srcTy dstTy : Ty) (srcSize dstSize : Nat)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok v locals')
    (h_dst_sz : tyByteSize decls layouts (resolveTyWithLocalDecls decls layouts dstTy) =
      some dstSize)
    (h_ty : operandTy decls layouts op = some srcTy)
    (h_src_sz : tyByteSize decls layouts (resolveTyWithLocalDecls decls layouts srcTy) =
      some srcSize) :
    evalByteCast locals op dstTy mem decls layouts =
      match Nat.beq srcSize dstSize with
      | false => .unsupported
      | true =>
        match encodeByteCastSourceBytes layouts (resolveTyWithLocalDecls decls layouts srcTy) v with
        | .none => .ub
        | .some bs =>
          match Nat.beq (Trusted.Sequence.length bs) dstSize with
          | false => .ub
          | true =>
            match decodeTypedValueFromBytes defaultCodecFuel layouts
                (resolveTyWithLocalDecls decls layouts dstTy) bs with
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

/-- `evalByteCast` on a same-size transmute whose source encoding succeeds with `bs` of the
destination length is the provenance-faithful `decodeTypedValueFromBytes` of `bs`. -/
theorem fc_evalByteCast_of_encode
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory) (decls : List LocalDecl)
    (layouts : LayoutTable) (v : Value) (srcTy dstTy : Ty) (size : Nat)
    (bs : List MirSemantics.AbstractByte)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok v locals')
    (h_dst_sz : tyByteSize decls layouts (resolveTyWithLocalDecls decls layouts dstTy) = some size)
    (h_ty : operandTy decls layouts op = some srcTy)
    (h_src_sz : tyByteSize decls layouts (resolveTyWithLocalDecls decls layouts srcTy) = some size)
    (h_enc : encodeByteCastSourceBytes layouts (resolveTyWithLocalDecls decls layouts srcTy) v =
      some bs)
    (h_len : Trusted.Sequence.length bs = size) :
    evalByteCast locals op dstTy mem decls layouts =
      match decodeTypedValueFromBytes defaultCodecFuel layouts
          (resolveTyWithLocalDecls decls layouts dstTy) bs with
      | .some v' => .ok v' locals' mem
      | .none => .ub := by
  have h_len_beq : Nat.beq (Trusted.Sequence.length bs) size = true := by
    rw [h_len]; exact Nat.beq_refl _
  rw [fc_evalByteCast_eq locals locals' op mem decls layouts v srcTy dstTy size size
    h_op h_dst_sz h_ty h_src_sz, Nat.beq_refl, h_enc]
  dsimp only
  rw [h_len_beq]

/-- `evalByteCast` fails closed (`.unsupported`) on a size mismatch. -/
theorem fc_evalByteCast_size_mismatch
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory) (decls : List LocalDecl)
    (layouts : LayoutTable) (v : Value) (srcTy dstTy : Ty) (srcSize dstSize : Nat)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok v locals')
    (h_dst_sz : tyByteSize decls layouts (resolveTyWithLocalDecls decls layouts dstTy) =
      some dstSize)
    (h_ty : operandTy decls layouts op = some srcTy)
    (h_src_sz : tyByteSize decls layouts (resolveTyWithLocalDecls decls layouts srcTy) =
      some srcSize)
    (h_ne : srcSize ≠ dstSize) :
    evalByteCast locals op dstTy mem decls layouts = .unsupported := by
  have h_beq : Nat.beq srcSize dstSize = false := by
    cases h : Nat.beq srcSize dstSize with
    | false => rfl
    | true => exact False.elim (h_ne (Nat.beq_eq.mp h))
  rw [fc_evalByteCast_eq locals locals' op mem decls layouts v srcTy dstTy srcSize dstSize
    h_op h_dst_sz h_ty h_src_sz, h_beq]

/-- **Uninitialized / dead / moved-out transmute sources are UB**: whenever the operand read
faults with UB (`evalOperand` on an `uninit` or `dead` local), so does the transmute. -/
theorem fc_evalRvalue_transmute_ub
    {locals : List LocalSlot} {op : Operand} {dstTy : Ty} {mem : Memory}
    {decls : List LocalDecl} {layouts : LayoutTable}
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
        mem.callStack = .ub) :
    evalRvalue locals (.cast .transmute op dstTy) mem decls layouts = .ub := by
  show evalByteCast locals op dstTy mem decls layouts = _
  unfold evalByteCast
  rw [hOp]

/-! ### 5.1 Types of `fcLayouts`: resolution and sizes -/

theorem fc_resolve_f32 (decls : List LocalDecl) :
    resolveTyWithLocalDecls decls fcLayouts fcF32Ty = fcF32Ty := rfl
theorem fc_resolve_f64 (decls : List LocalDecl) :
    resolveTyWithLocalDecls decls fcLayouts fcF64Ty = fcF64Ty := rfl
theorem fc_resolve_u32 (decls : List LocalDecl) :
    resolveTyWithLocalDecls decls fcLayouts fcU32Ty = fcU32Ty := rfl
theorem fc_resolve_i32 (decls : List LocalDecl) :
    resolveTyWithLocalDecls decls fcLayouts fcI32Ty = fcI32Ty := rfl
theorem fc_resolve_u64 (decls : List LocalDecl) :
    resolveTyWithLocalDecls decls fcLayouts fcU64Ty = fcU64Ty := rfl
theorem fc_resolve_i64 (decls : List LocalDecl) :
    resolveTyWithLocalDecls decls fcLayouts fcI64Ty = fcI64Ty := rfl
theorem fc_resolve_bytes4 (decls : List LocalDecl) :
    resolveTyWithLocalDecls decls fcLayouts fcBytes4Ty = fcBytes4Ty := rfl
theorem fc_resolve_bytes8 (decls : List LocalDecl) :
    resolveTyWithLocalDecls decls fcLayouts fcBytes8Ty = fcBytes8Ty := rfl

theorem fc_tyByteSize_f32 (decls : List LocalDecl) :
    tyByteSize decls fcLayouts (resolveTyWithLocalDecls decls fcLayouts fcF32Ty) = some 4 := rfl
theorem fc_tyByteSize_f64 (decls : List LocalDecl) :
    tyByteSize decls fcLayouts (resolveTyWithLocalDecls decls fcLayouts fcF64Ty) = some 8 := rfl
theorem fc_tyByteSize_u32 (decls : List LocalDecl) :
    tyByteSize decls fcLayouts (resolveTyWithLocalDecls decls fcLayouts fcU32Ty) = some 4 := rfl
theorem fc_tyByteSize_i32 (decls : List LocalDecl) :
    tyByteSize decls fcLayouts (resolveTyWithLocalDecls decls fcLayouts fcI32Ty) = some 4 := rfl
theorem fc_tyByteSize_u64 (decls : List LocalDecl) :
    tyByteSize decls fcLayouts (resolveTyWithLocalDecls decls fcLayouts fcU64Ty) = some 8 := rfl
theorem fc_tyByteSize_i64 (decls : List LocalDecl) :
    tyByteSize decls fcLayouts (resolveTyWithLocalDecls decls fcLayouts fcI64Ty) = some 8 := rfl
theorem fc_tyByteSize_bytes4 (decls : List LocalDecl) :
    tyByteSize decls fcLayouts (resolveTyWithLocalDecls decls fcLayouts fcBytes4Ty) = some 4 := rfl
theorem fc_tyByteSize_bytes8 (decls : List LocalDecl) :
    tyByteSize decls fcLayouts (resolveTyWithLocalDecls decls fcLayouts fcBytes8Ty) = some 8 := rfl

/-- Anneal sizes floats only through the layout table: `rigidTyKindByteSize` has no float arm, so
with an empty layout table `f32` has no byte size and every `f32` transmute fails closed. -/
theorem fc_tyByteSize_f32_emptyLayouts (decls : List LocalDecl) (h : decls = []) :
    tyByteSize decls emptyLayoutTable { kind := .float .f32, layoutIdx := 0 } = none := by
  subst h; rfl

/-! ### 5.2 Decoding at the carrier and float types -/

/-- Decoding at `u32` (and `u64`, `i32`, `i64`, `f32`, `f64` below) depends on the bytes only
through their provenance, their length, and Anneal's little-endian scalar decoder. -/
theorem fc_decodeTyped_u32_eq (bs : List MirSemantics.AbstractByte) :
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcU32Ty bs =
      match abstractBytesHaveProv bs with
      | true => none
      | false =>
        match Nat.beq (Trusted.Sequence.length bs) 4 with
        | false => none
        | true =>
          match decodeScalarBytes bs false with
          | some (sv, _) => some (.scalar sv)
          | none => none := rfl

theorem fc_decodeTyped_i32_eq (bs : List MirSemantics.AbstractByte) :
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcI32Ty bs =
      match abstractBytesHaveProv bs with
      | true => none
      | false =>
        match Nat.beq (Trusted.Sequence.length bs) 4 with
        | false => none
        | true =>
          match decodeScalarBytes bs true with
          | some (sv, _) => some (.scalar sv)
          | none => none := rfl

/-- `f32` decodes exactly like `u32` (`normalizeCodecTy`: floats have no invalid bit patterns). -/
theorem fc_decodeTyped_f32_eq (bs : List MirSemantics.AbstractByte) :
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcF32Ty bs =
      decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcU32Ty bs := rfl

theorem fc_decodeTyped_u64_eq (bs : List MirSemantics.AbstractByte) :
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcU64Ty bs =
      match abstractBytesHaveProv bs with
      | true => none
      | false =>
        match Nat.beq (Trusted.Sequence.length bs) 8 with
        | false => none
        | true =>
          match decodeScalarBytes bs false with
          | some (sv, _) => some (.scalar sv)
          | none => none := rfl

theorem fc_decodeTyped_i64_eq (bs : List MirSemantics.AbstractByte) :
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcI64Ty bs =
      match abstractBytesHaveProv bs with
      | true => none
      | false =>
        match Nat.beq (Trusted.Sequence.length bs) 8 with
        | false => none
        | true =>
          match decodeScalarBytes bs true with
          | some (sv, _) => some (.scalar sv)
          | none => none := rfl

/-- `f64` decodes exactly like `u64`. -/
theorem fc_decodeTyped_f64_eq (bs : List MirSemantics.AbstractByte) :
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcF64Ty bs =
      decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcU64Ty bs := rfl

theorem fc_lt_256_pow_4 {bits : Nat} (h : bits < 2 ^ 32) : bits < 256 ^ (3 + 1) := by
  simpa using h

theorem fc_lt_256_pow_8 {bits : Nat} (h : bits < 2 ^ 64) : bits < 256 ^ (7 + 1) := by
  simpa using h

theorem fc_decodeTyped_u32_encode (bits : Nat) (h : bits < 2 ^ 32) :
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcU32Ty
      (encodeLittleEndianBytes bits 4 none) = some (.scalar ⟨bits, 4⟩) := by
  rw [fc_decodeTyped_u32_eq, fc_abstractBytesHaveProv_encode_none,
    fc_seqLength_encodeLittleEndianBytes, fc_decodeScalarBytes_encode none false 3 bits
      (fc_lt_256_pow_4 h)]

theorem fc_decodeTyped_i32_encode (bits : Nat) (h : bits < 2 ^ 32) :
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcI32Ty
      (encodeLittleEndianBytes bits 4 none) = some (.scalar ⟨bits, 4⟩) := by
  rw [fc_decodeTyped_i32_eq, fc_abstractBytesHaveProv_encode_none,
    fc_seqLength_encodeLittleEndianBytes, fc_decodeScalarBytes_encode none true 3 bits
      (fc_lt_256_pow_4 h)]

theorem fc_decodeTyped_f32_encode (bits : Nat) (h : bits < 2 ^ 32) :
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcF32Ty
      (encodeLittleEndianBytes bits 4 none) = some (.scalar ⟨bits, 4⟩) := by
  rw [fc_decodeTyped_f32_eq, fc_decodeTyped_u32_encode bits h]

theorem fc_decodeTyped_u64_encode (bits : Nat) (h : bits < 2 ^ 64) :
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcU64Ty
      (encodeLittleEndianBytes bits 8 none) = some (.scalar ⟨bits, 8⟩) := by
  rw [fc_decodeTyped_u64_eq, fc_abstractBytesHaveProv_encode_none,
    fc_seqLength_encodeLittleEndianBytes, fc_decodeScalarBytes_encode none false 7 bits
      (fc_lt_256_pow_8 h)]

theorem fc_decodeTyped_i64_encode (bits : Nat) (h : bits < 2 ^ 64) :
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcI64Ty
      (encodeLittleEndianBytes bits 8 none) = some (.scalar ⟨bits, 8⟩) := by
  rw [fc_decodeTyped_i64_eq, fc_abstractBytesHaveProv_encode_none,
    fc_seqLength_encodeLittleEndianBytes, fc_decodeScalarBytes_encode none true 7 bits
      (fc_lt_256_pow_8 h)]

theorem fc_decodeTyped_f64_encode (bits : Nat) (h : bits < 2 ^ 64) :
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcF64Ty
      (encodeLittleEndianBytes bits 8 none) = some (.scalar ⟨bits, 8⟩) := by
  rw [fc_decodeTyped_f64_eq, fc_decodeTyped_u64_encode bits h]

/-- **Provenance, Anneal side**: provenance-carrying bytes (e.g. the bytes of a pointer) do not
decode at `f32` / `u32` / `i32` / `f64` / `u64` / `i64`, so transmuting them there is UB. -/
theorem fc_decodeTyped_prov_none (bs : List MirSemantics.AbstractByte)
    (h : abstractBytesHaveProv bs = true) :
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcF32Ty bs = none ∧
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcU32Ty bs = none ∧
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcI32Ty bs = none ∧
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcF64Ty bs = none ∧
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcU64Ty bs = none ∧
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcI64Ty bs = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [fc_decodeTyped_f32_eq, fc_decodeTyped_f64_eq, fc_decodeTyped_u32_eq,
      fc_decodeTyped_i32_eq, fc_decodeTyped_u64_eq, fc_decodeTyped_i64_eq, h]

/-- **Uninitialized bytes, Anneal side**: byte sequences containing `uninit` do not decode at
`f32` / `u32` / `i32` / `f64` / `u64` / `i64`. -/
theorem fc_decodeTyped_uninit_none (bs : List MirSemantics.AbstractByte)
    (h : MirSemantics.AbstractByte.uninit ∈ bs) :
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcF32Ty bs = none ∧
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcU32Ty bs = none ∧
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcI32Ty bs = none ∧
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcF64Ty bs = none ∧
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcU64Ty bs = none ∧
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcI64Ty bs = none := by
  have hdec : decodeLittleEndianBytes bs = none := (fc_decodeLittleEndianBytes_eq_none_iff bs).mpr h
  have hsc : ∀ signed, decodeScalarBytes bs signed = none := by
    intro signed
    unfold decodeScalarBytes
    simp only [hdec]
    split <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [fc_decodeTyped_f32_eq, fc_decodeTyped_f64_eq, fc_decodeTyped_u32_eq,
      fc_decodeTyped_i32_eq, fc_decodeTyped_u64_eq, fc_decodeTyped_i64_eq, hsc] <;>
    split <;> (try rfl) <;> split <;> rfl

/-! ### 5.3 `[u8; 4]` / `[u8; 8]` byte arrays -/

/-- One-byte decoding at `u8` (the element type of `[u8; n]`). -/
theorem fc_decodeTyped_u8_byte (bits : Nat) :
    decodeTypedValueFromBytes 15 fcLayouts { kind := .uint .u8, layoutIdx := 0 }
      [.init (UInt8.ofNat bits) none] = some (.scalar ⟨bits % 256, 1⟩) := by
  show some (Value.scalar ⟨Nat.add (UInt8.ofNat bits).toBitVec.toNat (Nat.mul 256 0), 1⟩) = _
  rw [fc_uint8_ofNat_toNat]
  rfl

theorem fc_decodeArrayChunks_u8 :
    ∀ (n bits : Nat),
      decodeArrayChunksWith
          (fun c => decodeTypedValueFromBytes 15 fcLayouts { kind := .uint .u8, layoutIdx := 0 } c)
          1 n (encodeLittleEndianBytes bits n none) = some (fcLeByteVals bits n)
  | 0, _ => rfl
  | n + 1, bits => by
    have ih := fc_decodeArrayChunks_u8 n (bits / 256)
    show (match decodeTypedValueFromBytes 15 fcLayouts { kind := .uint .u8, layoutIdx := 0 }
          [.init (UInt8.ofNat bits) none] with
        | some v =>
          match decodeArrayChunksWith
              (fun c => decodeTypedValueFromBytes 15 fcLayouts
                { kind := .uint .u8, layoutIdx := 0 } c)
              1 n (encodeLittleEndianBytes (bits / 256) n none) with
          | some vs => some (v :: vs)
          | none => none
        | none => none) = _
    rw [fc_decodeTyped_u8_byte, ih]
    rfl

theorem fc_decodeTyped_bytes4_encode (bits : Nat) :
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcBytes4Ty
      (encodeLittleEndianBytes bits 4 none) = some (.aggregate 0 (fcLeByteVals bits 4)) := by
  show (match decodeArrayChunksWith
      (fun c => decodeTypedValueFromBytes 15 fcLayouts { kind := .uint .u8, layoutIdx := 0 } c)
      1 4 (encodeLittleEndianBytes bits 4 none) with
    | some elems => some (Value.aggregate 0 elems)
    | none => none) = _
  rw [fc_decodeArrayChunks_u8]

theorem fc_decodeTyped_bytes8_encode (bits : Nat) :
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcBytes8Ty
      (encodeLittleEndianBytes bits 8 none) = some (.aggregate 0 (fcLeByteVals bits 8)) := by
  show (match decodeArrayChunksWith
      (fun c => decodeTypedValueFromBytes 15 fcLayouts { kind := .uint .u8, layoutIdx := 0 } c)
      1 8 (encodeLittleEndianBytes bits 8 none) with
    | some elems => some (Value.aggregate 0 elems)
    | none => none) = _
  rw [fc_decodeArrayChunks_u8]

theorem fc_encodeList_u8 :
    ∀ (n bits : Nat),
      encodeListWith
          (fun e => encodeValueToBytes 15 fcLayouts { kind := .uint .u8, layoutIdx := 0 } e)
          1 (fcLeByteVals bits n) = some (encodeLittleEndianBytes bits n none)
  | 0, _ => rfl
  | n + 1, bits => by
    have ih := fc_encodeList_u8 n (bits / 256)
    show (match encodeListWith
          (fun e => encodeValueToBytes 15 fcLayouts { kind := .uint .u8, layoutIdx := 0 } e)
          1 (fcLeByteVals (bits / 256) n) with
        | some restBs => some (appendAbstractBytes [.init (UInt8.ofNat (bits % 256)) none] restBs)
        | none => none) = _
    rw [ih, fc_uint8_ofNat_mod]
    rfl

theorem fc_encodeByteCastSource_bytes4 (bits : Nat) :
    encodeByteCastSourceBytes fcLayouts fcBytes4Ty (.aggregate 0 (fcLeByteVals bits 4)) =
      some (encodeLittleEndianBytes bits 4 none) := by
  show (match encodeListWith
      (fun e => encodeValueToBytes 15 fcLayouts { kind := .uint .u8, layoutIdx := 0 } e)
      1 (fcLeByteVals bits 4) with
    | some bs => some bs
    | none => none) = _
  rw [fc_encodeList_u8]

theorem fc_encodeByteCastSource_bytes8 (bits : Nat) :
    encodeByteCastSourceBytes fcLayouts fcBytes8Ty (.aggregate 0 (fcLeByteVals bits 8)) =
      some (encodeLittleEndianBytes bits 8 none) := by
  show (match encodeListWith
      (fun e => encodeValueToBytes 15 fcLayouts { kind := .uint .u8, layoutIdx := 0 } e)
      1 (fcLeByteVals bits 8) with
    | some bs => some bs
    | none => none) = _
  rw [fc_encodeList_u8]

/-- Every `[u8; n]` value of in-range bytes is `fcLeByteVals` of its little-endian number. -/
theorem fc_leByteVals_complete :
    ∀ (bs : List Nat), (∀ b ∈ bs, b < 256) →
      ∃ bits, bits < 256 ^ bs.length ∧
        bs.map (fun b => Value.scalar ⟨b, 1⟩) = fcLeByteVals bits bs.length
  | [], _ => ⟨0, by simp, rfl⟩
  | b :: rest, h => by
    obtain ⟨hi, hlt, heq⟩ := fc_leByteVals_complete rest (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hb : b < 256 := h b (List.mem_cons_self ..)
    refine ⟨b + 256 * hi, ?_, ?_⟩
    · simp only [List.length_cons, Nat.pow_succ]
      have : 256 * hi + 256 ≤ 256 * 256 ^ rest.length := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
      omega
    · simp only [List.map_cons, List.length_cons, fcLeByteVals, heq]
      have h1 : (b + 256 * hi) % 256 = b := by omega
      have h2 : (b + 256 * hi) / 256 = hi := by omega
      rw [h1, h2]

/-! ### 5.4 The transmute theorems -/

/-- Generic same-width transmute through `n` little-endian bytes. -/
theorem fc_evalRvalue_transmute_via_le
    {locals locals' : List LocalSlot} {op : Operand} {mem : Memory} {decls : List LocalDecl}
    {srcTy dstTy : Ty} {v res : Value} {n bits : Nat}
    (h_op : evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok v locals')
    (h_ty : operandTy decls fcLayouts op = some srcTy)
    (h_src_sz : tyByteSize decls fcLayouts (resolveTyWithLocalDecls decls fcLayouts srcTy) = some n)
    (h_dst_sz : tyByteSize decls fcLayouts (resolveTyWithLocalDecls decls fcLayouts dstTy) = some n)
    (h_enc : encodeByteCastSourceBytes fcLayouts (resolveTyWithLocalDecls decls fcLayouts srcTy) v =
      some (encodeLittleEndianBytes bits n none))
    (h_dec : decodeTypedValueFromBytes defaultCodecFuel fcLayouts
      (resolveTyWithLocalDecls decls fcLayouts dstTy) (encodeLittleEndianBytes bits n none) =
        some res) :
    evalRvalue locals (.cast .transmute op dstTy) mem decls fcLayouts = .ok res locals' mem := by
  show evalByteCast locals op dstTy mem decls fcLayouts = _
  rw [fc_evalByteCast_of_encode locals locals' op mem decls fcLayouts v srcTy dstTy n _ h_op
    h_dst_sz h_ty h_src_sz h_enc (fc_seqLength_encodeLittleEndianBytes none n bits), h_dec]

section TransmuteTheorems

variable {locals locals' : List LocalSlot} {op : Operand} {mem : Memory} {decls : List LocalDecl}

/-- **`f32::to_bits`**: transmuting an `f32` holding bit pattern `bits` to `u32` yields exactly
`bits`, for every bit pattern (signaling and quiet NaNs, `-0.0`, subnormals, infinities). -/
theorem fc_transmute_f32_to_u32 {bits : Nat} (hbits : bits < 2 ^ 32)
    (h_op : evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok (.scalar ⟨bits, 4⟩) locals')
    (h_ty : operandTy decls fcLayouts op = some fcF32Ty) :
    evalRvalue locals (.cast .transmute op fcU32Ty) mem decls fcLayouts =
      .ok (.scalar ⟨bits, 4⟩) locals' mem :=
  fc_evalRvalue_transmute_via_le h_op h_ty (fc_tyByteSize_f32 decls) (fc_tyByteSize_u32 decls) rfl
    (by rw [fc_resolve_u32]; exact fc_decodeTyped_u32_encode bits hbits)

/-- **`f32::from_bits`**: transmuting a `u32` holding `bits` to `f32` yields the `f32` with bit
pattern `bits`, for every bit pattern. -/
theorem fc_transmute_u32_to_f32 {bits : Nat} (hbits : bits < 2 ^ 32)
    (h_op : evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok (.scalar ⟨bits, 4⟩) locals')
    (h_ty : operandTy decls fcLayouts op = some fcU32Ty) :
    evalRvalue locals (.cast .transmute op fcF32Ty) mem decls fcLayouts =
      .ok (.scalar ⟨bits, 4⟩) locals' mem :=
  fc_evalRvalue_transmute_via_le h_op h_ty (fc_tyByteSize_u32 decls) (fc_tyByteSize_f32 decls) rfl
    (by rw [fc_resolve_f32]; exact fc_decodeTyped_f32_encode bits hbits)

/-- `f32 → i32`: the bits are preserved (Anneal stores signed integers as their canonical
two's-complement bit pattern; `intValueOfBits true 32 bits` is the `i32` they denote). -/
theorem fc_transmute_f32_to_i32 {bits : Nat} (hbits : bits < 2 ^ 32)
    (h_op : evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok (.scalar ⟨bits, 4⟩) locals')
    (h_ty : operandTy decls fcLayouts op = some fcF32Ty) :
    evalRvalue locals (.cast .transmute op fcI32Ty) mem decls fcLayouts =
      .ok (.scalar ⟨bits, 4⟩) locals' mem :=
  fc_evalRvalue_transmute_via_le h_op h_ty (fc_tyByteSize_f32 decls) (fc_tyByteSize_i32 decls) rfl
    (by rw [fc_resolve_i32]; exact fc_decodeTyped_i32_encode bits hbits)

/-- `i32 → f32`: the bits are preserved. -/
theorem fc_transmute_i32_to_f32 {bits : Nat} (hbits : bits < 2 ^ 32)
    (h_op : evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok (.scalar ⟨bits, 4⟩) locals')
    (h_ty : operandTy decls fcLayouts op = some fcI32Ty) :
    evalRvalue locals (.cast .transmute op fcF32Ty) mem decls fcLayouts =
      .ok (.scalar ⟨bits, 4⟩) locals' mem :=
  fc_evalRvalue_transmute_via_le h_op h_ty (fc_tyByteSize_i32 decls) (fc_tyByteSize_f32 decls) rfl
    (by rw [fc_resolve_f32]; exact fc_decodeTyped_f32_encode bits hbits)

/-- `f32 → [u8; 4]` (`f32::to_le_bytes`): the four little-endian bytes of `bits`. -/
theorem fc_transmute_f32_to_bytes4 {bits : Nat} (hbits : bits < 2 ^ 32)
    (h_op : evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok (.scalar ⟨bits, 4⟩) locals')
    (h_ty : operandTy decls fcLayouts op = some fcF32Ty) :
    evalRvalue locals (.cast .transmute op fcBytes4Ty) mem decls fcLayouts =
      .ok (.aggregate 0 (fcLeByteVals bits 4)) locals' mem :=
  have _ := hbits
  fc_evalRvalue_transmute_via_le h_op h_ty (fc_tyByteSize_f32 decls) (fc_tyByteSize_bytes4 decls)
    rfl (by rw [fc_resolve_bytes4]; exact fc_decodeTyped_bytes4_encode bits)

/-- `[u8; 4] → f32` (`f32::from_le_bytes`): the `f32` whose bit pattern has those
little-endian bytes. -/
theorem fc_transmute_bytes4_to_f32 {bits : Nat} (hbits : bits < 2 ^ 32)
    (h_op : evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok (.aggregate 0 (fcLeByteVals bits 4)) locals')
    (h_ty : operandTy decls fcLayouts op = some fcBytes4Ty) :
    evalRvalue locals (.cast .transmute op fcF32Ty) mem decls fcLayouts =
      .ok (.scalar ⟨bits, 4⟩) locals' mem :=
  fc_evalRvalue_transmute_via_le h_op h_ty (fc_tyByteSize_bytes4 decls) (fc_tyByteSize_f32 decls)
    (by rw [fc_resolve_bytes4]; exact fc_encodeByteCastSource_bytes4 bits)
    (by rw [fc_resolve_f32]; exact fc_decodeTyped_f32_encode bits hbits)

/-- **`f64::to_bits`**: transmuting an `f64` holding `bits` to `u64` yields exactly `bits`. -/
theorem fc_transmute_f64_to_u64 {bits : Nat} (hbits : bits < 2 ^ 64)
    (h_op : evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok (.scalar ⟨bits, 8⟩) locals')
    (h_ty : operandTy decls fcLayouts op = some fcF64Ty) :
    evalRvalue locals (.cast .transmute op fcU64Ty) mem decls fcLayouts =
      .ok (.scalar ⟨bits, 8⟩) locals' mem :=
  fc_evalRvalue_transmute_via_le h_op h_ty (fc_tyByteSize_f64 decls) (fc_tyByteSize_u64 decls) rfl
    (by rw [fc_resolve_u64]; exact fc_decodeTyped_u64_encode bits hbits)

/-- **`f64::from_bits`**: transmuting a `u64` holding `bits` to `f64` yields the `f64` with bit
pattern `bits`. -/
theorem fc_transmute_u64_to_f64 {bits : Nat} (hbits : bits < 2 ^ 64)
    (h_op : evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok (.scalar ⟨bits, 8⟩) locals')
    (h_ty : operandTy decls fcLayouts op = some fcU64Ty) :
    evalRvalue locals (.cast .transmute op fcF64Ty) mem decls fcLayouts =
      .ok (.scalar ⟨bits, 8⟩) locals' mem :=
  fc_evalRvalue_transmute_via_le h_op h_ty (fc_tyByteSize_u64 decls) (fc_tyByteSize_f64 decls) rfl
    (by rw [fc_resolve_f64]; exact fc_decodeTyped_f64_encode bits hbits)

/-- `f64 → i64`: the bits are preserved. -/
theorem fc_transmute_f64_to_i64 {bits : Nat} (hbits : bits < 2 ^ 64)
    (h_op : evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok (.scalar ⟨bits, 8⟩) locals')
    (h_ty : operandTy decls fcLayouts op = some fcF64Ty) :
    evalRvalue locals (.cast .transmute op fcI64Ty) mem decls fcLayouts =
      .ok (.scalar ⟨bits, 8⟩) locals' mem :=
  fc_evalRvalue_transmute_via_le h_op h_ty (fc_tyByteSize_f64 decls) (fc_tyByteSize_i64 decls) rfl
    (by rw [fc_resolve_i64]; exact fc_decodeTyped_i64_encode bits hbits)

/-- `i64 → f64`: the bits are preserved. -/
theorem fc_transmute_i64_to_f64 {bits : Nat} (hbits : bits < 2 ^ 64)
    (h_op : evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok (.scalar ⟨bits, 8⟩) locals')
    (h_ty : operandTy decls fcLayouts op = some fcI64Ty) :
    evalRvalue locals (.cast .transmute op fcF64Ty) mem decls fcLayouts =
      .ok (.scalar ⟨bits, 8⟩) locals' mem :=
  fc_evalRvalue_transmute_via_le h_op h_ty (fc_tyByteSize_i64 decls) (fc_tyByteSize_f64 decls) rfl
    (by rw [fc_resolve_f64]; exact fc_decodeTyped_f64_encode bits hbits)

/-- `f64 → [u8; 8]` (`f64::to_le_bytes`). -/
theorem fc_transmute_f64_to_bytes8 {bits : Nat} (hbits : bits < 2 ^ 64)
    (h_op : evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok (.scalar ⟨bits, 8⟩) locals')
    (h_ty : operandTy decls fcLayouts op = some fcF64Ty) :
    evalRvalue locals (.cast .transmute op fcBytes8Ty) mem decls fcLayouts =
      .ok (.aggregate 0 (fcLeByteVals bits 8)) locals' mem :=
  have _ := hbits
  fc_evalRvalue_transmute_via_le h_op h_ty (fc_tyByteSize_f64 decls) (fc_tyByteSize_bytes8 decls)
    rfl (by rw [fc_resolve_bytes8]; exact fc_decodeTyped_bytes8_encode bits)

/-- `[u8; 8] → f64` (`f64::from_le_bytes`). -/
theorem fc_transmute_bytes8_to_f64 {bits : Nat} (hbits : bits < 2 ^ 64)
    (h_op : evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok (.aggregate 0 (fcLeByteVals bits 8)) locals')
    (h_ty : operandTy decls fcLayouts op = some fcBytes8Ty) :
    evalRvalue locals (.cast .transmute op fcF64Ty) mem decls fcLayouts =
      .ok (.scalar ⟨bits, 8⟩) locals' mem :=
  fc_evalRvalue_transmute_via_le h_op h_ty (fc_tyByteSize_bytes8 decls) (fc_tyByteSize_f64 decls)
    (by rw [fc_resolve_bytes8]; exact fc_encodeByteCastSource_bytes8 bits)
    (by rw [fc_resolve_f64]; exact fc_decodeTyped_f64_encode bits hbits)

/-- **Size mismatch fails closed**: `f32 → u64`, `f64 → u32`, `u32 → f64`, and `u64 → f32`
transmutes are `.unsupported` (Anneal never certifies them), for every operand value. -/
theorem fc_transmute_size_mismatch {v : Value}
    (h_op : evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok v locals') :
    (operandTy decls fcLayouts op = some fcF32Ty →
      evalRvalue locals (.cast .transmute op fcU64Ty) mem decls fcLayouts = .unsupported) ∧
    (operandTy decls fcLayouts op = some fcF64Ty →
      evalRvalue locals (.cast .transmute op fcU32Ty) mem decls fcLayouts = .unsupported) ∧
    (operandTy decls fcLayouts op = some fcU32Ty →
      evalRvalue locals (.cast .transmute op fcF64Ty) mem decls fcLayouts = .unsupported) ∧
    (operandTy decls fcLayouts op = some fcU64Ty →
      evalRvalue locals (.cast .transmute op fcF32Ty) mem decls fcLayouts = .unsupported) :=
  ⟨fun h => fc_evalByteCast_size_mismatch locals locals' op mem decls fcLayouts v _ _ 4 8 h_op
      (fc_tyByteSize_u64 decls) h (fc_tyByteSize_f32 decls) (by decide),
   fun h => fc_evalByteCast_size_mismatch locals locals' op mem decls fcLayouts v _ _ 8 4 h_op
      (fc_tyByteSize_u32 decls) h (fc_tyByteSize_f64 decls) (by decide),
   fun h => fc_evalByteCast_size_mismatch locals locals' op mem decls fcLayouts v _ _ 4 8 h_op
      (fc_tyByteSize_f64 decls) h (fc_tyByteSize_u32 decls) (by decide),
   fun h => fc_evalByteCast_size_mismatch locals locals' op mem decls fcLayouts v _ _ 8 4 h_op
      (fc_tyByteSize_f32 decls) h (fc_tyByteSize_u64 decls) (by decide)⟩

/-- **Exact round trips**: for every `f32` bit pattern, `from_bits (to_bits x) = x` and
`to_bits (from_bits b) = b` at the `evalRvalue` level (each direction returns its operand's bits
unchanged), and likewise through `i32` and `[u8; 4]`. -/
theorem fc_f32_roundtrip {bits : Nat} (hbits : bits < 2 ^ 32)
    {locals₂ locals₂' : List LocalSlot} {op₂ : Operand}
    (h_op : evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok (.scalar ⟨bits, 4⟩) locals')
    (h_ty : operandTy decls fcLayouts op = some fcF32Ty)
    (h_op₂ : evalOperand locals₂ op₂ mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok (.scalar ⟨bits, 4⟩) locals₂')
    (h_ty₂ : operandTy decls fcLayouts op₂ = some fcU32Ty) :
    evalRvalue locals (.cast .transmute op fcU32Ty) mem decls fcLayouts =
        .ok (.scalar ⟨bits, 4⟩) locals' mem ∧
      evalRvalue locals₂ (.cast .transmute op₂ fcF32Ty) mem decls fcLayouts =
        .ok (.scalar ⟨bits, 4⟩) locals₂' mem :=
  ⟨fc_transmute_f32_to_u32 hbits h_op h_ty, fc_transmute_u32_to_f32 hbits h_op₂ h_ty₂⟩

/-- The `f64` analogue of `fc_f32_roundtrip`. -/
theorem fc_f64_roundtrip {bits : Nat} (hbits : bits < 2 ^ 64)
    {locals₂ locals₂' : List LocalSlot} {op₂ : Operand}
    (h_op : evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok (.scalar ⟨bits, 8⟩) locals')
    (h_ty : operandTy decls fcLayouts op = some fcF64Ty)
    (h_op₂ : evalOperand locals₂ op₂ mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok (.scalar ⟨bits, 8⟩) locals₂')
    (h_ty₂ : operandTy decls fcLayouts op₂ = some fcU64Ty) :
    evalRvalue locals (.cast .transmute op fcU64Ty) mem decls fcLayouts =
        .ok (.scalar ⟨bits, 8⟩) locals' mem ∧
      evalRvalue locals₂ (.cast .transmute op₂ fcF64Ty) mem decls fcLayouts =
        .ok (.scalar ⟨bits, 8⟩) locals₂' mem :=
  ⟨fc_transmute_f64_to_u64 hbits h_op h_ty, fc_transmute_u64_to_f64 hbits h_op₂ h_ty₂⟩

end TransmuteTheorems

theorem fc_tyByteSize_rawPtrU8 (decls : List LocalDecl) :
    tyByteSize decls fcLayouts (resolveTyWithLocalDecls decls fcLayouts fcRawPtrU8Ty) = some 8 :=
  rfl

/-- **Pointer provenance, Anneal side, at `evalRvalue`**: transmuting a thin raw pointer value
(`.ptr p 8`, whose bytes carry `(allocId, tag)` provenance) to `f64`, `u64`, or `i64` is UB in
Anneal, for every pointer `p`: the provenance-carrying bytes have no float or integer reading.
(MiniRust instead reads those bytes at `u64` with the provenance dropped, `fc_mr_decode_ptrBytes`.) -/
theorem fc_transmute_ptr_to_f64_ub
    {locals locals' : List LocalSlot} {op : Operand} {mem : Memory} {decls : List LocalDecl}
    {p : ProvenancePtr}
    (h_op : evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok (.ptr p 8) locals')
    (h_ty : operandTy decls fcLayouts op = some fcRawPtrU8Ty) :
    evalRvalue locals (.cast .transmute op fcF64Ty) mem decls fcLayouts = .ub ∧
    evalRvalue locals (.cast .transmute op fcU64Ty) mem decls fcLayouts = .ub ∧
    evalRvalue locals (.cast .transmute op fcI64Ty) mem decls fcLayouts = .ub := by
  have h_enc : encodeByteCastSourceBytes fcLayouts
      (resolveTyWithLocalDecls decls fcLayouts fcRawPtrU8Ty) (.ptr p 8) =
      some (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) := rfl
  have h_len := fc_seqLength_encodeLittleEndianBytes (some (p.allocId, p.tag)) 8 p.offsetBytes
  obtain ⟨_, _, _, hf64, hu64, hi64⟩ := fc_decodeTyped_prov_none _
    (fc_abstractBytesHaveProv_encode_some (p.allocId, p.tag) 7 p.offsetBytes)
  refine ⟨?_, ?_, ?_⟩
  · show evalByteCast locals op fcF64Ty mem decls fcLayouts = _
    rw [fc_evalByteCast_of_encode locals locals' op mem decls fcLayouts _ _ _ 8 _ h_op
      (fc_tyByteSize_f64 decls) h_ty (fc_tyByteSize_rawPtrU8 decls) h_enc h_len, fc_resolve_f64, hf64]
  · show evalByteCast locals op fcU64Ty mem decls fcLayouts = _
    rw [fc_evalByteCast_of_encode locals locals' op mem decls fcLayouts _ _ _ 8 _ h_op
      (fc_tyByteSize_u64 decls) h_ty (fc_tyByteSize_rawPtrU8 decls) h_enc h_len, fc_resolve_u64, hu64]
  · show evalByteCast locals op fcI64Ty mem decls fcLayouts = _
    rw [fc_evalByteCast_of_encode locals locals' op mem decls fcLayouts _ _ _ 8 _ h_op
      (fc_tyByteSize_i64 decls) h_ty (fc_tyByteSize_rawPtrU8 decls) h_enc h_len, fc_resolve_i64, hi64]

/-- The bytes of a pointer, erased of provenance by `fcByteToMR`, are exactly MiniRust's
`scalarBytes` of its address: provenance is the *only* difference between Anneal's pointer image
and an integer image, and it is what Anneal's float/integer decoding rejects. -/
theorem fc_ptr_bytes_erased (addr : Nat) (p : Nat × Nat) :
    (encodeLittleEndianBytes addr 8 (some p)).map fcByteToMR = scalarBytes fcU64It addr :=
  fc_map_encodeLittleEndianBytes .Unsigned (some p) 8 addr


/-! ## 6. MiniRust's side: `Type.encode` / `Type.decode` / `transmute` on the bit carriers -/

theorem fc_goodSize_4 : GoodSize 4 := by unfold GoodSize; omega
theorem fc_goodSize_8 : GoodSize 8 := by unfold GoodSize; omega

/-- **Signed readings agree**: Anneal's `intValueOfBits` (`Anneal.Mir.IeeeFloatCast`, the value a
two's-complement bit pattern denotes) is MiniRust's `intFromBits` (`minimize`'s
`int_from_bits`) on every in-range pattern of every positive byte width, for both signednesses. -/
theorem fc_intValueOfBits_eq_intFromBits (signed : Bool) (n bits : Nat)
    (hbits : bits < 2 ^ (8 * n)) :
    intValueOfBits signed (8 * n) bits =
      intFromBits bits ⟨if signed then .Signed else .Unsigned, ⟨n⟩⟩ := by
  unfold intValueOfBits intFromBits
  rw [Nat.mod_eq_of_lt hbits]
  cases signed with
  | false => simp
  | true =>
    simp only [true_and, ↓reduceIte]
    by_cases hlt : bits < 2 ^ (8 * n - 1)
    · have : ¬ 2 ^ (8 * n - 1) ≤ bits := by omega
      simp [hlt, this]
    · have : 2 ^ (8 * n - 1) ≤ bits := by omega
      simp [hlt, this]

/-- `intValueOfBits` at `i32` / `u32` / `i64` / `u64` is MiniRust's `intFromBits`. -/
theorem fc_intValueOfBits_carriers (bits : Nat) :
    (bits < 2 ^ 32 → intValueOfBits true 32 bits = intFromBits bits fcI32It ∧
      intValueOfBits false 32 bits = intFromBits bits fcU32It) ∧
    (bits < 2 ^ 64 → intValueOfBits true 64 bits = intFromBits bits fcI64It ∧
      intValueOfBits false 64 bits = intFromBits bits fcU64It) :=
  ⟨fun h => ⟨fc_intValueOfBits_eq_intFromBits true 4 bits h,
      fc_intValueOfBits_eq_intFromBits false 4 bits h⟩,
   fun h => ⟨fc_intValueOfBits_eq_intFromBits true 8 bits h,
      fc_intValueOfBits_eq_intFromBits false 8 bits h⟩⟩

/-- MiniRust's `Type.encode` of the integer a bit pattern denotes is its little-endian bytes. -/
theorem fc_mr_encode_intFromBits (it : Gen.IntType) (bits : Nat) (hgood : GoodSize it.size.bytes)
    (hbits : bits < 2 ^ (8 * it.size.bytes)) :
    Type.encode (.Int it) (.Int (intFromBits bits it)) = .ok (scalarBytes it bits) := by
  rw [encode_int it _ hgood (canRepresent_intFromBits it bits hgood hbits),
    intFromBits_emod bits it hbits]
  rfl

/-- **Anneal's encoding is MiniRust's `Type.encode`, byte for byte**: for every bit pattern of a
4- or 8-byte carrier (or any other MiniRust integer width), MiniRust's `Type.encode` of the integer
it denotes is the image of Anneal's `encodeLittleEndianBytes` under `fcByteToMR`. -/
theorem fc_mr_encode_eq_anneal (s : Signedness) (n bits : Nat) (hgood : GoodSize n)
    (hbits : bits < 2 ^ (8 * n)) :
    Type.encode (.Int ⟨s, ⟨n⟩⟩) (.Int (intFromBits bits ⟨s, ⟨n⟩⟩)) =
      .ok ((encodeLittleEndianBytes bits n none).map fcByteToMR) := by
  rw [fc_mr_encode_intFromBits ⟨s, ⟨n⟩⟩ bits hgood hbits, fc_map_encodeLittleEndianBytes]

/-- **MiniRust's `Type.decode` reads Anneal's bytes back**: decoding the image of Anneal's
little-endian encoding (with any provenance, which MiniRust's integer decoding ignores) yields the
integer `intFromBits bits` (= Anneal's `intValueOfBits`). -/
theorem fc_mr_decode_eq_anneal (s : Signedness) (n bits : Nat) (prov : Option (Nat × Nat))
    (hbits : bits < 2 ^ (8 * n)) :
    Type.decode (.Int ⟨s, ⟨n⟩⟩) ((encodeLittleEndianBytes bits n prov).map fcByteToMR) =
      .ok (some (.Int (intFromBits bits ⟨s, ⟨n⟩⟩))) := by
  rw [fc_map_encodeLittleEndianBytes s prov n bits]
  exact decode_int_scalarBytes ⟨s, ⟨n⟩⟩ bits hbits

/-- `scalarBytes` depends only on the width. -/
theorem fc_scalarBytes_sign (s₁ s₂ : Signedness) (n bits : Nat) :
    scalarBytes ⟨s₁, ⟨n⟩⟩ bits = scalarBytes ⟨s₂, ⟨n⟩⟩ bits := rfl

/-- **MiniRust `transmute` between same-width integers** (`u32 ↔ i32`, `u64 ↔ i64`, ...) moves
the bit pattern unchanged: `intFromBits bits` at the old type becomes `intFromBits bits` at the
new one, for every bit pattern. -/
theorem fc_mr_transmute_int (s₁ s₂ : Signedness) (n bits : Nat) (hgood : GoodSize n)
    (hbits : bits < 2 ^ (8 * n)) (m : Option Mach) :
    transmute (.Int (intFromBits bits ⟨s₁, ⟨n⟩⟩)) (.Int ⟨s₁, ⟨n⟩⟩) (.Int ⟨s₂, ⟨n⟩⟩) m =
      .ok (.Int (intFromBits bits ⟨s₂, ⟨n⟩⟩)) := by
  have henc := fc_mr_encode_intFromBits ⟨s₁, ⟨n⟩⟩ bits hgood hbits
  have hdec := decode_int_scalarBytes ⟨s₂, ⟨n⟩⟩ bits hbits
  have hrep := canRepresent_intFromBits ⟨s₂, ⟨n⟩⟩ bits hgood hbits
  unfold transmute
  simp only [layout_eq ⟨s₁, ⟨n⟩⟩ hgood, layout_eq ⟨s₂, ⟨n⟩⟩ hgood, bind, Except.bind,
    expect_size_sized, ne_eq, not_true_eq_false, ↓reduceIte, henc, fc_scalarBytes_sign s₁ s₂, hdec,
    checkValue_int hrep]
  rfl

theorem fc_mapM_dataM_init {M : Type} [Gen.Memory M] :
    ∀ data : List UInt8,
      (data.map (fun b =>
        (Gen.AbstractByte.Init b none : Gen.AbstractByte (Gen.Memory.Provenance M)))).mapM
        AbstractByte.dataM = some data
  | [] => rfl
  | b :: bs => by
    have ih := fc_mapM_dataM_init (M := M) bs
    simp only [List.map_cons, List.mapM_cons, AbstractByte.dataM] at ih ⊢
    rw [ih]
    rfl

/-- **Polymorphic MiniRust `transmuteM` between same-width integers**, for *every* memory model
`M` (in particular `BasicMemory` and `TreeBorrowsMemory`, below): the bit pattern is moved
unchanged. -/
theorem fc_mrM_transmute_int {M : Type} [Gen.Memory M] [MemoryOps M] (s₁ s₂ : Signedness)
    (n bits : Nat) (hgood : GoodSize n) (hbits : bits < 2 ^ (8 * n))
    (m : Option (Gen.Machine M)) :
    transmuteM (M := M) (.Int (intFromBits bits ⟨s₁, ⟨n⟩⟩)) (.Int ⟨s₁, ⟨n⟩⟩) (.Int ⟨s₂, ⟨n⟩⟩) m =
      .ok (.Int (intFromBits bits ⟨s₂, ⟨n⟩⟩)) := by
  have hrep₁ := canRepresent_intFromBits ⟨s₁, ⟨n⟩⟩ bits hgood hbits
  have hrep₂ := canRepresent_intFromBits ⟨s₂, ⟨n⟩⟩ bits hgood hbits
  have hmod : (intFromBits bits ⟨s₁, ⟨n⟩⟩ % 2 ^ Size.bits ⟨n⟩).toNat = bits := by
    have := intFromBits_emod bits ⟨s₁, ⟨n⟩⟩ hbits
    simp only [Size.bits] at this ⊢
    rw [this]; rfl
  have henc : Endianness.encode .LittleEndian s₁ ⟨n⟩ (intFromBits bits ⟨s₁, ⟨n⟩⟩) =
      some (leBytes bits n) := by
    rw [encode_eq s₁ ⟨n⟩ _ hrep₁, hmod]
  have hdec := decode_leBytes s₂ n bits hbits
  unfold transmuteM
  simp only [layout_eq ⟨s₁, ⟨n⟩⟩ hgood, layout_eq ⟨s₂, ⟨n⟩⟩ hgood, bind, Except.bind,
    expect_size_sized, ne_eq, not_true_eq_false,
    ↓reduceIte, Type.encodeM, Type.encodeIntM, x86_64.ENDIANNESS, henc, Type.decodeM,
    Type.decodeIntM, List.length_map, leBytes_length, fc_mapM_dataM_init, hdec, pure,
    Except.pure, checkValueM, ensureElseUb, hrep₂, Bool.not_true, Bool.false_eq_true]

/-- `transmuteM` over `BasicMemory` (`Machine<BasicMemory<x86_64>>`). -/
theorem fc_mrBM_transmute_int (s₁ s₂ : Signedness) (n bits : Nat) (hgood : GoodSize n)
    (hbits : bits < 2 ^ (8 * n)) (m : Option Mach) :
    transmuteM (M := BM) (.Int (intFromBits bits ⟨s₁, ⟨n⟩⟩)) (.Int ⟨s₁, ⟨n⟩⟩) (.Int ⟨s₂, ⟨n⟩⟩) m =
      .ok (.Int (intFromBits bits ⟨s₂, ⟨n⟩⟩)) :=
  fc_mrM_transmute_int s₁ s₂ n bits hgood hbits m

/-- `transmuteM` over `TreeBorrowsMemory` (`Machine<TreeBorrowsMemory<x86_64>>`). -/
theorem fc_mrTB_transmute_int (s₁ s₂ : Signedness) (n bits : Nat) (hgood : GoodSize n)
    (hbits : bits < 2 ^ (8 * n)) (m : Option MachTB) :
    transmuteM (M := TBM) (.Int (intFromBits bits ⟨s₁, ⟨n⟩⟩)) (.Int ⟨s₁, ⟨n⟩⟩) (.Int ⟨s₂, ⟨n⟩⟩)
      m = .ok (.Int (intFromBits bits ⟨s₂, ⟨n⟩⟩)) :=
  fc_mrM_transmute_int s₁ s₂ n bits hgood hbits m

/-- The `f32` carriers: `u32 ↔ i32` in MiniRust (`transmute`, and `transmuteM` over both memory
models) move every 32-bit pattern unchanged. -/
theorem fc_mr_transmute_u32_i32 (bits : Nat) (hbits : bits < 2 ^ 32) :
    transmute (.Int (intFromBits bits fcU32It)) (.Int fcU32It) (.Int fcI32It) =
        .ok (.Int (intFromBits bits fcI32It)) ∧
      transmute (.Int (intFromBits bits fcI32It)) (.Int fcI32It) (.Int fcU32It) =
        .ok (.Int (intFromBits bits fcU32It)) ∧
      transmuteM (M := BM) (.Int (intFromBits bits fcU32It)) (.Int fcU32It) (.Int fcI32It) =
        .ok (.Int (intFromBits bits fcI32It)) ∧
      transmuteM (M := TBM) (.Int (intFromBits bits fcU32It)) (.Int fcU32It) (.Int fcI32It) =
        .ok (.Int (intFromBits bits fcI32It)) :=
  ⟨fc_mr_transmute_int .Unsigned .Signed 4 bits fc_goodSize_4 hbits none,
   fc_mr_transmute_int .Signed .Unsigned 4 bits fc_goodSize_4 hbits none,
   fc_mrBM_transmute_int .Unsigned .Signed 4 bits fc_goodSize_4 hbits none,
   fc_mrTB_transmute_int .Unsigned .Signed 4 bits fc_goodSize_4 hbits none⟩

/-- The `f64` carriers: `u64 ↔ i64` in MiniRust move every 64-bit pattern unchanged. -/
theorem fc_mr_transmute_u64_i64 (bits : Nat) (hbits : bits < 2 ^ 64) :
    transmute (.Int (intFromBits bits fcU64It)) (.Int fcU64It) (.Int fcI64It) =
        .ok (.Int (intFromBits bits fcI64It)) ∧
      transmute (.Int (intFromBits bits fcI64It)) (.Int fcI64It) (.Int fcU64It) =
        .ok (.Int (intFromBits bits fcU64It)) ∧
      transmuteM (M := BM) (.Int (intFromBits bits fcU64It)) (.Int fcU64It) (.Int fcI64It) =
        .ok (.Int (intFromBits bits fcI64It)) ∧
      transmuteM (M := TBM) (.Int (intFromBits bits fcU64It)) (.Int fcU64It) (.Int fcI64It) =
        .ok (.Int (intFromBits bits fcI64It)) :=
  ⟨fc_mr_transmute_int .Unsigned .Signed 8 bits fc_goodSize_8 hbits none,
   fc_mr_transmute_int .Signed .Unsigned 8 bits fc_goodSize_8 hbits none,
   fc_mrBM_transmute_int .Unsigned .Signed 8 bits fc_goodSize_8 hbits none,
   fc_mrTB_transmute_int .Unsigned .Signed 8 bits fc_goodSize_8 hbits none⟩

/-- **Size mismatch, MiniRust side**: `CastOp::Transmute` between a 4-byte and an 8-byte carrier
raises UB (`transmute between types of different size`), whereas Anneal's `evalByteCast` fails
closed with `.unsupported` (`fc_transmute_size_mismatch`). -/
theorem fc_mr_transmute_size_mismatch_ub (v : Val) (m : Option Mach) :
    evalCastOp (.Transmute (.Int fcU64It)) (v, .Int fcU32It) m =
        .error (.ub "transmute between types of different size") ∧
      evalCastOp (.Transmute (.Int fcU32It)) (v, .Int fcU64It) m =
        .error (.ub "transmute between types of different size") := by
  constructor <;> cases v <;> rfl

/-- **Provenance, MiniRust side**: MiniRust decodes the bytes of a pointer at `u64` by silently
dropping their provenance, while it keeps the provenance at a raw pointer type. (Anneal instead
rejects provenance-carrying bytes at every float and integer type, `fc_decodeTyped_prov_none`, so
the Anneal transmute is UB: Anneal is the stricter side.) -/
theorem fc_mr_decode_ptrBytes (addr : Nat) (h : addr < 2 ^ 64) (prov : Option Prov) :
    Type.decode (.Int fcU64It) (ptrBytes addr prov) = .ok (some (.Int (addr : Int))) ∧
      Type.decode (.Ptr (.Raw .None)) (ptrBytes addr prov) =
        .ok (some (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none })) := by
  constructor
  · have hdata := encodePtrBytes_data prov 0 (leBytes addr 8)
    have hdec := decode_leBytes .Unsigned 8 addr (by simpa using h)
    simp only [Type.decode, Type.decodeInt, fcU64It, ptrBytes, ne_eq, hdata, x86_64.ENDIANNESS,
      hdec]
    rfl
  · simp only [Type.decode, PtrType.as_wide_pair, decodePtr_ptrBytes addr h prov]
    rfl

/-! ## 7. Executions: Anneal runs float casts, `translateFn` rejects them, and the bit carriers
run in both semantics -/

/-- Placeholder ABI (`extern "Rust"`, nothing reads its layouts). -/
def fcAbi : FnAbi :=
  { args := [{ layout := fcPrimLayout 4 (.int 32 false), mode := .direct }],
    ret := { layout := fcPrimLayout 4 (.int 32 false), mode := .direct }, conv := .rust,
    canUnwind := false }

/-- A one-argument `Runtime(PostCleanup)` body over `fcLayouts` whose only block runs `stmts`
and returns. -/
def fcBody (dp : String) (decls : List LocalDecl) (stmts : List StatementKind) : CapturedMir where
  defPath := dp
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := decls
  basicBlocks :=
    [{ statements := stmts.map mkStmt, terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fcAbi
  layouts := fcLayouts
  allocations := []

/-- `fn f32_as_i32(x: f32) -> i32 { x as i32 }` (`_0 = copy _1 as i32 (FloatToInt)`). -/
def fcF2iBody : CapturedMir :=
  fcBody "float_cast::f32_as_i32" [fcDecl fcI32Ty, fcDecl fcF32Ty]
    [.assign (local_ 0) (.cast .floatToInt (.copy (local_ 1)) fcI32Ty)]

/-- `fn i32_as_f64(x: i32) -> f64 { x as f64 }` (`IntToFloat`). -/
def fcI2fBody : CapturedMir :=
  fcBody "float_cast::i32_as_f64" [fcDecl fcF64Ty, fcDecl fcI32Ty]
    [.assign (local_ 0) (.cast .intToFloat (.copy (local_ 1)) fcF64Ty)]

/-- `fn f64_as_f32(x: f64) -> f32 { x as f32 }` (`FloatToFloat`). -/
def fcF2fBody : CapturedMir :=
  fcBody "float_cast::f64_as_f32" [fcDecl fcF32Ty, fcDecl fcF64Ty]
    [.assign (local_ 0) (.cast .floatToFloat (.copy (local_ 1)) fcF32Ty)]

/-- `fn f16_as_i32(x: f16) -> i32 { x as i32 }`: no modeled `f16` format. -/
def fcF16Body : CapturedMir :=
  fcBody "float_cast::f16_as_i32" [fcDecl fcI32Ty, fcDecl fcF16Ty]
    [.assign (local_ 0) (.cast .floatToInt (.copy (local_ 1)) fcI32Ty)]

/-- A float cast reading a live but uninitialized `f32` local:
`StorageLive(_2); _0 = copy _2 as i32 (FloatToInt)`. -/
def fcUninitBody : CapturedMir :=
  fcBody "float_cast::uninit_as_i32" [fcDecl fcI32Ty, fcDecl fcU32Ty, fcDecl fcF32Ty]
    [.storageLive 2, .assign (local_ 0) (.cast .floatToInt (.copy (local_ 2)) fcI32Ty)]

/-- `fn from_bits_as_i32(x: u32) -> i32 { f32::from_bits(x) as i32 }`:
`_2 = copy _1 as f32 (Transmute); _0 = copy _2 as i32 (FloatToInt)`. -/
def fcFromBitsAsI32Body : CapturedMir :=
  fcBody "float_cast::from_bits_as_i32" [fcDecl fcI32Ty, fcDecl fcU32Ty, fcDecl fcF32Ty]
    [.storageLive 2,
     .assign (local_ 2) (.cast .transmute (.copy (local_ 1)) fcF32Ty),
     .assign (local_ 0) (.cast .floatToInt (.copy (local_ 2)) fcI32Ty),
     .storageDead 2]

/-- `fn i32_to_f64_bits(x: i32) -> u64 { (x as f64).to_bits() }`:
`_2 = copy _1 as f64 (IntToFloat); _0 = copy _2 as u64 (Transmute)`. -/
def fcIntAsF64BitsBody : CapturedMir :=
  fcBody "float_cast::i32_as_f64_bits" [fcDecl fcU64Ty, fcDecl fcI32Ty, fcDecl fcF64Ty]
    [.storageLive 2,
     .assign (local_ 2) (.cast .intToFloat (.copy (local_ 1)) fcF64Ty),
     .assign (local_ 0) (.cast .transmute (.copy (local_ 2)) fcU64Ty),
     .storageDead 2]

/-- `fn widen_bits(x: u32) -> u64 { (f32::from_bits(x) as f64).to_bits() }`:
`_2 = copy _1 as f32 (Transmute); _3 = copy _2 as f64 (FloatToFloat);
_0 = copy _3 as u64 (Transmute)`. -/
def fcWidenBitsBody : CapturedMir :=
  fcBody "float_cast::widen_bits" [fcDecl fcU64Ty, fcDecl fcU32Ty, fcDecl fcF32Ty, fcDecl fcF64Ty]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.cast .transmute (.copy (local_ 1)) fcF32Ty),
     .assign (local_ 3) (.cast .floatToFloat (.copy (local_ 2)) fcF64Ty),
     .assign (local_ 0) (.cast .transmute (.copy (local_ 3)) fcU64Ty),
     .storageDead 3, .storageDead 2]

/-- `fn bits_round_trip(x: u32) -> u32 { f32::from_bits(x).to_bits() }`. -/
def fcBitsRoundTripBody : CapturedMir :=
  fcBody "float_cast::bits_round_trip" [fcDecl fcU32Ty, fcDecl fcU32Ty, fcDecl fcF32Ty]
    [.storageLive 2,
     .assign (local_ 2) (.cast .transmute (.copy (local_ 1)) fcF32Ty),
     .assign (local_ 0) (.cast .transmute (.copy (local_ 2)) fcU32Ty),
     .storageDead 2]

/-- The MiniRust-representable bit-carrier step: `fn carrier(x: u32) -> i32 { transmute(x) }`,
which `translateFn` accepts. -/
def fcCarrierBody : CapturedMir :=
  fcBody "float_cast::carrier_u32_i32" [fcDecl fcI32Ty, fcDecl fcU32Ty]
    [.assign (local_ 0) (.cast .transmute (.copy (local_ 1)) fcI32Ty)]

/-- **`translateFn` / `inFragment` / `progInFragment` reject every float-cast body above.** -/
theorem fc_float_bodies_rejected :
    translateFn fcF2iBody = none ∧ translateFn fcI2fBody = none ∧ translateFn fcF2fBody = none ∧
    translateFn fcF16Body = none ∧ translateFn fcUninitBody = none ∧
    translateFn fcFromBitsAsI32Body = none ∧ translateFn fcIntAsF64BitsBody = none ∧
    translateFn fcWidenBitsBody = none ∧ translateFn fcBitsRoundTripBody = none ∧
    inFragment fcF2iBody = false ∧ inFragment fcFromBitsAsI32Body = false ∧
    progInFragment fcF2iBody [] = false ∧ progInFragment fcWidenBitsBody [] = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   fc_inFragment_eq_false_of_float _ ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), _, _, rfl⟩,
   fc_inFragment_eq_false_of_float _ ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
     (List.mem_cons_self ..)), _, _, rfl⟩,
   fc_progInFragment_eq_false_of_float _ _
     ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), _, _, rfl⟩,
   fc_progInFragment_eq_false_of_float _ _ ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
     (List.mem_cons_self ..)), _, _, rfl⟩⟩

/-- The carrier body is translated by `minimize`. -/
theorem fc_carrier_translated : (translateFn fcCarrierBody).isSome = true := rfl

/-- **Anneal executes the three cast kinds** (kernel-computed `stepMirFn` runs):
`-3.14159f32 as i32 = -3` (`0xC0490FDB ↦ 0xFFFFFFFD`), `NaN as i32 = 0`,
`f32::INFINITY as i32 = i32::MAX`, `-1i32 as f64 = -1.0`, and the `f64` signaling NaN
`0x7FF0000000000001 as f32` is quietized to `0x7FC00000`. -/
theorem fc_anneal_float_cast_runs :
    (∃ mem, ReachesRet (mirCallTree fcF2iBody [.scalar ⟨0xC0490FDB, 4⟩]) []
      (.normal (.scalar ⟨0xFFFFFFFD, 4⟩, mem))) ∧
    (∃ mem, ReachesRet (mirCallTree fcF2iBody [.scalar ⟨0x7FC00000, 4⟩]) []
      (.normal (.scalar ⟨0, 4⟩, mem))) ∧
    (∃ mem, ReachesRet (mirCallTree fcF2iBody [.scalar ⟨0x7F800000, 4⟩]) []
      (.normal (.scalar ⟨0x7FFFFFFF, 4⟩, mem))) ∧
    (∃ mem, ReachesRet (mirCallTree fcI2fBody [.scalar ⟨0xFFFFFFFF, 4⟩]) []
      (.normal (.scalar ⟨0xBFF0000000000000, 8⟩, mem))) ∧
    (∃ mem, ReachesRet (mirCallTree fcF2fBody [.scalar ⟨0x7FF0000000000001, 8⟩]) []
      (.normal (.scalar ⟨0x7FC00000, 4⟩, mem))) :=
  ⟨⟨_, runA_sound fcF2iBody 10 _ _ _ rfl⟩, ⟨_, runA_sound fcF2iBody 10 _ _ _ rfl⟩,
   ⟨_, runA_sound fcF2iBody 10 _ _ _ rfl⟩, ⟨_, runA_sound fcI2fBody 10 _ _ _ rfl⟩,
   ⟨_, runA_sound fcF2fBody 10 _ _ _ rfl⟩⟩

/-- Anneal certifies these float-cast runs free of UB. -/
theorem fc_anneal_float_cast_noUB :
    MirNoUBTree (mirCallTree fcF2iBody [.scalar ⟨0xC0490FDB, 4⟩]) ∧
    MirNoUBTree (mirCallTree fcI2fBody [.scalar ⟨0xFFFFFFFF, 4⟩]) ∧
    MirNoUBTree (mirCallTree fcF2fBody [.scalar ⟨0x7FF0000000000001, 8⟩]) :=
  ⟨runA_noUB fcF2iBody 10 _ _ _ rfl, runA_noUB fcI2fBody 10 _ _ _ rfl,
   runA_noUB fcF2fBody 10 _ _ _ rfl⟩

/-- **`f16` fails closed in Anneal** (`MirStepNode.unsupported`), and **an uninitialized `f32`
source is UB** in Anneal: no UB-free tree reaches either. -/
theorem fc_anneal_f16_unsupported_uninit_ub :
    stepMirFn fcF16Body (initMachineState fcF16Body [.scalar ⟨0x3C00, 2⟩]) =
      MirStepNode.unsupported ∧
    faultsA fcUninitBody 5 (initMachineState fcUninitBody [.scalar ⟨7, 4⟩]) = true ∧
    ¬ MirNoUBTree (mirCallTree fcUninitBody [.scalar ⟨7, 4⟩]) := by
  refine ⟨rfl, rfl, ?_⟩
  obtain ⟨tr, u, hr, hf⟩ := faultsA_sound fcUninitBody 5 (initMachineState fcUninitBody [.scalar ⟨7, 4⟩]) rfl
  exact fun hsafe => hsafe tr u hr hf

/-- **The bit carrier runs in MiniRust over both memory models**: the translated carrier body
`transmute::<u32, i32>` stores, in the caller's return place, exactly the MiniRust image of
Anneal's little-endian encoding of the carried bits, under `Interp.steps` (`BasicMemory`) and
`Interp.stepsTB` (`TreeBorrowsMemory`). Witnessed for `-3` (`0xFFFFFFFD`), `i32::MIN`
(`0x80000000`, the image of `f32::NEG_INFINITY as i32`), and `i32::MAX`. -/
theorem fc_carrier_runs :
    retAfter fcCarrierBody [.scalar ⟨0xFFFFFFFD, 4⟩] 3 =
        some (some { retAlloc with data := (encodeLittleEndianBytes 0xFFFFFFFD 4 none).map fcByteToMR },
          [1]) ∧
      retAfterTB fcCarrierBody [.scalar ⟨0xFFFFFFFD, 4⟩] 3 = tbRetU32 0xFFFFFFFD ∧
      retAfter fcCarrierBody [.scalar ⟨0x80000000, 4⟩] 3 =
        some (some { retAlloc with data := (encodeLittleEndianBytes 0x80000000 4 none).map fcByteToMR },
          [1]) ∧
      retAfterTB fcCarrierBody [.scalar ⟨0x80000000, 4⟩] 3 = tbRetU32 0x80000000 ∧
      retAfter fcCarrierBody [.scalar ⟨0x7FFFFFFF, 4⟩] 3 =
        some (some { retAlloc with data := (encodeLittleEndianBytes 0x7FFFFFFF 4 none).map fcByteToMR },
          [1]) ∧
      retAfterTB fcCarrierBody [.scalar ⟨0x7FFFFFFF, 4⟩] 3 = tbRetU32 0x7FFFFFFF := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## 8. Bit-carrier bridges: Anneal's float-cast results are exactly MiniRust's carriers -/

/-- **`float → int` bridge** (`CastKind::FloatToInt`): for every IEEE-754 source format, every
source bit pattern, and every integer target of byte width `n`, Anneal's saturating cast result
`r = evalFloatToIntSaturating` is an `n`-byte carrier whose MiniRust integer reading
(`intFromBits`) is the mathematically truncated-and-saturated value `v` (`floatToIntValue`), and
MiniRust's `Type.encode` of `v` / `Type.decode` of Anneal's bytes agree with Anneal's encoding of
`r`, byte for byte. -/
theorem fc_bridge_floatToInt (src : IeeeFormat) (bits : Nat) (t : FloatIntTarget) (n : Nat)
    (hw : t.bitWidth .bits64 = 8 * n) (hgood : GoodSize n) :
    (evalFloatToIntSaturating src bits t .bits64).sizeBytes = n ∧
    (evalFloatToIntSaturating src bits t .bits64).bits < 2 ^ (8 * n) ∧
    intFromBits (evalFloatToIntSaturating src bits t .bits64).bits
        ⟨if t.isSigned then .Signed else .Unsigned, ⟨n⟩⟩ =
      floatToIntValue (decodeBits src bits) (t.minValue .bits64) (t.maxValue .bits64) ∧
    Type.encode (.Int ⟨if t.isSigned then .Signed else .Unsigned, ⟨n⟩⟩)
        (.Int (floatToIntValue (decodeBits src bits) (t.minValue .bits64) (t.maxValue .bits64))) =
      .ok ((encodeLittleEndianBytes (evalFloatToIntSaturating src bits t .bits64).bits n
        none).map fcByteToMR) ∧
    Type.decode (.Int ⟨if t.isSigned then .Signed else .Unsigned, ⟨n⟩⟩)
        ((encodeLittleEndianBytes (evalFloatToIntSaturating src bits t .bits64).bits n
          none).map fcByteToMR) =
      .ok (some (.Int (floatToIntValue (decodeBits src bits) (t.minValue .bits64)
        (t.maxValue .bits64)))) := by
  obtain ⟨hlt, hsz⟩ := Anneal.Mir.IeeeFloatCast.evalFloatToIntSaturating_bits_lt src bits t .bits64
  obtain ⟨_, _, hval, _, _⟩ := Anneal.Mir.IeeeFloatCast.evalFloatToIntSaturating_sound src bits t .bits64
  rw [hw] at hlt hsz hval
  have hint := (fc_intValueOfBits_eq_intFromBits t.isSigned n _ hlt).symm.trans hval
  refine ⟨by rw [hsz]; omega, hlt, hint, ?_, ?_⟩
  · rw [← hint]; exact fc_mr_encode_eq_anneal _ n _ hgood hlt
  · rw [← hint]; exact fc_mr_decode_eq_anneal _ n _ none hlt

/-- The `f32 → i32` instance (`x as i32` on an `f32`): Anneal's result is the `i32` carrier of
the saturated truncation. -/
theorem fc_bridge_f32_as_i32 (bits : Nat) :
    (evalFloatToIntSaturating .binary32 bits (.signed .i32) .bits64).sizeBytes = 4 ∧
    intFromBits (evalFloatToIntSaturating .binary32 bits (.signed .i32) .bits64).bits fcI32It =
      floatToIntValue (decodeBits .binary32 bits) (-2147483648) 2147483647 ∧
    Type.decode (.Int fcI32It)
        ((encodeLittleEndianBytes (evalFloatToIntSaturating .binary32 bits (.signed .i32) .bits64).bits
          4 none).map fcByteToMR) =
      .ok (some (.Int (floatToIntValue (decodeBits .binary32 bits) (-2147483648) 2147483647))) := by
  obtain ⟨h1, _, h3, _, h5⟩ := fc_bridge_floatToInt .binary32 bits (.signed .i32) 4 rfl fc_goodSize_4
  exact ⟨h1, h3, h5⟩

/-- The `f64 → u64` instance. -/
theorem fc_bridge_f64_as_u64 (bits : Nat) :
    (evalFloatToIntSaturating .binary64 bits (.unsigned .u64) .bits64).sizeBytes = 8 ∧
    intFromBits (evalFloatToIntSaturating .binary64 bits (.unsigned .u64) .bits64).bits fcU64It =
      floatToIntValue (decodeBits .binary64 bits) 0 18446744073709551615 := by
  obtain ⟨h1, _, h3, _, _⟩ := fc_bridge_floatToInt .binary64 bits (.unsigned .u64) 8 rfl fc_goodSize_8
  exact ⟨h1, h3⟩

theorem fc_ieeeFormat_width (f : IeeeFormat) : f.width = 8 * f.byteWidth := by cases f <;> rfl

theorem fc_goodSize_byteWidth (f : IeeeFormat) : GoodSize f.byteWidth := by
  cases f
  · exact fc_goodSize_4
  · exact fc_goodSize_8

/-- **`int → float` bridge** (`CastKind::IntToFloat`): Anneal's rounded result is an in-range
`f32` / `f64` bit pattern, so MiniRust's unsigned and signed carriers of the destination width
(`u32` / `i32` for `f32`, `u64` / `i64` for `f64`) encode it as exactly Anneal's bytes and
`transmute` moves it between them unchanged (`(x as f64).to_bits()`). -/
theorem fc_bridge_intToFloat (signed : Bool) (w bits : Nat) (dst : IeeeFormat) :
    evalIntToFloatRoundTiesToEven signed w bits dst < 2 ^ (8 * dst.byteWidth) ∧
    Type.encode (.Int ⟨.Unsigned, ⟨dst.byteWidth⟩⟩)
        (.Int (evalIntToFloatRoundTiesToEven signed w bits dst : Int)) =
      .ok ((encodeLittleEndianBytes (evalIntToFloatRoundTiesToEven signed w bits dst)
        dst.byteWidth none).map fcByteToMR) ∧
    transmute (.Int (evalIntToFloatRoundTiesToEven signed w bits dst : Int))
        (.Int ⟨.Unsigned, ⟨dst.byteWidth⟩⟩) (.Int ⟨.Signed, ⟨dst.byteWidth⟩⟩) =
      .ok (.Int (intFromBits (evalIntToFloatRoundTiesToEven signed w bits dst)
        ⟨.Signed, ⟨dst.byteWidth⟩⟩)) := by
  have hlt : evalIntToFloatRoundTiesToEven signed w bits dst < 2 ^ (8 * dst.byteWidth) := by
    rw [← fc_ieeeFormat_width]; exact Anneal.Mir.IeeeFloatCast.evalIntToFloatRoundTiesToEven_lt _ _ _ _
  exact ⟨hlt, fc_mr_encode_eq_anneal .Unsigned _ _ (fc_goodSize_byteWidth dst) hlt,
    fc_mr_transmute_int .Unsigned .Signed _ _ (fc_goodSize_byteWidth dst) hlt none⟩

/-- **`float → float` bridge** (`CastKind::FloatToFloat`): Anneal's rounded result is an
in-range destination bit pattern whose MiniRust carriers encode it as exactly Anneal's bytes and
`transmute` moves it between the destination's unsigned and signed carriers unchanged. -/
theorem fc_bridge_floatToFloat (src dst : IeeeFormat) (bits : Nat) :
    evalFloatToFloatRoundTiesToEven src dst bits < 2 ^ (8 * dst.byteWidth) ∧
    Type.encode (.Int ⟨.Unsigned, ⟨dst.byteWidth⟩⟩)
        (.Int (evalFloatToFloatRoundTiesToEven src dst bits : Int)) =
      .ok ((encodeLittleEndianBytes (evalFloatToFloatRoundTiesToEven src dst bits)
        dst.byteWidth none).map fcByteToMR) ∧
    transmute (.Int (evalFloatToFloatRoundTiesToEven src dst bits : Int))
        (.Int ⟨.Unsigned, ⟨dst.byteWidth⟩⟩) (.Int ⟨.Signed, ⟨dst.byteWidth⟩⟩) =
      .ok (.Int (intFromBits (evalFloatToFloatRoundTiesToEven src dst bits)
        ⟨.Signed, ⟨dst.byteWidth⟩⟩)) := by
  have hlt : evalFloatToFloatRoundTiesToEven src dst bits < 2 ^ (8 * dst.byteWidth) := by
    rw [← fc_ieeeFormat_width]; exact Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt _ _ _
  exact ⟨hlt, fc_mr_encode_eq_anneal .Unsigned _ _ (fc_goodSize_byteWidth dst) hlt,
    fc_mr_transmute_int .Unsigned .Signed _ _ (fc_goodSize_byteWidth dst) hlt none⟩

/-! ## 9. Special bit patterns and end-to-end runs -/

/-- The special `f32` / `f64` bit patterns covered by the universal transmute theorems:
signaling NaNs (`0x7F800001`, `0x7FF0000000000001`), quiet NaNs, negative zero (`0x80000000`,
`0x8000000000000000`), the least subnormal (`0x00000001`), and the infinities. -/
theorem fc_special_bit_patterns :
    Anneal.Mir.IeeeFloatCast.isNaNBits .binary32 0x7F800001 = true ∧
    Anneal.Mir.IeeeFloatCast.isQuietNaNBits .binary32 0x7F800001 = false ∧
    Anneal.Mir.IeeeFloatCast.isQuietNaNBits .binary32 0x7FC00000 = true ∧
    Anneal.Mir.IeeeFloatCast.isNaNBits .binary64 0x7FF0000000000001 = true ∧
    Anneal.Mir.IeeeFloatCast.isQuietNaNBits .binary64 0x7FF0000000000001 = false ∧
    decodeBits .binary32 0x80000000 = .zero true ∧
    decodeBits .binary64 0x8000000000000000 = .zero true ∧
    decodeBits .binary32 0x7F800000 = .inf false ∧
    decodeBits .binary32 0xFF800000 = .inf true ∧
    decodeBits .binary64 0xFFF0000000000000 = .inf true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **Transmute vs. float cast on a signaling NaN**: `to_bits ∘ from_bits` returns the `f32`
signaling NaN `0x7F800001` unchanged (`fc_transmute_u32_to_f32` / `fc_transmute_f32_to_u32`, here
executed end to end), whereas the float-cast round trip `f32 → f64 → f32` quietizes it. -/
theorem fc_snan_transmute_vs_cast :
    (∃ mem, ReachesRet (mirCallTree fcBitsRoundTripBody [.scalar ⟨0x7F800001, 4⟩]) []
      (.normal (.scalar ⟨0x7F800001, 4⟩, mem))) ∧
    evalFloatToFloatRoundTiesToEven .binary64 .binary32
        (evalFloatToFloatRoundTiesToEven .binary32 .binary64 0x7F800001) ≠ 0x7F800001 ∧
    Anneal.Mir.IeeeFloatCast.isQuietNaNBits .binary32 (evalFloatToFloatRoundTiesToEven .binary64
        .binary32 (evalFloatToFloatRoundTiesToEven .binary32 .binary64 0x7F800001)) = true :=
  ⟨⟨_, runA_sound fcBitsRoundTripBody 10 _ _ _ rfl⟩, by decide +kernel, by decide +kernel⟩

/-- **End-to-end `stepMirFn` runs through the bit carriers** (`from_bits`, a float cast,
`to_bits`): `f32::from_bits(0xC0490FDB) as i32 = -3`, `f32::NEG_INFINITY as i32 = i32::MIN`,
`f32::from_bits(0x7F800001) as i32 = 0` (signaling NaN), `-0.0 as i32 = 0`, the least subnormal
truncates to `0`, `2^31 as i32` saturates to `i32::MAX`; `(-1i32 as f64).to_bits() =
0xBFF0000000000000`, `(i32::MIN as f64).to_bits() = 0xC1E0000000000000`; and widening
`f32 → f64` maps the signaling NaN `0x7F800001` to the quiet NaN `0x7FF8000020000000` (payload
kept), `-0.0` to `-0.0`, and the least `f32` subnormal `2^-149` exactly to `0x36A0000000000000`. -/
theorem fc_e2e_bit_carrier_runs :
    (∃ mem, ReachesRet (mirCallTree fcFromBitsAsI32Body [.scalar ⟨0xC0490FDB, 4⟩]) []
      (.normal (.scalar ⟨0xFFFFFFFD, 4⟩, mem))) ∧
    (∃ mem, ReachesRet (mirCallTree fcFromBitsAsI32Body [.scalar ⟨0xFF800000, 4⟩]) []
      (.normal (.scalar ⟨0x80000000, 4⟩, mem))) ∧
    (∃ mem, ReachesRet (mirCallTree fcFromBitsAsI32Body [.scalar ⟨0x7F800001, 4⟩]) []
      (.normal (.scalar ⟨0, 4⟩, mem))) ∧
    (∃ mem, ReachesRet (mirCallTree fcFromBitsAsI32Body [.scalar ⟨0x80000000, 4⟩]) []
      (.normal (.scalar ⟨0, 4⟩, mem))) ∧
    (∃ mem, ReachesRet (mirCallTree fcFromBitsAsI32Body [.scalar ⟨0x00000001, 4⟩]) []
      (.normal (.scalar ⟨0, 4⟩, mem))) ∧
    (∃ mem, ReachesRet (mirCallTree fcFromBitsAsI32Body [.scalar ⟨0x4F000000, 4⟩]) []
      (.normal (.scalar ⟨0x7FFFFFFF, 4⟩, mem))) ∧
    (∃ mem, ReachesRet (mirCallTree fcIntAsF64BitsBody [.scalar ⟨0xFFFFFFFF, 4⟩]) []
      (.normal (.scalar ⟨0xBFF0000000000000, 8⟩, mem))) ∧
    (∃ mem, ReachesRet (mirCallTree fcIntAsF64BitsBody [.scalar ⟨0x80000000, 4⟩]) []
      (.normal (.scalar ⟨0xC1E0000000000000, 8⟩, mem))) ∧
    (∃ mem, ReachesRet (mirCallTree fcWidenBitsBody [.scalar ⟨0x7F800001, 4⟩]) []
      (.normal (.scalar ⟨0x7FF8000020000000, 8⟩, mem))) ∧
    (∃ mem, ReachesRet (mirCallTree fcWidenBitsBody [.scalar ⟨0x80000000, 4⟩]) []
      (.normal (.scalar ⟨0x8000000000000000, 8⟩, mem))) ∧
    (∃ mem, ReachesRet (mirCallTree fcWidenBitsBody [.scalar ⟨0x00000001, 4⟩]) []
      (.normal (.scalar ⟨0x36A0000000000000, 8⟩, mem))) :=
  ⟨⟨_, runA_sound fcFromBitsAsI32Body 12 _ _ _ rfl⟩, ⟨_, runA_sound fcFromBitsAsI32Body 12 _ _ _ rfl⟩,
   ⟨_, runA_sound fcFromBitsAsI32Body 12 _ _ _ rfl⟩, ⟨_, runA_sound fcFromBitsAsI32Body 12 _ _ _ rfl⟩,
   ⟨_, runA_sound fcFromBitsAsI32Body 12 _ _ _ rfl⟩, ⟨_, runA_sound fcFromBitsAsI32Body 12 _ _ _ rfl⟩,
   ⟨_, runA_sound fcIntAsF64BitsBody 12 _ _ _ rfl⟩, ⟨_, runA_sound fcIntAsF64BitsBody 12 _ _ _ rfl⟩,
   ⟨_, runA_sound fcWidenBitsBody 12 _ _ _ rfl⟩, ⟨_, runA_sound fcWidenBitsBody 12 _ _ _ rfl⟩,
   ⟨_, runA_sound fcWidenBitsBody 12 _ _ _ rfl⟩⟩

/-- **End-to-end bridge, both semantics**: `f32::NEG_INFINITY as i32` runs in Anneal to the
`i32` carrier `0x80000000`; feeding that carrier through the translated MiniRust carrier body
stores exactly Anneal's bytes under `BasicMemory` and `TreeBorrowsMemory`; and MiniRust decodes
those bytes to `i32::MIN = floatToIntValue (-∞)`. -/
theorem fc_e2e_neg_inf_as_i32_both :
    (∃ mem, ReachesRet (mirCallTree fcFromBitsAsI32Body [.scalar ⟨0xFF800000, 4⟩]) []
      (.normal (.scalar ⟨0x80000000, 4⟩, mem))) ∧
    retAfter fcCarrierBody [.scalar ⟨0x80000000, 4⟩] 3 =
      some (some { retAlloc with data := (encodeLittleEndianBytes 0x80000000 4 none).map fcByteToMR },
        [1]) ∧
    retAfterTB fcCarrierBody [.scalar ⟨0x80000000, 4⟩] 3 = tbRetU32 0x80000000 ∧
    Type.decode (.Int fcI32It) ((encodeLittleEndianBytes 0x80000000 4 none).map fcByteToMR) =
      .ok (some (.Int (floatToIntValue (decodeBits .binary32 0xFF800000) (-2147483648)
        2147483647))) ∧
    floatToIntValue (decodeBits .binary32 0xFF800000) (-2147483648) 2147483647 = -2147483648 := by
  refine ⟨(fc_e2e_bit_carrier_runs).2.1, (fc_carrier_runs).2.2.1, (fc_carrier_runs).2.2.2.1, ?_,
    by decide +kernel⟩
  rw [show fcI32It = ⟨.Signed, ⟨4⟩⟩ from rfl,
    fc_mr_decode_eq_anneal .Signed 4 0x80000000 none (by decide)]
  exact congrArg (fun z : Int => (Except.ok (some (Gen.Value.Int z)) : Interp (Option Val)))
    (by decide +kernel)

/-! ## 10. Symbolic multi-step `stepMirFn` executions through the bit carriers -/

/-- Anneal's little-endian encode-then-decode of the low `n` bytes of `x`. -/
def fcLeRound (n x : Nat) : Nat :=
  match decodeLittleEndianBytes (encodeLittleEndianBytes x n none) with
  | some (b, _) => b
  | none => 0

theorem fcLeRound_eq (n x : Nat) (h : x < 256 ^ (n + 1)) : fcLeRound (n + 1) x = x := by
  unfold fcLeRound
  rw [fc_decodeLittleEndianBytes_encode none n x h]

theorem fcLeRound_eq4 (x : Nat) (h : x < 2 ^ 32) : fcLeRound 4 x = x :=
  fcLeRound_eq 3 x (fc_lt_256_pow_4 h)

theorem fcLeRound_eq8 (x : Nat) (h : x < 2 ^ 64) : fcLeRound 8 x = x :=
  fcLeRound_eq 7 x (fc_lt_256_pow_8 h)

/-- Kernel-computed symbolic run of `f32::from_bits(x).to_bits()`: each transmute is one
little-endian encode/decode round (`fcLeRound`). -/
theorem fc_run_bits_round_trip_raw (bits : Nat) : ∃ mem, runA fcBitsRoundTripBody 10
    (initMachineState fcBitsRoundTripBody [.scalar ⟨bits, 4⟩]) =
      some ([], .normal (.scalar ⟨fcLeRound 4 (fcLeRound 4 bits), 4⟩, mem)) := ⟨_, rfl⟩

/-- Kernel-computed symbolic run of `f32::from_bits(x) as i32`. -/
theorem fc_run_from_bits_as_i32_raw (bits : Nat) : ∃ mem, runA fcFromBitsAsI32Body 10
    (initMachineState fcFromBitsAsI32Body [.scalar ⟨bits, 4⟩]) =
      some ([], .normal (.scalar (evalFloatToIntSaturating .binary32 (fcLeRound 4 bits)
        (.signed .i32) .bits64), mem)) := ⟨_, rfl⟩

/-- Kernel-computed symbolic run of `(x as f64).to_bits()` on `x : i32`. -/
theorem fc_run_int_as_f64_bits_raw (bits : Nat) : ∃ mem, runA fcIntAsF64BitsBody 10
    (initMachineState fcIntAsF64BitsBody [.scalar ⟨bits, 4⟩]) =
      some ([], .normal (.scalar ⟨fcLeRound 8 (evalIntToFloatRoundTiesToEven true 32 bits .binary64),
        8⟩, mem)) := ⟨_, rfl⟩

/-- Kernel-computed symbolic run of `(f32::from_bits(x) as f64).to_bits()`. -/
theorem fc_run_widen_bits_raw (bits : Nat) : ∃ mem, runA fcWidenBitsBody 12
    (initMachineState fcWidenBitsBody [.scalar ⟨bits, 4⟩]) =
      some ([], .normal (.scalar ⟨fcLeRound 8 (evalFloatToFloatRoundTiesToEven .binary32 .binary64
        (fcLeRound 4 bits)), 8⟩, mem)) := ⟨_, rfl⟩

/-- **Symbolic `to_bits ∘ from_bits = id`**: for *every* 32-bit pattern (signaling NaNs, `-0.0`,
subnormals, infinities included), Anneal's multi-step execution of
`f32::from_bits(x).to_bits()` returns `x` unchanged, free of UB. -/
theorem fc_sym_bits_round_trip (bits : Nat) (h : bits < 2 ^ 32) :
    (∃ mem, ReachesRet (mirCallTree fcBitsRoundTripBody [.scalar ⟨bits, 4⟩]) []
      (.normal (.scalar ⟨bits, 4⟩, mem))) ∧
    MirNoUBTree (mirCallTree fcBitsRoundTripBody [.scalar ⟨bits, 4⟩]) := by
  obtain ⟨mem, hrun⟩ := fc_run_bits_round_trip_raw bits
  rw [fcLeRound_eq4 bits h, fcLeRound_eq4 bits h] at hrun
  exact ⟨⟨mem, runA_sound _ _ _ _ _ hrun⟩, runA_noUB _ _ _ _ _ hrun⟩

/-- **Symbolic `f32::from_bits(x) as i32`**: for every 32-bit pattern, Anneal's multi-step
execution returns exactly `evalFloatToIntSaturating .binary32 x (.signed .i32)`, free of UB. -/
theorem fc_sym_from_bits_as_i32 (bits : Nat) (h : bits < 2 ^ 32) :
    (∃ mem, ReachesRet (mirCallTree fcFromBitsAsI32Body [.scalar ⟨bits, 4⟩]) []
      (.normal (.scalar (evalFloatToIntSaturating .binary32 bits (.signed .i32) .bits64), mem))) ∧
    MirNoUBTree (mirCallTree fcFromBitsAsI32Body [.scalar ⟨bits, 4⟩]) := by
  obtain ⟨mem, hrun⟩ := fc_run_from_bits_as_i32_raw bits
  rw [fcLeRound_eq4 bits h] at hrun
  exact ⟨⟨mem, runA_sound _ _ _ _ _ hrun⟩, runA_noUB _ _ _ _ _ hrun⟩

/-- **Symbolic `(x as f64).to_bits()`** on `x : i32`: for every 32-bit pattern, Anneal returns
the `f64` carrier `evalIntToFloatRoundTiesToEven true 32 x .binary64`, free of UB. -/
theorem fc_sym_int_as_f64_bits (bits : Nat) :
    (∃ mem, ReachesRet (mirCallTree fcIntAsF64BitsBody [.scalar ⟨bits, 4⟩]) []
      (.normal (.scalar ⟨evalIntToFloatRoundTiesToEven true 32 bits .binary64, 8⟩, mem))) ∧
    MirNoUBTree (mirCallTree fcIntAsF64BitsBody [.scalar ⟨bits, 4⟩]) := by
  obtain ⟨mem, hrun⟩ := fc_run_int_as_f64_bits_raw bits
  rw [fcLeRound_eq8 _ (Anneal.Mir.IeeeFloatCast.evalIntToFloatRoundTiesToEven_lt _ _ _ _)] at hrun
  exact ⟨⟨mem, runA_sound _ _ _ _ _ hrun⟩, runA_noUB _ _ _ _ _ hrun⟩

/-- **Symbolic `(f32::from_bits(x) as f64).to_bits()`**: for every 32-bit pattern, Anneal
returns the `f64` carrier `evalFloatToFloatRoundTiesToEven .binary32 .binary64 x`, free of UB. -/
theorem fc_sym_widen_bits (bits : Nat) (h : bits < 2 ^ 32) :
    (∃ mem, ReachesRet (mirCallTree fcWidenBitsBody [.scalar ⟨bits, 4⟩]) []
      (.normal (.scalar ⟨evalFloatToFloatRoundTiesToEven .binary32 .binary64 bits, 8⟩, mem))) ∧
    MirNoUBTree (mirCallTree fcWidenBitsBody [.scalar ⟨bits, 4⟩]) := by
  obtain ⟨mem, hrun⟩ := fc_run_widen_bits_raw bits
  rw [fcLeRound_eq4 bits h,
    fcLeRound_eq8 _ (Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt _ _ _)] at hrun
  exact ⟨⟨mem, runA_sound _ _ _ _ _ hrun⟩, runA_noUB _ _ _ _ _ hrun⟩

/-- **Symbolic end-to-end bit-carrier bridge (`FloatToInt`)**: for every 32-bit pattern `x`,
Anneal's multi-step run of `f32::from_bits(x) as i32` returns a carrier `r` whose bytes MiniRust
decodes at `i32` to the saturated truncation `floatToIntValue (decodeBits .binary32 x)`, and which
MiniRust's `transmuteM` moves from the `u32` carrier to `i32` with that same value over both
`BasicMemory` and `TreeBorrowsMemory`. -/
theorem fc_sym_e2e_from_bits_as_i32 (bits : Nat) (h : bits < 2 ^ 32) :
    (∃ mem, ReachesRet (mirCallTree fcFromBitsAsI32Body [.scalar ⟨bits, 4⟩]) []
      (.normal (.scalar (evalFloatToIntSaturating .binary32 bits (.signed .i32) .bits64), mem))) ∧
    Type.decode (.Int fcI32It)
        ((encodeLittleEndianBytes (evalFloatToIntSaturating .binary32 bits (.signed .i32)
          .bits64).bits 4 none).map fcByteToMR) =
      .ok (some (.Int (floatToIntValue (decodeBits .binary32 bits) (-2147483648) 2147483647))) ∧
    transmuteM (M := BM)
        (.Int (intFromBits (evalFloatToIntSaturating .binary32 bits (.signed .i32) .bits64).bits
          fcU32It)) (.Int fcU32It) (.Int fcI32It) =
      .ok (.Int (floatToIntValue (decodeBits .binary32 bits) (-2147483648) 2147483647)) ∧
    transmuteM (M := TBM)
        (.Int (intFromBits (evalFloatToIntSaturating .binary32 bits (.signed .i32) .bits64).bits
          fcU32It)) (.Int fcU32It) (.Int fcI32It) =
      .ok (.Int (floatToIntValue (decodeBits .binary32 bits) (-2147483648) 2147483647)) := by
  obtain ⟨_, hlt, hint, _, hdec⟩ :=
    fc_bridge_floatToInt .binary32 bits (.signed .i32) 4 rfl fc_goodSize_4
  refine ⟨(fc_sym_from_bits_as_i32 bits h).1, hdec, ?_, ?_⟩
  · exact (fc_mrBM_transmute_int .Unsigned .Signed 4 _ fc_goodSize_4 hlt none).trans
      (congrArg (fun z : Int => (Except.ok (Gen.Value.Int z) : Interp Val)) hint)
  · exact (fc_mrTB_transmute_int .Unsigned .Signed 4 _ fc_goodSize_4 hlt none).trans
      (congrArg (fun z : Int => (Except.ok (Gen.Value.Int z) : Interp (Gen.Value TBM))) hint)

/-- **Symbolic end-to-end bit-carrier bridge (`FloatToFloat`)**: for every 32-bit pattern `x`,
Anneal's multi-step run of `(f32::from_bits(x) as f64).to_bits()` returns the `u64` carrier
`r = evalFloatToFloatRoundTiesToEven .binary32 .binary64 x`, whose MiniRust `Type.encode` is
exactly Anneal's little-endian bytes and which MiniRust's `transmuteM` moves to `i64` unchanged
over both `BasicMemory` and `TreeBorrowsMemory`. -/
theorem fc_sym_e2e_widen_bits (bits : Nat) (h : bits < 2 ^ 32) :
    (∃ mem, ReachesRet (mirCallTree fcWidenBitsBody [.scalar ⟨bits, 4⟩]) []
      (.normal (.scalar ⟨evalFloatToFloatRoundTiesToEven .binary32 .binary64 bits, 8⟩, mem))) ∧
    Type.encode (.Int fcU64It)
        (.Int (intFromBits (evalFloatToFloatRoundTiesToEven .binary32 .binary64 bits) fcU64It)) =
      .ok ((encodeLittleEndianBytes (evalFloatToFloatRoundTiesToEven .binary32 .binary64 bits) 8
        none).map fcByteToMR) ∧
    transmuteM (M := BM)
        (.Int (intFromBits (evalFloatToFloatRoundTiesToEven .binary32 .binary64 bits) fcU64It))
        (.Int fcU64It) (.Int fcI64It) =
      .ok (.Int (intFromBits (evalFloatToFloatRoundTiesToEven .binary32 .binary64 bits) fcI64It)) ∧
    transmuteM (M := TBM)
        (.Int (intFromBits (evalFloatToFloatRoundTiesToEven .binary32 .binary64 bits) fcU64It))
        (.Int fcU64It) (.Int fcI64It) =
      .ok (.Int (intFromBits (evalFloatToFloatRoundTiesToEven .binary32 .binary64 bits) fcI64It)) := by
  have hlt : evalFloatToFloatRoundTiesToEven .binary32 .binary64 bits < 2 ^ (8 * 8) :=
    Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt _ _ _
  exact ⟨(fc_sym_widen_bits bits h).1, fc_mr_encode_eq_anneal .Unsigned 8 _ fc_goodSize_8 hlt,
    fc_mrBM_transmute_int .Unsigned .Signed 8 _ fc_goodSize_8 hlt none,
    fc_mrTB_transmute_int .Unsigned .Signed 8 _ fc_goodSize_8 hlt none⟩

/-- `fn ptr_to_f64(x: u32) -> f64 { transmute::<*const u32, f64>(&raw const x) }`:
`_2 = &raw const _1; _0 = copy _2 as f64 (Transmute)`. -/
def fcPtrToF64Body : CapturedMir :=
  fcBody "float_cast::ptr_to_f64" [fcDecl fcF64Ty, fcDecl fcU32Ty, fcDecl fcRawPtrU32Ty]
    [.storageLive 2,
     .assign (local_ 2) (.rawPtr .not (local_ 1)),
     .assign (local_ 0) (.cast .transmute (.copy (local_ 2)) fcF64Ty),
     .storageDead 2]

/-- **Pointer bytes transmuted to `f64` are UB in Anneal** (end to end): no UB-free tree reaches
the run of `fcPtrToF64Body`, which `translateFn` also rejects (float local). -/
theorem fc_ptr_to_f64_ub_run :
    faultsA fcPtrToF64Body 10 (initMachineState fcPtrToF64Body [.scalar ⟨7, 4⟩]) = true ∧
    ¬ MirNoUBTree (mirCallTree fcPtrToF64Body [.scalar ⟨7, 4⟩]) ∧
    translateFn fcPtrToF64Body = none := by
  refine ⟨rfl, ?_, rfl⟩
  obtain ⟨tr, u, hr, hf⟩ :=
    faultsA_sound fcPtrToF64Body 10 (initMachineState fcPtrToF64Body [.scalar ⟨7, 4⟩]) rfl
  exact fun hsafe => hsafe tr u hr hf

/-- **`statementOk` rejects every float-cast assignment to a local** (so no fragment body contains
one), for every local list, layout table, operand, and cast type. -/
theorem fc_statementOk_float_cast (decls : List LocalDecl) (i : Nat) (k : CastKind)
    (hk : fcIsFloatCastKind k = true) (op : Operand) (ty : Ty) (span : String)
    (layouts : LayoutTable) :
    statementOk decls ⟨.assign ⟨i, []⟩ (.cast k op ty), span⟩ layouts = false := by
  cases k <;> simp [fcIsFloatCastKind] at hk <;>
  · simp only [statementOk, copyRv]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · split
            · simp [rvalueOk, ptrDerefReadOk]
            · split
              · rfl
              · split
                · rfl
                · split <;> rfl

/-- **MiniRust's `[u8; 4]` / `[u8; 8]` carriers** (`f32::to_le_bytes`, `f64::to_le_bytes` as
MiniRust sees them): `transmute` from `u32` / `u64` to the byte array yields the little-endian
bytes, and back again, for the special patterns `-0.0`, the `f32` signaling NaN, `-∞`, and the
least `f64` subnormal. -/
theorem fc_mr_transmute_byte_arrays :
    transmute (.Int 0x80000000) (.Int fcU32It) (.Array (.Int fcU8It) 4) =
        .ok (.Tuple (fcLeByteValsMR 0x80000000 4)) ∧
      transmute (.Tuple (fcLeByteValsMR 0x7F800001 4)) (.Array (.Int fcU8It) 4) (.Int fcU32It) =
        .ok (.Int 0x7F800001) ∧
      transmute (.Int 0xFFF0000000000000) (.Int fcU64It) (.Array (.Int fcU8It) 8) =
        .ok (.Tuple (fcLeByteValsMR 0xFFF0000000000000 8)) ∧
      transmute (.Tuple (fcLeByteValsMR 1 8)) (.Array (.Int fcU8It) 8) (.Int fcU64It) =
        .ok (.Int 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-! ## 11. Strengthened fragment boundaries, layout-parametric transmutes, and signed two's-complement carriers -/

/-- Safe pointers to floats (`&ft`, `&mut ft`, `Box<ft>`) are rejected by `translateTy`, whereas
raw pointers (`*const ft`, `*mut ft`) erase their pointee to `PointerMetaKind::None` in
`translateTy` yet are rejected by `rawPtrPointeeOf` and `localDeclOk` (hence by `inFragment`). -/
theorem fc_ptr_ref_box_float_boundary (layouts : LayoutTable) (mutbl : MirAst.Mutability)
    (ft : FloatTy) (idx : Nat) (declMut : MirAst.Mutability) (dbg : Option String) :
    refTypeOf ⟨.ref mutbl (.float ft), idx⟩ = none ∧
    translateTy layouts ⟨.ref mutbl (.float ft), idx⟩ = none ∧
    boxTypeOf ⟨.adt "alloc::boxed::Box" [.float ft], idx⟩ = none ∧
    translateTy layouts ⟨.rawPtr mutbl (.float ft), idx⟩ = some (.Ptr (.Raw .None)) ∧
    rawPtrPointeeOf ⟨.rawPtr mutbl (.float ft), idx⟩ = none ∧
    localDeclOk layouts (LocalDecl.mk declMut ⟨.rawPtr mutbl (.float ft), idx⟩ dbg) = false ∧
    localDeclOk layouts (LocalDecl.mk declMut ⟨.float ft, idx⟩ dbg) = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp [localDeclOk, scalarTypeOf, isBoolTy, isOrderingTy, intBoolTupleOf, intTypeOf, intTyBytes,
      isPtrTy, ptrPointeeOf, arrayTypeOf, tupleTypeOf]
  · simp [localDeclOk, scalarTypeOf, isBoolTy, isOrderingTy, intBoolTupleOf, intTypeOf, intTyBytes,
      isPtrTy, ptrPointeeOf, arrayTypeOf, tupleTypeOf]

/-- Helper: `List.mapM f xs = none` whenever an element of `xs` maps to `none`. -/
theorem fc_list_mapM_option_eq_none {α β : Type} (f : α → Option β) :
    ∀ (xs : List α), (∃ x ∈ xs, f x = none) → xs.mapM f = none
  | [], ⟨_, hx, _⟩ => by simp at hx
  | x :: rest, ⟨y, hy, hfy⟩ => by
    rcases List.mem_cons.mp hy with rfl | hmem
    · simp [List.mapM_cons, hfy]
    · have ih := fc_list_mapM_option_eq_none f rest ⟨y, hmem, hfy⟩
      simp only [List.mapM_cons]
      cases f x with
      | none => rfl
      | some _ => simp [ih]

/-- `translateBlock` fails whenever any statement in the block fails `translateStatement`. -/
theorem fc_translateBlock_eq_none_of_stmt (layouts : LayoutTable) (decls : List LocalDecl)
    (bb : BasicBlockData) (h : ∃ s ∈ bb.statements, translateStatement decls s layouts = none) :
    translateBlock layouts decls bb = none := by
  unfold translateBlock
  rw [fc_list_mapM_option_eq_none (translateStatement decls · layouts) bb.statements h]
  rfl

/-- `translateBlocks` fails whenever any block in the list fails `translateBlock`. -/
theorem fc_translateBlocks_eq_none_of_block (layouts : LayoutTable) (decls : List LocalDecl) :
    ∀ (i : Nat) (bbs : List BasicBlockData),
      (∃ bb ∈ bbs, translateBlock layouts decls bb = none) →
      translateBlocks layouts decls i bbs = none
  | _, [], ⟨_, hbb, _⟩ => by simp at hbb
  | i, bb :: rest, ⟨bb', hbb, hnone⟩ => by
    rcases List.mem_cons.mp hbb with rfl | hmem
    · simp [translateBlocks, hnone]
    · have ih := fc_translateBlocks_eq_none_of_block layouts decls (i + 1) rest ⟨bb', hmem, hnone⟩
      simp only [translateBlocks]
      cases translateBlock layouts decls bb with
      | none => rfl
      | some _ => simp [ih]

/-- **Local-free whole-function rejection**: `translateFn` and `inFragment` reject *every* MIR body
containing a float-cast assignment (or transmute-to-float assignment) in any basic block, **even if
the body declares zero float locals** (e.g. casting a float constant directly into an integer
local). -/
theorem fc_translateFn_and_inFragment_of_float_cast_stmt (body : CapturedMir)
    (h : ∃ bb ∈ body.basicBlocks, ∃ s ∈ bb.statements,
      ∃ (dst : Place) (k : CastKind) (op : Operand) (ty : Ty) (span : String),
        fcIsFloatCastKind k = true ∧ s = ⟨.assign dst (.cast k op ty), span⟩) :
    translateFn body = none ∧ inFragment body = false := by
  obtain ⟨bb, hbb, s, hs, dst, k, op, ty, span, hk, rfl⟩ := h
  have hstmt := fc_translateStatement_float_cast body.localDecls dst k hk op ty span body.layouts
  have hblk := fc_translateBlock_eq_none_of_stmt body.layouts body.localDecls bb ⟨_, hs, hstmt⟩
  have hblks := fc_translateBlocks_eq_none_of_block body.layouts body.localDecls 0 body.basicBlocks
    ⟨bb, hbb, hblk⟩
  have hfn : translateFn body = none := by
    unfold translateFn
    cases translateCallConv body.fnAbi.conv with
    | none => rfl
    | some _ =>
      cases translateLocals body.layouts 0 body.localDecls with
      | none => rfl
      | some _ => simp [hblks]
  exact ⟨hfn, by simp [inFragment, hfn]⟩

/-- `translateBlocksWithIntrinsics` fails whenever any statement fails `translateStmtOrIntrinsic`. -/
theorem fc_translateBlocksWithIntrinsics_eq_none (layouts : LayoutTable) (decls : List LocalDecl) :
    ∀ (i nextFresh : Nat) (bbs : List BasicBlockData),
      (∃ bb ∈ bbs, ∃ s ∈ bb.statements, translateStmtOrIntrinsic decls s layouts = none) →
      translateBlocksWithIntrinsics layouts decls i nextFresh bbs = none
  | _, _, [], ⟨_, hbb, _⟩ => by simp at hbb
  | i, nf, bb :: rest, ⟨bb', hbb, hs⟩ => by
    rcases List.mem_cons.mp hbb with rfl | hmem
    · simp only [translateBlocksWithIntrinsics,
        fc_list_mapM_option_eq_none (translateStmtOrIntrinsic decls · layouts) bb'.statements hs]
      rfl
    · simp only [translateBlocksWithIntrinsics]
      cases bb.statements.mapM (translateStmtOrIntrinsic decls · layouts) with
      | none => rfl
      | some trs =>
        cases translateTerminator layouts decls bb.terminator with
        | none => rfl
        | some term =>
          simp [fc_translateBlocksWithIntrinsics_eq_none layouts decls (i + 1) _ rest
            ⟨bb', hmem, hs⟩]

/-- **`translateFnWithIntrinsics` rejects float locals and float-cast statements alike.** -/
theorem fc_translateFnWithIntrinsics_float_rejected (body : CapturedMir) :
    ((∃ d ∈ body.localDecls, ∃ (ft : FloatTy) (idx : Nat), d.ty = ⟨.float ft, idx⟩) →
      translateFnWithIntrinsics body = none) ∧
    ((∃ bb ∈ body.basicBlocks, ∃ s ∈ bb.statements,
        ∃ (dst : Place) (k : CastKind) (op : Operand) (ty : Ty) (span : String),
          fcIsFloatCastKind k = true ∧ s = ⟨.assign dst (.cast k op ty), span⟩) →
      translateFnWithIntrinsics body = none) := by
  refine ⟨fun hloc => ?_, fun hst => ?_⟩
  · have hl := fc_translateLocals_eq_none_of_float body.layouts 0 body.localDecls hloc
    unfold translateFnWithIntrinsics
    cases translateCallConv body.fnAbi.conv <;> simp [hl]
  · obtain ⟨bb, hbb, s, hs, dst, k, op, ty, span, hk, rfl⟩ := hst
    have hso : translateStmtOrIntrinsic body.localDecls ⟨.assign dst (.cast k op ty), span⟩
        body.layouts = none := by
      have hst0 := fc_translateStatement_float_cast body.localDecls dst k hk op ty span body.layouts
      cases k <;> simp [fcIsFloatCastKind] at hk <;> simp [translateStmtOrIntrinsic, hst0]
    have hblks := fc_translateBlocksWithIntrinsics_eq_none body.layouts body.localDecls 0
      body.basicBlocks.length body.basicBlocks ⟨bb, hbb, _, hs, hso⟩
    unfold translateFnWithIntrinsics
    cases translateCallConv body.fnAbi.conv with
    | none => rfl
    | some _ =>
      cases translateLocals body.layouts 0 body.localDecls with
      | none => rfl
      | some _ => simp [hblks]

/-- **`progInFragment` rejects float locals and float-cast statements in *any* function of
`entry :: callees` (not only `entry`).** -/
theorem fc_progInFragment_any_fn_rejected (entry : CapturedMir) (callees : List CapturedMir)
    (b : CapturedMir) (hb : b ∈ entry :: callees)
    (h : (∃ d ∈ b.localDecls, ∃ (ft : FloatTy) (idx : Nat), d.ty = ⟨.float ft, idx⟩) ∨
      (∃ bb ∈ b.basicBlocks, ∃ s ∈ bb.statements,
        ∃ (dst : Place) (k : CastKind) (op : Operand) (ty : Ty) (span : String),
          fcIsFloatCastKind k = true ∧ s = ⟨.assign dst (.cast k op ty), span⟩)) :
    progInFragment entry callees = false := by
  have hfn : translateFnInProg (fnNameMap entry callees) b = none := by
    rcases h with ⟨d, hd, ft, idx, hty⟩ | ⟨bb, hbb, s, hs, dst, k, op, ty, span, hk, rfl⟩
    · have hl := fc_translateLocals_eq_none_of_float b.layouts 0 b.localDecls ⟨d, hd, ft, idx, hty⟩
      unfold translateFnInProg
      cases translateCallConv b.fnAbi.conv <;> simp [hl]
    · have hsr : translateStmtResult b.localDecls ⟨.assign dst (.cast k op ty), span⟩ b.layouts =
          none := by
        simp [translateStmtResult,
          fc_translateStatement_float_cast b.localDecls dst k hk op ty span b.layouts]
      have hblks : ∀ (i nc : Nat) (bbs : List BasicBlockData),
          bb ∈ bbs → translateBlocksInProg (fnNameMap entry callees) b.layouts b.localDecls i nc
            bbs = none := by
        intro i nc bbs hmem
        induction bbs generalizing i nc with
        | nil => simp at hmem
        | cons bb0 rest ih =>
          rcases List.mem_cons.mp hmem with heq | hrest
          · subst heq
            simp only [translateBlocksInProg,
              fc_list_mapM_option_eq_none (translateStmtResult b.localDecls · b.layouts)
                bb.statements ⟨_, hs, hsr⟩]
            rfl
          · simp only [translateBlocksInProg]
            cases bb0.statements.mapM (translateStmtResult b.localDecls · b.layouts) with
            | none => rfl
            | some rs =>
              simp only [bind, Option.bind]
              cases translateTerminatorInProg (fnNameMap entry callees) b.layouts b.localDecls
                  (splitStmts (bbName i) [] nc rs).2.2.2 bb0.terminator with
              | none => rfl
              | some t => simp [ih (i + 1) t.2.1 hrest]
      unfold translateFnInProg
      cases translateCallConv b.fnAbi.conv with
      | none => rfl
      | some _ =>
        cases translateLocals b.layouts 0 b.localDecls with
        | none => rfl
        | some _ => simp [hblks 0 (b.basicBlocks.length + 1) b.basicBlocks hbb]
  have hpfns : ∀ (idx : Nat) (fns : List CapturedMir),
      b ∈ fns → translateProgFns (fnNameMap entry callees) idx fns = none := by
    intro idx fns hmem
    induction fns generalizing idx with
    | nil => simp at hmem
    | cons b0 rest ih =>
      rcases List.mem_cons.mp hmem with rfl | hrest
      · simp [translateProgFns, hfn]
      · simp only [translateProgFns]
        cases translateFnInProg (fnNameMap entry callees) b0 with
        | none => rfl
        | some _ => simp [ih (idx + 1) hrest]
  have hprog : translateProg entry callees = none := by
    simp [translateProg, hpfns 0 (entry :: callees) hb]
  simp [progInFragment, hprog]

/-- Concrete float-local-free witness: `fn const_f32_as_i32(_x: u32) -> i32 { -3.14159f32 as i32 }`
has only integer locals (`translateLocals` succeeds!), executes cleanly in Anneal to `-3`, and is
nonetheless rejected at the statement/block level by `translateFn` and `inFragment`. -/
def fcConstF32CastBody : CapturedMir :=
  fcBody "float_cast::const_f32_as_i32" [fcDecl fcI32Ty, fcDecl fcU32Ty]
    [.assign (local_ 0) (.cast .floatToInt
      (.constant { ty := fcF32Ty, val := .scalar (.int ⟨0xC0490FDB, 4⟩) }) fcI32Ty)]

theorem fc_const_f32_cast_witness :
    (translateLocals fcConstF32CastBody.layouts 0 fcConstF32CastBody.localDecls).isSome = true ∧
    (∃ mem, ReachesRet (mirCallTree fcConstF32CastBody [.scalar ⟨0, 4⟩]) []
      (.normal (.scalar ⟨0xFFFFFFFD, 4⟩, mem))) ∧
    MirNoUBTree (mirCallTree fcConstF32CastBody [.scalar ⟨0, 4⟩]) ∧
    translateFn fcConstF32CastBody = none ∧
    inFragment fcConstF32CastBody = false :=
  ⟨rfl, ⟨_, runA_sound fcConstF32CastBody 10 _ _ _ rfl⟩,
   runA_noUB fcConstF32CastBody 10 _ _ _ rfl, rfl, rfl⟩

/-- `u16` and `u128` types in `fcLayouts` (for the `f16` / `f128` transmute dichotomy). -/
def fcU16Ty : Ty := { kind := .uint .u16, layoutIdx := 13 }
def fcU128Ty : Ty := { kind := .uint .u128, layoutIdx := 14 }

/-- Layout-parametric `f32 ↔ u32 / i32` and `f64 ↔ u64 / i64` decoding for *any* `LayoutTable`!
Because `normalizeCodecTy` rewrites `.float .f32` to `{ kind := .uint .u32, layoutIdx := 0 }` and
`.float .f64` to `{ kind := .uint .u64, layoutIdx := 0 }`, decoding `encodeLittleEndianBytes` at
any `Ty` with `.kind ∈ {.float .f32, .uint .u32, .int .i32}` (or `.f64 / .u64 / .i64`) is completely
independent of `layouts` and `ty.layoutIdx`! -/
theorem fc_decodeTyped_any_layouts (layouts : LayoutTable) (idx : Nat) :
    (∀ bits < 2 ^ 32,
      decodeTypedValueFromBytes defaultCodecFuel layouts ⟨.float .f32, idx⟩
          (encodeLittleEndianBytes bits 4 none) = some (.scalar ⟨bits, 4⟩) ∧
      decodeTypedValueFromBytes defaultCodecFuel layouts ⟨.uint .u32, idx⟩
          (encodeLittleEndianBytes bits 4 none) = some (.scalar ⟨bits, 4⟩) ∧
      decodeTypedValueFromBytes defaultCodecFuel layouts ⟨.int .i32, idx⟩
          (encodeLittleEndianBytes bits 4 none) = some (.scalar ⟨bits, 4⟩)) ∧
    (∀ bits < 2 ^ 64,
      decodeTypedValueFromBytes defaultCodecFuel layouts ⟨.float .f64, idx⟩
          (encodeLittleEndianBytes bits 8 none) = some (.scalar ⟨bits, 8⟩) ∧
      decodeTypedValueFromBytes defaultCodecFuel layouts ⟨.uint .u64, idx⟩
          (encodeLittleEndianBytes bits 8 none) = some (.scalar ⟨bits, 8⟩) ∧
      decodeTypedValueFromBytes defaultCodecFuel layouts ⟨.int .i64, idx⟩
          (encodeLittleEndianBytes bits 8 none) = some (.scalar ⟨bits, 8⟩)) := by
  refine ⟨fun bits h32 => ⟨?_, ?_, ?_⟩, fun bits h64 => ⟨?_, ?_, ?_⟩⟩
  · change (match abstractBytesHaveProv (encodeLittleEndianBytes bits 4 none) with
      | true => none
      | false =>
        match Nat.beq (Trusted.Sequence.length (encodeLittleEndianBytes bits 4 none)) 4 with
        | false => none
        | true =>
          match decodeScalarBytes (encodeLittleEndianBytes bits 4 none) false with
          | some (sv, _) => some (Value.scalar sv)
          | none => none) = _
    rw [fc_abstractBytesHaveProv_encode_none, fc_seqLength_encodeLittleEndianBytes,
      fc_decodeScalarBytes_encode none false 3 bits (fc_lt_256_pow_4 h32)]
  · change (match abstractBytesHaveProv (encodeLittleEndianBytes bits 4 none) with
      | true => none
      | false =>
        match Nat.beq (Trusted.Sequence.length (encodeLittleEndianBytes bits 4 none)) 4 with
        | false => none
        | true =>
          match decodeScalarBytes (encodeLittleEndianBytes bits 4 none) false with
          | some (sv, _) => some (Value.scalar sv)
          | none => none) = _
    rw [fc_abstractBytesHaveProv_encode_none, fc_seqLength_encodeLittleEndianBytes,
      fc_decodeScalarBytes_encode none false 3 bits (fc_lt_256_pow_4 h32)]
  · change (match abstractBytesHaveProv (encodeLittleEndianBytes bits 4 none) with
      | true => none
      | false =>
        match Nat.beq (Trusted.Sequence.length (encodeLittleEndianBytes bits 4 none)) 4 with
        | false => none
        | true =>
          match decodeScalarBytes (encodeLittleEndianBytes bits 4 none) true with
          | some (sv, _) => some (Value.scalar sv)
          | none => none) = _
    rw [fc_abstractBytesHaveProv_encode_none, fc_seqLength_encodeLittleEndianBytes,
      fc_decodeScalarBytes_encode none true 3 bits (fc_lt_256_pow_4 h32)]
  · change (match abstractBytesHaveProv (encodeLittleEndianBytes bits 8 none) with
      | true => none
      | false =>
        match Nat.beq (Trusted.Sequence.length (encodeLittleEndianBytes bits 8 none)) 8 with
        | false => none
        | true =>
          match decodeScalarBytes (encodeLittleEndianBytes bits 8 none) false with
          | some (sv, _) => some (Value.scalar sv)
          | none => none) = _
    rw [fc_abstractBytesHaveProv_encode_none, fc_seqLength_encodeLittleEndianBytes,
      fc_decodeScalarBytes_encode none false 7 bits (fc_lt_256_pow_8 h64)]
  · change (match abstractBytesHaveProv (encodeLittleEndianBytes bits 8 none) with
      | true => none
      | false =>
        match Nat.beq (Trusted.Sequence.length (encodeLittleEndianBytes bits 8 none)) 8 with
        | false => none
        | true =>
          match decodeScalarBytes (encodeLittleEndianBytes bits 8 none) false with
          | some (sv, _) => some (Value.scalar sv)
          | none => none) = _
    rw [fc_abstractBytesHaveProv_encode_none, fc_seqLength_encodeLittleEndianBytes,
      fc_decodeScalarBytes_encode none false 7 bits (fc_lt_256_pow_8 h64)]
  · change (match abstractBytesHaveProv (encodeLittleEndianBytes bits 8 none) with
      | true => none
      | false =>
        match Nat.beq (Trusted.Sequence.length (encodeLittleEndianBytes bits 8 none)) 8 with
        | false => none
        | true =>
          match decodeScalarBytes (encodeLittleEndianBytes bits 8 none) true with
          | some (sv, _) => some (Value.scalar sv)
          | none => none) = _
    rw [fc_abstractBytesHaveProv_encode_none, fc_seqLength_encodeLittleEndianBytes,
      fc_decodeScalarBytes_encode none true 7 bits (fc_lt_256_pow_8 h64)]

/-- **Layout-parametric Anneal `f32`/`f64` ↔ `u32`/`i32`/`u64`/`i64` transmute**: for *any*
`layouts : LayoutTable` and `decls : List LocalDecl` (not restricted to `fcLayouts`) that resolve
`srcTy` and `dstTy` to 4-byte (`f32`/`u32`/`i32`) or 8-byte (`f64`/`u64`/`i64`) types, `evalRvalue
(.cast .transmute op dstTy)` preserves every in-range bit pattern unchanged! -/
theorem fc_transmute_float_scalar_any_layouts
    {locals locals' : List LocalSlot} {op : Operand} {mem : Memory}
    {decls : List LocalDecl} {layouts : LayoutTable} {srcTy dstTy : Ty} :
    (∀ {bits : Nat}, bits < 2 ^ 32 →
      evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
          mem.callStack = .ok (.scalar ⟨bits, 4⟩) locals' →
      operandTy decls layouts op = some srcTy →
      tyByteSize decls layouts (resolveTyWithLocalDecls decls layouts srcTy) = some 4 →
      tyByteSize decls layouts (resolveTyWithLocalDecls decls layouts dstTy) = some 4 →
      ((resolveTyWithLocalDecls decls layouts srcTy).kind = .float .f32 ∨
       (resolveTyWithLocalDecls decls layouts srcTy).kind = .uint .u32 ∨
       (resolveTyWithLocalDecls decls layouts srcTy).kind = .int .i32) →
      ((resolveTyWithLocalDecls decls layouts dstTy).kind = .float .f32 ∨
       (resolveTyWithLocalDecls decls layouts dstTy).kind = .uint .u32 ∨
       (resolveTyWithLocalDecls decls layouts dstTy).kind = .int .i32) →
      evalRvalue locals (.cast .transmute op dstTy) mem decls layouts =
        .ok (.scalar ⟨bits, 4⟩) locals' mem) ∧
    (∀ {bits : Nat}, bits < 2 ^ 64 →
      evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
          mem.callStack = .ok (.scalar ⟨bits, 8⟩) locals' →
      operandTy decls layouts op = some srcTy →
      tyByteSize decls layouts (resolveTyWithLocalDecls decls layouts srcTy) = some 8 →
      tyByteSize decls layouts (resolveTyWithLocalDecls decls layouts dstTy) = some 8 →
      ((resolveTyWithLocalDecls decls layouts srcTy).kind = .float .f64 ∨
       (resolveTyWithLocalDecls decls layouts srcTy).kind = .uint .u64 ∨
       (resolveTyWithLocalDecls decls layouts srcTy).kind = .int .i64) →
      ((resolveTyWithLocalDecls decls layouts dstTy).kind = .float .f64 ∨
       (resolveTyWithLocalDecls decls layouts dstTy).kind = .uint .u64 ∨
       (resolveTyWithLocalDecls decls layouts dstTy).kind = .int .i64) →
      evalRvalue locals (.cast .transmute op dstTy) mem decls layouts =
        .ok (.scalar ⟨bits, 8⟩) locals' mem) := by
  refine ⟨fun {bits} h32 hop hty hssz hdsz hsk hdk => ?_,
    fun {bits} h64 hop hty hssz hdsz hsk hdk => ?_⟩
  · have henc : encodeByteCastSourceBytes layouts (resolveTyWithLocalDecls decls layouts srcTy)
        (.scalar ⟨bits, 4⟩) = some (encodeLittleEndianBytes bits 4 none) := by
      cases hrs : resolveTyWithLocalDecls decls layouts srcTy with
      | mk ks ls =>
        rw [hrs] at hsk; rcases hsk with hk | hk | hk <;> simp only at hk <;> subst hk <;> rfl
    have hdec : decodeTypedValueFromBytes defaultCodecFuel layouts
        (resolveTyWithLocalDecls decls layouts dstTy)
        (encodeLittleEndianBytes bits 4 none) = some (.scalar ⟨bits, 4⟩) := by
      cases hrd : resolveTyWithLocalDecls decls layouts dstTy with
      | mk kd ld =>
        obtain ⟨hf, hu, hi⟩ := (fc_decodeTyped_any_layouts layouts ld).1 bits h32
        rw [hrd] at hdk; rcases hdk with hk | hk | hk <;> simp only at hk <;> subst hk
        · exact hf
        · exact hu
        · exact hi
    show evalByteCast locals op dstTy mem decls layouts = _
    rw [fc_evalByteCast_of_encode locals locals' op mem decls layouts _ srcTy dstTy 4 _
      hop hdsz hty hssz henc (fc_seqLength_encodeLittleEndianBytes none 4 bits), hdec]
  · have henc : encodeByteCastSourceBytes layouts (resolveTyWithLocalDecls decls layouts srcTy)
        (.scalar ⟨bits, 8⟩) = some (encodeLittleEndianBytes bits 8 none) := by
      cases hrs : resolveTyWithLocalDecls decls layouts srcTy with
      | mk ks ls =>
        rw [hrs] at hsk; rcases hsk with hk | hk | hk <;> simp only at hk <;> subst hk <;> rfl
    have hdec : decodeTypedValueFromBytes defaultCodecFuel layouts
        (resolveTyWithLocalDecls decls layouts dstTy)
        (encodeLittleEndianBytes bits 8 none) = some (.scalar ⟨bits, 8⟩) := by
      cases hrd : resolveTyWithLocalDecls decls layouts dstTy with
      | mk kd ld =>
        obtain ⟨hf, hu, hi⟩ := (fc_decodeTyped_any_layouts layouts ld).2 bits h64
        rw [hrd] at hdk; rcases hdk with hk | hk | hk <;> simp only at hk <;> subst hk
        · exact hf
        · exact hu
        · exact hi
    show evalByteCast locals op dstTy mem decls layouts = _
    rw [fc_evalByteCast_of_encode locals locals' op mem decls layouts _ srcTy dstTy 8 _
      hop hdsz hty hssz henc (fc_seqLength_encodeLittleEndianBytes none 8 bits), hdec]

/-- **`f16` / `f128` transmute vs. numeric float-cast dichotomy**: in Anneal, numeric `as` casts
(`CastKind.{floatToInt, intToFloat, floatToFloat}`) fail closed (`.unsupported`) on `f16` and `f128`,
whereas byte-level `CastKind.transmute` (`f16 ↔ u16` at 2 bytes, `f128 ↔ u128` at 16 bytes via
`byteCodecScalarKind`) succeeds and preserves every 16-bit and 128-bit pattern! -/
theorem fc_f16_f128_transmute_vs_float_cast
    {locals locals' : List LocalSlot} {op : Operand} {mem : Memory} {decls : List LocalDecl} :
    (∀ {bits : Nat}, bits < 2 ^ 16 →
      evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
          mem.callStack = .ok (.scalar ⟨bits, 2⟩) locals' →
      operandTy decls fcLayouts op = some fcF16Ty →
      evalRvalue locals (.cast .transmute op fcU16Ty) mem decls fcLayouts =
          .ok (.scalar ⟨bits, 2⟩) locals' mem ∧
      evalRvalue locals (.cast .floatToInt op fcI32Ty) mem decls fcLayouts = .unsupported ∧
      evalRvalue locals (.cast .floatToFloat op fcF32Ty) mem decls fcLayouts = .unsupported) ∧
    (∀ {bits : Nat}, bits < 2 ^ 128 →
      evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
          mem.callStack = .ok (.scalar ⟨bits, 16⟩) locals' →
      operandTy decls fcLayouts op = some fcF128Ty →
      evalRvalue locals (.cast .transmute op fcU128Ty) mem decls fcLayouts =
          .ok (.scalar ⟨bits, 16⟩) locals' mem ∧
      evalRvalue locals (.cast .floatToInt op fcI32Ty) mem decls fcLayouts = .unsupported ∧
      evalRvalue locals (.cast .floatToFloat op fcF64Ty) mem decls fcLayouts = .unsupported) := by
  refine ⟨fun {bits} h16 hop hty => ?_, fun {bits} h128 hop hty => ?_⟩
  · have hdec : decodeTypedValueFromBytes defaultCodecFuel fcLayouts
        (resolveTyWithLocalDecls decls fcLayouts fcU16Ty)
        (encodeLittleEndianBytes bits 2 none) = some (.scalar ⟨bits, 2⟩) := by
      change (match abstractBytesHaveProv (encodeLittleEndianBytes bits 2 none) with
        | true => none
        | false =>
          match Nat.beq (Trusted.Sequence.length (encodeLittleEndianBytes bits 2 none)) 2 with
          | false => none
          | true =>
            match decodeScalarBytes (encodeLittleEndianBytes bits 2 none) false with
            | some (sv, _) => some (Value.scalar sv)
            | none => none) = _
      rw [fc_abstractBytesHaveProv_encode_none, fc_seqLength_encodeLittleEndianBytes,
        fc_decodeScalarBytes_encode none false 1 bits (by simpa using h16)]
    exact ⟨fc_evalRvalue_transmute_via_le hop hty rfl rfl rfl hdec,
      ((fc_evalRvalue_float_cast_unsupported_of_no_format (dstTy := fcI32Ty) hop hty).1
        fc_ieeeFormatOfTy_f16).1,
      ((fc_evalRvalue_float_cast_unsupported_of_no_format (dstTy := fcF32Ty) hop hty).1
        fc_ieeeFormatOfTy_f16).2⟩
  · have hdec : decodeTypedValueFromBytes defaultCodecFuel fcLayouts
        (resolveTyWithLocalDecls decls fcLayouts fcU128Ty)
        (encodeLittleEndianBytes bits 16 none) = some (.scalar ⟨bits, 16⟩) := by
      change (match abstractBytesHaveProv (encodeLittleEndianBytes bits 16 none) with
        | true => none
        | false =>
          match Nat.beq (Trusted.Sequence.length (encodeLittleEndianBytes bits 16 none)) 16 with
          | false => none
          | true =>
            match decodeScalarBytes (encodeLittleEndianBytes bits 16 none) false with
            | some (sv, _) => some (Value.scalar sv)
            | none => none) = _
      rw [fc_abstractBytesHaveProv_encode_none, fc_seqLength_encodeLittleEndianBytes,
        fc_decodeScalarBytes_encode none false 15 bits (by simpa using h128)]
    exact ⟨fc_evalRvalue_transmute_via_le hop hty rfl rfl rfl hdec,
      ((fc_evalRvalue_float_cast_unsupported_of_no_format (dstTy := fcI32Ty) hop hty).1
        fc_ieeeFormatOfTy_f128).1,
      ((fc_evalRvalue_float_cast_unsupported_of_no_format (dstTy := fcF64Ty) hop hty).1
        fc_ieeeFormatOfTy_f128).2⟩

/-- **Signed two's-complement carrier bijection (`encodeTwosComplement` ↔ `intValueOfBits` ↔
`intFromBits`)**: for every signed integer `z` in `i32` or `i64` bounds (`n ∈ {1, 2, 4, 8}`),
`encodeTwosComplement (8 * n) z` produces the unique `< 2 ^ (8 * n)` bit pattern whose Anneal
`intValueOfBits` and MiniRust `intFromBits` both equal `z`, and MiniRust's `Type.encode` /
`transmuteM` (`BasicMemory` and `TreeBorrowsMemory`) maps `.Int z` at `i32`/`i64` to the exact
same unsigned bit pattern `encodeTwosComplement (8 * n) z` at `u32`/`u64`. -/
theorem fc_encodeTwosComplement_carrier_bridge (n : Nat)
    (hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8) (z : Int)
    (hlo : -((2 ^ (8 * n - 1) : Nat) : Int) ≤ z)
    (hhi : z ≤ ((2 ^ (8 * n - 1) : Nat) : Int) - 1) :
    encodeTwosComplement (8 * n) z < 2 ^ (8 * n) ∧
    intValueOfBits true (8 * n) (encodeTwosComplement (8 * n) z) = z ∧
    intFromBits (encodeTwosComplement (8 * n) z) ⟨.Signed, ⟨n⟩⟩ = z ∧
    Type.encode (.Int ⟨.Signed, ⟨n⟩⟩) (.Int z) =
      .ok ((encodeLittleEndianBytes (encodeTwosComplement (8 * n) z) n none).map fcByteToMR) ∧
    transmuteM (M := BM) (.Int z) (.Int ⟨.Signed, ⟨n⟩⟩) (.Int ⟨.Unsigned, ⟨n⟩⟩) =
      .ok (.Int (encodeTwosComplement (8 * n) z : Int)) ∧
    transmuteM (M := TBM) (.Int z) (.Int ⟨.Signed, ⟨n⟩⟩) (.Int ⟨.Unsigned, ⟨n⟩⟩) =
      .ok (.Int (encodeTwosComplement (8 * n) z : Int)) := by
  have hgood : GoodSize n := by rcases hn with rfl | rfl | rfl | rfl <;> unfold GoodSize <;> omega
  have hlt : encodeTwosComplement (8 * n) z < 2 ^ (8 * n) := by
    rcases hn with rfl | rfl | rfl | rfl <;>
      simp only [encodeTwosComplement, Nat.reduceMul, Nat.reducePow, Nat.reduceSub] at hlo hhi ⊢ <;>
      omega
  have hiv : intValueOfBits true (8 * n) (encodeTwosComplement (8 * n) z) = z := by
    rcases hn with rfl | rfl | rfl | rfl <;>
      simp only [encodeTwosComplement, intValueOfBits, Nat.reduceMul, Nat.reducePow,
        Nat.reduceSub, true_and] at hlo hhi ⊢ <;>
      split <;> omega
  have hifb : intFromBits (encodeTwosComplement (8 * n) z) ⟨.Signed, ⟨n⟩⟩ = z := by
    have h0 := fc_intValueOfBits_eq_intFromBits true n (encodeTwosComplement (8 * n) z) hlt
    simp only [↓reduceIte] at h0
    exact h0.symm.trans hiv
  have hu : intFromBits (encodeTwosComplement (8 * n) z) ⟨.Unsigned, ⟨n⟩⟩ =
      (encodeTwosComplement (8 * n) z : Int) := rfl
  have henc := fc_mr_encode_eq_anneal .Signed n (encodeTwosComplement (8 * n) z) hgood hlt
  have hbm := fc_mrBM_transmute_int .Signed .Unsigned n (encodeTwosComplement (8 * n) z) hgood hlt
    none
  have htb := fc_mrTB_transmute_int .Signed .Unsigned n (encodeTwosComplement (8 * n) z) hgood hlt
    none
  rw [hifb] at henc
  rw [hifb, hu] at hbm htb
  exact ⟨hlt, hiv, hifb, henc, hbm, htb⟩

/-! ## 12. Symbolic MiniRust `[u8; 4]` & `[u8; 8]` `Type.encode`/`Type.decode` & `transmuteM` -/

/-- Polymorphic MiniRust `[u8; n]` element values of the `n` little-endian bytes of `bits`, for
any memory model `M`. -/
def fcLeByteValsMRM {M : Type} [Gen.Memory M] (bits : Nat) : Nat → List (Gen.Value M)
  | 0 => []
  | n + 1 => .Int ((bits % 256 : Nat) : Int) :: fcLeByteValsMRM (bits / 256) n

/-- Raw definitional output of `Type.decodeM` / `Type.decode` on `n` little-endian `u8` bytes
before simplifying `(UInt8.ofNat (k % 256)).toNat + 256 * 0 = k % 256`. -/
def fcLeBytesDecodeMRM {M : Type} [Gen.Memory M] (bits : Nat) : Nat → List (Gen.Value M)
  | 0 => []
  | n + 1 =>
    .Int (((UInt8.ofNat (bits % 256)).toNat + 256 * 0 : Nat) : Int) ::
      fcLeBytesDecodeMRM (bits / 256) n

theorem fc_leByteValsMRM_eq_BM (bits n : Nat) :
    fcLeByteValsMRM (M := BM) bits n = fcLeByteValsMR bits n := by
  induction n generalizing bits with
  | zero => rfl
  | succ k ih => simp [fcLeByteValsMRM, fcLeByteValsMR, ih]

theorem fc_uint8_mod_toNat (k : Nat) : (UInt8.ofNat (k % 256)).toNat = k % 256 := by
  show (UInt8.ofNat (k % 256)).toBitVec.toNat = k % 256
  rw [fc_uint8_ofNat_toNat, Nat.mod_mod]

theorem fc_leBytesDecodeMRM_eq {M : Type} [Gen.Memory M] (bits n : Nat) :
    fcLeBytesDecodeMRM (M := M) bits n = fcLeByteValsMRM (M := M) bits n := by
  induction n generalizing bits with
  | zero => rfl
  | succ k ih =>
    simp only [fcLeBytesDecodeMRM, fcLeByteValsMRM, Nat.mul_zero, Nat.add_zero,
      fc_uint8_mod_toNat, ih]

theorem fc_u8_inBounds_mod (k : Nat) :
    inBounds ((k % 256 : Nat) : Int) .Unsigned ⟨1⟩ = true := by
  unfold inBounds Size.bits
  simp only [Nat.reduceMul, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem fc_u8_emod_toNat_mod (k : Nat) :
    (((k % 256 : Nat) : Int) % (2 : Int) ^ Size.bits ⟨1⟩).toNat = k % 256 := by
  simp only [Size.bits, Nat.reduceMul]
  omega

theorem fc_u8_encodeIntM_mod {M : Type} [Gen.Memory M] (k : Nat) :
    Type.encodeIntM (M := M) fcU8It (.Int ((k % 256 : Nat) : Int)) =
      .ok [.Init (UInt8.ofNat (k % 256)) none] := by
  simp only [Type.encodeIntM, fcU8It, Endianness.encode, x86_64.ENDIANNESS,
    fc_u8_inBounds_mod k, ↓reduceIte, fc_u8_emod_toNat_mod k, leBytes, Nat.mod_mod, List.map,
    pure, Except.pure]

theorem fc_u8_encodeInt_mod (k : Nat) :
    Type.encodeInt fcU8It (.Int ((k % 256 : Nat) : Int)) =
      .ok [.Init (UInt8.ofNat (k % 256)) none] := by
  simp only [Type.encodeInt, fcU8It, Endianness.encode, x86_64.ENDIANNESS,
    fc_u8_inBounds_mod k, ↓reduceIte, fc_u8_emod_toNat_mod k, leBytes, Nat.mod_mod, List.map,
    pure, Except.pure]

theorem fc_layout_u8 : Type.layout (.Int fcU8It) = .ok (.Sized ⟨1⟩ ⟨1⟩) := rfl

/-- **Symbolic MiniRust `Type.encodeM` and `Type.decodeM` for `[u8; 4]` and `[u8; 8]`**, for
*every* memory model `M` (`BasicMemory` and `TreeBorrowsMemory`) and *every* bit pattern `bits`:
encoding `fcLeByteValsMRM bits n` produces the exact little-endian `Init b none` byte sequence, and
decoding those bytes recovers `fcLeByteValsMRM bits n`. -/
theorem fc_mrM_array_u8_encode_decode {M : Type} [Gen.Memory M] [MemoryOps M] (bits : Nat) :
    Type.encodeM (M := M) (.Array (.Int fcU8It) 4) (.Tuple (fcLeByteValsMRM bits 4)) =
      .ok ((leBytes bits 4).map (fun b => .Init b none)) ∧
    Type.decodeM (M := M) (.Array (.Int fcU8It) 4)
        ((leBytes bits 4).map (fun b => .Init b none)) =
      .ok (some (.Tuple (fcLeByteValsMRM bits 4))) ∧
    Type.encodeM (M := M) (.Array (.Int fcU8It) 8) (.Tuple (fcLeByteValsMRM bits 8)) =
      .ok ((leBytes bits 8).map (fun b => .Init b none)) ∧
    Type.decodeM (M := M) (.Array (.Int fcU8It) 8)
        ((leBytes bits 8).map (fun b => .Init b none)) =
      .ok (some (.Tuple (fcLeByteValsMRM bits 8))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [fcLeByteValsMRM, Type.encodeM, List.length, List.mapM, List.mapM.loop,
      bind, Except.bind, pure, Except.pure, List.reverse, List.reverseAux]
    simp only [ne_eq, fc_u8_encodeIntM_mod, fc_layout_u8, LayoutStrategy.expect_size,
      List.length_singleton, leBytes, List.map]
    rfl
  · rw [← fc_leBytesDecodeMRM_eq (M := M) bits 4]; rfl
  · dsimp only [fcLeByteValsMRM, Type.encodeM, List.length, List.mapM, List.mapM.loop,
      bind, Except.bind, pure, Except.pure, List.reverse, List.reverseAux]
    simp only [ne_eq, fc_u8_encodeIntM_mod, fc_layout_u8, LayoutStrategy.expect_size,
      List.length_singleton, leBytes, List.map]
    rfl
  · rw [← fc_leBytesDecodeMRM_eq (M := M) bits 8]; rfl

/-- Non-polymorphic `Type.encode` / `Type.decode` on `[u8; 4]` and `[u8; 8]` equals Anneal's
`encodeLittleEndianBytes` image under `fcByteToMR`, byte for byte. -/
theorem fc_mr_array_u8_eq_anneal (bits : Nat) (prov : Option (Nat × Nat)) :
    Type.encode (.Array (.Int fcU8It) 4) (.Tuple (fcLeByteValsMR bits 4)) =
      .ok ((encodeLittleEndianBytes bits 4 none).map fcByteToMR) ∧
    Type.decode (.Array (.Int fcU8It) 4)
        ((encodeLittleEndianBytes bits 4 prov).map fcByteToMR) =
      .ok (some (.Tuple (fcLeByteValsMR bits 4))) ∧
    Type.encode (.Array (.Int fcU8It) 8) (.Tuple (fcLeByteValsMR bits 8)) =
      .ok ((encodeLittleEndianBytes bits 8 none).map fcByteToMR) ∧
    Type.decode (.Array (.Int fcU8It) 8)
        ((encodeLittleEndianBytes bits 8 prov).map fcByteToMR) =
      .ok (some (.Tuple (fcLeByteValsMR bits 8))) := by
  rw [fc_map_encodeLittleEndianBytes .Unsigned none 4 bits,
    fc_map_encodeLittleEndianBytes .Unsigned prov 4 bits,
    fc_map_encodeLittleEndianBytes .Unsigned none 8 bits,
    fc_map_encodeLittleEndianBytes .Unsigned prov 8 bits]
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [fcLeByteValsMR, Type.encode, List.length, List.mapM, List.mapM.loop,
      bind, Except.bind, pure, Except.pure, List.reverse, List.reverseAux]
    simp only [ne_eq, fc_u8_encodeInt_mod, fc_layout_u8, LayoutStrategy.expect_size,
      List.length_singleton, scalarBytes, leBytes, List.map]
    rfl
  · rw [← fc_leByteValsMRM_eq_BM bits 4, ← fc_leBytesDecodeMRM_eq (M := BM) bits 4]; rfl
  · dsimp only [fcLeByteValsMR, Type.encode, List.length, List.mapM, List.mapM.loop,
      bind, Except.bind, pure, Except.pure, List.reverse, List.reverseAux]
    simp only [ne_eq, fc_u8_encodeInt_mod, fc_layout_u8, LayoutStrategy.expect_size,
      List.length_singleton, scalarBytes, leBytes, List.map]
    rfl
  · rw [← fc_leByteValsMRM_eq_BM bits 8, ← fc_leBytesDecodeMRM_eq (M := BM) bits 8]; rfl

/-- **Polymorphic symbolic bidirectional `transmuteM` between `u32`/`i32` and `[u8; 4]`**, for
*every* memory model `M` (in particular `BasicMemory` and `TreeBorrowsMemory`) and *every*
`bits < 2 ^ 32`, for both signednesses `s ∈ {.Unsigned, .Signed}`! -/
theorem fc_mrM_transmute_int_bytes4 {M : Type} [Gen.Memory M] [MemoryOps M]
    (s : Signedness) (bits : Nat) (hbits : bits < 2 ^ 32) (m : Option (Gen.Machine M)) :
    transmuteM (M := M) (.Int (intFromBits bits ⟨s, ⟨4⟩⟩)) (.Int ⟨s, ⟨4⟩⟩)
        (.Array (.Int fcU8It) 4) m = .ok (.Tuple (fcLeByteValsMRM bits 4)) ∧
    transmuteM (M := M) (.Tuple (fcLeByteValsMRM bits 4)) (.Array (.Int fcU8It) 4)
        (.Int ⟨s, ⟨4⟩⟩) m = .ok (.Int (intFromBits bits ⟨s, ⟨4⟩⟩)) := by
  have hbits' : bits < 2 ^ (8 * 4) := hbits
  have hrep := canRepresent_intFromBits ⟨s, ⟨4⟩⟩ bits fc_goodSize_4 hbits'
  have hmod : (intFromBits bits ⟨s, ⟨4⟩⟩ % 2 ^ Size.bits ⟨4⟩).toNat = bits := by
    have := intFromBits_emod bits ⟨s, ⟨4⟩⟩ hbits'
    simp only [Size.bits] at this ⊢
    rw [this]; rfl
  have hencI : Endianness.encode .LittleEndian s ⟨4⟩ (intFromBits bits ⟨s, ⟨4⟩⟩) =
      some (leBytes bits 4) := by
    rw [encode_eq s ⟨4⟩ _ hrep, hmod]
  have hdecI := decode_leBytes s 4 bits hbits'
  obtain ⟨hencA, hdecA, _, _⟩ := fc_mrM_array_u8_encode_decode (M := M) bits
  have hlayA : Type.layout (.Array (.Int fcU8It) 4) = .ok (.Sized ⟨4⟩ ⟨1⟩) := rfl
  have hchkA : checkValueM (M := M) (.Tuple (fcLeByteValsMRM bits 4))
      (.Array (.Int fcU8It) 4) m = .ok () := by
    dsimp only [fcLeByteValsMRM, checkValueM, ensureElseUb, List.length, List.forM,
      bind, Except.bind, pure, Except.pure]
    simp only [IntType.can_represent, fcU8It, fc_u8_inBounds_mod, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]; rfl
  constructor
  · unfold transmuteM
    simp only [layout_eq ⟨s, ⟨4⟩⟩ fc_goodSize_4, hlayA, bind, Except.bind, expect_size_sized,
      ne_eq, not_true_eq_false, ↓reduceIte, Type.encodeM, Type.encodeIntM, x86_64.ENDIANNESS,
      hencI, hdecA, hchkA, pure, Except.pure]
  · unfold transmuteM
    simp only [layout_eq ⟨s, ⟨4⟩⟩ fc_goodSize_4, hlayA, bind, Except.bind, expect_size_sized,
      ne_eq, not_true_eq_false, ↓reduceIte, hencA, Type.decodeM, Type.decodeIntM,
      List.length_map, leBytes_length, fc_mapM_dataM_init, x86_64.ENDIANNESS, hdecI, checkValueM,
      ensureElseUb, hrep, Bool.not_true, Bool.false_eq_true, pure, Except.pure]

/-- **Polymorphic symbolic bidirectional `transmuteM` between `u64`/`i64` and `[u8; 8]`**, for
*every* memory model `M` (`BasicMemory` and `TreeBorrowsMemory`) and *every* `bits < 2 ^ 64`,
for both signednesses `s ∈ {.Unsigned, .Signed}`! -/
theorem fc_mrM_transmute_int_bytes8 {M : Type} [Gen.Memory M] [MemoryOps M]
    (s : Signedness) (bits : Nat) (hbits : bits < 2 ^ 64) (m : Option (Gen.Machine M)) :
    transmuteM (M := M) (.Int (intFromBits bits ⟨s, ⟨8⟩⟩)) (.Int ⟨s, ⟨8⟩⟩)
        (.Array (.Int fcU8It) 8) m = .ok (.Tuple (fcLeByteValsMRM bits 8)) ∧
    transmuteM (M := M) (.Tuple (fcLeByteValsMRM bits 8)) (.Array (.Int fcU8It) 8)
        (.Int ⟨s, ⟨8⟩⟩) m = .ok (.Int (intFromBits bits ⟨s, ⟨8⟩⟩)) := by
  have hbits' : bits < 2 ^ (8 * 8) := hbits
  have hrep := canRepresent_intFromBits ⟨s, ⟨8⟩⟩ bits fc_goodSize_8 hbits'
  have hmod : (intFromBits bits ⟨s, ⟨8⟩⟩ % 2 ^ Size.bits ⟨8⟩).toNat = bits := by
    have := intFromBits_emod bits ⟨s, ⟨8⟩⟩ hbits'
    simp only [Size.bits] at this ⊢
    rw [this]; rfl
  have hencI : Endianness.encode .LittleEndian s ⟨8⟩ (intFromBits bits ⟨s, ⟨8⟩⟩) =
      some (leBytes bits 8) := by
    rw [encode_eq s ⟨8⟩ _ hrep, hmod]
  have hdecI := decode_leBytes s 8 bits hbits'
  obtain ⟨_, _, hencA, hdecA⟩ := fc_mrM_array_u8_encode_decode (M := M) bits
  have hlayA : Type.layout (.Array (.Int fcU8It) 8) = .ok (.Sized ⟨8⟩ ⟨1⟩) := rfl
  have hchkA : checkValueM (M := M) (.Tuple (fcLeByteValsMRM bits 8))
      (.Array (.Int fcU8It) 8) m = .ok () := by
    dsimp only [fcLeByteValsMRM, checkValueM, ensureElseUb, List.length, List.forM,
      bind, Except.bind, pure, Except.pure]
    simp only [IntType.can_represent, fcU8It, fc_u8_inBounds_mod, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]; rfl
  constructor
  · unfold transmuteM
    simp only [layout_eq ⟨s, ⟨8⟩⟩ fc_goodSize_8, hlayA, bind, Except.bind, expect_size_sized,
      ne_eq, not_true_eq_false, ↓reduceIte, Type.encodeM, Type.encodeIntM, x86_64.ENDIANNESS,
      hencI, hdecA, hchkA, pure, Except.pure]
  · unfold transmuteM
    simp only [layout_eq ⟨s, ⟨8⟩⟩ fc_goodSize_8, hlayA, bind, Except.bind, expect_size_sized,
      ne_eq, not_true_eq_false, ↓reduceIte, hencA, Type.decodeM, Type.decodeIntM,
      List.length_map, leBytes_length, fc_mapM_dataM_init, x86_64.ENDIANNESS, hdecI, checkValueM,
      ensureElseUb, hrep, Bool.not_true, Bool.false_eq_true, pure, Except.pure]

/-- Non-polymorphic `Interp.transmute` + `BasicMemory` + `TreeBorrowsMemory` bundle for all 4-byte
(`u32 ↔ [u8; 4]`, `i32 ↔ [u8; 4]`) and 8-byte (`u64 ↔ [u8; 8]`, `i64 ↔ [u8; 8]`) IEEE-754 byte
carriers. -/
theorem fc_mr_transmute_byte_arrays_symbolic (s : Signedness) :
    (∀ bits < 2 ^ 32,
      transmute (.Int (intFromBits bits ⟨s, ⟨4⟩⟩)) (.Int ⟨s, ⟨4⟩⟩) (.Array (.Int fcU8It) 4) =
        .ok (.Tuple (fcLeByteValsMR bits 4)) ∧
      transmute (.Tuple (fcLeByteValsMR bits 4)) (.Array (.Int fcU8It) 4) (.Int ⟨s, ⟨4⟩⟩) =
        .ok (.Int (intFromBits bits ⟨s, ⟨4⟩⟩)) ∧
      transmuteM (M := BM) (.Int (intFromBits bits ⟨s, ⟨4⟩⟩)) (.Int ⟨s, ⟨4⟩⟩)
          (.Array (.Int fcU8It) 4) = .ok (.Tuple (fcLeByteValsMR bits 4)) ∧
      transmuteM (M := TBM) (.Int (intFromBits bits ⟨s, ⟨4⟩⟩)) (.Int ⟨s, ⟨4⟩⟩)
          (.Array (.Int fcU8It) 4) = .ok (.Tuple (fcLeByteValsMRM bits 4)) ∧
      transmuteM (M := TBM) (.Tuple (fcLeByteValsMRM bits 4)) (.Array (.Int fcU8It) 4)
          (.Int ⟨s, ⟨4⟩⟩) = .ok (.Int (intFromBits bits ⟨s, ⟨4⟩⟩))) ∧
    (∀ bits < 2 ^ 64,
      transmute (.Int (intFromBits bits ⟨s, ⟨8⟩⟩)) (.Int ⟨s, ⟨8⟩⟩) (.Array (.Int fcU8It) 8) =
        .ok (.Tuple (fcLeByteValsMR bits 8)) ∧
      transmute (.Tuple (fcLeByteValsMR bits 8)) (.Array (.Int fcU8It) 8) (.Int ⟨s, ⟨8⟩⟩) =
        .ok (.Int (intFromBits bits ⟨s, ⟨8⟩⟩)) ∧
      transmuteM (M := BM) (.Int (intFromBits bits ⟨s, ⟨8⟩⟩)) (.Int ⟨s, ⟨8⟩⟩)
          (.Array (.Int fcU8It) 8) = .ok (.Tuple (fcLeByteValsMR bits 8)) ∧
      transmuteM (M := TBM) (.Int (intFromBits bits ⟨s, ⟨8⟩⟩)) (.Int ⟨s, ⟨8⟩⟩)
          (.Array (.Int fcU8It) 8) = .ok (.Tuple (fcLeByteValsMRM bits 8)) ∧
      transmuteM (M := TBM) (.Tuple (fcLeByteValsMRM bits 8)) (.Array (.Int fcU8It) 8)
          (.Int ⟨s, ⟨8⟩⟩) = .ok (.Int (intFromBits bits ⟨s, ⟨8⟩⟩))) := by
  refine ⟨fun bits h32 => ?_, fun bits h64 => ?_⟩
  · have hbits' : bits < 2 ^ (8 * 4) := h32
    have hencI := fc_mr_encode_intFromBits ⟨s, ⟨4⟩⟩ bits fc_goodSize_4 hbits'
    have hdecI := decode_int_scalarBytes ⟨s, ⟨4⟩⟩ bits hbits'
    have hrep := canRepresent_intFromBits ⟨s, ⟨4⟩⟩ bits fc_goodSize_4 hbits'
    obtain ⟨hencA, hdecA, _, _⟩ := fc_mr_array_u8_eq_anneal bits none
    rw [fc_map_encodeLittleEndianBytes .Unsigned none 4 bits] at hencA hdecA
    have hlayA : Type.layout (.Array (.Int fcU8It) 4) = .ok (.Sized ⟨4⟩ ⟨1⟩) := rfl
    have hchkA : checkValue (.Tuple (fcLeByteValsMR bits 4)) (.Array (.Int fcU8It) 4) none =
        .ok () := by
      dsimp only [fcLeByteValsMR, checkValue, ensureElseUb, List.length, List.forM,
        bind, Except.bind, pure, Except.pure]
      simp only [IntType.can_represent, fcU8It, fc_u8_inBounds_mod, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte]; rfl
    have hbm := fc_mrM_transmute_int_bytes4 (M := BM) s bits h32 none
    rw [fc_leByteValsMRM_eq_BM] at hbm
    have htb := fc_mrM_transmute_int_bytes4 (M := TBM) s bits h32 none
    refine ⟨?_, ?_, hbm.1, htb.1, htb.2⟩
    · unfold transmute
      simp only [layout_eq ⟨s, ⟨4⟩⟩ fc_goodSize_4, hlayA, bind, Except.bind, expect_size_sized,
        ne_eq, not_true_eq_false, ↓reduceIte, hencI, fc_scalarBytes_sign s .Unsigned, hdecA, hchkA,
        pure, Except.pure]
    · unfold transmute
      simp only [layout_eq ⟨s, ⟨4⟩⟩ fc_goodSize_4, hlayA, bind, Except.bind, expect_size_sized,
        ne_eq, not_true_eq_false, ↓reduceIte, hencA, fc_scalarBytes_sign .Unsigned s, hdecI,
        checkValue_int hrep, pure, Except.pure]
  · have hbits' : bits < 2 ^ (8 * 8) := h64
    have hencI := fc_mr_encode_intFromBits ⟨s, ⟨8⟩⟩ bits fc_goodSize_8 hbits'
    have hdecI := decode_int_scalarBytes ⟨s, ⟨8⟩⟩ bits hbits'
    have hrep := canRepresent_intFromBits ⟨s, ⟨8⟩⟩ bits fc_goodSize_8 hbits'
    obtain ⟨_, _, hencA, hdecA⟩ := fc_mr_array_u8_eq_anneal bits none
    rw [fc_map_encodeLittleEndianBytes .Unsigned none 8 bits] at hencA hdecA
    have hlayA : Type.layout (.Array (.Int fcU8It) 8) = .ok (.Sized ⟨8⟩ ⟨1⟩) := rfl
    have hchkA : checkValue (.Tuple (fcLeByteValsMR bits 8)) (.Array (.Int fcU8It) 8) none =
        .ok () := by
      dsimp only [fcLeByteValsMR, checkValue, ensureElseUb, List.length, List.forM,
        bind, Except.bind, pure, Except.pure]
      simp only [IntType.can_represent, fcU8It, fc_u8_inBounds_mod, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte]; rfl
    have hbm := fc_mrM_transmute_int_bytes8 (M := BM) s bits h64 none
    rw [fc_leByteValsMRM_eq_BM] at hbm
    have htb := fc_mrM_transmute_int_bytes8 (M := TBM) s bits h64 none
    refine ⟨?_, ?_, hbm.1, htb.1, htb.2⟩
    · unfold transmute
      simp only [layout_eq ⟨s, ⟨8⟩⟩ fc_goodSize_8, hlayA, bind, Except.bind, expect_size_sized,
        ne_eq, not_true_eq_false, ↓reduceIte, hencI, fc_scalarBytes_sign s .Unsigned, hdecA, hchkA,
        pure, Except.pure]
    · unfold transmute
      simp only [layout_eq ⟨s, ⟨8⟩⟩ fc_goodSize_8, hlayA, bind, Except.bind, expect_size_sized,
        ne_eq, not_true_eq_false, ↓reduceIte, hencA, fc_scalarBytes_sign .Unsigned s, hdecI,
        checkValue_int hrep, pure, Except.pure]

/-! ## 13. Uninitialized-byte UB, size-mismatch UB, and pointer-provenance transmute boundaries -/

/-- Single-chunk `n`-byte MiniRust `Type.Union` carrier, capable of holding arbitrary
`AbstractByte` lists (including `.Uninit` padding bytes). -/
def fcUnionTy (n : Nat) : Gen.Type :=
  .Union [] [(⟨0⟩, ⟨n⟩)] ⟨n⟩ ⟨1⟩

private theorem fc_mapM_dataM_loop_none {P : Type} :
    ∀ (bs : List (Gen.AbstractByte P)) (acc : List UInt8),
      .Uninit ∈ bs → List.mapM.loop AbstractByte.dataM bs acc = none
  | [], _, h => nomatch h
  | .Uninit :: _, _, _ => rfl
  | .Init b _ :: rest, acc, h => by
    rcases List.mem_cons.mp h with h0 | hmem
    · nomatch h0
    · exact fc_mapM_dataM_loop_none rest (b :: acc) hmem

private theorem fc_mapM_dataM_none_of_uninit {P : Type}
    (bs : List (Gen.AbstractByte P)) (h : .Uninit ∈ bs) :
    bs.mapM AbstractByte.dataM = none :=
  fc_mapM_dataM_loop_none bs [] h

private theorem fc_mapM_data_loop_none :
    ∀ (bs : List Byte) (acc : List UInt8),
      .Uninit ∈ bs → List.mapM.loop AbstractByte.data bs acc = none
  | [], _, h => nomatch h
  | .Uninit :: _, _, _ => rfl
  | .Init b _ :: rest, acc, h => by
    rcases List.mem_cons.mp h with h0 | hmem
    · nomatch h0
    · exact fc_mapM_data_loop_none rest (b :: acc) hmem

private theorem fc_mapM_data_none_of_uninit (bs : List Byte) (h : .Uninit ∈ bs) :
    bs.mapM AbstractByte.data = none :=
  fc_mapM_data_loop_none bs [] h

private theorem fc_encodeUnion_uninitM {M : Type} [Gen.Memory M]
    (n : Nat) (bytes : List (Gen.AbstractByte (Gen.Memory.Provenance M))) (hlen : bytes.length = n) :
    Type.encodeM (M := M) (fcUnionTy n) (.Union [bytes]) = .ok bytes := by
  have hrep : (List.replicate n (Gen.AbstractByte.Uninit : Gen.AbstractByte (Gen.Memory.Provenance M))).length = n :=
    List.length_replicate
  have hdrop : (List.replicate n (Gen.AbstractByte.Uninit : Gen.AbstractByte (Gen.Memory.Provenance M))).drop n = [] := by
    rw [List.drop_eq_nil_iff, hrep]; exact Nat.le_refl n
  have hws : writeSubsliceAtIndex
      (List.replicate n (Gen.AbstractByte.Uninit : Gen.AbstractByte (Gen.Memory.Provenance M)))
      ((0 : Nat) : Int) bytes = .ok bytes := by
    unfold writeSubsliceAtIndex
    split
    · simp [hlen, hdrop]
    · exfalso; rename_i hneg; apply hneg; rw [hrep, hlen]; omega
  dsimp only [fcUnionTy, Type.encodeM, Type.encodeUnionChunksM, List.length, bind, Except.bind,
    pure, Except.pure]
  simp only [ne_eq, hlen, not_true_eq_false, ↓reduceIte]
  rw [hws]

/-- **Uninitialized-byte transmute UB in MiniRust (`Interp.transmute` and polymorphic `transmuteM`
over both `BasicMemory` and `TreeBorrowsMemory`)**: transmuting an `n`-byte `Type.Union` value
whose byte list contains *any* `.Uninit` byte into `.Int ⟨s, ⟨n⟩⟩` (`u32`, `i32`, `u64`, `i64`, etc.)
raises UB (`"transmuted value is not valid at new type"`). -/
theorem fc_mrM_uninit_union_transmute_ub {M : Type} [Gen.Memory M] [MemoryOps M]
    (s : Signedness) (n : Nat) (hgood : GoodSize n)
    (bytes : List (Gen.AbstractByte (Gen.Memory.Provenance M)))
    (hlen : bytes.length = n) (huninit : .Uninit ∈ bytes) (m : Option (Gen.Machine M))
    (bytesBM : List Byte) (hlenBM : bytesBM.length = n) (huninitBM : .Uninit ∈ bytesBM) :
    Type.decodeM (M := M) (.Int ⟨s, ⟨n⟩⟩) bytes = .ok none ∧
    transmuteM (M := M) (.Union [bytes]) (fcUnionTy n) (.Int ⟨s, ⟨n⟩⟩) m =
      .error (.ub "transmuted value is not valid at new type") ∧
    transmute (.Union [bytesBM]) (fcUnionTy n) (.Int ⟨s, ⟨n⟩⟩) =
      .error (.ub "transmuted value is not valid at new type") := by
  have hdecM : Type.decodeM (M := M) (.Int ⟨s, ⟨n⟩⟩) bytes = .ok none := by
    dsimp only [Type.decodeM, Type.decodeIntM]
    simp only [ne_eq, hlen, not_true_eq_false, ↓reduceIte, fc_mapM_dataM_none_of_uninit bytes huninit,
      pure, Except.pure]
  have hlayU : Type.layout (fcUnionTy n) = .ok (.Sized ⟨n⟩ ⟨1⟩) := rfl
  refine ⟨hdecM, ?_, ?_⟩
  · unfold transmuteM
    simp only [hlayU, layout_eq ⟨s, ⟨n⟩⟩ hgood, bind, Except.bind, expect_size_sized,
      ne_eq, not_true_eq_false, ↓reduceIte, fc_encodeUnion_uninitM (M := M) n bytes hlen,
      hdecM, ub]
  · have hdecB : Type.decode (.Int ⟨s, ⟨n⟩⟩) bytesBM = .ok none := by
      dsimp only [Type.decode, Type.decodeInt]
      simp only [ne_eq, hlenBM, not_true_eq_false, ↓reduceIte,
        fc_mapM_data_none_of_uninit bytesBM huninitBM, pure, Except.pure]
    have hencB : Type.encode (fcUnionTy n) (.Union [bytesBM]) = .ok bytesBM := by
      have hrep : (List.replicate n (Gen.AbstractByte.Uninit : Byte)).length = n :=
        List.length_replicate
      have hdrop : (List.replicate n (Gen.AbstractByte.Uninit : Byte)).drop n = [] := by
        rw [List.drop_eq_nil_iff, hrep]; exact Nat.le_refl n
      have hws : writeSubsliceAtIndex (List.replicate n (Gen.AbstractByte.Uninit : Byte))
          ((0 : Nat) : Int) bytesBM = .ok bytesBM := by
        unfold writeSubsliceAtIndex
        split
        · simp [hlenBM, hdrop]
        · exfalso; rename_i hneg; apply hneg; rw [hrep, hlenBM]; omega
      dsimp only [fcUnionTy, Type.encode, Type.encodeUnionChunks, List.length, bind, Except.bind,
        pure, Except.pure]
      simp only [ne_eq, hlenBM, not_true_eq_false, ↓reduceIte]
      rw [hws]
    unfold transmute
    simp only [hlayU, layout_eq ⟨s, ⟨n⟩⟩ hgood, bind, Except.bind, expect_size_sized,
      ne_eq, not_true_eq_false, ↓reduceIte, hencB, hdecB, ub]

/-- **Polymorphic `evalCastOpM (.Transmute ...)` size-mismatch UB** across *every* memory model `M`
(`BasicMemory` and `TreeBorrowsMemory`) and *every* source value `v`: mismatched widths (`4 ↔ 8`
across `u32`/`u64`, `[u8; 4]`/`[u8; 8]`, and thin raw pointers) raise UB before inspecting `v`. -/
theorem fc_mrM_evalCastOpM_size_mismatch_ub {M : Type} [Gen.Memory M] [MemoryOps M]
    (v : Gen.Value M) (m : Option (Gen.Machine M)) :
    evalCastOpM (M := M) (.Transmute (.Int fcU64It)) (v, .Int fcU32It) m =
      .error (.ub "transmute between types of different size") ∧
    evalCastOpM (M := M) (.Transmute (.Int fcU32It)) (v, .Int fcU64It) m =
      .error (.ub "transmute between types of different size") ∧
    evalCastOpM (M := M) (.Transmute (.Array (.Int fcU8It) 8)) (v, .Int fcU32It) m =
      .error (.ub "transmute between types of different size") ∧
    evalCastOpM (M := M) (.Transmute (.Int fcU64It)) (v, .Array (.Int fcU8It) 4) m =
      .error (.ub "transmute between types of different size") ∧
    evalCastOpM (M := M) (.Transmute (.Int fcU32It)) (v, .Ptr (.Raw .None)) m =
      .error (.ub "transmute between types of different size") :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem fc_encodePtrBytesM_len {M : Type} [Gen.Memory M]
    (prov : Option (Gen.Memory.Provenance M)) :
    ∀ (idx : Nat) (bs : List UInt8), (encodePtrBytesM (M := M) prov idx bs).length = bs.length
  | _, [] => rfl
  | idx, _ :: rest => congrArg Nat.succ (fc_encodePtrBytesM_len prov (idx + 1) rest)

private theorem fc_encodePtrBytesM_dataM_loop {M : Type} [Gen.Memory M]
    (prov : Option (Gen.Memory.Provenance M)) :
    ∀ (idx : Nat) (bs acc : List UInt8),
      List.mapM.loop AbstractByte.dataM (encodePtrBytesM (M := M) prov idx bs) acc =
        some (acc.reverse ++ bs)
  | _, [], acc => by simp [encodePtrBytesM, List.mapM.loop]
  | idx, b :: rest, acc => by
    dsimp only [encodePtrBytesM, List.mapM.loop, AbstractByte.dataM, bind, Option.bind]
    rw [fc_encodePtrBytesM_dataM_loop prov (idx + 1) rest (b :: acc)]
    simp [List.reverse_cons]

private theorem fc_encodePtrBytesM_dataM {M : Type} [Gen.Memory M]
    (prov : Option (Gen.Memory.Provenance M)) (idx : Nat) (bs : List UInt8) :
    (encodePtrBytesM (M := M) prov idx bs).mapM AbstractByte.dataM = some bs :=
  fc_encodePtrBytesM_dataM_loop prov idx bs []

private theorem fc_decodePtrProvenanceM_encode {M : Type} [Gen.Memory M] [MemoryOps M]
    (p : Gen.Memory.Provenance M) :
    ∀ (idx : Nat) (bs : List UInt8),
      decodePtrProvenanceM (M := M) idx (some p) (encodePtrBytesM (M := M) (some p) idx bs) = some p
  | _, [] => rfl
  | idx, _ :: rest => by
    dsimp only [encodePtrBytesM, decodePtrProvenanceM, AbstractByte.provenance_fragM, Option.map]
    simp only [and_self, ↓reduceIte]
    exact fc_decodePtrProvenanceM_encode p (idx + 1) rest

private theorem fc_decodePtrM_encodePtrBytesM {M : Type} [Gen.Memory M] [MemoryOps M]
    (prov : Option (Gen.Memory.Provenance M)) (addr : Nat) (haddr : addr < 2 ^ 64) :
    decodePtrM (M := M) (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) =
      .ok (some { addr := (addr : Int), provenance := prov }) := by
  have hbits' : addr < 2 ^ (8 * 8) := haddr
  have hdec := decode_leBytes .Unsigned 8 addr hbits'
  simp only [intFromBits] at hdec
  dsimp only [decodePtrM]
  simp only [ne_eq, fc_encodePtrBytesM_len, leBytes_length, x86_64.PTR_SIZE, not_true_eq_false,
    ↓reduceIte, fc_encodePtrBytesM_dataM, x86_64.ENDIANNESS, hdec, pure, Except.pure]
  cases prov with
  | none => rfl
  | some p =>
    have hf : firstProvenanceM (M := M) (encodePtrBytesM (M := M) (some p) 0 (leBytes addr 8)) =
        some p := rfl
    rw [hf, fc_decodePtrProvenanceM_encode (M := M) p 0 (leBytes addr 8)]

private theorem fc_decodeArray8_encodePtrBytesM {M : Type} [Gen.Memory M] [MemoryOps M]
    (prov : Option (Gen.Memory.Provenance M)) (addr : Nat) :
    Type.decodeM (M := M) (.Array (.Int fcU8It) 8)
      (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) =
      .ok (some (.Tuple (fcLeByteValsMRM addr 8))) := by
  rw [← fc_leBytesDecodeMRM_eq (M := M) addr 8]
  cases prov <;> rfl

private theorem fc_layout_rawPtrNone :
    Type.layout (.Ptr (.Raw .None)) = .ok (.Sized ⟨8⟩ ⟨8⟩) := rfl

private theorem fc_canRepresent_eq_inBounds (signed : Signedness) (size : LibSpecr.Size) (v : Int) :
    IntType.can_represent ⟨signed, size⟩ v = inBounds v signed size := rfl

private theorem fc_intFromBits_unsigned (n addr : Nat) :
    intFromBits addr ⟨.Unsigned, ⟨n⟩⟩ = (addr : Int) := rfl

private theorem fc_inBounds_u64 (addr : Nat) (haddr : addr < 2 ^ 64) :
    inBounds (addr : Int) .Unsigned ⟨8⟩ = true := by
  have hbits' : addr < 2 ^ (8 * (⟨.Unsigned, ⟨8⟩⟩ : Gen.IntType).size.bytes) := haddr
  have h := canRepresent_intFromBits ⟨.Unsigned, ⟨8⟩⟩ addr fc_goodSize_8 hbits'
  rw [fc_canRepresent_eq_inBounds, fc_intFromBits_unsigned] at h
  exact h

private theorem fc_encodePtrM_of_encode {M : Type} [Gen.Memory M]
    (ptr : Gen.ThinPointer (Gen.Memory.Provenance M)) (data : List UInt8)
    (henc : Endianness.encode x86_64.ENDIANNESS .Unsigned x86_64.PTR_SIZE ptr.addr = some data) :
    encodePtrM (M := M) ptr = .ok (encodePtrBytesM (M := M) ptr.provenance 0 data) := by
  unfold encodePtrM
  rw [henc]
  rfl

private theorem fc_encodePtrM_u64 {M : Type} [Gen.Memory M]
    (addr : Nat) (haddr : addr < 2 ^ 64) (prov : Option (Gen.Memory.Provenance M)) :
    encodePtrM (M := M) ⟨(addr : Int), prov⟩ =
      .ok (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) :=
  fc_encodePtrM_of_encode (M := M) ⟨(addr : Int), prov⟩ (leBytes addr 8) (encode_usize addr haddr)

private theorem fc_encodeIntM_of_encode {M : Type} [Gen.Memory M]
    (it : Gen.IntType) (v : Int) (data : List UInt8)
    (henc : Endianness.encode x86_64.ENDIANNESS it.signed it.size v = some data) :
    Type.encodeM (M := M) (.Int it) (.Int v) =
      .ok (data.map (fun b => Gen.AbstractByte.Init b none)) := by
  simp only [Type.encodeM, Type.encodeIntM, henc, pure, Except.pure]

private theorem fc_map_init_eq_encodePtrBytesM_none {M : Type} [Gen.Memory M] :
    ∀ (idx : Nat) (data : List UInt8),
      data.map (fun b => (Gen.AbstractByte.Init b none : Gen.AbstractByte (Gen.Memory.Provenance M))) =
        encodePtrBytesM (M := M) none idx data
  | _, [] => rfl
  | idx, b :: rest =>
    congrArg (Gen.AbstractByte.Init b none :: ·)
      (fc_map_init_eq_encodePtrBytesM_none (idx + 1) rest)

private theorem fc_encodeM_rawPtrNone {M : Type} [Gen.Memory M]
    (addr : Nat) (haddr : addr < 2 ^ 64) (prov : Option (Gen.Memory.Provenance M)) :
    Type.encodeM (M := M) (.Ptr (.Raw .None)) (.Ptr ⟨⟨(addr : Int), prov⟩, none⟩) =
      .ok (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) := by
  simp only [Type.encodeM, PtrType.as_wide_pair, PtrType.meta_kind, Option.map]
  exact fc_encodePtrM_u64 (M := M) addr haddr prov

private theorem fc_decodeM_rawPtrNone {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr : Nat) (haddr : addr < 2 ^ 64) (p' : Option (Gen.Memory.Provenance M)) :
    Type.decodeM (M := M) (.Ptr (.Raw .None))
      (encodePtrBytesM (M := M) p' 0 (leBytes addr 8)) =
      .ok (some (.Ptr ⟨⟨(addr : Int), p'⟩, none⟩)) := by
  simp only [Type.decodeM, PtrType.as_wide_pair, PtrType.meta_kind, Option.map,
    bind, Except.bind, pure, Except.pure, fc_decodePtrM_encodePtrBytesM (M := M) p' addr haddr]
  rfl

private theorem fc_checkPtrM_rawPtrNone {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr : Nat) (haddr : addr < 2 ^ 64) (p' : Option (Gen.Memory.Provenance M))
    (m : Option (Gen.Machine M)) :
    checkPtrM (M := M) ⟨⟨(addr : Int), p'⟩, none⟩ (.Raw .None) m = .ok () := by
  unfold checkPtrM
  have hp : x86_64.PTR_SIZE = ⟨8⟩ := rfl
  rw [hp, fc_inBounds_u64 addr haddr]
  rfl

private theorem fc_checkValueM_rawPtrNone {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr : Nat) (haddr : addr < 2 ^ 64) (p' : Option (Gen.Memory.Provenance M))
    (m : Option (Gen.Machine M)) :
    checkValueM (M := M) (.Ptr ⟨⟨(addr : Int), p'⟩, none⟩) (.Ptr (.Raw .None)) m = .ok () := by
  simp only [checkValueM]
  exact fc_checkPtrM_rawPtrNone (M := M) addr haddr p' m

private theorem fc_transmuteM_of_steps {M : Type} [Gen.Memory M] [MemoryOps M]
    (v v' : Gen.Value M) (ty1 ty2 : Gen.Type) (sz : LibSpecr.Size) (a1 a2 : LibSpecr.Align)
    (bytes : List (Gen.AbstractByte (Gen.Memory.Provenance M))) (m : Option (Gen.Machine M))
    (hl1 : Type.layout ty1 = .ok (.Sized sz a1))
    (hl2 : Type.layout ty2 = .ok (.Sized sz a2))
    (henc : Type.encodeM (M := M) ty1 v = .ok bytes)
    (hdec : Type.decodeM (M := M) ty2 bytes = .ok (some v'))
    (hchk : checkValueM (M := M) v' ty2 m = .ok ()) :
    transmuteM (M := M) v ty1 ty2 m = .ok v' := by
  unfold transmuteM
  simp only [hl1, hl2, bind, Except.bind, expect_size_sized, ne_eq, not_true_eq_false, ↓reduceIte,
    henc, hdec, hchk, pure, Except.pure]

private theorem fc_decodeIntM_encodePtrBytesM {M : Type} [Gen.Memory M] [MemoryOps M]
    (s : Signedness) (addr : Nat) (haddr : addr < 2 ^ 64)
    (prov : Option (Gen.Memory.Provenance M)) :
    Type.decodeM (M := M) (.Int ⟨s, ⟨8⟩⟩) (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) =
      .ok (some (.Int (intFromBits addr ⟨s, ⟨8⟩⟩))) := by
  have hbits' : addr < 2 ^ (8 * 8) := haddr
  simp only [Type.decodeM, Type.decodeIntM, fc_encodePtrBytesM_len, leBytes_length, ne_eq,
    not_true_eq_false, ↓reduceIte, fc_encodePtrBytesM_dataM, x86_64.ENDIANNESS,
    decode_leBytes s 8 addr hbits', pure, Except.pure]

/-- **Polymorphic pointer-provenance `transmuteM` boundary in MiniRust**, valid across *every*
memory model `M` (`BasicMemory` and `TreeBorrowsMemory`), *every* 64-bit address `addr < 2 ^ 64`,
and *every* provenance `prov`:
1. Transmuting `.Ptr ⟨⟨addr, prov⟩, none⟩` at `.Ptr (.Raw .None)` (`*const f32`, `*const u32`, ...)
   to `.Int ⟨s, ⟨8⟩⟩` (`u64` or `i64`) **succeeds and strips provenance** (contrast Anneal, where
   pointer-to-integer/float transmute is UB!).
2. Transmuting `.Ptr ⟨⟨addr, prov⟩, none⟩` to `[u8; 8]` **succeeds and strips provenance** into
   8 `u8` elements (contrast Anneal, where `ptr -> [u8; 8]` is UB!).
3. Transmuting `.Ptr ⟨⟨addr, prov⟩, none⟩` to `.Ptr (.Raw .None)` **preserves both `addr` and
   `prov` intact** (under both `BasicMemory` and `TreeBorrowsMemory`).
4. Transmuting `u64` (`addr`) to `.Ptr (.Raw .None)` produces the provenance-free raw pointer
   `⟨⟨addr, none⟩, none⟩`. -/
theorem fc_mrM_transmute_ptr_boundary {M : Type} [Gen.Memory M] [MemoryOps M]
    (s : Signedness) (addr : Nat) (haddr : addr < 2 ^ 64)
    (prov : Option (Gen.Memory.Provenance M)) (m : Option (Gen.Machine M)) :
    transmuteM (M := M) (.Ptr ⟨⟨(addr : Int), prov⟩, none⟩) (.Ptr (.Raw .None))
        (.Int ⟨s, ⟨8⟩⟩) m = .ok (.Int (intFromBits addr ⟨s, ⟨8⟩⟩)) ∧
    transmuteM (M := M) (.Ptr ⟨⟨(addr : Int), prov⟩, none⟩) (.Ptr (.Raw .None))
        (.Array (.Int fcU8It) 8) m = .ok (.Tuple (fcLeByteValsMRM addr 8)) ∧
    transmuteM (M := M) (.Ptr ⟨⟨(addr : Int), prov⟩, none⟩) (.Ptr (.Raw .None))
        (.Ptr (.Raw .None)) m = .ok (.Ptr ⟨⟨(addr : Int), prov⟩, none⟩) ∧
    transmuteM (M := M) (.Int (addr : Int)) (.Int fcU64It)
        (.Ptr (.Raw .None)) m = .ok (.Ptr ⟨⟨(addr : Int), none⟩, none⟩) := by
  have hbits' : addr < 2 ^ (8 * 8) := haddr
  have hrepS := canRepresent_intFromBits ⟨s, ⟨8⟩⟩ addr fc_goodSize_8 hbits'
  have hchkS : checkValueM (M := M) (.Int (intFromBits addr ⟨s, ⟨8⟩⟩)) (.Int ⟨s, ⟨8⟩⟩) m =
      .ok () := by
    simp only [checkValueM, ensureElseUb, hrepS, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      pure, Except.pure]
  have hlayA : Type.layout (.Array (.Int fcU8It) 8) = .ok (.Sized ⟨8⟩ ⟨1⟩) := rfl
  have hchkA : checkValueM (M := M) (.Tuple (fcLeByteValsMRM addr 8))
      (.Array (.Int fcU8It) 8) m = .ok () := by
    dsimp only [fcLeByteValsMRM, checkValueM, ensureElseUb, List.length, List.forM,
      bind, Except.bind, pure, Except.pure]
    simp only [IntType.can_represent, fcU8It, fc_u8_inBounds_mod, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]; rfl
  have hencU : Type.encodeM (M := M) (.Int fcU64It) (.Int (addr : Int)) =
      .ok (encodePtrBytesM (M := M) none 0 (leBytes addr 8)) := by
    rw [← fc_map_init_eq_encodePtrBytesM_none (M := M) 0 (leBytes addr 8)]
    exact fc_encodeIntM_of_encode (M := M) fcU64It (addr : Int) (leBytes addr 8)
      (encode_usize addr haddr)
  exact ⟨
    fc_transmuteM_of_steps _ _ _ _ _ _ _ _ m fc_layout_rawPtrNone (layout_eq ⟨s, ⟨8⟩⟩ fc_goodSize_8)
      (fc_encodeM_rawPtrNone (M := M) addr haddr prov)
      (fc_decodeIntM_encodePtrBytesM (M := M) s addr haddr prov) hchkS,
    fc_transmuteM_of_steps _ _ _ _ _ _ _ _ m fc_layout_rawPtrNone hlayA
      (fc_encodeM_rawPtrNone (M := M) addr haddr prov)
      (fc_decodeArray8_encodePtrBytesM (M := M) prov addr) hchkA,
    fc_transmuteM_of_steps _ _ _ _ _ _ _ _ m fc_layout_rawPtrNone fc_layout_rawPtrNone
      (fc_encodeM_rawPtrNone (M := M) addr haddr prov)
      (fc_decodeM_rawPtrNone (M := M) addr haddr prov)
      (fc_checkValueM_rawPtrNone (M := M) addr haddr prov m),
    fc_transmuteM_of_steps _ _ _ _ _ _ _ _ m (layout_eq fcU64It fc_goodSize_8) fc_layout_rawPtrNone
      hencU (fc_decodeM_rawPtrNone (M := M) addr haddr none)
      (fc_checkValueM_rawPtrNone (M := M) addr haddr none m)⟩

/-- **Anneal pointer-provenance transmute and float-cast boundary**:
1. Transmuting `Value.ptr p 8` to `[u8; 8]` (`fcBytes8Ty`) or `i64` (`fcI64Ty`) is **UB** (`.ub`),
   because integer/byte-array elements reject pointer provenance (`abstractBytesHaveProv = true`).
2. Transmuting `Value.ptr p 8` (`p.offsetBytes < 2 ^ 64`) to `*const u8` (`fcRawPtrU8Ty`) **succeeds**
   and decodes via `decodePtrBytesNoForge` to `.ptr { allocId := p.allocId, offsetBytes := p.offsetBytes } 8`
   (` locals' mem`).
3. Transmuting a `f64`/`u64` scalar `⟨bits, 8⟩` (`bits < 2 ^ 64`) to `*const u8` (`fcRawPtrU8Ty`)
   **never fabricates provenance**, yielding `.ok (.scalar ⟨bits, 8⟩) locals' mem`, whereas
   transmuting it to `&u8` (`isRef = true`) is **UB** (`.ub`).
4. Applying numeric `CastKind.floatToInt` or `CastKind.floatToFloat` to `Value.ptr p 8` fails closed
   (`.unsupported`). -/
theorem fc_anneal_ptr_transmute_and_cast_boundary
    {locals locals' : List LocalSlot} {op opScalar : Operand} {mem : Memory}
    {decls : List LocalDecl} {p : ProvenancePtr} (hp : p.offsetBytes < 2 ^ 64)
    {bits : Nat} (hbits : bits < 2 ^ 64)
    (hOpPtr : evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok (.ptr p 8) locals')
    (hTyPtr : operandTy decls fcLayouts op = some fcRawPtrU8Ty)
    (hOpSc : evalOperand locals opScalar mem.borrows mem.globals fcLayouts mem.callerLocals decls
      mem.callStack = .ok (.scalar ⟨bits, 8⟩) locals')
    (hTySc : operandTy decls fcLayouts opScalar = some fcF64Ty) :
    evalRvalue locals (.cast .transmute op fcBytes8Ty) mem decls fcLayouts = .ub ∧
    evalRvalue locals (.cast .transmute op fcI64Ty) mem decls fcLayouts = .ub ∧
    evalRvalue locals (.cast .transmute op fcRawPtrU8Ty) mem decls fcLayouts =
      .ok (.ptr { allocId := p.allocId, offsetBytes := p.offsetBytes } 8) locals' mem ∧
    evalRvalue locals (.cast .transmute opScalar fcRawPtrU8Ty) mem decls fcLayouts =
      .ok (.scalar ⟨bits, 8⟩) locals' mem ∧
    evalRvalue locals (.cast .transmute opScalar ⟨.ref .not (.uint .u8), 12⟩)
        mem decls fcLayouts = .ub ∧
    evalRvalue locals (.cast .floatToInt op fcI64Ty) mem decls fcLayouts = .unsupported ∧
    evalRvalue locals (.cast .floatToFloat op fcF64Ty) mem decls fcLayouts = .unsupported := by
  have hp256 : p.offsetBytes < 256 ^ 8 := fc_lt_256_pow_8 hp
  have hb256 : bits < 256 ^ 8 := fc_lt_256_pow_8 hbits
  have hEncPtr : encodeByteCastSourceBytes fcLayouts
      (resolveTyWithLocalDecls decls fcLayouts fcRawPtrU8Ty) (.ptr p 8) =
      some (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) := rfl
  have hLenPtr := fc_seqLength_encodeLittleEndianBytes (some (p.allocId, p.tag)) 8 p.offsetBytes
  have hEncSc : encodeByteCastSourceBytes fcLayouts
      (resolveTyWithLocalDecls decls fcLayouts fcF64Ty) (.scalar ⟨bits, 8⟩) =
      some (encodeLittleEndianBytes bits 8 none) := rfl
  have hLenSc := fc_seqLength_encodeLittleEndianBytes none 8 bits
  let refU8Ty : Ty := ⟨.ref .not (.uint .u8), 12⟩
  have hSzRef : tyByteSize decls fcLayouts (resolveTyWithLocalDecls decls fcLayouts refU8Ty) =
      some 8 := rfl
  have hResPtr : resolveTyWithLocalDecls decls fcLayouts fcRawPtrU8Ty = fcRawPtrU8Ty := rfl
  have hResRef : resolveTyWithLocalDecls decls fcLayouts refU8Ty = refU8Ty := rfl
  refine ⟨?_, (fc_transmute_ptr_to_f64_ub hOpPtr hTyPtr).2.2, ?_, ?_, ?_, ?_, ?_⟩
  · have hDecB8 : decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcBytes8Ty
        (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) = none := rfl
    show evalByteCast locals op fcBytes8Ty mem decls fcLayouts = _
    rw [fc_evalByteCast_of_encode locals locals' op mem decls fcLayouts _ _ _ 8 _ hOpPtr
      (fc_tyByteSize_bytes8 decls) hTyPtr (fc_tyByteSize_rawPtrU8 decls) hEncPtr hLenPtr,
      fc_resolve_bytes8, hDecB8]
  · have hUnif : abstractBytesUniformProv
        (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) = true := by
      simp [abstractBytesUniformProv, abstractBytesAllProvAux, Nat.beq_refl]
    have hDecPtr : decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcRawPtrU8Ty
        (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) =
        some (.ptr { allocId := p.allocId, offsetBytes := p.offsetBytes } 8) := by
      change decodePtrBytesNoForge false (.uint .u8) 8
          (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) = _
      dsimp only [decodePtrBytesNoForge]
      rw [fc_seqLength_encodeLittleEndianBytes,
        fc_decodeScalarBytes_encode (some (p.allocId, p.tag)) false 7 p.offsetBytes hp256, hUnif]
    show evalByteCast locals op fcRawPtrU8Ty mem decls fcLayouts = _
    rw [fc_evalByteCast_of_encode locals locals' op mem decls fcLayouts _ _ _ 8 _ hOpPtr
      (fc_tyByteSize_rawPtrU8 decls) hTyPtr (fc_tyByteSize_rawPtrU8 decls) hEncPtr hLenPtr,
      hResPtr, hDecPtr]
  · have hDecSc : decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcRawPtrU8Ty
        (encodeLittleEndianBytes bits 8 none) = some (.scalar ⟨bits, 8⟩) := by
      change decodePtrBytesNoForge false (.uint .u8) 8 (encodeLittleEndianBytes bits 8 none) = _
      dsimp only [decodePtrBytesNoForge]
      rw [fc_seqLength_encodeLittleEndianBytes,
        fc_decodeScalarBytes_encode none false 7 bits hb256]
    show evalByteCast locals opScalar fcRawPtrU8Ty mem decls fcLayouts = _
    rw [fc_evalByteCast_of_encode locals locals' opScalar mem decls fcLayouts _ _ _ 8 _ hOpSc
      (fc_tyByteSize_rawPtrU8 decls) hTySc (fc_tyByteSize_f64 decls) hEncSc hLenSc,
      hResPtr, hDecSc]
  · have hDecRef : decodeTypedValueFromBytes defaultCodecFuel fcLayouts refU8Ty
        (encodeLittleEndianBytes bits 8 none) = none := by
      change decodePtrBytesNoForge true (.uint .u8) 8 (encodeLittleEndianBytes bits 8 none) = _
      dsimp only [decodePtrBytesNoForge]
      rw [fc_seqLength_encodeLittleEndianBytes,
        fc_decodeScalarBytes_encode none false 7 bits hb256]
    show evalByteCast locals opScalar refU8Ty mem decls fcLayouts = _
    rw [fc_evalByteCast_of_encode locals locals' opScalar mem decls fcLayouts _ _ _ 8 _ hOpSc
      hSzRef hTySc (fc_tyByteSize_f64 decls) hEncSc hLenSc,
      hResRef, hDecRef]
  · show evalFloatCastRvalue locals .floatToInt op fcI64Ty mem decls fcLayouts = _
    unfold evalFloatCastRvalue; rw [hOpPtr, hTyPtr]; rfl
  · show evalFloatCastRvalue locals .floatToFloat op fcF64Ty mem decls fcLayouts = _
    unfold evalFloatCastRvalue; rw [hOpPtr, hTyPtr]; rfl


/-! ## 14. Symbolic MiniRust machine executions and 64-bit / narrowing / exact `int → float`
bit-carrier bridges (`[adv shard-b A1]`)

`fc_carrier_runs` exercises MiniRust's `Interp.steps` / `Interp.stepsTB` only on three concrete
32-bit carriers. Here the library's whole-execution simulation theorem `mirCall_ret`
(`Correspondence/Run.lean`) lifts Anneal's *symbolic* run of the fragment carrier
`fn(x: u32) -> i32 { x as i32 }` (an equal-width `IntToInt` cast moves the bits exactly as the
transmute does; `minimize`'s translation of an integer-to-integer transmute is outside
`inFragment`) to a MiniRust `BasicMemory` execution for *every* 32-bit pattern, ending with
Anneal's little-endian bytes in the caller's return place. -/

/-- `fn carrier_cast(x: u32) -> i32 { x as i32 }`: the fragment form of the `u32 → i32` bit
carrier (`_0 = copy _1 as i32 (IntToInt)`). -/
def fcCarrierCastBody : CapturedMir :=
  ptrBody "float_cast::carrier_cast_u32_i32" [i32Decl, u32Decl]
    [.assign (local_ 0) (.cast .intToInt (.copy (local_ 1)) i32Ty)]

theorem fc_carrierCast_inFragment : inFragment fcCarrierCastBody = true := by decide +kernel

theorem fc_carrierCast_ctxOk : CtxOk fcCarrierCastBody ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd
    match i, hd with
    | 0, hd => simp only [fcCarrierCastBody, ptrBody] at hd; cases hd; decide
    | 1, hd => simp only [fcCarrierCastBody, ptrBody] at hd; cases hd; decide
    | _ + 2, hd => simp [fcCarrierCastBody, ptrBody] at hd
  ret := by
    intro d hd
    simp only [fcCarrierCastBody, ptrBody] at hd
    cases hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem fc_carrierCast_argsOk (bits : Nat) (h : bits < 2 ^ 32) :
    argsOk fcCarrierCastBody [.scalar ⟨bits, 4⟩] = true := by
  have h' : bits < 2 ^ (8 * 4) := h
  simp [argsOk, argsOkAux, declArgOk, fcCarrierCastBody, ptrBody, u32Decl, u32Ty, argOk, tyOf,
    translateTy, scalarTypeOf, isBoolTy, isOrderingTy, intBoolTupleOf, intTypeOf, intTyBytes,
    tyBytes, validBits, h']

theorem fc_wrapScalarBits_of_lt {val modulus : Nat} (h : val < modulus) :
    wrapScalarBits val modulus = val := by
  unfold wrapScalarBits
  have : Nat.ble modulus val = false := by
    cases hb : Nat.ble modulus val with
    | false => rfl
    | true => exact absurd (Nat.le_of_ble_eq_true hb) (Nat.not_le.mpr h)
  rw [this]

/-- Kernel-computed symbolic Anneal run of the fragment carrier. -/
theorem fc_run_carrierCast_raw (bits : Nat) : ∃ mem, runA fcCarrierCastBody 10
    (initMachineState fcCarrierCastBody [.scalar ⟨bits, 4⟩]) =
      some ([], .normal (.scalar ⟨wrapScalarBits bits (scalarModulus 4), 4⟩, mem)) := ⟨_, rfl⟩

/-- Anneal: the carrier returns its argument's bits unchanged, for every 32-bit pattern. -/
theorem fc_sym_carrierCast_anneal (bits : Nat) (h : bits < 2 ^ 32) :
    ∃ mem, ReachesRet (mirCallTree fcCarrierCastBody [.scalar ⟨bits, 4⟩]) []
      (.normal (.scalar ⟨bits, 4⟩, mem)) := by
  obtain ⟨mem, hrun⟩ := fc_run_carrierCast_raw bits
  rw [fc_wrapScalarBits_of_lt (show bits < scalarModulus 4 from h)] at hrun
  exact ⟨mem, runA_sound _ _ _ _ _ hrun⟩

/-- **Symbolic MiniRust `Interp.steps` (`BasicMemory`) execution of the bit carrier**: for
*every* 32-bit pattern `bits`, the MiniRust machine running `minimize`'s translation of the
carrier from its start reaches, after finitely many `Machine::step`s, the state in which the callee
has returned (only the caller's frame is left) and the caller's return place holds exactly
Anneal's little-endian encoding of `bits` (`fcByteToMR` image). -/
theorem fc_sym_mr_carrier_steps (bits : Nat) (h : bits < 2 ^ 32) :
    ∃ (m : Mach) (n : Nat) (m' : Mach),
      startMachine fcCarrierCastBody [.scalar ⟨bits, 4⟩] = some m ∧
      Interp.steps n m = .ok m' ∧
      m'.threads = [thread1 ctx0 [{ ctx0.caller with next_block := ctx0.nextBlock, next_stmt := 0 }]] ∧
      m'.mem.memory.allocations[0]? =
        some { retAlloc with data := (encodeLittleEndianBytes bits 4 none).map fcByteToMR } := by
  obtain ⟨f, hf⟩ : ∃ f, translateFn fcCarrierCastBody = some f := ⟨_, rfl⟩
  obtain ⟨mem, hret⟩ := fc_sym_carrierCast_anneal bits h
  let m := machine fcCarrierCastBody f
    (initMachineState fcCarrierCastBody [.scalar ⟨bits, 4⟩]).frame.locals f.start
  have hm : startMachine fcCarrierCastBody [.scalar ⟨bits, 4⟩] = some m := by
    simp [startMachine, hf, m]
  obtain ⟨n, s', m', hsteps, hrel⟩ := mirCall_ret fc_carrierCast_inFragment hf ctx0
    fc_carrierCast_ctxOk [.scalar ⟨bits, 4⟩] (fc_carrierCast_argsOk bits h) m rfl rfl rfl hret
  obtain ⟨r, a, d, R, hd, _, hprov, ha, hthreads, hallocs, _⟩ := hrel
  simp only [fcCarrierCastBody, ptrBody, List.getElem?_cons_zero, Option.some.injEq] at hd
  have hr : r = 0 := by
    simp only [ctx0, retPtr, Option.some.injEq, Prod.mk.injEq, and_true] at hprov
    have h0 : (r : Int) = 0 := (congrArg Gen.AllocId._0 hprov).symm
    omega
  subst hr hd
  simp only [ctx0, List.getElem?_cons_zero, Option.some.injEq] at ha
  subst ha
  refine ⟨m, n, m', hm, hsteps, hthreads, ?_⟩
  rw [hallocs, fc_map_encodeLittleEndianBytes .Signed none 4 bits]
  rfl

/-- **Symbolic end-to-end bridge through the MiniRust machine**: for every 32-bit pattern `x`,
Anneal's multi-step run of `f32::from_bits(x) as i32` returns a carrier `r`; MiniRust's
`BasicMemory` machine running the translated carrier on `r` returns exactly Anneal's bytes of `r`,
which MiniRust decodes at `i32` to the saturated truncation `floatToIntValue (decodeBits x)`. -/
theorem fc_sym_e2e_from_bits_as_i32_machine (bits : Nat) (h : bits < 2 ^ 32) :
    (∃ mem, ReachesRet (mirCallTree fcFromBitsAsI32Body [.scalar ⟨bits, 4⟩]) []
      (.normal (.scalar (evalFloatToIntSaturating .binary32 bits (.signed .i32) .bits64), mem))) ∧
    (∃ (m : Mach) (n : Nat) (m' : Mach),
      startMachine fcCarrierCastBody
          [.scalar ⟨(evalFloatToIntSaturating .binary32 bits (.signed .i32) .bits64).bits, 4⟩] =
        some m ∧
      Interp.steps n m = .ok m' ∧
      m'.mem.memory.allocations[0]? =
        some { retAlloc with
          data := List.map fcByteToMR (encodeLittleEndianBytes
            (evalFloatToIntSaturating .binary32 bits (.signed .i32) .bits64).bits 4 none) }) ∧
    Type.decode (.Int fcI32It)
        ((encodeLittleEndianBytes (evalFloatToIntSaturating .binary32 bits (.signed .i32)
          .bits64).bits 4 none).map fcByteToMR) =
      .ok (some (.Int (floatToIntValue (decodeBits .binary32 bits) (-2147483648) 2147483647))) := by
  obtain ⟨_, hlt, _, _, hdec⟩ :=
    fc_bridge_floatToInt .binary32 bits (.signed .i32) 4 rfl fc_goodSize_4
  obtain ⟨m, n, m', hm, hs, _, ha⟩ := fc_sym_mr_carrier_steps _ hlt
  exact ⟨(fc_sym_from_bits_as_i32 bits h).1, ⟨m, n, m', hm, hs, ha⟩, hdec⟩

/-! ### 14.0 The 64-bit carrier under an 8-byte return place

`ctx0`'s return place is 4 bytes, so the `u64 → i64` carrier runs under `fcCtx8`, which differs
from `ctx0` only by an 8-byte, 8-aligned return place and a caller whose `_0` is a `u64`. -/

/-- `u64` / `i64` with layout index `0` (layout-free fragment types). -/
def fcU64Ty0 : Ty := { kind := .uint .u64, layoutIdx := 0 }
def fcI64Ty0 : Ty := { kind := .int .i64, layoutIdx := 0 }

/-- The caller's 8-byte return place: allocation `0` at address `64`. -/
def fcRetAlloc8 : Gen.Allocation :=
  { data := List.replicate 8 .Uninit, addr := 64, align := ⟨8⟩, kind := .Stack, live := true,
    extra := () }

def fcCallerFn8 : Gen.Function where
  locals := ⟨[(localName 0, .Int fcU64It)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[]⟩
  start := bbName 0
  implicit_writes := true

def fcCallerFrame8 : Frame :=
  { func := fcCallerFn8, locals := ⟨[(localName 0, retPtr)]⟩, stack_pop_action := .BottomOfStack,
    next_block := bbName 0, next_stmt := 0, extra := () }

/-- `ctx0` with an 8-byte return place. -/
def fcCtx8 : Ctx :=
  { caller := fcCallerFrame8, payloads := [], base := [fcRetAlloc8], addrs := [128, 256],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

/-- `fn carrier_cast64(x: u64) -> i64 { x as i64 }`: the fragment form of the `u64 → i64` bit
carrier. -/
def fcCarrierCast64Body : CapturedMir :=
  ptrBody "float_cast::carrier_cast_u64_i64" [fcDecl fcI64Ty0, fcDecl fcU64Ty0]
    [.assign (local_ 0) (.cast .intToInt (.copy (local_ 1)) fcI64Ty0)]

theorem fc_carrierCast64_inFragment : inFragment fcCarrierCast64Body = true := by decide +kernel

theorem fc_carrierCast64_ctxOk : CtxOk fcCarrierCast64Body fcCtx8 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd
    match i, hd with
    | 0, hd => simp only [fcCarrierCast64Body, ptrBody] at hd; cases hd; decide
    | 1, hd => simp only [fcCarrierCast64Body, ptrBody] at hd; cases hd; decide
    | _ + 2, hd => simp [fcCarrierCast64Body, ptrBody] at hd
  ret := by
    intro d hd
    simp only [fcCarrierCast64Body, ptrBody] at hd
    cases hd
    exact ⟨0, fcRetAlloc8, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem fc_carrierCast64_argsOk (bits : Nat) (h : bits < 2 ^ 64) :
    argsOk fcCarrierCast64Body [.scalar ⟨bits, 8⟩] = true := by
  have h' : bits < 2 ^ (8 * 8) := h
  simp [argsOk, argsOkAux, declArgOk, fcCarrierCast64Body, ptrBody, fcDecl, fcU64Ty0, argOk,
    tyOf, translateTy, scalarTypeOf, isBoolTy, isOrderingTy, intBoolTupleOf, intTypeOf,
    intTyBytes, tyBytes, validBits, h']

theorem fc_run_carrierCast64_raw (bits : Nat) : ∃ mem, runA fcCarrierCast64Body 10
    (initMachineState fcCarrierCast64Body [.scalar ⟨bits, 8⟩]) =
      some ([], .normal (.scalar ⟨wrapScalarBits bits (scalarModulus 8), 8⟩, mem)) := ⟨_, rfl⟩

theorem fc_sym_carrierCast64_anneal (bits : Nat) (h : bits < 2 ^ 64) :
    ∃ mem, ReachesRet (mirCallTree fcCarrierCast64Body [.scalar ⟨bits, 8⟩]) []
      (.normal (.scalar ⟨bits, 8⟩, mem)) := by
  obtain ⟨mem, hrun⟩ := fc_run_carrierCast64_raw bits
  rw [fc_wrapScalarBits_of_lt (show bits < scalarModulus 8 from h)] at hrun
  exact ⟨mem, runA_sound _ _ _ _ _ hrun⟩

/-- **Symbolic MiniRust `Interp.steps` (`BasicMemory`) execution of the 64-bit bit carrier**: for
*every* 64-bit pattern `bits`, the MiniRust machine running the translated `u64 → i64` carrier
from its start (under `fcCtx8`) returns to the caller with exactly Anneal's little-endian encoding
of `bits` in the 8-byte return place. -/
theorem fc_sym_mr_carrier64_steps (bits : Nat) (h : bits < 2 ^ 64) :
    ∃ (f : Gen.Function) (n : Nat) (m' : Mach),
      translateFn fcCarrierCast64Body = some f ∧
      Interp.steps n (machineWithCtx fcCtx8 fcCarrierCast64Body f
        (initMachineState fcCarrierCast64Body [.scalar ⟨bits, 8⟩]).frame.locals f.start) =
        .ok m' ∧
      m'.threads =
        [thread1 fcCtx8 [{ fcCtx8.caller with next_block := fcCtx8.nextBlock, next_stmt := 0 }]] ∧
      m'.mem.memory.allocations[0]? =
        some { fcRetAlloc8 with data := (encodeLittleEndianBytes bits 8 none).map fcByteToMR } := by
  obtain ⟨f, hf⟩ : ∃ f, translateFn fcCarrierCast64Body = some f := ⟨_, rfl⟩
  obtain ⟨mem, hret⟩ := fc_sym_carrierCast64_anneal bits h
  obtain ⟨n, s', m', hsteps, hrel⟩ := mirCall_ret fc_carrierCast64_inFragment hf fcCtx8
    fc_carrierCast64_ctxOk [.scalar ⟨bits, 8⟩] (fc_carrierCast64_argsOk bits h)
    (machineWithCtx fcCtx8 fcCarrierCast64Body f
      (initMachineState fcCarrierCast64Body [.scalar ⟨bits, 8⟩]).frame.locals f.start)
    rfl rfl rfl hret
  obtain ⟨r, a, d, R, hd, _, hprov, ha, hthreads, hallocs, _⟩ := hrel
  simp only [fcCarrierCast64Body, ptrBody, List.getElem?_cons_zero, Option.some.injEq] at hd
  have hr : r = 0 := by
    simp only [fcCtx8, retPtr, Option.some.injEq, Prod.mk.injEq, and_true] at hprov
    have h0 : (r : Int) = 0 := (congrArg Gen.AllocId._0 hprov).symm
    omega
  subst hr hd
  simp only [fcCtx8, List.getElem?_cons_zero, Option.some.injEq] at ha
  subst ha
  refine ⟨f, n, m', hf, hsteps, hthreads, ?_⟩
  rw [hallocs, fc_map_encodeLittleEndianBytes .Signed none 8 bits]
  rfl

/-- **Symbolic end-to-end `f64` bridge through the MiniRust machine**: for every 32-bit pattern
`x`, Anneal's run of `(f32::from_bits(x) as f64).to_bits()` returns the `u64` carrier
`r = evalFloatToFloatRoundTiesToEven .binary32 .binary64 x`, and MiniRust's `BasicMemory` machine
running the translated 64-bit carrier on `r` returns exactly Anneal's bytes of `r`. -/
theorem fc_sym_e2e_widen_bits_machine (bits : Nat) (h : bits < 2 ^ 32) :
    (∃ mem, ReachesRet (mirCallTree fcWidenBitsBody [.scalar ⟨bits, 4⟩]) []
      (.normal (.scalar ⟨evalFloatToFloatRoundTiesToEven .binary32 .binary64 bits, 8⟩, mem))) ∧
    ∃ (f : Gen.Function) (n : Nat) (m' : Mach),
      translateFn fcCarrierCast64Body = some f ∧
      Interp.steps n (machineWithCtx fcCtx8 fcCarrierCast64Body f
        (initMachineState fcCarrierCast64Body
          [.scalar ⟨evalFloatToFloatRoundTiesToEven .binary32 .binary64 bits, 8⟩]).frame.locals
        f.start) = .ok m' ∧
      m'.mem.memory.allocations[0]? =
        some { fcRetAlloc8 with
          data := List.map fcByteToMR (encodeLittleEndianBytes
            (evalFloatToFloatRoundTiesToEven .binary32 .binary64 bits) 8 none) } := by
  have hlt : evalFloatToFloatRoundTiesToEven .binary32 .binary64 bits < 2 ^ 64 :=
    Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt _ _ _
  obtain ⟨f, n, m', hf, hs, _, ha⟩ := fc_sym_mr_carrier64_steps _ hlt
  exact ⟨(fc_sym_widen_bits bits h).1, f, n, m', hf, hs, ha⟩

/-! ### 14.1 `f64` carriers: `f64::from_bits(x) as i64` and narrowing `f64 → f32` -/

/-- `fn f64_from_bits_as_i64(x: u64) -> i64 { f64::from_bits(x) as i64 }`. -/
def fcF64FromBitsAsI64Body : CapturedMir :=
  fcBody "float_cast::f64_from_bits_as_i64" [fcDecl fcI64Ty, fcDecl fcU64Ty, fcDecl fcF64Ty]
    [.storageLive 2,
     .assign (local_ 2) (.cast .transmute (.copy (local_ 1)) fcF64Ty),
     .assign (local_ 0) (.cast .floatToInt (.copy (local_ 2)) fcI64Ty),
     .storageDead 2]

/-- `fn narrow_bits(x: u64) -> u32 { (f64::from_bits(x) as f32).to_bits() }`. -/
def fcNarrowBitsBody : CapturedMir :=
  fcBody "float_cast::narrow_bits" [fcDecl fcU32Ty, fcDecl fcU64Ty, fcDecl fcF64Ty, fcDecl fcF32Ty]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.cast .transmute (.copy (local_ 1)) fcF64Ty),
     .assign (local_ 3) (.cast .floatToFloat (.copy (local_ 2)) fcF32Ty),
     .assign (local_ 0) (.cast .transmute (.copy (local_ 3)) fcU32Ty),
     .storageDead 3, .storageDead 2]

theorem fc_run_f64_from_bits_as_i64_raw (bits : Nat) : ∃ mem, runA fcF64FromBitsAsI64Body 10
    (initMachineState fcF64FromBitsAsI64Body [.scalar ⟨bits, 8⟩]) =
      some ([], .normal (.scalar (evalFloatToIntSaturating .binary64 (fcLeRound 8 bits)
        (.signed .i64) .bits64), mem)) := ⟨_, rfl⟩

theorem fc_run_narrow_bits_raw (bits : Nat) : ∃ mem, runA fcNarrowBitsBody 12
    (initMachineState fcNarrowBitsBody [.scalar ⟨bits, 8⟩]) =
      some ([], .normal (.scalar ⟨fcLeRound 4 (evalFloatToFloatRoundTiesToEven .binary64 .binary32
        (fcLeRound 8 bits)), 4⟩, mem)) := ⟨_, rfl⟩

/-- **Symbolic 64-bit end-to-end bridge (`FloatToInt` on `f64`)**: for every 64-bit pattern `x`,
Anneal's multi-step run of `f64::from_bits(x) as i64` returns, free of UB, the `i64` carrier `r`
of `evalFloatToIntSaturating .binary64 x`, whose bytes MiniRust decodes at `i64` to the saturated
truncation `floatToIntValue (decodeBits .binary64 x)`, and which MiniRust's `transmuteM` moves from
the `u64` carrier to `i64` with that same value over both `BasicMemory` and `TreeBorrowsMemory`. -/
theorem fc_sym_e2e_f64_from_bits_as_i64 (bits : Nat) (h : bits < 2 ^ 64) :
    (∃ mem, ReachesRet (mirCallTree fcF64FromBitsAsI64Body [.scalar ⟨bits, 8⟩]) []
      (.normal (.scalar (evalFloatToIntSaturating .binary64 bits (.signed .i64) .bits64), mem))) ∧
    MirNoUBTree (mirCallTree fcF64FromBitsAsI64Body [.scalar ⟨bits, 8⟩]) ∧
    Type.decode (.Int fcI64It)
        ((encodeLittleEndianBytes (evalFloatToIntSaturating .binary64 bits (.signed .i64)
          .bits64).bits 8 none).map fcByteToMR) =
      .ok (some (.Int (floatToIntValue (decodeBits .binary64 bits) (-9223372036854775808)
        9223372036854775807))) ∧
    transmuteM (M := BM)
        (.Int (intFromBits (evalFloatToIntSaturating .binary64 bits (.signed .i64) .bits64).bits
          fcU64It)) (.Int fcU64It) (.Int fcI64It) =
      .ok (.Int (floatToIntValue (decodeBits .binary64 bits) (-9223372036854775808)
        9223372036854775807)) ∧
    transmuteM (M := TBM)
        (.Int (intFromBits (evalFloatToIntSaturating .binary64 bits (.signed .i64) .bits64).bits
          fcU64It)) (.Int fcU64It) (.Int fcI64It) =
      .ok (.Int (floatToIntValue (decodeBits .binary64 bits) (-9223372036854775808)
        9223372036854775807)) := by
  obtain ⟨mem, hrun⟩ := fc_run_f64_from_bits_as_i64_raw bits
  rw [fcLeRound_eq8 bits h] at hrun
  obtain ⟨_, hlt, hint, _, hdec⟩ :=
    fc_bridge_floatToInt .binary64 bits (.signed .i64) 8 rfl fc_goodSize_8
  refine ⟨⟨mem, runA_sound _ _ _ _ _ hrun⟩, runA_noUB _ _ _ _ _ hrun, hdec, ?_, ?_⟩
  · exact (fc_mrBM_transmute_int .Unsigned .Signed 8 _ fc_goodSize_8 hlt none).trans
      (congrArg (fun z : Int => (Except.ok (Gen.Value.Int z) : Interp Val)) hint)
  · exact (fc_mrTB_transmute_int .Unsigned .Signed 8 _ fc_goodSize_8 hlt none).trans
      (congrArg (fun z : Int => (Except.ok (Gen.Value.Int z) : Interp (Gen.Value TBM))) hint)

/-- **Symbolic narrowing bridge (`FloatToFloat`, `f64 → f32`)**: for every 64-bit pattern `x`,
Anneal's multi-step run of `(f64::from_bits(x) as f32).to_bits()` returns, free of UB, the `u32`
carrier `evalFloatToFloatRoundTiesToEven .binary64 .binary32 x`, whose MiniRust `Type.encode` is
exactly Anneal's bytes and which `transmuteM` moves to `i32` unchanged over both memory models. -/
theorem fc_sym_e2e_narrow_bits (bits : Nat) (h : bits < 2 ^ 64) :
    (∃ mem, ReachesRet (mirCallTree fcNarrowBitsBody [.scalar ⟨bits, 8⟩]) []
      (.normal (.scalar ⟨evalFloatToFloatRoundTiesToEven .binary64 .binary32 bits, 4⟩, mem))) ∧
    MirNoUBTree (mirCallTree fcNarrowBitsBody [.scalar ⟨bits, 8⟩]) ∧
    Type.encode (.Int fcU32It)
        (.Int (intFromBits (evalFloatToFloatRoundTiesToEven .binary64 .binary32 bits) fcU32It)) =
      .ok ((encodeLittleEndianBytes (evalFloatToFloatRoundTiesToEven .binary64 .binary32 bits) 4
        none).map fcByteToMR) ∧
    transmuteM (M := BM)
        (.Int (intFromBits (evalFloatToFloatRoundTiesToEven .binary64 .binary32 bits) fcU32It))
        (.Int fcU32It) (.Int fcI32It) =
      .ok (.Int (intFromBits (evalFloatToFloatRoundTiesToEven .binary64 .binary32 bits) fcI32It)) ∧
    transmuteM (M := TBM)
        (.Int (intFromBits (evalFloatToFloatRoundTiesToEven .binary64 .binary32 bits) fcU32It))
        (.Int fcU32It) (.Int fcI32It) =
      .ok (.Int (intFromBits (evalFloatToFloatRoundTiesToEven .binary64 .binary32 bits) fcI32It)) := by
  have hlt : evalFloatToFloatRoundTiesToEven .binary64 .binary32 bits < 2 ^ (8 * 4) :=
    Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt _ _ _
  obtain ⟨mem, hrun⟩ := fc_run_narrow_bits_raw bits
  rw [fcLeRound_eq8 bits h, fcLeRound_eq4 _ hlt] at hrun
  exact ⟨⟨mem, runA_sound _ _ _ _ _ hrun⟩, runA_noUB _ _ _ _ _ hrun,
    fc_mr_encode_eq_anneal .Unsigned 4 _ fc_goodSize_4 hlt,
    fc_mrBM_transmute_int .Unsigned .Signed 4 _ fc_goodSize_4 hlt none,
    fc_mrTB_transmute_int .Unsigned .Signed 4 _ fc_goodSize_4 hlt none⟩

/-- **Symbolic exact `int → float` bridge**: for every 32-bit pattern `x`, Anneal's multi-step
run of `(x as f64).to_bits()` (on `x : i32`) returns, free of UB, the `u64` carrier
`r = evalIntToFloatRoundTiesToEven true 32 x .binary64`, which decodes as a binary64 float to
*exactly* the integer `intValueOfBits true 32 x` (every `i32` is representable in `f64`); MiniRust's
`Type.encode` of `r` at `u64` is exactly Anneal's bytes, and `transmuteM` moves `r` from `u64` to
`i64` unchanged over both `BasicMemory` and `TreeBorrowsMemory`. -/
theorem fc_sym_e2e_int_as_f64_bits (bits : Nat) :
    (∃ mem, ReachesRet (mirCallTree fcIntAsF64BitsBody [.scalar ⟨bits, 4⟩]) []
      (.normal (.scalar ⟨evalIntToFloatRoundTiesToEven true 32 bits .binary64, 8⟩, mem))) ∧
    MirNoUBTree (mirCallTree fcIntAsF64BitsBody [.scalar ⟨bits, 4⟩]) ∧
    Anneal.Mir.IeeeFloatCast.floatKindDenotesInt
      (decodeBits .binary64 (evalIntToFloatRoundTiesToEven true 32 bits .binary64))
      (intValueOfBits true 32 bits) ∧
    Type.encode (.Int fcU64It)
        (.Int (intFromBits (evalIntToFloatRoundTiesToEven true 32 bits .binary64) fcU64It)) =
      .ok ((encodeLittleEndianBytes (evalIntToFloatRoundTiesToEven true 32 bits .binary64) 8
        none).map fcByteToMR) ∧
    transmuteM (M := BM)
        (.Int (intFromBits (evalIntToFloatRoundTiesToEven true 32 bits .binary64) fcU64It))
        (.Int fcU64It) (.Int fcI64It) =
      .ok (.Int (intFromBits (evalIntToFloatRoundTiesToEven true 32 bits .binary64) fcI64It)) ∧
    transmuteM (M := TBM)
        (.Int (intFromBits (evalIntToFloatRoundTiesToEven true 32 bits .binary64) fcU64It))
        (.Int fcU64It) (.Int fcI64It) =
      .ok (.Int (intFromBits (evalIntToFloatRoundTiesToEven true 32 bits .binary64) fcI64It)) := by
  have hlt : evalIntToFloatRoundTiesToEven true 32 bits .binary64 < 2 ^ (8 * 8) :=
    Anneal.Mir.IeeeFloatCast.evalIntToFloatRoundTiesToEven_lt _ _ _ _
  obtain ⟨hrun, hnoub⟩ := fc_sym_int_as_f64_bits bits
  exact ⟨hrun, hnoub, Anneal.Mir.IeeeFloatCast.evalIntToFloatRoundTiesToEven_sound.2.1 true bits,
    fc_mr_encode_eq_anneal .Unsigned 8 _ fc_goodSize_8 hlt,
    fc_mrBM_transmute_int .Unsigned .Signed 8 _ fc_goodSize_8 hlt none,
    fc_mrTB_transmute_int .Unsigned .Signed 8 _ fc_goodSize_8 hlt none⟩

/-! ### 14.2 `f16` / `f128` transmutes in the reverse direction

`fc_f16_f128_transmute_vs_float_cast` states the `f16 ↔ u16` / `f128 ↔ u128` dichotomy but proves
only the `f16 → u16` and `f128 → u128` directions; the reverse directions (`f16::from_bits`,
`f128::from_bits`) are below, so both directions preserve every bit pattern while the numeric casts
fail closed. -/

theorem fc_tyByteSize_f16 (decls : List LocalDecl) :
    tyByteSize decls fcLayouts (resolveTyWithLocalDecls decls fcLayouts fcF16Ty) = some 2 := rfl
theorem fc_tyByteSize_f128 (decls : List LocalDecl) :
    tyByteSize decls fcLayouts (resolveTyWithLocalDecls decls fcLayouts fcF128Ty) = some 16 := rfl
theorem fc_tyByteSize_u16 (decls : List LocalDecl) :
    tyByteSize decls fcLayouts (resolveTyWithLocalDecls decls fcLayouts fcU16Ty) = some 2 := rfl
theorem fc_tyByteSize_u128 (decls : List LocalDecl) :
    tyByteSize decls fcLayouts (resolveTyWithLocalDecls decls fcLayouts fcU128Ty) = some 16 := rfl

/-- `f16` / `f128` decode exactly like `u16` / `u128` (`normalizeCodecTy`). -/
theorem fc_decodeTyped_f16_f128_eq (bs : List MirSemantics.AbstractByte) :
    decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcF16Ty bs =
        decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcU16Ty bs ∧
      decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcF128Ty bs =
        decodeTypedValueFromBytes defaultCodecFuel fcLayouts fcU128Ty bs := ⟨rfl, rfl⟩

/-- **`f16::from_bits` / `f128::from_bits` in Anneal**: transmuting a `u16` (`u128`) holding
`bits` to `f16` (`f128`) yields exactly `bits`, for every 16-bit (128-bit) pattern, even though no
numeric `f16` / `f128` cast is modeled. -/
theorem fc_f16_f128_from_bits
    {locals locals' : List LocalSlot} {op : Operand} {mem : Memory} {decls : List LocalDecl} :
    (∀ {bits : Nat}, bits < 2 ^ 16 →
      evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
          mem.callStack = .ok (.scalar ⟨bits, 2⟩) locals' →
      operandTy decls fcLayouts op = some fcU16Ty →
      evalRvalue locals (.cast .transmute op fcF16Ty) mem decls fcLayouts =
        .ok (.scalar ⟨bits, 2⟩) locals' mem) ∧
    (∀ {bits : Nat}, bits < 2 ^ 128 →
      evalOperand locals op mem.borrows mem.globals fcLayouts mem.callerLocals decls
          mem.callStack = .ok (.scalar ⟨bits, 16⟩) locals' →
      operandTy decls fcLayouts op = some fcU128Ty →
      evalRvalue locals (.cast .transmute op fcF128Ty) mem decls fcLayouts =
        .ok (.scalar ⟨bits, 16⟩) locals' mem) := by
  refine ⟨fun {bits} h16 hop hty => ?_, fun {bits} h128 hop hty => ?_⟩
  · have hdec : decodeTypedValueFromBytes defaultCodecFuel fcLayouts
        (resolveTyWithLocalDecls decls fcLayouts fcF16Ty)
        (encodeLittleEndianBytes bits 2 none) = some (.scalar ⟨bits, 2⟩) := by
      change (match abstractBytesHaveProv (encodeLittleEndianBytes bits 2 none) with
        | true => none
        | false =>
          match Nat.beq (Trusted.Sequence.length (encodeLittleEndianBytes bits 2 none)) 2 with
          | false => none
          | true =>
            match decodeScalarBytes (encodeLittleEndianBytes bits 2 none) false with
            | some (sv, _) => some (Value.scalar sv)
            | none => none) = _
      rw [fc_abstractBytesHaveProv_encode_none, fc_seqLength_encodeLittleEndianBytes,
        fc_decodeScalarBytes_encode none false 1 bits (by simpa using h16)]
    exact fc_evalRvalue_transmute_via_le hop hty (fc_tyByteSize_u16 decls) (fc_tyByteSize_f16 decls)
      rfl hdec
  · have hdec : decodeTypedValueFromBytes defaultCodecFuel fcLayouts
        (resolveTyWithLocalDecls decls fcLayouts fcF128Ty)
        (encodeLittleEndianBytes bits 16 none) = some (.scalar ⟨bits, 16⟩) := by
      change (match abstractBytesHaveProv (encodeLittleEndianBytes bits 16 none) with
        | true => none
        | false =>
          match Nat.beq (Trusted.Sequence.length (encodeLittleEndianBytes bits 16 none)) 16 with
          | false => none
          | true =>
            match decodeScalarBytes (encodeLittleEndianBytes bits 16 none) false with
            | some (sv, _) => some (Value.scalar sv)
            | none => none) = _
      rw [fc_abstractBytesHaveProv_encode_none, fc_seqLength_encodeLittleEndianBytes,
        fc_decodeScalarBytes_encode none false 15 bits (by simpa using h128)]
    exact fc_evalRvalue_transmute_via_le hop hty (fc_tyByteSize_u128 decls)
      (fc_tyByteSize_f128 decls) rfl hdec

/-! ## Axiom guards

Every public theorem of this module depends at most on `propext`, `Classical.choice`, and
`Quot.sound` (no `sorryAx`, no `Lean.ofReduceBool`); the Anneal-side transmute, decoding, and
symbolic-run theorems avoid `Classical.choice`, which enters only through MiniRust-side
library lemmas (`decode_int_scalarBytes`, `canRepresent_intFromBits`, `decode_leBytes`,
`decodePtr_ptrBytes`, and the simulation theorem `mirCall_ret`). -/

section AxiomGuards

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_intTyBytes_float' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_intTyBytes_float

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_intTypeOf_float' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_intTypeOf_float

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_scalarTypeOf_float' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_scalarTypeOf_float

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_arrayTypeOf_float' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_arrayTypeOf_float

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_arrayTypeOf_floatArray' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_arrayTypeOf_floatArray

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_specOfRigidTy_float' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_specOfRigidTy_float

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_tupleTypeOf_float' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_tupleTypeOf_float

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_translateTy_float' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_translateTy_float

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_translateTy_floatArray' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_translateTy_floatArray

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_operandType_copy_float' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_operandType_copy_float

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_operandType_const_float' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_operandType_const_float

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_translateOperand_const_float' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_translateOperand_const_float

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_translateLocals_eq_none_of_float' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_translateLocals_eq_none_of_float

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_translateFn_eq_none_of_float' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_translateFn_eq_none_of_float

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_inFragment_eq_false_of_float' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_inFragment_eq_false_of_float

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_progInFragment_eq_false_of_float' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_progInFragment_eq_false_of_float

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_translateRvalue_floatToInt' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_translateRvalue_floatToInt

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_translateRvalue_intToFloat' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_translateRvalue_intToFloat

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_translateRvalue_floatToFloat' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_translateRvalue_floatToFloat

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_translateRvalue_float_cast' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_translateRvalue_float_cast

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_translateRvalue_float_cast_never_intToInt_or_transmute' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_translateRvalue_float_cast_never_intToInt_or_transmute

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_translateRvalue_transmute_to_float' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_translateRvalue_transmute_to_float

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_translateRvalue_transmute_from_local' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_translateRvalue_transmute_from_local

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_translateStatement_float_cast' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_translateStatement_float_cast

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_translateStatement_transmute_to_float' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_translateStatement_transmute_to_float

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_evalRvalue_floatToInt_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_evalRvalue_floatToInt_eq

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_evalRvalue_intToFloat_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_evalRvalue_intToFloat_eq

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_evalRvalue_floatToFloat_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_evalRvalue_floatToFloat_eq

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_evalRvalue_float_cast_ub' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_evalRvalue_float_cast_ub

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_evalRvalue_float_cast_unsupported_of_no_format' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_evalRvalue_float_cast_unsupported_of_no_format

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_ieeeFormatOfTy_f16' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_ieeeFormatOfTy_f16

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_ieeeFormatOfTy_f128' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_ieeeFormatOfTy_f128

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_ieeeFormatOfTy_f32' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_ieeeFormatOfTy_f32

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_ieeeFormatOfTy_f64' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_ieeeFormatOfTy_f64

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_uint8_ofNat_mod' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_uint8_ofNat_mod

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_uint8_ofNat_toNat' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_uint8_ofNat_toNat

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_map_encodeLittleEndianBytes' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_map_encodeLittleEndianBytes

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_seqLength_encodeLittleEndianBytes' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_seqLength_encodeLittleEndianBytes

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_length_encodeLittleEndianBytes' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_length_encodeLittleEndianBytes

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mergeByteProvenance_none_right' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mergeByteProvenance_none_right

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mergeByteProvenance_self' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mergeByteProvenance_self

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeLittleEndianBytes_encode' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeLittleEndianBytes_encode

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeScalarBytes_encode' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeScalarBytes_encode

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_abstractBytesHaveProv_encode_none' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_abstractBytesHaveProv_encode_none

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_abstractBytesHaveProv_encode_some' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_abstractBytesHaveProv_encode_some

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeLittleEndianBytes_eq_none_iff' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeLittleEndianBytes_eq_none_iff

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mapM_data_eq_none_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mapM_data_eq_none_iff

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decode_int_none_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decode_int_none_iff

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_evalByteCast_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_evalByteCast_eq

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_evalByteCast_of_encode' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_evalByteCast_of_encode

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_evalByteCast_size_mismatch' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_evalByteCast_size_mismatch

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_evalRvalue_transmute_ub' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_evalRvalue_transmute_ub

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_resolve_f32' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_resolve_f32

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_resolve_f64' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_resolve_f64

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_resolve_u32' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_resolve_u32

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_resolve_i32' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_resolve_i32

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_resolve_u64' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_resolve_u64

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_resolve_i64' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_resolve_i64

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_resolve_bytes4' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_resolve_bytes4

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_resolve_bytes8' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_resolve_bytes8

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_f32' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_f32

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_f64' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_f64

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_u32' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_u32

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_i32' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_i32

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_u64' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_u64

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_i64' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_i64

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_bytes4' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_bytes4

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_bytes8' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_bytes8

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_f32_emptyLayouts' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_f32_emptyLayouts

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_u32_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_u32_eq

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_i32_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_i32_eq

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_f32_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_f32_eq

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_u64_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_u64_eq

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_i64_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_i64_eq

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_f64_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_f64_eq

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_lt_256_pow_4' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_lt_256_pow_4

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_lt_256_pow_8' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_lt_256_pow_8

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_u32_encode' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_u32_encode

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_i32_encode' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_i32_encode

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_f32_encode' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_f32_encode

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_u64_encode' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_u64_encode

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_i64_encode' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_i64_encode

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_f64_encode' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_f64_encode

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_prov_none' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_prov_none

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_uninit_none' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_uninit_none

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_u8_byte' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_u8_byte

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeArrayChunks_u8' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeArrayChunks_u8

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_bytes4_encode' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_bytes4_encode

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_bytes8_encode' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_bytes8_encode

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_encodeList_u8' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_encodeList_u8

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_encodeByteCastSource_bytes4' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_encodeByteCastSource_bytes4

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_encodeByteCastSource_bytes8' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_encodeByteCastSource_bytes8

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_leByteVals_complete' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_leByteVals_complete

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_evalRvalue_transmute_via_le' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_evalRvalue_transmute_via_le

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_f32_to_u32' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_f32_to_u32

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_u32_to_f32' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_u32_to_f32

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_f32_to_i32' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_f32_to_i32

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_i32_to_f32' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_i32_to_f32

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_f32_to_bytes4' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_f32_to_bytes4

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_bytes4_to_f32' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_bytes4_to_f32

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_f64_to_u64' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_f64_to_u64

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_u64_to_f64' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_u64_to_f64

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_f64_to_i64' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_f64_to_i64

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_i64_to_f64' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_i64_to_f64

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_f64_to_bytes8' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_f64_to_bytes8

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_bytes8_to_f64' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_bytes8_to_f64

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_size_mismatch' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_size_mismatch

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_f32_roundtrip' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_f32_roundtrip

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_f64_roundtrip' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_f64_roundtrip

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_rawPtrU8' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_rawPtrU8

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_ptr_to_f64_ub' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_ptr_to_f64_ub

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_ptr_bytes_erased' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_ptr_bytes_erased

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_goodSize_4' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_goodSize_4

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_goodSize_8' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_goodSize_8

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_intValueOfBits_eq_intFromBits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_intValueOfBits_eq_intFromBits

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_intValueOfBits_carriers' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_intValueOfBits_carriers

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mr_encode_intFromBits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mr_encode_intFromBits

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mr_encode_eq_anneal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mr_encode_eq_anneal

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mr_decode_eq_anneal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mr_decode_eq_anneal

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_scalarBytes_sign' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_scalarBytes_sign

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mr_transmute_int' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mr_transmute_int

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mapM_dataM_init' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mapM_dataM_init

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mrM_transmute_int' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mrM_transmute_int

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mrBM_transmute_int' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mrBM_transmute_int

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mrTB_transmute_int' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mrTB_transmute_int

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mr_transmute_u32_i32' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mr_transmute_u32_i32

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mr_transmute_u64_i64' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mr_transmute_u64_i64

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mr_transmute_size_mismatch_ub' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mr_transmute_size_mismatch_ub

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mr_decode_ptrBytes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mr_decode_ptrBytes

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_float_bodies_rejected' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_float_bodies_rejected

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_carrier_translated' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_carrier_translated

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_anneal_float_cast_runs' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_anneal_float_cast_runs

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_anneal_float_cast_noUB' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_anneal_float_cast_noUB

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_anneal_f16_unsupported_uninit_ub' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_anneal_f16_unsupported_uninit_ub

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_carrier_runs' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_carrier_runs

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_bridge_floatToInt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_bridge_floatToInt

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_bridge_f32_as_i32' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_bridge_f32_as_i32

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_bridge_f64_as_u64' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_bridge_f64_as_u64

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_ieeeFormat_width' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_ieeeFormat_width

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_goodSize_byteWidth' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_goodSize_byteWidth

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_bridge_intToFloat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_bridge_intToFloat

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_bridge_floatToFloat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_bridge_floatToFloat

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_special_bit_patterns' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_special_bit_patterns

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_snan_transmute_vs_cast' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_snan_transmute_vs_cast

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_e2e_bit_carrier_runs' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_e2e_bit_carrier_runs

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_e2e_neg_inf_as_i32_both' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_e2e_neg_inf_as_i32_both

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fcLeRound_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fcLeRound_eq

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fcLeRound_eq4' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fcLeRound_eq4

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fcLeRound_eq8' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fcLeRound_eq8

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_run_bits_round_trip_raw' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_run_bits_round_trip_raw

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_run_from_bits_as_i32_raw' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_run_from_bits_as_i32_raw

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_run_int_as_f64_bits_raw' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_run_int_as_f64_bits_raw

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_run_widen_bits_raw' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_run_widen_bits_raw

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_sym_bits_round_trip' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_sym_bits_round_trip

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_sym_from_bits_as_i32' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_sym_from_bits_as_i32

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_sym_int_as_f64_bits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_sym_int_as_f64_bits

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_sym_widen_bits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_sym_widen_bits

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_sym_e2e_from_bits_as_i32' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_sym_e2e_from_bits_as_i32

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_sym_e2e_widen_bits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_sym_e2e_widen_bits

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_ptr_to_f64_ub_run' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_ptr_to_f64_ub_run

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_statementOk_float_cast' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_statementOk_float_cast

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mr_transmute_byte_arrays' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mr_transmute_byte_arrays

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_ptr_ref_box_float_boundary' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_ptr_ref_box_float_boundary

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_list_mapM_option_eq_none' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_list_mapM_option_eq_none

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_translateBlock_eq_none_of_stmt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_translateBlock_eq_none_of_stmt

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_translateBlocks_eq_none_of_block' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_translateBlocks_eq_none_of_block

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_translateFn_and_inFragment_of_float_cast_stmt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_translateFn_and_inFragment_of_float_cast_stmt

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_translateBlocksWithIntrinsics_eq_none' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_translateBlocksWithIntrinsics_eq_none

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_translateFnWithIntrinsics_float_rejected' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_translateFnWithIntrinsics_float_rejected

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_progInFragment_any_fn_rejected' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_progInFragment_any_fn_rejected

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_const_f32_cast_witness' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_const_f32_cast_witness

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_any_layouts' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_any_layouts

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_float_scalar_any_layouts' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_transmute_float_scalar_any_layouts

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_f16_f128_transmute_vs_float_cast' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_f16_f128_transmute_vs_float_cast

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_encodeTwosComplement_carrier_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_encodeTwosComplement_carrier_bridge

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_leByteValsMRM_eq_BM' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_leByteValsMRM_eq_BM

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_uint8_mod_toNat' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_uint8_mod_toNat

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_leBytesDecodeMRM_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_leBytesDecodeMRM_eq

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_u8_inBounds_mod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_u8_inBounds_mod

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_u8_emod_toNat_mod' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_u8_emod_toNat_mod

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_u8_encodeIntM_mod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_u8_encodeIntM_mod

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_u8_encodeInt_mod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_u8_encodeInt_mod

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_layout_u8' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_layout_u8

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mrM_array_u8_encode_decode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mrM_array_u8_encode_decode

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mr_array_u8_eq_anneal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mr_array_u8_eq_anneal

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mrM_transmute_int_bytes4' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mrM_transmute_int_bytes4

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mrM_transmute_int_bytes8' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mrM_transmute_int_bytes8

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mr_transmute_byte_arrays_symbolic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mr_transmute_byte_arrays_symbolic

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mrM_uninit_union_transmute_ub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mrM_uninit_union_transmute_ub

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mrM_evalCastOpM_size_mismatch_ub' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mrM_evalCastOpM_size_mismatch_ub

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_mrM_transmute_ptr_boundary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_mrM_transmute_ptr_boundary

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_anneal_ptr_transmute_and_cast_boundary' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_anneal_ptr_transmute_and_cast_boundary

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_carrierCast_inFragment' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_carrierCast_inFragment

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_carrierCast_ctxOk' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_carrierCast_ctxOk

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_carrierCast_argsOk' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_carrierCast_argsOk

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_wrapScalarBits_of_lt' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_wrapScalarBits_of_lt

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_run_carrierCast_raw' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_run_carrierCast_raw

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_sym_carrierCast_anneal' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_sym_carrierCast_anneal

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_sym_mr_carrier_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_sym_mr_carrier_steps

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_sym_e2e_from_bits_as_i32_machine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_sym_e2e_from_bits_as_i32_machine

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_carrierCast64_inFragment' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_carrierCast64_inFragment

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_carrierCast64_ctxOk' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_carrierCast64_ctxOk

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_carrierCast64_argsOk' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_carrierCast64_argsOk

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_run_carrierCast64_raw' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_run_carrierCast64_raw

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_sym_carrierCast64_anneal' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_sym_carrierCast64_anneal

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_sym_mr_carrier64_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_sym_mr_carrier64_steps

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_sym_e2e_widen_bits_machine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_sym_e2e_widen_bits_machine

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_run_f64_from_bits_as_i64_raw' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_run_f64_from_bits_as_i64_raw

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_run_narrow_bits_raw' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_run_narrow_bits_raw

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_sym_e2e_f64_from_bits_as_i64' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_sym_e2e_f64_from_bits_as_i64

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_sym_e2e_narrow_bits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_sym_e2e_narrow_bits

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_sym_e2e_int_as_f64_bits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_sym_e2e_int_as_f64_bits

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_f16' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_f16

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_f128' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_f128

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_u16' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_u16

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_u128' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_tyByteSize_u128

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_f16_f128_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_decodeTyped_f16_f128_eq

/--
info: 'MiniRustSpec.Correspondence.FloatCastMR.fc_f16_f128_from_bits' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.Correspondence.FloatCastMR.fc_f16_f128_from_bits

end AxiomGuards

end MiniRustSpec.Correspondence.FloatCastMR
