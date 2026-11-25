/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.Mir.IeeeFloatArith
import MiniRustSpec.FloatCastMR

/-!
# IEEE-754 Float Arithmetic, Comparisons, Negation, and `Ptr2IntTransmutePolicy` at `MiniRustSpec`

Episode 2 Shard B correspondence module pairing Anneal's trusted MIR semantics
(`Trusted.Rustc.V2026_06_01.MirSemantics` + `Anneal.Mir.IeeeFloatArith`) against pinned MiniRust
(`MiniRustSpec.Gen`, `MiniRustSpec.Interp`, `MiniRustSpec.Correspondence.Translate`) across both
`BasicMemory<x86_64>` (`Mach`) and `TreeBorrowsMemory<x86_64>` (`MachTB` with `MachTB.wfLive`):
- **§1**: Two-sided fail-closed translation boundary on float unary/binary ops (including
  no-float-local comparisons and arbitrary projected float places `*p`, `_s.0`, `_a[i]`, `_a[0]`)
  across `translate*`, `statementOk*`, `inFragment*`, and `progInFragment*`.
- **§2**: IEEE-754 bit-carrier bridges (`UnOp.neg ↔ BitXor` sign-bit flip, `Bool` comparisons, and
  `EvalFloatBinOpRel` / `nanChoices` carriers) across `BM`, `TBM`, `Mach`, and `MachTB` (`wfLive`).
- **§3**: Mode-parametric `Ptr2IntTransmutePolicy` (`.strictUcg630Ub` vs. `.stripProvenance`)
  correspondence on scalars, composites (`(*const u8, usize)` & `struct Mixed`), provenance-free
  equivalence, shared no-forgery (`usize → &u8`), and uninit-byte UB across `Mach` & `MachTB`.
- **§4**: Shared concrete witnesses `W1–W6` and complete `#guard_msgs` `#print axioms` audit
  covering 100% of public theorems (`[propext, Quot.sound]` / `[propext, Classical.choice, Quot.sound]`).
-/

namespace MiniRustSpec.FloatArithMR

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
open MiniRustSpec.Correspondence.FloatCastMR
open Anneal.Mir.IeeeFloatArith

/-! ## §0. Shared Types, Policy Layouts, Builders, and `Classical.choice`-Free Polymorphic Codecs -/
/-- A typed floating-point constant operand of bit pattern `bits` and byte width `sz`. -/
def faFloatConst (ty : Ty) (bits sz : Nat) : Operand :=
  .constant { ty := ty, val := .scalar (.int ⟨bits, sz⟩) }
/-- A `u64` constant operand (`layoutIdx := 0`) for fragment 64-bit carrier bodies. -/
def faConstU64 (n : Nat) : Operand :=
  .constant { ty := fcU64Ty0, val := .scalar (.int ⟨n, 8⟩) }
/-- `&u8` on `fcLayouts` (using layout entry `12`, 8-byte thin pointer). -/
def faRefU8Ty : Ty := { kind := .ref .not (.uint .u8), layoutIdx := 12 }
/-- Two-field 16-byte aggregate layout (offsets `0` and `8`, align `8`) with `fieldLayouts`. -/
def faPairLayout (fl0 fl1 : Nat) : TypeLayout :=
  { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := .memory,
    fields := .arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1],
    variants := .single 0, isUninhabited := false, fieldLayouts := [fl0, fl1] }
/-- Dedicated 64-bit little-endian `LayoutTable` covering scalar, pointer, reference, byte-array,
composite tuple/struct, and union types for the §3 `Ptr2IntTransmutePolicy` correspondence proofs.
Index `0` is `()` (unresolved sentinel); every resolved type below carries a non-zero index so it
is a fixed point of `resolveTyWithLocalDecls`. -/
def faPolicyLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [
      { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory,
        fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }, -- 0: ()
      fcPrimLayout 4 (.float 32),                                                    -- 1: f32
      fcPrimLayout 8 (.float 64),                                                    -- 2: f64
      fcPrimLayout 4 (.int 32 false),                                                -- 3: u32
      fcPrimLayout 4 (.int 32 true),                                                 -- 4: i32
      fcPrimLayout 8 (.int 64 false),                                                -- 5: u64
      fcPrimLayout 8 (.int 64 true),                                                 -- 6: i64
      fcPrimLayout 1 (.int 8 false),                                                 -- 7: u8
      { size := { bytes := 1 }, align := { bytes := 1 },
        backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 1 }),
        fields := .primitive, variants := .single 0, isUninhabited := false },       -- 8: bool
      fcPrimLayout 8 (.int 64 false),                                                -- 9: usize
      fcPrimLayout 8 (.pointer 0),                                                   -- 10: *const u8 / &u8
      fcByteArrayLayout 8,                                                           -- 11: [u8; 8]
      faPairLayout 10 10,                                                            -- 12: (*const u8, *const u8)
      faPairLayout 10 9,                                                             -- 13: (*const u8, usize) / Mixed
      faPairLayout 5 5,                                                              -- 14: (u64, u64)
      { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := .memory,
        fields := .union 1, variants := .single 0, isUninhabited := false,
        fieldLayouts := [5] }                                                        -- 15: MaybeUninit<u64>
    ] }
def faPolF32Ty : Ty := { kind := .float .f32, layoutIdx := 1 }
def faPolF64Ty : Ty := { kind := .float .f64, layoutIdx := 2 }
def faPolU32Ty : Ty := { kind := .uint .u32, layoutIdx := 3 }
def faPolI32Ty : Ty := { kind := .int .i32, layoutIdx := 4 }
def faPolU64Ty : Ty := { kind := .uint .u64, layoutIdx := 5 }
def faPolI64Ty : Ty := { kind := .int .i64, layoutIdx := 6 }
def faPolUsizeTy : Ty := { kind := .uint .usize, layoutIdx := 9 }
def faPolPtrTy : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 10 }
def faPolRefU8Ty : Ty := { kind := .ref .not (.uint .u8), layoutIdx := 10 }
def faPolBytes8Ty : Ty := { kind := .array (.uint .u8) 8, layoutIdx := 11 }
def faPolPtrPtrTupTy : Ty :=
  { kind := .tuple [.rawPtr .not (.uint .u8), .rawPtr .not (.uint .u8)], layoutIdx := 12 }
def faPolPtrUsizeTupTy : Ty :=
  { kind := .tuple [.rawPtr .not (.uint .u8), .uint .usize], layoutIdx := 13 }
def faPolMixedStructTy : Ty := { kind := .adt "Mixed" .nil, layoutIdx := 13 }
def faPolU64PairTupTy : Ty := { kind := .tuple [.uint .u64, .uint .u64], layoutIdx := 14 }
def faPolMaybeUninitU64Ty : Ty := { kind := .adt "MaybeUninitU64" .nil, layoutIdx := 15 }
/-- MiniRust `(*const u8, *const u8)` 16-byte tuple type. -/
def faMrPtrPtrTupleTy : Gen.Type :=
  .Tuple [(⟨0⟩, .Ptr (.Raw .None)), (⟨8⟩, .Ptr (.Raw .None))]
    { «end» := ⟨16⟩, align := ⟨8⟩, packed_align := none } none
/-- MiniRust `(*const u8, usize)` / `struct Mixed { p: *const u8, n: u64 }` 16-byte tuple type. -/
def faMrPtrU64TupleTy : Gen.Type :=
  .Tuple [(⟨0⟩, .Ptr (.Raw .None)), (⟨8⟩, .Int fcU64It)]
    { «end» := ⟨16⟩, align := ⟨8⟩, packed_align := none } none
/-- MiniRust `(u64, u64)` 16-byte tuple type. -/
def faMrU64U64TupleTy : Gen.Type :=
  .Tuple [(⟨0⟩, .Int fcU64It), (⟨8⟩, .Int fcU64It)]
    { «end» := ⟨16⟩, align := ⟨8⟩, packed_align := none } none
/-- MiniRust safe shared reference `&u8`. -/
def faMrRefU8Ty : Gen.Type := refTy .not fcU8It
/-- A zero-argument `Runtime(PostCleanup)` body over `fcLayouts`. -/
def faBody0 (dp : String) (decls : List LocalDecl) (stmts : List StatementKind) : CapturedMir where
  defPath := dp
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := decls
  basicBlocks :=
    [{ statements := stmts.map mkStmt, terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := { args := [], ret := { layout := fcPrimLayout 4 (.int 32 false), mode := .direct },
             conv := .rust, canUnwind := false }
  layouts := fcLayouts
  allocations := []
/-- A two-argument `Runtime(PostCleanup)` body over `fcLayouts`. -/
def faBody2 (dp : String) (decls : List LocalDecl) (stmts : List StatementKind) : CapturedMir where
  defPath := dp
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := decls
  basicBlocks :=
    [{ statements := stmts.map mkStmt, terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := { args := [{ layout := fcPrimLayout 4 (.int 32 false), mode := .direct },
                      { layout := fcPrimLayout 4 (.int 32 false), mode := .direct }],
             ret := { layout := fcPrimLayout 4 (.int 32 false), mode := .direct },
             conv := .rust, canUnwind := false }
  layouts := fcLayouts
  allocations := []
/-- UB message after `n` `Mach` steps under `fcCtx8` (8-byte return place). -/
def faUbAfter8 (body : CapturedMir) (args : List Value) (n : Nat) : Option String :=
  (fcStartMachine8 body args).bind fun m =>
    match Interp.steps n m with
    | .error (.ub msg) => some msg
    | _ => none
/-- UB message after `n` `MachTB` (`TreeBorrowsMemory`) steps under `fcCtx8`. -/
def faUbAfterTB8 (body : CapturedMir) (args : List Value) (n : Nat) : Option String :=
  (fcStartMachineTB8 body args).bind fun m =>
    match Interp.stepsTB n m with
    | .error (.ub msg) => some msg
    | _ => none
/-! ### §0.1 `Classical.choice`-free polymorphic pointer, tuple, and `wfLive` helpers -/
private theorem fa_encode_usize_cf (addr : Nat) (haddr : addr < 2 ^ 64) :
    Endianness.encode x86_64.ENDIANNESS .Unsigned x86_64.PTR_SIZE (addr : Int) =
      some (leBytes addr 8) := by
  have hlt : (addr : Int) < (2 : Int) ^ (64 : Nat) := by
    have := Int.ofNat_lt.mpr haddr
    simpa [Int.natCast_pow] using this
  have hge : (0 : Int) ≤ (addr : Int) := Int.natCast_nonneg addr
  have hib : inBounds (addr : Int) .Unsigned ⟨8⟩ = true := by
    unfold inBounds Size.bits
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hge, hlt⟩
  have hmod : ((addr : Int) % (2 : Int) ^ Size.bits ⟨8⟩).toNat = addr := by
    change ((addr : Int) % (2 : Int) ^ (64 : Nat)).toNat = addr
    rw [Int.emod_eq_of_lt hge hlt, Int.toNat_natCast]
  unfold Endianness.encode x86_64.ENDIANNESS x86_64.PTR_SIZE
  simp only [hib, ↓reduceIte, hmod]
private theorem fa_inBounds_u64 (addr : Nat) (haddr : addr < 2 ^ 64) :
    inBounds (addr : Int) .Unsigned ⟨8⟩ = true := by
  have hlt : (addr : Int) < (2 : Int) ^ (64 : Nat) := by
    have := Int.ofNat_lt.mpr haddr
    simpa [Int.natCast_pow] using this
  unfold inBounds Size.bits
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨Int.natCast_nonneg addr, hlt⟩
private theorem fa_encodePtrBytesM_len {M : Type} [Gen.Memory M]
    (prov : Option (Gen.Memory.Provenance M)) :
    ∀ (idx : Nat) (bs : List UInt8), (encodePtrBytesM (M := M) prov idx bs).length = bs.length
  | _, [] => rfl
  | idx, _ :: rest => congrArg Nat.succ (fa_encodePtrBytesM_len prov (idx + 1) rest)
private theorem fa_encodePtrBytesM_dataM_loop {M : Type} [Gen.Memory M]
    (prov : Option (Gen.Memory.Provenance M)) :
    ∀ (idx : Nat) (bs acc : List UInt8),
      List.mapM.loop AbstractByte.dataM (encodePtrBytesM (M := M) prov idx bs) acc =
        some (acc.reverse ++ bs)
  | _, [], acc => by simp [encodePtrBytesM, List.mapM.loop]
  | idx, b :: rest, acc => by
    dsimp only [encodePtrBytesM, List.mapM.loop, AbstractByte.dataM, bind, Option.bind]
    rw [fa_encodePtrBytesM_dataM_loop prov (idx + 1) rest (b :: acc)]
    simp [List.reverse_cons]
private theorem fa_encodePtrBytesM_dataM {M : Type} [Gen.Memory M]
    (prov : Option (Gen.Memory.Provenance M)) (idx : Nat) (bs : List UInt8) : (encodePtrBytesM (M := M) prov idx bs).mapM AbstractByte.dataM = some bs :=
  fa_encodePtrBytesM_dataM_loop prov idx bs []
private theorem fa_decodePtrProvenanceM_encode {M : Type} [Gen.Memory M] [MemoryOps M]
    (p : Gen.Memory.Provenance M) :
    ∀ (idx : Nat) (bs : List UInt8),
      decodePtrProvenanceM (M := M) idx (some p) (encodePtrBytesM (M := M) (some p) idx bs) = some p
  | _, [] => rfl
  | idx, _ :: rest => by
    dsimp only [encodePtrBytesM, decodePtrProvenanceM, AbstractByte.provenance_fragM, Option.map]
    simp only [and_self, ↓reduceIte]
    exact fa_decodePtrProvenanceM_encode p (idx + 1) rest
private theorem fa_decodePtrM_encodePtrBytesM {M : Type} [Gen.Memory M] [MemoryOps M]
    (prov : Option (Gen.Memory.Provenance M)) (addr : Nat) (haddr : addr < 2 ^ 64) :
    decodePtrM (M := M) (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) =
      .ok (some { addr := (addr : Int), provenance := prov }) := by
  have hbits' : addr < 2 ^ (8 * 8) := haddr
  have hdec := fc_decode_leBytes .Unsigned 8 addr hbits'
  simp only [intFromBits] at hdec
  dsimp only [decodePtrM]
  simp only [ne_eq, fa_encodePtrBytesM_len, leBytes_length, x86_64.PTR_SIZE, not_true_eq_false, ↓reduceIte, fa_encodePtrBytesM_dataM, x86_64.ENDIANNESS, hdec, pure, Except.pure]
  cases prov with
  | none => rfl
  | some p =>
    have hf : firstProvenanceM (M := M) (encodePtrBytesM (M := M) (some p) 0 (leBytes addr 8)) =
        some p := rfl
    rw [hf, fa_decodePtrProvenanceM_encode (M := M) p 0 (leBytes addr 8)]
private theorem fa_encodePtrM_of_encode {M : Type} [Gen.Memory M]
    (ptr : Gen.ThinPointer (Gen.Memory.Provenance M)) (data : List UInt8)
    (henc : Endianness.encode x86_64.ENDIANNESS .Unsigned x86_64.PTR_SIZE ptr.addr = some data) :
    encodePtrM (M := M) ptr = .ok (encodePtrBytesM (M := M) ptr.provenance 0 data) := by
  unfold encodePtrM
  rw [henc]
  rfl
private theorem fa_encodePtrM_u64 {M : Type} [Gen.Memory M]
    (addr : Nat) (haddr : addr < 2 ^ 64) (prov : Option (Gen.Memory.Provenance M)) :
    encodePtrM (M := M) ⟨(addr : Int), prov⟩ =
      .ok (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) :=
  fa_encodePtrM_of_encode (M := M) ⟨(addr : Int), prov⟩ (leBytes addr 8)
    (fa_encode_usize_cf addr haddr)
private theorem fa_encodeM_rawPtrNone {M : Type} [Gen.Memory M]
    (addr : Nat) (haddr : addr < 2 ^ 64) (prov : Option (Gen.Memory.Provenance M)) :
    Type.encodeM (M := M) (.Ptr (.Raw .None)) (.Ptr ⟨⟨(addr : Int), prov⟩, none⟩) =
      .ok (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) := by
  simp only [Type.encodeM, PtrType.as_wide_pair, PtrType.meta_kind, Option.map]
  exact fa_encodePtrM_u64 (M := M) addr haddr prov
private theorem fa_decodeM_rawPtrNone {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr : Nat) (haddr : addr < 2 ^ 64) (prov : Option (Gen.Memory.Provenance M)) :
    Type.decodeM (M := M) (.Ptr (.Raw .None))
      (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) =
      .ok (some (.Ptr ⟨⟨(addr : Int), prov⟩, none⟩)) := by
  simp only [Type.decodeM, PtrType.as_wide_pair, PtrType.meta_kind, Option.map, bind, Except.bind, pure, Except.pure, fa_decodePtrM_encodePtrBytesM (M := M) prov addr haddr]
  rfl
private theorem fa_checkValueM_rawPtrNone {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr : Nat) (haddr : addr < 2 ^ 64) (prov : Option (Gen.Memory.Provenance M)) (m : Option (Gen.Machine M)) :
    checkValueM (M := M) (.Ptr ⟨⟨(addr : Int), prov⟩, none⟩) (.Ptr (.Raw .None)) m = .ok () := by
  unfold checkValueM checkPtrM
  have hp : x86_64.PTR_SIZE = ⟨8⟩ := rfl
  rw [hp, fa_inBounds_u64 addr haddr]
  rfl
private theorem fa_decodeIntM_encodePtrBytesM {M : Type} [Gen.Memory M] [MemoryOps M]
    (s : Signedness) (addr : Nat) (haddr : addr < 2 ^ 64) (prov : Option (Gen.Memory.Provenance M)) :
    Type.decodeM (M := M) (.Int ⟨s, ⟨8⟩⟩) (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) =
      .ok (some (.Int (intFromBits addr ⟨s, ⟨8⟩⟩))) := by
  have hbits' : addr < 2 ^ (8 * 8) := haddr
  simp only [Type.decodeM, Type.decodeIntM, fa_encodePtrBytesM_len, leBytes_length, ne_eq, not_true_eq_false, ↓reduceIte, fa_encodePtrBytesM_dataM, x86_64.ENDIANNESS,
    fc_decode_leBytes s 8 addr hbits', pure, Except.pure]
private theorem fa_map_init_eq_encodePtrBytesM_none {M : Type} [Gen.Memory M] :
    ∀ (idx : Nat) (data : List UInt8),
      data.map (fun b => (Gen.AbstractByte.Init b none : Gen.AbstractByte (Gen.Memory.Provenance M))) =
        encodePtrBytesM (M := M) none idx data
  | _, [] => rfl
  | idx, b :: rest =>
    congrArg (Gen.AbstractByte.Init b none :: ·)
      (fa_map_init_eq_encodePtrBytesM_none (idx + 1) rest)
private theorem fa_encodeIntM_of_encode {M : Type} [Gen.Memory M]
    (it : Gen.IntType) (v : Int) (data : List UInt8) (henc : Endianness.encode x86_64.ENDIANNESS it.signed it.size v = some data) :
    Type.encodeM (M := M) (.Int it) (.Int v) =
      .ok (data.map (fun b => Gen.AbstractByte.Init b none)) := by
  simp only [Type.encodeM, Type.encodeIntM, henc, pure, Except.pure]
private theorem fa_encodeIntM_u64_cf {M : Type} [Gen.Memory M]
    (addr : Nat) (haddr : addr < 2 ^ 64) :
    Type.encodeM (M := M) (.Int fcU64It) (.Int (addr : Int)) =
      .ok (encodePtrBytesM (M := M) none 0 (leBytes addr 8)) := by
  rw [← fa_map_init_eq_encodePtrBytesM_none (M := M) 0 (leBytes addr 8)]
  exact fa_encodeIntM_of_encode (M := M) fcU64It (addr : Int) (leBytes addr 8)
    (fa_encode_usize_cf addr haddr)
private theorem fa_decodeArray8_encodePtrBytesM {M : Type} [Gen.Memory M] [MemoryOps M]
    (prov : Option (Gen.Memory.Provenance M)) (addr : Nat) :
    Type.decodeM (M := M) (.Array (.Int fcU8It) 8)
      (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) =
      .ok (some (.Tuple (fcLeByteValsMRM addr 8))) := by
  rw [← fc_leBytesDecodeMRM_eq (M := M) addr 8]
  cases prov <;> rfl
private theorem fa_transmuteM_of_steps {M : Type} [Gen.Memory M] [MemoryOps M]
    (v v' : Gen.Value M) (ty1 ty2 : Gen.Type) (sz : LibSpecr.Size) (a1 a2 : LibSpecr.Align)
    (bytes : List (Gen.AbstractByte (Gen.Memory.Provenance M))) (m : Option (Gen.Machine M))
    (hl1 : Type.layout ty1 = .ok (.Sized sz a1)) (hl2 : Type.layout ty2 = .ok (.Sized sz a2)) (henc : Type.encodeM (M := M) ty1 v = .ok bytes)
    (hdec : Type.decodeM (M := M) ty2 bytes = .ok (some v')) (hchk : checkValueM (M := M) v' ty2 m = .ok ()) :
    transmuteM (M := M) v ty1 ty2 m = .ok v' := by
  unfold transmuteM
  simp only [hl1, hl2, bind, Except.bind, expect_size_sized, ne_eq, not_true_eq_false, ↓reduceIte, henc, hdec, hchk, pure, Except.pure]
private theorem fa_transmuteM_of_check_err {M : Type} [Gen.Memory M] [MemoryOps M]
    (v v' : Gen.Value M) (ty1 ty2 : Gen.Type) (sz : LibSpecr.Size) (a1 a2 : LibSpecr.Align)
    (bytes : List (Gen.AbstractByte (Gen.Memory.Provenance M))) (m : Option (Gen.Machine M))
    (err : Stop) (hl1 : Type.layout ty1 = .ok (.Sized sz a1)) (hl2 : Type.layout ty2 = .ok (.Sized sz a2)) (henc : Type.encodeM (M := M) ty1 v = .ok bytes)
    (hdec : Type.decodeM (M := M) ty2 bytes = .ok (some v')) (hchk : checkValueM (M := M) v' ty2 m = .error err) :
    transmuteM (M := M) v ty1 ty2 m = .error err := by
  unfold transmuteM
  simp only [hl1, hl2, bind, Except.bind, expect_size_sized, ne_eq, not_true_eq_false, ↓reduceIte, henc, hdec, hchk]
private theorem fa_wfLive_of_stepsTB_isOk (m : Mach) (n : Nat)
    (h : (Interp.stepsTB n (liftMachToTB m)).isOk = true) :
    ∃ m0 m', some (liftMachToTB m) = some m0 ∧
      Interp.stepsTB n m0 = .ok m' ∧ MachTB.wfLive m' := by
  cases hs : Interp.stepsTB n (liftMachToTB m) with
  | error e => simp [hs, Except.isOk, Except.toBool] at h
  | ok m' => exact ⟨liftMachToTB m, m', rfl, hs, TbWitness.liftMachToTB_stepsTB_wfLive hs⟩

/-! ## §1. Two-Sided Fail-Closed Translation Boundary for Float Unary & Binary Ops -/
/-- Whether `op` is either a floating-point constant or a `copy`/`move` of an unprojected
floating-point local in `decls`. -/
def faIsFloatOperand (decls : List LocalDecl) (op : Operand) : Prop :=
  (∃ (ft : FloatTy) (idx : Nat) (val : ConstValue),
      op = .constant ⟨⟨.float ft, idx⟩, val⟩) ∨
  (∃ (j : Nat) (m : MirAst.Mutability) (ft : FloatTy) (idx : Nat) (dbg : Option String),
      decls[j]? = some { mutability := m, ty := ⟨.float ft, idx⟩, debugName := dbg } ∧
      (op = .copy ⟨j, []⟩ ∨ op = .move ⟨j, []⟩))
theorem fa_operandType_float_operand (layouts : LayoutTable) (decls : List LocalDecl)
    (op : Operand) (h : faIsFloatOperand decls op) :
    operandType layouts decls op = none ∧ operandType layouts decls (copyOp op) = none := by
  rcases h with ⟨ft, idx, val, rfl⟩ | ⟨j, m, ft, idx, dbg, hd, rfl | rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨fc_operandType_copy_float layouts decls j m ft idx dbg hd,
      fc_operandType_copy_float layouts decls j m ft idx dbg hd⟩
  · exact ⟨rfl, fc_operandType_copy_float layouts decls j m ft idx dbg hd⟩
theorem fa_operandIntType_float_operand (layouts : LayoutTable) (decls : List LocalDecl)
    (op : Operand) (h : faIsFloatOperand decls op) :
    operandIntType layouts decls op = none ∧ operandIntType layouts decls (copyOp op) = none := by
  rcases h with ⟨ft, idx, val, rfl⟩ | ⟨j, m, ft, idx, dbg, hd, rfl | rfl⟩
  · exact ⟨rfl, rfl⟩
  · have hcp : operandIntType layouts decls (.copy ⟨j, []⟩) = none := by
      simp only [operandIntType, placeIntType, hd, Option.bind_eq_bind, Option.bind_some]; rfl
    exact ⟨hcp, hcp⟩
  · have hcp : operandIntType layouts decls (.copy ⟨j, []⟩) = none := by
      simp only [operandIntType, placeIntType, hd, Option.bind_eq_bind, Option.bind_some]; rfl
    exact ⟨rfl, hcp⟩
/-- **`translateRvalue` fails closed on every float unary op** (both float constants and float
locals, `copy` or `move`, for every `UnOp`). -/
theorem fa_translateRvalue_unaryOp_float (layouts : LayoutTable) (decls : List LocalDecl)
    (targetTy : Option Ty) (uop : UnOp) (op : Operand) (h : faIsFloatOperand decls op) :
    translateRvalue layouts decls targetTy (.unaryOp uop op) = none ∧
    translateRvalue layouts decls targetTy (copyRv (.unaryOp uop op)) = none := by
  obtain ⟨ht1, ht2⟩ := fa_operandType_float_operand layouts decls op h
  constructor
  · simp only [translateRvalue, bind, Option.bind]
    cases translateOperand decls op with
    | none => rfl
    | some _ => simp [ht1]
  · simp only [copyRv, translateRvalue, bind, Option.bind]
    cases translateOperand decls (copyOp op) with
    | none => rfl
    | some _ => simp [ht2]
/-- **`translateRvalue` fails closed on every binary op with a float constant on EITHER side**
— covering ALL 5 arithmetic ops (`add`, `sub`, `mul`, `div`, `rem`) AND ALL 6 comparison ops
(`eq`, `ne`, `lt`, `le`, `gt`, `ge`), even when all locals in `decls` are `bool` or integers! -/
theorem fa_translateRvalue_binaryOp_float_const (layouts : LayoutTable) (decls : List LocalDecl)
    (targetTy : Option Ty) (op : MirAst.BinOp) (l r : Operand) (h : (∃ (ft : FloatTy) (idx : Nat) (val : ConstValue), l = .constant ⟨⟨.float ft, idx⟩, val⟩) ∨
         (∃ (ft : FloatTy) (idx : Nat) (val : ConstValue), r = .constant ⟨⟨.float ft, idx⟩, val⟩)) :
    translateRvalue layouts decls targetTy (.binaryOp op l r) = none ∧
    translateRvalue layouts decls targetTy (copyRv (.binaryOp op l r)) = none := by
  rcases h with ⟨ft, idx, val, rfl⟩ | ⟨ft, idx, val, rfl⟩
  · have hl := fc_translateOperand_const_float decls ft idx val
    constructor <;> simp [translateRvalue, copyRv, copyOp, hl]
  · have hr := fc_translateOperand_const_float decls ft idx val
    constructor
    · simp only [translateRvalue, bind, Option.bind]
      cases translateOperand decls l with
      | none => rfl
      | some _ => simp [hr]
    · simp only [copyRv, translateRvalue, bind, Option.bind]
      cases translateOperand decls (copyOp l) with
      | none => rfl
      | some _ => simp [copyOp, hr]
/-- **`translateRvalue` fails closed on every float arithmetic `BinOp`** (`add`, `sub`, `mul`,
`div`, `rem`) whose left operand is a float local (`copy` or `move`) or float constant. -/
theorem fa_translateRvalue_binaryOp_arith_float (layouts : LayoutTable) (decls : List LocalDecl)
    (targetTy : Option Ty) (op : MirAst.BinOp) (l r : Operand) (hop : isFloatArithBinOp op = true) (hl : faIsFloatOperand decls l) :
    translateRvalue layouts decls targetTy (.binaryOp op l r) = none ∧
    translateRvalue layouts decls targetTy (copyRv (.binaryOp op l r)) = none := by
  obtain ⟨ht1, ht2⟩ := fa_operandType_float_operand layouts decls l hl
  have hrel : translateRelOp op = none := by
    cases op <;> first | rfl | simp [isFloatArithBinOp] at hop
  have hbin : (translateBinOp op).isSome = true := by
    cases op <;> first | rfl | simp [isFloatArithBinOp] at hop
  obtain ⟨iop, hiop⟩ := Option.isSome_iff_exists.mp hbin
  constructor
  · simp only [translateRvalue, bind, Option.bind]
    cases translateOperand decls l with
    | none => rfl
    | some _ =>
      cases translateOperand decls r with
      | none => rfl
      | some _ => simp [hrel, hiop, ht1]
  · simp only [copyRv, translateRvalue, bind, Option.bind]
    cases translateOperand decls (copyOp l) with
    | none => rfl
    | some _ =>
      cases translateOperand decls (copyOp r) with
      | none => rfl
      | some _ => simp [hrel, hiop, ht2]
/-- Negative control: on two local copies `copy _i == copy _j`, `translateRvalue` alone is
type-erased (`some (.BinOp (.Rel .Eq) (.Load _) (.Load _))`), just like `transmute` in
`FloatCastMR`. Rejecting float-local comparisons therefore relies on BOTH `statementOk`
(`relOperandsOk`) AND local/function-level checks (`translateLocals` / `translateFn` /
`inFragment` / `progInFragment`). -/
theorem fa_translateRvalue_relOp_local_negative_control (layouts : LayoutTable)
    (decls : List LocalDecl) (targetTy : Option Ty) (i j : Nat) :
    translateRvalue layouts decls targetTy (.binaryOp .eq (.copy ⟨i, []⟩) (.copy ⟨j, []⟩)) =
      some (.BinOp (.Rel .Eq) (.Load (.Local (localName i))) (.Load (.Local (localName j)))) := rfl
/-- **`translateStatement` fails closed** on every assignment of a float unary op, every
assignment of a binary op with a float constant on either side (including comparisons `eq..ge`!),
and every assignment of an arithmetic binary op with a float local on the left. -/
theorem fa_translateStatement_float_unary_or_binary (layouts : LayoutTable)
    (decls : List LocalDecl) (dst : Place) (rv : Rvalue) (span : String) (hrv : translateRvalue layouts decls (placeMirTy decls dst) (copyRv rv) = none) :
    translateStatement decls ⟨.assign dst rv, span⟩ layouts = none := by
  simp only [translateStatement]
  cases translatePlace decls dst with
  | none => rfl
  | some _ => simp [hrv]
private theorem fa_operandOk_float_eq_false (layouts : LayoutTable) (decls : List LocalDecl)
    (it : Gen.IntType) (op : Operand) (h : faIsFloatOperand decls op) :
    operandOk layouts decls it op = false ∧ operandOk layouts decls it (copyOp op) = false := by
  rcases h with ⟨ft, idx, val, rfl⟩ | ⟨j, m, ft, idx, dbg, hd, rfl | rfl⟩
  · have ht := fc_translateOperand_const_float decls ft idx val
    exact ⟨by simp [operandOk, ht], by simp [copyOp, operandOk, ht]⟩
  · have hcp : operandOk layouts decls it (.copy ⟨j, []⟩) = false := by
      simp only [operandOk, placeOk, hd, Option.bind_eq_bind, Option.bind_some, fc_intTypeOf_float]
      simp
    exact ⟨hcp, hcp⟩
  · have hcp : operandOk layouts decls it (.copy ⟨j, []⟩) = false := by
      simp only [operandOk, placeOk, hd, Option.bind_eq_bind, Option.bind_some, fc_intTypeOf_float]
      simp
    exact ⟨rfl, hcp⟩
private theorem fa_operandOkB_float_eq_false (layouts : LayoutTable) (decls : List LocalDecl)
    (op : Operand) (h : faIsFloatOperand decls op) :
    operandOkB layouts decls op = false ∧ operandOkB layouts decls (copyOp op) = false := by
  obtain ⟨ht1, ht2⟩ := fa_operandType_float_operand layouts decls op h
  rcases h with ⟨ft, idx, val, rfl⟩ | ⟨j, m, ft, idx, dbg, hd, rfl | rfl⟩
  · exact ⟨by simp [operandOkB, operandIsBool, ht1], by simp [copyOp, operandOkB, operandIsBool, ht1]⟩
  · exact ⟨by simp [operandOkB, operandIsBool, ht1], by simp [copyOp, operandOkB, operandIsBool, ht1]⟩
  · simp only [copyOp] at ht2
    exact ⟨rfl, by simp [copyOp, operandOkB, operandIsBool, ht2]⟩
private theorem fa_relOperandsOk_float_eq_false (layouts : LayoutTable) (decls : List LocalDecl)
    (a b : Operand) (h : faIsFloatOperand decls a ∨ faIsFloatOperand decls b) :
    relOperandsOk layouts decls a b = false ∧
    relOperandsOk layouts decls (copyOp a) (copyOp b) = false := by
  rcases h with ha | hb
  · obtain ⟨ht1, ht2⟩ := fa_operandType_float_operand layouts decls a ha
    exact ⟨by simp [relOperandsOk, ht1], by simp [relOperandsOk, ht2]⟩
  · constructor
    · unfold relOperandsOk
      cases operandType layouts decls a with
      | none => rfl
      | some ty =>
        cases ty with
        | Int it => simp [(fa_operandOk_float_eq_false layouts decls it b hb).1]
        | Bool => simp [(fa_operandOkB_float_eq_false layouts decls b hb).1]
        | _ => rfl
    · unfold relOperandsOk
      cases operandType layouts decls (copyOp a) with
      | none => rfl
      | some ty =>
        cases ty with
        | Int it => simp [(fa_operandOk_float_eq_false layouts decls it b hb).2]
        | Bool => simp [(fa_operandOkB_float_eq_false layouts decls b hb).2]
        | _ => rfl
private theorem fa_rvalueOk_float_unary_eq_false (layouts : LayoutTable) (decls : List LocalDecl)
    (uop : UnOp) (op : Operand) (h : faIsFloatOperand decls op) : (∀ it, rvalueOk layouts decls it (.unaryOp uop op) = false ∧
           rvalueOk layouts decls it (copyRv (.unaryOp uop op)) = false) ∧
    rvalueOkB layouts decls (copyRv (.unaryOp uop op)) = false := by
  refine ⟨fun it => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := fa_operandOk_float_eq_false layouts decls it op h
    exact ⟨by simp [rvalueOk, h1], by simp [copyRv, rvalueOk, h2]⟩
  · cases uop with
    | not => simp [copyRv, rvalueOkB, (fa_operandOkB_float_eq_false layouts decls op h).2]
    | _ => rfl
private theorem fa_rvalueOk_float_binary_eq_false (layouts : LayoutTable) (decls : List LocalDecl)
    (bop : MirAst.BinOp) (l r : Operand) (h : faIsFloatOperand decls l ∨ faIsFloatOperand decls r) : (∀ it, rvalueOk layouts decls it (.binaryOp bop l r) = false ∧
           rvalueOk layouts decls it (copyRv (.binaryOp bop l r)) = false) ∧
    rvalueOkB layouts decls (copyRv (.binaryOp bop l r)) = false ∧
    rvalueOkO layouts decls (copyRv (.binaryOp bop l r)) = false ∧
    (∀ it, rvalueOkTuple layouts decls it (copyRv (.binaryOp bop l r)) = false) ∧
    (∀ m pit isR, ptrRvalueOk layouts decls m pit isR (copyRv (.binaryOp bop l r)) = false) := by
  have hrel := fa_relOperandsOk_float_eq_false layouts decls l r h
  refine ⟨fun it => ⟨?_, ?_⟩, ?_, ?_, fun it => ?_, fun m pit isR => ?_⟩
  · simp only [rvalueOk]
    cases translateBinOp bop with
    | none => rfl
    | some iop =>
      rcases h with hl | hr
      · simp [(fa_operandOk_float_eq_false layouts decls it l hl).1]
      · simp [(fa_operandOk_float_eq_false layouts decls it r hr).1,
              (fa_operandIntType_float_operand layouts decls r hr).1]
  · simp only [copyRv, rvalueOk]
    cases translateBinOp bop with
    | none => rfl
    | some iop =>
      rcases h with hl | hr
      · simp [(fa_operandOk_float_eq_false layouts decls it l hl).2]
      · simp [(fa_operandOk_float_eq_false layouts decls it r hr).2,
              (fa_operandIntType_float_operand layouts decls r hr).2]
  · simp only [copyRv, rvalueOkB]
    cases (translateRelOp bop).isSome with
    | true => simp [hrel.2]
    | false =>
      rcases h with hl | hr
      · simp [(fa_operandOkB_float_eq_false layouts decls l hl).2]
      · simp [(fa_operandOkB_float_eq_false layouts decls r hr).2]
  · cases bop with
    | cmp => simp [copyRv, rvalueOkO, hrel.2]
    | _ => rfl
  · simp only [copyRv, rvalueOkTuple]
    rcases h with hl | hr
    · simp [(fa_operandOk_float_eq_false layouts decls it l hl).2]
    · simp [(fa_operandOk_float_eq_false layouts decls it r hr).2]
  · cases bop with
    | offset =>
      simp only [copyRv]
      rcases h with hl | hr
      · rcases hl with ⟨ft, idx, val, rfl⟩ | ⟨j, mu, ft, idx, dbg, hd, rfl | rfl⟩
        · rfl
        · cases copyOp r with
          | constant c =>
            simp only [copyOp, ptrRvalueOk, hd, Option.bind_eq_bind, Option.bind_some]
            have hraw : rawPtrPointeeOf ⟨.float ft, idx⟩ = none := rfl
            simp [hraw]
          | _ => rfl
        · cases copyOp r with
          | constant c =>
            simp only [copyOp, ptrRvalueOk, hd, Option.bind_eq_bind, Option.bind_some]
            have hraw : rawPtrPointeeOf ⟨.float ft, idx⟩ = none := rfl
            simp [hraw]
          | _ => rfl
      · rcases hr with ⟨ft, idx, val, rfl⟩ | ⟨j, mu, ft, idx, dbg, hd, rfl | rfl⟩
        · cases copyOp l with
          | copy p =>
            rcases p with ⟨idxP, ps⟩
            cases ps with
            | nil =>
              simp only [copyOp, ptrRvalueOk]
              have hz : zeroOffsetConstOk ⟨⟨.float ft, idx⟩, val⟩ = false := by
                cases hz0 : zeroOffsetConstOk ⟨⟨.float ft, idx⟩, val⟩ with
                | false => rfl
                | true =>
                  obtain ⟨_, _, hit, _⟩ := zeroOffsetConstOk_iff.mp hz0
                  rw [fc_intTypeOf_float] at hit; cases hit
              simp [hz]
            | cons _ _ => rfl
          | _ => rfl
        · cases copyOp l with
          | copy p => rcases p with ⟨_, ps⟩; cases ps <;> rfl
          | _ => rfl
        · cases copyOp l with
          | copy p => rcases p with ⟨_, ps⟩; cases ps <;> rfl
          | _ => rfl
    | _ => rfl
private theorem fa_statementOk_of_rvalue_core (layouts : LayoutTable) (decls : List LocalDecl)
    (dst : Place) (rv : Rvalue) (span : String)
    (hcore :
      (∀ it, rvalueOk layouts decls it rv = false ∧ rvalueOk layouts decls it (copyRv rv) = false) ∧
      rvalueOkB layouts decls (copyRv rv) = false ∧ rvalueOkO layouts decls (copyRv rv) = false ∧
      (∀ it, rvalueOkTuple layouts decls it (copyRv rv) = false) ∧
      (∀ it, ptrDerefReadOk decls it (copyRv rv) = false) ∧
      (∀ e c, arrayRvalueOk layouts decls e c rv = false) ∧
      (∀ dty fs sz al, tupleRvalueOk layouts decls dty fs sz al rv = false) ∧
      (∀ m pit isR, ptrRvalueOk layouts decls m pit isR (copyRv rv) = false) ∧
      (∀ it, exposeCastOk decls it (copyRv rv) = false) ∧
      (∀ m pit isR, withExposedCastOk layouts decls m pit isR (copyRv rv) = false)) :
    statementOk decls ⟨.assign dst rv, span⟩ layouts = false ∧
    progStatementOk decls ⟨.assign dst rv, span⟩ layouts = false ∧
    provCastStmtOk decls ⟨.assign dst rv, span⟩ layouts = false ∧
    statementOkWithIntrinsics decls ⟨.assign dst rv, span⟩ layouts = false := by
  obtain ⟨hrvOk, hrvB, hrvO, hrvTup, hpd, harr, htup, hptr, hexp, hwe⟩ := hcore
  have hs : statementOk decls ⟨.assign dst rv, span⟩ layouts = false := by
    rcases dst with ⟨i, projs⟩
    cases projs with
    | nil =>
      unfold statementOk; dsimp only; split
      · rfl
      · next d _ =>
        split
        · exact hrvB
        · split
          · exact hrvO
          · split
            · next it _ => exact hrvTup it
            · split
              · next it _ => simp [(hrvOk it).2, hpd it]
              · split
                · next e c _ => exact harr e c
                · split
                  · next fs sz al _ => exact htup d.ty fs sz al
                  · split
                    · next m pit _ => exact hptr m pit (isRefTy d.ty)
                    · rfl
    | cons p rest =>
      cases p with
      | field idx fieldTy =>
        simp only [statementOk]
        cases placeIntType layouts decls ⟨i, .field idx fieldTy :: rest⟩ with
        | some it => simp [(hrvOk it).1]
        | none =>
          cases tuplePlaceSpec layouts decls ⟨i, .field idx fieldTy :: rest⟩ with
          | none => simp
          | some v =>
            rcases v with ⟨fs, sz, al⟩
            cases placeMirTy decls ⟨i, .field idx fieldTy :: rest⟩ with
            | none => simp | some dstTy => simp [htup dstTy fs sz al]
      | deref =>
        cases rest with
        | nil =>
          simp only [statementOk]
          cases (decls[i]? >>= (ptrPointeeOf ·.ty)) with
          | none => simp
          | some v => rcases v with ⟨m, pit⟩; cases m with | not => simp | «mut» => simp [(hrvOk pit).2, hpd pit]
        | cons _ _ => rfl
      | _ =>
        cases rest with
        | nil =>
          simp only [statementOk]
          cases (decls[i]? >>= (arrayTypeOf ·.ty)) with | none => rfl | some v => rcases v with ⟨e, _⟩; simp [(hrvOk e).1]
        | cons _ _ => rfl
  have hp : provCastStmtOk decls ⟨.assign dst rv, span⟩ layouts = false := by
    rcases dst with ⟨i, projs⟩
    cases projs with
    | nil =>
      unfold provCastStmtOk; dsimp only; split
      · rfl
      · next d _ =>
        split
        · next it _ => exact hexp it
        · split
          · next m pit _ => exact hwe m pit (isRefTy d.ty)
          · rfl
    | cons _ _ => rfl
  have hps : progStatementOk decls ⟨.assign dst rv, span⟩ layouts = false := by simpa [progStatementOk] using hs
  exact ⟨hs, hps, hp, by simp [statementOkWithIntrinsics, hps, hp]⟩
private theorem fa_translateFn_of_stmt_none (b : CapturedMir) (bb : BasicBlockData)
    (hbb : bb ∈ b.basicBlocks) (s : Statement) (hs : s ∈ bb.statements)
    (hst : translateStatement b.localDecls s b.layouts = none)
    (hso : translateStmtOrIntrinsic b.localDecls s b.layouts = none) :
    translateFn b = none ∧ translateFnWithIntrinsics b = none := by
  have hblk := fc_translateBlock_eq_none_of_stmt b.layouts b.localDecls bb ⟨s, hs, hst⟩
  have hblks := fc_translateBlocks_eq_none_of_block b.layouts b.localDecls 0 b.basicBlocks ⟨bb, hbb, hblk⟩
  have hfn : translateFn b = none := by
    unfold translateFn; cases translateCallConv b.fnAbi.conv with | none => rfl | some _ => cases translateLocals b.layouts 0 b.localDecls with | none => rfl | some _ => simp [hblks]
  have hblksWI := fc_translateBlocksWithIntrinsics_eq_none b.layouts b.localDecls 0 b.basicBlocks.length b.basicBlocks ⟨bb, hbb, s, hs, hso⟩
  have hfnWI : translateFnWithIntrinsics b = none := by
    unfold translateFnWithIntrinsics; cases translateCallConv b.fnAbi.conv with | none => rfl | some _ => cases translateLocals b.layouts 0 b.localDecls with | none => rfl | some _ => simp [hblksWI]
  exact ⟨hfn, hfnWI⟩
private theorem fa_progInFragment_of_stmt_false (entry : CapturedMir) (callees : List CapturedMir)
    (b : CapturedMir) (hb : b ∈ entry :: callees) (bb : BasicBlockData) (hbb : bb ∈ b.basicBlocks)
    (s : Statement) (hs : s ∈ bb.statements)
    (hsOk : statementOk b.localDecls s b.layouts = false)
    (hswi : statementOkWithIntrinsics b.localDecls s b.layouts = false) :
    inFragment b = false ∧ inFragmentWithIntrinsics b = false ∧
    progInFragment entry callees = false ∧ progInFragmentWithIntrinsics entry callees = false := by
  have hstAll1 : bb.statements.all (statementOk b.localDecls · b.layouts) = false := by
    cases hall : bb.statements.all (statementOk b.localDecls · b.layouts) with
    | false => rfl | true => have := List.all_eq_true.mp hall _ hs; rw [hsOk] at this; cases this
  have hbbAll1 : b.basicBlocks.all (fun bb => !bb.isCleanup && bb.statements.all (statementOk b.localDecls · b.layouts) &&
      terminatorOk b.layouts b.localDecls b.basicBlocks.length bb.terminator) = false := by
    cases hall : b.basicBlocks.all (fun bb => !bb.isCleanup && bb.statements.all (statementOk b.localDecls · b.layouts) &&
        terminatorOk b.layouts b.localDecls b.basicBlocks.length bb.terminator) with
    | false => rfl | true => have := List.all_eq_true.mp hall bb hbb; simp [hstAll1] at this
  have hstAll2 : bb.statements.all (statementOkWithIntrinsics b.localDecls · b.layouts) = false := by
    cases hall : bb.statements.all (statementOkWithIntrinsics b.localDecls · b.layouts) with
    | false => rfl | true => have := List.all_eq_true.mp hall _ hs; rw [hswi] at this; cases this
  have hbbAll2 : b.basicBlocks.all (fun bb => !bb.isCleanup && bb.statements.all (statementOkWithIntrinsics b.localDecls · b.layouts) &&
      terminatorOk b.layouts b.localDecls b.basicBlocks.length bb.terminator) = false := by
    cases hall : b.basicBlocks.all (fun bb => !bb.isCleanup && bb.statements.all (statementOkWithIntrinsics b.localDecls · b.layouts) &&
        terminatorOk b.layouts b.localDecls b.basicBlocks.length bb.terminator) with
    | false => rfl | true => have := List.all_eq_true.mp hall bb hbb; simp [hstAll2] at this
  obtain ⟨blk, hblkLt, hbbEq⟩ := List.mem_iff_getElem.mp hbb
  have hbbOpt : b.basicBlocks[blk]? = some bb := by simp [hblkLt, hbbEq]
  have hbodyWI : bodyInProgFragmentWithIntrinsics (fnNameMap entry callees) callees b = false := by
    cases hbf : bodyInProgFragmentWithIntrinsics (fnNameMap entry callees) callees b with
    | false => rfl
    | true =>
      simp only [bodyInProgFragmentWithIntrinsics, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hbf
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hrng⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hbf
      have hblkOk := hrng blk hblkLt; simp [hbbOpt, hstAll2] at hblkOk
  have hallB : (entry :: callees).all (bodyInProgFragmentWithIntrinsics (fnNameMap entry callees) callees) = false := by
    cases hbAll : (entry :: callees).all (bodyInProgFragmentWithIntrinsics (fnNameMap entry callees) callees) with
    | false => rfl | true => have := List.all_eq_true.mp hbAll b hb; rw [hbodyWI] at this; cases this
  have hprogWI : progInFragmentWithIntrinsics entry callees = false := by
    simp only [progInFragmentWithIntrinsics, hallB, Bool.and_false, Bool.false_and]
  have hprog : progInFragment entry callees = false := by
    cases hpf : progInFragment entry callees with
    | false => rfl | true => have := progInFragment_implies_progInFragmentWithIntrinsics hpf; rw [hprogWI] at this; cases this
  exact ⟨by simp only [inFragment, hbbAll1, Bool.and_false, Bool.false_and],
    by simp only [inFragmentWithIntrinsics, hbbAll2, Bool.and_false, Bool.false_and], hprog, hprogWI⟩
/-- **All four statement well-formedness predicates (`statementOk`, `progStatementOk`,
`provCastStmtOk`, `statementOkWithIntrinsics`) reject every float unary or binary assignment**
(whether operands are float locals or float constants, including comparisons `eq..ge` with zero
float locals!). -/
theorem fa_statementOk_all_preds_float_op_eq_false (layouts : LayoutTable)
    (decls : List LocalDecl) (dst : Place) (rv : Rvalue) (span : String)
    (hrv : (∃ uop op, rv = .unaryOp uop op ∧ faIsFloatOperand decls op) ∨
           (∃ bop l r, rv = .binaryOp bop l r ∧
             (faIsFloatOperand decls l ∨ faIsFloatOperand decls r))) :
    statementOk decls ⟨.assign dst rv, span⟩ layouts = false ∧
    progStatementOk decls ⟨.assign dst rv, span⟩ layouts = false ∧
    provCastStmtOk decls ⟨.assign dst rv, span⟩ layouts = false ∧
    statementOkWithIntrinsics decls ⟨.assign dst rv, span⟩ layouts = false := by
  refine fa_statementOk_of_rvalue_core layouts decls dst rv span ?_
  rcases hrv with ⟨uop, op, rfl, hop⟩ | ⟨bop, l, r, rfl, hlr⟩
  · obtain ⟨h1, h2⟩ := fa_rvalueOk_float_unary_eq_false layouts decls uop op hop
    exact ⟨h1, h2, rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl,
      fun _ _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := fa_rvalueOk_float_binary_eq_false layouts decls bop l r hlr
    exact ⟨h1, h2, h3, h4, fun _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, h5,
      fun _ => rfl, fun _ _ _ => rfl⟩
/-- **Complete whole-function & multi-function fail-closed rejection (all 6 MiniRust checks)**:
if a MIR body `b` contains EITHER (a) a float local `d ∈ b.localDecls` OR (b) an assignment
statement of a float-constant unary or binary op (on either operand side, including ALL 6
comparison ops `eq..ge` — **even when `b` declares ZERO float locals**!), then `translateFn b`,
`translateFnWithIntrinsics b`, `inFragment b`, `inFragmentWithIntrinsics b`, and (for any program
`entry :: callees` containing `b`) `progInFragment entry callees` and
`progInFragmentWithIntrinsics entry callees` ALL fail closed (`none` / `false`).
Scope: (a)/(b) cover float-typed locals and float constant operands; arbitrary projected float
places (`*p`, `_s.0`, `_a[i]`, `_a[0]`, etc., resolved via `placeTy`) are proved rejected universally
by `fa_projected_float_place_rejection` and `fa_no_fragment_admits_projected_float_op` below. -/
theorem fa_no_fragment_admits_float_arith_or_cmp (entry : CapturedMir)
    (callees : List CapturedMir) (b : CapturedMir) (hb : b ∈ entry :: callees)
    (h : (∃ d ∈ b.localDecls, ∃ (ft : FloatTy) (idx : Nat), d.ty = ⟨.float ft, idx⟩) ∨
         (∃ bb ∈ b.basicBlocks, ∃ s ∈ bb.statements, ∃ (dst : Place) (rv : Rvalue) (span : String),
           s = ⟨.assign dst rv, span⟩ ∧
           ((∃ uop ft idx val, rv = .unaryOp uop (.constant ⟨⟨.float ft, idx⟩, val⟩)) ∨
            (∃ bop l r, rv = .binaryOp bop l r ∧
              ((∃ ft idx val, l = .constant ⟨⟨.float ft, idx⟩, val⟩) ∨
               (∃ ft idx val, r = .constant ⟨⟨.float ft, idx⟩, val⟩)))))) :
    translateFn b = none ∧ translateFnWithIntrinsics b = none ∧
    inFragment b = false ∧ inFragmentWithIntrinsics b = false ∧
    progInFragment entry callees = false ∧ progInFragmentWithIntrinsics entry callees = false := by
  rcases h with hloc | ⟨bb, hbb, s, hs, dst, rv, span, rfl, hrv⟩
  · have hnf := fc_no_fragment_admits_float_local b callees hloc
    exact ⟨hnf.1, hnf.2.1, hnf.2.2.1, hnf.2.2.2.1,
      fc_progInFragment_any_fn_rejected entry callees b hb (.inl hloc),
      fc_progInFragmentWithIntrinsics_float_rejected entry callees b hb hloc⟩
  · have htrv : translateRvalue b.layouts b.localDecls (placeMirTy b.localDecls dst) (copyRv rv) = none := by
      rcases hrv with ⟨uop, ft, idx, val, rfl⟩ | ⟨bop, l, r, rfl, hlr⟩
      · exact (fa_translateRvalue_unaryOp_float b.layouts b.localDecls _ uop _ (.inl ⟨ft, idx, val, rfl⟩)).2
      · exact (fa_translateRvalue_binaryOp_float_const b.layouts b.localDecls _ bop l r hlr).2
    have hst := fa_translateStatement_float_unary_or_binary b.layouts b.localDecls dst rv span htrv
    have hso : translateStmtOrIntrinsic b.localDecls ⟨.assign dst rv, span⟩ b.layouts = none := by
      rcases hrv with ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;> simp [translateStmtOrIntrinsic, hst]
    obtain ⟨hfn, hfnWI⟩ := fa_translateFn_of_stmt_none b bb hbb _ hs hst hso
    have hrvF : (∃ uop op, rv = .unaryOp uop op ∧ faIsFloatOperand b.localDecls op) ∨
        (∃ bop l r, rv = .binaryOp bop l r ∧ (faIsFloatOperand b.localDecls l ∨ faIsFloatOperand b.localDecls r)) := by
      rcases hrv with ⟨uop, ft, idx, val, rfl⟩ | ⟨bop, l, r, rfl, hlr⟩
      · exact .inl ⟨uop, _, rfl, .inl ⟨ft, idx, val, rfl⟩⟩
      · rcases hlr with ⟨ft, idx, val, rfl⟩ | ⟨ft, idx, val, rfl⟩
        · exact .inr ⟨bop, _, r, rfl, .inl (.inl ⟨ft, idx, val, rfl⟩)⟩
        · exact .inr ⟨bop, l, _, rfl, .inr (.inl ⟨ft, idx, val, rfl⟩)⟩
    obtain ⟨hsOk, _, _, hswi⟩ := fa_statementOk_all_preds_float_op_eq_false b.layouts b.localDecls dst rv span hrvF
    obtain ⟨hinF, hinFWI, hprog, hprogWI⟩ := fa_progInFragment_of_stmt_false entry callees b hb bb hbb _ hs hsOk hswi
    exact ⟨hfn, hfnWI, hinF, hinFWI, hprog, hprogWI⟩

/-! ### §1.0b General Projected-Place Float Rejection (F5 Closure) -/
private theorem fa_resolveFieldPath_none_of_float (layouts : LayoutTable) :
    ∀ (rest : List ProjectionElem) (spec : TupleSpec) (curTy : Ty) (idx : Nat)
      (fTy ty : Ty) (ft : FloatTy),
      resolveProjectedTy layouts curTy (.field idx fTy :: rest) = some ty → ty.kind = .float ft →
      resolveFieldPath layouts spec (.field idx fTy :: rest) = none
  | [], spec, _, idx, fTy, ty, ft, hres, hft => by
    simp only [resolveProjectedTy, Option.some.injEq] at hres; subst hres
    cases spec with
    | scalar _ => rfl
    | tuple fields _ _ =>
      simp only [resolveFieldPath, bind, Option.bind]
      cases fields[idx]? with | none => rfl | some p => simp [hft, specOfRigidTy]
  | e :: rest, spec, _, idx, fTy, ty, ft, hres, hft => by
    cases spec with
    | scalar _ => rfl
    | tuple fields _ _ =>
      simp only [resolveFieldPath, bind, Option.bind]
      cases fields[idx]? with
      | none => rfl
      | some p =>
        cases specOfRigidTy layouts fTy.kind fTy.layoutIdx with
        | none => rfl
        | some exp =>
          dsimp only; split
          · cases e with
            | field idx' fTy' => simp [fa_resolveFieldPath_none_of_float layouts rest p.2 fTy idx' fTy' ty ft hres hft]
            | _ => cases p.2 <;> rfl
          · rfl
private theorem fa_arrayTypeOf_none_of_elemTy_float {t eTy : Ty} {ft : FloatTy}
    (he : elemTyOf t = some eTy) (hft : eTy.kind = .float ft) : arrayTypeOf t = none := by
  rcases t with ⟨k, l⟩; cases k with
  | array elemKind _ => simp only [elemTyOf, Option.some.injEq] at he; subst he; simp only at hft; subst hft; rfl
  | slice _ => rfl | _ => cases he
private theorem fa_derefPointeeTy_none_of_pointeeTy_float {t pTy : Ty} {ft : FloatTy}
    (hp : pointeeTyOf t = some pTy) (hft : pTy.kind = .float ft) : derefPointeeTy t = none := by
  rcases t with ⟨k, l⟩; cases k with
  | ref _ inner | rawPtr _ inner => simp only [pointeeTyOf, Option.some.injEq] at hp; subst hp; simp only at hft; subst hft; rfl
  | adt dp args =>
    cases args with
    | nil => cases hp
    | cons inner rest =>
      cases rest with
      | nil =>
        unfold pointeeTyOf at hp; dsimp only at hp
        cases hbox : Bool.or (stringEq dp "std::boxed::Box") (stringEq dp "alloc::boxed::Box") with
        | false => rw [hbox] at hp; cases hp
        | true => rw [hbox] at hp; simp only [Option.some.injEq] at hp; subst hp; simp only at hft; subst hft; unfold derefPointeeTy; dsimp only; split <;> rfl
      | cons _ _ => cases hp
  | _ => cases hp
private theorem fa_placeIntType_float_place (layouts : LayoutTable) (decls : List LocalDecl)
    (pl : Place) (ty : Ty) (ft : FloatTy) (hpl : placeTy decls layouts pl = some ty) (hft : ty.kind = .float ft) :
    placeIntType layouts decls pl = none := by
  rcases pl with ⟨j, projs⟩; unfold placeTy at hpl; dsimp only [Trusted.Sequence.get?] at hpl
  cases hd : decls[j]? with
  | none => rw [hd] at hpl; cases hpl
  | some d =>
    rw [hd] at hpl
    cases projs with
    | nil => simp only [resolveProjectedTy, Option.some.injEq] at hpl; subst hpl; simp [placeIntType, hd, intTypeOf, hft, intTyBytes]
    | cons e rest =>
      cases e with
      | field idx fTy =>
        simp only [placeIntType, hd, bind, Option.bind]
        cases intBoolTupleOf d.ty with
        | some it =>
          cases idx with
          | zero => cases rest with | nil => simp only [resolveProjectedTy, Option.some.injEq] at hpl; subst hpl; simp [intTypeOf, hft, intTyBytes] | cons _ _ => rfl
          | succ _ => rfl
        | none =>
          cases tupleTypeOf layouts d.ty with
          | none => rfl | some v => rcases v with ⟨fs, sz, al⟩; simp [fa_resolveFieldPath_none_of_float layouts rest (.tuple fs sz al) d.ty idx fTy ty ft hpl hft]
      | index _ | constantIndex _ _ _ =>
        cases rest with
        | nil =>
          simp only [resolveProjectedTy] at hpl
          cases he : elemTyOf d.ty with
          | none => rw [he] at hpl; cases hpl
          | some eTy => rw [he] at hpl; simp only [Option.some.injEq] at hpl; subst hpl; simp [placeIntType, hd, fa_arrayTypeOf_none_of_elemTy_float he hft]
        | cons _ _ => rfl
      | _ => rfl
private theorem fa_placeOk_float_place (layouts : LayoutTable) (decls : List LocalDecl) (it : Gen.IntType)
    (pl : Place) (ty : Ty) (ft : FloatTy) (hpl : placeTy decls layouts pl = some ty) (hft : ty.kind = .float ft) :
    placeOk layouts decls it pl = false := by
  rcases pl with ⟨j, projs⟩; unfold placeTy at hpl; dsimp only [Trusted.Sequence.get?] at hpl
  cases hd : decls[j]? with
  | none => rw [hd] at hpl; cases hpl
  | some d =>
    rw [hd] at hpl
    cases projs with
    | nil => simp only [resolveProjectedTy, Option.some.injEq] at hpl; subst hpl; simp [placeOk, hd, intTypeOf, hft, intTyBytes]
    | cons e rest =>
      cases e with
      | field idx fTy =>
        simp only [placeOk, hd]
        cases intBoolTupleOf d.ty with
        | some tupIt =>
          cases idx with
          | zero => cases rest with | nil => simp only [resolveProjectedTy, Option.some.injEq] at hpl; subst hpl; simp [intTypeOf, hft, intTyBytes] | cons _ _ => simp
          | succ _ => simp
        | none =>
          cases tupleTypeOf layouts d.ty with
          | none => simp | some v => rcases v with ⟨fs, sz, al⟩; simp [fa_resolveFieldPath_none_of_float layouts rest (.tuple fs sz al) d.ty idx fTy ty ft hpl hft]
      | index _ | constantIndex _ _ _ =>
        cases rest with
        | nil =>
          simp only [resolveProjectedTy] at hpl
          cases he : elemTyOf d.ty with
          | none => rw [he] at hpl; cases hpl
          | some eTy => rw [he] at hpl; simp only [Option.some.injEq] at hpl; subst hpl; simp [placeOk, hd, fa_arrayTypeOf_none_of_elemTy_float he hft]
        | cons _ _ => rfl
      | deref | subslice _ _ _ | downcast _ _ | opaqueCast _ | unwrapUnsafeBinder _ =>
        cases rest with
        | nil => simp only [placeOk, hd, Option.bind_eq_bind, Option.bind_some]; cases arrayTypeOf d.ty with | none => simp | some _ => simp [projOk]
        | cons _ _ => rfl
private theorem fa_operandType_float_place_copy (layouts : LayoutTable) (decls : List LocalDecl)
    (pl : Place) (ty : Ty) (ft : FloatTy) (hpl : placeTy decls layouts pl = some ty) (hft : ty.kind = .float ft) :
    operandType layouts decls (.copy pl) = none := by
  have hpi := fa_placeIntType_float_place layouts decls pl ty ft hpl hft
  rcases pl with ⟨j, projs⟩
  cases projs with
  | nil =>
    unfold placeTy at hpl; dsimp only [Trusted.Sequence.get?] at hpl
    cases hd : decls[j]? with
    | none => rw [hd] at hpl; cases hpl
    | some d => rw [hd] at hpl; simp only [resolveProjectedTy, Option.some.injEq] at hpl; subst hpl; simp [operandType, hd, scalarTypeOf, isBoolTy, isOrderingTy, intBoolTupleOf, intTypeOf, hft, intTyBytes]
  | cons e rest =>
    cases e with
    | field idx fTy =>
      cases idx with
      | zero => simp [operandType, hpi]
      | succ k =>
        cases k with
        | zero =>
          cases rest with
          | nil =>
            unfold placeTy at hpl; dsimp only [Trusted.Sequence.get?] at hpl
            cases hd : decls[j]? with
            | none => rw [hd] at hpl; cases hpl
            | some d => rw [hd] at hpl; simp only [resolveProjectedTy, Option.some.injEq] at hpl; subst hpl; simp only [operandType, hd, Option.bind_eq_bind, Option.bind_some]; cases intBoolTupleOf d.ty with | some _ => simp [isBoolTy, hft] | none => simp [hpi]
          | cons _ _ => simp [operandType, hpi]
        | succ _ => simp [operandType, hpi]
    | _ => simp [operandType, hpi]
private theorem fa_operandOkB_float_place_copy (layouts : LayoutTable) (decls : List LocalDecl)
    (pl : Place) (ty : Ty) (ft : FloatTy) (hpl : placeTy decls layouts pl = some ty) (hft : ty.kind = .float ft) :
    operandOkB layouts decls (.copy pl) = false := by
  have hot := fa_operandType_float_place_copy layouts decls pl ty ft hpl hft
  rcases pl with ⟨j, projs⟩
  cases projs with
  | nil => simp [operandOkB, operandIsBool, hot]
  | cons e rest =>
    cases e with
    | field idx fTy =>
      cases idx with
      | zero => rfl
      | succ k =>
        cases k with
        | zero =>
          cases rest with
          | nil =>
            unfold placeTy at hpl; dsimp only [Trusted.Sequence.get?] at hpl
            cases hd : decls[j]? with
            | none => rw [hd] at hpl; cases hpl
            | some d => rw [hd] at hpl; simp only [resolveProjectedTy, Option.some.injEq] at hpl; subst hpl; simp only [operandOkB, hd, Option.bind_eq_bind, Option.bind_some]; cases intBoolTupleOf d.ty with | some _ => simp [isBoolTy, hft] | none => simp
          | cons _ _ => rfl
        | succ _ => rfl
    | _ => rfl
/-- **General projected-place float rejection (F5 closure)**: for ANY (possibly projected) place `pl`
(`*p`, `_s.0`, `_s.0.1`, `_a[i]`, `_a[0]`, downcast, subslice, or unprojected local) whose `Trusted`
`placeTy decls layouts pl` resolves to `.float ft` and `op ∈ {.copy pl, .move pl}`:
1. `placeIntType`, `operandType`, `operandIntType` return `none` and `placeOk` returns `false`;
2. `translatePlace` / `translateOperand` return `none` on deref (`*p`) and constant-index (`_a[k]`)
   float places (even when `translateLocals` admits `*const f32`!);
3. `translateRvalue` & `translateStatement` fail closed (`none`) on every unary op and every
   float-arithmetic binary op (and on ALL binary ops including comparisons for `*p` / `_a[k]`);
4. ALL four statement predicates (`statementOk`, `progStatementOk`, `provCastStmtOk`,
   `statementOkWithIntrinsics`) return `false` for EVERY unary OR binary op (including `eq..ge`,
   `cmp`, `offset`) with `op` on EITHER operand side! -/
theorem fa_projected_float_place_rejection (layouts : LayoutTable) (decls : List LocalDecl)
    (pl : Place) (ty : Ty) (ft : FloatTy) (op : Operand)
    (hpl : placeTy decls layouts pl = some ty) (hft : ty.kind = .float ft) (hop : op = .copy pl ∨ op = .move pl) :
    placeIntType layouts decls pl = none ∧ (∀ it, placeOk layouts decls it pl = false) ∧
    (operandType layouts decls op = none ∧ operandType layouts decls (copyOp op) = none) ∧
    (operandIntType layouts decls op = none ∧ operandIntType layouts decls (copyOp op) = none) ∧
    (∀ j, pl = ⟨j, [.deref]⟩ → translatePlace decls pl = none ∧ translateOperand decls op = none ∧ translateOperand decls (copyOp op) = none) ∧
    (∀ j o m fe, pl = ⟨j, [.constantIndex o m fe]⟩ → translatePlace decls pl = none ∧ translateOperand decls op = none ∧ translateOperand decls (copyOp op) = none) ∧
    (∀ targetTy uop, translateRvalue layouts decls targetTy (.unaryOp uop op) = none ∧ translateRvalue layouts decls targetTy (copyRv (.unaryOp uop op)) = none) ∧
    (∀ targetTy bop r, isFloatArithBinOp bop = true → translateRvalue layouts decls targetTy (.binaryOp bop op r) = none ∧ translateRvalue layouts decls targetTy (copyRv (.binaryOp bop op r)) = none) ∧
    (∀ dst uop span, translateStatement decls ⟨.assign dst (.unaryOp uop op), span⟩ layouts = none) ∧
    (∀ dst bop r span, isFloatArithBinOp bop = true → translateStatement decls ⟨.assign dst (.binaryOp bop op r), span⟩ layouts = none) ∧
    (∀ dst rv span, ((∃ uop, rv = .unaryOp uop op) ∨ (∃ bop l r, rv = .binaryOp bop l r ∧ (l = op ∨ r = op))) →
      statementOk decls ⟨.assign dst rv, span⟩ layouts = false ∧
      progStatementOk decls ⟨.assign dst rv, span⟩ layouts = false ∧
      provCastStmtOk decls ⟨.assign dst rv, span⟩ layouts = false ∧
      statementOkWithIntrinsics decls ⟨.assign dst rv, span⟩ layouts = false) := by
  have hpi := fa_placeIntType_float_place layouts decls pl ty ft hpl hft
  have hpok : ∀ it, placeOk layouts decls it pl = false := fun it => fa_placeOk_float_place layouts decls it pl ty ft hpl hft
  have hotC := fa_operandType_float_place_copy layouts decls pl ty ft hpl hft
  have hokBC := fa_operandOkB_float_place_copy layouts decls pl ty ft hpl hft
  have hot : operandType layouts decls op = none ∧ operandType layouts decls (copyOp op) = none := by cases hop with | inl h => subst h; exact ⟨hotC, hotC⟩ | inr h => subst h; exact ⟨rfl, hotC⟩
  have hoi : operandIntType layouts decls op = none ∧ operandIntType layouts decls (copyOp op) = none := by cases hop with | inl h => subst h; exact ⟨hpi, hpi⟩ | inr h => subst h; exact ⟨rfl, hpi⟩
  have hook : ∀ it, operandOk layouts decls it op = false ∧ operandOk layouts decls it (copyOp op) = false := fun it => by rcases hop with rfl | rfl <;> simp [operandOk, copyOp, hpok it]
  have hookB : operandOkB layouts decls op = false ∧ operandOkB layouts decls (copyOp op) = false := by cases hop with | inl h => subst h; exact ⟨hokBC, hokBC⟩ | inr h => subst h; exact ⟨rfl, hokBC⟩
  have hderef : ∀ j, pl = ⟨j, [.deref]⟩ → translatePlace decls pl = none ∧ translateOperand decls op = none ∧ translateOperand decls (copyOp op) = none := by
    intro j hEq; subst hEq; unfold placeTy at hpl; dsimp only [Trusted.Sequence.get?] at hpl
    cases hd : decls[j]? with
    | none => rw [hd] at hpl; cases hpl
    | some d =>
      rw [hd] at hpl; simp only [resolveProjectedTy] at hpl
      cases hp : pointeeTyOf d.ty with
      | none => rw [hp] at hpl; cases hpl
      | some pTy =>
        rw [hp] at hpl; simp only [Option.some.injEq] at hpl; subst hpl
        have htp : translatePlace decls ⟨j, [.deref]⟩ = none := by simp [translatePlace, hd, fa_derefPointeeTy_none_of_pointeeTy_float hp hft]
        exact ⟨htp, by rcases hop with rfl | rfl <;> simp [translateOperand, htp], by rcases hop with rfl | rfl <;> simp [copyOp, translateOperand, htp]⟩
  have hcidx : ∀ j o m fe, pl = ⟨j, [.constantIndex o m fe]⟩ → translatePlace decls pl = none ∧ translateOperand decls op = none ∧ translateOperand decls (copyOp op) = none := by
    intro j o m fe hEq; subst hEq; unfold placeTy at hpl; dsimp only [Trusted.Sequence.get?] at hpl
    cases hd : decls[j]? with
    | none => rw [hd] at hpl; cases hpl
    | some d =>
      rw [hd] at hpl; simp only [resolveProjectedTy] at hpl
      cases he : elemTyOf d.ty with
      | none => rw [he] at hpl; cases hpl
      | some eTy =>
        rw [he] at hpl; simp only [Option.some.injEq] at hpl; subst hpl
        have htp : translatePlace decls ⟨j, [.constantIndex o m fe]⟩ = none := by simp [translatePlace, hd, fa_arrayTypeOf_none_of_elemTy_float he hft]
        exact ⟨htp, by rcases hop with rfl | rfl <;> simp [translateOperand, htp], by rcases hop with rfl | rfl <;> simp [copyOp, translateOperand, htp]⟩
  have htrUn : ∀ targetTy uop, translateRvalue layouts decls targetTy (.unaryOp uop op) = none ∧ translateRvalue layouts decls targetTy (copyRv (.unaryOp uop op)) = none := fun targetTy uop => by
    constructor
    · simp only [translateRvalue, bind, Option.bind]; cases translateOperand decls op with | none => rfl | some _ => simp [hot.1]
    · simp only [copyRv, translateRvalue, bind, Option.bind]; cases translateOperand decls (copyOp op) with | none => rfl | some _ => simp [hot.2]
  have htrArith : ∀ targetTy bop r, isFloatArithBinOp bop = true → translateRvalue layouts decls targetTy (.binaryOp bop op r) = none ∧ translateRvalue layouts decls targetTy (copyRv (.binaryOp bop op r)) = none := fun targetTy bop r hbop => by
    have hrel : translateRelOp bop = none := by cases bop <;> first | rfl | simp [isFloatArithBinOp] at hbop
    have hbin : (translateBinOp bop).isSome = true := by cases bop <;> first | rfl | simp [isFloatArithBinOp] at hbop
    obtain ⟨iop, hiop⟩ := Option.isSome_iff_exists.mp hbin
    constructor
    · simp only [translateRvalue, bind, Option.bind]; cases translateOperand decls op with | none => rfl | some _ => cases translateOperand decls r with | none => rfl | some _ => simp [hrel, hiop, hot.1]
    · simp only [copyRv, translateRvalue, bind, Option.bind]; cases translateOperand decls (copyOp op) with | none => rfl | some _ => cases translateOperand decls (copyOp r) with | none => rfl | some _ => simp [hrel, hiop, hot.2]
  refine ⟨hpi, hpok, hot, hoi, hderef, hcidx, htrUn, htrArith,
    fun dst uop span => fa_translateStatement_float_unary_or_binary layouts decls dst _ span (htrUn _ uop).2,
    fun dst bop r span hb => fa_translateStatement_float_unary_or_binary layouts decls dst _ span (htrArith _ bop r hb).2,
    fun dst rv span hrv => fa_statementOk_of_rvalue_core layouts decls dst rv span ?_⟩
  rcases hrv with ⟨uop, rfl⟩ | ⟨bop, l, r, rfl, hlr⟩
  · exact ⟨fun it => ⟨by simp [rvalueOk, (hook it).1], by simp [copyRv, rvalueOk, (hook it).2]⟩,
      by cases uop with | not => simp [copyRv, rvalueOkB, hookB.2] | _ => rfl,
      rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  · have hrelB : relOperandsOk layouts decls (copyOp l) (copyOp r) = false := by
      rcases hlr with rfl | rfl
      · simp [relOperandsOk, hot.2]
      · unfold relOperandsOk; cases operandType layouts decls (copyOp l) with
        | none => rfl | some t => cases t with | Int it => simp [(hook it).2] | Bool => simp [hookB.2] | _ => rfl
    refine ⟨fun it => ⟨?_, ?_⟩, ?_, by cases bop with | cmp => simp [copyRv, rvalueOkO, hrelB] | _ => rfl,
      fun it => by simp only [copyRv, rvalueOkTuple]; rcases hlr with rfl | rfl <;> simp [(hook it).2],
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, fun m pit isR => ?_, fun _ => rfl, fun _ _ _ => rfl⟩
    · simp only [rvalueOk]; cases translateBinOp bop with | none => rfl | some _ => rcases hlr with rfl | rfl <;> simp [(hook it).1, hoi.1]
    · simp only [copyRv, rvalueOk]; cases translateBinOp bop with | none => rfl | some _ => rcases hlr with rfl | rfl <;> simp [(hook it).2, hoi.2]
    · simp only [copyRv, rvalueOkB]; cases (translateRelOp bop).isSome with | true => simp [hrelB] | false => rcases hlr with rfl | rfl <;> simp [hookB.2]
    · cases bop with
      | offset =>
        simp only [copyRv]
        rcases hlr with rfl | rfl
        · have hcop : copyOp l = .copy pl := by rcases hop with rfl | rfl <;> rfl
          rw [hcop]; rcases pl with ⟨j, projs⟩
          cases projs with
          | nil =>
            unfold placeTy at hpl; dsimp only [Trusted.Sequence.get?] at hpl
            cases hd : decls[j]? with
            | none => rw [hd] at hpl; cases hpl
            | some d => rw [hd] at hpl; simp only [resolveProjectedTy, Option.some.injEq] at hpl; subst hpl; cases copyOp r with | constant _ => simp [ptrRvalueOk, hd, rawPtrPointeeOf, hft] | _ => rfl
          | cons _ _ => cases copyOp r <;> rfl
        · have hcop : copyOp r = .copy pl := by rcases hop with rfl | rfl <;> rfl
          rw [hcop]; cases copyOp l with | copy p => rcases p with ⟨_, ps⟩; cases ps <;> rfl | _ => rfl
      | _ => rfl
/-- **Whole-function & multi-function rejection of ANY projected float operand (F5 closure)**:
if a MIR body `b ∈ entry :: callees` contains ANY assignment of a unary or binary op (including
comparisons `eq..ge`) reading ANY projected place `pl` (`*p`, `_s.0`, `_a[i]`, `_a[0]`, etc.) whose
`placeTy b.localDecls b.layouts pl` is `.float ft`, then ALL four fragment gates (`inFragment`,
`inFragmentWithIntrinsics`, `progInFragment`, `progInFragmentWithIntrinsics`) return `false`; and
whenever `rv` is unary, float-arithmetic on the left, or `pl` is a deref `*p` / constant-index `_a[k]`
(covering `*p < *q` with zero float locals!), `translateStatement`, `translateFn`, and
`translateFnWithIntrinsics` ALSO return `none`! -/
theorem fa_no_fragment_admits_projected_float_op (entry : CapturedMir) (callees : List CapturedMir)
    (b : CapturedMir) (hb : b ∈ entry :: callees) (bb : BasicBlockData) (hbb : bb ∈ b.basicBlocks)
    (dst : Place) (rv : Rvalue) (span : String) (hs : ⟨.assign dst rv, span⟩ ∈ bb.statements)
    (pl : Place) (ty : Ty) (ft : FloatTy) (op : Operand)
    (hpl : placeTy b.localDecls b.layouts pl = some ty) (hft : ty.kind = .float ft) (hop : op = .copy pl ∨ op = .move pl)
    (hrv : (∃ uop, rv = .unaryOp uop op) ∨ (∃ bop l r, rv = .binaryOp bop l r ∧ (l = op ∨ r = op))) :
    inFragment b = false ∧ inFragmentWithIntrinsics b = false ∧
    progInFragment entry callees = false ∧ progInFragmentWithIntrinsics entry callees = false ∧
    (((∃ uop, rv = .unaryOp uop op) ∨ (∃ bop r, isFloatArithBinOp bop = true ∧ rv = .binaryOp bop op r) ∨
      (∃ j, pl = ⟨j, [.deref]⟩) ∨ (∃ j o m fe, pl = ⟨j, [.constantIndex o m fe]⟩)) →
      translateStatement b.localDecls ⟨.assign dst rv, span⟩ b.layouts = none ∧
      translateFn b = none ∧ translateFnWithIntrinsics b = none) := by
  have hrej := fa_projected_float_place_rejection b.layouts b.localDecls pl ty ft op hpl hft hop
  obtain ⟨hsOk, _, _, hswi⟩ := hrej.2.2.2.2.2.2.2.2.2.2 dst rv span hrv
  obtain ⟨hinF, hinFWI, hprog, hprogWI⟩ := fa_progInFragment_of_stmt_false entry callees b hb bb hbb _ hs hsOk hswi
  refine ⟨hinF, hinFWI, hprog, hprogWI, fun htr => ?_⟩
  have hstOfOpNone : translateOperand b.localDecls (copyOp op) = none →
      translateStatement b.localDecls ⟨.assign dst rv, span⟩ b.layouts = none := fun hopN => by
    refine fa_translateStatement_float_unary_or_binary b.layouts b.localDecls dst rv span ?_
    rcases hrv with ⟨uop, rfl⟩ | ⟨bop, l, r, rfl, hlr⟩
    · simp [copyRv, translateRvalue, hopN]
    · rcases hlr with rfl | rfl
      · simp [copyRv, translateRvalue, hopN]
      · simp only [copyRv, translateRvalue, bind, Option.bind]; cases translateOperand b.localDecls (copyOp l) with | none => rfl | some _ => simp [hopN]
  have hst : translateStatement b.localDecls ⟨.assign dst rv, span⟩ b.layouts = none := by
    rcases htr with ⟨uop, rfl⟩ | ⟨bop, r, hbop, rfl⟩ | ⟨j, hEq⟩ | ⟨j, o, m, fe, hEq⟩
    · exact hrej.2.2.2.2.2.2.2.2.1 dst uop span
    · exact hrej.2.2.2.2.2.2.2.2.2.1 dst bop r span hbop
    · exact hstOfOpNone (hrej.2.2.2.2.1 j hEq).2.2
    · exact hstOfOpNone (hrej.2.2.2.2.2.1 j o m fe hEq).2.2
  have hso : translateStmtOrIntrinsic b.localDecls ⟨.assign dst rv, span⟩ b.layouts = none := by
    rcases hrv with ⟨_, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;> simp [translateStmtOrIntrinsic, hst]
  obtain ⟨hfn, hfnWI⟩ := fa_translateFn_of_stmt_none b bb hbb _ hs hst hso
  exact ⟨hst, hfn, hfnWI⟩
/-! ### §1.1 No-float-local comparison witnesses & Anneal's side of the §1 boundary -/
/-- **Zero float locals**: `_0 : bool = const 1.0_f32 == const -0.0_f32`.
`translateLocals` succeeds (`[boolDecl]` has no float locals!), yet MiniRust's operand/rvalue/
statement/function checks MUST still reject it. -/
def faConstCmpOneNegZeroBody : CapturedMir :=
  faBody0 "float_arith::const_cmp_1_neg0" [boolDecl]
    [.assign (local_ 0)
      (.binaryOp .eq (faFloatConst fcF32Ty 0x3F800000 4) (faFloatConst fcF32Ty 0x80000000 4))]
/-- **Zero float locals**: `_0 : bool = const -0.0_f32 == const +0.0_f32`.
Under integer equality `0x80000000 == 0x00000000` is `false`, whereas IEEE-754 returns `true`! -/
def faConstCmpSignedZerosBody : CapturedMir :=
  faBody0 "float_arith::const_cmp_neg0_pos0" [boolDecl]
    [.assign (local_ 0)
      (.binaryOp .eq (faFloatConst fcF32Ty 0x80000000 4) (faFloatConst fcF32Ty 0x00000000 4))]
/-- **Zero float locals**: `_0 : bool = const qNaN_f32 == const qNaN_f32`.
Under integer equality `0x7FC00000 == 0x7FC00000` is `true`, whereas IEEE-754 returns `false`! -/
def faConstCmpQNaNBody : CapturedMir :=
  faBody0 "float_arith::const_cmp_qnan_qnan" [boolDecl]
    [.assign (local_ 0)
      (.binaryOp .eq (faFloatConst fcF32Ty 0x7FC00000 4) (faFloatConst fcF32Ty 0x7FC00000 4))]
/-- `fn f32_neg(x: f32) -> f32 { -x }`. -/
def faF32NegBody : CapturedMir :=
  fcBody "float_arith::f32_neg" [fcDecl fcF32Ty, fcDecl fcF32Ty]
    [.assign (local_ 0) (.unaryOp .neg (.copy (local_ 1)))]
/-- `fn f32_bin(x: f32, y: f32) -> f32 { x <op> y }`. -/
def faF32BinBody (dp : String) (op : MirAst.BinOp) : CapturedMir :=
  faBody2 dp [fcDecl fcF32Ty, fcDecl fcF32Ty, fcDecl fcF32Ty]
    [.assign (local_ 0) (.binaryOp op (.copy (local_ 1)) (.copy (local_ 2)))]
/-- `fn f64_bin(x: f64, y: f64) -> f64 { x <op> y }`. -/
def faF64BinBody (dp : String) (op : MirAst.BinOp) : CapturedMir :=
  faBody2 dp [fcDecl fcF64Ty, fcDecl fcF64Ty, fcDecl fcF64Ty]
    [.assign (local_ 0) (.binaryOp op (.copy (local_ 1)) (.copy (local_ 2)))]
/-- `fn f32_cmp(x: f32, y: f32) -> bool { x <op> y }`. -/
def faF32CmpBody (dp : String) (op : MirAst.BinOp) : CapturedMir :=
  faBody2 dp [boolDecl, fcDecl fcF32Ty, fcDecl fcF32Ty]
    [.assign (local_ 0) (.binaryOp op (.copy (local_ 1)) (.copy (local_ 2)))]
/-- `f16` addition (fails closed `.unsupported` in Anneal). -/
def faF16AddBody : CapturedMir :=
  faBody2 "float_arith::f16_add" [fcDecl fcF16Ty, fcDecl fcF16Ty, fcDecl fcF16Ty]
    [.assign (local_ 0) (.binaryOp .add (.copy (local_ 1)) (.copy (local_ 2)))]
/-- `f128` negation (fails closed `.unsupported` in Anneal). -/
def faF128NegBody : CapturedMir :=
  fcBody "float_arith::f128_neg" [fcDecl fcF128Ty, fcDecl fcF128Ty]
    [.assign (local_ 0) (.unaryOp .neg (.copy (local_ 1)))]
/-- Uninitialized `f32` local read by `.unaryOp .neg` (`.ub` in Anneal). -/
def faUninitFloatNegBody : CapturedMir :=
  fcBody "float_arith::uninit_f32_neg" [fcDecl fcF32Ty, fcDecl fcU32Ty, fcDecl fcF32Ty]
    [.storageLive 2, .assign (local_ 0) (.unaryOp .neg (.copy (local_ 2)))]
/-- Uninitialized `f32` local read by `.binaryOp .add` (`.ub` in Anneal). -/
def faUninitFloatAddBody : CapturedMir :=
  fcBody "float_arith::uninit_f32_add" [fcDecl fcF32Ty, fcDecl fcF32Ty, fcDecl fcF32Ty]
    [.storageLive 2, .assign (local_ 0) (.binaryOp .add (.copy (local_ 1)) (.copy (local_ 2)))]
private theorem fa_no_float_local_cmp_helper (b : CapturedMir) (aBits bBits : Nat)
    (hbb : b.basicBlocks =
      [{ statements := [mkStmt (.assign (local_ 0)
           (.binaryOp .eq (faFloatConst fcF32Ty aBits 4) (faFloatConst fcF32Ty bBits 4)))],
         terminator := mkTerm .return_, isCleanup := false }]) :
    translateFn b = none ∧ translateFnWithIntrinsics b = none ∧
    inFragment b = false ∧ inFragmentWithIntrinsics b = false ∧
    progInFragment b [] = false ∧ progInFragmentWithIntrinsics b [] = false :=
  fa_no_fragment_admits_float_arith_or_cmp b [] b (List.mem_cons_self ..)
    (.inr ⟨_, by rw [hbb]; exact List.mem_cons_self .., _, List.mem_cons_self ..,
      local_ 0, _, _, rfl,
      .inr ⟨.eq, _, _, rfl, .inl ⟨.f32, 1, .scalar (.int ⟨aBits, 4⟩), rfl⟩⟩⟩)
/-- **Crucial no-float-local comparison two-sided boundary**:
1. `faConstCmpOneNegZeroBody` (`1.0 == -0.0`), `faConstCmpSignedZerosBody` (`-0.0 == +0.0`), and
   `faConstCmpQNaNBody` (`qNaN == qNaN`) declare **zero float locals** (`translateLocals` succeeds!);
2. Yet ALL SIX MiniRust checks (`translateFn`, `translateFnWithIntrinsics`, `inFragment`,
   `inFragmentWithIntrinsics`, `progInFragment`, `progInFragmentWithIntrinsics`) reject all three,
   preventing MiniRust from miscompiling `-0.0 == +0.0` or `qNaN == qNaN` as integer equality;
3. Meanwhile Anneal's `mirCallTree` / `MirNoUBTree` / `EvalRvalueFloatRel` (in BOTH modes and at
   ANY policy) execute them cleanly to `false`, `true`, and `false` respectively. -/
theorem fa_no_float_local_cmp_two_sided_boundary :
    (translateLocals faConstCmpOneNegZeroBody.layouts 0 faConstCmpOneNegZeroBody.localDecls).isSome = true ∧
    (translateLocals faConstCmpSignedZerosBody.layouts 0 faConstCmpSignedZerosBody.localDecls).isSome = true ∧
    (translateLocals faConstCmpQNaNBody.layouts 0 faConstCmpQNaNBody.localDecls).isSome = true ∧
    (translateFn faConstCmpOneNegZeroBody = none ∧
     translateFnWithIntrinsics faConstCmpOneNegZeroBody = none ∧
     inFragment faConstCmpOneNegZeroBody = false ∧
     inFragmentWithIntrinsics faConstCmpOneNegZeroBody = false ∧
     progInFragment faConstCmpOneNegZeroBody [] = false ∧
     progInFragmentWithIntrinsics faConstCmpOneNegZeroBody [] = false) ∧
    (translateFn faConstCmpSignedZerosBody = none ∧
     translateFnWithIntrinsics faConstCmpSignedZerosBody = none ∧
     inFragment faConstCmpSignedZerosBody = false ∧
     inFragmentWithIntrinsics faConstCmpSignedZerosBody = false ∧
     progInFragment faConstCmpSignedZerosBody [] = false ∧
     progInFragmentWithIntrinsics faConstCmpSignedZerosBody [] = false) ∧
    (translateFn faConstCmpQNaNBody = none ∧
     translateFnWithIntrinsics faConstCmpQNaNBody = none ∧
     inFragment faConstCmpQNaNBody = false ∧
     inFragmentWithIntrinsics faConstCmpQNaNBody = false ∧
     progInFragment faConstCmpQNaNBody [] = false ∧
     progInFragmentWithIntrinsics faConstCmpQNaNBody [] = false) ∧
    (∃ mem, ReachesRet (mirCallTree faConstCmpOneNegZeroBody []) []
      (.normal (.scalar (boolToScalar false), mem))) ∧
    MirNoUBTree (mirCallTree faConstCmpOneNegZeroBody []) ∧
    (∃ mem, ReachesRet (mirCallTree faConstCmpSignedZerosBody []) []
      (.normal (.scalar (boolToScalar true), mem))) ∧
    MirNoUBTree (mirCallTree faConstCmpSignedZerosBody []) ∧
    (∃ mem, ReachesRet (mirCallTree faConstCmpQNaNBody []) []
      (.normal (.scalar (boolToScalar false), mem))) ∧
    MirNoUBTree (mirCallTree faConstCmpQNaNBody []) := by
  have h1 := fa_no_float_local_cmp_helper faConstCmpOneNegZeroBody 0x3F800000 0x80000000
    (by rfl)
  have h2 := fa_no_float_local_cmp_helper faConstCmpSignedZerosBody 0x80000000 0x00000000
    (by rfl)
  have h3 := fa_no_float_local_cmp_helper faConstCmpQNaNBody 0x7FC00000 0x7FC00000
    (by rfl)
  exact ⟨rfl, rfl, rfl, h1, h2, h3,
    ⟨_, runA_sound faConstCmpOneNegZeroBody 10 _ _ _ rfl⟩,
    runA_noUB faConstCmpOneNegZeroBody 10 _ _ _ rfl,
    ⟨_, runA_sound faConstCmpSignedZerosBody 10 _ _ _ rfl⟩,
    runA_noUB faConstCmpSignedZerosBody 10 _ _ _ rfl,
    ⟨_, runA_sound faConstCmpQNaNBody 10 _ _ _ rfl⟩,
    runA_noUB faConstCmpQNaNBody 10 _ _ _ rfl⟩
/-- **Anneal's side of the §1 boundary**:
1. `f32`/`f64` `UnOp.neg`, `add`, `sub`, `mul`, `div`, `rem`, and `eq..ge` execute cleanly free of
   UB in Anneal (`mirCallTree`, `MirNoUBTree`), while MiniRust rejects every one of these bodies;
2. `f16` `add`, `f128` `neg`, and non-float `BinOp`s (`bitXor`, `shl`) on `f32` fail closed with
   `.unsupported` (and `EvalRvalueFloatRel` admits `.unsupported` in BOTH modes!);
3. Reading an uninitialized `f32` local in `neg` or `add` faults with `.ub` (`faultsA = true`,
   `¬ MirNoUBTree`, and `EvalRvalueFloatRel` admits `.ub` in BOTH modes!). -/
theorem fa_anneal_float_ops_and_fail_closed_boundary :
    (∃ mem, ReachesRet (mirCallTree faF32NegBody [.scalar ⟨0x3F800000, 4⟩]) []
      (.normal (.scalar ⟨0xBF800000, 4⟩, mem))) ∧
    (∃ mem, ReachesRet (mirCallTree (faF32BinBody "fa::add" .add)
      [.scalar ⟨0x3F800000, 4⟩, .scalar ⟨0x40000000, 4⟩]) []
      (.normal (.scalar ⟨0x40400000, 4⟩, mem))) ∧
    (∃ mem, ReachesRet (mirCallTree (faF32BinBody "fa::sub" .sub)
      [.scalar ⟨0x40400000, 4⟩, .scalar ⟨0x3F800000, 4⟩]) []
      (.normal (.scalar ⟨0x40000000, 4⟩, mem))) ∧
    (∃ mem, ReachesRet (mirCallTree (faF32BinBody "fa::mul" .mul)
      [.scalar ⟨0x40000000, 4⟩, .scalar ⟨0x40400000, 4⟩]) []
      (.normal (.scalar ⟨0x40C00000, 4⟩, mem))) ∧
    (∃ mem, ReachesRet (mirCallTree (faF32BinBody "fa::div" .div)
      [.scalar ⟨0x40C00000, 4⟩, .scalar ⟨0x40000000, 4⟩]) []
      (.normal (.scalar ⟨0x40400000, 4⟩, mem))) ∧
    (∃ mem, ReachesRet (mirCallTree (faF32BinBody "fa::rem" .rem)
      [.scalar ⟨0x40E00000, 4⟩, .scalar ⟨0x40400000, 4⟩]) []
      (.normal (.scalar ⟨0x3F800000, 4⟩, mem))) ∧
    (∃ mem, ReachesRet (mirCallTree (faF32CmpBody "fa::lt" .lt)
      [.scalar ⟨0x3F800000, 4⟩, .scalar ⟨0x40000000, 4⟩]) []
      (.normal (.scalar (boolToScalar true), mem))) ∧
    stepMirFn faF16AddBody (initMachineState faF16AddBody
      [.scalar ⟨0x3C00, 2⟩, .scalar ⟨0x3C00, 2⟩]) = MirStepNode.unsupported ∧
    stepMirFn faF128NegBody (initMachineState faF128NegBody [.scalar ⟨0, 16⟩]) =
      MirStepNode.unsupported ∧
    (∀ mode policy,
      EvalRvalueFloatRel mode policy
        [.init (.scalar ⟨0x3F800000, 4⟩), .init (.scalar ⟨0x3F800000, 4⟩)]
        (.binaryOp .bitXor (.copy (local_ 0)) (.copy (local_ 1)))
        emptyMemory [fcDecl fcF32Ty, fcDecl fcF32Ty] fcLayouts .unsupported ∧
      EvalRvalueFloatRel mode policy
        [.init (.scalar ⟨0x3F800000, 4⟩), .init (.scalar ⟨1, 4⟩)]
        (.binaryOp .shl (.copy (local_ 0)) (.copy (local_ 1)))
        emptyMemory [fcDecl fcF32Ty, fcDecl fcF32Ty] fcLayouts .unsupported) ∧
    faultsA faUninitFloatNegBody 5 (initMachineState faUninitFloatNegBody [.scalar ⟨0, 4⟩]) = true ∧
    ¬ MirNoUBTree (mirCallTree faUninitFloatNegBody [.scalar ⟨0, 4⟩]) ∧
    faultsA faUninitFloatAddBody 5 (initMachineState faUninitFloatAddBody [.scalar ⟨0x3F800000, 4⟩]) = true ∧
    ¬ MirNoUBTree (mirCallTree faUninitFloatAddBody [.scalar ⟨0x3F800000, 4⟩]) ∧
    (∀ mode policy,
      EvalRvalueFloatRel mode policy [.uninit] (.unaryOp .neg (.copy (local_ 0)))
        emptyMemory [fcDecl fcF32Ty] fcLayouts .ub ∧
      EvalRvalueFloatRel mode policy [.init (.scalar ⟨0x3F800000, 4⟩), .uninit]
        (.binaryOp .add (.copy (local_ 0)) (.copy (local_ 1)))
        emptyMemory [fcDecl fcF32Ty, fcDecl fcF32Ty] fcLayouts .ub) := by
  refine ⟨⟨_, runA_sound _ 10 _ _ _ rfl⟩, ⟨_, runA_sound _ 10 _ _ _ rfl⟩,
    ⟨_, runA_sound _ 10 _ _ _ rfl⟩, ⟨_, runA_sound _ 10 _ _ _ rfl⟩,
    ⟨_, runA_sound _ 10 _ _ _ rfl⟩, ⟨_, runA_sound _ 10 _ _ _ rfl⟩,
    ⟨_, runA_sound _ 10 _ _ _ rfl⟩, rfl, rfl, fun mode policy => ⟨?_, ?_⟩,
    rfl, ?_, rfl, ?_, fun mode policy => ⟨?_, ?_⟩⟩
  · refine (EvalRvalueFloatRel_unsupported_iff_evalRvalue mode policy _ _ _ _ _ ?_ ?_).mpr rfl <;>
      (intro _ _ h; cases h)
  · refine (EvalRvalueFloatRel_unsupported_iff_evalRvalue mode policy _ _ _ _ _ ?_ ?_).mpr rfl <;>
      (intro _ _ h; cases h)
  · obtain ⟨tr, u, hr, hf⟩ := faultsA_sound faUninitFloatNegBody 5
      (initMachineState faUninitFloatNegBody [.scalar ⟨0, 4⟩]) rfl
    exact fun hsafe => hsafe tr u hr hf
  · obtain ⟨tr, u, hr, hf⟩ := faultsA_sound faUninitFloatAddBody 5
      (initMachineState faUninitFloatAddBody [.scalar ⟨0x3F800000, 4⟩]) rfl
    exact fun hsafe => hsafe tr u hr hf
  · refine (EvalRvalueFloatRel_ub_iff_evalRvalue mode policy _ _ _ _ _ ?_ ?_).mpr rfl <;>
      (intro _ _ h; cases h)
  · refine (EvalRvalueFloatRel_ub_iff_evalRvalue mode policy _ _ _ _ _ ?_ ?_).mpr rfl <;>
      (intro _ _ h; cases h)

/-! ## §2. IEEE-754 Bit-Carrier Bridges Across `BasicMemory` (`Mach`) & `TreeBorrowsMemory` (`MachTB` + `wfLive`) -/
private theorem fa_nat_xor_two_pow (k : Nat) :
    ∀ b : Nat, b < 2 ^ (k + 1) →
      Nat.xor b (2 ^ k) = if 2 ^ k ≤ b then b - 2 ^ k else b + 2 ^ k := by
  intro b hb
  apply Nat.eq_of_testBit_eq
  intro i
  change (b ^^^ 2 ^ k).testBit i = _
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hge : 2 ^ k ≤ b
  · simp only [hge, ↓reduceIte]
    have hlt : b - 2 ^ k < 2 ^ k := by rw [Nat.pow_succ] at hb; omega
    have hsum : b = (b - 2 ^ k) + 2 ^ k := by omega
    by_cases hi : k = i
    · subst hi
      have hbi : b.testBit k = true := by
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
        have hq : b / 2 ^ k = 1 := by
          rw [Nat.pow_succ] at hb
          exact Nat.div_eq_of_lt_le (by omega) (by omega)
        rw [hq]; rfl
      have hsub : (b - 2 ^ k).testBit k = false := Nat.testBit_lt_two_pow hlt
      simp [hbi, hsub]
    · have hne : decide (k = i) = false := decide_eq_false hi
      rw [hne, Bool.xor_false]
      by_cases hlt_i : i < k
      · have hmod : b % 2 ^ k = b - 2 ^ k := by
          conv => lhs; rw [hsum]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
        rw [← hmod, Nat.testBit_mod_two_pow, decide_eq_true hlt_i, Bool.true_and]
      · have hgt : k + 1 ≤ i := by omega
        have hb0 : b.testBit i = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) hgt))
        have hs0 : (b - 2 ^ k).testBit i = false :=
          Nat.testBit_lt_two_pow
            (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega)))
        rw [hb0, hs0]
  · simp only [hge, ↓reduceIte]
    have hlt : b < 2 ^ k := Nat.lt_of_not_le hge
    by_cases hi : k = i
    · subst hi
      have hbi : b.testBit k = false := Nat.testBit_lt_two_pow hlt
      have hadd : (b + 2 ^ k).testBit k = true := by
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
        have hq : (b + 2 ^ k) / 2 ^ k = 1 := by
          rw [Nat.add_div_right _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hlt]
        rw [hq]; rfl
      simp [hbi, hadd]
    · have hne : decide (k = i) = false := decide_eq_false hi
      rw [hne, Bool.xor_false]
      by_cases hlt_i : i < k
      · have hmod : (b + 2 ^ k) % 2 ^ k = b := by
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
        conv => lhs; rw [← hmod]
        rw [Nat.testBit_mod_two_pow, decide_eq_true hlt_i, Bool.true_and]
      · have hgt : k + 1 ≤ i := by omega
        have hb0 : b.testBit i = false :=
          Nat.testBit_lt_two_pow
            (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega)))
        have ha0 : (b + 2 ^ k).testBit i = false := by
          apply Nat.testBit_lt_two_pow
          have h2 : b + 2 ^ k < 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
          exact Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) hgt)
        rw [hb0, ha0]
/-- **IEEE-754 `f32` unary negation is bitwise XOR with the sign bit `0x80000000`** for EVERY
bit pattern (including signaling NaNs, `cl/1023458250`). -/
theorem fa_evalFloatNeg_eq_natXor_f32 (bits : Nat) :
    evalFloatNeg .binary32 bits = Nat.xor (bits % 2 ^ 32) 0x80000000 := by
  have hlt : bits % 2 ^ 32 < 2 ^ (31 + 1) := Nat.mod_lt bits (by decide)
  exact (fa_nat_xor_two_pow 31 (bits % 2 ^ 32) hlt).symm
/-- **IEEE-754 `f64` unary negation is bitwise XOR with the sign bit `0x8000000000000000`** for
EVERY bit pattern (including signaling NaNs). -/
theorem fa_evalFloatNeg_eq_natXor_f64 (bits : Nat) :
    evalFloatNeg .binary64 bits = Nat.xor (bits % 2 ^ 64) 0x8000000000000000 := by
  have hlt : bits % 2 ^ 64 < 2 ^ (63 + 1) := Nat.mod_lt bits (by decide)
  exact (fa_nat_xor_two_pow 63 (bits % 2 ^ 64) hlt).symm
/-- `MirSemantics.bitwiseXorBits (k + 1) b (2 ^ k)` equals the sign-bit flip for every `b < 2^(k+1)`. -/
theorem fa_bitwiseXorBits_two_pow :
    ∀ (k b : Nat), b < 2 ^ (k + 1) →
      bitwiseXorBits (k + 1) b (2 ^ k) = if 2 ^ k ≤ b then b - 2 ^ k else b + 2 ^ k
  | 0, b, h => by
    simp only [Nat.pow_zero, Nat.pow_succ] at h ⊢
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> rfl
  | k + 1, b, h => by
    have hdiv : b / 2 < 2 ^ (k + 1) := by rw [Nat.pow_succ] at h; omega
    have ih := fa_bitwiseXorBits_two_pow k (b / 2) hdiv
    have h2m : 2 ^ (k + 1) % 2 = 0 := by rw [Nat.pow_succ]; exact Nat.mul_mod_left _ 2
    have h2d : 2 ^ (k + 1) / 2 = 2 ^ k := by
      rw [Nat.pow_succ]; exact Nat.mul_div_cancel _ (by decide)
    change Nat.add (match Nat.beq (b % 2) (2 ^ (k + 1) % 2) with | true => 0 | false => 1)
        (Nat.mul 2 (bitwiseXorBits (k + 1) (b / 2) (2 ^ (k + 1) / 2))) = _
    rw [h2m, h2d, ih]
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rcases (by omega : b % 2 = 0 ∨ b % 2 = 1) with hm | hm
    · rw [hm]
      change 0 + 2 * (if 2 ^ k ≤ b / 2 then b / 2 - 2 ^ k else b / 2 + 2 ^ k) = _
      by_cases hge : 2 ^ k ≤ b / 2
      · have hge' : 2 ^ (k + 1) ≤ b := by omega
        simp only [hge, hge', ↓reduceIte]; omega
      · have hlt' : ¬ 2 ^ (k + 1) ≤ b := by omega
        simp only [hge, hlt', ↓reduceIte]; omega
    · rw [hm]
      change 1 + 2 * (if 2 ^ k ≤ b / 2 then b / 2 - 2 ^ k else b / 2 + 2 ^ k) = _
      by_cases hge : 2 ^ k ≤ b / 2
      · have hge' : 2 ^ (k + 1) ≤ b := by omega
        simp only [hge, hge', ↓reduceIte]; omega
      · have hlt' : ¬ 2 ^ (k + 1) ≤ b := by omega
        simp only [hge, hlt', ↓reduceIte]; omega
/-- Anneal's `evalFloatNeg .binary32` equals `bitwiseXorBits 32 bits 0x80000000` for every 32-bit
pattern. -/
theorem fa_evalFloatNeg_eq_bitwiseXorBits_f32 (bits : Nat) (h : bits < 2 ^ 32) :
    evalFloatNeg .binary32 bits = bitwiseXorBits 32 bits 0x80000000 := by
  have h1 : evalFloatNeg .binary32 bits =
      if 0x80000000 ≤ bits then bits - 0x80000000 else bits + 0x80000000 := by
    unfold evalFloatNeg IeeeFormat.width
    rw [Nat.mod_eq_of_lt h]
    rfl
  rw [h1]
  exact (fa_bitwiseXorBits_two_pow 31 bits h).symm
/-- Anneal's `evalFloatNeg .binary64` equals `bitwiseXorBits 64 bits 0x8000000000000000` for every
64-bit pattern. -/
theorem fa_evalFloatNeg_eq_bitwiseXorBits_f64 (bits : Nat) (h : bits < 2 ^ 64) :
    evalFloatNeg .binary64 bits = bitwiseXorBits 64 bits 0x8000000000000000 := by
  have h1 : evalFloatNeg .binary64 bits =
      if 0x8000000000000000 ≤ bits then bits - 0x8000000000000000
      else bits + 0x8000000000000000 := by
    unfold evalFloatNeg IeeeFormat.width
    rw [Nat.mod_eq_of_lt h]
    rfl
  rw [h1]
  exact (fa_bitwiseXorBits_two_pow 63 bits h).symm
private theorem fa_intBitRec_nat_eq :
    ∀ (fuel : Nat) (a b : Nat), a ≤ fuel →
      intBitRec (fun y => y) (fun y => -y - 1) (fun x y => if x = y then 0 else 1) fuel
        (a : Int) (b : Int) = ((Nat.xor a b : Nat) : Int)
  | 0, a, b, ha => by
    have ha0 : a = 0 := by omega
    subst ha0
    simp [intBitRec]
  | fuel + 1, a, b, ha => by
    unfold intBitRec
    by_cases ha0 : a = 0
    · subst ha0
      simp
    · have hne0 : ((a : Nat) : Int) ≠ 0 := by omega
      have hne1 : ((a : Nat) : Int) ≠ -1 := by omega
      simp only [hne0, hne1, ↓reduceIte]
      have hdiv_le : a / 2 ≤ fuel := by omega
      have hdiv_a : ((a : Nat) : Int) / 2 = ((a / 2 : Nat) : Int) := by omega
      have hdiv_b : ((b : Nat) : Int) / 2 = ((b / 2 : Nat) : Int) := by omega
      have hmod_a : ((a : Nat) : Int) % 2 = ((a % 2 : Nat) : Int) := by omega
      have hmod_b : ((b : Nat) : Int) % 2 = ((b % 2 : Nat) : Int) := by omega
      rw [hdiv_a, hdiv_b, hmod_a, hmod_b, fa_intBitRec_nat_eq fuel (a / 2) (b / 2) hdiv_le]
      have hnat : Nat.xor a b =
          2 * Nat.xor (a / 2) (b / 2) + (if a % 2 = b % 2 then 0 else 1) := by
        apply Nat.eq_of_testBit_eq
        intro i
        cases i with
        | zero =>
          change (a ^^^ b).testBit 0 = _
          rw [Nat.testBit_xor]
          rcases (by omega : a % 2 = 0 ∨ a % 2 = 1) with h1 | h1 <;>
            rcases (by omega : b % 2 = 0 ∨ b % 2 = 1) with h2 | h2 <;>
            simp [Nat.testBit_zero, h1, h2]
        | succ i =>
          change (a ^^^ b).testBit (i + 1) = _
          rw [Nat.testBit_xor]
          have hbit : (if a % 2 = b % 2 then 0 else 1) < 2 := by split <;> omega
          have hsh : (2 * Nat.xor (a / 2) (b / 2) +
              (if a % 2 = b % 2 then 0 else 1)).testBit (i + 1) =
              (Nat.xor (a / 2) (b / 2)).testBit i := by
            rw [Nat.testBit_succ]
            have hq : (2 * Nat.xor (a / 2) (b / 2) + (if a % 2 = b % 2 then 0 else 1)) / 2 =
                Nat.xor (a / 2) (b / 2) := by omega
            rw [hq]
          rw [hsh]
          change _ = ((a / 2) ^^^ (b / 2)).testBit i
          rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ]
      rw [hnat]
      by_cases hmeq : a % 2 = b % 2
      · simp only [hmeq, ↓reduceIte]
        omega
      · have hmeqI : ((a % 2 : Nat) : Int) ≠ ((b % 2 : Nat) : Int) :=
          fun h => hmeq (Int.ofNat.inj h)
        simp only [hmeq, hmeqI, ↓reduceIte]
        omega
/-- MiniRust's `intBitXor` on non-negative integers coincides with `Nat.xor` (choice-free). -/
theorem fa_intBitXor_nat (a b : Nat) :
    intBitXor (a : Int) (b : Int) = ((Nat.xor a b : Nat) : Int) := by
  unfold intBitXor intBitMeasure
  have hnn : ¬ ((a : Int) < 0) := by omega
  simp only [hnn, ↓reduceIte]
  exact fa_intBitRec_nat_eq a a b (Nat.le_refl a)
private theorem fa_bringInBounds_unsigned_nat (n x : Nat) (hx : x < 2 ^ (8 * n)) :
    bringInBounds (x : Int) .Unsigned ⟨n⟩ = (x : Int) := by
  have hlt : (x : Int) < (2 : Int) ^ (8 * n) := by
    have := Int.ofNat_lt.mpr hx
    simpa [Int.natCast_pow] using this
  have hge : (0 : Int) ≤ (x : Int) := Int.natCast_nonneg x
  unfold bringInBounds Size.bits
  exact Int.emod_eq_of_lt hge hlt
/-- **Polymorphic MiniRust `evalBinOpM (.Int .BitXor)` equals Anneal's `evalFloatNeg`** across
BOTH `BasicMemory` and `TreeBorrowsMemory`, for EVERY 32-bit `f32` and 64-bit `f64` bit pattern
(choice-free, signaling NaNs included!). -/
theorem fa_mrM_evalBinOpM_negXor {M : Type} [Gen.Memory M] :
    (∀ (bits : Nat), bits < 2 ^ 32 →
      evalBinOpM (M := M) (.Int .BitXor) (.Int (bits : Int), .Int fcU32It)
          (.Int (0x80000000 : Int), .Int fcU32It) =
        .ok (.Int (evalFloatNeg .binary32 bits : Int), .Int fcU32It)) ∧
    (∀ (bits : Nat), bits < 2 ^ 64 →
      evalBinOpM (M := M) (.Int .BitXor) (.Int (bits : Int), .Int fcU64It)
          (.Int (0x8000000000000000 : Int), .Int fcU64It) =
        .ok (.Int (evalFloatNeg .binary64 bits : Int), .Int fcU64It)) := by
  refine ⟨fun bits h32 => ?_, fun bits h64 => ?_⟩
  · have hxor : Nat.xor bits 0x80000000 = evalFloatNeg .binary32 bits := by
      rw [fa_evalFloatNeg_eq_natXor_f32, Nat.mod_eq_of_lt h32]
    have hlt : evalFloatNeg .binary32 bits < 2 ^ (8 * 4) := evalFloatNeg_lt .binary32 bits
    unfold evalBinOpM evalIntBinOp IntType.bring_in_bounds
    simp only [bind, Except.bind, pure, Except.pure, fcU32It]
    rw [show (0x80000000 : Int) = ((0x80000000 : Nat) : Int) from rfl, fa_intBitXor_nat, hxor, fa_bringInBounds_unsigned_nat 4 _ hlt]
  · have hxor : Nat.xor bits 0x8000000000000000 = evalFloatNeg .binary64 bits := by
      rw [fa_evalFloatNeg_eq_natXor_f64, Nat.mod_eq_of_lt h64]
    have hlt : evalFloatNeg .binary64 bits < 2 ^ (8 * 8) := evalFloatNeg_lt .binary64 bits
    unfold evalBinOpM evalIntBinOp IntType.bring_in_bounds
    simp only [bind, Except.bind, pure, Except.pure, fcU64It]
    rw [show (0x8000000000000000 : Int) = ((0x8000000000000000 : Nat) : Int) from rfl, fa_intBitXor_nat, hxor, fa_bringInBounds_unsigned_nat 8 _ hlt]
/-! ### §2.1 Symbolic `UnOp.neg` ↔ XOR carrier lockstep on `Mach` & `MachTB` (`wfLive`) -/
/-- `fn f64_neg(x: f64) -> f64 { -x }`. -/
def faF64NegBody : CapturedMir :=
  fcBody "float_arith::f64_neg" [fcDecl fcF64Ty, fcDecl fcF64Ty]
    [.assign (local_ 0) (.unaryOp .neg (.copy (local_ 1)))]
/-- `fn f32_neg_bits(x: u32) -> u32 { (-f32::from_bits(x)).to_bits() }`. -/
def faF32NegBitsBody : CapturedMir :=
  fcBody "float_arith::f32_neg_bits"
    [fcDecl fcU32Ty, fcDecl fcU32Ty, fcDecl fcF32Ty, fcDecl fcF32Ty]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.cast .transmute (.copy (local_ 1)) fcF32Ty),
     .assign (local_ 3) (.unaryOp .neg (.copy (local_ 2))),
     .assign (local_ 0) (.cast .transmute (.copy (local_ 3)) fcU32Ty),
     .storageDead 3, .storageDead 2]
/-- `fn f64_neg_bits(x: u64) -> u64 { (-f64::from_bits(x)).to_bits() }`. -/
def faF64NegBitsBody : CapturedMir :=
  fcBody "float_arith::f64_neg_bits"
    [fcDecl fcU64Ty, fcDecl fcU64Ty, fcDecl fcF64Ty, fcDecl fcF64Ty]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.cast .transmute (.copy (local_ 1)) fcF64Ty),
     .assign (local_ 3) (.unaryOp .neg (.copy (local_ 2))),
     .assign (local_ 0) (.cast .transmute (.copy (local_ 3)) fcU64Ty),
     .storageDead 3, .storageDead 2]
/-- Kernel-computed symbolic Anneal run of `(-f32::from_bits(x)).to_bits()`. -/
theorem fa_run_f32_neg_bits_raw (bits : Nat) :
    ∃ mem, runA faF32NegBitsBody 12 (initMachineState faF32NegBitsBody [.scalar ⟨bits, 4⟩]) =
      some ([], .normal (.scalar ⟨fcLeRound 4 (evalFloatNeg .binary32 (fcLeRound 4 bits)), 4⟩,
        mem)) := ⟨_, rfl⟩
private theorem fa_runA_step_tau (body : CapturedMir) (fuel : Nat) (s s' : MachineState)
    (h : stepMirFn body s = .tau (.running s')) :
    runA body (fuel + 1) s = runA body fuel s' := by
  simp [runA, h]
/-- Kernel-computed symbolic Anneal run of `(-f64::from_bits(x)).to_bits()`. -/
theorem fa_run_f64_neg_bits_raw (bits : Nat) :
    ∃ mem, runA faF64NegBitsBody 12 (initMachineState faF64NegBitsBody [.scalar ⟨bits, 8⟩]) =
      some ([], .normal (.scalar ⟨fcLeRound 8 (evalFloatNeg .binary64 (fcLeRound 8 bits)), 8⟩,
        mem)) := by
  let m0 := (initMachineState faF64NegBitsBody []).memory
  let mkS (idx : Nat) (locs : List LocalSlot) : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := idx, locals := locs }, memory := m0 }
  have hs0 : stepMirFn faF64NegBitsBody
      (mkS 0 [.uninit, .init (.scalar ⟨bits, 8⟩), .dead, .dead]) =
      .tau (.running (mkS 1 [.uninit, .init (.scalar ⟨bits, 8⟩), .uninit, .dead])) := rfl
  have hs1 : stepMirFn faF64NegBitsBody
      (mkS 1 [.uninit, .init (.scalar ⟨bits, 8⟩), .uninit, .dead]) =
      .tau (.running (mkS 2 [.uninit, .init (.scalar ⟨bits, 8⟩), .uninit, .uninit])) := rfl
  have hs2 : stepMirFn faF64NegBitsBody
      (mkS 2 [.uninit, .init (.scalar ⟨bits, 8⟩), .uninit, .uninit]) =
      .tau (.running (mkS 3 [.uninit, .init (.scalar ⟨bits, 8⟩),
        .init (.scalar ⟨fcLeRound 8 bits, 8⟩), .uninit])) := rfl
  have hs3 : ∀ x : Nat, stepMirFn faF64NegBitsBody
      (mkS 3 [.uninit, .init (.scalar ⟨bits, 8⟩), .init (.scalar ⟨x, 8⟩), .uninit]) =
      .tau (.running (mkS 4 [.uninit, .init (.scalar ⟨bits, 8⟩),
        .init (.scalar ⟨x, 8⟩), .init (.scalar ⟨evalFloatNeg .binary64 x, 8⟩)])) := fun _ => rfl
  have hs4 : ∀ x y : Nat, stepMirFn faF64NegBitsBody
      (mkS 4 [.uninit, .init (.scalar ⟨bits, 8⟩), .init (.scalar ⟨x, 8⟩),
        .init (.scalar ⟨y, 8⟩)]) =
      .tau (.running (mkS 5 [.init (.scalar ⟨fcLeRound 8 y, 8⟩), .init (.scalar ⟨bits, 8⟩),
        .init (.scalar ⟨x, 8⟩), .init (.scalar ⟨y, 8⟩)])) := fun _ _ => rfl
  have htail : ∀ x y z : Nat, runA faF64NegBitsBody 7
      (mkS 5 [.init (.scalar ⟨z, 8⟩), .init (.scalar ⟨bits, 8⟩), .init (.scalar ⟨x, 8⟩),
        .init (.scalar ⟨y, 8⟩)]) =
      some ([], .normal (.scalar ⟨z, 8⟩, m0)) := fun _ _ _ => rfl
  refine ⟨m0, ?_⟩
  change runA faF64NegBitsBody 12
    (mkS 0 [.uninit, .init (.scalar ⟨bits, 8⟩), .dead, .dead]) = _
  rw [fa_runA_step_tau _ 11 _ _ hs0, fa_runA_step_tau _ 10 _ _ hs1, fa_runA_step_tau _ 9 _ _ hs2, fa_runA_step_tau _ 8 _ _ (hs3 _), fa_runA_step_tau _ 7 _ _ (hs4 _ _)]
  exact htail _ _ _
/-- **Symbolic Anneal `f32` negation pipelines** (for ALL `bits < 2 ^ 32`, including sNaNs):
both `faF32NegBody` and `faF32NegBitsBody` terminate UB-free at `evalFloatNeg .binary32 bits`. -/
theorem fa_sym_f32_neg_bits (bits : Nat) (h : bits < 2 ^ 32) :
    (∃ mem, ReachesRet (mirCallTree faF32NegBody [.scalar ⟨bits, 4⟩]) []
      (.normal (.scalar ⟨evalFloatNeg .binary32 bits, 4⟩, mem))) ∧
    MirNoUBTree (mirCallTree faF32NegBody [.scalar ⟨bits, 4⟩]) ∧
    (∃ mem, ReachesRet (mirCallTree faF32NegBitsBody [.scalar ⟨bits, 4⟩]) []
      (.normal (.scalar ⟨evalFloatNeg .binary32 bits, 4⟩, mem))) ∧
    MirNoUBTree (mirCallTree faF32NegBitsBody [.scalar ⟨bits, 4⟩]) := by
  have hraw0 : ∃ mem, runA faF32NegBody 10 (initMachineState faF32NegBody [.scalar ⟨bits, 4⟩]) =
      some ([], .normal (.scalar ⟨evalFloatNeg .binary32 bits, 4⟩, mem)) := ⟨_, rfl⟩
  obtain ⟨mem0, hr0⟩ := hraw0
  obtain ⟨mem1, hr1⟩ := fa_run_f32_neg_bits_raw bits
  rw [fcLeRound_eq4 bits h, fcLeRound_eq4 _ (evalFloatNeg_lt .binary32 bits)] at hr1
  exact ⟨⟨mem0, runA_sound _ _ _ _ _ hr0⟩, runA_noUB _ _ _ _ _ hr0,
    ⟨mem1, runA_sound _ _ _ _ _ hr1⟩, runA_noUB _ _ _ _ _ hr1⟩
/-- **Symbolic Anneal `f64` negation pipelines** (for ALL `bits < 2 ^ 64`, including sNaNs):
both `faF64NegBody` and `faF64NegBitsBody` terminate UB-free at `evalFloatNeg .binary64 bits`. -/
theorem fa_sym_f64_neg_bits (bits : Nat) (h : bits < 2 ^ 64) :
    (∃ mem, ReachesRet (mirCallTree faF64NegBody [.scalar ⟨bits, 8⟩]) []
      (.normal (.scalar ⟨evalFloatNeg .binary64 bits, 8⟩, mem))) ∧
    MirNoUBTree (mirCallTree faF64NegBody [.scalar ⟨bits, 8⟩]) ∧
    (∃ mem, ReachesRet (mirCallTree faF64NegBitsBody [.scalar ⟨bits, 8⟩]) []
      (.normal (.scalar ⟨evalFloatNeg .binary64 bits, 8⟩, mem))) ∧
    MirNoUBTree (mirCallTree faF64NegBitsBody [.scalar ⟨bits, 8⟩]) := by
  have hraw0 : ∃ mem, runA faF64NegBody 10 (initMachineState faF64NegBody [.scalar ⟨bits, 8⟩]) =
      some ([], .normal (.scalar ⟨evalFloatNeg .binary64 bits, 8⟩, mem)) := ⟨_, rfl⟩
  obtain ⟨mem0, hr0⟩ := hraw0
  obtain ⟨mem1, hr1⟩ := fa_run_f64_neg_bits_raw bits
  rw [fcLeRound_eq8 bits h, fcLeRound_eq8 _ (evalFloatNeg_lt .binary64 bits)] at hr1
  exact ⟨⟨mem0, runA_sound _ _ _ _ _ hr0⟩, runA_noUB _ _ _ _ _ hr0,
    ⟨mem1, runA_sound _ _ _ _ _ hr1⟩, runA_noUB _ _ _ _ _ hr1⟩
/-- Fragment 32-bit sign-bit XOR carrier: `fn neg_xor_u32(x: u32) -> u32 { x ^ 0x8000_0000 }`. -/
def faNegXorU32Body : CapturedMir :=
  ptrBody "float_arith::neg_xor_u32" [u32Decl, u32Decl]
    [.assign (local_ 0) (.binaryOp .bitXor (.copy (local_ 1)) (constU32 0x80000000))]
/-- Translated MiniRust function of `faNegXorU32Body`. -/
def faNegXorU32Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int fcU32It), (localName 1, .Int fcU32It)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .BitXor) (.Load (.Local (localName 1)))
          (.Constant (.Int 0x80000000) (.Int fcU32It)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true
theorem fa_negXorU32_translate : translateFn faNegXorU32Body = some faNegXorU32Fn := rfl
theorem fa_negXorU32_inFragment : inFragment faNegXorU32Body = true := by decide +kernel
theorem fa_negXorU32_ctxOk : CtxOk faNegXorU32Body ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd
    match i, hd with
    | 0, hd => simp only [faNegXorU32Body, ptrBody] at hd; cases hd; decide
    | 1, hd => simp only [faNegXorU32Body, ptrBody] at hd; cases hd; decide
    | _ + 2, hd => simp [faNegXorU32Body, ptrBody] at hd
  ret := by
    intro d hd
    simp only [faNegXorU32Body, ptrBody] at hd
    cases hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩
theorem fa_negXorU32_argsOk (bits : Nat) (h : bits < 2 ^ 32) :
    argsOk faNegXorU32Body [.scalar ⟨bits, 4⟩] = true := by
  have h' : bits < 2 ^ (8 * 4) := h
  simp [argsOk, argsOkAux, declArgOk, faNegXorU32Body, ptrBody, u32Decl, u32Ty, argOk, tyOf,
    translateTy, scalarTypeOf, isBoolTy, isOrderingTy, intBoolTupleOf, intTypeOf, intTyBytes,
    tyBytes, validBits, h']
theorem fa_run_negXorU32_raw (bits : Nat) :
    ∃ mem, runA faNegXorU32Body 10 (initMachineState faNegXorU32Body [.scalar ⟨bits, 4⟩]) =
      some ([], .normal (.scalar ⟨bitwiseXorBits 32 bits 0x80000000, 4⟩, mem)) := ⟨_, rfl⟩
/-- Fragment 64-bit sign-bit XOR carrier:
`fn neg_xor_u64(x: u64) -> u64 { x ^ 0x8000_0000_0000_0000 }`. -/
def faNegXorU64Body : CapturedMir :=
  ptrBody "float_arith::neg_xor_u64" [fcDecl fcU64Ty0, fcDecl fcU64Ty0]
    [.assign (local_ 0) (.binaryOp .bitXor (.copy (local_ 1)) (faConstU64 0x8000000000000000))]
/-- Translated MiniRust function of `faNegXorU64Body`. -/
def faNegXorU64Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int fcU64It), (localName 1, .Int fcU64It)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .BitXor) (.Load (.Local (localName 1)))
          (.Constant (.Int 0x8000000000000000) (.Int fcU64It)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true
theorem fa_negXorU64_translate : translateFn faNegXorU64Body = some faNegXorU64Fn := rfl
theorem fa_negXorU64_inFragment : inFragment faNegXorU64Body = true := by decide +kernel
theorem fa_negXorU64_ctxOk : CtxOk faNegXorU64Body fcCtx8 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd
    match i, hd with
    | 0, hd => simp only [faNegXorU64Body, ptrBody] at hd; cases hd; decide
    | 1, hd => simp only [faNegXorU64Body, ptrBody] at hd; cases hd; decide
    | _ + 2, hd => simp [faNegXorU64Body, ptrBody] at hd
  ret := by
    intro d hd
    simp only [faNegXorU64Body, ptrBody] at hd
    cases hd
    exact ⟨0, fcRetAlloc8, rfl, rfl, rfl, rfl, rfl, by decide⟩
theorem fa_negXorU64_argsOk (bits : Nat) (h : bits < 2 ^ 64) :
    argsOk faNegXorU64Body [.scalar ⟨bits, 8⟩] = true := by
  have h' : bits < 2 ^ (8 * 8) := h
  simp [argsOk, argsOkAux, declArgOk, faNegXorU64Body, ptrBody, fcDecl, fcU64Ty0, argOk, tyOf,
    translateTy, scalarTypeOf, isBoolTy, isOrderingTy, intBoolTupleOf, intTypeOf, intTyBytes,
    tyBytes, validBits, h']
theorem fa_run_negXorU64_raw (bits : Nat) :
    ∃ mem, runA faNegXorU64Body 10 (initMachineState faNegXorU64Body [.scalar ⟨bits, 8⟩]) =
      some ([], .normal (.scalar ⟨bitwiseXorBits 64 bits 0x8000000000000000, 8⟩, mem)) := ⟨_, rfl⟩
/-- **Symbolic `f32` `UnOp.neg` ↔ MiniRust `x ^ 0x8000_0000_u32` lockstep across ALL `2 ^ 32`
bit patterns** (signaling NaNs included!):
1. Anneal's `(-f32::from_bits(x)).to_bits()` returns `evalFloatNeg .binary32 bits` free of UB;
2. MiniRust's `BasicMemory` machine (`Interp.steps`) running `faNegXorU32Body` from `startMachine`
   terminates in the caller with the caller's return place holding the EXACT byte encoding of
   Anneal's `evalFloatNeg .binary32 bits`;
3. Those return bytes decode at `u32` to `evalFloatNeg .binary32 bits` (= `Nat.xor bits 0x80000000`)
   and transmute losslessly to `i32` and `[u8; 4]` across both `BM` and `TBM`. -/
theorem fa_sym_mr_negXor_f32_lockstep (bits : Nat) (h : bits < 2 ^ 32) :
    (∃ mem, ReachesRet (mirCallTree faF32NegBitsBody [.scalar ⟨bits, 4⟩]) []
      (.normal (.scalar ⟨evalFloatNeg .binary32 bits, 4⟩, mem))) ∧
    (∃ (m : Mach) (n : Nat) (m' : Mach),
      startMachine faNegXorU32Body [.scalar ⟨bits, 4⟩] = some m ∧
      Interp.steps n m = .ok m' ∧
      m'.threads = [thread1 ctx0 [{ ctx0.caller with next_block := ctx0.nextBlock, next_stmt := 0 }]] ∧
      m'.mem.memory.allocations[0]? =
        some { retAlloc with
          data := (encodeLittleEndianBytes (evalFloatNeg .binary32 bits) 4 none).map fcByteToMR }) ∧
    Type.decode (.Int fcU32It)
        ((encodeLittleEndianBytes (evalFloatNeg .binary32 bits) 4 none).map fcByteToMR) =
      .ok (some (.Int (evalFloatNeg .binary32 bits : Int))) ∧
    transmuteM (M := TBM) (.Int (evalFloatNeg .binary32 bits : Int)) (.Int fcU32It)
        (.Array (.Int fcU8It) 4) =
      .ok (.Tuple (fcLeByteValsMRM (evalFloatNeg .binary32 bits) 4)) := by
  have hnegLt : evalFloatNeg .binary32 bits < 2 ^ (8 * 4) := evalFloatNeg_lt .binary32 bits
  obtain ⟨memA, hrunA⟩ := fa_run_negXorU32_raw bits
  rw [← fa_evalFloatNeg_eq_bitwiseXorBits_f32 bits h] at hrunA
  have hretA := runA_sound _ _ _ _ _ hrunA
  let m := machine faNegXorU32Body faNegXorU32Fn
    (initMachineState faNegXorU32Body [.scalar ⟨bits, 4⟩]).frame.locals faNegXorU32Fn.start
  have hm : startMachine faNegXorU32Body [.scalar ⟨bits, 4⟩] = some m := by
    simp [startMachine, fa_negXorU32_translate, m]
  obtain ⟨n, s', m', hsteps, hrel⟩ := mirCall_ret fa_negXorU32_inFragment fa_negXorU32_translate
    ctx0 fa_negXorU32_ctxOk [.scalar ⟨bits, 4⟩] (fa_negXorU32_argsOk bits h) m rfl rfl rfl hretA
  obtain ⟨r, a, d, R, hd, _, hprov, ha, hthreads, hallocs, _⟩ := hrel
  simp only [faNegXorU32Body, ptrBody, List.getElem?_cons_zero, Option.some.injEq] at hd
  have hr : r = 0 := by
    simp only [ctx0, retPtr, Option.some.injEq, Prod.mk.injEq, and_true] at hprov
    have h0 : (r : Int) = 0 := (congrArg Gen.AllocId._0 hprov).symm
    omega
  subst hr hd
  simp only [ctx0, List.getElem?_cons_zero, Option.some.injEq] at ha
  subst ha
  refine ⟨(fa_sym_f32_neg_bits bits h).2.2.1, ⟨m, n, m', hm, hsteps, hthreads, ?_⟩,
    fc_mr_decode_eq_anneal .Unsigned 4 _ none hnegLt,
    (fc_mrM_transmute_int_bytes4 (M := TBM) .Unsigned _ hnegLt none).1⟩
  rw [hallocs, fc_map_encodeLittleEndianBytes .Unsigned none 4 (evalFloatNeg .binary32 bits)]
  rfl
/-- **Symbolic `f64` `UnOp.neg` ↔ MiniRust `x ^ 0x8000_0000_0000_0000_u64` lockstep across ALL
`2 ^ 64` bit patterns** (signaling NaNs included!), running under the 8-byte return place `fcCtx8`. -/
theorem fa_sym_mr_negXor_f64_lockstep (bits : Nat) (h : bits < 2 ^ 64) :
    (∃ mem, ReachesRet (mirCallTree faF64NegBitsBody [.scalar ⟨bits, 8⟩]) []
      (.normal (.scalar ⟨evalFloatNeg .binary64 bits, 8⟩, mem))) ∧
    (∃ (m : Mach) (n : Nat) (m' : Mach),
      fcStartMachine8 faNegXorU64Body [.scalar ⟨bits, 8⟩] = some m ∧
      Interp.steps n m = .ok m' ∧
      m'.threads =
        [thread1 fcCtx8 [{ fcCtx8.caller with next_block := fcCtx8.nextBlock, next_stmt := 0 }]] ∧
      m'.mem.memory.allocations[0]? =
        some { fcRetAlloc8 with
          data := (encodeLittleEndianBytes (evalFloatNeg .binary64 bits) 8 none).map fcByteToMR }) ∧
    Type.decode (.Int fcU64It)
        ((encodeLittleEndianBytes (evalFloatNeg .binary64 bits) 8 none).map fcByteToMR) =
      .ok (some (.Int (evalFloatNeg .binary64 bits : Int))) ∧
    transmuteM (M := TBM) (.Int (evalFloatNeg .binary64 bits : Int)) (.Int fcU64It)
        (.Array (.Int fcU8It) 8) =
      .ok (.Tuple (fcLeByteValsMRM (evalFloatNeg .binary64 bits) 8)) := by
  have hnegLt : evalFloatNeg .binary64 bits < 2 ^ (8 * 8) := evalFloatNeg_lt .binary64 bits
  obtain ⟨memA, hrunA⟩ := fa_run_negXorU64_raw bits
  rw [← fa_evalFloatNeg_eq_bitwiseXorBits_f64 bits h] at hrunA
  have hretA := runA_sound _ _ _ _ _ hrunA
  let m := machineWithCtx fcCtx8 faNegXorU64Body faNegXorU64Fn
    (initMachineState faNegXorU64Body [.scalar ⟨bits, 8⟩]).frame.locals faNegXorU64Fn.start
  have hm : fcStartMachine8 faNegXorU64Body [.scalar ⟨bits, 8⟩] = some m := by
    simp [fcStartMachine8, fa_negXorU64_translate, m]
  obtain ⟨n, s', m', hsteps, hrel⟩ := mirCall_ret fa_negXorU64_inFragment fa_negXorU64_translate
    fcCtx8 fa_negXorU64_ctxOk [.scalar ⟨bits, 8⟩] (fa_negXorU64_argsOk bits h) m rfl rfl rfl hretA
  obtain ⟨r, a, d, R, hd, _, hprov, ha, hthreads, hallocs, _⟩ := hrel
  simp only [faNegXorU64Body, ptrBody, List.getElem?_cons_zero, Option.some.injEq] at hd
  have hr : r = 0 := by
    simp only [fcCtx8, retPtr, Option.some.injEq, Prod.mk.injEq, and_true] at hprov
    have h0 : (r : Int) = 0 := (congrArg Gen.AllocId._0 hprov).symm
    omega
  subst hr hd
  simp only [fcCtx8, List.getElem?_cons_zero, Option.some.injEq] at ha
  subst ha
  refine ⟨(fa_sym_f64_neg_bits bits h).2.2.1, ⟨m, n, m', hm, hsteps, hthreads, ?_⟩,
    fc_mr_decode_eq_anneal .Unsigned 8 _ none hnegLt,
    (fc_mrM_transmute_int_bytes8 (M := TBM) .Unsigned _ hnegLt none).1⟩
  rw [hallocs, fc_map_encodeLittleEndianBytes .Unsigned none 8 (evalFloatNeg .binary64 bits)]
  rfl
/-- **`Mach` (`BasicMemory`) + `MachTB` (`TreeBorrowsMemory` + `MachTB.wfLive`) lockstep for the
`UnOp.neg` ↔ XOR sign-bit carriers**, verified across signaling NaNs (`0x7F800001`, `0x7FA00001`,
`0x7FF0000000000001`), quiet NaNs (`0x7FC00000`), signed zeros (`±0.0`), and normal `1.0`. -/
theorem fa_negXor_f32_f64_machTB_wfLive :
    -- f32 sNaN 0x7F800001 -> 0xFF800001 (payload & signaling bit preserved!)
    retAfter faNegXorU32Body [.scalar ⟨0x7F800001, 4⟩] 3 =
      some (some { retAlloc with data := (encodeLittleEndianBytes 0xFF800001 4 none).map fcByteToMR },
        [1]) ∧
    retAfterTB faNegXorU32Body [.scalar ⟨0x7F800001, 4⟩] 3 = tbRetU32 0xFF800001 ∧
    (∃ m0 m', startMachineTB faNegXorU32Body [.scalar ⟨0x7F800001, 4⟩] = some m0 ∧
      Interp.stepsTB 3 m0 = .ok m' ∧ MachTB.wfLive m') ∧
    -- f32 sNaN 0x7FA00001 -> 0xFFA00001 & qNaN 0x7FC00000 -> 0xFFC00000
    retAfterTB faNegXorU32Body [.scalar ⟨0x7FA00001, 4⟩] 3 = tbRetU32 0xFFA00001 ∧
    retAfterTB faNegXorU32Body [.scalar ⟨0x7FC00000, 4⟩] 3 = tbRetU32 0xFFC00000 ∧
    -- f32 +0.0 -> -0.0 and -0.0 -> +0.0
    retAfterTB faNegXorU32Body [.scalar ⟨0x00000000, 4⟩] 3 = tbRetU32 0x80000000 ∧
    retAfterTB faNegXorU32Body [.scalar ⟨0x80000000, 4⟩] 3 = tbRetU32 0x00000000 ∧
    -- f64 sNaN 0x7FF0000000000001 -> 0xFFF0000000000001 (Mach + MachTB + wfLive)
    fcRetAfter8 faNegXorU64Body [.scalar ⟨0x7FF0000000000001, 8⟩] 3 =
      some (some { fcRetAlloc8 with
        data := (encodeLittleEndianBytes 0xFFF0000000000001 8 none).map fcByteToMR }, [1]) ∧
    fcRetAfterTB8 faNegXorU64Body [.scalar ⟨0x7FF0000000000001, 8⟩] 3 =
      tbRetU64 0xFFF0000000000001 ∧
    (∃ m0 m', fcStartMachineTB8 faNegXorU64Body [.scalar ⟨0x7FF0000000000001, 8⟩] = some m0 ∧
      Interp.stepsTB 3 m0 = .ok m' ∧ MachTB.wfLive m') ∧
    -- f64 -0.0 -> +0.0 and 1.0 -> -1.0
    fcRetAfterTB8 faNegXorU64Body [.scalar ⟨0x8000000000000000, 8⟩] 3 =
      tbRetU64 0x0000000000000000 ∧
    fcRetAfterTB8 faNegXorU64Body [.scalar ⟨0x3FF0000000000000, 8⟩] 3 =
      tbRetU64 0xBFF0000000000000 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_,
    by decide +kernel, by decide +kernel⟩
  · exact fa_wfLive_of_stepsTB_isOk
      (machine faNegXorU32Body faNegXorU32Fn
        (initMachineState faNegXorU32Body [.scalar ⟨0x7F800001, 4⟩]).frame.locals faNegXorU32Fn.start)
      3 (by decide +kernel)
  · exact fa_wfLive_of_stepsTB_isOk
      (machineWithCtx fcCtx8 faNegXorU64Body faNegXorU64Fn
        (initMachineState faNegXorU64Body [.scalar ⟨0x7FF0000000000001, 8⟩]).frame.locals
        faNegXorU64Fn.start)
      3 (by decide +kernel)
/-! ### §2.2 `Bool` comparison carriers & `EvalFloatBinOpRel` / `nanChoices` carrier bridges -/
/-- **Choice-free polymorphic `Bool ↔ u8` carrier codec** across BOTH `BasicMemory` and
`TreeBorrowsMemory`, matching Anneal's `boolToScalar` byte image byte for byte. -/
theorem fa_mrM_bool_codec {M : Type} [Gen.Memory M] [MemoryOps M] (b : Bool)
    (m : Option (Gen.Machine M)) :
    Type.encodeM (M := M) .Bool (.Bool b) =
      .ok [.Init (if b then 1 else 0) none] ∧
    Type.decodeM (M := M) .Bool [.Init (if b then 1 else 0) none] = .ok (some (.Bool b)) ∧
    transmuteM (M := M) (.Bool b) .Bool (.Int fcU8It) m =
      .ok (.Int (if b then 1 else 0)) ∧
    transmuteM (M := M) (.Int (if b then 1 else 0)) (.Int fcU8It) .Bool m =
      .ok (.Bool b) ∧
    Type.encode .Bool (.Bool b) =
      .ok ((encodeLittleEndianBytes (boolToScalar b).bits 1 none).map fcByteToMR) ∧
    Type.decode .Bool ((encodeLittleEndianBytes (boolToScalar b).bits 1 none).map fcByteToMR) =
      .ok (some (.Bool b)) := by
  cases b <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
/-- **Float comparison carrier bridge (both `FloatArithMode`s, both `BM` and `TBM`)**: whenever
`evalFloatCmp op f a b = some c`, `EvalFloatBinOpRel mode op f a b (boolToScalar c)` holds and
Anneal's 1-byte `boolToScalar c` image round-trips losslessly through MiniRust's `Bool` and `u8`
carriers across both `BasicMemory` and `TreeBorrowsMemory`. -/
theorem fa_bridge_floatCmp (mode : FloatArithMode) (op : BinOp) (f : IeeeFormat) (a b : Nat)
    (c : Bool) (hc : evalFloatCmp op f a b = some c) :
    EvalFloatBinOpRel mode op f a b (boolToScalar c) ∧
    Type.encode .Bool (.Bool c) =
      .ok ((encodeLittleEndianBytes (boolToScalar c).bits 1 none).map fcByteToMR) ∧
    Type.decode .Bool ((encodeLittleEndianBytes (boolToScalar c).bits 1 none).map fcByteToMR) =
      .ok (some (.Bool c)) ∧
    transmuteM (M := BM) (.Bool c) .Bool (.Int fcU8It) = .ok (.Int (if c then 1 else 0)) ∧
    transmuteM (M := TBM) (.Bool c) .Bool (.Int fcU8It) = .ok (.Int (if c then 1 else 0)) ∧
    transmuteM (M := TBM) (.Int (if c then 1 else 0)) (.Int fcU8It) .Bool = .ok (.Bool c) := by
  have hrel : EvalFloatBinOpRel mode op f a b (boolToScalar c) := by
    unfold EvalFloatBinOpRel
    rw [hc]
  have hbm := fa_mrM_bool_codec (M := BM) c none
  have htb := fa_mrM_bool_codec (M := TBM) c none
  exact ⟨hrel, hbm.2.2.2.2.1, hbm.2.2.2.2.2, hbm.2.2.1, htb.2.2.1, htb.2.2.2.1⟩
/-- **Carrier encoding bridge for every admissible `nanChoices` candidate** (both `.deterministic`
and `.nondeterministic`, both `f32` and `f64`, choice-free): every `cand ∈ nanChoices f inputs mode`
is a canonical `f.byteWidth`-byte bit pattern whose Anneal byte image round-trips losslessly through
MiniRust `Type.encode`, `Type.decode`, `transmute`, and polymorphic `transmuteM` across `BM` and
`TBM` (`u32`/`i32`/`[u8; 4]` for `f32`; `u64`/`i64`/`[u8; 8]` for `f64`). -/
theorem fa_bridge_nanChoices_carriers (mode : FloatArithMode) (f : IeeeFormat)
    (inputs : List (IeeeFormat × Nat)) (cand : Nat) (hmem : cand ∈ nanChoices f inputs mode) :
    cand < 2 ^ (8 * f.byteWidth) ∧
    isNaNBits f cand = true ∧
    Type.encode (.Int ⟨.Unsigned, ⟨f.byteWidth⟩⟩) (.Int (cand : Int)) =
      .ok ((encodeLittleEndianBytes cand f.byteWidth none).map fcByteToMR) ∧
    Type.decode (.Int ⟨.Unsigned, ⟨f.byteWidth⟩⟩)
        ((encodeLittleEndianBytes cand f.byteWidth none).map fcByteToMR) =
      .ok (some (.Int (cand : Int))) ∧
    transmuteM (M := BM) (.Int (cand : Int))
        (.Int ⟨.Unsigned, ⟨f.byteWidth⟩⟩) (.Int ⟨.Signed, ⟨f.byteWidth⟩⟩) =
      .ok (.Int (intFromBits cand ⟨.Signed, ⟨f.byteWidth⟩⟩)) ∧
    transmuteM (M := TBM) (.Int (cand : Int))
        (.Int ⟨.Unsigned, ⟨f.byteWidth⟩⟩) (.Int ⟨.Signed, ⟨f.byteWidth⟩⟩) =
      .ok (.Int (intFromBits cand ⟨.Signed, ⟨f.byteWidth⟩⟩)) ∧
    transmuteM (M := TBM) (.Int (cand : Int))
        (.Int ⟨.Unsigned, ⟨f.byteWidth⟩⟩) (.Array (.Int fcU8It) f.byteWidth) =
      .ok (.Tuple (fcLeByteValsMRM cand f.byteWidth)) ∧
    transmuteM (M := TBM) (.Tuple (fcLeByteValsMRM cand f.byteWidth))
        (.Array (.Int fcU8It) f.byteWidth) (.Int ⟨.Unsigned, ⟨f.byteWidth⟩⟩) =
      .ok (.Int (cand : Int)) := by
  obtain ⟨hltW, hnan⟩ := mem_nanChoices_props f inputs mode cand hmem
  have hlt : cand < 2 ^ (8 * f.byteWidth) := by rw [← fc_ieeeFormat_width]; exact hltW
  have hgood := fc_goodSize_byteWidth f
  have harr :
      transmuteM (M := TBM) (.Int (cand : Int))
          (.Int ⟨.Unsigned, ⟨f.byteWidth⟩⟩) (.Array (.Int fcU8It) f.byteWidth) =
        .ok (.Tuple (fcLeByteValsMRM cand f.byteWidth)) ∧
      transmuteM (M := TBM) (.Tuple (fcLeByteValsMRM cand f.byteWidth))
          (.Array (.Int fcU8It) f.byteWidth) (.Int ⟨.Unsigned, ⟨f.byteWidth⟩⟩) =
        .ok (.Int (cand : Int)) := by
    cases f with
    | binary32 => exact fc_mrM_transmute_int_bytes4 (M := TBM) .Unsigned cand hlt none
    | binary64 => exact fc_mrM_transmute_int_bytes8 (M := TBM) .Unsigned cand hlt none
  exact ⟨hlt, hnan,
    fc_mr_encode_eq_anneal .Unsigned f.byteWidth cand hgood hlt,
    fc_mr_decode_eq_anneal .Unsigned f.byteWidth cand none hlt,
    fc_mrBM_transmute_int .Unsigned .Signed f.byteWidth cand hgood hlt none,
    fc_mrTB_transmute_int .Unsigned .Signed f.byteWidth cand hgood hlt none,
    harr.1, harr.2⟩
/-- **Unified `EvalFloatBinOpRel` carrier bridge (both `.deterministic` and `.nondeterministic`,
comparisons AND arithmetic, `BM` AND `TBM`, choice-free)**: every output scalar `outSc` admitted by
`EvalFloatBinOpRel mode op f a b outSc` has a canonical MiniRust carrier encoding (`Bool`/`u8` for
comparisons, `u32`/`i32`/`[u8; 4]` for `f32` arithmetic, `u64`/`i64`/`[u8; 8]` for `f64`
arithmetic) that round-trips losslessly through `Type.encode`, `Type.decode`, `transmute`, and
`transmuteM` over both `BasicMemory` and `TreeBorrowsMemory`. -/
theorem fa_bridge_evalFloatBinOpRel_carriers (mode : FloatArithMode) (op : BinOp) (f : IeeeFormat)
    (a b : Nat) (outSc : ScalarInt) (hrel : EvalFloatBinOpRel mode op f a b outSc) : (∃ c, evalFloatCmp op f a b = some c ∧ outSc = boolToScalar c ∧
      Type.encode .Bool (.Bool c) =
        .ok ((encodeLittleEndianBytes outSc.bits 1 none).map fcByteToMR) ∧
      Type.decode .Bool ((encodeLittleEndianBytes outSc.bits 1 none).map fcByteToMR) =
        .ok (some (.Bool c)) ∧
      transmuteM (M := BM) (.Bool c) .Bool (.Int fcU8It) = .ok (.Int (if c then 1 else 0)) ∧
      transmuteM (M := TBM) (.Bool c) .Bool (.Int fcU8It) = .ok (.Int (if c then 1 else 0))) ∨
    (evalFloatCmp op f a b = none ∧ outSc.sizeBytes = f.byteWidth ∧
      outSc.bits < 2 ^ (8 * f.byteWidth) ∧
      Type.encode (.Int ⟨.Unsigned, ⟨f.byteWidth⟩⟩) (.Int (outSc.bits : Int)) =
        .ok ((encodeLittleEndianBytes outSc.bits f.byteWidth none).map fcByteToMR) ∧
      Type.decode (.Int ⟨.Unsigned, ⟨f.byteWidth⟩⟩)
          ((encodeLittleEndianBytes outSc.bits f.byteWidth none).map fcByteToMR) =
        .ok (some (.Int (outSc.bits : Int))) ∧
      transmuteM (M := BM) (.Int (outSc.bits : Int))
          (.Int ⟨.Unsigned, ⟨f.byteWidth⟩⟩) (.Int ⟨.Signed, ⟨f.byteWidth⟩⟩) =
        .ok (.Int (intFromBits outSc.bits ⟨.Signed, ⟨f.byteWidth⟩⟩)) ∧
      transmuteM (M := TBM) (.Int (outSc.bits : Int))
          (.Int ⟨.Unsigned, ⟨f.byteWidth⟩⟩) (.Int ⟨.Signed, ⟨f.byteWidth⟩⟩) =
        .ok (.Int (intFromBits outSc.bits ⟨.Signed, ⟨f.byteWidth⟩⟩)) ∧
      transmuteM (M := TBM) (.Int (outSc.bits : Int))
          (.Int ⟨.Unsigned, ⟨f.byteWidth⟩⟩) (.Array (.Int fcU8It) f.byteWidth) =
        .ok (.Tuple (fcLeByteValsMRM outSc.bits f.byteWidth))) := by
  rcases EvalFloatBinOpRel_out_wf mode op f a b outSc hrel with
    ⟨c, hc, rfl⟩ | ⟨hcmp, hsz, hltW⟩
  · have hbr := fa_bridge_floatCmp mode op f a b c hc
    exact Or.inl ⟨c, hc, rfl, hbr.2.1, hbr.2.2.1, hbr.2.2.2.1, hbr.2.2.2.2.1⟩
  · have hlt : outSc.bits < 2 ^ (8 * f.byteWidth) := by rw [← fc_ieeeFormat_width]; exact hltW
    have hgood := fc_goodSize_byteWidth f
    have harr : transmuteM (M := TBM) (.Int (outSc.bits : Int))
        (.Int ⟨.Unsigned, ⟨f.byteWidth⟩⟩) (.Array (.Int fcU8It) f.byteWidth) =
        .ok (.Tuple (fcLeByteValsMRM outSc.bits f.byteWidth)) := by
      cases f with
      | binary32 => exact (fc_mrM_transmute_int_bytes4 (M := TBM) .Unsigned outSc.bits hlt none).1
      | binary64 => exact (fc_mrM_transmute_int_bytes8 (M := TBM) .Unsigned outSc.bits hlt none).1
    exact Or.inr ⟨hcmp, hsz, hlt,
      fc_mr_encode_eq_anneal .Unsigned f.byteWidth outSc.bits hgood hlt,
      fc_mr_decode_eq_anneal .Unsigned f.byteWidth outSc.bits none hlt,
      fc_mrBM_transmute_int .Unsigned .Signed f.byteWidth outSc.bits hgood hlt none,
      fc_mrTB_transmute_int .Unsigned .Signed f.byteWidth outSc.bits hgood hlt none,
      harr⟩
/-- **Symbolic `BasicMemory` machine carrier execution for EVERY arithmetic `EvalFloatBinOpRel`
outcome** (both `.deterministic` and `.nondeterministic`, including every `nanChoices` candidate):
for `f32` (`f = .binary32`) the MiniRust 32-bit carrier runs via `Interp.steps` to Anneal's exact
4-byte image in `retAlloc`; for `f64` (`f = .binary64`) the MiniRust 64-bit carrier runs via
`Interp.steps` under `fcCtx8` to Anneal's exact 8-byte image in `fcRetAlloc8`. `TreeBorrowsMemory`
(`Interp.stepsTB` + `MachTB.wfLive`) runs on every `binary64` `nanChoices` outcome of a concrete sNaN
addition are kernel-checked by `w11_mr_*` in `tests/mir/FloatArithAndUcg630Tests.lean`. -/
theorem fa_bridge_evalFloatBinOpRel_mach_steps (mode : FloatArithMode) (op : BinOp)
    (a b : Nat) (outSc : ScalarInt) (hop : isFloatArithBinOp op = true) : (EvalFloatBinOpRel mode op .binary32 a b outSc →
      outSc.sizeBytes = 4 ∧
      ∃ (m : Mach) (n : Nat) (m' : Mach),
        startMachine fcCarrierCastBody [.scalar ⟨outSc.bits, 4⟩] = some m ∧
        Interp.steps n m = .ok m' ∧
        m'.mem.memory.allocations[0]? =
          some { retAlloc with data := (encodeLittleEndianBytes outSc.bits 4 none).map fcByteToMR }) ∧
    (EvalFloatBinOpRel mode op .binary64 a b outSc →
      outSc.sizeBytes = 8 ∧
      ∃ (f : Gen.Function) (n : Nat) (m' : Mach),
        translateFn fcCarrierCast64Body = some f ∧
        Interp.steps n (machineWithCtx fcCtx8 fcCarrierCast64Body f
          (initMachineState fcCarrierCast64Body [.scalar ⟨outSc.bits, 8⟩]).frame.locals f.start) =
          .ok m' ∧
        m'.mem.memory.allocations[0]? =
          some { fcRetAlloc8 with
            data := (encodeLittleEndianBytes outSc.bits 8 none).map fcByteToMR }) := by
  refine ⟨fun hrel => ?_, fun hrel => ?_⟩
  · rcases EvalFloatBinOpRel_out_wf mode op .binary32 a b outSc hrel with
      ⟨c, hc, _⟩ | ⟨_, hsz, hlt⟩
    · rw [evalFloatCmp_of_arith op .binary32 a b hop] at hc; cases hc
    · obtain ⟨m, n, m', hm, hs, _, ha⟩ := fc_sym_mr_carrier_steps outSc.bits hlt
      exact ⟨hsz, m, n, m', hm, hs, ha⟩
  · rcases EvalFloatBinOpRel_out_wf mode op .binary64 a b outSc hrel with
      ⟨c, hc, _⟩ | ⟨_, hsz, hlt⟩
    · rw [evalFloatCmp_of_arith op .binary64 a b hop] at hc; cases hc
    · obtain ⟨fn, n, m', hfn, hs, _, ha⟩ := fc_sym_mr_carrier64_steps outSc.bits hlt
      exact ⟨hsz, fn, n, m', hfn, hs, ha⟩

/-! ## §3. Mode-Parametric `Ptr2IntTransmutePolicy` (`ucg#630` vs. `reference#1752`) Correspondence Across `Mach` & `MachTB` -/
/-- Policy-parametric step-level reduction of `evalByteCast`. -/
theorem fa_evalByteCast_eq
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory) (decls : List LocalDecl)
    (layouts : LayoutTable) (v : Value) (srcTy dstTy : Ty) (srcSize dstSize : Nat) (policy : Ptr2IntTransmutePolicy)
    (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok v locals')
    (h_dst_sz : tyByteSize decls layouts (resolveTyWithLocalDecls decls layouts dstTy) =
      some dstSize)
    (h_ty : operandTy decls layouts op = some srcTy) (h_src_sz : tyByteSize decls layouts (resolveTyWithLocalDecls decls layouts srcTy) =
      some srcSize) :
    evalByteCast locals op dstTy mem decls layouts policy =
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
                (resolveTyWithLocalDecls decls layouts dstTy) bs policy with
            | .some v' => .ok v' locals' mem
            | .none => .ub := by
  unfold evalByteCast resolveByteCastSrcTyAndSize
  rw [h_op]
  dsimp only
  rw [h_dst_sz]
  dsimp only
  rw [h_ty]
  dsimp only
  rw [h_src_sz]
  rfl
/-- Policy-parametric `evalByteCast` reduction when source encoding succeeds at the target size. -/
theorem fa_evalByteCast_of_encode
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory) (decls : List LocalDecl) (layouts : LayoutTable) (v : Value) (srcTy dstTy : Ty) (size : Nat)
    (bs : List MirSemantics.AbstractByte) (policy : Ptr2IntTransmutePolicy) (h_op : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok v locals')
    (h_dst_sz : tyByteSize decls layouts (resolveTyWithLocalDecls decls layouts dstTy) = some size) (h_ty : operandTy decls layouts op = some srcTy)
    (h_src_sz : tyByteSize decls layouts (resolveTyWithLocalDecls decls layouts srcTy) = some size)
    (h_enc : encodeByteCastSourceBytes layouts (resolveTyWithLocalDecls decls layouts srcTy) v =
      some bs)
    (h_len : Trusted.Sequence.length bs = size) :
    evalByteCast locals op dstTy mem decls layouts policy =
      match decodeTypedValueFromBytes defaultCodecFuel layouts
          (resolveTyWithLocalDecls decls layouts dstTy) bs policy with
      | .some v' => .ok v' locals' mem
      | .none => .ub := by
  have h_len_beq : Nat.beq (Trusted.Sequence.length bs) size = true := by
    rw [h_len]; exact Nat.beq_refl _
  rw [fa_evalByteCast_eq locals locals' op mem decls layouts v srcTy dstTy size size policy h_op h_dst_sz h_ty h_src_sz, Nat.beq_refl, h_enc]
  dsimp only
  rw [h_len_beq]
/-- **Choice-free polymorphic MiniRust pointer-provenance `transmuteM` laws** across BOTH
`BasicMemory` and `TreeBorrowsMemory`, for every `addr < 2 ^ 64` and every provenance `prov`. -/
theorem fa_mrM_transmute_ptr_strip {M : Type} [Gen.Memory M] [MemoryOps M]
    (s : Signedness) (addr : Nat) (haddr : addr < 2 ^ 64) (prov : Option (Gen.Memory.Provenance M)) (m : Option (Gen.Machine M)) :
    transmuteM (M := M) (.Ptr ⟨⟨(addr : Int), prov⟩, none⟩) (.Ptr (.Raw .None))
        (.Int ⟨s, ⟨8⟩⟩) m = .ok (.Int (intFromBits addr ⟨s, ⟨8⟩⟩)) ∧
    transmuteM (M := M) (.Ptr ⟨⟨(addr : Int), prov⟩, none⟩) (.Ptr (.Raw .None))
        (.Array (.Int fcU8It) 8) m = .ok (.Tuple (fcLeByteValsMRM addr 8)) ∧
    transmuteM (M := M) (.Ptr ⟨⟨(addr : Int), prov⟩, none⟩) (.Ptr (.Raw .None))
        (.Ptr (.Raw .None)) m = .ok (.Ptr ⟨⟨(addr : Int), prov⟩, none⟩) ∧
    transmuteM (M := M) (.Int (addr : Int)) (.Int fcU64It)
        (.Ptr (.Raw .None)) m = .ok (.Ptr ⟨⟨(addr : Int), none⟩, none⟩) := by
  have hbits' : addr < 2 ^ (8 * 8) := haddr
  have hlayR : Type.layout (.Ptr (.Raw .None)) = .ok (.Sized ⟨8⟩ ⟨8⟩) := rfl
  have hlayA : Type.layout (.Array (.Int fcU8It) 8) = .ok (.Sized ⟨8⟩ ⟨1⟩) := rfl
  have hrepS := fc_canRepresent_intFromBits ⟨s, ⟨8⟩⟩ addr fc_goodSize_8 hbits'
  have hchkS : checkValueM (M := M) (.Int (intFromBits addr ⟨s, ⟨8⟩⟩)) (.Int ⟨s, ⟨8⟩⟩) m =
      .ok () := by
    simp only [checkValueM, ensureElseUb, hrepS, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
  have hchkA : checkValueM (M := M) (.Tuple (fcLeByteValsMRM addr 8))
      (.Array (.Int fcU8It) 8) m = .ok () := by
    dsimp only [fcLeByteValsMRM, checkValueM, ensureElseUb, List.length, List.forM, bind, Except.bind, pure, Except.pure]
    simp only [IntType.can_represent, fcU8It, fc_u8_inBounds_mod, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rfl
  exact ⟨
    fa_transmuteM_of_steps _ _ _ _ _ _ _ _ m hlayR (layout_eq ⟨s, ⟨8⟩⟩ fc_goodSize_8)
      (fa_encodeM_rawPtrNone (M := M) addr haddr prov)
      (fa_decodeIntM_encodePtrBytesM (M := M) s addr haddr prov) hchkS,
    fa_transmuteM_of_steps _ _ _ _ _ _ _ _ m hlayR hlayA
      (fa_encodeM_rawPtrNone (M := M) addr haddr prov)
      (fa_decodeArray8_encodePtrBytesM (M := M) prov addr) hchkA,
    fa_transmuteM_of_steps _ _ _ _ _ _ _ _ m hlayR hlayR
      (fa_encodeM_rawPtrNone (M := M) addr haddr prov)
      (fa_decodeM_rawPtrNone (M := M) addr haddr prov)
      (fa_checkValueM_rawPtrNone (M := M) addr haddr prov m),
    fa_transmuteM_of_steps _ _ _ _ _ _ _ _ m (layout_eq fcU64It fc_goodSize_8) hlayR
      (fa_encodeIntM_u64_cf (M := M) addr haddr)
      (fa_decodeM_rawPtrNone (M := M) addr haddr none)
      (fa_checkValueM_rawPtrNone (M := M) addr haddr none m)⟩
private theorem fa_decodeArrayChunks_u8_encode (allocId tag : Nat) :
    ∀ (n bits : Nat),
      decodeArrayChunksWith
        (fun chunk => decodeTypedValueFromBytes 15 faPolicyLayouts
          { kind := .uint .u8, layoutIdx := 0 } chunk .stripProvenance)
        1 n (encodeLittleEndianBytes bits n (some (allocId, tag))) =
        some (fcLeByteVals bits n)
  | 0, _ => rfl
  | n + 1, bits => by
    have hble : Nat.ble 1 (Trusted.Sequence.length
        (encodeLittleEndianBytes bits (n + 1) (some (allocId, tag)))) = true := by
      rw [fc_seqLength_encodeLittleEndianBytes]; rfl
    have hbyte : decodeTypedValueFromBytes 15 faPolicyLayouts
        { kind := .uint .u8, layoutIdx := 0 }
        [.init (UInt8.ofNat bits) (some (allocId, tag))] .stripProvenance =
        some (Value.scalar ⟨bits % 256, 1⟩) := by
      change some (Value.scalar ⟨(UInt8.ofNat bits).toBitVec.toNat, 1⟩) = _
      rw [fc_uint8_ofNat_toNat]
    unfold decodeArrayChunksWith
    rw [hble]
    dsimp only [encodeLittleEndianBytes, takeAbstractBytes, dropAbstractBytes]
    rw [hbyte, fa_decodeArrayChunks_u8_encode allocId tag n (Nat.div bits 256)]
    rfl
/-- **Decoder-level `ucg#630` vs. `reference#1752` flip on pointer bytes**: on `faPolicyLayouts`,
decoding 8 provenance-carrying bytes `encodeLittleEndianBytes addr 8 (some (allocId, tag))`
at `usize`, `u64`, `i64`, `f64`, or `[u8; 8]` returns `.none` under `.strictUcg630Ub` and
decodes the exact address bits (or byte array) under `.stripProvenance`. -/
theorem fa_decodeTyped_ptr_bytes_policy_flip (addr allocId tag : Nat) (haddr : addr < 2 ^ 64) :
    let bs := encodeLittleEndianBytes addr 8 (some (allocId, tag))
    -- .strictUcg630Ub rejects all 5 non-pointer targets
    decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolUsizeTy bs .strictUcg630Ub = none ∧
    decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolU64Ty bs .strictUcg630Ub = none ∧
    decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolI64Ty bs .strictUcg630Ub = none ∧
    decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolF64Ty bs .strictUcg630Ub = none ∧
    decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolBytes8Ty bs .strictUcg630Ub = none ∧
    -- .stripProvenance decodes all 5 targets to the exact provenance-less address bits
    decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolUsizeTy bs .stripProvenance =
      some (.scalar ⟨addr, 8⟩) ∧
    decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolU64Ty bs .stripProvenance =
      some (.scalar ⟨addr, 8⟩) ∧
    decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolI64Ty bs .stripProvenance =
      some (.scalar ⟨addr, 8⟩) ∧
    decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolF64Ty bs .stripProvenance =
      some (.scalar ⟨addr, 8⟩) ∧
    decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolBytes8Ty bs .stripProvenance =
      some (.aggregate 0 (fcLeByteVals addr 8)) := by
  dsimp only
  have h256 : addr < 256 ^ (7 + 1) := fc_lt_256_pow_8 haddr
  have hdecU := fc_decodeScalarBytes_encode (some (allocId, tag)) false 7 addr h256
  have hdecS := fc_decodeScalarBytes_encode (some (allocId, tag)) true 7 addr h256
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · change (match decodeScalarBytes (encodeLittleEndianBytes addr 8 (some (allocId, tag))) false with
      | some (sv, _) => some (Value.scalar sv) | none => none) = _
    rw [hdecU]
  · change (match decodeScalarBytes (encodeLittleEndianBytes addr 8 (some (allocId, tag))) false with
      | some (sv, _) => some (Value.scalar sv) | none => none) = _
    rw [hdecU]
  · change (match decodeScalarBytes (encodeLittleEndianBytes addr 8 (some (allocId, tag))) true with
      | some (sv, _) => some (Value.scalar sv) | none => none) = _
    rw [hdecS]
  · change (match decodeScalarBytes (encodeLittleEndianBytes addr 8 (some (allocId, tag))) false with
      | some (sv, _) => some (Value.scalar sv) | none => none) = _
    rw [hdecU]
  · change
      (match decodeArrayChunksWith
          (fun chunk => decodeTypedValueFromBytes 15 faPolicyLayouts
            { kind := .uint .u8, layoutIdx := 0 } chunk .stripProvenance)
          1 8 (encodeLittleEndianBytes addr 8 (some (allocId, tag))) with
       | some elems => some (Value.aggregate 0 elems)
       | none => none) = some (Value.aggregate 0 (fcLeByteVals addr 8))
    rw [fa_decodeArrayChunks_u8_encode allocId tag 8 addr]
/-- **Headline Episode 2 Theorem — `Ptr2IntTransmutePolicy.stripProvenance` Restores Exact
Agreement With MiniRust (`ucg#630` vs. `reference#1752`)**: for every `p : ProvenancePtr`
(`p.offsetBytes < 2^64`), mode, and memory model (`BM` / `TBM`, choice-free), `.strictUcg630Ub`
returns `.ub` on `*const u8 → {usize, u64, i64, f64, [u8; 8]}`, while `.stripProvenance` restores
exact agreement with MiniRust's `transmuteM` and `Type.decode`. -/
theorem fa_ptr2int_policy_flip_scalar_correspondence
    {locals locals' : List LocalSlot} {op : Operand} {mem : Memory} {decls : List LocalDecl} {p : ProvenancePtr} (hp : p.offsetBytes < 2 ^ 64)
    (hOp : evalOperand locals op mem.borrows mem.globals faPolicyLayouts mem.callerLocals decls
      mem.callStack = .ok (.ptr p 8) locals')
    (hTy : operandTy decls faPolicyLayouts op = some faPolPtrTy) (provBM : Option (Gen.Memory.Provenance BM)) (provTB : Option (Gen.Memory.Provenance TBM)) :
    -- (1) Strict ucg#630: Anneal returns .ub on all 5 non-pointer targets (and EvalRvalueFloatRel)
    evalByteCast locals op faPolUsizeTy mem decls faPolicyLayouts .strictUcg630Ub = .ub ∧
    evalByteCast locals op faPolU64Ty mem decls faPolicyLayouts .strictUcg630Ub = .ub ∧
    evalByteCast locals op faPolI64Ty mem decls faPolicyLayouts .strictUcg630Ub = .ub ∧
    evalByteCast locals op faPolF64Ty mem decls faPolicyLayouts .strictUcg630Ub = .ub ∧
    evalByteCast locals op faPolBytes8Ty mem decls faPolicyLayouts .strictUcg630Ub = .ub ∧
    -- (2) reference#1752 (.stripProvenance): Anneal restores exact agreement across all 5 targets
    evalByteCast locals op faPolUsizeTy mem decls faPolicyLayouts .stripProvenance =
      .ok (.scalar ⟨p.offsetBytes, 8⟩) locals' mem ∧
    evalByteCast locals op faPolU64Ty mem decls faPolicyLayouts .stripProvenance =
      .ok (.scalar ⟨p.offsetBytes, 8⟩) locals' mem ∧
    evalByteCast locals op faPolI64Ty mem decls faPolicyLayouts .stripProvenance =
      .ok (.scalar ⟨p.offsetBytes, 8⟩) locals' mem ∧
    evalByteCast locals op faPolF64Ty mem decls faPolicyLayouts .stripProvenance =
      .ok (.scalar ⟨p.offsetBytes, 8⟩) locals' mem ∧
    evalByteCast locals op faPolBytes8Ty mem decls faPolicyLayouts .stripProvenance =
      .ok (.aggregate 0 (fcLeByteVals p.offsetBytes 8)) locals' mem ∧
    -- (3) EvalRvalueFloatRel mode-independent policy flip (both .deterministic and .nondeterministic)
    (∀ mode,
      EvalRvalueFloatRel mode .strictUcg630Ub locals (.cast .transmute op faPolUsizeTy) mem decls
        faPolicyLayouts .ub ∧
      EvalRvalueFloatRel mode .stripProvenance locals (.cast .transmute op faPolUsizeTy) mem decls
        faPolicyLayouts (.ok (.scalar ⟨p.offsetBytes, 8⟩) locals' mem) ∧
      EvalRvalueFloatRel mode .strictUcg630Ub locals (.cast .transmute op faPolF64Ty) mem decls
        faPolicyLayouts .ub ∧
      EvalRvalueFloatRel mode .stripProvenance locals (.cast .transmute op faPolF64Ty) mem decls
        faPolicyLayouts (.ok (.scalar ⟨p.offsetBytes, 8⟩) locals' mem)) ∧
    -- (4) Exact MiniRust lockstep across BasicMemory (BM) and TreeBorrowsMemory (TBM)
    (∀ s : Signedness,
      transmuteM (M := BM) (.Ptr ⟨⟨(p.offsetBytes : Int), provBM⟩, none⟩) (.Ptr (.Raw .None))
          (.Int ⟨s, ⟨8⟩⟩) = .ok (.Int (intFromBits p.offsetBytes ⟨s, ⟨8⟩⟩)) ∧
      transmuteM (M := TBM) (.Ptr ⟨⟨(p.offsetBytes : Int), provTB⟩, none⟩) (.Ptr (.Raw .None))
          (.Int ⟨s, ⟨8⟩⟩) = .ok (.Int (intFromBits p.offsetBytes ⟨s, ⟨8⟩⟩)) ∧
      Type.decode (.Int ⟨s, ⟨8⟩⟩)
          ((encodeLittleEndianBytes p.offsetBytes 8 none).map fcByteToMR) =
        .ok (some (.Int (intFromBits p.offsetBytes ⟨s, ⟨8⟩⟩)))) ∧
    transmuteM (M := BM) (.Ptr ⟨⟨(p.offsetBytes : Int), provBM⟩, none⟩) (.Ptr (.Raw .None))
        (.Array (.Int fcU8It) 8) = .ok (.Tuple (fcLeByteValsMRM p.offsetBytes 8)) ∧
    transmuteM (M := TBM) (.Ptr ⟨⟨(p.offsetBytes : Int), provTB⟩, none⟩) (.Ptr (.Raw .None))
        (.Array (.Int fcU8It) 8) = .ok (.Tuple (fcLeByteValsMRM p.offsetBytes 8)) := by
  have hEnc : encodeByteCastSourceBytes faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolPtrTy) (.ptr p 8) =
      some (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) := rfl
  have hLen := fc_seqLength_encodeLittleEndianBytes (some (p.allocId, p.tag)) 8 p.offsetBytes
  have hSzPtr : tyByteSize decls faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolPtrTy) = some 8 := rfl
  have hSzUsize : tyByteSize decls faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolUsizeTy) = some 8 := rfl
  have hSzU64 : tyByteSize decls faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolU64Ty) = some 8 := rfl
  have hSzI64 : tyByteSize decls faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolI64Ty) = some 8 := rfl
  have hSzF64 : tyByteSize decls faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolF64Ty) = some 8 := rfl
  have hSzB8 : tyByteSize decls faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolBytes8Ty) = some 8 := rfl
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hp1, hp2, hp3, hp4, hp5⟩ :=
    fa_decodeTyped_ptr_bytes_policy_flip p.offsetBytes p.allocId p.tag hp
  have hResUsize : resolveTyWithLocalDecls decls faPolicyLayouts faPolUsizeTy = faPolUsizeTy := rfl
  have hResU64 : resolveTyWithLocalDecls decls faPolicyLayouts faPolU64Ty = faPolU64Ty := rfl
  have hResI64 : resolveTyWithLocalDecls decls faPolicyLayouts faPolI64Ty = faPolI64Ty := rfl
  have hResF64 : resolveTyWithLocalDecls decls faPolicyLayouts faPolF64Ty = faPolF64Ty := rfl
  have hResB8 : resolveTyWithLocalDecls decls faPolicyLayouts faPolBytes8Ty = faPolBytes8Ty := rfl
  have hUS : evalByteCast locals op faPolUsizeTy mem decls faPolicyLayouts .strictUcg630Ub = .ub := by
    rw [fa_evalByteCast_of_encode locals locals' op mem decls faPolicyLayouts _ _ _ 8 _ _ hOp hSzUsize hTy hSzPtr hEnc hLen, hResUsize, hs1]
  have hU64S : evalByteCast locals op faPolU64Ty mem decls faPolicyLayouts .strictUcg630Ub = .ub := by
    rw [fa_evalByteCast_of_encode locals locals' op mem decls faPolicyLayouts _ _ _ 8 _ _ hOp hSzU64 hTy hSzPtr hEnc hLen, hResU64, hs2]
  have hI64S : evalByteCast locals op faPolI64Ty mem decls faPolicyLayouts .strictUcg630Ub = .ub := by
    rw [fa_evalByteCast_of_encode locals locals' op mem decls faPolicyLayouts _ _ _ 8 _ _ hOp hSzI64 hTy hSzPtr hEnc hLen, hResI64, hs3]
  have hF64S : evalByteCast locals op faPolF64Ty mem decls faPolicyLayouts .strictUcg630Ub = .ub := by
    rw [fa_evalByteCast_of_encode locals locals' op mem decls faPolicyLayouts _ _ _ 8 _ _ hOp hSzF64 hTy hSzPtr hEnc hLen, hResF64, hs4]
  have hB8S : evalByteCast locals op faPolBytes8Ty mem decls faPolicyLayouts .strictUcg630Ub = .ub := by
    rw [fa_evalByteCast_of_encode locals locals' op mem decls faPolicyLayouts _ _ _ 8 _ _ hOp hSzB8 hTy hSzPtr hEnc hLen, hResB8, hs5]
  have hUP : evalByteCast locals op faPolUsizeTy mem decls faPolicyLayouts .stripProvenance =
      .ok (.scalar ⟨p.offsetBytes, 8⟩) locals' mem := by
    rw [fa_evalByteCast_of_encode locals locals' op mem decls faPolicyLayouts _ _ _ 8 _ _ hOp hSzUsize hTy hSzPtr hEnc hLen, hResUsize, hp1]
  have hU64P : evalByteCast locals op faPolU64Ty mem decls faPolicyLayouts .stripProvenance =
      .ok (.scalar ⟨p.offsetBytes, 8⟩) locals' mem := by
    rw [fa_evalByteCast_of_encode locals locals' op mem decls faPolicyLayouts _ _ _ 8 _ _ hOp hSzU64 hTy hSzPtr hEnc hLen, hResU64, hp2]
  have hI64P : evalByteCast locals op faPolI64Ty mem decls faPolicyLayouts .stripProvenance =
      .ok (.scalar ⟨p.offsetBytes, 8⟩) locals' mem := by
    rw [fa_evalByteCast_of_encode locals locals' op mem decls faPolicyLayouts _ _ _ 8 _ _ hOp hSzI64 hTy hSzPtr hEnc hLen, hResI64, hp3]
  have hF64P : evalByteCast locals op faPolF64Ty mem decls faPolicyLayouts .stripProvenance =
      .ok (.scalar ⟨p.offsetBytes, 8⟩) locals' mem := by
    rw [fa_evalByteCast_of_encode locals locals' op mem decls faPolicyLayouts _ _ _ 8 _ _ hOp hSzF64 hTy hSzPtr hEnc hLen, hResF64, hp4]
  have hB8P : evalByteCast locals op faPolBytes8Ty mem decls faPolicyLayouts .stripProvenance =
      .ok (.aggregate 0 (fcLeByteVals p.offsetBytes 8)) locals' mem := by
    rw [fa_evalByteCast_of_encode locals locals' op mem decls faPolicyLayouts _ _ _ 8 _ _ hOp hSzB8 hTy hSzPtr hEnc hLen, hResB8, hp5]
  refine ⟨hUS, hU64S, hI64S, hF64S, hB8S, hUP, hU64P, hI64P, hF64P, hB8P, ?_, ?_,
    (fa_mrM_transmute_ptr_strip (M := BM) .Unsigned p.offsetBytes hp provBM none).2.1,
    (fa_mrM_transmute_ptr_strip (M := TBM) .Unsigned p.offsetBytes hp provTB none).2.1⟩
  · intro mode
    exact ⟨
      (EvalRvalueFloatRel_byteCast_iff mode .strictUcg630Ub locals .transmute op faPolUsizeTy mem
        decls faPolicyLayouts .ub (.inl rfl)).mpr hUS.symm,
      (EvalRvalueFloatRel_byteCast_iff mode .stripProvenance locals .transmute op faPolUsizeTy mem
        decls faPolicyLayouts _ (.inl rfl)).mpr hUP.symm,
      (EvalRvalueFloatRel_byteCast_iff mode .strictUcg630Ub locals .transmute op faPolF64Ty mem
        decls faPolicyLayouts .ub (.inl rfl)).mpr hF64S.symm,
      (EvalRvalueFloatRel_byteCast_iff mode .stripProvenance locals .transmute op faPolF64Ty mem
        decls faPolicyLayouts _ (.inl rfl)).mpr hF64P.symm⟩
  · intro s
    exact ⟨(fa_mrM_transmute_ptr_strip (M := BM) s p.offsetBytes hp provBM none).1,
      (fa_mrM_transmute_ptr_strip (M := TBM) s p.offsetBytes hp provTB none).1,
      fc_mr_decode_eq_anneal s 8 p.offsetBytes none hp⟩
/-! ### §3.1 Selective per-field composite tuple / struct correspondence (`BM` & `TBM`) -/
private theorem fa_write_and_subslice_two_8 {α : Type} (u : α) (xs ys : List α)
    (hx : xs.length = 8) (hy : ys.length = 8) :
    writeSubsliceAtIndex (List.replicate 16 u) ((0 : Nat) : Int) xs =
      .ok (xs ++ List.replicate 8 u) ∧
    writeSubsliceAtIndex (xs ++ List.replicate 8 u) ((8 : Nat) : Int) ys = .ok (xs ++ ys) ∧
    subsliceWithLength (xs ++ ys) ((0 : Nat) : Int) ((8 : Nat) : Int) = .ok xs ∧
    subsliceWithLength (xs ++ ys) ((8 : Nat) : Int) ((8 : Nat) : Int) = .ok ys := by
  have h1 : writeSubsliceAtIndex (List.replicate 16 u) (0 : Int) xs =
      .ok (xs ++ List.replicate 8 u) := by
    unfold writeSubsliceAtIndex
    have hc : (0 : Int) ≤ 0 ∧ (0 : Int) + xs.length ≤ (List.replicate 16 u).length := by
      simp [hx]
    simp only [hc]
    simp only [Int.toNat_zero, List.take_zero, List.nil_append, Nat.zero_add, hx, List.drop_replicate, pure, Except.pure]
    rfl
  have hlen1 : (xs ++ List.replicate 8 u).length = 16 := by simp [hx]
  have h2 : writeSubsliceAtIndex (xs ++ List.replicate 8 u) (8 : Int) ys = .ok (xs ++ ys) := by
    unfold writeSubsliceAtIndex
    have hc : (0 : Int) ≤ 8 ∧ (8 : Int) + ys.length ≤ (xs ++ List.replicate 8 u).length := by
      rw [hy, hlen1]; decide
    simp only [hc, pure, Except.pure]
    change Except.ok ((xs ++ List.replicate 8 u).take 8 ++ ys ++
      (xs ++ List.replicate 8 u).drop (8 + ys.length)) = .ok (xs ++ ys)
    have ht : (xs ++ List.replicate 8 u).take 8 = xs := by
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    have hd : (xs ++ List.replicate 8 u).drop (8 + ys.length) = [] := by
      rw [List.drop_eq_nil_iff, hlen1, hy]; exact Nat.le_refl 16
    rw [ht, hd, List.append_nil]
  have hlen16 : (xs ++ ys).length = 16 := by simp [hx, hy]
  have hs1 : subsliceWithLength (xs ++ ys) (0 : Int) (8 : Int) = .ok xs := by
    unfold subsliceWithLength
    have hc : (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 8 ∧ (0 : Int) + 8 ≤ (xs ++ ys).length := by
      rw [hlen16]; decide
    simp only [hc, pure, Except.pure]
    change Except.ok (((xs ++ ys).drop 0).take 8) = .ok xs
    rw [List.drop_zero, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have hs2 : subsliceWithLength (xs ++ ys) (8 : Int) (8 : Int) = .ok ys := by
    unfold subsliceWithLength
    have hc : (0 : Int) ≤ 8 ∧ (0 : Int) ≤ 8 ∧ (8 : Int) + 8 ≤ (xs ++ ys).length := by
      rw [hlen16]; decide
    simp only [hc, pure, Except.pure]
    change Except.ok (((xs ++ ys).drop 8).take 8) = .ok ys
    rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append, List.take_of_length_le (by omega)]
  exact ⟨h1, h2, hs1, hs2⟩
private theorem fa_encodeM_tuple2 {M : Type} [Gen.Memory M]
    (ty0 ty1 : Gen.Type) (v0 v1 : Gen.Value M) (bs0 bs1 mid res : List (Gen.AbstractByte (Gen.Memory.Provenance M))) (he0 : Type.encodeM (M := M) ty0 v0 = .ok bs0)
    (he1 : Type.encodeM (M := M) ty1 v1 = .ok bs1) (hw1 : writeSubsliceAtIndex (List.replicate 16 Gen.AbstractByte.Uninit) ((0 : Nat) : Int) bs0 =
      .ok mid)
    (hw2 : writeSubsliceAtIndex mid ((8 : Nat) : Int) bs1 = .ok res) :
    Type.encodeM (M := M)
        (.Tuple [(⟨0⟩, ty0), (⟨8⟩, ty1)]
          { «end» := ⟨16⟩, align := ⟨8⟩, packed_align := none } none)
        (.Tuple [v0, v1]) = .ok res := by
  have h16 : TupleHeadLayout.head_size_and_align
      { «end» := ⟨16⟩, align := ⟨8⟩, packed_align := none } = (⟨16⟩, ⟨8⟩) := rfl
  unfold Type.encodeM
  rw [h16]
  simp only [List.length_cons, List.length_nil, ne_eq, not_true_eq_false, ↓reduceIte]
  unfold Type.encodeFieldsM
  simp only [bind, Except.bind, he0, hw1]
  unfold Type.encodeFieldsM
  simp only [bind, Except.bind, he1, hw2]
  rfl
private theorem fa_decodeM_tuple2 {M : Type} [Gen.Memory M] [MemoryOps M]
    (ty0 ty1 : Gen.Type) (a0 a1 : LibSpecr.Align) (v0 v1 : Gen.Value M) (bs bs0 bs1 : List (Gen.AbstractByte (Gen.Memory.Provenance M))) (hlen : bs.length = 16)
    (hl0 : Type.layout ty0 = .ok (.Sized ⟨8⟩ a0)) (hl1 : Type.layout ty1 = .ok (.Sized ⟨8⟩ a1))
    (hs0 : subsliceWithLength bs ((0 : Nat) : Int) ((8 : Nat) : Int) = .ok bs0) (hs1 : subsliceWithLength bs ((8 : Nat) : Int) ((8 : Nat) : Int) = .ok bs1)
    (hd0 : Type.decodeM (M := M) ty0 bs0 = .ok (some v0)) (hd1 : Type.decodeM (M := M) ty1 bs1 = .ok (some v1)) :
    Type.decodeM (M := M)
        (.Tuple [(⟨0⟩, ty0), (⟨8⟩, ty1)]
          { «end» := ⟨16⟩, align := ⟨8⟩, packed_align := none } none) bs =
      .ok (some (.Tuple [v0, v1])) := by
  have h16 : TupleHeadLayout.head_size_and_align
      { «end» := ⟨16⟩, align := ⟨8⟩, packed_align := none } = (⟨16⟩, ⟨8⟩) := rfl
  unfold Type.decodeM
  rw [h16]
  simp only [hlen, ne_eq, not_true_eq_false, ↓reduceIte]
  have hdf : Type.decodeFieldsM (M := M) [(⟨0⟩, ty0), (⟨8⟩, ty1)] bs = .ok (some [v0, v1]) := by
    unfold Type.decodeFieldsM
    simp only [bind, Except.bind, hl0, expect_size_sized, hs0, hd0]
    unfold Type.decodeFieldsM
    simp only [bind, Except.bind, hl1, expect_size_sized, hs1, hd1]
    rfl
  simp only [bind, Except.bind, hdf, pure, Except.pure]
private theorem fa_checkValueM_tuple2 {M : Type} [Gen.Memory M] [MemoryOps M]
    (ty0 ty1 : Gen.Type) (v0 v1 : Gen.Value M) (m : Option (Gen.Machine M)) (hc0 : checkValueM (M := M) v0 ty0 m = .ok ())
    (hc1 : checkValueM (M := M) v1 ty1 m = .ok ()) :
    checkValueM (M := M) (.Tuple [v0, v1])
        (.Tuple [(⟨0⟩, ty0), (⟨8⟩, ty1)]
          { «end» := ⟨16⟩, align := ⟨8⟩, packed_align := none } none) m = .ok () := by
  unfold checkValueM
  dsimp only [ensureElseUb, List.length_cons, List.length_nil, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
  unfold checkFieldsM
  simp only [bind, Except.bind, hc0]
  unfold checkFieldsM
  simp only [bind, Except.bind, hc1]
  rfl
/-- **Polymorphic MiniRust per-field `Type.Tuple` transmutation** (choice-free, across BOTH
`BasicMemory` and `TreeBorrowsMemory`): transmuting `(*const u8, *const u8)` to
`(*const u8, usize)` preserves field 0's provenance `provA` while stripping field 1's provenance
`provB`, and transmuting to `(u64, u64)` strips both. -/
theorem fa_mrM_transmute_ptr_tuple_selective {M : Type} [Gen.Memory M] [MemoryOps M]
    (addrA addrB : Nat) (hA : addrA < 2 ^ 64) (hB : addrB < 2 ^ 64) (provA provB : Option (Gen.Memory.Provenance M)) (m : Option (Gen.Machine M)) :
    transmuteM (M := M)
        (.Tuple [.Ptr ⟨⟨(addrA : Int), provA⟩, none⟩, .Ptr ⟨⟨(addrB : Int), provB⟩, none⟩])
        faMrPtrPtrTupleTy faMrPtrU64TupleTy m =
      .ok (.Tuple [.Ptr ⟨⟨(addrA : Int), provA⟩, none⟩, .Int (addrB : Int)]) ∧
    transmuteM (M := M)
        (.Tuple [.Ptr ⟨⟨(addrA : Int), provA⟩, none⟩, .Ptr ⟨⟨(addrB : Int), provB⟩, none⟩])
        faMrPtrPtrTupleTy faMrU64U64TupleTy m =
      .ok (.Tuple [.Int (addrA : Int), .Int (addrB : Int)]) := by
  let xs := encodePtrBytesM (M := M) provA 0 (leBytes addrA 8)
  let ys := encodePtrBytesM (M := M) provB 0 (leBytes addrB 8)
  have hxs : xs.length = 8 := by simp [xs, fa_encodePtrBytesM_len, leBytes_length]
  have hys : ys.length = 8 := by simp [ys, fa_encodePtrBytesM_len, leBytes_length]
  have hlen16 : (xs ++ ys).length = 16 := by simp [hxs, hys]
  obtain ⟨hw1, hw2, hs0, hs1⟩ := fa_write_and_subslice_two_8
    (Gen.AbstractByte.Uninit : Gen.AbstractByte (Gen.Memory.Provenance M)) xs ys hxs hys
  have hlayPP : Type.layout faMrPtrPtrTupleTy = .ok (.Sized ⟨16⟩ ⟨8⟩) := rfl
  have hlayPU : Type.layout faMrPtrU64TupleTy = .ok (.Sized ⟨16⟩ ⟨8⟩) := rfl
  have hlayUU : Type.layout faMrU64U64TupleTy = .ok (.Sized ⟨16⟩ ⟨8⟩) := rfl
  have hlayPtr : Type.layout (.Ptr (.Raw .None)) = .ok (.Sized ⟨8⟩ ⟨8⟩) := rfl
  have hlayU64 := layout_eq fcU64It fc_goodSize_8
  have hencPP : Type.encodeM (M := M) faMrPtrPtrTupleTy
      (.Tuple [.Ptr ⟨⟨(addrA : Int), provA⟩, none⟩, .Ptr ⟨⟨(addrB : Int), provB⟩, none⟩]) =
      .ok (xs ++ ys) :=
    fa_encodeM_tuple2 (M := M) (.Ptr (.Raw .None)) (.Ptr (.Raw .None)) _ _ xs ys _ (xs ++ ys)
      (fa_encodeM_rawPtrNone (M := M) addrA hA provA)
      (fa_encodeM_rawPtrNone (M := M) addrB hB provB) hw1 hw2
  have hdecIntA : Type.decodeM (M := M) (.Int fcU64It) xs = .ok (some (.Int (addrA : Int))) :=
    fa_decodeIntM_encodePtrBytesM (M := M) .Unsigned addrA hA provA
  have hdecIntB : Type.decodeM (M := M) (.Int fcU64It) ys = .ok (some (.Int (addrB : Int))) :=
    fa_decodeIntM_encodePtrBytesM (M := M) .Unsigned addrB hB provB
  have hdecPU : Type.decodeM (M := M) faMrPtrU64TupleTy (xs ++ ys) =
      .ok (some (.Tuple [.Ptr ⟨⟨(addrA : Int), provA⟩, none⟩, .Int (addrB : Int)])) :=
    fa_decodeM_tuple2 (M := M) (.Ptr (.Raw .None)) (.Int fcU64It) _ _ _ _ (xs ++ ys) xs ys
      hlen16 hlayPtr hlayU64 hs0 hs1 (fa_decodeM_rawPtrNone (M := M) addrA hA provA) hdecIntB
  have hdecUU : Type.decodeM (M := M) faMrU64U64TupleTy (xs ++ ys) =
      .ok (some (.Tuple [.Int (addrA : Int), .Int (addrB : Int)])) :=
    fa_decodeM_tuple2 (M := M) (.Int fcU64It) (.Int fcU64It) _ _ _ _ (xs ++ ys) xs ys
      hlen16 hlayU64 hlayU64 hs0 hs1 hdecIntA hdecIntB
  have hchkA : checkValueM (M := M) (.Int (addrA : Int)) (.Int fcU64It) m = .ok () := by
    simp only [checkValueM, ensureElseUb, IntType.can_represent, fcU64It, fa_inBounds_u64 addrA hA, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
  have hchkB : checkValueM (M := M) (.Int (addrB : Int)) (.Int fcU64It) m = .ok () := by
    simp only [checkValueM, ensureElseUb, IntType.can_represent, fcU64It, fa_inBounds_u64 addrB hB, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
  have hchkPU : checkValueM (M := M)
      (.Tuple [.Ptr ⟨⟨(addrA : Int), provA⟩, none⟩, .Int (addrB : Int)]) faMrPtrU64TupleTy m =
      .ok () :=
    fa_checkValueM_tuple2 (M := M) (.Ptr (.Raw .None)) (.Int fcU64It) _ _ m
      (fa_checkValueM_rawPtrNone (M := M) addrA hA provA m) hchkB
  have hchkUU : checkValueM (M := M)
      (.Tuple [.Int (addrA : Int), .Int (addrB : Int)]) faMrU64U64TupleTy m = .ok () :=
    fa_checkValueM_tuple2 (M := M) (.Int fcU64It) (.Int fcU64It) _ _ m hchkA hchkB
  exact ⟨
    fa_transmuteM_of_steps _ _ _ _ _ _ _ _ m hlayPP hlayPU hencPP hdecPU hchkPU,
    fa_transmuteM_of_steps _ _ _ _ _ _ _ _ m hlayPP hlayUU hencPP hdecUU hchkUU⟩
private theorem fa_seqLen_append : ∀ (xs ys : List MirSemantics.AbstractByte),
    Trusted.Sequence.length (appendAbstractBytes xs ys) =
      Trusted.Sequence.length xs + Trusted.Sequence.length ys
  | [], _ => (Nat.zero_add _).symm
  | _ :: xs, ys => by
    change Trusted.Sequence.length (appendAbstractBytes xs ys) + 1 =
      (Trusted.Sequence.length xs + 1) + Trusted.Sequence.length ys
    rw [fa_seqLen_append xs ys, Nat.add_right_comm]
private theorem fa_take_append : ∀ (xs ys : List MirSemantics.AbstractByte),
    takeAbstractBytes (Trusted.Sequence.length xs) (appendAbstractBytes xs ys) = xs
  | [], _ => rfl
  | x :: xs, ys => congrArg (x :: ·) (fa_take_append xs ys)
private theorem fa_drop_append : ∀ (xs ys : List MirSemantics.AbstractByte),
    dropAbstractBytes (Trusted.Sequence.length xs) (appendAbstractBytes xs ys) = ys
  | [], _ => rfl
  | _ :: xs, ys => fa_drop_append xs ys
private theorem fa_take_self : ∀ (xs : List MirSemantics.AbstractByte),
    takeAbstractBytes (Trusted.Sequence.length xs) xs = xs
  | [] => rfl
  | x :: xs => congrArg (x :: ·) (fa_take_self xs)
private theorem fa_slice_append_8 (xs ys : List MirSemantics.AbstractByte)
    (hx : Trusted.Sequence.length xs = 8) (hy : Trusted.Sequence.length ys = 8) :
    Trusted.Sequence.length (appendAbstractBytes xs ys) = 16 ∧
    sliceAbstractBytes (appendAbstractBytes xs ys) 0 8 = some xs ∧
    sliceAbstractBytes (appendAbstractBytes xs ys) 8 8 = some ys := by
  have h16 : Trusted.Sequence.length (appendAbstractBytes xs ys) = 16 := by rw [fa_seqLen_append, hx, hy]
  refine ⟨h16, ?_, ?_⟩
  · unfold sliceAbstractBytes; rw [h16]
    change some (takeAbstractBytes 8 (appendAbstractBytes xs ys)) = some xs
    rw [← hx, fa_take_append]
  · unfold sliceAbstractBytes; rw [h16]
    change some (takeAbstractBytes 8 (dropAbstractBytes 8 (appendAbstractBytes xs ys))) = some ys
    rw [← hx, fa_drop_append, hx, ← hy, fa_take_self]
private theorem fa_decodeTyped_ptrUsizeTup (xs ys : List MirSemantics.AbstractByte)
    (hx : Trusted.Sequence.length xs = 8) (hy : Trusted.Sequence.length ys = 8) (policy : Ptr2IntTransmutePolicy) :
    decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolPtrUsizeTupTy
        (appendAbstractBytes xs ys) policy =
      match decodePtrBytesNoForge false (.uint .u8) 8 xs with
      | none => none
      | some v0 =>
        match decodeTypedValueFromBytes 15 faPolicyLayouts
            { kind := .uint .usize, layoutIdx := 9 } ys policy with
        | none => none
        | some v1 => some (.aggregate 0 [v0, v1]) := by
  obtain ⟨h16, hs0, hs8⟩ := fa_slice_append_8 xs ys hx hy
  conv => lhs; unfold decodeTypedValueFromBytes
  rw [h16]
  have hk : decodeTypedKindsAndLayoutsAtOffsets
        (fun cTy bs => decodeTypedValueFromBytes 15 faPolicyLayouts cTy bs policy)
        faPolicyLayouts (appendAbstractBytes xs ys) [{ bytes := 0 }, { bytes := 8 }]
        [.rawPtr .not (.uint .u8), .uint .usize] [10, 9] =
      match decodePtrBytesNoForge false (.uint .u8) 8 xs with
      | none => none
      | some v0 =>
        match decodeTypedValueFromBytes 15 faPolicyLayouts
            { kind := .uint .usize, layoutIdx := 9 } ys policy with
        | none => none
        | some v1 => some [v0, v1] := by
    have hl10 : LayoutTable.lookup faPolicyLayouts 10 = some (fcPrimLayout 8 (.pointer 0)) := rfl
    have hl9 : LayoutTable.lookup faPolicyLayouts 9 = some (fcPrimLayout 8 (.int 64 false)) := rfl
    have hp0 : decodeTypedValueFromBytes 15 faPolicyLayouts
        { kind := .rawPtr .not (.uint .u8), layoutIdx := 10 } xs policy =
        decodePtrBytesNoForge false (.uint .u8) 8 xs := rfl
    unfold decodeTypedKindsAndLayoutsAtOffsets
    rw [hl10]; dsimp only [fcPrimLayout]; rw [hs0]; dsimp only; rw [hp0]
    cases decodePtrBytesNoForge false (.uint .u8) 8 xs with
    | none => rfl
    | some _ =>
      dsimp only; unfold decodeTypedKindsAndLayoutsAtOffsets
      rw [hl9]; dsimp only [fcPrimLayout]; rw [hs8]; dsimp only
      cases decodeTypedValueFromBytes 15 faPolicyLayouts
          { kind := .uint .usize, layoutIdx := 9 } ys policy <;> rfl
  change (match decodeTypedKindsAndLayoutsAtOffsets
      (fun cTy bs => decodeTypedValueFromBytes 15 faPolicyLayouts cTy bs policy)
      faPolicyLayouts (appendAbstractBytes xs ys) [{ bytes := 0 }, { bytes := 8 }]
      [.rawPtr .not (.uint .u8), .uint .usize] [10, 9] with
    | some vals => some (Value.aggregate 0 vals) | none => none) = _
  rw [hk]
  cases decodePtrBytesNoForge false (.uint .u8) 8 xs with
  | none => rfl
  | some _ =>
    cases decodeTypedValueFromBytes 15 faPolicyLayouts
        { kind := .uint .usize, layoutIdx := 9 } ys policy <;> rfl
private theorem fa_decodeTyped_mixedStruct (xs ys : List MirSemantics.AbstractByte)
    (hx : Trusted.Sequence.length xs = 8) (hy : Trusted.Sequence.length ys = 8) (policy : Ptr2IntTransmutePolicy) :
    decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolMixedStructTy
        (appendAbstractBytes xs ys) policy =
      match decodeScalarLayoutBytesNoForge
          (.initialized (.pointer 0) { start := 0, end_ := 2 ^ (8 * 8) - 1 }) xs policy with
      | none => none
      | some v0 =>
        match decodeScalarLayoutBytesNoForge
            (.initialized (.int 64 false) { start := 0, end_ := 2 ^ (8 * 8) - 1 }) ys policy with
        | none => none
        | some v1 => some (.aggregate 0 [v0, v1]) := by
  obtain ⟨h16, hs0, hs8⟩ := fa_slice_append_8 xs ys hx hy
  conv => lhs; unfold decodeTypedValueFromBytes
  rw [h16]
  have hf0 : decodeTypedValueFromBytes 15 faPolicyLayouts { kind := .adt "" .nil, layoutIdx := 10 }
      xs policy = decodeScalarLayoutBytesNoForge
        (.initialized (.pointer 0) { start := 0, end_ := 2 ^ (8 * 8) - 1 }) xs policy := by
    unfold decodeTypedValueFromBytes; rw [hx]; rfl
  have hf1 : decodeTypedValueFromBytes 15 faPolicyLayouts { kind := .adt "" .nil, layoutIdx := 9 }
      ys policy = decodeScalarLayoutBytesNoForge
        (.initialized (.int 64 false) { start := 0, end_ := 2 ^ (8 * 8) - 1 }) ys policy := by
    unfold decodeTypedValueFromBytes; rw [hy]; rfl
  have hk : decodeFieldsByLayoutIdxs
        (fun fIdx fSlice => decodeTypedValueFromBytes 15 faPolicyLayouts
          { kind := .adt "" .nil, layoutIdx := fIdx } fSlice policy)
        faPolicyLayouts (appendAbstractBytes xs ys) [{ bytes := 0 }, { bytes := 8 }] [10, 9] =
      match decodeScalarLayoutBytesNoForge
          (.initialized (.pointer 0) { start := 0, end_ := 2 ^ (8 * 8) - 1 }) xs policy with
      | none => none
      | some v0 =>
        match decodeScalarLayoutBytesNoForge
            (.initialized (.int 64 false) { start := 0, end_ := 2 ^ (8 * 8) - 1 }) ys policy with
        | none => none
        | some v1 => some [v0, v1] := by
    have hl10 : LayoutTable.lookup faPolicyLayouts 10 = some (fcPrimLayout 8 (.pointer 0)) := rfl
    have hl9 : LayoutTable.lookup faPolicyLayouts 9 = some (fcPrimLayout 8 (.int 64 false)) := rfl
    unfold decodeFieldsByLayoutIdxs
    rw [hl10]; dsimp only [fcPrimLayout]; rw [hs0]; dsimp only; rw [hf0]
    cases decodeScalarLayoutBytesNoForge
        (.initialized (.pointer 0) { start := 0, end_ := 2 ^ (8 * 8) - 1 }) xs policy with
    | none => rfl
    | some _ =>
      dsimp only; unfold decodeFieldsByLayoutIdxs
      rw [hl9]; dsimp only [fcPrimLayout]; rw [hs8]; dsimp only; rw [hf1]
      cases decodeScalarLayoutBytesNoForge
          (.initialized (.int 64 false) { start := 0, end_ := 2 ^ (8 * 8) - 1 }) ys policy <;> rfl
  change (match decodeFieldsByLayoutIdxs
      (fun fIdx fSlice => decodeTypedValueFromBytes 15 faPolicyLayouts
        { kind := .adt "" .nil, layoutIdx := fIdx } fSlice policy)
      faPolicyLayouts (appendAbstractBytes xs ys) [{ bytes := 0 }, { bytes := 8 }] [10, 9] with
    | some vals => some (Value.aggregate 0 vals) | none => none) = _
  rw [hk]
  cases decodeScalarLayoutBytesNoForge
      (.initialized (.pointer 0) { start := 0, end_ := 2 ^ (8 * 8) - 1 }) xs policy with
  | none => rfl
  | some _ =>
    cases decodeScalarLayoutBytesNoForge
        (.initialized (.int 64 false) { start := 0, end_ := 2 ^ (8 * 8) - 1 }) ys policy <;> rfl
/-- **Selective per-field composite tuple & struct policy correspondence (`(*const u8, *const u8)`
→ `(*const u8, usize)` and `struct Mixed`)**: `.strictUcg630Ub` faults `.ub`, while
`.stripProvenance` preserves field-0 pointer provenance and strips field-1 integer provenance,
matching MiniRust's `Type.Tuple` `transmuteM` across `BM` and `TBM`. -/
theorem fa_composite_tuple_struct_policy_correspondence
    {locals locals' : List LocalSlot} {op : Operand} {mem : Memory} {decls : List LocalDecl}
    {pA pB : ProvenancePtr} (hA : pA.offsetBytes < 2 ^ 64) (hB : pB.offsetBytes < 2 ^ 64)
    (hOp : evalOperand locals op mem.borrows mem.globals faPolicyLayouts mem.callerLocals decls
      mem.callStack = .ok (.aggregate 0 [.ptr pA 8, .ptr pB 8]) locals')
    (hTy : operandTy decls faPolicyLayouts op = some faPolPtrPtrTupTy) (provABM provBBM : Option (Gen.Memory.Provenance BM))
    (provATB provBTB : Option (Gen.Memory.Provenance TBM)) :
    let expectedVal : Value :=
      .aggregate 0 [.ptr { allocId := pA.allocId, offsetBytes := pA.offsetBytes } 8,
                    .scalar ⟨pB.offsetBytes, 8⟩]
    -- Tuple target: .strictUcg630Ub = .ub vs .stripProvenance = selective preserve+strip
    evalByteCast locals op faPolPtrUsizeTupTy mem decls faPolicyLayouts .strictUcg630Ub = .ub ∧
    evalByteCast locals op faPolPtrUsizeTupTy mem decls faPolicyLayouts .stripProvenance =
      .ok expectedVal locals' mem ∧
    -- Struct Mixed target: .strictUcg630Ub = .ub vs .stripProvenance = selective preserve+strip
    evalByteCast locals op faPolMixedStructTy mem decls faPolicyLayouts .strictUcg630Ub = .ub ∧
    evalByteCast locals op faPolMixedStructTy mem decls faPolicyLayouts .stripProvenance =
      .ok expectedVal locals' mem ∧
    -- MiniRust per-field Type.Tuple transmuteM lockstep across BM and TBM
    transmuteM (M := BM)
        (.Tuple [.Ptr ⟨⟨(pA.offsetBytes : Int), provABM⟩, none⟩,
                 .Ptr ⟨⟨(pB.offsetBytes : Int), provBBM⟩, none⟩])
        faMrPtrPtrTupleTy faMrPtrU64TupleTy =
      .ok (.Tuple [.Ptr ⟨⟨(pA.offsetBytes : Int), provABM⟩, none⟩, .Int (pB.offsetBytes : Int)]) ∧
    transmuteM (M := TBM)
        (.Tuple [.Ptr ⟨⟨(pA.offsetBytes : Int), provATB⟩, none⟩,
                 .Ptr ⟨⟨(pB.offsetBytes : Int), provBTB⟩, none⟩])
        faMrPtrPtrTupleTy faMrPtrU64TupleTy =
      .ok (.Tuple [.Ptr ⟨⟨(pA.offsetBytes : Int), provATB⟩, none⟩, .Int (pB.offsetBytes : Int)]) := by
  dsimp only
  let bsA := encodeLittleEndianBytes pA.offsetBytes 8 (some (pA.allocId, pA.tag))
  let bsB := encodeLittleEndianBytes pB.offsetBytes 8 (some (pB.allocId, pB.tag))
  let bsAB := appendAbstractBytes bsA bsB
  have hLenA : Trusted.Sequence.length bsA = 8 := fc_seqLength_encodeLittleEndianBytes _ 8 _
  have hLenB : Trusted.Sequence.length bsB = 8 := fc_seqLength_encodeLittleEndianBytes _ 8 _
  have hEnc : encodeByteCastSourceBytes faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolPtrPtrTupTy)
      (.aggregate 0 [.ptr pA 8, .ptr pB 8]) = some bsAB := rfl
  have hLen : Trusted.Sequence.length bsAB = 16 := (fa_slice_append_8 bsA bsB hLenA hLenB).1
  have hSzPP : tyByteSize decls faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolPtrPtrTupTy) = some 16 := rfl
  have hSzPU : tyByteSize decls faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolPtrUsizeTupTy) = some 16 := rfl
  have hSzMix : tyByteSize decls faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolMixedStructTy) = some 16 := rfl
  have hUnifA : abstractBytesUniformProv bsA = true := by
    simp [bsA, abstractBytesUniformProv, abstractBytesAllProvAux, Nat.beq_refl]
  have hDecA := fc_decodeScalarBytes_encode (some (pA.allocId, pA.tag)) false 7 pA.offsetBytes
    (fc_lt_256_pow_8 hA)
  have hDecB := fc_decodeScalarBytes_encode (some (pB.allocId, pB.tag)) false 7 pB.offsetBytes
    (fc_lt_256_pow_8 hB)
  have hPtrA : decodePtrBytesNoForge false (.uint .u8) 8 bsA =
      some (.ptr { allocId := pA.allocId, offsetBytes := pA.offsetBytes } 8) := by
    dsimp only [decodePtrBytesNoForge]
    rw [fc_seqLength_encodeLittleEndianBytes, Nat.beq_refl, hDecA, hUnifA]
  have hWrB : wrappingRangeContains { start := 0, end_ := 2 ^ (8 * 8) - 1 } pB.offsetBytes = true := by
    unfold wrappingRangeContains
    have h01 : Nat.ble 0 (2 ^ (8 * 8) - 1) = true := Nat.ble_eq.mpr (Nat.zero_le _)
    have h0 : Nat.ble 0 pB.offsetBytes = true := Nat.ble_eq.mpr (Nat.zero_le _)
    have h1 : Nat.ble pB.offsetBytes (2 ^ (8 * 8) - 1) = true :=
      Nat.ble_eq.mpr (Nat.le_sub_one_of_lt hB)
    simp only [h01, h0, h1, Bool.and_true]
  have hBstrict : decodeTypedValueFromBytes 15 faPolicyLayouts
      { kind := .uint .usize, layoutIdx := 9 } bsB .strictUcg630Ub = none := rfl
  have hBstrip : decodeTypedValueFromBytes 15 faPolicyLayouts
      { kind := .uint .usize, layoutIdx := 9 } bsB .stripProvenance =
      some (.scalar ⟨pB.offsetBytes, 8⟩) := by
    change (match decodeScalarBytes bsB false with
      | some (sv, _) => some (Value.scalar sv) | none => none) = _
    rw [hDecB]
  have hMixA : ∀ pol, decodeScalarLayoutBytesNoForge
      (.initialized (.pointer 0) { start := 0, end_ := 2 ^ (8 * 8) - 1 }) bsA pol =
      some (.ptr { allocId := pA.allocId, offsetBytes := pA.offsetBytes } 8) := fun _ => by
    dsimp only [decodeScalarLayoutBytesNoForge, scalarLayoutByteWidth]
    rw [fc_seqLength_encodeLittleEndianBytes, Nat.beq_refl, hDecA, hUnifA]
  have hMixBS : decodeScalarLayoutBytesNoForge
      (.initialized (.int 64 false) { start := 0, end_ := 2 ^ (8 * 8) - 1 }) bsB .strictUcg630Ub =
      none := by
    dsimp only [decodeScalarLayoutBytesNoForge, scalarLayoutByteWidth]
    rw [fc_seqLength_encodeLittleEndianBytes]
  have hMixBP : decodeScalarLayoutBytesNoForge
      (.initialized (.int 64 false) { start := 0, end_ := 2 ^ (8 * 8) - 1 }) bsB .stripProvenance =
      some (.scalar ⟨pB.offsetBytes, 8⟩) := by
    dsimp only [decodeScalarLayoutBytesNoForge, scalarLayoutByteWidth]
    rw [fc_seqLength_encodeLittleEndianBytes, Nat.beq_refl, hDecB]
    dsimp only
    rw [hWrB]
    rfl
  have hTupS : decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolPtrUsizeTupTy bsAB .strictUcg630Ub = none := by
    rw [fa_decodeTyped_ptrUsizeTup bsA bsB hLenA hLenB .strictUcg630Ub, hPtrA, hBstrict]
  have hTupP : decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolPtrUsizeTupTy bsAB .stripProvenance =
      some (.aggregate 0 [.ptr { allocId := pA.allocId, offsetBytes := pA.offsetBytes } 8, .scalar ⟨pB.offsetBytes, 8⟩]) := by
    rw [fa_decodeTyped_ptrUsizeTup bsA bsB hLenA hLenB .stripProvenance, hPtrA, hBstrip]
  have hMixS : decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolMixedStructTy bsAB .strictUcg630Ub = none := by
    rw [fa_decodeTyped_mixedStruct bsA bsB hLenA hLenB .strictUcg630Ub, hMixA, hMixBS]
  have hMixP : decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolMixedStructTy bsAB .stripProvenance =
      some (.aggregate 0 [.ptr { allocId := pA.allocId, offsetBytes := pA.offsetBytes } 8, .scalar ⟨pB.offsetBytes, 8⟩]) := by
    rw [fa_decodeTyped_mixedStruct bsA bsB hLenA hLenB .stripProvenance, hMixA, hMixBP]
  have hResPU : resolveTyWithLocalDecls decls faPolicyLayouts faPolPtrUsizeTupTy = faPolPtrUsizeTupTy := rfl
  have hResMix : resolveTyWithLocalDecls decls faPolicyLayouts faPolMixedStructTy = faPolMixedStructTy := rfl
  refine ⟨?_, ?_, ?_, ?_,
    (fa_mrM_transmute_ptr_tuple_selective (M := BM) pA.offsetBytes pB.offsetBytes hA hB provABM provBBM none).1,
    (fa_mrM_transmute_ptr_tuple_selective (M := TBM) pA.offsetBytes pB.offsetBytes hA hB provATB provBTB none).1⟩
  · rw [fa_evalByteCast_of_encode locals locals' op mem decls faPolicyLayouts _ _ _ 16 _ _ hOp hSzPU hTy hSzPP hEnc hLen, hResPU, hTupS]
  · rw [fa_evalByteCast_of_encode locals locals' op mem decls faPolicyLayouts _ _ _ 16 _ _ hOp hSzPU hTy hSzPP hEnc hLen, hResPU, hTupP]
  · rw [fa_evalByteCast_of_encode locals locals' op mem decls faPolicyLayouts _ _ _ 16 _ _ hOp hSzMix hTy hSzPP hEnc hLen, hResMix, hMixS]
  · rw [fa_evalByteCast_of_encode locals locals' op mem decls faPolicyLayouts _ _ _ 16 _ _ hOp hSzMix hTy hSzPP hEnc hLen, hResMix, hMixP]
/-! ### §3.2 Provenance-free equivalence & shared UB / no-forgery under BOTH policies -/
/-- **Provenance-free policy equivalence (`usize ↔ u64`, `u32 ↔ i32 ↔ [u8; 4]`, `u64 → *const u8`)**:
whenever the source operand is provenance-free (`Value.scalar`), `.strictUcg630Ub` and
`.stripProvenance` agree 100% with each other (on both `evalByteCast` and `EvalRvalueFloatRel`)
AND with MiniRust's `transmuteM` across both `BasicMemory` and `TreeBorrowsMemory`. -/
theorem fa_provFree_policy_equivalence_correspondence
    {locals locals' : List LocalSlot} {op32 op64 : Operand} {mem : Memory} {decls : List LocalDecl} {b32 b64 : Nat} (h32 : b32 < 2 ^ 32) (h64 : b64 < 2 ^ 64)
    (hOp32 : evalOperand locals op32 mem.borrows mem.globals faPolicyLayouts mem.callerLocals decls
      mem.callStack = .ok (.scalar ⟨b32, 4⟩) locals')
    (hTy32 : operandTy decls faPolicyLayouts op32 = some faPolU32Ty) (hOp64 : evalOperand locals op64 mem.borrows mem.globals faPolicyLayouts mem.callerLocals decls
      mem.callStack = .ok (.scalar ⟨b64, 8⟩) locals')
    (hTy64 : operandTy decls faPolicyLayouts op64 = some faPolU64Ty) :
    -- Both policies identical on u64 -> usize, u64 -> *const u8, u32 -> i32
    (∀ policy,
      evalByteCast locals op64 faPolUsizeTy mem decls faPolicyLayouts policy =
        .ok (.scalar ⟨b64, 8⟩) locals' mem ∧
      evalByteCast locals op64 faPolPtrTy mem decls faPolicyLayouts policy =
        .ok (.scalar ⟨b64, 8⟩) locals' mem ∧
      evalByteCast locals op32 faPolI32Ty mem decls faPolicyLayouts policy =
        .ok (.scalar ⟨b32, 4⟩) locals' mem) ∧
    -- EvalRvalueFloatRel policy-irrelevant on provenance-free casts (for every targetTy & mode)
    (∀ mode dstTy res,
      EvalRvalueFloatRel mode .strictUcg630Ub locals (.cast .transmute op64 dstTy) mem decls
        faPolicyLayouts res ↔
      EvalRvalueFloatRel mode .stripProvenance locals (.cast .transmute op64 dstTy) mem decls
        faPolicyLayouts res) ∧
    -- MiniRust BM & TBM lockstep on u64 -> u64/i64/*const u8 and u32 <-> i32 <-> [u8; 4]
    transmuteM (M := BM) (.Int (b64 : Int)) (.Int fcU64It) (.Ptr (.Raw .None)) =
      .ok (.Ptr ⟨⟨(b64 : Int), none⟩, none⟩) ∧
    transmuteM (M := TBM) (.Int (b64 : Int)) (.Int fcU64It) (.Ptr (.Raw .None)) =
      .ok (.Ptr ⟨⟨(b64 : Int), none⟩, none⟩) ∧
    transmuteM (M := BM) (.Int (b32 : Int)) (.Int fcU32It) (.Int fcI32It) =
      .ok (.Int (intFromBits b32 fcI32It)) ∧
    transmuteM (M := TBM) (.Int (b32 : Int)) (.Int fcU32It) (.Array (.Int fcU8It) 4) =
      .ok (.Tuple (fcLeByteValsMRM b32 4)) ∧
    transmuteM (M := TBM) (.Tuple (fcLeByteValsMRM b32 4)) (.Array (.Int fcU8It) 4) (.Int fcI32It) =
      .ok (.Int (intFromBits b32 fcI32It)) := by
  have h64_eq : ∀ dstTy,
      evalByteCast locals op64 dstTy mem decls faPolicyLayouts .strictUcg630Ub =
      evalByteCast locals op64 dstTy mem decls faPolicyLayouts .stripProvenance :=
    fun dstTy => evalByteCast_eq_of_provFree locals locals' op64 dstTy mem decls faPolicyLayouts
      (.scalar ⟨b64, 8⟩) hOp64 rfl
  have h32_eq : ∀ dstTy,
      evalByteCast locals op32 dstTy mem decls faPolicyLayouts .strictUcg630Ub =
      evalByteCast locals op32 dstTy mem decls faPolicyLayouts .stripProvenance :=
    fun dstTy => evalByteCast_eq_of_provFree locals locals' op32 dstTy mem decls faPolicyLayouts
      (.scalar ⟨b32, 4⟩) hOp32 rfl
  have hEnc64 : encodeByteCastSourceBytes faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolU64Ty) (.scalar ⟨b64, 8⟩) =
      some (encodeLittleEndianBytes b64 8 none) := rfl
  have hEnc32 : encodeByteCastSourceBytes faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolU32Ty) (.scalar ⟨b32, 4⟩) =
      some (encodeLittleEndianBytes b32 4 none) := rfl
  have hSz64 : tyByteSize decls faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolU64Ty) = some 8 := rfl
  have hSzUsize : tyByteSize decls faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolUsizeTy) = some 8 := rfl
  have hSzPtr : tyByteSize decls faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolPtrTy) = some 8 := rfl
  have hSz32 : tyByteSize decls faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolU32Ty) = some 4 := rfl
  have hSzI32 : tyByteSize decls faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolI32Ty) = some 4 := rfl
  have hDecU64 : decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolUsizeTy
      (encodeLittleEndianBytes b64 8 none) .strictUcg630Ub = some (.scalar ⟨b64, 8⟩) := by
    change (match decodeScalarBytes (encodeLittleEndianBytes b64 8 none) false with
      | some (sv, _) => some (Value.scalar sv) | none => none) = _
    rw [fc_decodeScalarBytes_encode none false 7 b64 (fc_lt_256_pow_8 h64)]
  have hDecPtr : decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolPtrTy
      (encodeLittleEndianBytes b64 8 none) .strictUcg630Ub = some (.scalar ⟨b64, 8⟩) := by
    change decodePtrBytesNoForge false (.uint .u8) 8 (encodeLittleEndianBytes b64 8 none) = _
    dsimp only [decodePtrBytesNoForge]
    rw [fc_seqLength_encodeLittleEndianBytes, fc_decodeScalarBytes_encode none false 7 b64 (fc_lt_256_pow_8 h64)]
  have hDecI32 : decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolI32Ty
      (encodeLittleEndianBytes b32 4 none) .strictUcg630Ub = some (.scalar ⟨b32, 4⟩) := by
    change (match decodeScalarBytes (encodeLittleEndianBytes b32 4 none) true with
      | some (sv, _) => some (Value.scalar sv) | none => none) = _
    rw [fc_decodeScalarBytes_encode none true 3 b32 (fc_lt_256_pow_4 h32)]
  have hResUsize : resolveTyWithLocalDecls decls faPolicyLayouts faPolUsizeTy = faPolUsizeTy := rfl
  have hResPtr : resolveTyWithLocalDecls decls faPolicyLayouts faPolPtrTy = faPolPtrTy := rfl
  have hResI32 : resolveTyWithLocalDecls decls faPolicyLayouts faPolI32Ty = faPolI32Ty := rfl
  have h1S : evalByteCast locals op64 faPolUsizeTy mem decls faPolicyLayouts .strictUcg630Ub =
      .ok (.scalar ⟨b64, 8⟩) locals' mem := by
    rw [fa_evalByteCast_of_encode locals locals' op64 mem decls faPolicyLayouts _ _ _ 8 _ _ hOp64 hSzUsize hTy64 hSz64 hEnc64 (fc_seqLength_encodeLittleEndianBytes none 8 b64),
      hResUsize, hDecU64]
  have h2S : evalByteCast locals op64 faPolPtrTy mem decls faPolicyLayouts .strictUcg630Ub =
      .ok (.scalar ⟨b64, 8⟩) locals' mem := by
    rw [fa_evalByteCast_of_encode locals locals' op64 mem decls faPolicyLayouts _ _ _ 8 _ _ hOp64 hSzPtr hTy64 hSz64 hEnc64 (fc_seqLength_encodeLittleEndianBytes none 8 b64),
      hResPtr, hDecPtr]
  have h3S : evalByteCast locals op32 faPolI32Ty mem decls faPolicyLayouts .strictUcg630Ub =
      .ok (.scalar ⟨b32, 4⟩) locals' mem := by
    rw [fa_evalByteCast_of_encode locals locals' op32 mem decls faPolicyLayouts _ _ _ 4 _ _ hOp32 hSzI32 hTy32 hSz32 hEnc32 (fc_seqLength_encodeLittleEndianBytes none 4 b32),
      hResI32, hDecI32]
  refine ⟨fun policy => ?_, fun mode dstTy res =>
      EvalRvalueFloatRel_byteCast_policy_irrelevant_of_provFree mode .strictUcg630Ub
        .stripProvenance locals locals' .transmute op64 dstTy mem decls faPolicyLayouts
        (.scalar ⟨b64, 8⟩) res (.inl rfl) hOp64 rfl,
    (fa_mrM_transmute_ptr_strip (M := BM) .Unsigned b64 h64 none none).2.2.2, (fa_mrM_transmute_ptr_strip (M := TBM) .Unsigned b64 h64 none none).2.2.2,
    fc_mrBM_transmute_int .Unsigned .Signed 4 b32 fc_goodSize_4 h32 none,
    (fc_mrM_transmute_int_bytes4 (M := TBM) .Unsigned b32 h32 none).1, (fc_mrM_transmute_int_bytes4 (M := TBM) .Signed b32 h32 none).2⟩
  cases policy with
  | strictUcg630Ub => exact ⟨h1S, h2S, h3S⟩
  | stripProvenance => exact ⟨(h64_eq _).symm.trans h1S, (h64_eq _).symm.trans h2S, (h32_eq _).symm.trans h3S⟩
private theorem fa_isAligned_one (addr : Nat) : Align.is_aligned ⟨1⟩ (addr : Int) = true := by
  unfold Align.is_aligned
  change ((addr : Int) % (1 : Int) == 0) = true
  rw [Int.emod_one]
  rfl
private theorem fa_checkPtrM_refU8_of_bounds {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr : Nat) (m : Option (Gen.Machine M)) (hbU : inBounds (addr : Int) .Unsigned x86_64.PTR_SIZE = true)
    (hbS : inBounds ((⟨1⟩ : LibSpecr.Size).bytes : Int) .Signed x86_64.PTR_SIZE = true) (hDeref : ∀ mach : Gen.Machine M,
      ConcurrentMemory.dereferenceable mach.mem ⟨(addr : Int), none⟩ ⟨1⟩ =
        .error (.ub "dereferencing pointer without provenance")) :
    checkPtrM (M := M) ⟨⟨(addr : Int), none⟩, none⟩ (refPtrType .not fcU8It) m =
      .error (.ub (if addr = 0 then "Value::Ptr: null safe pointer"
                   else "Value::Ptr: non-dereferenceable safe pointer")) := by
  have hmeta : checkPtrMetadataM (none : Option (Gen.PointerMeta (Gen.Memory.Provenance M)))
      (PtrType.meta_kind (refPtrType .not fcU8It)) (m.map (vtableFromPtrM ·)) = .ok () := rfl
  have hsp : PtrType.safe_pointee (refPtrType .not fcU8It) =
      some { layout := .Sized ⟨1⟩ ⟨1⟩, inhabited := true, unsafe_cells := .Sized [],
             freeze := true, unpin := true } := rfl
  have hcsa : ∀ (lk : Gen.ThinPointer (Gen.Memory.Provenance M) → Interp Gen.VTable),
      LayoutStrategy.compute_size_and_align lk (.Sized ⟨1⟩ ⟨1⟩) none = .ok (⟨1⟩, ⟨1⟩) :=
    fun _ => rfl
  unfold checkPtrM
  dsimp only
  rw [hbU]
  simp only [ensureElseUb, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure, hmeta, hsp, hcsa]
  rw [hbS]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases addr with
  | zero => rfl
  | succ k =>
    have hne : (((Nat.succ k : Nat) : Int) != 0) = true := rfl
    rw [hne, fa_isAligned_one (Nat.succ k)]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
    cases m with
    | none => rfl
    | some mach =>
      dsimp only
      rw [hDeref mach]
      rfl
private theorem fa_checkPtrM_refU8_noProv_ub {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr : Nat) (haddr : addr < 2 ^ 64) (m : Option (Gen.Machine M)) (hDeref : ∀ mach : Gen.Machine M,
      ConcurrentMemory.dereferenceable mach.mem ⟨(addr : Int), none⟩ ⟨1⟩ =
        .error (.ub "dereferencing pointer without provenance")) :
    checkPtrM (M := M) ⟨⟨(addr : Int), none⟩, none⟩ (refPtrType .not fcU8It) m =
      .error (.ub (if addr = 0 then "Value::Ptr: null safe pointer"
                   else "Value::Ptr: non-dereferenceable safe pointer")) :=
  fa_checkPtrM_refU8_of_bounds (M := M) addr m (fa_inBounds_u64 addr haddr) (by decide) hDeref
/-- **Choice-free MiniRust no-forgery UB for `usize / u64 → &u8`**, for EVERY `addr < 2 ^ 64`
and EVERY machine context (`none` or `some mach`) across BOTH `BasicMemory` and
`TreeBorrowsMemory`: transmuting an integer without provenance to a safe shared reference `&u8`
always raises UB (`"Value::Ptr: null safe pointer"` for `0`, `"Value::Ptr: non-dereferenceable
safe pointer"` for every nonzero address). -/
theorem fa_mrM_transmute_u64_to_refU8_ub (addr : Nat) (haddr : addr < 2 ^ 64)
    (mBM : Option Mach) (mTB : Option MachTB) :
    transmuteM (M := BM) (.Int (addr : Int)) (.Int fcU64It) faMrRefU8Ty mBM =
      .error (.ub (if addr = 0 then "Value::Ptr: null safe pointer"
                   else "Value::Ptr: non-dereferenceable safe pointer")) ∧
    transmuteM (M := TBM) (.Int (addr : Int)) (.Int fcU64It) faMrRefU8Ty mTB =
      .error (.ub (if addr = 0 then "Value::Ptr: null safe pointer"
                   else "Value::Ptr: non-dereferenceable safe pointer")) := by
  have hlayU := layout_eq fcU64It fc_goodSize_8
  have hlayR : Type.layout faMrRefU8Ty = .ok (.Sized ⟨8⟩ ⟨8⟩) := rfl
  have hdecBM : Type.decodeM (M := BM) faMrRefU8Ty
      (encodePtrBytesM (M := BM) none 0 (leBytes addr 8)) =
      .ok (some (.Ptr ⟨⟨(addr : Int), none⟩, none⟩)) := by
    simp only [faMrRefU8Ty, refTy, Type.decodeM, PtrType.as_wide_pair, PtrType.meta_kind, Option.map, bind, Except.bind, pure, Except.pure,
      fa_decodePtrM_encodePtrBytesM (M := BM) none addr haddr]
    rfl
  have hdecTB : Type.decodeM (M := TBM) faMrRefU8Ty
      (encodePtrBytesM (M := TBM) none 0 (leBytes addr 8)) =
      .ok (some (.Ptr ⟨⟨(addr : Int), none⟩, none⟩)) := by
    simp only [faMrRefU8Ty, refTy, Type.decodeM, PtrType.as_wide_pair, PtrType.meta_kind, Option.map, bind, Except.bind, pure, Except.pure,
      fa_decodePtrM_encodePtrBytesM (M := TBM) none addr haddr]
    rfl
  have hchkBM : checkValueM (M := BM) (.Ptr ⟨⟨(addr : Int), none⟩, none⟩) faMrRefU8Ty mBM =
      .error (.ub (if addr = 0 then "Value::Ptr: null safe pointer"
                   else "Value::Ptr: non-dereferenceable safe pointer")) :=
    fa_checkPtrM_refU8_noProv_ub (M := BM) addr haddr mBM (fun _ => rfl)
  have hchkTB : checkValueM (M := TBM) (.Ptr ⟨⟨(addr : Int), none⟩, none⟩) faMrRefU8Ty mTB =
      .error (.ub (if addr = 0 then "Value::Ptr: null safe pointer"
                   else "Value::Ptr: non-dereferenceable safe pointer")) :=
    fa_checkPtrM_refU8_noProv_ub (M := TBM) addr haddr mTB (fun _ => rfl)
  exact ⟨
    fa_transmuteM_of_check_err _ _ _ _ _ _ _ _ mBM _ hlayU hlayR
      (fa_encodeIntM_u64_cf (M := BM) addr haddr) hdecBM hchkBM,
    fa_transmuteM_of_check_err _ _ _ _ _ _ _ _ mTB _ hlayU hlayR
      (fa_encodeIntM_u64_cf (M := TBM) addr haddr) hdecTB hchkTB⟩
/-- **Shared UB / No-Forgery Under BOTH Policies (choice-free)**:
1. `usize / u64 → &u8` safe-reference forgery: BOTH `.strictUcg630Ub` and `.stripProvenance` fault
   `.ub` (at `evalByteCast` and `EvalRvalueFloatRel` in both modes), matching MiniRust's UB across
   both `BasicMemory` and `TreeBorrowsMemory` for ALL `addr < 2 ^ 64`;
2. `MaybeUninit<u64>` uninitialized bytes → `u64`: BOTH policies return `.none` / `.ub`, matching
   MiniRust's `Type.Union` uninit-byte transmute UB across both `BM` and `TBM`;
3. Size mismatch (`u32 ↔ u64`, `*const u8 → u32`): BOTH policies fail closed `.unsupported` in
   Anneal while MiniRust raises `"transmute between types of different size"` across `BM` & `TBM`. -/
theorem fa_shared_ub_no_forge_both_policies
    {locals locals' : List LocalSlot} {op64 opUninit : Operand} {mem : Memory} {decls : List LocalDecl} {addr : Nat} (haddr : addr < 2 ^ 64)
    (hOp64 : evalOperand locals op64 mem.borrows mem.globals faPolicyLayouts mem.callerLocals decls
      mem.callStack = .ok (.scalar ⟨addr, 8⟩) locals')
    (hTy64 : operandTy decls faPolicyLayouts op64 = some faPolUsizeTy) (hOpUninit : evalOperand locals opUninit mem.borrows mem.globals faPolicyLayouts
      mem.callerLocals decls mem.callStack = .ub)
    (mBM : Option Mach) (mTB : Option MachTB) :
    -- (1) usize -> &u8 UB under BOTH policies and BOTH MiniRust memory models
    (∀ mode policy,
      evalByteCast locals op64 faPolRefU8Ty mem decls faPolicyLayouts policy = .ub ∧
      EvalRvalueFloatRel mode policy locals (.cast .transmute op64 faPolRefU8Ty) mem decls
        faPolicyLayouts .ub) ∧
    transmuteM (M := BM) (.Int (addr : Int)) (.Int fcU64It) faMrRefU8Ty mBM =
      .error (.ub (if addr = 0 then "Value::Ptr: null safe pointer"
                   else "Value::Ptr: non-dereferenceable safe pointer")) ∧
    transmuteM (M := TBM) (.Int (addr : Int)) (.Int fcU64It) faMrRefU8Ty mTB =
      .error (.ub (if addr = 0 then "Value::Ptr: null safe pointer"
                   else "Value::Ptr: non-dereferenceable safe pointer")) ∧
    -- (2) MaybeUninit<u64> uninit bytes -> u64 UB under BOTH policies and BOTH MiniRust memory models
    (∀ policy,
      decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolU64Ty
        (List.replicate 8 .uninit) policy = none ∧
      evalByteCast locals opUninit faPolU64Ty mem decls faPolicyLayouts policy = .ub) ∧
    transmuteM (M := BM) (.Union [List.replicate 8 .Uninit]) (fcUnionTy 8) (.Int fcU64It) mBM =
      .error (.ub "transmuted value is not valid at new type") ∧
    transmuteM (M := TBM) (.Union [List.replicate 8 .Uninit]) (fcUnionTy 8) (.Int fcU64It) mTB =
      .error (.ub "transmuted value is not valid at new type") ∧
    -- (3) Size mismatch: Anneal .unsupported under BOTH policies vs MiniRust UB across BM & TBM
    (∀ policy,
      evalByteCast locals op64 faPolU32Ty mem decls faPolicyLayouts policy = .unsupported) ∧
    evalCastOpM (M := BM) (.Transmute (.Int fcU32It)) (.Int (addr : Int), .Int fcU64It) mBM =
      .error (.ub "transmute between types of different size") ∧
    evalCastOpM (M := TBM) (.Transmute (.Int fcU32It)) (.Int (addr : Int), .Int fcU64It) mTB =
      .error (.ub "transmute between types of different size") := by
  have hEnc64 : encodeByteCastSourceBytes faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolUsizeTy) (.scalar ⟨addr, 8⟩) =
      some (encodeLittleEndianBytes addr 8 none) := rfl
  have hSzUsize : tyByteSize decls faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolUsizeTy) = some 8 := rfl
  have hSzRef : tyByteSize decls faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolRefU8Ty) = some 8 := rfl
  have hSzU32 : tyByteSize decls faPolicyLayouts
      (resolveTyWithLocalDecls decls faPolicyLayouts faPolU32Ty) = some 4 := rfl
  have hDecRef : ∀ policy, decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolRefU8Ty
      (encodeLittleEndianBytes addr 8 none) policy = none := by
    intro policy
    change decodePtrBytesNoForge true (.uint .u8) 8 (encodeLittleEndianBytes addr 8 none) = none
    dsimp only [decodePtrBytesNoForge]
    rw [fc_seqLength_encodeLittleEndianBytes, fc_decodeScalarBytes_encode none false 7 addr (fc_lt_256_pow_8 haddr)]
  have hResRef : resolveTyWithLocalDecls decls faPolicyLayouts faPolRefU8Ty = faPolRefU8Ty := rfl
  have hRefUb : ∀ policy,
      evalByteCast locals op64 faPolRefU8Ty mem decls faPolicyLayouts policy = .ub := by
    intro policy
    rw [fa_evalByteCast_of_encode locals locals' op64 mem decls faPolicyLayouts _ _ _ 8 _ policy hOp64 hSzRef hTy64 hSzUsize hEnc64 (fc_seqLength_encodeLittleEndianBytes none 8 addr),
      hResRef, hDecRef policy]
  have hMrRef := fa_mrM_transmute_u64_to_refU8_ub addr haddr mBM mTB
  have hMrUninitBM : transmuteM (M := BM) (.Union [List.replicate 8 .Uninit]) (fcUnionTy 8)
      (.Int fcU64It) mBM = .error (.ub "transmuted value is not valid at new type") := rfl
  have hMrUninitTB : transmuteM (M := TBM) (.Union [List.replicate 8 .Uninit]) (fcUnionTy 8)
      (.Int fcU64It) mTB = .error (.ub "transmuted value is not valid at new type") := rfl
  have hSzMis : ∀ policy,
      evalByteCast locals op64 faPolU32Ty mem decls faPolicyLayouts policy = .unsupported := by
    intro policy
    rw [fa_evalByteCast_eq locals locals' op64 mem decls faPolicyLayouts _ _ _ 8 4 policy hOp64 hSzU32 hTy64 hSzUsize]
  refine ⟨fun mode policy => ⟨hRefUb policy,
      (EvalRvalueFloatRel_byteCast_iff mode policy locals .transmute op64 faPolRefU8Ty mem decls
        faPolicyLayouts .ub (.inl rfl)).mpr (hRefUb policy).symm⟩,
    hMrRef.1, hMrRef.2, fun policy => ⟨by cases policy <;> rfl, by unfold evalByteCast; rw [hOpUninit]⟩,
    hMrUninitBM, hMrUninitTB, hSzMis,
    (fc_mrM_evalCastOpM_size_mismatch_ub (M := BM) (.Int (addr : Int)) mBM).2.1, (fc_mrM_evalCastOpM_size_mismatch_ub (M := TBM) (.Int (addr : Int)) mTB).2.1⟩
/-! ### §3.3 Live `Mach` & `MachTB` (`wfLive`) machine witnesses for `Ptr2IntTransmutePolicy` & shared UB -/
/-- `fn ptr_to_u64(x: u32) -> u64 { transmute::<*const u32, u64>(&raw const x) }`:
`_2 = &raw const _1; _0 = copy _2 as u64 (Transmute)`. -/
def faPtrToU64Body : CapturedMir :=
  fcBody "float_arith::ptr_to_u64" [fcDecl fcU64Ty, fcDecl fcU32Ty, fcDecl fcRawPtrU32Ty]
    [.storageLive 2,
     .assign (local_ 2) (.rawPtr .not (local_ 1)),
     .assign (local_ 0) (.cast .transmute (.copy (local_ 2)) fcU64Ty),
     .storageDead 2]
/-- Translated MiniRust function of `faPtrToU64Body`. -/
def faPtrToU64Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int fcU64It), (localName 1, .Int fcU32It),
              (localName 2, .Ptr (.Raw .None))]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (.Raw .None)),
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.Transmute (.Int fcU64It))) (.Load (.Local (localName 2)))),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true
theorem fa_ptrToU64_translate : translateFn faPtrToU64Body = some faPtrToU64Fn := rfl
/-- `fn usize_to_ref_u8(x: u64) -> u64 { let _r: &u8 = transmute(x); x }`:
transmutes a provenance-free `u64` into a safe shared reference `&u8`. -/
def faUsizeToRefU8Body : CapturedMir :=
  fcBody "float_arith::usize_to_ref_u8" [fcDecl fcU64Ty, fcDecl fcU64Ty, fcDecl faRefU8Ty]
    [.storageLive 2,
     .assign (local_ 2) (.cast .transmute (.copy (local_ 1)) faRefU8Ty),
     .assign (local_ 0) (.use (.copy (local_ 1))),
     .storageDead 2]
/-- Translated MiniRust function of `faUsizeToRefU8Body`. -/
def faUsizeToRefU8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int fcU64It), (localName 1, .Int fcU64It),
              (localName 2, faMrRefU8Ty)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 2))
        (.UnOp (.Cast (.Transmute faMrRefU8Ty)) (.Load (.Local (localName 1)))),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 1))),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true
theorem fa_usizeToRefU8_translate : translateFn faUsizeToRefU8Body = some faUsizeToRefU8Fn := rfl
/-- `fn uninit_transmute_u64(x: u64) -> u64`: reads an uninitialized local `_2 : u64` into
`transmute::<u64, u64>`. -/
def faUninitTransmuteU64Body : CapturedMir :=
  fcBody "float_arith::uninit_transmute_u64" [fcDecl fcU64Ty, fcDecl fcU64Ty, fcDecl fcU64Ty]
    [.storageLive 2,
     .assign (local_ 0) (.cast .transmute (.copy (local_ 2)) fcU64Ty),
     .storageDead 2]
/-- Translated MiniRust function of `faUninitTransmuteU64Body`. -/
def faUninitTransmuteU64Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int fcU64It), (localName 1, .Int fcU64It),
              (localName 2, .Int fcU64It)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.Transmute (.Int fcU64It))) (.Load (.Local (localName 2)))),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true
theorem fa_uninitTransmuteU64_translate :
    translateFn faUninitTransmuteU64Body = some faUninitTransmuteU64Fn := rfl
/-- `fn int_div_zero(x: u32) -> u32 { x / 0 }`: contrasts with IEEE-754 `1.0_f32 / 0.0_f32 = +Inf`. -/
def faIntDivZeroBody : CapturedMir :=
  ptrBody "float_arith::int_div_zero" [u32Decl, u32Decl]
    [.assign (local_ 0) (.binaryOp .div (.copy (local_ 1)) (constU32 0))]
/-- Translated MiniRust function of `faIntDivZeroBody`. -/
def faIntDivZeroFn : Gen.Function where
  locals := ⟨[(localName 0, .Int fcU32It), (localName 1, .Int fcU32It)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Div) (.Load (.Local (localName 1))) (.Constant (.Int 0) (.Int fcU32It)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true
theorem fa_intDivZero_translate : translateFn faIntDivZeroBody = some faIntDivZeroFn := rfl
/-- **Live `Mach` & `MachTB` (`wfLive`) execution of `*const u32 → u64` (`faPtrToU64Body`)**:
- MiniRust (`BasicMemory` `Interp.steps` AND `TreeBorrowsMemory` `Interp.stepsTB` preserving
  `MachTB.wfLive`) strips provenance and returns `_1`'s stack address `256` (`fcCtx8.addrs[1]`)
  in `fcRetAlloc8`;
- Anneal's default executable `mirCallTree` (`.strictUcg630Ub`) faults `.ub` (`faultsA = true`,
  `¬ MirNoUBTree`);
- Switching Anneal's `evalByteCast` on the exact same live pointer `.ptr { allocId := 2,
  offsetBytes := 256 } 8` from `.strictUcg630Ub` to `.stripProvenance` flips `.ub` to
  `.ok (.scalar ⟨256, 8⟩)` — matching MiniRust `Mach` & `MachTB` byte-for-byte! -/
theorem fa_ptr2int_live_mach_and_machTB_wfLive :
    fcRetAfter8 faPtrToU64Body [.scalar ⟨7, 4⟩] 6 =
      some (some { fcRetAlloc8 with data := (encodeLittleEndianBytes 256 8 none).map fcByteToMR },
        [1]) ∧
    fcRetAfterTB8 faPtrToU64Body [.scalar ⟨7, 4⟩] 6 = tbRetU64 256 ∧
    (∃ m0 m', fcStartMachineTB8 faPtrToU64Body [.scalar ⟨7, 4⟩] = some m0 ∧
      Interp.stepsTB 6 m0 = .ok m' ∧ MachTB.wfLive m') ∧
    faultsA faPtrToU64Body 10 (initMachineState faPtrToU64Body [.scalar ⟨7, 4⟩]) = true ∧
    ¬ MirNoUBTree (mirCallTree faPtrToU64Body [.scalar ⟨7, 4⟩]) ∧
    evalByteCast [.init (.ptr { allocId := 2, offsetBytes := 256 } 8)]
        (.copy (local_ 0)) fcU64Ty emptyMemory [fcDecl fcRawPtrU32Ty] fcLayouts .strictUcg630Ub =
      .ub ∧
    evalByteCast [.init (.ptr { allocId := 2, offsetBytes := 256 } 8)]
        (.copy (local_ 0)) fcU64Ty emptyMemory [fcDecl fcRawPtrU32Ty] fcLayouts .stripProvenance =
      .ok (.scalar ⟨256, 8⟩)
        [.init (.ptr { allocId := 2, offsetBytes := 256 } 8)] emptyMemory := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, rfl, ?_, rfl, rfl⟩
  · exact fa_wfLive_of_stepsTB_isOk
      (machineWithCtx fcCtx8 faPtrToU64Body faPtrToU64Fn
        (initMachineState faPtrToU64Body [.scalar ⟨7, 4⟩]).frame.locals faPtrToU64Fn.start)
      6 (by decide +kernel)
  · obtain ⟨tr, u, hr, hf⟩ :=
      faultsA_sound faPtrToU64Body 10 (initMachineState faPtrToU64Body [.scalar ⟨7, 4⟩]) rfl
    exact fun hsafe => hsafe tr u hr hf
/-- **Live `Mach` & `MachTB` (`wfLive`) UB lockstep for `usize → &u8` and uninitialized `u64`
transmute**:
- `faUsizeToRefU8Body` (`0` and `256`): Anneal faults `.ub` under BOTH policies (`faultsA = true`,
  `¬ MirNoUBTree`, and `evalByteCast .stripProvenance = .ub`), while MiniRust `Mach` & `MachTB`
  raise `"Value::Ptr: null safe pointer"` / `"Value::Ptr: non-dereferenceable safe pointer"` at
  step 3 (preserving `MachTB.wfLive` at step 2 right before the UB cast);
- `faUninitTransmuteU64Body`: Anneal faults `.ub` under BOTH policies, while MiniRust `Mach` &
  `MachTB` raise `"load at type but the data in memory violates the language invariant"` at step 3
  (preserving `MachTB.wfLive` at step 2 right before the UB load). -/
theorem fa_no_forge_ref_and_uninit_live_mach_and_machTB_wfLive :
    -- usize -> &u8 on 0 (null) and 256 (non-null without provenance)
    faultsA faUsizeToRefU8Body 10 (initMachineState faUsizeToRefU8Body [.scalar ⟨0, 8⟩]) = true ∧
    ¬ MirNoUBTree (mirCallTree faUsizeToRefU8Body [.scalar ⟨0, 8⟩]) ∧
    faultsA faUsizeToRefU8Body 10 (initMachineState faUsizeToRefU8Body [.scalar ⟨256, 8⟩]) = true ∧
    ¬ MirNoUBTree (mirCallTree faUsizeToRefU8Body [.scalar ⟨256, 8⟩]) ∧
    evalByteCast [.init (.scalar ⟨256, 8⟩)] (.copy (local_ 0)) faRefU8Ty emptyMemory
        [fcDecl fcU64Ty] fcLayouts .stripProvenance = .ub ∧
    faUbAfter8 faUsizeToRefU8Body [.scalar ⟨0, 8⟩] 3 = some "Value::Ptr: null safe pointer" ∧
    faUbAfterTB8 faUsizeToRefU8Body [.scalar ⟨0, 8⟩] 3 = some "Value::Ptr: null safe pointer" ∧
    faUbAfter8 faUsizeToRefU8Body [.scalar ⟨256, 8⟩] 3 =
      some "Value::Ptr: non-dereferenceable safe pointer" ∧
    faUbAfterTB8 faUsizeToRefU8Body [.scalar ⟨256, 8⟩] 3 =
      some "Value::Ptr: non-dereferenceable safe pointer" ∧
    (∃ m0 m', fcStartMachineTB8 faUsizeToRefU8Body [.scalar ⟨256, 8⟩] = some m0 ∧
      Interp.stepsTB 2 m0 = .ok m' ∧ MachTB.wfLive m') ∧
    -- uninit u64 transmute
    faultsA faUninitTransmuteU64Body 10 (initMachineState faUninitTransmuteU64Body [.scalar ⟨0, 8⟩]) = true ∧
    ¬ MirNoUBTree (mirCallTree faUninitTransmuteU64Body [.scalar ⟨0, 8⟩]) ∧
    evalByteCast [.uninit] (.copy (local_ 0)) fcU64Ty emptyMemory
        [fcDecl fcU64Ty] fcLayouts .stripProvenance = .ub ∧
    faUbAfter8 faUninitTransmuteU64Body [.scalar ⟨0, 8⟩] 3 =
      some "load at type but the data in memory violates the language invariant" ∧
    faUbAfterTB8 faUninitTransmuteU64Body [.scalar ⟨0, 8⟩] 3 =
      some "load at type but the data in memory violates the language invariant" ∧
    (∃ m0 m', fcStartMachineTB8 faUninitTransmuteU64Body [.scalar ⟨0, 8⟩] = some m0 ∧
      Interp.stepsTB 2 m0 = .ok m' ∧ MachTB.wfLive m') := by
  refine ⟨rfl, ?_, rfl, ?_, rfl, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_, rfl, ?_, rfl, by decide +kernel, by decide +kernel, ?_⟩
  · obtain ⟨tr, u, hr, hf⟩ :=
      faultsA_sound faUsizeToRefU8Body 10 (initMachineState faUsizeToRefU8Body [.scalar ⟨0, 8⟩]) rfl
    exact fun hsafe => hsafe tr u hr hf
  · obtain ⟨tr, u, hr, hf⟩ :=
      faultsA_sound faUsizeToRefU8Body 10 (initMachineState faUsizeToRefU8Body [.scalar ⟨256, 8⟩]) rfl
    exact fun hsafe => hsafe tr u hr hf
  · exact fa_wfLive_of_stepsTB_isOk
      (machineWithCtx fcCtx8 faUsizeToRefU8Body faUsizeToRefU8Fn
        (initMachineState faUsizeToRefU8Body [.scalar ⟨256, 8⟩]).frame.locals faUsizeToRefU8Fn.start)
      2 (by decide +kernel)
  · obtain ⟨tr, u, hr, hf⟩ :=
      faultsA_sound faUninitTransmuteU64Body 10
        (initMachineState faUninitTransmuteU64Body [.scalar ⟨0, 8⟩]) rfl
    exact fun hsafe => hsafe tr u hr hf
  · exact fa_wfLive_of_stepsTB_isOk
      (machineWithCtx fcCtx8 faUninitTransmuteU64Body faUninitTransmuteU64Fn
        (initMachineState faUninitTransmuteU64Body [.scalar ⟨0, 8⟩]).frame.locals
        faUninitTransmuteU64Fn.start)
      2 (by decide +kernel)

/-! ## §4. Shared Concrete Episode 2 Witnesses `W1–W6` & Complete `#guard_msgs` Axiom Audit -/
/-- **`W1` — Finite, Subnormal, Overflow-Tie, and Signed-Zero Carrier Witness** (choice-free):
- Exact `f32`/`f64` subnormal addition (`0x00000001 + 0x00000001 = 0x00000002`, matching
  `exact_subnormal_add` and executing cleanly in `mirCallTree`);
- IEEE-754 ties-to-even overflow boundaries (`f32` `MAX + half-ULP = +Inf` vs `MAX + (half-ULP-1)
  = MAX`, and `f64` analogue via `evalFloatBinOp_overflow_tie_witness`);
- Signed-zero sums (`-0.0 + -0.0 = -0.0`, `-0.0 + +0.0 = +0.0`, `-0.0 - +0.0 = -0.0`);
- Canonical MiniRust `Type.encode`/`Type.decode`/`transmuteM (M := BM/TBM)` carrier round-trips
  for the subnormal (`0x00000002`), overflow (`0x7F800000`, `0x7FF0000000000000`), and `-0.0`
  (`0x80000000`) results. -/
theorem w1_mr_finite_subnormal_overflow :
    evalFloatArithBase .add .binary32 0x00000001 0x00000001 = .some 0x00000002 ∧
    (∃ mem, ReachesRet (mirCallTree (faF32BinBody "w1::subnormal_add_f32" .add) [.scalar ⟨0x00000001, 4⟩, .scalar ⟨0x00000001, 4⟩]) [] (.normal (.scalar ⟨0x00000002, 4⟩, mem))) ∧
    evalFloatArithBase .add .binary64 0x0000000000000001 0x0000000000000001 = .some 0x0000000000000002 ∧
    evalFloatBinOp .add .binary32 0x7F7FFFFF 0x73000000 = .some ⟨0x7F800000, 4⟩ ∧
    evalFloatBinOp .add .binary32 0x7F7FFFFF 0x72FFFFFF = .some ⟨0x7F7FFFFF, 4⟩ ∧
    evalFloatBinOp .add .binary64 0x7FEFFFFFFFFFFFFF 0x7C90000000000000 = .some ⟨0x7FF0000000000000, 8⟩ ∧
    evalFloatBinOp .add .binary64 0x7FEFFFFFFFFFFFFF 0x7C8FFFFFFFFFFFFF = .some ⟨0x7FEFFFFFFFFFFFFF, 8⟩ ∧
    evalFloatArithBase .add .binary32 (zeroBits .binary32 true) (zeroBits .binary32 true) = .some (zeroBits .binary32 true) ∧
    evalFloatArithBase .add .binary32 (zeroBits .binary32 true) (zeroBits .binary32 false) = .some (zeroBits .binary32 false) ∧
    evalFloatArithBase .sub .binary32 (zeroBits .binary32 true) (zeroBits .binary32 false) = .some (zeroBits .binary32 true) ∧
    Type.encode (.Int fcU32It) (.Int 0x00000002) = .ok ((encodeLittleEndianBytes 0x00000002 4 none).map fcByteToMR) ∧
    Type.decode (.Int fcU32It) ((encodeLittleEndianBytes 0x7F800000 4 none).map fcByteToMR) = .ok (some (.Int 0x7F800000)) ∧
    transmuteM (M := BM) (.Int 0x80000000) (.Int fcU32It) (.Int fcI32It) = .ok (.Int (-2147483648)) ∧
    transmuteM (M := TBM) (.Int 0x7FF0000000000000) (.Int fcU64It) (.Array (.Int fcU8It) 8) = .ok (.Tuple (fcLeByteValsMRM 0x7FF0000000000000 8)) := by
  have hov := evalFloatBinOp_overflow_tie_witness
  have hszTT := evalFloatArithBase_signed_zero_sums .binary32 true true
  have hszTF := evalFloatArithBase_signed_zero_sums .binary32 true false
  refine ⟨by decide +kernel, ⟨_, runA_sound _ 10 _ _ _ rfl⟩, by decide +kernel,
    hov.1, hov.2.1, hov.2.2.2.2.1, hov.2.2.2.2.2.1, hszTT.1, hszTF.1, hszTF.2,
    fc_mr_encode_eq_anneal .Unsigned 4 0x00000002 fc_goodSize_4 (by decide),
    fc_mr_decode_eq_anneal .Unsigned 4 0x7F800000 none (by decide),
    fc_mrBM_transmute_int .Unsigned .Signed 4 0x80000000 fc_goodSize_4 (by decide) none,
    (fc_mrM_transmute_int_bytes8 (M := TBM) .Unsigned 0x7FF0000000000000 (by decide) none).1⟩
/-- **`W2` — IEEE-754 Comparisons (`Bool` Carrier) & Signaling-NaN-Preserving `UnOp.neg` XOR
Carrier on `Mach` & `MachTB` (`wfLive`)**:
- `-0.0 == +0.0` is `true`, `qNaN == qNaN` is `false`, `qNaN != qNaN` is `true`, and `boolToScalar`
  round-trips through MiniRust `Bool ↔ u8` across both `BM` and `TBM`;
- Signaling NaN negation (`0x7F800001_f32 → 0xFF800001_f32`, `0x7FF0000000000001_f64 →
  0xFFF0000000000001_f64`, `cl/1023458250`) preserves the signaling bit (`isSignalingNaNBits`) and
  runs in exact byte-for-byte lockstep between Anneal (`faF32NegBitsBody`/`faF64NegBitsBody`) and
  MiniRust's XOR carriers (`faNegXorU32Body`/`faNegXorU64Body`) across BOTH `Mach` (`Interp.steps`)
  and `MachTB` (`Interp.stepsTB` + `MachTB.wfLive`)! -/
theorem w2_mr_cmp_and_snan_neg_xor_carrier :
    -- IEEE-754 comparisons & Bool carrier
    evalFloatCmp .eq .binary32 (zeroBits .binary32 true) (zeroBits .binary32 false) = .some true ∧
    evalFloatCmp .eq .binary32 0x7FC00000 0x7FC00000 = .some false ∧
    evalFloatCmp .ne .binary32 0x7FC00000 0x7FC00000 = .some true ∧
    Type.encode .Bool (.Bool true) =
      .ok ((encodeLittleEndianBytes (boolToScalar true).bits 1 none).map fcByteToMR) ∧
    transmuteM (M := BM) (.Bool false) .Bool (.Int fcU8It) = .ok (.Int 0) ∧
    transmuteM (M := TBM) (.Bool true) .Bool (.Int fcU8It) = .ok (.Int 1) ∧
    -- sNaN-preserving UnOp.neg (f32 and f64)
    isSignalingNaNBits .binary32 0x7F800001 = true ∧
    isSignalingNaNBits .binary32 (evalFloatNeg .binary32 0x7F800001) = true ∧
    evalFloatNeg .binary32 0x7F800001 = 0xFF800001 ∧
    isSignalingNaNBits .binary64 0x7FF0000000000001 = true ∧
    isSignalingNaNBits .binary64 (evalFloatNeg .binary64 0x7FF0000000000001) = true ∧
    evalFloatNeg .binary64 0x7FF0000000000001 = 0xFFF0000000000001 ∧
    -- Anneal + Mach + MachTB + wfLive lockstep on sNaN negation
    (∃ mem, ReachesRet (mirCallTree faF32NegBitsBody [.scalar ⟨0x7F800001, 4⟩]) []
      (.normal (.scalar ⟨0xFF800001, 4⟩, mem))) ∧
    retAfter faNegXorU32Body [.scalar ⟨0x7F800001, 4⟩] 3 =
      some (some { retAlloc with data := (encodeLittleEndianBytes 0xFF800001 4 none).map fcByteToMR },
        [1]) ∧
    retAfterTB faNegXorU32Body [.scalar ⟨0x7F800001, 4⟩] 3 = tbRetU32 0xFF800001 ∧
    (∃ m0 m', startMachineTB faNegXorU32Body [.scalar ⟨0x7F800001, 4⟩] = some m0 ∧
      Interp.stepsTB 3 m0 = .ok m' ∧ MachTB.wfLive m') ∧
    (∃ mem, ReachesRet (mirCallTree faF64NegBitsBody [.scalar ⟨0x7FF0000000000001, 8⟩]) []
      (.normal (.scalar ⟨0xFFF0000000000001, 8⟩, mem))) ∧
    fcRetAfter8 faNegXorU64Body [.scalar ⟨0x7FF0000000000001, 8⟩] 3 =
      some (some { fcRetAlloc8 with
        data := (encodeLittleEndianBytes 0xFFF0000000000001 8 none).map fcByteToMR }, [1]) ∧
    fcRetAfterTB8 faNegXorU64Body [.scalar ⟨0x7FF0000000000001, 8⟩] 3 =
      tbRetU64 0xFFF0000000000001 ∧
    (∃ m0 m', fcStartMachineTB8 faNegXorU64Body [.scalar ⟨0x7FF0000000000001, 8⟩] = some m0 ∧
      Interp.stepsTB 3 m0 = .ok m' ∧ MachTB.wfLive m') := by
  have htb := fa_negXor_f32_f64_machTB_wfLive
  have h32 := (fa_sym_f32_neg_bits 0x7F800001 (by decide)).2.2.1
  have h64 := (fa_sym_f64_neg_bits 0x7FF0000000000001 (by decide)).2.2.1
  exact ⟨(evalFloatCmp_signed_zeros_eq .binary32 true false).1, rfl, rfl, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, rfl, by decide +kernel, by decide +kernel, rfl,
    h32, htb.1, htb.2.1, htb.2.2.1, h64, htb.2.2.2.2.2.2.2.1, htb.2.2.2.2.2.2.2.2.1,
    htb.2.2.2.2.2.2.2.2.2.1⟩
/-- **`W3` — `nanChoices` `.deterministic` vs. `.nondeterministic` Carrier Witness**:
- Quiet NaN `0x7FC00001` yields 4 `.nondeterministic` choices vs. signaling NaN `0x7F800001`
  yielding 6 `.nondeterministic` choices (`nanChoices_4_qnan_vs_6_snan_witness`), whereas
  `.deterministic` pins the single preferred NaN `[0x7FC00000]`;
- For `0x7FA00001 + 1.0`, `EvalFloatBinOpRel .nondeterministic` admits all 6 NaN payloads while
  `EvalFloatBinOpRel .deterministic` admits only `0x7FC00000`;
- Every single candidate in both modes round-trips through MiniRust `Type.encode`/`Type.decode`/
  `transmuteM` across `BM` & `TBM` AND runs through `Mach` (`Interp.steps`) to Anneal's exact
  little-endian bytes! -/
theorem w3_mr_nanChoices_det_vs_nondet :
    (nanChoices .binary32 [(.binary32, 0x7FC00001)] .nondeterministic).length = 4 ∧
    (nanChoices .binary32 [(.binary32, 0x7F800001)] .nondeterministic).length = 6 ∧
    nanChoices .binary32 [(.binary32, 0x7FA00001), (.binary32, 0x3F800000)] .deterministic =
      [0x7FC00000] ∧
    nanChoices .binary32 [(.binary32, 0x7FA00001), (.binary32, 0x3F800000)] .nondeterministic =
      [0x7FC00000, 0xFFC00000, 0x7FE00001, 0xFFE00001, 0x7FA00001, 0xFFA00001] ∧
    (∀ mode cand,
      cand ∈ nanChoices .binary32 [(.binary32, 0x7FA00001), (.binary32, 0x3F800000)] mode →
      EvalFloatBinOpRel mode .add .binary32 0x7FA00001 0x3F800000 ⟨cand, 4⟩ ∧
      Type.encode (.Int fcU32It) (.Int (cand : Int)) =
        .ok ((encodeLittleEndianBytes cand 4 none).map fcByteToMR) ∧
      transmuteM (M := BM) (.Int (cand : Int)) (.Int fcU32It) (.Int fcI32It) =
        .ok (.Int (intFromBits cand fcI32It)) ∧
      transmuteM (M := TBM) (.Int (cand : Int)) (.Int fcU32It) (.Array (.Int fcU8It) 4) =
        .ok (.Tuple (fcLeByteValsMRM cand 4)) ∧
      ∃ (m : Mach) (n : Nat) (m' : Mach),
        startMachine fcCarrierCastBody [.scalar ⟨cand, 4⟩] = some m ∧
        Interp.steps n m = .ok m' ∧
        m'.mem.memory.allocations[0]? =
          some { retAlloc with data := (encodeLittleEndianBytes cand 4 none).map fcByteToMR }) := by
  have h46 := nanChoices_4_qnan_vs_6_snan_witness
  have hbase : evalFloatArithBase .add .binary32 0x7FA00001 0x3F800000 = .some 0x7FC00000 := by
    decide +kernel
  have hnan : isNaNBits .binary32 0x7FC00000 = true := by decide +kernel
  refine ⟨h46.1, h46.2.1, by decide +kernel, by decide +kernel, fun mode cand hmem => ?_⟩
  have hrel : EvalFloatBinOpRel mode .add .binary32 0x7FA00001 0x3F800000 ⟨cand, 4⟩ :=
    (EvalFloatBinOpRel_of_base_nan mode .add .binary32 0x7FA00001 0x3F800000 0x7FC00000
      ⟨cand, 4⟩ rfl hbase hnan).mpr ⟨cand, hmem, rfl⟩
  have hcar := fa_bridge_nanChoices_carriers mode .binary32
    [(.binary32, 0x7FA00001), (.binary32, 0x3F800000)] cand hmem
  have hmach := (fa_bridge_evalFloatBinOpRel_mach_steps mode .add 0x7FA00001 0x3F800000
    ⟨cand, 4⟩ rfl).1 hrel
  exact ⟨hrel, hcar.2.2.1, hcar.2.2.2.2.1, hcar.2.2.2.2.2.2.1, hmach.2⟩
/-- **`W4` — Uninit Float UB, `1.0 / 0.0 = +Inf` vs. Int `/ 0` UB, and No-Float-Local Cmp
Rejection** (choice-free): uninit float local faults `.ub`; `1.0_f32 / +0.0_f32 = +Inf` is UB-free
(contrasting with `faIntDivZeroBody` UB on `Mach`/`MachTB`/Anneal); no-float-local comparisons
pass `translateLocals` yet fail all six MiniRust checks while Anneal evaluates them cleanly. -/
theorem w4_mr_uninit_divzero_and_no_float_local_rejection :
    -- Uninit float local UB in Anneal
    faultsA faUninitFloatNegBody 5 (initMachineState faUninitFloatNegBody [.scalar ⟨0, 4⟩]) = true ∧
    ¬ MirNoUBTree (mirCallTree faUninitFloatNegBody [.scalar ⟨0, 4⟩]) ∧
    -- 1.0_f32 / +0.0_f32 = +Inf in Anneal (UB-free!)
    evalFloatArithBase .div .binary32 0x3F800000 (zeroBits .binary32 false) =
      .some (infBits .binary32 false) ∧
    (∃ mem, ReachesRet (mirCallTree (faF32BinBody "w4::div_by_zero_f32" .div)
      [.scalar ⟨0x3F800000, 4⟩, .scalar ⟨0x00000000, 4⟩]) []
      (.normal (.scalar ⟨0x7F800000, 4⟩, mem))) ∧
    MirNoUBTree (mirCallTree (faF32BinBody "w4::div_by_zero_f32" .div)
      [.scalar ⟨0x3F800000, 4⟩, .scalar ⟨0x00000000, 4⟩]) ∧
    -- Contrast: MiniRust & Anneal integer division by zero is UB on Mach and MachTB!
    faultsA faIntDivZeroBody 5 (initMachineState faIntDivZeroBody [.scalar ⟨1, 4⟩]) = true ∧
    ¬ MirNoUBTree (mirCallTree faIntDivZeroBody [.scalar ⟨1, 4⟩]) ∧
    ubAfter faIntDivZeroBody [.scalar ⟨1, 4⟩] 2 = some "division by zero" ∧
    ubAfterTB faIntDivZeroBody [.scalar ⟨1, 4⟩] 2 = some "division by zero" ∧
    -- No-float-local comparison rejection (1.0 == -0.0, -0.0 == +0.0, qNaN == qNaN)
    (translateLocals faConstCmpOneNegZeroBody.layouts 0
      faConstCmpOneNegZeroBody.localDecls).isSome = true ∧
    translateFn faConstCmpOneNegZeroBody = none ∧
    inFragment faConstCmpOneNegZeroBody = false ∧
    progInFragmentWithIntrinsics faConstCmpOneNegZeroBody [] = false ∧
    translateFn faConstCmpSignedZerosBody = none ∧
    translateFn faConstCmpQNaNBody = none ∧
    (∃ mem, ReachesRet (mirCallTree faConstCmpOneNegZeroBody []) []
      (.normal (.scalar (boolToScalar false), mem))) ∧
    (∃ mem, ReachesRet (mirCallTree faConstCmpSignedZerosBody []) []
      (.normal (.scalar (boolToScalar true), mem))) ∧
    (∃ mem, ReachesRet (mirCallTree faConstCmpQNaNBody []) []
      (.normal (.scalar (boolToScalar false), mem))) := by
  have hb := fa_anneal_float_ops_and_fail_closed_boundary
  have hnf := fa_no_float_local_cmp_two_sided_boundary
  have hdiv : evalFloatArithBase .div .binary32 0x3F800000 (zeroBits .binary32 false) =
      .some (infBits .binary32 false) := by decide +kernel
  refine ⟨hb.2.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.2.1, hdiv,
    ⟨_, runA_sound _ 10 _ _ _ rfl⟩, runA_noUB _ 10 _ _ _ rfl,
    rfl, ?_, by decide +kernel, by decide +kernel,
    hnf.1, hnf.2.2.2.1.1, hnf.2.2.2.1.2.2.1, hnf.2.2.2.1.2.2.2.2.2,
    hnf.2.2.2.2.1.1, hnf.2.2.2.2.2.1.1,
    hnf.2.2.2.2.2.2.1, hnf.2.2.2.2.2.2.2.2.1, hnf.2.2.2.2.2.2.2.2.2.2.1⟩
  obtain ⟨tr, u, hr, hf⟩ :=
    faultsA_sound faIntDivZeroBody 5 (initMachineState faIntDivZeroBody [.scalar ⟨1, 4⟩]) rfl
  exact fun hsafe => hsafe tr u hr hf
/-- **`W5` — `Ptr2IntTransmutePolicy` `.stripProvenance` Lockstep vs. `.strictUcg630Ub` UB Flip
on `Mach` & `MachTB` (`wfLive`)**: scalar `*const u32 → u64` (`faPtrToU64Body`) and composite
`(*const u8, *const u8) → (*const u8, usize)` / `struct Mixed` selective provenance preservation
and stripping across Anneal, `BM`, `TBM`, `Mach`, and `MachTB`. -/
theorem w5_mr_ptr2int_policy_flip_mach_and_machTB :
    let pA : ProvenancePtr := { allocId := 7, offsetBytes := 0x1000 }
    let pB : ProvenancePtr := { allocId := 9, offsetBytes := 0x2000 }
    let tupLocals : List LocalSlot := [.init (.aggregate 0 [.ptr pA 8, .ptr pB 8])]
    let tupDecls : List LocalDecl := [fcDecl faPolPtrPtrTupTy]
    -- Live Mach + MachTB + wfLive scalar pointer -> u64 flip
    fcRetAfter8 faPtrToU64Body [.scalar ⟨7, 4⟩] 6 =
      some (some { fcRetAlloc8 with data := (encodeLittleEndianBytes 256 8 none).map fcByteToMR },
        [1]) ∧
    fcRetAfterTB8 faPtrToU64Body [.scalar ⟨7, 4⟩] 6 = tbRetU64 256 ∧
    (∃ m0 m', fcStartMachineTB8 faPtrToU64Body [.scalar ⟨7, 4⟩] = some m0 ∧
      Interp.stepsTB 6 m0 = .ok m' ∧ MachTB.wfLive m') ∧
    faultsA faPtrToU64Body 10 (initMachineState faPtrToU64Body [.scalar ⟨7, 4⟩]) = true ∧
    evalByteCast [.init (.ptr { allocId := 2, offsetBytes := 256 } 8)]
        (.copy (local_ 0)) fcU64Ty emptyMemory [fcDecl fcRawPtrU32Ty] fcLayouts .strictUcg630Ub =
      .ub ∧
    evalByteCast [.init (.ptr { allocId := 2, offsetBytes := 256 } 8)]
        (.copy (local_ 0)) fcU64Ty emptyMemory [fcDecl fcRawPtrU32Ty] fcLayouts .stripProvenance =
      .ok (.scalar ⟨256, 8⟩)
        [.init (.ptr { allocId := 2, offsetBytes := 256 } 8)] emptyMemory ∧
    -- Composite (*const u8, *const u8) -> (*const u8, usize) & struct Mixed selective flip
    evalByteCast tupLocals (.copy (local_ 0)) faPolPtrUsizeTupTy emptyMemory tupDecls
        faPolicyLayouts .strictUcg630Ub = .ub ∧
    evalByteCast tupLocals (.copy (local_ 0)) faPolPtrUsizeTupTy emptyMemory tupDecls
        faPolicyLayouts .stripProvenance =
      .ok (.aggregate 0 [.ptr pA 8, .scalar ⟨0x2000, 8⟩]) tupLocals emptyMemory ∧
    evalByteCast tupLocals (.copy (local_ 0)) faPolMixedStructTy emptyMemory tupDecls
        faPolicyLayouts .strictUcg630Ub = .ub ∧
    evalByteCast tupLocals (.copy (local_ 0)) faPolMixedStructTy emptyMemory tupDecls
        faPolicyLayouts .stripProvenance =
      .ok (.aggregate 0 [.ptr pA 8, .scalar ⟨0x2000, 8⟩]) tupLocals emptyMemory ∧
    transmuteM (M := BM)
        (.Tuple [.Ptr ⟨⟨0x1000, some (⟨7⟩, ())⟩, none⟩, .Ptr ⟨⟨0x2000, some (⟨9⟩, ())⟩, none⟩])
        faMrPtrPtrTupleTy faMrPtrU64TupleTy =
      .ok (.Tuple [.Ptr ⟨⟨0x1000, some (⟨7⟩, ())⟩, none⟩, .Int 0x2000]) ∧
    transmuteM (M := TBM)
        (.Tuple [.Ptr ⟨⟨0x1000, none⟩, none⟩, .Ptr ⟨⟨0x2000, none⟩, none⟩])
        faMrPtrPtrTupleTy faMrPtrU64TupleTy =
      .ok (.Tuple [.Ptr ⟨⟨0x1000, none⟩, none⟩, .Int 0x2000]) := by
  have hlive := fa_ptr2int_live_mach_and_machTB_wfLive
  have hcomp := fa_composite_tuple_struct_policy_correspondence
    (pA := { allocId := 7, offsetBytes := 0x1000 }) (pB := { allocId := 9, offsetBytes := 0x2000 })
    (by decide) (by decide)
    (locals := [.init (.aggregate 0
      [.ptr { allocId := 7, offsetBytes := 0x1000 } 8,
       .ptr { allocId := 9, offsetBytes := 0x2000 } 8])])
    (locals' := [.init (.aggregate 0
      [.ptr { allocId := 7, offsetBytes := 0x1000 } 8,
       .ptr { allocId := 9, offsetBytes := 0x2000 } 8])])
    (op := .copy (local_ 0)) (mem := emptyMemory) (decls := [fcDecl faPolPtrPtrTupTy])
    rfl rfl (some (⟨7⟩, ())) (some (⟨9⟩, ())) none none
  exact ⟨hlive.1, hlive.2.1, hlive.2.2.1, hlive.2.2.2.1, hlive.2.2.2.2.2.1, hlive.2.2.2.2.2.2,
    hcomp.1, hcomp.2.1, hcomp.2.2.1, hcomp.2.2.2.1, hcomp.2.2.2.2.1, hcomp.2.2.2.2.2⟩
/-- **`W6` — Shared No-Forgery (`usize → &u8`) & Uninit-Byte UB Under BOTH Policies With
`MachTB.wfLive`**: `usize → &u8` (`0` and `256`) and uninitialized `u64` / `MaybeUninit<u64>`
transmute fault `.ub` under both policies, matching `transmuteM` (`BM`/`TBM`) and live `Mach`/
`MachTB` (+ `MachTB.wfLive` before the UB step). -/
theorem w6_mr_no_forge_ref_uninit :
    -- Both policies fault .ub on usize -> &u8 (256)
    (∀ mode policy,
      evalByteCast [.init (.scalar ⟨256, 8⟩)] (.copy (local_ 0)) faPolRefU8Ty emptyMemory
          [fcDecl faPolUsizeTy] faPolicyLayouts policy = .ub ∧
      EvalRvalueFloatRel mode policy [.init (.scalar ⟨256, 8⟩)]
          (.cast .transmute (.copy (local_ 0)) faPolRefU8Ty) emptyMemory [fcDecl faPolUsizeTy]
          faPolicyLayouts .ub) ∧
    -- MiniRust transmuteM (BM & TBM) & live Mach / MachTB / wfLive on usize -> &u8
    transmuteM (M := BM) (.Int 256) (.Int fcU64It) faMrRefU8Ty =
      .error (.ub "Value::Ptr: non-dereferenceable safe pointer") ∧
    transmuteM (M := TBM) (.Int 0) (.Int fcU64It) faMrRefU8Ty =
      .error (.ub "Value::Ptr: null safe pointer") ∧
    faUbAfter8 faUsizeToRefU8Body [.scalar ⟨0, 8⟩] 3 = some "Value::Ptr: null safe pointer" ∧
    faUbAfterTB8 faUsizeToRefU8Body [.scalar ⟨0, 8⟩] 3 = some "Value::Ptr: null safe pointer" ∧
    faUbAfter8 faUsizeToRefU8Body [.scalar ⟨256, 8⟩] 3 =
      some "Value::Ptr: non-dereferenceable safe pointer" ∧
    faUbAfterTB8 faUsizeToRefU8Body [.scalar ⟨256, 8⟩] 3 =
      some "Value::Ptr: non-dereferenceable safe pointer" ∧
    (∃ m0 m', fcStartMachineTB8 faUsizeToRefU8Body [.scalar ⟨256, 8⟩] = some m0 ∧
      Interp.stepsTB 2 m0 = .ok m' ∧ MachTB.wfLive m') ∧
    -- Both policies fault .ub on uninit u64 transmute (decoder + live Mach & MachTB + wfLive)
    (∀ policy,
      decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolU64Ty
        (List.replicate 8 .uninit) policy = none) ∧
    faUbAfter8 faUninitTransmuteU64Body [.scalar ⟨0, 8⟩] 3 =
      some "load at type but the data in memory violates the language invariant" ∧
    faUbAfterTB8 faUninitTransmuteU64Body [.scalar ⟨0, 8⟩] 3 =
      some "load at type but the data in memory violates the language invariant" ∧
    (∃ m0 m', fcStartMachineTB8 faUninitTransmuteU64Body [.scalar ⟨0, 8⟩] = some m0 ∧
      Interp.stepsTB 2 m0 = .ok m' ∧ MachTB.wfLive m') := by
  have hsh := fa_shared_ub_no_forge_both_policies
    (locals := [.init (.scalar ⟨256, 8⟩), .uninit]) (locals' := [.init (.scalar ⟨256, 8⟩), .uninit]) (op64 := .copy (local_ 0)) (opUninit := .copy (local_ 1))
    (mem := emptyMemory) (decls := [fcDecl faPolUsizeTy, fcDecl faPolU64Ty]) (addr := 256) (by decide) rfl rfl rfl none none
  have hlive := fa_no_forge_ref_and_uninit_live_mach_and_machTB_wfLive
  have hzero := (fa_mrM_transmute_u64_to_refU8_ub 0 (by decide) none none).2
  refine ⟨fun mode policy => ⟨by cases policy <;> rfl,
      (EvalRvalueFloatRel_byteCast_iff mode policy _ .transmute (.copy (local_ 0)) faPolRefU8Ty
        emptyMemory [fcDecl faPolUsizeTy] faPolicyLayouts .ub (.inl rfl)).mpr
        (by cases policy <;> rfl)⟩,
    hsh.2.1, hzero,
    hlive.2.2.2.2.2.1, hlive.2.2.2.2.2.2.1, hlive.2.2.2.2.2.2.2.1, hlive.2.2.2.2.2.2.2.2.1,
    hlive.2.2.2.2.2.2.2.2.2.1,
    fun policy => (hsh.2.2.2.1 policy).1,
    hlive.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hlive.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hlive.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
/-! ### §4.1 Complete `#guard_msgs` Axiom Audit (100% of Public Theorems)
`axiomAudit_choiceFree` pins every non-machine public theorem to `[propext, Quot.sound]`;
`axiomAudit_machine` pins every machine/simulation public theorem to `[propext, Classical.choice, Quot.sound]`. -/

section AxiomGuards
set_option linter.defProp false in
/-- Complete choice-free axiom-audit bundle covering every non-machine public theorem in §1–§4. -/
def axiomAudit_choiceFree :=
  And.intro (@Anneal.Mir.IeeeFloatCast.pack_unpack_f32) <|
  -- §1 Fail-closed translation & Anneal boundary (including §1.0b general projected-place F5 closure)
  And.intro (@fa_operandType_float_operand) <| And.intro (@fa_operandIntType_float_operand) <|
  And.intro (@fa_translateRvalue_unaryOp_float) <| And.intro (@fa_translateRvalue_binaryOp_float_const) <|
  And.intro (@fa_translateRvalue_binaryOp_arith_float) <| And.intro (@fa_translateRvalue_relOp_local_negative_control) <|
  And.intro (@fa_translateStatement_float_unary_or_binary) <| And.intro (@fa_statementOk_all_preds_float_op_eq_false) <|
  And.intro (@fa_no_fragment_admits_float_arith_or_cmp) <| And.intro (@fa_projected_float_place_rejection) <|
  And.intro (@fa_no_fragment_admits_projected_float_op) <| And.intro (@fa_no_float_local_cmp_two_sided_boundary) <|
  And.intro (@fa_anneal_float_ops_and_fail_closed_boundary) <|
  -- §2 Bitwise UnOp.neg <-> XOR, symbolic Anneal pipelines, Bool & EvalFloatBinOpRel carriers
  And.intro (@fa_evalFloatNeg_eq_natXor_f32) <| And.intro (@fa_evalFloatNeg_eq_natXor_f64) <|
  And.intro (@fa_bitwiseXorBits_two_pow) <| And.intro (@fa_evalFloatNeg_eq_bitwiseXorBits_f32) <|
  And.intro (@fa_evalFloatNeg_eq_bitwiseXorBits_f64) <| And.intro (@fa_intBitXor_nat) <|
  And.intro (@fa_mrM_evalBinOpM_negXor) <| And.intro (@fa_run_f32_neg_bits_raw) <|
  And.intro (@fa_run_f64_neg_bits_raw) <| And.intro (@fa_sym_f32_neg_bits) <|
  And.intro (@fa_sym_f64_neg_bits) <| And.intro (@fa_negXorU32_translate) <|
  And.intro (@fa_negXorU32_inFragment) <| And.intro (@fa_negXorU32_ctxOk) <|
  And.intro (@fa_negXorU32_argsOk) <| And.intro (@fa_run_negXorU32_raw) <|
  And.intro (@fa_negXorU64_translate) <| And.intro (@fa_negXorU64_inFragment) <|
  And.intro (@fa_negXorU64_ctxOk) <| And.intro (@fa_negXorU64_argsOk) <|
  And.intro (@fa_run_negXorU64_raw) <| And.intro (@fa_mrM_bool_codec) <|
  And.intro (@fa_bridge_floatCmp) <| And.intro (@fa_bridge_nanChoices_carriers) <|
  And.intro (@fa_bridge_evalFloatBinOpRel_carriers) <|
  -- §3 Ptr2IntTransmutePolicy & composite / no-forgery / uninit / size-mismatch correspondence
  And.intro (@fa_evalByteCast_eq) <| And.intro (@fa_evalByteCast_of_encode) <|
  And.intro (@fa_mrM_transmute_ptr_strip) <| And.intro (@fa_decodeTyped_ptr_bytes_policy_flip) <|
  And.intro (@fa_ptr2int_policy_flip_scalar_correspondence) <| And.intro (@fa_mrM_transmute_ptr_tuple_selective) <|
  And.intro (@fa_composite_tuple_struct_policy_correspondence) <| And.intro (@fa_provFree_policy_equivalence_correspondence) <|
  And.intro (@fa_mrM_transmute_u64_to_refU8_ub) <| And.intro (@fa_shared_ub_no_forge_both_policies) <|
  And.intro (@fa_ptrToU64_translate) <| And.intro (@fa_usizeToRefU8_translate) <|
  And.intro (@fa_uninitTransmuteU64_translate) <| And.intro (@fa_intDivZero_translate) <|
  -- §4 Choice-free concrete witnesses W1 & W4
  And.intro (@w1_mr_finite_subnormal_overflow) <| @w4_mr_uninit_divzero_and_no_float_local_rejection
/--
info: 'MiniRustSpec.FloatArithMR.axiomAudit_choiceFree' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms axiomAudit_choiceFree

set_option linter.defProp false in
/-- Complete machine-level axiom-audit bundle covering every public theorem invoking `mirCall_ret`
or `TbWitness.liftMachToTB_stepsTB_wfLive`. -/
def axiomAudit_machine :=
  And.intro (@fa_sym_mr_negXor_f32_lockstep) <| And.intro (@fa_sym_mr_negXor_f64_lockstep) <|
  And.intro (@fa_negXor_f32_f64_machTB_wfLive) <| And.intro (@fa_bridge_evalFloatBinOpRel_mach_steps) <|
  And.intro (@fa_ptr2int_live_mach_and_machTB_wfLive) <| And.intro (@fa_no_forge_ref_and_uninit_live_mach_and_machTB_wfLive) <|
  And.intro (@w2_mr_cmp_and_snan_neg_xor_carrier) <| And.intro (@w3_mr_nanChoices_det_vs_nondet) <|
  And.intro (@w5_mr_ptr2int_policy_flip_mach_and_machTB) <| @w6_mr_no_forge_ref_uninit
/--
info: 'MiniRustSpec.FloatArithMR.axiomAudit_machine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms axiomAudit_machine

end AxiomGuards

end MiniRustSpec.FloatArithMR
