/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.CallLM4_2

/-!
# `write_bytes` Call Correspondence for `LM-4.2`

One-step correspondence between Anneal's `stepMirFn` (`evalWriteBytesCall`) and
`lean-miri`'s `Miri.Interpreter.Step.step` (`annealWriteBytesEval` /
`annealWriteRepeatedBytes`) on a translated `TerminatorKind.call` to
`core::intrinsics::write_bytes::<T>(dst, val, count)` from `StateRelLM3_1`:

* `call_intrinsic_write_bytes_simulation` proves one-step `StepRelLM3_1`
  simulation preserving `allocMap` (when any live in-bounds positive write uses
  an active borrow with foreign borrows on that local already disabled), and
  `call_intrinsic_write_bytes_simulation_explicit` generalizes live in-bounds
  positive writes to `.active` or `.reserved` borrows under
  `writeBytesNextAllocMap`:
  1. `count * size_of::<T>() > isize::MAX` (`isizeMaxBytes`) reports UB in both
     machines;
  2. `count * size_of::<T>() = 0` steps to `(targetBb, 0)` without mutating
     memory or `dstIdx`, preserving `StateRelLM3_1` even on provenance-free,
     dangling, dead, or out-of-bounds pointers;
  3. uninitialized or dead `dst` / `val` / `count`, provenance-free `.scalar`
     `dst` on positive size, or a dead target stack allocation on positive size
     reports UB in both machines;
  4. `dst` holding a `PtrRel`-related `.ptr ptrVal 8` into an address-taken
     primitive integer local (`StackScalarAllocShape`) reports UB in both
     machines on out-of-bounds positive size (`targetBytes < offset + total`),
     writes `repeatByteBits` while preserving `StateRelLM3_1` on whole-local
     in-bounds fills (`offset = 0`, `total = targetBytes`, whether previously
     `.uninit` or `.init`), and splices `[offset, offset + total)` via
     `spliceRepeatedBytes` while preserving surrounding bytes and
     `StateRelLM3_1` on partial in-bounds fills into an initialized scalar
     local (`∃ oldSc, get? s.frame.locals e.localIdx = some (.init (.scalar oldSc))`).
     Only partial fills into an `.uninit` scalar local remain outside
     `hlive_inbounds` scope (Miri tracks per-byte `InitMask`, whereas Anneal's
     `LocalSlot` tracks whole-local initialization).
* Characterized divergences and shared modeling gaps:
  - **Tree Borrows permissions (`call_intrinsic_write_bytes_perm_divergence`)**:
    on a live in-bounds whole-local fill through a `.frozen` or `.disabled`
    borrow entry, Anneal fails with `.ub` while `lean-miri`'s
    `annealWriteRepeatedBytes` (which checks allocation liveness, bounds, and
    mutability without Tree Borrows transitions) steps with `.ok true`.
  - **Pointer alignment**: neither Anneal's `evalWriteBytesCall` nor
    `lean-miri`'s `annealWriteRepeatedBytes` (matching `write_bytes_intrinsic`
    in `rustc_const_eval`) checks alignment of `dst` to `align_of::<T>()`.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Anneal side -/

/-- `evalInlineIntrinsicCall?` on `core::intrinsics::write_bytes`. -/
theorem evalInlineIntrinsicCall?_writeBytes (s : MachineState) (argOps : List MirAst.Operand)
    (argVals : List Value) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalInlineIntrinsicCall? s AnnealIntrinsic.writeBytes.defPath argOps argVals locals'
        destination targetBb localDecls layouts =
      some (match argOps, argVals with
        | dstOp :: _ :: _ :: .nil, dstVal :: .scalar val :: .scalar count :: .nil =>
          evalWriteBytesCall s dstOp dstVal val count locals' targetBb localDecls layouts
        | _, _ => MirStepNode.unsupported) := by
  rfl

/-- The pointee size of a copied raw-pointer local. -/
theorem operandPointeeBytes?_copy_rawPtr {localDecls : List LocalDecl} {layouts : LayoutTable}
    {ptrIdx : Local} {ptrDecl : LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    {elemBytes : Nat}
    (hdecl : get? localDecls ptrIdx = some ptrDecl)
    (hty : ptrDecl.ty.kind = .rawPtr mutability pointeeKind)
    (hsize : rigidTyKindByteSize pointeeKind = some elemBytes) :
    operandPointeeBytes? localDecls layouts (.copy ⟨ptrIdx, []⟩) = some elemBytes := by
  simp [operandPointeeBytes?, operandTy, placeTy, hdecl, resolveProjectedTy, pointeeTyOf, hty,
    hsize]

theorem writeBytes_arity : AnnealIntrinsic.writeBytes.arity = 3 := rfl

private theorem wbEvalOperand_copy_local_eq (locals : List LocalSlot) (idx : Local)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation) (ly : LayoutTable)
    (callerLocals : List LocalSlot) :
    evalOperand locals (.copy ⟨idx, .nil⟩) borrows globals ly callerLocals =
      match get? locals idx with
      | some (.init v) => .ok v locals
      | _ => .ub := by
  unfold evalOperand
  dsimp only
  cases get? locals idx with
  | none => rfl
  | some slot => cases slot <;> rfl

/-- Repeating a byte `b < 256` across `n` bytes yields a canonical `n`-byte
unsigned integer. -/
theorem repeatByteBits_lt_scalarModulus {b : Nat} (hb : b < 256) :
    ∀ n : Nat, repeatByteBits b n < scalarModulus n
  | 0 => by simp [repeatByteBits, scalarModulus]
  | k + 1 => by
    have ih := repeatByteBits_lt_scalarModulus hb k
    simp only [repeatByteBits, scalarModulus, Nat.add_eq, Nat.mul_eq]
    omega

/-- Whole-local byte fill (`off = 0`, `total = targetBytes`) overwrites any old
scalar bits with `fill`. -/
theorem evalWriteBytesCall_full_merge (oldBits fill targetBytes : Nat) :
    let lowMod := scalarModulus 0
    let highMod := scalarModulus (Nat.add 0 targetBytes)
    let old := wrapScalarBits oldBits (scalarModulus targetBytes)
    Nat.add (Nat.mod old lowMod)
      (Nat.add (Nat.mul fill lowMod) (Nat.mul (Nat.div old highMod) highMod)) = fill := by
  have hpos : 0 < scalarModulus targetBytes := by
    induction targetBytes with
    | zero => decide
    | succ k ih => simp only [scalarModulus, Nat.mul_eq]; omega
  have hlt : wrapScalarBits oldBits (scalarModulus targetBytes) < scalarModulus targetBytes := by
    unfold wrapScalarBits
    cases hble : (scalarModulus targetBytes).ble oldBits
    · dsimp only
      exact Nat.lt_of_not_ge (fun hle => Bool.noConfusion ((Nat.ble_eq.mpr hle).symm.trans hble))
    · dsimp only
      exact Nat.mod_lt _ hpos
  have hdiv : wrapScalarBits oldBits (scalarModulus targetBytes) / scalarModulus targetBytes = 0 :=
    Nat.div_eq_of_lt hlt
  change (wrapScalarBits oldBits (scalarModulus targetBytes)) % 1 +
    (fill * 1 + (wrapScalarBits oldBits (scalarModulus targetBytes) /
      scalarModulus (0 + targetBytes)) * scalarModulus (0 + targetBytes)) = fill
  rw [Nat.zero_add, Nat.mod_one, hdiv, Nat.mul_one, Nat.zero_mul, Nat.add_zero, Nat.zero_add]

/-! ## 2. Pointee type and `lean-miri` operand / size extraction -/

/-- Pointee type and byte-size agreement across Anneal (`rigidTyKindByteSize`) and
`lean-miri` (`rawPtrPointeeEncodedTyId?` / `layoutOfEncodedTyId`). -/
structure WriteBytesPointee (ly : LayoutTable) (pointeeKind : RigidTy)
    (ptId : Miri.MIR.TyId) (elemBytes : Nat) : Prop where
  encoded_eq : rawPtrPointeeEncodedTyId? (encodeRawPtrTyId pointeeKind) = some ptId
  anneal_size : rigidTyKindByteSize pointeeKind = some elemBytes
  miri_size : (layoutOfEncodedTyId ptId ly).layout.size =
    Miri.ABI.Size.ofBytes (UInt64.ofNat elemBytes)
  lt_u64 : elemBytes < 2 ^ 64

/-- Every primitive scalar type (`bool`, `char`, `i8`..`i128`, `isize`,
`u8`..`u128`, `usize`) has known matching pointee size on both sides. -/
theorem IsPrimScalarTy.writeBytesPointee {ty : Ty} (hprim : IsPrimScalarTy ty)
    (ly : LayoutTable) :
    ∃ ptId elemBytes, WriteBytesPointee ly ty.kind ptId elemBytes := by
  rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
  · rw [hk]
    exact ⟨1, 1, rfl, rfl, rfl, by decide⟩
  · rw [hk]
    exact ⟨2, 4, rfl, rfl, rfl, by decide⟩
  · rw [hk]
    cases it <;> exact ⟨_, _, rfl, rfl, rfl, by decide⟩
  · rw [hk]
    cases ut <;> exact ⟨_, _, rfl, rfl, rfl, by decide⟩

/-- `annealPointeeTypeOf` on a translated raw-pointer layout. -/
theorem annealPointeeTypeOf_rawPtr {ly : LayoutTable} {ptrDecl : LocalDecl}
    {mutability : Mutability} {pk : RigidTy} {ptId : Miri.MIR.TyId}
    (hty : ptrDecl.ty.kind = .rawPtr mutability pk)
    (hpt : rawPtrPointeeEncodedTyId? (encodeRawPtrTyId pk) = some ptId)
    (m : AnnealStepState) :
    annealPointeeTypeOf (translateTy ptrDecl.ty ly).ty m = .ok ptId m := by
  have henc : (translateTy ptrDecl.ty ly).ty = encodeRawPtrTyId pk := by
    unfold translateTy encodeTyId
    rw [hty]
  rw [henc]
  simp [annealPointeeTypeOf, hpt, pure, EStateM.pure]

private theorem wbIntrinsicPointer_uninit (lay : Miri.Interpreter.LocalLayout)
    (m : AnnealStepState) :
    intrinsicPointer ⟨.immediate .uninit, lay⟩ m =
      .error (.undefinedBehavior "read of uninitialized local") m := rfl

private theorem wbIntrinsicScalar_uninit (lay : Miri.Interpreter.LocalLayout)
    (m : AnnealStepState) :
    intrinsicScalar ⟨.immediate .uninit, lay⟩ m =
      .error (.undefinedBehavior "read of uninitialized local") m := rfl

private theorem wbIntrinsicUsize_uninit (lay : Miri.Interpreter.LocalLayout)
    (m : AnnealStepState) :
    intrinsicUsize ⟨.immediate .uninit, lay⟩ m =
      .error (.undefinedBehavior "read of uninitialized local") m := rfl

private theorem wbIntrinsicPointer_fromPointer (mptr : Miri.Memory.Pointer AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) (m : AnnealStepState) :
    intrinsicPointer
        ⟨.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)), lay⟩ m =
      .ok mptr.withOptionalProvenance m := rfl

private theorem wbIntrinsicPointer_fromScalarInt {sc : MirAst.ScalarInt}
    {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc) (hsz8 : sc.sizeBytes = 8)
    (lay : Miri.Interpreter.LocalLayout) (m : AnnealStepState) :
    intrinsicPointer ⟨.immediate (.scalar (.fromScalarInt msc)), lay⟩ m =
      .ok (Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits)) m := by
  have h := scalar_fromScalarInt_toPointer_eq hrel hsz8
  have hs : intrinsicScalar ⟨.immediate (.scalar (.fromScalarInt msc)), lay⟩ m =
      .ok (.fromScalarInt msc) m := rfl
  unfold intrinsicPointer
  rw [EStateM.bind_eq_ok hs, h]
  rfl

private theorem wbScalar_fromScalarInt_toUInt8 {sc : MirAst.ScalarInt}
    {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc) (hsz1 : sc.sizeBytes = 1) :
    sc.bits < 256 ∧
    (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toUInt8 =
      .ok (UInt8.ofNat sc.bits) := by
  have hlt : sc.bits < 256 := by
    have hc := hrel.canonical
    rw [hsz1] at hc
    simpa [scalarModulus] using hc
  refine ⟨hlt, ?_⟩
  have hsi : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toScalarInt = .ok msc := rfl
  have hbz : ((Miri.ABI.Size.ofBytes 1).bytes == 0) = false := rfl
  have hsz1' : Miri.ABI.Size.ofBytes 1 = translateSizeBytes sc.sizeBytes := by rw [hsz1]; rfl
  have htb : msc.toBits (Miri.ABI.Size.ofBytes 1) = .ok (BitVec.ofNat 128 sc.bits) := by
    rw [hsz1']; exact hrel.toBits_eq
  have hbv : (BitVec.ofNat 128 sc.bits).toNat = sc.bits := by
    rw [BitVec.toNat_ofNat]; omega
  unfold Miri.Memory.Scalar.toUInt8 Miri.Memory.Scalar.toUInt Miri.Memory.Scalar.toBits
  simp only [hbz, Bool.false_eq_true, ↓reduceIte, hsi, htb, hbv,
    Except.mapError, bind, Except.bind, pure, Except.pure]

private theorem wbScalar_fromScalarInt_toTargetUsize {sc : MirAst.ScalarInt}
    {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc) (hsz8 : sc.sizeBytes = 8) :
    sc.bits < 2 ^ 64 ∧
    (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toTargetUsize
        (Miri.ABI.Size.ofBytes 8) =
      .ok (UInt64.ofNat sc.bits) := by
  have hlt : sc.bits < 2 ^ 64 := by
    have hc := hrel.canonical
    rw [hsz8] at hc
    simpa [scalarModulus] using hc
  refine ⟨hlt, ?_⟩
  have hsi : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toScalarInt = .ok msc := rfl
  have hbz : ((Miri.ABI.Size.ofBytes 8).bytes == 0) = false := rfl
  have hsz8' : Miri.ABI.Size.ofBytes 8 = translateSizeBytes sc.sizeBytes := by rw [hsz8]; rfl
  have htb : msc.toBits (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 sc.bits) := by
    rw [hsz8']; exact hrel.toBits_eq
  have hbv : (BitVec.ofNat 128 sc.bits).toNat = sc.bits := by
    rw [BitVec.toNat_ofNat]; omega
  have hfit : ¬ sc.bits > 18446744073709551615 := by omega
  unfold Miri.Memory.Scalar.toTargetUsize Miri.Memory.Scalar.toUInt Miri.Memory.Scalar.toBits
  simp only [hbz, Bool.false_eq_true, ↓reduceIte, hsi, htb, hbv, hfit,
    Except.mapError, bind, Except.bind, pure, Except.pure]

private theorem wbIntrinsicUsize_fromScalarInt {sc : MirAst.ScalarInt}
    {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc) (hsz8 : sc.sizeBytes = 8)
    (lay : Miri.Interpreter.LocalLayout) (m : AnnealStepState) :
    intrinsicUsize ⟨.immediate (.scalar (.fromScalarInt msc)), lay⟩ m =
      .ok (UInt64.ofNat sc.bits) m := by
  have hs : intrinsicScalar ⟨.immediate (.scalar (.fromScalarInt msc)), lay⟩ m =
      .ok (.fromScalarInt msc) m := rfl
  have hsz : Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits =
      Miri.ABI.Size.ofBytes 8 := rfl
  unfold intrinsicUsize
  rw [EStateM.bind_eq_ok hs, hsz, (wbScalar_fromScalarInt_toTargetUsize hrel hsz8).2]
  rfl

/-- `IntegerOps.computeSizeInBytes` with `0x7fff_ffff_ffff_ffff` (`isize::MAX`)
succeeds iff `countBits * elemBytes ≤ isizeMaxBytes`. -/
theorem computeSizeInBytes_writeBytes {elemBytes countBits : Nat}
    (helem : elemBytes < 2 ^ 64) (hcount : countBits < 2 ^ 64) :
    Miri.Interpreter.IntegerOps.computeSizeInBytes
        (Miri.ABI.Size.ofBytes (UInt64.ofNat elemBytes))
        (UInt64.ofNat countBits)
        (Miri.ABI.Size.ofBytes 0x7fff_ffff_ffff_ffff) =
      if countBits * elemBytes ≤ isizeMaxBytes then
        some (Miri.ABI.Size.ofBytes (UInt64.ofNat (countBits * elemBytes)))
      else none := by
  have he : (Miri.ABI.Size.ofBytes (UInt64.ofNat elemBytes)).bytes.toNat = elemBytes :=
    UInt64.toNat_ofNat_of_lt helem
  have hc : (UInt64.ofNat countBits).toNat = countBits :=
    UInt64.toNat_ofNat_of_lt hcount
  have hm : (Miri.ABI.Size.ofBytes 0x7fff_ffff_ffff_ffff).bytes.toNat = isizeMaxBytes := rfl
  unfold Miri.Interpreter.IntegerOps.computeSizeInBytes
  rw [he, hc, hm, Nat.mul_comm elemBytes countBits]
  by_cases hle : countBits * elemBytes ≤ isizeMaxBytes
  · have hlt64 : countBits * elemBytes < 2 ^ 64 := by
      unfold isizeMaxBytes at hle; omega
    simp [hle, hlt64]
  · simp [hle]

/-! ## 3. `annealWriteRepeatedBytes` behavior -/

private theorem wbSizeAsI64_of_le_isizeMax {total : Nat} (hle : total ≤ isizeMaxBytes) :
    Miri.Memory.sizeAsI64 (Miri.ABI.Size.ofBytes (UInt64.ofNat total)) =
      .ok (Int.ofNat total) := by
  have hlt64 : total < 2 ^ 64 := by unfold isizeMaxBytes at hle; omega
  have ht : (Miri.ABI.Size.ofBytes (UInt64.ofNat total)).bytes.toNat = total :=
    UInt64.toNat_ofNat_of_lt hlt64
  have hlt63 : total < 9223372036854775808 := by unfold isizeMaxBytes at hle; omega
  unfold Miri.Memory.sizeAsI64
  rw [ht]
  simp [hlt63]

private theorem wbInt_lt_two_pow_63 {total : Nat} (hle : total ≤ isizeMaxBytes) :
    (total : Int) < 2 ^ 63 := by
  have hlt : total < 2 ^ 63 := Nat.lt_of_le_of_lt hle (by decide)
  exact Int.ofNat_lt.mpr hlt

private theorem wbAnnealWriteRepeatedBytes_of_check_err
    {ptr : Miri.Memory.Pointer (Option AnnealProv)} {byte : UInt8} {size : Miri.ABI.Size}
    {st : AnnealStepState} {signedSize : Int} {err : Miri.Memory.AccessError}
    (hsz : Miri.Memory.sizeAsI64 size = .ok signedSize)
    (hchk : Miri.Memory.checkAndDerefPtr annealPointerArithmetic ptr signedSize .memoryAccess
      (annealResolvePtr st.machine) (annealLookupAlloc st.machine) = .error err) :
    annealWriteRepeatedBytes ptr byte size st =
      .error (.undefinedBehavior "write_bytes pointer check failed") st := by
  unfold annealWriteRepeatedBytes
  simp only [hsz, hchk]

/-- Zero-byte `annealWriteRepeatedBytes` is a no-op for any pointer (even
dangling, dead, or provenance-free). -/
theorem annealWriteRepeatedBytes_zero (ptr : Miri.Memory.Pointer (Option AnnealProv))
    (byte : UInt8) (st : AnnealStepState) :
    annealWriteRepeatedBytes ptr byte (Miri.ABI.Size.ofBytes (UInt64.ofNat 0)) st = .ok () st := by
  have hsz : Miri.Memory.sizeAsI64 (Miri.ABI.Size.ofBytes (UInt64.ofNat 0)) = .ok 0 := rfl
  have hchk : Miri.Memory.checkAndDerefPtr annealPointerArithmetic ptr 0 .memoryAccess
      (annealResolvePtr st.machine) (annealLookupAlloc st.machine) = .ok none := rfl
  unfold annealWriteRepeatedBytes
  cases h1 : Miri.Memory.sizeAsI64 (Miri.ABI.Size.ofBytes (UInt64.ofNat 0)) with
  | error _ => rw [hsz] at h1; cases h1
  | ok s =>
    injection (h1.symm.trans hsz) with hs
    subst hs
    cases h2 : Miri.Memory.checkAndDerefPtr annealPointerArithmetic ptr 0 .memoryAccess
        (annealResolvePtr st.machine) (annealLookupAlloc st.machine) with
    | error _ => rw [hchk] at h2; cases h2
    | ok opt =>
      injection (h2.symm.trans hchk) with ho
      subst ho
      rfl

/-- Non-zero `annealWriteRepeatedBytes` on a provenance-free integer pointer
reports UB. -/
theorem annealWriteRepeatedBytes_withoutProvenance_err (addr : UInt64) (byte : UInt8)
    {total : Nat} (hpos : 0 < total) (hle : total ≤ isizeMaxBytes) (st : AnnealStepState) :
    annealWriteRepeatedBytes (Miri.Memory.Pointer.withoutProvenance addr) byte
        (Miri.ABI.Size.ofBytes (UInt64.ofNat total)) st =
      .error (.undefinedBehavior "write_bytes pointer check failed") st :=
  wbAnnealWriteRepeatedBytes_of_check_err (wbSizeAsI64_of_le_isizeMax hle)
    (checkAndDerefPtr_withoutProvenance_err st.machine addr (Int.ofNat total) .memoryAccess
      (Int.ofNat_lt.mpr hpos) (wbInt_lt_two_pow_63 hle))

/-- Non-zero `annealWriteRepeatedBytes` to a deallocated stack allocation
reports UB. -/
theorem annealWriteRepeatedBytes_dead_err
    {st : AnnealStepState} (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes : Nat) (byte : UInt8) {total : Nat}
    (hid : allocId.value.toNat < 2 ^ 32) (hoff : offsetBytes < 2 ^ 32)
    (hbase : st.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hdead : st.machine.memory.live.find? (fun entry => entry.1 == allocId) = none)
    (hpos : 0 < total) (hle : total ≤ isizeMaxBytes) :
    annealWriteRepeatedBytes
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
          some (.concrete allocId borTag)⟩
        byte (Miri.ABI.Size.ofBytes (UInt64.ofNat total)) st =
      .error (.undefinedBehavior "write_bytes pointer check failed") st :=
  wbAnnealWriteRepeatedBytes_of_check_err (wbSizeAsI64_of_le_isizeMax hle)
    (checkAndDerefPtr_deadAlloc_err allocId borTag offsetBytes (Int.ofNat total) .memoryAccess
      hid hoff hbase hdead (Int.ofNat_lt.mpr hpos) (wbInt_lt_two_pow_63 hle))

/-- Out-of-bounds non-zero `annealWriteRepeatedBytes` on a live stack allocation
reports UB. -/
theorem annealWriteRepeatedBytes_oob_err
    {st : AnnealStepState} (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes : Nat)
    (localAlloc : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind)
    (byte : UInt8) {total : Nat}
    (hid : allocId.value.toNat < 2 ^ 32) (hoff : offsetBytes < 2 ^ 32)
    (hbase : st.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hlive : st.machine.memory.live.find? (fun entry => entry.1 == allocId) =
      some (allocId, localAlloc))
    (hpos : 0 < total) (hle : total ≤ isizeMaxBytes)
    (hoob : localAlloc.allocation.byteSize.bytes.toNat < offsetBytes + total) :
    annealWriteRepeatedBytes
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
          some (.concrete allocId borTag)⟩
        byte (Miri.ABI.Size.ofBytes (UInt64.ofNat total)) st =
      .error (.undefinedBehavior "write_bytes pointer check failed") st :=
  wbAnnealWriteRepeatedBytes_of_check_err (wbSizeAsI64_of_le_isizeMax hle)
    (checkAndDerefPtr_live_oob_err allocId borTag offsetBytes total localAlloc .memoryAccess
      hid hoff hbase hlive hpos (wbInt_lt_two_pow_63 hle) hoob)

private theorem wbAnnealWriteRepeatedBytes_of_ok
    {ptr : Miri.Memory.Pointer (Option AnnealProv)} {byte : UInt8} {size : Miri.ABI.Size}
    {st : AnnealStepState} {signedSize : Int}
    {access : Miri.Memory.CheckedPointerAccess Miri.Memory.BorTag}
    {aid : Miri.Memory.AllocId}
    {localAlloc : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {nextMem : AnnealMemory}
    (hsz : Miri.Memory.sizeAsI64 size = .ok signedSize)
    (hchk : Miri.Memory.checkAndDerefPtr annealPointerArithmetic ptr signedSize .memoryAccess
      (annealResolvePtr st.machine) (annealLookupAlloc st.machine) = .ok (some access))
    (hlive : st.machine.memory.live.find? (fun entry => entry.1 == access.pointer.allocId) =
      some (aid, localAlloc))
    (hwrite : Miri.Memory.Allocation.writeRepeatedByte access.pointer.offset byte size.bytes
      (Miri.ABI.Size.ofBytes 8) localAlloc.allocation = .ok () alloc')
    (hset : st.machine.memory.setLiveAllocation access.pointer.allocId alloc' = .ok nextMem) :
    annealWriteRepeatedBytes ptr byte size st =
      .ok () { st with machine := { st.machine with memory := nextMem } } := by
  unfold annealWriteRepeatedBytes
  simp only [hsz, hchk, hlive, hwrite, hset]

/-- In-bounds non-zero `annealWriteRepeatedBytes` on a live stack allocation
updates `live` when `Allocation.writeRepeatedByte` succeeds. -/
theorem annealWriteRepeatedBytes_live_ok
    {st : AnnealStepState} (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes : Nat)
    (localAlloc : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind)
    (alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (byte : UInt8) {total : Nat}
    (hid : allocId.value.toNat < 2 ^ 32) (hoff : offsetBytes < 2 ^ 32)
    (hbase : st.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hlive : st.machine.memory.live.find? (fun entry => entry.1 == allocId) =
      some (allocId, localAlloc))
    (hpos : 0 < total) (hle : total ≤ isizeMaxBytes)
    (hinbounds : offsetBytes + total ≤ localAlloc.allocation.byteSize.bytes.toNat)
    (hwrite : Miri.Memory.Allocation.writeRepeatedByte
        (Miri.ABI.Size.ofBytes (UInt64.ofNat offsetBytes)) byte (UInt64.ofNat total)
        (Miri.ABI.Size.ofBytes 8) localAlloc.allocation = .ok () alloc') :
    annealWriteRepeatedBytes
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
          some (.concrete allocId borTag)⟩
        byte (Miri.ABI.Size.ofBytes (UInt64.ofNat total)) st =
      .ok () { st with machine := { st.machine with
        memory := { st.machine.memory with
          live := (st.machine.memory.live.filter (fun x => x.1 != allocId)).push
            (allocId, ⟨localAlloc.kind, alloc'⟩) } } } :=
  wbAnnealWriteRepeatedBytes_of_ok (wbSizeAsI64_of_le_isizeMax hle)
    (checkAndDerefPtr_live_inbounds_ok allocId borTag offsetBytes total localAlloc .memoryAccess
      hid hoff hbase hlive hpos (wbInt_lt_two_pow_63 hle) hinbounds)
    hlive hwrite
    (Miri.Memory.MemoryState.setLiveAllocation_of_find st.machine.memory allocId localAlloc alloc'
      hlive)

private theorem wbEvalOperand_rawPtr_lm3_1
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {idx : Local} {decl : LocalDecl} {mutability : Mutability} {pk : RigidTy}
    (hdecl : get? body.localDecls idx = some decl)
    (hty : decl.ty.kind = .rawPtr mutability pk)
    (himm : IsImmediateFrameLocal tf idx) :
    (get? s.frame.locals idx = some .dead ∧
      ∃ m' msg, annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩) none m =
        .error (.undefinedBehavior msg) m') ∨
    (∃ tf', get? s.frame.locals idx = some .uninit ∧
      annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩) none m =
        .ok ⟨.immediate .uninit, translateTy decl.ty body.layouts⟩ { m with stack := ⟨#[tf']⟩ } ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf']⟩ } allocMap ∧
      (∀ k : Nat, (tf'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value)) ∨
    (∃ sc msc tf', get? s.frame.locals idx = some (.init (.scalar sc)) ∧ sc.sizeBytes = 8 ∧
      ScalarRel sc msc ∧
      annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩) none m =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy decl.ty body.layouts⟩
          { m with stack := ⟨#[tf']⟩ } ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf']⟩ } allocMap ∧
      (∀ k : Nat, (tf'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value)) ∨
    (∃ ptrVal mptr tf', get? s.frame.locals idx = some (.init (.ptr ptrVal 8)) ∧
      PtrRel allocMap ptrVal mptr ∧
      annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩) none m =
        .ok ⟨.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)),
          translateTy decl.ty body.layouts⟩ { m with stack := ⟨#[tf']⟩ } ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf']⟩ } allocMap ∧
      (∀ k : Nat, (tf'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value)) := by
  rcases id hstate with ⟨tf₀, hframes₀, _, _, hfr, _, _, _, _, _, _, _⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₁
  injection h₁ with htf
  subst htf
  obtain ⟨slot, mls, _, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have hcache := hloc.cachedLayout_eq
  have hvals : ∀ k : Nat,
      ((cacheFrameLocalLayout tf idx hlt_mf (translateTy decl.ty body.layouts)).locals[k]?).map
        Miri.Interpreter.LocalState.value =
      (tf.locals[k]?).map Miri.Interpreter.LocalState.value := by
    intro k
    simp only [cacheFrameLocalLayout]
    by_cases hki : idx = k
    · subst hki
      rw [Array.getElem?_set_self, Array.getElem?_eq_getElem hlt_mf]
      rfl
    · rw [Array.getElem?_set_ne _ hki]
  have hstate' := hstate.cache_layout hframes hdecl hlt_mf
  rcases hloc.rawPtr_immediate_cases hty (himm mls hmls) with
    ⟨hss, hms⟩ | ⟨hss, hms⟩ | ⟨sc, msc, hss, hsz8, hrel, hms⟩ | ⟨ptrVal, mptr, hss, hptr, hms⟩
  · subst hss
    have hmls' : tf.locals[idx]'hlt_mf = ⟨.dead, mls.layout⟩ := by
      rw [hmls_eq]; rcases mls with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    exact Or.inl ⟨hslot, _, _, annealEvalOperand_copy_dead hframes hlt_mf hdecl hmls' hcache⟩
  · subst hss
    have hmls' : tf.locals[idx]'hlt_mf = ⟨.live (.immediate .uninit), mls.layout⟩ := by
      rw [hmls_eq]; rcases mls with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    exact Or.inr (Or.inl ⟨_, hslot,
      annealEvalOperand_copy_live hframes hlt_mf hdecl hmls' hcache, hstate', hvals⟩)
  · subst hss
    have hmls' : tf.locals[idx]'hlt_mf =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls.layout⟩ := by
      rw [hmls_eq]; rcases mls with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    exact Or.inr (Or.inr (Or.inl ⟨sc, msc, _, hslot, hsz8, hrel,
      annealEvalOperand_copy_live hframes hlt_mf hdecl hmls' hcache, hstate', hvals⟩))
  · subst hss
    have hmls' : tf.locals[idx]'hlt_mf =
        ⟨.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))), mls.layout⟩ := by
      rw [hmls_eq]; rcases mls with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    exact Or.inr (Or.inr (Or.inr ⟨ptrVal, mptr, _, hslot, hptr,
      annealEvalOperand_copy_live hframes hlt_mf hdecl hmls' hcache, hstate', hvals⟩))

/-! ## 4. Repeated-byte fill on `StackScalarAllocShape` -/

private def wbAlloc_raw {P E : Type} (a : Miri.Memory.Allocation P E) : Array UInt8 :=
  Miri.Memory.Allocation.casesOn (motive := fun _ => Array UInt8) a
    (fun raw _ _ _ _ _ _ _ => raw)

private def wbAlloc_pointerSize (layout : Miri.ABI.TargetDataLayout) : Miri.ABI.Size :=
  Miri.ABI.Size.fromBits layout.pointerWidth.bits

private def wbAlloc_readTargetUInt (layout : Miri.ABI.TargetDataLayout)
    (bytes : Array UInt8) : Except Miri.Memory.AllocError Miri.ABI.U128 := do
  if bytes.size > 16 then
    throw (.scalarBytesTooWide (Miri.ABI.Size.ofBytes (UInt64.ofNat bytes.size)))
  let mut value := 0
  for index in [:bytes.size] do
    let some byte := bytes[index]? | throw (.invalidSliceEndpoints index (index + 1) bytes.size)
    let valueIndex := if layout.endian == .little then index else bytes.size - index - 1
    value := value + byte.toNat * 2 ^ (8 * valueIndex)
  return BitVec.ofNat 128 value

private def wbAlloc_checkedSlice {P E : Type} (allocation : Miri.Memory.Allocation P E)
    (range : Miri.Memory.AllocRange) : Except Miri.Memory.AllocError (Array UInt8) := do
  if (wbAlloc_raw allocation).size != allocation.byteSize.bytes.toNat then
    throw (.storageLengthMismatch allocation.byteSize (wbAlloc_raw allocation).size)
  let finish ← range.endExclusive |>.mapError Miri.Memory.AllocError.memory
  if range.start.bytes > finish.bytes || finish.bytes > allocation.byteSize.bytes then
    throw (.outOfBounds range allocation.byteSize)
  return (wbAlloc_raw allocation).extract range.start.bytes.toNat finish.bytes.toNat

private theorem wbAlloc_getBytesUnchecked_eq {P E : Type}
    (allocation : Miri.Memory.Allocation P E) (range : Miri.Memory.AllocRange) :
    Miri.Memory.Allocation.getBytesUnchecked allocation range =
      wbAlloc_checkedSlice allocation range := rfl

private def wbAlloc_readScalar {P E : Type} [DecidableEq P] [Miri.Memory.PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : Miri.ABI.TargetDataLayout)
    (range : Miri.Memory.AllocRange) (readProvenance : Bool) :
    Except Miri.Memory.AllocError (Miri.Memory.Scalar P) := do
  match ← (allocation.initializationMask.isRangeInitialized range).mapError
      Miri.Memory.AllocError.memory with
  | .error bad => throw (.invalidUninitBytes (some ⟨range, bad⟩))
  | .ok () => pure ()
  let bytes ← Miri.Memory.Allocation.getBytesUnchecked allocation range
  let bits ← wbAlloc_readTargetUInt layout bytes
  if readProvenance then
    let targetSize := wbAlloc_pointerSize layout
    if range.size != targetSize then
      throw (.scalarPointerNotTargetSized range.size targetSize)
    let provenance ← match allocation.provenanceMap.readPtr range.start targetSize with
      | .ok provenance => pure provenance
      | .error (.readPartialPointer offset) => throw (.readPartialPointer offset)
      | .error reason => throw (.provenance reason)
    match provenance with
    | some provenance =>
      if bits.toNat > 18446744073709551615 then
        throw (.pointerBitsDoNotFitOffset bits)
      return Miri.Memory.Scalar.fromPointer layout
        (Miri.Memory.Pointer.new provenance (Miri.ABI.Size.ofBytes (UInt64.ofNat bits.toNat)))
    | none =>
      let scalar ← (Miri.Memory.Scalar.fromUInt bits range.size).mapError
        Miri.Memory.AllocError.scalar
      return scalar
  else
    if Miri.Memory.PointerProvenance.offsetIsAddr (Prov := P) then
      let scalar ← (Miri.Memory.Scalar.fromUInt bits range.size).mapError
        Miri.Memory.AllocError.scalar
      return scalar
    let isEmpty ←
      (allocation.provenanceMap.rangeEmpty range (wbAlloc_pointerSize layout)).mapError
        Miri.Memory.AllocError.provenance
    if isEmpty then
      let scalar ← (Miri.Memory.Scalar.fromUInt bits range.size).mapError
        Miri.Memory.AllocError.scalar
      return scalar
    throw (.readPointerAsInt none)

private theorem wbAlloc_readScalar_eq {P E : Type} [DecidableEq P]
    [Miri.Memory.PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : Miri.ABI.TargetDataLayout)
    (range : Miri.Memory.AllocRange) (readProvenance : Bool) :
    allocation.readScalar layout range readProvenance =
      wbAlloc_readScalar allocation layout range readProvenance := rfl

private def wbAlloc_leBytes (x n : Nat) : Array UInt8 :=
  ((List.range' 0 n).map fun i => UInt8.ofNat ((x / 2 ^ (8 * i)) % 256)).toArray

private theorem wbAlloc_leBytes_size (x n : Nat) : (wbAlloc_leBytes x n).size = n := by
  simp [wbAlloc_leBytes]

private def wbAlloc_leSum (x k : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) + wbAlloc_leSum x (k + 1) m

private theorem wbAlloc_leSum_spec (x : Nat) :
    ∀ m k, x % 2 ^ (8 * k) + wbAlloc_leSum x k m = x % 2 ^ (8 * (k + m)) := by
  intro m
  induction m with
  | zero => intro k; simp [wbAlloc_leSum]
  | succ m ih =>
    intro k
    have hstep : x % 2 ^ (8 * k) + x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) =
        x % 2 ^ (8 * (k + 1)) := by
      rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add, Nat.mod_mul]
      simp only [show (2 : Nat) ^ 8 = 256 by rfl]
      rw [Nat.mul_comm (2 ^ (8 * k))]
    simp only [wbAlloc_leSum]
    rw [← Nat.add_assoc, hstep, ih (k + 1), show k + 1 + m = k + (m + 1) by omega]

private theorem wbAlloc_decode_loop (x n : Nat)
    (f : Nat → Nat → Except Miri.Memory.AllocError (ForInStep Nat))
    (hf : ∀ index s, index < n →
      f index s = .ok (.yield (s + x / 2 ^ (8 * index) % 256 * 2 ^ (8 * index)))) :
    ∀ m k acc, k + m ≤ n →
      forIn (List.range' k m) acc f = .ok (acc + wbAlloc_leSum x k m) := by
  intro m
  induction m with
  | zero => intro k acc _; simp [wbAlloc_leSum, pure, Except.pure]
  | succ m ih =>
    intro k acc hkm
    rw [List.range'_succ, List.forIn_cons, hf k acc (by omega)]
    simp only [wbAlloc_leSum]
    rw [show (Except.ok (ForInStep.yield (acc + x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k))) :
        Except Miri.Memory.AllocError (ForInStep Nat)) = pure (ForInStep.yield _) from rfl,
      pure_bind]
    simp only
    rw [ih (k + 1) _ (by omega), Nat.add_assoc]

private theorem wbAlloc_readTargetUInt_leBytes (x n : Nat) (hn : n ≤ 16) :
    wbAlloc_readTargetUInt annealTargetDataLayout (wbAlloc_leBytes x n) =
      .ok (BitVec.ofNat 128 (x % 2 ^ (8 * n))) := by
  have small : ¬ n > 16 := by omega
  have hendian : (annealTargetDataLayout.endian == Miri.ABI.Endian.little) = true := rfl
  have hlsize : (wbAlloc_leBytes x n).size = n := by simp [wbAlloc_leBytes]
  unfold wbAlloc_readTargetUInt
  simp only [hlsize, small, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range',
    hendian, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [wbAlloc_decode_loop x n _ ?hf n 0 0 (by omega)]
  · have := wbAlloc_leSum_spec x n 0
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mod_one, Nat.zero_add] at this
    simp [this, pure, Except.pure, bind, Except.bind]
  · intro index s hi
    have hb : (x / 2 ^ (8 * index) % 256) < 256 := Nat.mod_lt _ (by decide)
    simp [wbAlloc_leBytes, hi, pure, Except.pure, Nat.mod_eq_of_lt hb]

private theorem wbAlloc_allocRange_end (size : Miri.ABI.Size) :
    (Miri.Memory.allocRange Miri.ABI.Size.ZERO size).endExclusive = .ok size := by
  cases size
  simp [Miri.Memory.AllocRange.endExclusive, Miri.Memory.AllocRange.end, Miri.Memory.allocRange,
    Miri.ABI.Size.ZERO, Miri.ABI.Size.add, Miri.ABI.Size.ofBytes, Except.mapError]

private theorem wbAlloc_scalarModulus_eq_two_pow (sz : Nat) :
    scalarModulus sz = 2 ^ (8 * sz) := by
  induction sz with
  | zero => rfl
  | succ k ih =>
    show 256 * scalarModulus k = 2 ^ (8 * (k + 1))
    rw [ih, show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add, Nat.mul_comm]

private theorem wbAlloc_fromUInt {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) :
    Miri.Memory.Scalar.fromUInt (Prov := AnnealProv) (BitVec.ofNat 128 sc.bits)
        (translateSizeBytes sc.sizeBytes) = .ok (Miri.Memory.Scalar.fromScalarInt msc) := by
  obtain ⟨msc', htry, hrel'⟩ := tryFromUInt_of_valid_canonical hrel.validBytes hrel.canonical
  have heq : msc' = msc := by
    cases msc'; cases msc
    have hd := hrel'.data_eq.trans hrel.data_eq.symm
    have hs := hrel'.size_eq.trans hrel.size_eq.symm
    simp only [Miri.Memory.ScalarInt.data, Miri.Memory.ScalarInt.size] at hd hs
    subst hd hs; rfl
  subst heq
  unfold Miri.Memory.Scalar.fromUInt
  simp [htry, Except.mapError, bind, Except.bind, pure, Except.pure]

private def wbAlloc_mkList : Nat → List UInt8 → List UInt8
  | 0, _ => []
  | k + 1, l => l.headD 0 :: wbAlloc_mkList k l.tail

private theorem wbAlloc_mkList_eq (l : List UInt8) :
    wbAlloc_mkList l.length l = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [wbAlloc_mkList, ih]

private theorem wbAlloc_array_eta (a : Array UInt8) (n : Nat) (h : a.size = n) :
    a = ⟨wbAlloc_mkList n a.toList⟩ := by
  cases a with
  | mk l =>
    subst h
    exact congrArg Array.mk (wbAlloc_mkList_eq l).symm

private def wbAlloc_setList (start : Nat) (byte : UInt8) : List Nat → Array UInt8 → Array UInt8
  | [], bytes => bytes
  | offset :: rest, bytes =>
    wbAlloc_setList start byte rest ⟨bytes.toList.set (start + offset) byte⟩

private theorem wbAlloc_setList_size (start : Nat) (byte : UInt8) (l : List Nat)
    (bytes : Array UInt8) :
    (wbAlloc_setList start byte l bytes).size = bytes.size := by
  induction l generalizing bytes with
  | nil => rfl
  | cons offset rest ih =>
    rw [wbAlloc_setList, ih]
    exact List.length_set

private theorem wbAlloc_setList_getElem? (start : Nat) (byte : UInt8) :
    ∀ (m k : Nat) (bytes : Array UInt8) (i : Nat),
      start + (k + m) ≤ bytes.size →
      (wbAlloc_setList start byte (List.range' k m) bytes)[i]? =
        if start + k ≤ i ∧ i < start + (k + m) then some byte else bytes[i]? := by
  intro m
  induction m with
  | zero =>
    intro k bytes i _
    have hfalse : ¬(start + k ≤ i ∧ i < start + (k + 0)) := by omega
    simp only [hfalse, ↓reduceIte]
    rfl
  | succ m ih =>
    intro k bytes i hbound
    have hk : start + k < bytes.size := by omega
    have hset : (⟨bytes.toList.set (start + k) byte⟩ : Array UInt8) =
      bytes.set (start + k) byte hk := rfl
    have hsize : (bytes.set (start + k) byte hk).size = bytes.size := Array.size_set hk
    rw [List.range'_succ, wbAlloc_setList, hset, ih (k + 1) _ i (by omega), Array.getElem?_set]
    by_cases h1 : start + (k + 1) ≤ i ∧ i < start + (k + 1 + m)
    · have h2 : start + k ≤ i ∧ i < start + (k + (m + 1)) := by omega
      simp [h1, h2]
    · by_cases h2 : start + k = i
      · have h3 : start + k ≤ i ∧ i < start + (k + (m + 1)) := by omega
        simp [h1, h2, h3]
      · have h3 : ¬(start + k ≤ i ∧ i < start + (k + (m + 1))) := by omega
        simp [h1, h2, h3]

private theorem wbAlloc_setList_zero_full (byte : UInt8) (m : Nat) (bytes : Array UInt8)
    (hm : m = bytes.size) :
    wbAlloc_setList 0 byte (List.range' 0 m) bytes = Array.replicate m byte := by
  apply Array.ext
  · rw [wbAlloc_setList_size, Array.size_replicate, hm]
  · intro i hi₁ hi₂
    have hget := wbAlloc_setList_getElem? 0 byte m 0 bytes i (by omega)
    have hcond : 0 + 0 ≤ i ∧ i < 0 + (0 + m) := by rw [Array.size_replicate] at hi₂; omega
    simp only [hcond, Array.getElem?_eq_getElem hi₁] at hget
    injection hget with hget'
    rw [hget', Array.getElem_replicate]

private def wbAlloc_loopFallback {P E : Type} (start : Nat) (byte : UInt8)
    (cleared : Miri.Memory.Allocation P E) :
    List Nat →
    Option (EStateM.Result Miri.Memory.AllocError (Miri.Memory.Allocation P E) Unit) × Array UInt8 →
    Option (EStateM.Result Miri.Memory.AllocError (Miri.Memory.Allocation P E) Unit) × Array UInt8
  | [], s => s
  | offset :: rest, s =>
    if h : start + offset < s.snd.size then
      wbAlloc_loopFallback start byte cleared rest (none, s.snd.set (start + offset) byte h)
    else
      (some (.error (.invalidSliceEndpoints start (start + offset + 1) s.snd.size) cleared), s.snd)

private theorem wbAlloc_forIn_eq_fallback {P E : Type} (start : Nat) (byte : UInt8)
    (cleared : Miri.Memory.Allocation P E) (l : List Nat)
    (s : Option (EStateM.Result Miri.Memory.AllocError (Miri.Memory.Allocation P E) Unit) ×
      Array UInt8) :
    forIn (m := Id) l s
      (fun offset __s =>
        if h : start + offset < __s.snd.size then
          pure (ForInStep.yield (none, __s.snd.set (start + offset) byte h))
        else
          pure (ForInStep.done
            (some (EStateM.Result.error
              (.invalidSliceEndpoints start (start + offset + 1) __s.snd.size)
              cleared),
             __s.snd))) =
      wbAlloc_loopFallback start byte cleared l s := by
  induction l generalizing s with
  | nil => rfl
  | cons offset rest ih =>
    rw [List.forIn_cons]
    by_cases h : start + offset < s.snd.size
    · simp only [wbAlloc_loopFallback, h, ↓reduceDIte, pure_bind, ih]
    · simp only [wbAlloc_loopFallback, h, ↓reduceDIte]; rfl

private theorem wbAlloc_fallback_eq_setList {P E : Type} (start : Nat) (byte : UInt8)
    (cleared : Miri.Memory.Allocation P E) :
    ∀ (m k : Nat) (bytes : Array UInt8),
      start + (k + m) ≤ bytes.size →
      wbAlloc_loopFallback start byte cleared (List.range' k m) (none, bytes) =
        (none, wbAlloc_setList start byte (List.range' k m) bytes) := by
  intro m
  induction m with
  | zero => intro k bytes _; rfl
  | succ m ih =>
    intro k bytes hbound
    have hk : start + k < bytes.size := by omega
    rw [List.range'_succ]
    simp only [wbAlloc_loopFallback, hk, ↓reduceDIte, wbAlloc_setList]
    have hset : bytes.set (start + k) byte hk = ⟨bytes.toList.set (start + k) byte⟩ := rfl
    rw [hset]
    apply ih (k + 1) ⟨bytes.toList.set (start + k) byte⟩
    have hsize : (⟨bytes.toList.set (start + k) byte⟩ : Array UInt8).size = bytes.size := by
      rw [← hset, Array.size_set]
    omega

private theorem wbAlloc_forIn_full {P E : Type} (byte : UInt8)
    (cleared : Miri.Memory.Allocation P E) (m : Nat) (bytes : Array UInt8) :
    forIn (m := Id) (List.range' 0 m)
      (none (α := EStateM.Result Miri.Memory.AllocError (Miri.Memory.Allocation P E) Unit), bytes)
      (fun offset __s =>
        if h : 0 + offset < __s.snd.size then
          pure (ForInStep.yield (none, __s.snd.set (0 + offset) byte h))
        else
          pure (ForInStep.done
            (some (EStateM.Result.error
              (.invalidSliceEndpoints 0 (0 + offset + 1) __s.snd.size)
              cleared),
             __s.snd))) =
      if m = bytes.size then
        (none, Array.replicate m byte)
      else
        wbAlloc_loopFallback 0 byte cleared (List.range' 0 m) (none, bytes) := by
  rw [wbAlloc_forIn_eq_fallback]
  split
  · next h =>
    rw [wbAlloc_fallback_eq_setList 0 byte cleared m 0 bytes (by omega),
      wbAlloc_setList_zero_full byte m bytes h]
  · rfl

private theorem wbAlloc_repeatByteBits_byte (b : Nat) (hb : b < 256) :
    ∀ (n i : Nat), i < n → (repeatByteBits b n / 2 ^ (8 * i)) % 256 = b
  | 0, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, 0, _ => by
    show (b + 256 * repeatByteBits b k) / 1 % 256 = b
    omega
  | k + 1, j + 1, hi => by
    have hj : j < k := by omega
    have hpow : 2 ^ (8 * (j + 1)) = 256 * 2 ^ (8 * j) := by
      rw [show 8 * (j + 1) = 8 + 8 * j by omega, Nat.pow_add]
    have hdiv : (b + 256 * repeatByteBits b k) / (256 * 2 ^ (8 * j)) =
        repeatByteBits b k / 2 ^ (8 * j) := by
      rw [← Nat.div_div_eq_div_mul]
      have h1 : (b + 256 * repeatByteBits b k) / 256 = repeatByteBits b k := by omega
      rw [h1]
    show (b + 256 * repeatByteBits b k) / 2 ^ (8 * (j + 1)) % 256 = b
    rw [hpow, hdiv]
    exact wbAlloc_repeatByteBits_byte b hb k j hj

private theorem wbAlloc_leBytes_repeatByteBits (byte : UInt8) (n : Nat) :
    wbAlloc_leBytes (repeatByteBits byte.toNat n) n = Array.replicate n byte := by
  apply Array.ext
  · simp [wbAlloc_leBytes]
  · intro i hi₁ hi₂
    rw [Array.size_replicate] at hi₂
    have hbyte := wbAlloc_repeatByteBits_byte byte.toNat byte.toNat_lt n i hi₂
    simp [wbAlloc_leBytes, hbyte]

/-- Whole-local `Allocation.writeRepeatedByte` (`offset = 0`, `count = n`) on a
`StackScalarAllocShape (translateSizeBytes n)` stack allocation produces an
initialized `StackScalarAllocShape` allocation whose `readScalar` yields the
`ScalarInt` related to `⟨repeatByteBits byte.toNat n, n⟩`. -/
theorem StackScalarAllocShape.writeRepeatedByte_full {E : Type} {n : Nat}
    (hn : ValidScalarBytes n) (byte : UInt8) {A : Miri.Memory.Allocation AnnealProv E}
    (hshape : StackScalarAllocShape (translateSizeBytes n) A) :
    ∃ (alloc' : Miri.Memory.Allocation AnnealProv E) (msc : Miri.Memory.ScalarInt),
      Miri.Memory.Allocation.writeRepeatedByte (Miri.ABI.Size.ofBytes (UInt64.ofNat 0)) byte
          (UInt64.ofNat n) (Miri.ABI.Size.ofBytes 8) A = .ok () alloc' ∧
      ScalarRel ⟨repeatByteBits byte.toNat n, n⟩ msc ∧
      alloc'.align = A.align ∧
      StackScalarAllocShape (translateSizeBytes n) alloc' ∧
      alloc'.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) = .ok (.ok ()) ∧
      alloc'.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) false =
        .ok (Miri.Memory.Scalar.fromScalarInt msc) := by
  have hcan : repeatByteBits byte.toNat n < scalarModulus n :=
    repeatByteBits_lt_scalarModulus byte.toNat_lt n
  obtain ⟨msc, _, hrel⟩ :=
    tryFromUInt_of_valid_canonical (sc := ⟨repeatByteBits byte.toNat n, n⟩) hn hcan
  have hn_eq : (translateSizeBytes n).bytes.toNat = n := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hn16 : (translateSizeBytes n).bytes.toNat ≤ 16 := by
    rw [hn_eq]; rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have hend := wbAlloc_allocRange_end (translateSizeBytes n)
  obtain ⟨alloc', hw, halign', hshape', hinit', hraw'⟩ :
      ∃ alloc' : Miri.Memory.Allocation AnnealProv E,
        Miri.Memory.Allocation.writeRepeatedByte (Miri.ABI.Size.ofBytes (UInt64.ofNat 0)) byte
            (UInt64.ofNat n) (Miri.ABI.Size.ofBytes 8) A = .ok () alloc' ∧
        alloc'.align = A.align ∧
        StackScalarAllocShape (translateSizeBytes n) alloc' ∧
        alloc'.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) = .ok (.ok ()) ∧
        wbAlloc_raw alloc' = Array.replicate n byte := by
    rcases hshape with ⟨hsz, hlen, hmut, hprov, ⟨initBool, hmask⟩⟩
    rcases A with ⟨rawBytes, size, provenance, initMask, align, mutability, extra, nativeBuffer⟩
    unfold Miri.Memory.Allocation.byteSize at hsz
    unfold Miri.Memory.Allocation.len at hlen
    unfold Miri.Memory.Allocation.provenanceMap at hprov
    unfold Miri.Memory.Allocation.initializationMask at hmask
    dsimp only at hsz hlen hmut hprov hmask
    subst hsz hmut hprov hmask
    rw [hn_eq] at hlen
    have hstart0 : (Miri.ABI.Size.ofBytes (UInt64.ofNat 0)).bytes.toNat = 0 := rfl
    rcases hn with rfl | rfl | rfl | rfl | rfl <;>
      cases initBool <;>
      { rw [wbAlloc_array_eta rawBytes _ hlen]
        unfold Miri.Memory.Allocation.writeRepeatedByte
        simp only [hstart0, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
          Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind, Id.run, wbAlloc_forIn_full]
        refine ⟨_, rfl, rfl, ⟨rfl, rfl, rfl, rfl, ⟨true, rfl⟩⟩, rfl, rfl⟩ }
  refine ⟨alloc', msc, hw, hrel, halign', hshape', hinit', ?_⟩
  have hraw_le : wbAlloc_raw alloc' =
      wbAlloc_leBytes (repeatByteBits byte.toNat n) (translateSizeBytes n).bytes.toNat := by
    rw [hraw', hn_eq, wbAlloc_leBytes_repeatByteBits]
  have hslice_read : wbAlloc_checkedSlice alloc'
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) =
      .ok (wbAlloc_leBytes (repeatByteBits byte.toNat n) (translateSizeBytes n).bytes.toNat) := by
    have hrawsize : (wbAlloc_raw alloc').size = (translateSizeBytes n).bytes.toNat :=
      hshape'.len_eq
    unfold wbAlloc_checkedSlice
    simp only [hrawsize, hshape'.byteSize_eq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      hend, Except.mapError, bind, Except.bind]
    simp [Miri.Memory.allocRange, Miri.ABI.Size.ZERO, pure, Except.pure, hraw_le,
      wbAlloc_leBytes_size]
  have hoff : Miri.Memory.PointerProvenance.offsetIsAddr AnnealProv = true := rfl
  have hmod : repeatByteBits byte.toNat n % 2 ^ (8 * (translateSizeBytes n).bytes.toNat) =
      repeatByteBits byte.toNat n := by
    rw [hn_eq, ← wbAlloc_scalarModulus_eq_two_pow]
    exact Nat.mod_eq_of_lt hcan
  have hrange :
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)).size =
        translateSizeBytes n := rfl
  rw [wbAlloc_readScalar_eq]
  unfold wbAlloc_readScalar
  rw [hinit']
  simp only [Except.mapError, bind, Except.bind]
  rw [wbAlloc_getBytesUnchecked_eq, hslice_read]
  simp only []
  rw [wbAlloc_readTargetUInt_leBytes _ _ hn16, hmod]
  simp only [Bool.false_eq_true, ↓reduceIte, hoff, hrange, wbAlloc_fromUInt hrel]

/-- Byte-splice result of overwriting bytes `[off, off + total)` of an
`n`-byte unsigned integer `oldBits` with `total` copies of `byteVal` (`< 256`)
in little-endian order, matching `evalWriteBytesCall` on `.init (.scalar sc)`. -/
def spliceRepeatedBytes (oldBits byteVal off total n : Nat) : Nat :=
  let fill := repeatByteBits byteVal total
  let lowMod := scalarModulus off
  let highMod := scalarModulus (Nat.add off total)
  let old := wrapScalarBits oldBits (scalarModulus n)
  Nat.add (Nat.mod old lowMod)
    (Nat.add (Nat.mul fill lowMod)
      (Nat.mul (Nat.div old highMod) highMod))

private theorem wbScalarModulus_pos (sz : Nat) : 0 < scalarModulus sz := by
  rw [wbAlloc_scalarModulus_eq_two_pow]; exact Nat.two_pow_pos _

private theorem wbWrapScalarBits_lt (bits sz : Nat) :
    wrapScalarBits bits (scalarModulus sz) < scalarModulus sz := by
  unfold wrapScalarBits
  cases hble : (scalarModulus sz).ble bits
  · dsimp only
    exact Nat.lt_of_not_ge (fun hle => Bool.noConfusion ((Nat.ble_eq.mpr hle).symm.trans hble))
  · dsimp only
    exact Nat.mod_lt _ (wbScalarModulus_pos sz)

private theorem wbWrapScalarBits_eq_of_lt {bits sz : Nat} (h : bits < scalarModulus sz) :
    wrapScalarBits bits (scalarModulus sz) = bits := by
  unfold wrapScalarBits
  have hble : (scalarModulus sz).ble bits = false := by
    cases hb : (scalarModulus sz).ble bits
    · rfl
    · exact absurd (Nat.ble_eq.mp hb) (Nat.not_le_of_lt h)
  rw [hble]

/-- `spliceRepeatedBytes` produces a canonical `n`-byte unsigned integer
whenever `byteVal < 256` and `off + total ≤ n`. -/
theorem spliceRepeatedBytes_lt_scalarModulus (oldBits : Nat) {byteVal off total n : Nat}
    (hb : byteVal < 256) (hinb : off + total ≤ n) :
    spliceRepeatedBytes oldBits byteVal off total n < scalarModulus n := by
  unfold spliceRepeatedBytes
  have hlow_pos := wbScalarModulus_pos off
  have hmod_lt : wrapScalarBits oldBits (scalarModulus n) % scalarModulus off <
      scalarModulus off := Nat.mod_lt _ hlow_pos
  have hfill_lt : repeatByteBits byteVal total < scalarModulus total :=
    repeatByteBits_lt_scalarModulus hb total
  have hhigh_eq : scalarModulus (Nat.add off total) =
      scalarModulus total * scalarModulus off := by
    simp only [Nat.add_eq, wbAlloc_scalarModulus_eq_two_pow]
    rw [show 8 * (off + total) = 8 * total + 8 * off by omega, Nat.pow_add]
  have hmid_lt :
      wrapScalarBits oldBits (scalarModulus n) % scalarModulus off +
        repeatByteBits byteVal total * scalarModulus off <
      scalarModulus (Nat.add off total) := by
    have hmul_le : repeatByteBits byteVal total * scalarModulus off + scalarModulus off ≤
        scalarModulus total * scalarModulus off := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ hfill_lt
    rw [hhigh_eq]; omega
  have hold_lt := wbWrapScalarBits_lt oldBits n
  have htop_eq : scalarModulus n =
      scalarModulus (n - (off + total)) * scalarModulus (Nat.add off total) := by
    simp only [Nat.add_eq, wbAlloc_scalarModulus_eq_two_pow]
    rw [← Nat.pow_add, show 8 * (n - (off + total)) + 8 * (off + total) = 8 * n by omega]
  have hhigh_pos := wbScalarModulus_pos (Nat.add off total)
  have hdiv_lt : wrapScalarBits oldBits (scalarModulus n) / scalarModulus (Nat.add off total) <
      scalarModulus (n - (off + total)) := by
    rw [Nat.div_lt_iff_lt_mul hhigh_pos, ← htop_eq]
    exact hold_lt
  have htop_le :
      (wrapScalarBits oldBits (scalarModulus n) / scalarModulus (Nat.add off total)) *
        scalarModulus (Nat.add off total) + scalarModulus (Nat.add off total) ≤
      scalarModulus n := by
    calc (wrapScalarBits oldBits (scalarModulus n) / scalarModulus (Nat.add off total)) *
            scalarModulus (Nat.add off total) + scalarModulus (Nat.add off total)
        = (wrapScalarBits oldBits (scalarModulus n) / scalarModulus (Nat.add off total) + 1) *
            scalarModulus (Nat.add off total) := by rw [← Nat.succ_mul]
      _ ≤ scalarModulus (n - (off + total)) * scalarModulus (Nat.add off total) :=
            Nat.mul_le_mul_right _ hdiv_lt
      _ = scalarModulus n := htop_eq.symm
  change (wrapScalarBits oldBits (scalarModulus n) % scalarModulus off) +
    (repeatByteBits byteVal total * scalarModulus off +
      (wrapScalarBits oldBits (scalarModulus n) / scalarModulus (Nat.add off total)) *
        scalarModulus (Nat.add off total)) < scalarModulus n
  omega

private theorem wbByte_of_split {a b k i : Nat} (ha : a < 2 ^ (8 * k)) :
    ((a + b * 2 ^ (8 * k)) / 2 ^ (8 * i)) % 256 =
      if i < k then (a / 2 ^ (8 * i)) % 256 else (b / 2 ^ (8 * (i - k))) % 256 := by
  by_cases hik : i < k
  · simp only [hik, ↓reduceIte]
    have hpow : 2 ^ (8 * k) = (256 * 2 ^ (8 * (k - i - 1))) * 2 ^ (8 * i) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_add, ← Nat.pow_add]
      exact congrArg (2 ^ ·) (by omega)
    have hmul : b * 2 ^ (8 * k) = (b * 2 ^ (8 * (k - i - 1)) * 256) * 2 ^ (8 * i) := by
      rw [hpow]; ac_rfl
    rw [hmul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_right]
  · simp only [hik, ↓reduceIte]
    have hpow : 2 ^ (8 * i) = 2 ^ (8 * k) * 2 ^ (8 * (i - k)) := by
      rw [← Nat.pow_add]
      exact congrArg (2 ^ ·) (by omega)
    rw [hpow, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt ha, Nat.zero_add]

/-- Every little-endian byte `i < n` of `spliceRepeatedBytes` equals `byteVal`
inside `[off, off + total)` and the original byte `(oldBits / 2^(8*i)) % 256`
outside `[off, off + total)`. -/
theorem spliceRepeatedBytes_byte {oldBits byteVal off total n i : Nat}
    (hold : oldBits < scalarModulus n) (hb : byteVal < 256)
    (_hinb : off + total ≤ n) (_hi : i < n) :
    (spliceRepeatedBytes oldBits byteVal off total n / 2 ^ (8 * i)) % 256 =
      if off ≤ i ∧ i < off + total then byteVal else (oldBits / 2 ^ (8 * i)) % 256 := by
  have hwrap := wbWrapScalarBits_eq_of_lt hold
  have hlow_eq := wbAlloc_scalarModulus_eq_two_pow off
  have hhigh_eq : scalarModulus (Nat.add off total) = 2 ^ (8 * (off + total)) :=
    wbAlloc_scalarModulus_eq_two_pow (off + total)
  have hlow_lt : oldBits % 2 ^ (8 * off) < 2 ^ (8 * off) :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hfill_lt : repeatByteBits byteVal total < 2 ^ (8 * total) := by
    rw [← wbAlloc_scalarModulus_eq_two_pow]
    exact repeatByteBits_lt_scalarModulus hb total
  have hmid_lt :
      oldBits % 2 ^ (8 * off) + repeatByteBits byteVal total * 2 ^ (8 * off) <
        2 ^ (8 * (off + total)) := by
    have hpow : 2 ^ (8 * (off + total)) = 2 ^ (8 * total) * 2 ^ (8 * off) := by
      rw [← Nat.pow_add, show 8 * total + 8 * off = 8 * (off + total) by omega]
    have hle : repeatByteBits byteVal total * 2 ^ (8 * off) + 2 ^ (8 * off) ≤
        2 ^ (8 * total) * 2 ^ (8 * off) := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ hfill_lt
    rw [hpow]; omega
  have hsum :
      spliceRepeatedBytes oldBits byteVal off total n =
        (oldBits % 2 ^ (8 * off) + repeatByteBits byteVal total * 2 ^ (8 * off)) +
          (oldBits / 2 ^ (8 * (off + total))) * 2 ^ (8 * (off + total)) := by
    change wrapScalarBits oldBits (scalarModulus n) % scalarModulus off +
        (repeatByteBits byteVal total * scalarModulus off +
          (wrapScalarBits oldBits (scalarModulus n) / scalarModulus (Nat.add off total)) *
            scalarModulus (Nat.add off total)) = _
    rw [hwrap, hlow_eq, hhigh_eq, ← Nat.add_assoc]
  rw [hsum, wbByte_of_split hmid_lt]
  by_cases hhi : i < off + total
  · simp only [hhi, and_true, ↓reduceIte, wbByte_of_split hlow_lt]
    by_cases hlo : i < off
    · have hnot_ge : ¬ (off ≤ i) := by omega
      simp only [hlo, hnot_ge, ↓reduceIte]
      have hold_decomp : oldBits =
          oldBits % 2 ^ (8 * off) + (oldBits / 2 ^ (8 * off)) * 2 ^ (8 * off) := by
        have h := (Nat.mod_add_div oldBits (2 ^ (8 * off))).symm
        rwa [Nat.mul_comm (2 ^ (8 * off))] at h
      conv => rhs; rw [hold_decomp]
      rw [wbByte_of_split hlow_lt]
      simp [hlo]
    · have hge : off ≤ i := by omega
      simp only [hlo, hge, ↓reduceIte]
      exact wbAlloc_repeatByteBits_byte byteVal hb total (i - off) (by omega)
  · simp only [hhi, and_false, ↓reduceIte]
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add,
      show 8 * (off + total) + 8 * (i - (off + total)) = 8 * i by omega]

private def wbAlloc_fromLeBytes : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * wbAlloc_fromLeBytes bs

private theorem wbAlloc_fromLeBytes_lt :
    ∀ l : List UInt8, wbAlloc_fromLeBytes l < 2 ^ (8 * l.length)
  | [] => by simp [wbAlloc_fromLeBytes]
  | b :: bs => by
    have ih := wbAlloc_fromLeBytes_lt bs
    have hb := b.toNat_lt
    simp only [wbAlloc_fromLeBytes, List.length_cons]
    rw [show 8 * (bs.length + 1) = 8 + 8 * bs.length by omega, Nat.pow_add]
    have hle : wbAlloc_fromLeBytes bs + 1 ≤ 2 ^ (8 * bs.length) := ih
    have hmul : 256 * (wbAlloc_fromLeBytes bs + 1) ≤ 2 ^ 8 * 2 ^ (8 * bs.length) :=
      Nat.mul_le_mul_left 256 hle
    omega

private theorem wbAlloc_fromLeBytes_byte :
    ∀ (l : List UInt8) (i : Nat) (hi : i < l.length),
      (wbAlloc_fromLeBytes l / 2 ^ (8 * i)) % 256 = (l[i]'hi).toNat
  | [], _, hi => absurd hi (Nat.not_lt_zero _)
  | b :: bs, 0, _ => by
    have hb := b.toNat_lt
    show (b.toNat + 256 * wbAlloc_fromLeBytes bs) / 1 % 256 = b.toNat
    omega
  | b :: bs, j + 1, hi => by
    have hb := b.toNat_lt
    have hj : j < bs.length := by simp at hi; omega
    have hpow : 2 ^ (8 * (j + 1)) = 256 * 2 ^ (8 * j) := by
      rw [show 8 * (j + 1) = 8 + 8 * j by omega, Nat.pow_add]
    have hdiv : (b.toNat + 256 * wbAlloc_fromLeBytes bs) / (256 * 2 ^ (8 * j)) =
        wbAlloc_fromLeBytes bs / 2 ^ (8 * j) := by
      rw [← Nat.div_div_eq_div_mul]
      have h1 : (b.toNat + 256 * wbAlloc_fromLeBytes bs) / 256 = wbAlloc_fromLeBytes bs := by
        omega
      rw [h1]
    show (b.toNat + 256 * wbAlloc_fromLeBytes bs) / 2 ^ (8 * (j + 1)) % 256 = bs[j].toNat
    rw [hpow, hdiv]
    exact wbAlloc_fromLeBytes_byte bs j hj

private theorem wbAlloc_leBytes_fromLeBytes (bytes : Array UInt8) :
    wbAlloc_leBytes (wbAlloc_fromLeBytes bytes.toList) bytes.size = bytes := by
  apply Array.ext
  · simp [wbAlloc_leBytes]
  · intro i hi₁ hi₂
    have hi_list : i < bytes.toList.length := by simpa using hi₂
    have hbyte := wbAlloc_fromLeBytes_byte bytes.toList i hi_list
    simp [wbAlloc_leBytes, hbyte]

private theorem wbIte_pos {P : Prop} [Decidable P] {α : Type _} {a b : α} (h : P) :
    (if P then a else b) = a := by simp [h]

private theorem wbIte_neg {P : Prop} [Decidable P] {α : Type _} {a b : α} (h : ¬ P) :
    (if P then a else b) = b := by simp [h]

private theorem wbAlloc_setList_leBytes_eq_splice
    {oldBits : Nat} {n : Nat} (hold : oldBits < scalarModulus n)
    (byte : UInt8) {off total : Nat} (hinb : off + total ≤ n) :
    wbAlloc_setList off byte (List.range' 0 total) (wbAlloc_leBytes oldBits n) =
      wbAlloc_leBytes (spliceRepeatedBytes oldBits byte.toNat off total n) n := by
  have hsz_old : (wbAlloc_leBytes oldBits n).size = n := wbAlloc_leBytes_size oldBits n
  apply Array.ext
  · rw [wbAlloc_setList_size, hsz_old, wbAlloc_leBytes_size]
  · intro i hi₁ hi₂
    have hi_n : i < n := by rw [wbAlloc_leBytes_size] at hi₂; exact hi₂
    have hget := wbAlloc_setList_getElem? off byte total 0 (wbAlloc_leBytes oldBits n) i (by omega)
    simp only [Array.getElem?_eq_getElem hi₁, Nat.add_zero, Nat.zero_add] at hget
    have hs := spliceRepeatedBytes_byte hold byte.toNat_lt hinb hi_n
    by_cases hcond : off ≤ i ∧ i < off + total
    · rw [wbIte_pos hcond] at hget hs
      injection hget with hget'
      rw [hget']
      simp [wbAlloc_leBytes, hs]
    · rw [wbIte_neg hcond] at hget hs
      have hi_old : i < (wbAlloc_leBytes oldBits n).size := by omega
      rw [Array.getElem?_eq_getElem hi_old] at hget
      injection hget with hget'
      rw [hget']
      simp [wbAlloc_leBytes, hs]

private theorem wbAlloc_range_endExclusive {off total : Nat} (hlt : off + total < 2 ^ 64) :
    (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat off))
      (Miri.ABI.Size.ofBytes (UInt64.ofNat total))).endExclusive =
      .ok (Miri.ABI.Size.ofBytes (UInt64.ofNat (off + total))) := by
  have hsum : UInt64.ofNat off + UInt64.ofNat total = UInt64.ofNat (off + total) :=
    (UInt64.ofNat_add off total).symm
  have hoff_lt : off < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right off total) hlt
  have h1 : (UInt64.ofNat off).toNat = off := UInt64.toNat_ofNat_of_lt hoff_lt
  have h2 : (UInt64.ofNat (off + total)).toNat = off + total := UInt64.toNat_ofNat_of_lt hlt
  have hnot_lt : ¬ (UInt64.ofNat (off + total) < UInt64.ofNat off) := by
    rw [UInt64.lt_iff_toNat_lt, h1, h2]; omega
  unfold Miri.Memory.AllocRange.endExclusive Miri.Memory.AllocRange.end Miri.Memory.allocRange
    Miri.ABI.Size.add Miri.ABI.Size.ofBytes
  simp only [hsum, hnot_lt, ↓reduceIte, Except.mapError]

private theorem wbInitMask_setRange_true {off total n : Nat} (hn : ValidScalarBytes n)
    (hinb : off + total ≤ n) :
    (Miri.Memory.InitMask.new (translateSizeBytes n) true).setRange
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat off))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat total))) true =
      .ok (Miri.Memory.InitMask.new (translateSizeBytes n) true) := by
  have hn_eq : (translateSizeBytes n).bytes.toNat = n := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hn64 : n < 2 ^ 64 := by rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have hlt64 : off + total < 2 ^ 64 := Nat.lt_of_le_of_lt hinb hn64
  have hend := wbAlloc_range_endExclusive hlt64
  have hend_nat : (UInt64.ofNat (off + total)).toNat = off + total :=
    UInt64.toNat_ofNat_of_lt hlt64
  have hle_bytes : UInt64.ofNat (off + total) ≤ (translateSizeBytes n).bytes := by
    rw [UInt64.le_iff_toNat_le, hend_nat, hn_eq]; exact hinb
  have hnot_gt : ¬ ((UInt64.ofNat (off + total)) > (translateSizeBytes n).bytes) := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hend_nat, hn_eq]; omega
  unfold Miri.Memory.InitMask.setRange Miri.Memory.InitMask.new
  rw [hend]
  dsimp only [bind, Except.bind, Miri.Memory.allocRange, Miri.ABI.Size.ofBytes]
  by_cases hfull : UInt64.ofNat off = 0 ∧ (translateSizeBytes n).bytes ≤ UInt64.ofNat (off + total)
  · have hsz_eq : (⟨UInt64.ofNat (off + total)⟩ : Miri.ABI.Size) = translateSizeBytes n := by
      cases hs : translateSizeBytes n with
      | mk nb =>
        rw [hs] at hle_bytes hfull
        exact congrArg Miri.ABI.Size.mk (UInt64.le_antisymm hle_bytes hfull.2)
    rw [wbIte_pos hfull, hsz_eq]
    rfl
  · rw [wbIte_neg hfull]
    simp only [beq_self_eq_true, ↓reduceIte, hnot_gt, pure, Except.pure]

private theorem wbProv_clear_new {off total : Nat} (hpos : 0 < total) (hlt : off + total < 2 ^ 64)
    (raw : Array UInt8) :
    Miri.Memory.ProvenanceMap.clear
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat off))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat total)))
      raw (Miri.ABI.Size.ofBytes 8) (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)) =
      EStateM.Result.ok () Miri.Memory.ProvenanceMap.new := by
  have htot_lt : total < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_left total off) hlt
  have hnz : (UInt64.ofNat total == 0) = false := by
    have ht : (UInt64.ofNat total).toNat = total := UInt64.toNat_ofNat_of_lt htot_lt
    cases hb : (UInt64.ofNat total == 0)
    · rfl
    · have := eq_of_beq hb; rw [this] at ht; simp at ht; omega
  have hend' :
      ({ start := { bytes := UInt64.ofNat off }, size := { bytes := UInt64.ofNat total } } :
        Miri.Memory.AllocRange).endExclusive =
      Except.ok { bytes := UInt64.ofNat (off + total) } := wbAlloc_range_endExclusive hlt
  have hrp : Miri.Memory.ProvenanceMap.new.rangePtrs (Prov := AnnealProv)
      { start := { bytes := UInt64.ofNat off }, size := { bytes := UInt64.ofNat total } }
      { bytes := 8 } = .ok #[] := by
    unfold Miri.Memory.ProvenanceMap.rangePtrs
    simp only [bind, Except.bind]
    with_unfolding_all (conv => lhs; whnf)
    split
    · next r hv =>
      with_unfolding_all (conv at hv => lhs; whnf)
      rw [hend'] at hv
      cases hv
    · next v hv =>
      with_unfolding_all (conv at hv => lhs; whnf)
      rw [hend'] at hv
      cases hv
      with_unfolding_all rfl
  unfold Miri.Memory.ProvenanceMap.clear
  simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes, hnz, Bool.false_eq_true, ↓reduceIte,
    bind, EStateM.bind, EStateM.get, EStateM.set]
  split
  · next a s heq =>
    with_unfolding_all (conv at heq => lhs; whnf)
    split at heq
    · next v hv =>
      with_unfolding_all (conv at hv => lhs; whnf)
      rw [hend'] at hv
      cases hv
      injection heq with ha hs
      subst ha hs
      dsimp only []
      with_unfolding_all erw [hrp]
      with_unfolding_all rfl
    · next r hv =>
      with_unfolding_all (conv at hv => lhs; whnf)
      rw [hend'] at hv
      cases hv
  · next e s heq =>
    with_unfolding_all (conv at heq => lhs; whnf)
    split at heq
    · next v hv => cases heq
    · next r hv =>
      with_unfolding_all (conv at hv => lhs; whnf)
      rw [hend'] at hv
      cases hv

/-- Any in-bounds positive `Allocation.writeRepeatedByte` (`0 < total`,
`off + total ≤ n`) on an already initialized `StackScalarAllocShape` scalar
allocation storing `oldSc` (`ScalarRel oldSc oldMsc`) splices bytes
`[off, off + total)` with `byte`, preserves `StackScalarAllocShape` and
initialization, and yields `readScalar = .ok (.fromScalarInt msc)` with
`ScalarRel ⟨spliceRepeatedBytes oldSc.bits byte.toNat off total n, n⟩ msc`. -/
theorem StackScalarAllocShape.writeRepeatedByte_partial {E : Type} {n : Nat}
    (hn : ValidScalarBytes n) {oldSc : MirAst.ScalarInt} {oldMsc : Miri.Memory.ScalarInt}
    (holdRel : ScalarRel oldSc oldMsc) (holdSz : oldSc.sizeBytes = n)
    (byte : UInt8) {off total : Nat} (hpos : 0 < total) (hinb : off + total ≤ n)
    {A : Miri.Memory.Allocation AnnealProv E}
    (hshape : StackScalarAllocShape (translateSizeBytes n) A)
    (hread_old : A.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) false =
      .ok (Miri.Memory.Scalar.fromScalarInt oldMsc)) :
    ∃ (alloc' : Miri.Memory.Allocation AnnealProv E) (msc : Miri.Memory.ScalarInt),
      Miri.Memory.Allocation.writeRepeatedByte (Miri.ABI.Size.ofBytes (UInt64.ofNat off)) byte
          (UInt64.ofNat total) (Miri.ABI.Size.ofBytes 8) A = .ok () alloc' ∧
      ScalarRel ⟨spliceRepeatedBytes oldSc.bits byte.toNat off total n, n⟩ msc ∧
      alloc'.align = A.align ∧
      StackScalarAllocShape (translateSizeBytes n) alloc' ∧
      alloc'.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) = .ok (.ok ()) ∧
      alloc'.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) false =
        .ok (Miri.Memory.Scalar.fromScalarInt msc) := by
  have hold_can : oldSc.bits < scalarModulus n := holdSz ▸ holdRel.canonical
  have hcan : spliceRepeatedBytes oldSc.bits byte.toNat off total n < scalarModulus n :=
    spliceRepeatedBytes_lt_scalarModulus oldSc.bits byte.toNat_lt hinb
  obtain ⟨msc, _, hrel⟩ :=
    tryFromUInt_of_valid_canonical
      (sc := ⟨spliceRepeatedBytes oldSc.bits byte.toNat off total n, n⟩) hn hcan
  have hn_eq : (translateSizeBytes n).bytes.toNat = n := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hn16 : n ≤ 16 := by rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have hn16_tr : (translateSizeBytes n).bytes.toNat ≤ 16 := by rw [hn_eq]; exact hn16
  have hend_full := wbAlloc_allocRange_end (translateSizeBytes n)
  have hinitA : A.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) = .ok (.ok ()) :=
    Classical.byContradiction fun hni => by
      obtain ⟨_, herr⟩ := hshape.uninit_readScalar_err hni false
      rw [hread_old] at herr
      cases herr
  -- Decode `wbAlloc_raw A = wbAlloc_leBytes oldSc.bits n`.
  have hraw_old : wbAlloc_raw A = wbAlloc_leBytes oldSc.bits n := by
    have hraw_sz : (wbAlloc_raw A).size = n := hshape.len_eq.trans hn_eq
    let x := wbAlloc_fromLeBytes (wbAlloc_raw A).toList
    have hx_can : x < scalarModulus n := by
      rw [wbAlloc_scalarModulus_eq_two_pow]
      have hlt := wbAlloc_fromLeBytes_lt (wbAlloc_raw A).toList
      have hlen_l : (wbAlloc_raw A).toList.length = n := by simpa using hraw_sz
      rw [hlen_l] at hlt
      exact hlt
    obtain ⟨xmsc, _, hx_rel⟩ := tryFromUInt_of_valid_canonical (sc := ⟨x, n⟩) hn hx_can
    have hraw_x : wbAlloc_raw A = wbAlloc_leBytes x n := by
      have := wbAlloc_leBytes_fromLeBytes (wbAlloc_raw A)
      rw [hraw_sz] at this
      exact this.symm
    have hslice_A : wbAlloc_checkedSlice A
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) =
        .ok (wbAlloc_leBytes x (translateSizeBytes n).bytes.toNat) := by
      have hrawsize : (wbAlloc_raw A).size = (translateSizeBytes n).bytes.toNat := hshape.len_eq
      unfold wbAlloc_checkedSlice
      simp only [hrawsize, hshape.byteSize_eq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        hend_full, Except.mapError, bind, Except.bind]
      simp [Miri.Memory.allocRange, Miri.ABI.Size.ZERO, pure, Except.pure, hraw_x, hn_eq,
        wbAlloc_leBytes_size]
    have hoff_addr : Miri.Memory.PointerProvenance.offsetIsAddr AnnealProv = true := rfl
    have hx_mod : x % 2 ^ (8 * (translateSizeBytes n).bytes.toNat) = x := by
      rw [hn_eq, ← wbAlloc_scalarModulus_eq_two_pow]
      exact Nat.mod_eq_of_lt hx_can
    have hrange_sz :
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)).size =
          translateSizeBytes n := rfl
    have hread_x : A.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) false =
        .ok (Miri.Memory.Scalar.fromScalarInt xmsc) := by
      rw [wbAlloc_readScalar_eq]
      unfold wbAlloc_readScalar
      rw [hinitA]
      simp only [Except.mapError, bind, Except.bind]
      rw [wbAlloc_getBytesUnchecked_eq, hslice_A]
      simp only []
      rw [wbAlloc_readTargetUInt_leBytes _ _ hn16_tr, hx_mod]
      simp only [Bool.false_eq_true, ↓reduceIte, hoff_addr, hrange_sz, wbAlloc_fromUInt hx_rel]
    have hsc_eq : Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) xmsc =
        Miri.Memory.Scalar.fromScalarInt oldMsc :=
      Except.ok.inj (hread_x.symm.trans hread_old)
    have hdata_eq : BitVec.ofNat 128 x = BitVec.ofNat 128 oldSc.bits := by
      unfold Miri.Memory.Scalar.fromScalarInt at hsc_eq
      injection hsc_eq with hpay _
      injection hpay with hmsc_eq
      exact hx_rel.data_eq.symm.trans ((congrArg Miri.Memory.ScalarInt.data hmsc_eq).trans
        holdRel.data_eq)
    have hx_eq : x = oldSc.bits := by
      have hpow128 : scalarModulus n ≤ 2 ^ 128 := by
        rw [wbAlloc_scalarModulus_eq_two_pow]
        exact Nat.pow_le_pow_right (by decide) (by omega)
      have h1 : (BitVec.ofNat 128 x).toNat = x := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hx_can hpow128)
      have h2 : (BitVec.ofNat 128 oldSc.bits).toNat = oldSc.bits := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hold_can hpow128)
      rw [← h1, ← h2, hdata_eq]
    rw [hraw_x, hx_eq]
  -- Evaluate `Allocation.writeRepeatedByte` on `A`.
  obtain ⟨alloc', hw, halign', hshape', hinit', hraw'⟩ :
      ∃ alloc' : Miri.Memory.Allocation AnnealProv E,
        Miri.Memory.Allocation.writeRepeatedByte (Miri.ABI.Size.ofBytes (UInt64.ofNat off)) byte
            (UInt64.ofNat total) (Miri.ABI.Size.ofBytes 8) A = .ok () alloc' ∧
        alloc'.align = A.align ∧
        StackScalarAllocShape (translateSizeBytes n) alloc' ∧
        alloc'.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) = .ok (.ok ()) ∧
        wbAlloc_raw alloc' =
          wbAlloc_leBytes (spliceRepeatedBytes oldSc.bits byte.toNat off total n) n := by
    have hn64 : n < 2 ^ 64 := by rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
    have hlt64 : off + total < 2 ^ 64 := Nat.lt_of_le_of_lt hinb hn64
    have hoff64 : off < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right off total) hlt64
    have htot64 : total < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_left total off) hlt64
    have hslice_sub : Miri.Memory.Allocation.getBytesUnchecked A
        (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat off))
          (Miri.ABI.Size.ofBytes (UInt64.ofNat total))) =
        .ok ((wbAlloc_raw A).extract off (off + total)) := by
      rw [wbAlloc_getBytesUnchecked_eq]; unfold wbAlloc_checkedSlice
      have hrawsize : (wbAlloc_raw A).size = (translateSizeBytes n).bytes.toNat := hshape.len_eq
      have hend_sub := wbAlloc_range_endExclusive hlt64
      have hoff_u64 : (UInt64.ofNat off).toNat = off := UInt64.toNat_ofNat_of_lt hoff64
      have hend_u64 : (UInt64.ofNat (off + total)).toNat = off + total :=
        UInt64.toNat_ofNat_of_lt hlt64
      have hnot_gt1 : ¬ (UInt64.ofNat off > UInt64.ofNat (off + total)) := by
        rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hoff_u64, hend_u64]; omega
      have hnot_gt2 : ¬ (UInt64.ofNat (off + total) > (translateSizeBytes n).bytes) := by
        rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hend_u64, hn_eq]; omega
      have hcond_false :
          (decide (UInt64.ofNat off > UInt64.ofNat (off + total)) ||
            decide (UInt64.ofNat (off + total) > (translateSizeBytes n).bytes)) = false := by
        rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
        exact ⟨hnot_gt1, hnot_gt2⟩
      rw [hend_sub]
      simp only [hrawsize, hshape.byteSize_eq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        Except.mapError, bind, Except.bind, Miri.Memory.allocRange, Miri.ABI.Size.ofBytes]
      erw [hcond_false]
      simp only [Bool.false_eq_true, ↓reduceIte, hoff_u64, hend_u64, pure, Except.pure]
    unfold Miri.Memory.Allocation.getBytesUnchecked at hslice_sub
    rcases hshape with ⟨hsz, hlen, hmut, hprov, ⟨initBool, hmask⟩⟩
    have hbInit : initBool = true := by
      cases initBool with
      | true => rfl
      | false =>
        rw [hmask] at hinitA
        rcases hn with rfl | rfl | rfl | rfl | rfl <;> cases hinitA
    subst hbInit
    let res := Miri.Memory.Allocation.writeRepeatedByte (Miri.ABI.Size.ofBytes (UInt64.ofNat off))
      byte (UInt64.ofNat total) (Miri.ABI.Size.ofBytes 8) A
    have hres_def : res = Miri.Memory.Allocation.writeRepeatedByte
        (Miri.ABI.Size.ofBytes (UInt64.ofNat off)) byte (UInt64.ofNat total)
        (Miri.ABI.Size.ofBytes 8) A := rfl
    rcases A with ⟨rawBytes, size, provenance, initMask, align, mutability, extra, nativeBuffer⟩
    unfold Miri.Memory.Allocation.byteSize at hsz
    unfold Miri.Memory.Allocation.len at hlen
    unfold Miri.Memory.Allocation.provenanceMap at hprov
    unfold Miri.Memory.Allocation.initializationMask at hmask
    dsimp only [wbAlloc_raw] at hsz hlen hmut hprov hmask hraw_old
    subst hsz hmut hprov hmask hraw_old
    have hcnt_nz : (UInt64.ofNat total == 0) = false := by
      have ht : (UInt64.ofNat total).toNat = total := UInt64.toNat_ofNat_of_lt htot64
      cases hb : (UInt64.ofNat total == 0)
      · rfl
      · have := eq_of_beq hb; rw [this] at ht; simp at ht; omega
    have hstart_nat :
        (Miri.ABI.Size.ofBytes (UInt64.ofNat off)).bytes.toNat = off :=
      UInt64.toNat_ofNat_of_lt hoff64
    have hcnt_nat : (UInt64.ofNat total).toNat = total :=
      UInt64.toNat_ofNat_of_lt htot64
    have hmask_ok := wbInitMask_setRange_true hn hinb
    have hprov_ok := wbProv_clear_new hpos hlt64 (wbAlloc_leBytes oldSc.bits n)
    have hset_eq := wbAlloc_setList_leBytes_eq_splice hold_can byte hinb
    have hloop_inb : off + (0 + total) ≤ (wbAlloc_leBytes oldSc.bits n).size := by
      rw [wbAlloc_leBytes_size]; omega
    unfold Miri.Memory.Allocation.writeRepeatedByte at hres_def
    dsimp only [] at hres_def
    rw [hslice_sub] at hres_def
    dsimp only [] at hres_def
    rw [hcnt_nz] at hres_def
    simp only [Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, pure_bind, Id.run] at hres_def
    split at hres_def
    · next initialized heq =>
      have heq' := heq
      with_unfolding_all (conv at heq' => lhs; whnf)
      rw [hmask_ok] at heq'
      with_unfolding_all (conv at heq' => lhs; whnf)
      injection heq' with hinit_eq
      subst hinit_eq
      dsimp only [] at hres_def
      with_unfolding_all erw [hprov_ok] at hres_def
      simp only [hstart_nat, hcnt_nat, Std.Legacy.Range.forIn_eq_forIn_range',
        Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
        wbAlloc_forIn_eq_fallback, wbAlloc_fallback_eq_setList _ _ _ total 0 _ hloop_inb,
        hset_eq] at hres_def
      have hinit_res :
          (Miri.Memory.InitMask.new (translateSizeBytes n) true).isRangeInitialized
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) = .ok (.ok ()) := by
        rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
      refine ⟨_, hres_def, rfl, ⟨rfl, ?_, rfl, rfl, ⟨true, rfl⟩⟩, hinit_res, rfl⟩
      change (wbAlloc_leBytes (spliceRepeatedBytes oldSc.bits byte.toNat off total n) n).size =
        (translateSizeBytes n).bytes.toNat
      rw [wbAlloc_leBytes_size, hn_eq]
    · next reason heq =>
      with_unfolding_all (conv at heq => lhs; whnf)
      rw [hmask_ok] at heq
      with_unfolding_all (conv at heq => lhs; whnf)
      cases heq
  refine ⟨alloc', msc, hw, hrel, halign', hshape', hinit', ?_⟩
  have hraw_le : wbAlloc_raw alloc' =
      wbAlloc_leBytes (spliceRepeatedBytes oldSc.bits byte.toNat off total n)
        (translateSizeBytes n).bytes.toNat := by
    rw [hraw', hn_eq]
  have hslice_read : wbAlloc_checkedSlice alloc'
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) =
      .ok (wbAlloc_leBytes (spliceRepeatedBytes oldSc.bits byte.toNat off total n)
        (translateSizeBytes n).bytes.toNat) := by
    have hrawsize : (wbAlloc_raw alloc').size = (translateSizeBytes n).bytes.toNat :=
      hshape'.len_eq
    unfold wbAlloc_checkedSlice
    simp only [hrawsize, hshape'.byteSize_eq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      hend_full, Except.mapError, bind, Except.bind]
    simp [Miri.Memory.allocRange, Miri.ABI.Size.ZERO, pure, Except.pure, hraw_le,
      wbAlloc_leBytes_size]
  have hoff_addr : Miri.Memory.PointerProvenance.offsetIsAddr AnnealProv = true := rfl
  have hmod :
      spliceRepeatedBytes oldSc.bits byte.toNat off total n %
        2 ^ (8 * (translateSizeBytes n).bytes.toNat) =
      spliceRepeatedBytes oldSc.bits byte.toNat off total n := by
    rw [hn_eq, ← wbAlloc_scalarModulus_eq_two_pow]
    exact Nat.mod_eq_of_lt hcan
  have hrange :
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)).size =
        translateSizeBytes n := rfl
  rw [wbAlloc_readScalar_eq]
  unfold wbAlloc_readScalar
  rw [hinit']
  simp only [Except.mapError, bind, Except.bind]
  rw [wbAlloc_getBytesUnchecked_eq, hslice_read]
  simp only []
  rw [wbAlloc_readTargetUInt_leBytes _ _ hn16_tr, hmod]
  simp only [Bool.false_eq_true, ↓reduceIte, hoff_addr, hrange, wbAlloc_fromUInt hrel]

/-! ## 5. `annealWriteBytesEval` reduction and post-step `allocMap` -/

private theorem wbAnnealWriteBytesEval_uninit_dst {ly : LayoutTable}
    {ptrLay : Miri.Interpreter.LocalLayout} {ptId : Miri.MIR.TyId}
    (v₂ v₃ : Miri.Interpreter.OpTy AnnealProv) (m : AnnealStepState)
    (hpt : annealPointeeTypeOf ptrLay.ty m = .ok ptId m) :
    annealWriteBytesEval ly ⟨.immediate .uninit, ptrLay⟩ v₂ v₃ m =
      .error (.undefinedBehavior "read of uninitialized local") m := by
  unfold annealWriteBytesEval
  rw [EStateM.bind_eq_ok hpt, EStateM.bind_eq_error (wbIntrinsicPointer_uninit ptrLay m)]

private theorem wbAnnealWriteBytesEval_uninit_val {ly : LayoutTable}
    {v₁ v₃ : Miri.Interpreter.OpTy AnnealProv} {valLay : Miri.Interpreter.LocalLayout}
    {ptId : Miri.MIR.TyId} {ptr : Miri.Memory.Pointer (Option AnnealProv)}
    (m : AnnealStepState)
    (hpt : annealPointeeTypeOf v₁.layout.ty m = .ok ptId m)
    (hptr : intrinsicPointer v₁ m = .ok ptr m) :
    annealWriteBytesEval ly v₁ ⟨.immediate .uninit, valLay⟩ v₃ m =
      .error (.undefinedBehavior "read of uninitialized local") m := by
  unfold annealWriteBytesEval
  rw [EStateM.bind_eq_ok hpt, EStateM.bind_eq_ok hptr,
    EStateM.bind_eq_error (wbIntrinsicScalar_uninit valLay m)]

private theorem wbAnnealWriteBytesEval_uninit_count {ly : LayoutTable}
    {v₁ : Miri.Interpreter.OpTy AnnealProv} {valLay countLay : Miri.Interpreter.LocalLayout}
    {ptId : Miri.MIR.TyId} {ptr : Miri.Memory.Pointer (Option AnnealProv)}
    {valSc : MirAst.ScalarInt} {mval : Miri.Memory.ScalarInt}
    (m : AnnealStepState)
    (hpt : annealPointeeTypeOf v₁.layout.ty m = .ok ptId m)
    (hptr : intrinsicPointer v₁ m = .ok ptr m)
    (hrelV : ScalarRel valSc mval) (hszV : valSc.sizeBytes = 1) :
    annealWriteBytesEval ly v₁ ⟨.immediate (.scalar (.fromScalarInt mval)), valLay⟩
        ⟨.immediate .uninit, countLay⟩ m =
      .error (.undefinedBehavior "read of uninitialized local") m := by
  have hsV : intrinsicScalar ⟨.immediate (.scalar (.fromScalarInt mval)), valLay⟩ m =
      .ok (.fromScalarInt mval) m := rfl
  have hlift : liftScalarResult
      ((Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) mval).toUInt8 |>.mapError
        Miri.Interpreter.ScalarOps.scalarError) m =
      .ok (UInt8.ofNat valSc.bits) m := by
    rw [(wbScalar_fromScalarInt_toUInt8 hrelV hszV).2]; rfl
  unfold annealWriteBytesEval
  rw [EStateM.bind_eq_ok hpt, EStateM.bind_eq_ok hptr, EStateM.bind_eq_ok hsV,
    EStateM.bind_eq_ok hlift, EStateM.bind_eq_error (wbIntrinsicUsize_uninit countLay m)]

private theorem wbAnnealWriteBytesEval_init {ly : LayoutTable}
    {v₁ : Miri.Interpreter.OpTy AnnealProv} {valLay countLay : Miri.Interpreter.LocalLayout}
    {ptId : Miri.MIR.TyId} {elemBytes : Nat}
    {ptr : Miri.Memory.Pointer (Option AnnealProv)}
    {valSc countSc : MirAst.ScalarInt} {mval mcount : Miri.Memory.ScalarInt}
    (m : AnnealStepState)
    (hpt : annealPointeeTypeOf v₁.layout.ty m = .ok ptId m)
    (hlay_sz : (layoutOfEncodedTyId ptId ly).layout.size =
      Miri.ABI.Size.ofBytes (UInt64.ofNat elemBytes))
    (helem_lt : elemBytes < 2 ^ 64)
    (hptr : intrinsicPointer v₁ m = .ok ptr m)
    (hrelV : ScalarRel valSc mval) (hszV : valSc.sizeBytes = 1)
    (hrelC : ScalarRel countSc mcount) (hszC : countSc.sizeBytes = 8) :
    annealWriteBytesEval ly v₁ ⟨.immediate (.scalar (.fromScalarInt mval)), valLay⟩
        ⟨.immediate (.scalar (.fromScalarInt mcount)), countLay⟩ m =
      if countSc.bits * elemBytes ≤ isizeMaxBytes then
        annealWriteRepeatedBytes ptr (UInt8.ofNat valSc.bits)
          (Miri.ABI.Size.ofBytes (UInt64.ofNat (countSc.bits * elemBytes))) m
      else
        .error (.undefinedBehavior "overflow computing total size of write_bytes") m := by
  have hsV : intrinsicScalar ⟨.immediate (.scalar (.fromScalarInt mval)), valLay⟩ m =
      .ok (.fromScalarInt mval) m := rfl
  have hlift : liftScalarResult
      ((Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) mval).toUInt8 |>.mapError
        Miri.Interpreter.ScalarOps.scalarError) m =
      .ok (UInt8.ofNat valSc.bits) m := by
    rw [(wbScalar_fromScalarInt_toUInt8 hrelV hszV).2]; rfl
  have hcnt := wbIntrinsicUsize_fromScalarInt hrelC hszC countLay m
  have hcnt_lt := (wbScalar_fromScalarInt_toTargetUsize hrelC hszC).1
  have hcomp := computeSizeInBytes_writeBytes helem_lt hcnt_lt
  unfold annealWriteBytesEval
  rw [EStateM.bind_eq_ok hpt, EStateM.bind_eq_ok hptr, EStateM.bind_eq_ok hsV,
    EStateM.bind_eq_ok hlift, EStateM.bind_eq_ok hcnt, hlay_sz, hcomp]
  by_cases hle : countSc.bits * elemBytes ≤ isizeMaxBytes
  · simp only [hle, ↓reduceIte]
  · simp only [hle, ↓reduceIte]; rfl

/-- Syntactic pre-state scalar value of a `WellTypedScalarOperand` (`constant`
or `copy` of an unprojected local), stated directly on `locals` without
mentioning `evalOperand` or `stepMirFn`. -/
def WriteBytesScalarPreVal (locals : List LocalSlot) (op : MirAst.Operand)
    (sc : MirAst.ScalarInt) : Prop :=
  (∃ cc, op = .constant cc ∧ cc.val = .scalar (.int sc)) ∨
    (∃ idx, op = .copy ⟨idx, []⟩ ∧ get? locals idx = some (.init (.scalar sc)))

/-- Extract the scalar value of a constant or copied unprojected local directly
from `locals`. -/
def writeBytesScalarVal? (locals : List LocalSlot) : MirAst.Operand → Option MirAst.ScalarInt
  | .constant cc =>
    match cc.val with
    | .scalar (.int sc) => some sc
    | _ => none
  | .copy ⟨idx, []⟩ =>
    match get? locals idx with
    | some (.init (.scalar sc)) => some sc
    | _ => none
  | _ => none

private theorem writeBytesScalarVal?_of_evalOperand_ok
    {body : CapturedMir} {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {locals : List LocalSlot} {op : MirAst.Operand} {ty : Ty} {sc : MirAst.ScalarInt}
    {borrows : List BorrowEntry} {globals : List CapturedAllocation} {callerLocals : List LocalSlot}
    (hop : WellTypedScalarOperand body tf op ty)
    (heval : evalOperand locals op borrows globals body.layouts callerLocals =
      .ok (.scalar sc) locals) :
    writeBytesScalarVal? locals op = some sc ∧ WriteBytesScalarPreVal locals op sc := by
  cases hop with
  | constScalar c sc₀ hval _ _ _ _ _ _ =>
    unfold evalOperand at heval
    dsimp only at heval
    rw [hval] at heval
    injection heval with hv _
    injection hv with hsc
    subst hsc
    exact ⟨by simp [writeBytesScalarVal?, hval], Or.inl ⟨c, rfl, hval⟩⟩
  | copyLocal idx _ _ _ _ =>
    rw [wbEvalOperand_copy_local_eq] at heval
    cases hslot : get? locals idx with
    | none => rw [hslot] at heval; cases heval
    | some slot =>
      cases slot with
      | dead => rw [hslot] at heval; cases heval
      | uninit => rw [hslot] at heval; cases heval
      | init v =>
        rw [hslot] at heval
        injection heval with hv _
        subst hv
        exact ⟨by simp [writeBytesScalarVal?, hslot], Or.inr ⟨idx, rfl, hslot⟩⟩

/-- Computable post-step `allocMap'` for
`write_bytes::<T>(copy _ptr, valOp, countOp)` with pointee byte size
`elemBytes`: leaves `allocMap` unchanged on zero-byte writes
(`count * elemBytes = 0`) or non-tracked pointers, and applies
`updateAllocMapOnWrite allocMap e.localIdx (some ptrVal.tag)` on positive-byte
writes through a tracked pointer `ptrVal`. -/
def writeBytesNextAllocMap (locals : List LocalSlot) (allocMap : List AllocMapEntry)
    (ptrIdx : Local) (countOp : MirAst.Operand) (elemBytes : Nat) : List AllocMapEntry :=
  match writeBytesScalarVal? locals countOp with
  | some countSc =>
    if countSc.bits * elemBytes = 0 then
      allocMap
    else
      match get? locals ptrIdx with
      | some (.init (.ptr ptrVal 8)) =>
        match lookupAllocMapByTag allocMap ptrVal.tag with
        | some e => updateAllocMapOnWrite allocMap e.localIdx (some ptrVal.tag)
        | none => allocMap
      | _ => allocMap
  | none => allocMap

private theorem wbInvalidateConflictingBorrows_eq_map_updateAllocMapOnWrite
    (allocMap : List AllocMapEntry) (targetLocal : Local) (writerTag : Option Nat) :
    invalidateConflictingBorrows (allocMap.map AllocMapEntry.toBorrowEntry) targetLocal writerTag =
      (updateAllocMapOnWrite allocMap targetLocal writerTag).map AllocMapEntry.toBorrowEntry := by
  induction allocMap with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.map_cons, invalidateConflictingBorrows_cons, updateAllocMapOnWrite,
      AllocMapEntry.toBorrowEntry_updateOnWrite, ih]

private theorem wbUpdateOnWrite_eq_self_of_active
    {x : AllocMapEntry} {targetLocal : Local} {wTag : Nat}
    (hx : x.localIdx = targetLocal →
      (x.tag = wTag ∧ x.perm = .active) ∨ (x.tag ≠ wTag ∧ x.perm = .disabled)) :
    x.updateOnWrite targetLocal (some wTag) = x := by
  rcases x with ⟨tag, localIdx, allocId, perm⟩
  unfold AllocMapEntry.updateOnWrite AllocMapEntry.toBorrowEntry updateBorrowPerm
    treeBorrowWriterRelatedness treeBorrowNodeAccess applyTreeBorrowTransition
  dsimp only
  cases hloc : Nat.beq localIdx targetLocal with
  | false => rfl
  | true =>
    rcases hx (Nat.eq_of_beq_eq_true hloc) with ⟨htag, hact⟩ | ⟨htag_ne, hdis⟩
    · dsimp only at htag hact
      subst htag hact
      rw [Nat.beq_refl]; rfl
    · dsimp only at htag_ne hdis
      subst hdis
      have hbeq : Nat.beq tag wTag = false := by
        cases h : Nat.beq tag wTag
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) htag_ne
      rw [hbeq]

/-- When `e.perm = .active` and every foreign borrow of `e.localIdx` in
`allocMap` is already `.disabled` (in particular, whenever `e` is the unique
borrow of `e.localIdx`), writing through `e.tag` leaves `allocMap` unchanged. -/
theorem updateAllocMapOnWrite_eq_self_of_active
    {allocMap : List AllocMapEntry} {targetLocal : Local} {wTag : Nat}
    (hperm : ∀ x ∈ allocMap, x.localIdx = targetLocal →
      (x.tag = wTag ∧ x.perm = .active) ∨ (x.tag ≠ wTag ∧ x.perm = .disabled)) :
    updateAllocMapOnWrite allocMap targetLocal (some wTag) = allocMap := by
  induction allocMap with
  | nil => rfl
  | cons x xs ih =>
    simp only [updateAllocMapOnWrite, List.map_cons] at ih ⊢
    rw [wbUpdateOnWrite_eq_self_of_active (hperm x (List.mem_cons_self ..)),
      ih (fun y hy => hperm y (List.mem_cons_of_mem _ hy))]

/-! ## 6. Full-step `write_bytes` simulation and characterized divergences -/

private theorem wbImmediateRel_of_integral {ty : Ty} {ly : LayoutTable}
    {kind : Miri.MIR.IntegerKind} {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (h : IsIntegralTy ty kind)
    (hrelI : ImmediateRel ty ly (.scalar sc) (.scalar (.fromScalarInt msc))) :
    ScalarRel sc msc ∧ sc.sizeBytes = integerKindByteWidth kind := by
  obtain ⟨sc', msc', hsc, hmsc, hrel, hsz, _, _⟩ := hrelI.of_primitive_scalar h.prim
  injection hsc with hsc'; subst hsc'
  injection hmsc with h1
  unfold Miri.Memory.Scalar.fromScalarInt at h1
  injection h1 with h2
  injection h2 with h3; subst h3
  have hlay_sz :
      (translateTy ty ly).layout.size = translateSizeBytes (integerKindByteWidth kind) := by
    rw [← h.prim.translateTy_layoutIdx ly]
    rcases h with ⟨it, hk⟩ | ⟨ut, hk⟩
    · rw [hk]; cases it <;> rfl
    · rw [hk]; cases ut <;> rfl
  have heq : (translateSizeBytes sc.sizeBytes).bytes.toNat =
      (translateSizeBytes (integerKindByteWidth kind)).bytes.toNat := by
    rw [← hsz, hlay_sz]
  have h1 : (translateSizeBytes sc.sizeBytes).bytes.toNat = sc.sizeBytes := by
    rcases hrel.validBytes with hsz1 | hsz1 | hsz1 | hsz1 | hsz1 <;> (rw [hsz1]; rfl)
  have h2 : (translateSizeBytes (integerKindByteWidth kind)).bytes.toNat =
      integerKindByteWidth kind := by
    cases kind <;> rfl
  exact ⟨hrel, h1 ▸ h2 ▸ heq⟩

private theorem wbValidScalarBytes_integerKind (kind : Miri.MIR.IntegerKind) :
    ValidScalarBytes (integerKindByteWidth kind) := by
  cases kind <;> simp [ValidScalarBytes, integerKindByteWidth]

private def wbMiriBodyAction (body : CapturedMir) (ptrIdx : Local)
    (valOp countOp : MirAst.Operand) :
    EStateM Miri.Interpreter.StepError AnnealStepState Unit := do
  let v₁ ← annealEvalOperand body.localDecls body.layouts (.Copy ⟨ptrIdx, #[]⟩) none
  let v₂ ← annealEvalOperand body.localDecls body.layouts (translateOperand valOp) none
  let v₃ ← annealEvalOperand body.localDecls body.layouts (translateOperand countOp) none
  annealWriteBytesEval body.layouts v₁ v₂ v₃

private theorem wbMiri_step_writeBytes_ub
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {bb : BasicBlockData} {c : ConstOperand} {ptrIdx dstIdx : Local}
    {valOp countOp : MirAst.Operand} {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    {pointeeKind : RigidTy} {dstDecl : LocalDecl} {msg : String}
    (hframes : m.stack.frames = #[tf])
    (hbody : tf.body = translateBody body)
    (hloc : tf.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hterm : bb.terminator.kind =
      .call (.constant c) [.copy ⟨ptrIdx, []⟩, valOp, countOp] ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef AnnealIntrinsic.writeBytes.defPath [pointeeKind])
    (hdst : get? body.localDecls dstIdx = some dstDecl)
    (hlt_mf : dstIdx < tf.locals.size)
    (hcache_dst : ∀ l, (tf.locals[dstIdx]'hlt_mf).layout = some l →
      l = translateTy dstDecl.ty body.layouts)
    (hval_nm : ∀ p, translateOperand valOp ≠ .Move p)
    (hcount_nm : ∀ p, translateOperand countOp ≠ .Move p)
    (hact : wbMiriBodyAction body ptrIdx valOp countOp
      { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_mf
          (translateTy dstDecl.ty body.layouts)]⟩ } =
      .error (.undefinedBehavior msg) m') :
    Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
      (m', .error (.undefinedBehavior msg)) := by
  rw [miri_step_at_terminator hframes hbody hloc hbb hstmt_none,
    translateTerminator_intrinsic_call hterm hc]
  simp only [List.map_cons, List.map_nil]
  have hptr_nm : ∀ p, translateOperand (.copy ⟨ptrIdx, []⟩) ≠ .Move p := by
    intro p hp; simp only [translateOperand, reduceCtorEq] at hp
  have htr_ptr : translateOperand (.copy ⟨ptrIdx, []⟩) = .Copy ⟨ptrIdx, #[]⟩ := rfl
  rw [controlFlow_evalTerminator_call _ _ _ rfl,
    evalCallTerminator_intrinsic_three _ _ AnnealIntrinsic.writeBytes _ writeBytes_arity _ _ _
      hptr_nm hval_nm hcount_nm, htr_ptr]
  have hplace := annealEvalPlace_unprojected (body := body) hframes hlt_mf hdst hcache_dst
  let m₁ : AnnealStepState :=
    { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_mf
        (translateTy dstDecl.ty body.layouts)]⟩ }
  have hcallee := annealEvalOperand_fnItemConst_ok body.localDecls body.layouts
    AnnealIntrinsic.writeBytes (encodeTyId { kind := pointeeKind, layoutIdx := 0 }) (m := m₁) rfl
  rw [EStateM.bind_eq_ok (annealPlaceHooks_frameIndex_eq hframes),
    EStateM.bind_eq_ok (annealPlaceHooks_getFrame_eq hframes), EStateM.bind_eq_ok hplace,
    EStateM.bind_eq_ok hcallee]
  unfold wbMiriBodyAction at hact
  cases hv₁ : annealEvalOperand body.localDecls body.layouts (.Copy ⟨ptrIdx, #[]⟩) none m₁ with
  | error e s₁ =>
    rw [EStateM.bind_eq_error hv₁] at hact; cases hact
    rw [EStateM.bind_eq_error hv₁]; rfl
  | ok v₁ s₁ =>
    rw [EStateM.bind_eq_ok hv₁] at hact; rw [EStateM.bind_eq_ok hv₁]
    cases hv₂ : annealEvalOperand body.localDecls body.layouts (translateOperand valOp) none s₁ with
    | error e s₂ =>
      rw [EStateM.bind_eq_error hv₂] at hact; cases hact
      rw [EStateM.bind_eq_error hv₂]; rfl
    | ok v₂ s₂ =>
      rw [EStateM.bind_eq_ok hv₂] at hact; rw [EStateM.bind_eq_ok hv₂]
      cases hv₃ : annealEvalOperand body.localDecls body.layouts
          (translateOperand countOp) none s₂ with
      | error e s₃ =>
        rw [EStateM.bind_eq_error hv₃] at hact; cases hact
        rw [EStateM.bind_eq_error hv₃]; rfl
      | ok v₃ s₃ =>
        rw [EStateM.bind_eq_ok hv₃] at hact
        rw [EStateM.bind_eq_ok hv₃, intrinsics_eval_writeBytes]
        have hev : (do
            annealWriteBytesEval body.layouts v₁ v₂ v₃
            annealReturnToBlock (some targetBb)
            pure true) s₃ = .error (.undefinedBehavior msg) m' := by
          rw [EStateM.bind_eq_error hact]
        rw [EStateM.bind_eq_error hev]; rfl

private theorem wbMiri_step_writeBytes_ok
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {tf tf₃ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {mach' : AnnealMachine}
    {bb : BasicBlockData} {c : ConstOperand} {ptrIdx dstIdx : Local}
    {valOp countOp : MirAst.Operand} {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    {pointeeKind : RigidTy} {dstDecl : LocalDecl}
    (hframes : m.stack.frames = #[tf])
    (hbody : tf.body = translateBody body)
    (hloc : tf.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hterm : bb.terminator.kind =
      .call (.constant c) [.copy ⟨ptrIdx, []⟩, valOp, countOp] ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef AnnealIntrinsic.writeBytes.defPath [pointeeKind])
    (hprog : targetBb ≠ s.frame.blockIdx ∨ s.frame.stmtIdx ≠ 0)
    (hdst : get? body.localDecls dstIdx = some dstDecl)
    (hlt_mf : dstIdx < tf.locals.size)
    (hcache_dst : ∀ l, (tf.locals[dstIdx]'hlt_mf).layout = some l →
      l = translateTy dstDecl.ty body.layouts)
    (hval_nm : ∀ p, translateOperand valOp ≠ .Move p)
    (hcount_nm : ∀ p, translateOperand countOp ≠ .Move p)
    (hact : wbMiriBodyAction body ptrIdx valOp countOp
      { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_mf
          (translateTy dstDecl.ty body.layouts)]⟩ } =
      .ok () { stack := ⟨#[tf₃]⟩, machine := mach' }) :
    Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
      ({ stack := ⟨#[{ tf₃ with location := .mir ⟨targetBb, 0⟩ }]⟩, machine := mach' },
        .ok true) := by
  rw [miri_step_at_terminator hframes hbody hloc hbb hstmt_none,
    translateTerminator_intrinsic_call hterm hc]
  simp only [List.map_cons, List.map_nil]
  have hptr_nm : ∀ p, translateOperand (.copy ⟨ptrIdx, []⟩) ≠ .Move p := by
    intro p hp; simp only [translateOperand, reduceCtorEq] at hp
  have htr_ptr : translateOperand (.copy ⟨ptrIdx, []⟩) = .Copy ⟨ptrIdx, #[]⟩ := rfl
  rw [controlFlow_evalTerminator_call _ _ _ rfl,
    evalCallTerminator_intrinsic_three _ _ AnnealIntrinsic.writeBytes _ writeBytes_arity _ _ _
      hptr_nm hval_nm hcount_nm, htr_ptr]
  have hplace := annealEvalPlace_unprojected (body := body) hframes hlt_mf hdst hcache_dst
  let m₁ : AnnealStepState :=
    { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_mf
        (translateTy dstDecl.ty body.layouts)]⟩ }
  have hcallee := annealEvalOperand_fnItemConst_ok body.localDecls body.layouts
    AnnealIntrinsic.writeBytes (encodeTyId { kind := pointeeKind, layoutIdx := 0 }) (m := m₁) rfl
  rw [EStateM.bind_eq_ok (annealPlaceHooks_frameIndex_eq hframes),
    EStateM.bind_eq_ok (annealPlaceHooks_getFrame_eq hframes), EStateM.bind_eq_ok hplace,
    EStateM.bind_eq_ok hcallee]
  unfold wbMiriBodyAction at hact
  cases hv₁ : annealEvalOperand body.localDecls body.layouts (.Copy ⟨ptrIdx, #[]⟩) none m₁ with
  | error e s₁ => rw [EStateM.bind_eq_error hv₁] at hact; cases hact
  | ok v₁ s₁ =>
    rw [EStateM.bind_eq_ok hv₁] at hact; rw [EStateM.bind_eq_ok hv₁]
    cases hv₂ : annealEvalOperand body.localDecls body.layouts (translateOperand valOp) none s₁ with
    | error e s₂ => rw [EStateM.bind_eq_error hv₂] at hact; cases hact
    | ok v₂ s₂ =>
      rw [EStateM.bind_eq_ok hv₂] at hact; rw [EStateM.bind_eq_ok hv₂]
      cases hv₃ : annealEvalOperand body.localDecls body.layouts
          (translateOperand countOp) none s₂ with
      | error e s₃ => rw [EStateM.bind_eq_error hv₃] at hact; cases hact
      | ok v₃ s₃ =>
        rw [EStateM.bind_eq_ok hv₃] at hact
        rw [EStateM.bind_eq_ok hv₃, intrinsics_eval_writeBytes]
        let tf₄ := { tf₃ with location := .mir ⟨targetBb, 0⟩ }
        have hret := annealReturnToBlock_some
          (m := { stack := ⟨#[tf₃]⟩, machine := mach' }) (tf := tf₃) rfl targetBb
        have hev : (do
            annealWriteBytesEval body.layouts v₁ v₂ v₃
            annealReturnToBlock (some targetBb)
            pure true) s₃ = .ok true { stack := ⟨#[tf₄]⟩, machine := mach' } := by
          rw [EStateM.bind_eq_ok hact, EStateM.bind_eq_ok hret]
          rfl
        rw [EStateM.bind_eq_ok hev]
        simp only [↓reduceIte, Option.isSome_some]
        rw [EStateM.bind_eq_ok (annealPlaceHooks_frameIndex_eq
          (m := { stack := ⟨#[tf₄]⟩, machine := mach' }) (tf := tf₄) rfl)]
        simp only [beq_self_eq_true, ↓reduceIte]
        rw [EStateM.bind_eq_ok (annealPlaceHooks_getFrame_eq
          (m := { stack := { frames := #[tf₄] }, machine := mach' }) (tf := tf₄) rfl)]
        have hloc₄ : tf₄.location = .mir ⟨targetBb, 0⟩ := rfl
        rw [hloc₄, hloc, frameLocation_beq_false hprog]
        simp only [Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure,
          stack_currentFrame?_singleton m.stack tf hframes, hframes,
          stack_currentFrame?_singleton (⟨#[tf₄]⟩ : Miri.Interpreter.Stack AnnealProv
            Miri.Interpreter.LocalLayout Unit) tf₄ rfl, Option.map_some, hloc₄, hloc,
          option_frameLocation_beq_false hprog, Bool.and_false, Except.map]
        rfl

private theorem wbEvalOperand_scalar_ub_or_ok
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {op : MirAst.Operand} {ty : Ty}
    (hop : WellTypedScalarOperand body tf op ty)
    (hprim : IsPrimScalarTy ty) :
    (∃ m' msg,
      annealEvalOperand body.localDecls body.layouts (translateOperand op) none m =
        .error (.undefinedBehavior msg) m') ∨
    (∃ v tf',
      annealEvalOperand body.localDecls body.layouts (translateOperand op) none m =
        .ok v { m with stack := ⟨#[tf']⟩ } ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf']⟩ } allocMap ∧
      (∀ k : Nat, (tf'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value)) := by
  rcases annealEvalOperand_scalar_lm3_1 hstate hframes hop hprim with
    ⟨m', msg, _, hm⟩ | ⟨tf', _, hm, hst, hv⟩ | ⟨_, _, tf', _, hm, hst, _, hv⟩
  · exact Or.inl ⟨m', msg, hm⟩
  · exact Or.inr ⟨_, tf', hm, hst, hv⟩
  · exact Or.inr ⟨_, tf', hm, hst, hv⟩

private theorem wbBle_eq_false_of_gt {a b : Nat} (h : ¬ a ≤ b) : Nat.ble a b = false := by
  cases hb : Nat.ble a b
  · rfl
  · exact absurd (Nat.ble_eq.mp hb) h

private theorem wbBeq_zero_eq_false_of_pos {n : Nat} (h : 0 < n) : Nat.beq n 0 = false := by
  cases hb : Nat.beq n 0
  · rfl
  · have heq := Nat.eq_of_beq_eq_true hb; omega

private theorem wbEvalWriteBytesCall_scalar_overflow_ub
    {s : MachineState} {dstOp : MirAst.Operand} {sc_p valSc countSc : MirAst.ScalarInt}
    {targetBb : BasicBlockIdx} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {elemBytes : Nat}
    (hsz8 : sc_p.sizeBytes = 8)
    (hop : operandPointeeBytes? localDecls layouts dstOp = some elemBytes)
    (hovf : ¬ countSc.bits * elemBytes ≤ isizeMaxBytes) :
    evalWriteBytesCall s dstOp (.scalar sc_p) valSc countSc s.frame.locals targetBb
        localDecls layouts =
      MirStepNode.fail .ub := by
  unfold evalWriteBytesCall
  dsimp only
  rw [hsz8, hop]; dsimp only
  rw [show Nat.mul countSc.bits elemBytes = countSc.bits * elemBytes from rfl,
    wbBle_eq_false_of_gt hovf]

private theorem wbEvalWriteBytesCall_scalar_zero_ok
    {s : MachineState} {dstOp : MirAst.Operand} {sc_p valSc countSc : MirAst.ScalarInt}
    {targetBb : BasicBlockIdx} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {elemBytes : Nat}
    (hsz8 : sc_p.sizeBytes = 8)
    (hop : operandPointeeBytes? localDecls layouts dstOp = some elemBytes)
    (hz : countSc.bits * elemBytes = 0) :
    evalWriteBytesCall s dstOp (.scalar sc_p) valSc countSc s.frame.locals targetBb
        localDecls layouts =
      intrinsicReturnTo s targetBb s.frame.locals s.memory := by
  have hle : Nat.ble (countSc.bits * elemBytes) isizeMaxBytes = true := by
    rw [hz]; rfl
  have hbeq : Nat.beq (countSc.bits * elemBytes) 0 = true := by
    rw [hz]; rfl
  unfold evalWriteBytesCall
  dsimp only
  rw [hsz8, hop]; dsimp only
  rw [show Nat.mul countSc.bits elemBytes = countSc.bits * elemBytes from rfl, hle, hbeq]

private theorem wbEvalWriteBytesCall_scalar_pos_ub
    {s : MachineState} {dstOp : MirAst.Operand} {sc_p valSc countSc : MirAst.ScalarInt}
    {targetBb : BasicBlockIdx} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {elemBytes : Nat}
    (hsz8 : sc_p.sizeBytes = 8)
    (hop : operandPointeeBytes? localDecls layouts dstOp = some elemBytes)
    (hpos : 0 < countSc.bits * elemBytes)
    (hle : countSc.bits * elemBytes ≤ isizeMaxBytes) :
    evalWriteBytesCall s dstOp (.scalar sc_p) valSc countSc s.frame.locals targetBb
        localDecls layouts =
      MirStepNode.fail .ub := by
  unfold evalWriteBytesCall
  dsimp only
  rw [hsz8, hop]; dsimp only
  rw [show Nat.mul countSc.bits elemBytes = countSc.bits * elemBytes from rfl,
    Nat.ble_eq.mpr hle, wbBeq_zero_eq_false_of_pos hpos]

private theorem wbEvalWriteBytesCall_overflow_ub
    {s : MachineState} {dstOp : MirAst.Operand} {dstPtr : ProvenancePtr}
    {valSc countSc : MirAst.ScalarInt} {targetBb : BasicBlockIdx}
    {localDecls : List LocalDecl} {layouts : LayoutTable} {elemBytes : Nat}
    (hop : operandPointeeBytes? localDecls layouts dstOp = some elemBytes)
    (hovf : ¬ countSc.bits * elemBytes ≤ isizeMaxBytes) :
    evalWriteBytesCall s dstOp (.ptr dstPtr 8) valSc countSc s.frame.locals targetBb
        localDecls layouts =
      MirStepNode.fail .ub := by
  unfold evalWriteBytesCall
  rw [hop]; dsimp only
  rw [show Nat.mul countSc.bits elemBytes = countSc.bits * elemBytes from rfl,
    wbBle_eq_false_of_gt hovf]

private theorem wbEvalWriteBytesCall_zero_ok
    {s : MachineState} {dstOp : MirAst.Operand} {dstPtr : ProvenancePtr}
    {valSc countSc : MirAst.ScalarInt} {targetBb : BasicBlockIdx}
    {localDecls : List LocalDecl} {layouts : LayoutTable} {elemBytes : Nat}
    (hop : operandPointeeBytes? localDecls layouts dstOp = some elemBytes)
    (hz : countSc.bits * elemBytes = 0) :
    evalWriteBytesCall s dstOp (.ptr dstPtr 8) valSc countSc s.frame.locals targetBb
        localDecls layouts =
      intrinsicReturnTo s targetBb s.frame.locals s.memory := by
  have hle : Nat.ble (countSc.bits * elemBytes) isizeMaxBytes = true := by
    rw [hz]; rfl
  have hbeq : Nat.beq (countSc.bits * elemBytes) 0 = true := by
    rw [hz]; rfl
  unfold evalWriteBytesCall
  rw [hop]; dsimp only
  rw [show Nat.mul countSc.bits elemBytes = countSc.bits * elemBytes from rfl, hle, hbeq]

private theorem wbEvalWriteBytesCall_perm_ub
    {s : MachineState} {dstOp : MirAst.Operand} {dstPtr : ProvenancePtr}
    {valSc countSc : MirAst.ScalarInt} {targetBb : BasicBlockIdx}
    {localDecls : List LocalDecl} {layouts : LayoutTable} {elemBytes : Nat}
    {e : AllocMapEntry}
    (hop : operandPointeeBytes? localDecls layouts dstOp = some elemBytes)
    (hpos : 0 < countSc.bits * elemBytes)
    (hle : countSc.bits * elemBytes ≤ isizeMaxBytes)
    (hbor : lookupBorrow s.memory.borrows dstPtr.tag =
      some { tag := e.tag, targetLocal := e.localIdx, targetProjection := [], perm := e.perm })
    (hperm : e.perm = .frozen ∨ e.perm = .disabled) :
    evalWriteBytesCall s dstOp (.ptr dstPtr 8) valSc countSc s.frame.locals targetBb
        localDecls layouts =
      MirStepNode.fail .ub := by
  unfold evalWriteBytesCall
  rw [hop]; dsimp only
  rw [show Nat.mul countSc.bits elemBytes = countSc.bits * elemBytes from rfl,
    Nat.ble_eq.mpr hle, wbBeq_zero_eq_false_of_pos hpos, hbor]
  rcases hperm with hp | hp <;> simp [hp]

private theorem wbEvalWriteBytesCall_dead_ub
    {s : MachineState} {dstOp : MirAst.Operand} {dstPtr : ProvenancePtr}
    {valSc countSc : MirAst.ScalarInt} {targetBb : BasicBlockIdx}
    {localDecls : List LocalDecl} {layouts : LayoutTable} {elemBytes : Nat}
    {e : AllocMapEntry} {tgtDecl : LocalDecl} {tgtKind : Miri.MIR.IntegerKind}
    (hop : operandPointeeBytes? localDecls layouts dstOp = some elemBytes)
    (hpos : 0 < countSc.bits * elemBytes)
    (hle : countSc.bits * elemBytes ≤ isizeMaxBytes)
    (hbor : lookupBorrow s.memory.borrows dstPtr.tag =
      some { tag := e.tag, targetLocal := e.localIdx, targetProjection := [], perm := e.perm })
    (hdecl : get? localDecls e.localIdx = some tgtDecl)
    (_htgt : IsIntegralTy tgtDecl.ty tgtKind)
    (hdead : get? s.frame.locals e.localIdx = some .dead) :
    evalWriteBytesCall s dstOp (.ptr dstPtr 8) valSc countSc s.frame.locals targetBb
        localDecls layouts =
      MirStepNode.fail .ub := by
  unfold evalWriteBytesCall
  rw [hop]; dsimp only
  rw [show Nat.mul countSc.bits elemBytes = countSc.bits * elemBytes from rfl,
    Nat.ble_eq.mpr hle, wbBeq_zero_eq_false_of_pos hpos, hbor]
  dsimp only
  cases e.perm with
  | frozen => rfl
  | disabled => rfl
  | reservedFrz _ | reservedIM | unique | cell =>
    dsimp only
    rw [hdead, hdecl]

private theorem wbEvalWriteBytesCall_oob_ub
    {s : MachineState} {dstOp : MirAst.Operand} {dstPtr : ProvenancePtr}
    {valSc countSc : MirAst.ScalarInt} {targetBb : BasicBlockIdx}
    {localDecls : List LocalDecl} {layouts : LayoutTable} {elemBytes : Nat}
    {e : AllocMapEntry} {tgtDecl : LocalDecl} {tgtKind : Miri.MIR.IntegerKind}
    (hop : operandPointeeBytes? localDecls layouts dstOp = some elemBytes)
    (hpos : 0 < countSc.bits * elemBytes)
    (hle : countSc.bits * elemBytes ≤ isizeMaxBytes)
    (hbor : lookupBorrow s.memory.borrows dstPtr.tag =
      some { tag := e.tag, targetLocal := e.localIdx, targetProjection := [], perm := e.perm })
    (hdecl : get? localDecls e.localIdx = some tgtDecl)
    (htgt : IsIntegralTy tgtDecl.ty tgtKind)
    (hoob : ¬ dstPtr.offsetBytes + countSc.bits * elemBytes ≤ integerKindByteWidth tgtKind) :
    evalWriteBytesCall s dstOp (.ptr dstPtr 8) valSc countSc s.frame.locals targetBb
        localDecls layouts =
      MirStepNode.fail .ub := by
  unfold evalWriteBytesCall
  rw [hop]; dsimp only
  rw [show Nat.mul countSc.bits elemBytes = countSc.bits * elemBytes from rfl,
    Nat.ble_eq.mpr hle, wbBeq_zero_eq_false_of_pos hpos, hbor]
  dsimp only
  cases e.perm with
  | frozen => rfl
  | disabled => rfl
  | reservedFrz _ | reservedIM | unique | cell =>
    dsimp only
    rw [hdecl]
    cases get? s.frame.locals e.localIdx with
    | none => rfl
    | some slot =>
      cases slot with
      | dead => rfl
      | uninit | init _ =>
        dsimp only
        rw [htgt.intCastTargetBytes_eq]; dsimp only
        rw [show Nat.add dstPtr.offsetBytes (countSc.bits * elemBytes) =
            dstPtr.offsetBytes + countSc.bits * elemBytes from rfl,
          wbBle_eq_false_of_gt hoob]

private theorem wbEvalWriteBytesCall_full_ok
    {s : MachineState} {dstOp : MirAst.Operand} {dstPtr : ProvenancePtr}
    {valSc countSc : MirAst.ScalarInt} {targetBb : BasicBlockIdx}
    {localDecls : List LocalDecl} {layouts : LayoutTable} {elemBytes : Nat}
    {e : AllocMapEntry} {tgtDecl : LocalDecl} {tgtKind : Miri.MIR.IntegerKind}
    {slot_t : LocalSlot}
    (hop : operandPointeeBytes? localDecls layouts dstOp = some elemBytes)
    (hpos : 0 < countSc.bits * elemBytes)
    (hle : countSc.bits * elemBytes ≤ isizeMaxBytes)
    (hbor : lookupBorrow s.memory.borrows dstPtr.tag =
      some { tag := e.tag, targetLocal := e.localIdx, targetProjection := [], perm := e.perm })
    (hperm : e.perm = .active ∨ e.perm = .reserved)
    (hdecl : get? localDecls e.localIdx = some tgtDecl)
    (htgt : IsIntegralTy tgtDecl.ty tgtKind)
    (hslot : get? s.frame.locals e.localIdx = some slot_t)
    (hlt_af : e.localIdx < length s.frame.locals)
    (hne_dead : slot_t ≠ .dead)
    (hscalar : ∀ v, slot_t = .init v → ∃ sc, v = .scalar sc)
    (hoff0 : dstPtr.offsetBytes = 0)
    (hfull : countSc.bits * elemBytes = integerKindByteWidth tgtKind) :
    evalWriteBytesCall s dstOp (.ptr dstPtr 8) valSc countSc s.frame.locals targetBb
        localDecls layouts =
      intrinsicReturnTo s targetBb
        (s.frame.locals.set e.localIdx
          (.init (.scalar ⟨repeatByteBits (valSc.bits % 256) (integerKindByteWidth tgtKind),
            integerKindByteWidth tgtKind⟩)))
        { s.memory with
          borrows := invalidateConflictingBorrows s.memory.borrows e.localIdx (some dstPtr.tag) } := by
  let targetBytes := integerKindByteWidth tgtKind
  have hble_in : Nat.ble (Nat.add dstPtr.offsetBytes (countSc.bits * elemBytes)) targetBytes = true := by
    rw [show Nat.add dstPtr.offsetBytes (countSc.bits * elemBytes) =
        dstPtr.offsetBytes + countSc.bits * elemBytes from rfl, hoff0, Nat.zero_add, hfull]
    exact Nat.ble_eq.mpr (Nat.le_refl _)
  have hset := set?_eq_some_set hlt_af
    (.init (.scalar ⟨repeatByteBits (valSc.bits % 256) targetBytes, targetBytes⟩))
  unfold evalWriteBytesCall
  rw [hop]; dsimp only
  rw [show Nat.mul countSc.bits elemBytes = countSc.bits * elemBytes from rfl,
    Nat.ble_eq.mpr hle, wbBeq_zero_eq_false_of_pos hpos, hbor]
  dsimp only
  rcases hperm with hp | hp <;> rw [hp] <;>
  · dsimp only
    rw [hslot, hdecl]
    cases slot_t with
    | dead => exact absurd rfl hne_dead
    | uninit =>
      dsimp only
      rw [htgt.intCastTargetBytes_eq]; dsimp only
      rw [hble_in]; dsimp only
      rw [hoff0, hfull]
      simp only [Nat.beq_refl, Bool.and_self]
      rw [show Nat.mod valSc.bits 256 = valSc.bits % 256 from rfl, hset]
    | init v =>
      obtain ⟨oldSc, rfl⟩ := hscalar v rfl
      dsimp only
      rw [htgt.intCastTargetBytes_eq]; dsimp only
      rw [hble_in]; dsimp only
      rw [hoff0, hfull, show Nat.mod valSc.bits 256 = valSc.bits % 256 from rfl,
        evalWriteBytesCall_full_merge oldSc.bits
          (repeatByteBits (valSc.bits % 256) targetBytes) targetBytes,
        hset]

private theorem wbEvalWriteBytesCall_partial_ok
    {s : MachineState} {dstOp : MirAst.Operand} {dstPtr : ProvenancePtr}
    {valSc countSc oldSc : MirAst.ScalarInt} {targetBb : BasicBlockIdx}
    {localDecls : List LocalDecl} {layouts : LayoutTable} {elemBytes : Nat}
    {e : AllocMapEntry} {tgtDecl : LocalDecl} {tgtKind : Miri.MIR.IntegerKind}
    (hop : operandPointeeBytes? localDecls layouts dstOp = some elemBytes)
    (hpos : 0 < countSc.bits * elemBytes)
    (hle : countSc.bits * elemBytes ≤ isizeMaxBytes)
    (hbor : lookupBorrow s.memory.borrows dstPtr.tag =
      some { tag := e.tag, targetLocal := e.localIdx, targetProjection := [], perm := e.perm })
    (hperm : e.perm = .active ∨ e.perm = .reserved)
    (hdecl : get? localDecls e.localIdx = some tgtDecl)
    (htgt : IsIntegralTy tgtDecl.ty tgtKind)
    (hslot : get? s.frame.locals e.localIdx = some (.init (.scalar oldSc)))
    (hlt_af : e.localIdx < length s.frame.locals)
    (hinb : dstPtr.offsetBytes + countSc.bits * elemBytes ≤ integerKindByteWidth tgtKind) :
    evalWriteBytesCall s dstOp (.ptr dstPtr 8) valSc countSc s.frame.locals targetBb
        localDecls layouts =
      intrinsicReturnTo s targetBb
        (s.frame.locals.set e.localIdx
          (.init (.scalar ⟨spliceRepeatedBytes oldSc.bits (valSc.bits % 256)
            dstPtr.offsetBytes (countSc.bits * elemBytes) (integerKindByteWidth tgtKind),
            integerKindByteWidth tgtKind⟩)))
        { s.memory with
          borrows := invalidateConflictingBorrows s.memory.borrows e.localIdx (some dstPtr.tag) } := by
  let targetBytes := integerKindByteWidth tgtKind
  have hble_max : Nat.ble (countSc.bits * elemBytes) isizeMaxBytes = true :=
    Nat.ble_eq.mpr hle
  have hble_in : Nat.ble (Nat.add dstPtr.offsetBytes (countSc.bits * elemBytes)) targetBytes = true := by
    rw [show Nat.add dstPtr.offsetBytes (countSc.bits * elemBytes) =
        dstPtr.offsetBytes + countSc.bits * elemBytes from rfl]
    exact Nat.ble_eq.mpr hinb
  have hset := set?_eq_some_set hlt_af
    (.init (.scalar ⟨spliceRepeatedBytes oldSc.bits (valSc.bits % 256)
      dstPtr.offsetBytes (countSc.bits * elemBytes) targetBytes, targetBytes⟩))
  unfold evalWriteBytesCall
  unfold spliceRepeatedBytes at hset ⊢
  dsimp only at hset ⊢
  rw [hop]; dsimp only
  rw [show Nat.mul countSc.bits elemBytes = countSc.bits * elemBytes from rfl,
    hble_max, wbBeq_zero_eq_false_of_pos hpos, hbor]
  dsimp only
  rcases hperm with hp | hp <;> rw [hp] <;>
  · dsimp only
    rw [hslot, hdecl]; dsimp only
    rw [htgt.intCastTargetBytes_eq]; dsimp only
    rw [hble_in]; dsimp only
    rw [show Nat.mod valSc.bits 256 = valSc.bits % 256 from rfl, hset]

private theorem WriteBytesScalarPreVal.evalOperand_ok
    {locals : List LocalSlot} {op : MirAst.Operand} {sc : MirAst.ScalarInt}
    (h : WriteBytesScalarPreVal locals op sc)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (ly : LayoutTable) (callerLocals : List LocalSlot) :
    evalOperand locals op borrows globals ly callerLocals = .ok (.scalar sc) locals := by
  rcases h with ⟨cc, rfl, hval⟩ | ⟨idx, rfl, hslot⟩
  · unfold evalOperand; dsimp only; rw [hval]; rfl
  · rw [wbEvalOperand_copy_local_eq, hslot]

private theorem wbLookupAllocMapByTag_of_mem_nodup
    {allocMap : List AllocMapEntry} (hnodup : (allocMap.map AllocMapEntry.tag).Nodup)
    {e : AllocMapEntry} (he : e ∈ allocMap) {t : Nat} (htag : e.tag = t) :
    lookupAllocMapByTag allocMap t = some e := by
  induction allocMap with
  | nil => cases he
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    simp only [lookupAllocMapByTag]
    rcases List.mem_cons.mp he with rfl | hmem
    · subst htag; simp [Nat.beq_refl]
    · have hne : Nat.beq hd.tag t = false := by
        cases hb : Nat.beq hd.tag t
        · rfl
        · have heq := Nat.eq_of_beq_eq_true hb
          exact absurd (heq.trans htag.symm ▸ List.mem_map_of_mem hmem) hnodup.1
      rw [hne]
      exact ih hnodup.2 hmem

private theorem wbMiriBodyAction_eval_eq {body : CapturedMir} {ptrIdx : Local}
    {valOp countOp : MirAst.Operand} {m : AnnealStepState}
    {s₁ s₂ s₃ s₄ : Miri.Interpreter.Stack AnnealProv Miri.Interpreter.LocalLayout Unit}
    {v₁ v₂ v₃ : Miri.Interpreter.OpTy AnnealProv}
    (hm₁ : annealEvalOperand body.localDecls body.layouts (.Copy ⟨ptrIdx, #[]⟩) none
      { m with stack := s₁ } = .ok v₁ { ({ m with stack := s₁ } : AnnealStepState) with stack := s₂ })
    (hm₂ : annealEvalOperand body.localDecls body.layouts (translateOperand valOp) none
      { ({ m with stack := s₁ } : AnnealStepState) with stack := s₂ } =
      .ok v₂ { ({ ({ m with stack := s₁ } : AnnealStepState) with stack := s₂ } :
        AnnealStepState) with stack := s₃ })
    (hm₃ : annealEvalOperand body.localDecls body.layouts (translateOperand countOp) none
      { ({ ({ m with stack := s₁ } : AnnealStepState) with stack := s₂ } :
        AnnealStepState) with stack := s₃ } =
      .ok v₃ { ({ ({ ({ m with stack := s₁ } : AnnealStepState) with stack := s₂ } :
        AnnealStepState) with stack := s₃ } : AnnealStepState) with stack := s₄ }) :
    wbMiriBodyAction body ptrIdx valOp countOp { m with stack := s₁ } =
      annealWriteBytesEval body.layouts v₁ v₂ v₃ { m with stack := s₄ } := by
  unfold wbMiriBodyAction
  rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]

private theorem wbCall_writeBytes_core
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {c : ConstOperand} {ptrIdx dstIdx : Local} {valOp countOp : MirAst.Operand}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {pointeeTy : Ty}
    (hterm : bb.terminator.kind =
      .call (.constant c) [.copy ⟨ptrIdx, []⟩, valOp, countOp] ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef AnnealIntrinsic.writeBytes.defPath [pointeeTy.kind])
    (hcallee : findCallee? s.memory.callees AnnealIntrinsic.writeBytes.defPath = none)
    (hprog : targetBb ≠ s.frame.blockIdx ∨ s.frame.stmtIdx ≠ 0)
    {ptrDecl : LocalDecl} {ptrMut : Mutability}
    (hptrDecl : get? body.localDecls ptrIdx = some ptrDecl)
    (hptrTy : ptrDecl.ty.kind = .rawPtr ptrMut pointeeTy.kind)
    (hptrImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf ptrIdx)
    {valTy countTy : Ty}
    (hvalInt : IsIntegralTy valTy .u8)
    (hvalOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf valOp valTy)
    (hcountInt : IsIntegralTy countTy .usize)
    (hcountOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf countOp countTy)
    {dstDecl : LocalDecl} (hdst : get? body.localDecls dstIdx = some dstDecl)
    {ptId : Miri.MIR.TyId} {elemBytes : Nat}
    (hpt : WriteBytesPointee body.layouts pointeeTy.kind ptId elemBytes)
    (htgt_int : ∀ ptrVal e tgtDecl,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      ∃ tgtKind, IsIntegralTy tgtDecl.ty tgtKind)
    (hlive_inbounds : ∀ ptrVal countSc e tgtDecl tgtKind,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      0 < countSc.bits * elemBytes →
      countSc.bits * elemBytes ≤ isizeMaxBytes →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      IsIntegralTy tgtDecl.ty tgtKind →
      get? s.frame.locals e.localIdx ≠ some .dead →
      ptrVal.offsetBytes + countSc.bits * elemBytes ≤ integerKindByteWidth tgtKind →
      (e.perm = .active ∨ e.perm = .reserved) ∧
        ((ptrVal.offsetBytes = 0 ∧ countSc.bits * elemBytes = integerKindByteWidth tgtKind) ∨
          ∃ oldSc, get? s.frame.locals e.localIdx = some (.init (.scalar oldSc)))) :
    (stepMirFn body s = MirStepNode.fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg))) ∨
    (∃ s' m',
      stepMirFn body s = MirStepNode.step s' ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      writeBytesNextAllocMap s.frame.locals allocMap ptrIdx countOp elemBytes = allocMap ∧
      StateRelLM3_1 body s' m' allocMap) ∨
    (∃ s' m' ptrVal countSc e tgtDecl tgtKind,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) ∧
      WriteBytesScalarPreVal s.frame.locals countOp countSc ∧
      0 < countSc.bits * elemBytes ∧
      countSc.bits * elemBytes ≤ isizeMaxBytes ∧
      e ∈ allocMap ∧ e.tag = ptrVal.tag ∧
      get? body.localDecls e.localIdx = some tgtDecl ∧
      IsIntegralTy tgtDecl.ty tgtKind ∧
      get? s.frame.locals e.localIdx ≠ some .dead ∧
      ptrVal.offsetBytes + countSc.bits * elemBytes ≤ integerKindByteWidth tgtKind ∧
      stepMirFn body s = MirStepNode.step s' ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      writeBytesNextAllocMap s.frame.locals allocMap ptrIdx countOp elemBytes =
        updateAllocMapOnWrite allocMap e.localIdx (some ptrVal.tag) ∧
      StateRelLM3_1 body s' m' (updateAllocMapOnWrite allocMap e.localIdx (some ptrVal.tag))) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, hbor, halloc, _⟩ := id hstate
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
  have hanneal_step : stepMirFn body s = evalTerminator s bb.terminator (some body) := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  have hanneal_term :=
    evalTerminator_inline_intrinsic_call (s := s) (body := body) hterm hc hcallee (by nofun)
  obtain ⟨_, _, _, hlt_mf, _, _, hdmls_eq, hdloc⟩ := hfr.lookup_local hdst
  have hcache_dst : ∀ l, (tf.locals[dstIdx]'hlt_mf).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    intro l hl; rw [hdmls_eq] at hl; exact hdloc.cachedLayout_eq l hl
  let tf₁ := cacheFrameLocalLayout tf dstIdx hlt_mf (translateTy dstDecl.ty body.layouts)
  have hstate₁ : StateRelLM3_1 body s { m with stack := ⟨#[tf₁]⟩ } allocMap :=
    hstate.cache_layout hframes hdst hlt_mf
  have himm₁ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₁ j :=
    fun j hj => hj.cache_layout hlt_mf _
  have hval_nm := (hvalOp tf hframes).translate_ne_move
  have hcount_nm := (hcountOp tf hframes).translate_ne_move
  have hpt_m : ∀ st, annealPointeeTypeOf (translateTy ptrDecl.ty body.layouts).ty st = .ok ptId st :=
    annealPointeeTypeOf_rawPtr hptrTy hpt.encoded_eq
  have hop_pt := operandPointeeBytes?_copy_rawPtr (layouts := body.layouts) hptrDecl hptrTy hpt.anneal_size
  have mk_ub : ∀ {m' msg},
      stepMirFn body s = MirStepNode.fail .ub →
      wbMiriBodyAction body ptrIdx valOp countOp { m with stack := ⟨#[tf₁]⟩ } =
        .error (.undefinedBehavior msg) m' →
      stepMirFn body s = MirStepNode.fail .ub ∧
        ∃ m' msg, Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .error (.undefinedBehavior msg)) :=
    fun ha hact_m => ⟨ha, _, _, wbMiri_step_writeBytes_ub hframes hfr.body_eq hfr.location_eq hbb
      hstmt_none hterm hc hdst hlt_mf hcache_dst hval_nm hcount_nm hact_m⟩
  have mk_op_ub : ∀ {m' msg},
      evalOperands s.frame.locals [.copy ⟨ptrIdx, []⟩, valOp, countOp]
        s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals = .ub →
      wbMiriBodyAction body ptrIdx valOp countOp { m with stack := ⟨#[tf₁]⟩ } =
        .error (.undefinedBehavior msg) m' →
      stepMirFn body s = MirStepNode.fail .ub ∧
        ∃ m' msg, Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .error (.undefinedBehavior msg)) := by
    intro m' msg hev_a hact_m
    refine mk_ub ?_ hact_m
    rw [hanneal_step, hanneal_term, hev_a]
  rcases wbEvalOperand_rawPtr_lm3_1 hstate₁ rfl hptrDecl hptrTy (himm₁ ptrIdx (hptrImm tf hframes)) with
    ⟨hptr_dead, m₂, msg, hm₁⟩ |
    ⟨tf₂, hptr_un, hm₁, hstate₂, hvals₂⟩ |
    ⟨sc_p, msc_p, tf₂, hptr_sc, hsz8_p, hrel_p, hm₁, hstate₂, hvals₂⟩ |
    ⟨ptrVal, mptr, tf₂, hptr_ok, hptrRel, hm₁, hstate₂, hvals₂⟩
  · -- Branch 1: `ptrIdx` is `.dead` -> UB in both.
    have ha₁ : evalOperand s.frame.locals (.copy ⟨ptrIdx, []⟩) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals = .ub := by
      rw [wbEvalOperand_copy_local_eq, hptr_dead]
    left
    exact mk_op_ub (by simp only [evalOperands, ha₁])
      (by unfold wbMiriBodyAction; rw [EStateM.bind_eq_error hm₁])
  · -- Branch 2: `ptrIdx` is `.uninit` -> UB in both.
    have ha₁ : evalOperand s.frame.locals (.copy ⟨ptrIdx, []⟩) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals = .ub := by
      rw [wbEvalOperand_copy_local_eq, hptr_un]
    have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
      fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂ (himm₁ j hj)
    rcases wbEvalOperand_scalar_ub_or_ok hstate₂ rfl ((hvalOp tf hframes).mono_immediate himm₂)
        hvalInt.prim with
      ⟨m₃, msg, hm₂⟩ | ⟨v₂, tf₃, hm₂, hstate₃, hvals₃⟩
    · left
      exact mk_op_ub (by simp only [evalOperands, ha₁])
        (by unfold wbMiriBodyAction; rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_error hm₂])
    · have himm₃ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₃ j :=
        fun j hj => IsImmediateFrameLocal.of_values_eq hvals₃ (himm₂ j hj)
      rcases wbEvalOperand_scalar_ub_or_ok hstate₃ rfl ((hcountOp tf hframes).mono_immediate himm₃)
          hcountInt.prim with
        ⟨m₄, msg, hm₃⟩ | ⟨v₃, tf₄, hm₃, _, _⟩
      · left
        exact mk_op_ub (by simp only [evalOperands, ha₁])
          (by unfold wbMiriBodyAction
              rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_error hm₃])
      · left
        exact mk_op_ub (by simp only [evalOperands, ha₁])
          (by unfold wbMiriBodyAction
              rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
              exact wbAnnealWriteBytesEval_uninit_dst v₂ v₃ { m with stack := ⟨#[tf₄]⟩ } (hpt_m _))
  · -- Branch 3: `ptrIdx` holds provenance-free `.scalar sc_p`.
    have ha₁ : evalOperand s.frame.locals (.copy ⟨ptrIdx, []⟩) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals = .ok (.scalar sc_p) s.frame.locals := by
      rw [wbEvalOperand_copy_local_eq, hptr_sc]
    have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
      fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂ (himm₁ j hj)
    rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl ((hvalOp tf hframes).mono_immediate himm₂)
        hvalInt.prim with
      ⟨m₃, msg, ha₂, hm₂⟩ | ⟨tf₃, ha₂, hm₂, hstate₃, hvals₃⟩ |
      ⟨valSc, mval, tf₃, ha₂, hm₂, hstate₃, hrelI_val, hvals₃⟩
    · left
      exact mk_op_ub (by simp only [evalOperands, ha₁, ha₂])
        (by unfold wbMiriBodyAction; rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_error hm₂])
    · have himm₃ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₃ j :=
        fun j hj => IsImmediateFrameLocal.of_values_eq hvals₃ (himm₂ j hj)
      rcases wbEvalOperand_scalar_ub_or_ok hstate₃ rfl ((hcountOp tf hframes).mono_immediate himm₃)
          hcountInt.prim with
        ⟨m₄, msg, hm₃⟩ | ⟨v₃, tf₄, hm₃, _, _⟩
      · left
        exact mk_op_ub (by simp only [evalOperands, ha₁, ha₂])
          (by unfold wbMiriBodyAction
              rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_error hm₃])
      · left
        exact mk_op_ub (by simp only [evalOperands, ha₁, ha₂])
          (by unfold wbMiriBodyAction
              rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
              exact wbAnnealWriteBytesEval_uninit_val { m with stack := ⟨#[tf₄]⟩ } (hpt_m _)
                (wbIntrinsicPointer_fromScalarInt hrel_p hsz8_p _ _))
    · obtain ⟨hrelV, hszV⟩ := wbImmediateRel_of_integral hvalInt hrelI_val
      have himm₃ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₃ j :=
        fun j hj => IsImmediateFrameLocal.of_values_eq hvals₃ (himm₂ j hj)
      rcases annealEvalOperand_scalar_lm3_1 hstate₃ rfl ((hcountOp tf hframes).mono_immediate himm₃)
          hcountInt.prim with
        ⟨m₄, msg, ha₃, hm₃⟩ | ⟨tf₄, ha₃, hm₃, _, _⟩ |
        ⟨countSc, mcount, tf₄, ha₃, hm₃, hstate₄, hrelI_cnt, _⟩
      · left
        exact mk_op_ub (by simp only [evalOperands, ha₁, ha₂, ha₃])
          (by unfold wbMiriBodyAction
              rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_error hm₃])
      · left
        exact mk_op_ub (by simp only [evalOperands, ha₁, ha₂, ha₃])
          (by unfold wbMiriBodyAction
              rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
              exact wbAnnealWriteBytesEval_uninit_count { m with stack := ⟨#[tf₄]⟩ } (hpt_m _)
                (wbIntrinsicPointer_fromScalarInt hrel_p hsz8_p _ _) hrelV hszV)
      · obtain ⟨hrelC, hszC⟩ := wbImmediateRel_of_integral hcountInt hrelI_cnt
        obtain ⟨hcount_opt, _⟩ := writeBytesScalarVal?_of_evalOperand_ok (hcountOp tf hframes) ha₃
        have hevals : evalOperands s.frame.locals [.copy ⟨ptrIdx, []⟩, valOp, countOp]
            s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals =
            .ok [.scalar sc_p, .scalar valSc, .scalar countSc] s.frame.locals := by
          simp only [evalOperands, ha₁, ha₂, ha₃]
        have hm_init := wbAnnealWriteBytesEval_init { m with stack := ⟨#[tf₄]⟩ } (hpt_m _)
          hpt.miri_size hpt.lt_u64
          (wbIntrinsicPointer_fromScalarInt hrel_p hsz8_p (translateTy ptrDecl.ty body.layouts) _)
          (valLay := translateTy valTy body.layouts) (countLay := translateTy countTy body.layouts)
          hrelV hszV hrelC hszC
        by_cases hle : countSc.bits * elemBytes ≤ isizeMaxBytes
        · by_cases hz : countSc.bits * elemBytes = 0
          · -- `total = 0` on `.scalar` pointer -> no-op step in both!
            right; left
            refine ⟨_, _, ?_, ?_, ?_, hstate₄.relocate rfl targetBb 0⟩
            · rw [hanneal_step, hanneal_term, hevals]; dsimp only
              rw [evalInlineIntrinsicCall?_writeBytes]
              dsimp only
              exact wbEvalWriteBytesCall_scalar_zero_ok hsz8_p hop_pt hz
            · apply wbMiri_step_writeBytes_ok (tf₃ := tf₄) hframes hfr.body_eq hfr.location_eq hbb
                hstmt_none hterm hc hprog hdst hlt_mf hcache_dst hval_nm hcount_nm
              rw [wbMiriBodyAction_eval_eq hm₁ hm₂ hm₃, hm_init, wbIte_pos hle, hz]
              exact annealWriteRepeatedBytes_zero _ _ _
            · simp [writeBytesNextAllocMap, hcount_opt, hz]
          · -- `0 < total ≤ isizeMaxBytes` on `.scalar` pointer -> UB in both!
            have hpos : 0 < countSc.bits * elemBytes := Nat.pos_of_ne_zero hz
            left
            refine mk_ub (m' := { m with stack := ⟨#[tf₄]⟩ })
              (msg := "write_bytes pointer check failed") ?_ ?_
            · rw [hanneal_step, hanneal_term, hevals]; dsimp only
              rw [evalInlineIntrinsicCall?_writeBytes]
              dsimp only
              exact wbEvalWriteBytesCall_scalar_pos_ub hsz8_p hop_pt hpos hle
            · rw [wbMiriBodyAction_eval_eq hm₁ hm₂ hm₃, hm_init, wbIte_pos hle]
              exact annealWriteRepeatedBytes_withoutProvenance_err (UInt64.ofNat sc_p.bits)
                (UInt8.ofNat valSc.bits) hpos hle { m with stack := ⟨#[tf₄]⟩ }
        · -- `total > isizeMaxBytes` on `.scalar` pointer -> UB in both!
          left
          refine mk_ub (m' := { m with stack := ⟨#[tf₄]⟩ })
            (msg := "overflow computing total size of write_bytes") ?_ ?_
          · rw [hanneal_step, hanneal_term, hevals]; dsimp only
            rw [evalInlineIntrinsicCall?_writeBytes]
            dsimp only
            exact wbEvalWriteBytesCall_scalar_overflow_ub hsz8_p hop_pt hle
          · rw [wbMiriBodyAction_eval_eq hm₁ hm₂ hm₃, hm_init, wbIte_neg hle]
  · -- Branch 4: `ptrIdx` holds tracked `.ptr ptrVal 8` with `PtrRel`.
    have ha₁ : evalOperand s.frame.locals (.copy ⟨ptrIdx, []⟩) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals = .ok (.ptr ptrVal 8) s.frame.locals := by
      rw [wbEvalOperand_copy_local_eq, hptr_ok]
    have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
      fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂ (himm₁ j hj)
    rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl ((hvalOp tf hframes).mono_immediate himm₂)
        hvalInt.prim with
      ⟨m₃, msg, ha₂, hm₂⟩ | ⟨tf₃, ha₂, hm₂, hstate₃, hvals₃⟩ |
      ⟨valSc, mval, tf₃, ha₂, hm₂, hstate₃, hrelI_val, hvals₃⟩
    · left
      exact mk_op_ub (by simp only [evalOperands, ha₁, ha₂])
        (by unfold wbMiriBodyAction; rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_error hm₂])
    · have himm₃ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₃ j :=
        fun j hj => IsImmediateFrameLocal.of_values_eq hvals₃ (himm₂ j hj)
      rcases wbEvalOperand_scalar_ub_or_ok hstate₃ rfl ((hcountOp tf hframes).mono_immediate himm₃)
          hcountInt.prim with
        ⟨m₄, msg, hm₃⟩ | ⟨v₃, tf₄, hm₃, _, _⟩
      · left
        exact mk_op_ub (by simp only [evalOperands, ha₁, ha₂])
          (by unfold wbMiriBodyAction
              rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_error hm₃])
      · left
        exact mk_op_ub (by simp only [evalOperands, ha₁, ha₂])
          (by unfold wbMiriBodyAction
              rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
              exact wbAnnealWriteBytesEval_uninit_val { m with stack := ⟨#[tf₄]⟩ } (hpt_m _)
                (wbIntrinsicPointer_fromPointer mptr _ _))
    · obtain ⟨hrelV, hszV⟩ := wbImmediateRel_of_integral hvalInt hrelI_val
      have himm₃ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₃ j :=
        fun j hj => IsImmediateFrameLocal.of_values_eq hvals₃ (himm₂ j hj)
      rcases annealEvalOperand_scalar_lm3_1 hstate₃ rfl ((hcountOp tf hframes).mono_immediate himm₃)
          hcountInt.prim with
        ⟨m₄, msg, ha₃, hm₃⟩ | ⟨tf₄, ha₃, hm₃, _, _⟩ |
        ⟨countSc, mcount, tf₄, ha₃, hm₃, hstate₄, hrelI_cnt, _⟩
      · left
        exact mk_op_ub (by simp only [evalOperands, ha₁, ha₂, ha₃])
          (by unfold wbMiriBodyAction
              rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_error hm₃])
      · left
        exact mk_op_ub (by simp only [evalOperands, ha₁, ha₂, ha₃])
          (by unfold wbMiriBodyAction
              rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
              exact wbAnnealWriteBytesEval_uninit_count { m with stack := ⟨#[tf₄]⟩ } (hpt_m _)
                (wbIntrinsicPointer_fromPointer mptr _ _) hrelV hszV)
      · obtain ⟨hrelC, hszC⟩ := wbImmediateRel_of_integral hcountInt hrelI_cnt
        obtain ⟨hcount_opt, hcount_pre⟩ :=
          writeBytesScalarVal?_of_evalOperand_ok (hcountOp tf hframes) ha₃
        have hevals : evalOperands s.frame.locals [.copy ⟨ptrIdx, []⟩, valOp, countOp]
            s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals =
            .ok [.ptr ptrVal 8, .scalar valSc, .scalar countSc] s.frame.locals := by
          simp only [evalOperands, ha₁, ha₂, ha₃]
        have hm_init := wbAnnealWriteBytesEval_init { m with stack := ⟨#[tf₄]⟩ } (hpt_m _)
          hpt.miri_size hpt.lt_u64
          (wbIntrinsicPointer_fromPointer mptr (translateTy ptrDecl.ty body.layouts) _)
          (valLay := translateTy valTy body.layouts) (countLay := translateTy countTy body.layouts)
          hrelV hszV hrelC hszC
        by_cases hle : countSc.bits * elemBytes ≤ isizeMaxBytes
        · by_cases hz : countSc.bits * elemBytes = 0
          · -- Subcase 4a: `total = 0` on `.ptr` -> no-op step in both!
            right; left
            refine ⟨_, _, ?_, ?_, ?_, hstate₄.relocate rfl targetBb 0⟩
            · rw [hanneal_step, hanneal_term, hevals]; dsimp only
              rw [evalInlineIntrinsicCall?_writeBytes]
              dsimp only
              rw [wbEvalWriteBytesCall_zero_ok hop_pt hz]
              rfl
            · apply wbMiri_step_writeBytes_ok (tf₃ := tf₄) hframes hfr.body_eq hfr.location_eq hbb
                hstmt_none hterm hc hprog hdst hlt_mf hcache_dst hval_nm hcount_nm
              rw [wbMiriBodyAction_eval_eq hm₁ hm₂ hm₃, hm_init, wbIte_pos hle, hz]
              exact annealWriteRepeatedBytes_zero _ _ _
            · simp [writeBytesNextAllocMap, hcount_opt, hz]
          · -- Subcase 4b: `0 < total ≤ isizeMaxBytes` on `.ptr ptrVal 8`.
            have hpos : 0 < countSc.bits * elemBytes := Nat.pos_of_ne_zero hz
            rcases hptrRel with ⟨_, borTag, hprov_eq, hid_lt, hoff_lt, hmptr_off, ⟨e, he, htag, rfl⟩⟩
            obtain ⟨tgtDecl, hdecl_tgt, _⟩ := halloc.target_decl e he
            obtain ⟨tgtKind, htgtInt⟩ := htgt_int ptrVal e tgtDecl hptr_ok he htag hdecl_tgt
            obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e he
            have hbor_look : lookupBorrow s.memory.borrows ptrVal.tag =
                some { tag := e.tag, targetLocal := e.localIdx,
                       targetProjection := [], perm := e.perm } := by
              rw [← htag]; exact (halloc.borrow_sync e he).2
            have hmptr_opt : mptr.withOptionalProvenance =
                ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId +
                    UInt64.ofNat ptrVal.offsetBytes),
                  some (.concrete e.allocId borTag)⟩ := by
              rcases mptr with ⟨off, prov⟩
              dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at hprov_eq hmptr_off ⊢
              subst hprov_eq hmptr_off; rfl
            rcases id hstate₄ with ⟨tf₀₄, hframes₄, _, _, hfr₄, _, _, _, _, _, halloc₄, _⟩
            injection hframes₄ with h1_tf
            injection h1_tf with h2_tf
            subst h2_tf
            obtain ⟨slot_t, mls_t, hlt_af_t, _, hslot_t, hmls_t, _, hloc_t⟩ :=
              hfr₄.lookup_local hdecl_tgt
            obtain ⟨hlive_sync, hdead_sync⟩ := halloc₄.local_alloc_sync tf₄ rfl e he
            by_cases ht_dead : slot_t = .dead
            · -- Subcase 4b-i: `e.localIdx` is `.dead` -> UB in both!
              have hs_dead : get? s.frame.locals e.localIdx = some .dead :=
                hslot_t.trans (congrArg some ht_dead)
              have hfind_none := hdead_sync hs_dead
              left
              refine mk_ub (m' := { m with stack := ⟨#[tf₄]⟩ })
                (msg := "write_bytes pointer check failed") ?_ ?_
              · rw [hanneal_step, hanneal_term, hevals]; dsimp only
                rw [evalInlineIntrinsicCall?_writeBytes]
                dsimp only
                exact wbEvalWriteBytesCall_dead_ub hop_pt hpos hle hbor_look hdecl_tgt htgtInt
                  hs_dead
              · rw [wbMiriBodyAction_eval_eq hm₁ hm₂ hm₃, hm_init, wbIte_pos hle, hmptr_opt]
                exact annealWriteRepeatedBytes_dead_err e.allocId borTag ptrVal.offsetBytes
                  (UInt8.ofNat valSc.bits) hid_lt hoff_lt hbase hfind_none hpos hle
            · -- Subcase 4b-ii: `e.localIdx` is live (`slot_t ≠ .dead`).
              have hs_not_dead : get? s.frame.locals e.localIdx ≠ some .dead := by
                rw [hslot_t]; exact fun h => ht_dead (Option.some.inj h)
              obtain ⟨⟨lay_t, hlay_t⟩, hslot_sc, hshape_fn⟩ := hlive_sync slot_t hslot_t ht_dead
              obtain ⟨localAlloc, hfind_la, hkind_la, halign_la, hshape_la⟩ :=
                hshape_fn tgtDecl hdecl_tgt
              let targetBytes := integerKindByteWidth tgtKind
              have hlay_tgt_sz : (translateTy tgtDecl.ty body.layouts).layout.size =
                  translateSizeBytes targetBytes := by
                rw [← htgtInt.prim.translateTy_layoutIdx body.layouts]
                rcases htgtInt with ⟨it, hk⟩ | ⟨ut, hk⟩
                · rw [hk]; cases it <;> rfl
                · rw [hk]; cases ut <;> rfl
              have halloc_bytes : localAlloc.allocation.byteSize.bytes.toNat = targetBytes := by
                rw [hshape_la.byteSize_eq, hlay_tgt_sz]
                cases tgtKind <;> rfl
              by_cases hinb : ptrVal.offsetBytes + countSc.bits * elemBytes ≤ targetBytes
              · -- Live in-bounds write -> whole-local fill or partial byte splice in both!
                obtain ⟨hperm_ok, hinb_kind⟩ := hlive_inbounds ptrVal countSc e tgtDecl tgtKind
                  hptr_ok hcount_pre hpos hle he htag hdecl_tgt htgtInt hs_not_dead hinb
                have hshape_tb : StackScalarAllocShape (translateSizeBytes targetBytes)
                    localAlloc.allocation := hlay_tgt_sz ▸ hshape_la
                have hbyte_nat : (UInt8.ofNat valSc.bits).toNat = valSc.bits % 256 := by
                  have hlt256 := (wbScalar_fromScalarInt_toUInt8 hrelV hszV).1
                  simp [Nat.mod_eq_of_lt hlt256]
                have hinb_la : ptrVal.offsetBytes + countSc.bits * elemBytes ≤
                    localAlloc.allocation.byteSize.bytes.toNat := by
                  rw [halloc_bytes]; exact hinb
                have hinv_eq : invalidateConflictingBorrows s.memory.borrows e.localIdx
                    (some ptrVal.tag) =
                    (updateAllocMapOnWrite allocMap e.localIdx (some ptrVal.tag)).map
                      AllocMapEntry.toBorrowEntry := by
                  rw [hbor]
                  exact wbInvalidateConflictingBorrows_eq_map_updateAllocMapOnWrite allocMap
                    e.localIdx (some ptrVal.tag)
                rcases hinb_kind with ⟨hoff0, hfull⟩ | ⟨oldSc, hold_slot⟩
                · obtain ⟨alloc', msc_new, hw_alloc, hrel_raw, halign_alloc', hshape_alloc',
                    hinit_alloc', hread_alloc'⟩ :=
                    hshape_tb.writeRepeatedByte_full (wbValidScalarBytes_integerKind tgtKind)
                      (UInt8.ofNat valSc.bits)
                  let newSc : MirAst.ScalarInt :=
                    ⟨repeatByteBits (valSc.bits % 256) targetBytes, targetBytes⟩
                  have hrel_new : ScalarRel newSc msc_new := by
                    simpa [newSc, hbyte_nat] using hrel_raw
                  have hw_alloc' : Miri.Memory.Allocation.writeRepeatedByte
                      (Miri.ABI.Size.ofBytes (UInt64.ofNat ptrVal.offsetBytes))
                      (UInt8.ofNat valSc.bits) (UInt64.ofNat (countSc.bits * elemBytes))
                      (Miri.ABI.Size.ofBytes 8) localAlloc.allocation = .ok () alloc' := by
                    rw [hoff0, hfull]; exact hw_alloc
                  have hm_write := annealWriteRepeatedBytes_live_ok e.allocId borTag
                    ptrVal.offsetBytes localAlloc alloc' (UInt8.ofNat valSc.bits)
                    hid_lt hoff_lt hbase hfind_la hpos hle hinb_la hw_alloc'
                    (st := { m with stack := ⟨#[tf₄]⟩ })
                  have hbool_tgt : tgtDecl.ty.kind = .bool →
                      newSc.sizeBytes = 1 ∧ (newSc.bits = 0 ∨ newSc.bits = 1) := by
                    intro hb; rcases htgtInt with ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hk] at hb <;> cases hb
                  have hchar_tgt : tgtDecl.ty.kind = .char →
                      newSc.sizeBytes = 4 ∧ isValidCharCode newSc.bits = true := by
                    intro hc'; rcases htgtInt with ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hk] at hc' <;> cases hc'
                  have hadv := hstate₄.advance_write_deref_scalar rfl
                    (fun x => x.updateOnWrite e.localIdx (some ptrVal.tag))
                    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                    he hdecl_tgt htgtInt.prim hslot_t ht_dead hfind_la hkind_la halign_la
                    hrel_new hlay_tgt_sz hbool_tgt hchar_tgt halign_alloc' hshape_alloc'
                    hinit_alloc' hread_alloc'
                  right; right
                  refine ⟨_, _, ptrVal, countSc, e, tgtDecl, tgtKind, hptr_ok, hcount_pre, hpos, hle,
                    he, htag, hdecl_tgt, htgtInt, hs_not_dead, hinb, ?_, ?_, ?_,
                    hadv.relocate rfl targetBb 0⟩
                  · rw [hanneal_step, hanneal_term, hevals]; dsimp only
                    rw [evalInlineIntrinsicCall?_writeBytes]
                    dsimp only
                    rw [wbEvalWriteBytesCall_full_ok hop_pt hpos hle hbor_look hperm_ok hdecl_tgt
                      htgtInt hslot_t hlt_af_t ht_dead hslot_sc hoff0 hfull, hinv_eq]
                    rfl
                  · apply wbMiri_step_writeBytes_ok (tf₃ := tf₄) hframes hfr.body_eq hfr.location_eq
                      hbb hstmt_none hterm hc hprog hdst hlt_mf hcache_dst hval_nm hcount_nm
                    rw [wbMiriBodyAction_eval_eq hm₁ hm₂ hm₃, hm_init, wbIte_pos hle, hmptr_opt]
                    exact hm_write
                  · simp [writeBytesNextAllocMap, hcount_opt, hz, hptr_ok,
                      wbLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he htag]
                · -- Partial (or full) in-bounds write into an initialized scalar local `oldSc`.
                  have hslot_eq : slot_t = .init (.scalar oldSc) :=
                    Option.some.inj (hslot_t.symm.trans hold_slot)
                  subst hslot_eq
                  have hmls_t_eq :
                      mls_t = ⟨.live (.indirect (stackAllocPlace e.allocId)), lay_t⟩ := by
                    rw [hlay_t] at hmls_t; exact Option.some.inj hmls_t.symm
                  have hvalid_tgt := wbValidScalarBytes_integerKind tgtKind
                  have hts_tgt_nat : (translateSizeBytes targetBytes).bytes.toNat = targetBytes := by
                    dsimp only [targetBytes]
                    rcases hvalid_tgt with h0 | h0 | h0 | h0 | h0 <;> (rw [h0]; rfl)
                  have hnz_sz_t :
                      (translateTy tgtDecl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO := by
                    rw [hlay_tgt_sz]; dsimp only [targetBytes]
                    cases tgtKind <;> decide
                  obtain ⟨_, hsc_spec⟩ := hloc_t.indirect_stackAllocPlace_spec hmls_t_eq
                    hbase hfind_la (halloc₄.live_key_unique e he) hnz_sz_t
                  obtain ⟨hsz_sc_eq, _, _, oldMsc, holdRel, hread_old⟩ := hsc_spec oldSc rfl
                  have holdSz : oldSc.sizeBytes = targetBytes := by
                    have h := hlay_tgt_sz.symm.trans hsz_sc_eq
                    have h1 : (translateSizeBytes oldSc.sizeBytes).bytes.toNat = oldSc.sizeBytes := by
                      rcases holdRel.validBytes with h0 | h0 | h0 | h0 | h0 <;> (rw [h0]; rfl)
                    have := congrArg (fun z : Miri.ABI.Size => z.bytes.toNat) h
                    omega
                  rw [hlay_tgt_sz] at hread_old
                  obtain ⟨alloc', msc_new, hw_alloc', hrel_raw, halign_alloc', hshape_alloc',
                    hinit_alloc', hread_alloc'⟩ :=
                    hshape_tb.writeRepeatedByte_partial hvalid_tgt holdRel holdSz
                      (UInt8.ofNat valSc.bits) hpos hinb hread_old
                  let newSc : MirAst.ScalarInt :=
                    ⟨spliceRepeatedBytes oldSc.bits (valSc.bits % 256)
                      ptrVal.offsetBytes (countSc.bits * elemBytes) targetBytes, targetBytes⟩
                  have hrel_new : ScalarRel newSc msc_new := by
                    simpa [newSc, hbyte_nat] using hrel_raw
                  have hm_write := annealWriteRepeatedBytes_live_ok e.allocId borTag
                    ptrVal.offsetBytes localAlloc alloc' (UInt8.ofNat valSc.bits)
                    hid_lt hoff_lt hbase hfind_la hpos hle hinb_la hw_alloc'
                    (st := { m with stack := ⟨#[tf₄]⟩ })
                  have hbool_tgt : tgtDecl.ty.kind = .bool →
                      newSc.sizeBytes = 1 ∧ (newSc.bits = 0 ∨ newSc.bits = 1) := by
                    intro hb; rcases htgtInt with ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hk] at hb <;> cases hb
                  have hchar_tgt : tgtDecl.ty.kind = .char →
                      newSc.sizeBytes = 4 ∧ isValidCharCode newSc.bits = true := by
                    intro hc'; rcases htgtInt with ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hk] at hc' <;> cases hc'
                  have hadv := hstate₄.advance_write_deref_scalar rfl
                    (fun x => x.updateOnWrite e.localIdx (some ptrVal.tag))
                    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                    he hdecl_tgt htgtInt.prim hslot_t ht_dead hfind_la hkind_la halign_la
                    hrel_new hlay_tgt_sz hbool_tgt hchar_tgt halign_alloc' hshape_alloc'
                    hinit_alloc' hread_alloc'
                  right; right
                  refine ⟨_, _, ptrVal, countSc, e, tgtDecl, tgtKind, hptr_ok, hcount_pre, hpos, hle,
                    he, htag, hdecl_tgt, htgtInt, hs_not_dead, hinb, ?_, ?_, ?_,
                    hadv.relocate rfl targetBb 0⟩
                  · rw [hanneal_step, hanneal_term, hevals]; dsimp only
                    rw [evalInlineIntrinsicCall?_writeBytes]
                    dsimp only
                    rw [wbEvalWriteBytesCall_partial_ok hop_pt hpos hle hbor_look hperm_ok hdecl_tgt
                      htgtInt hold_slot hlt_af_t hinb, hinv_eq]
                    rfl
                  · apply wbMiri_step_writeBytes_ok (tf₃ := tf₄) hframes hfr.body_eq hfr.location_eq
                      hbb hstmt_none hterm hc hprog hdst hlt_mf hcache_dst hval_nm hcount_nm
                    rw [wbMiriBodyAction_eval_eq hm₁ hm₂ hm₃, hm_init, wbIte_pos hle, hmptr_opt]
                    exact hm_write
                  · simp [writeBytesNextAllocMap, hcount_opt, hz, hptr_ok,
                      wbLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he htag]
              · -- Out-of-bounds write on live target allocation -> UB in both!
                have hoob_la : localAlloc.allocation.byteSize.bytes.toNat <
                    ptrVal.offsetBytes + countSc.bits * elemBytes := by
                  rw [halloc_bytes]; omega
                left
                refine mk_ub (m' := { m with stack := ⟨#[tf₄]⟩ })
                  (msg := "write_bytes pointer check failed") ?_ ?_
                · rw [hanneal_step, hanneal_term, hevals]; dsimp only
                  rw [evalInlineIntrinsicCall?_writeBytes]
                  dsimp only
                  exact wbEvalWriteBytesCall_oob_ub hop_pt hpos hle hbor_look hdecl_tgt htgtInt hinb
                · rw [wbMiriBodyAction_eval_eq hm₁ hm₂ hm₃, hm_init, wbIte_pos hle, hmptr_opt]
                  exact annealWriteRepeatedBytes_oob_err e.allocId borTag ptrVal.offsetBytes
                    localAlloc (UInt8.ofNat valSc.bits) hid_lt hoff_lt hbase hfind_la hpos hle
                    hoob_la
        · -- Subcase 4c: `total > isizeMaxBytes` on `.ptr` -> UB in both!
          left
          refine mk_ub (m' := { m with stack := ⟨#[tf₄]⟩ })
            (msg := "overflow computing total size of write_bytes") ?_ ?_
          · rw [hanneal_step, hanneal_term, hevals]; dsimp only
            rw [evalInlineIntrinsicCall?_writeBytes]
            dsimp only
            exact wbEvalWriteBytesCall_overflow_ub hop_pt hle
          · rw [wbMiriBodyAction_eval_eq hm₁ hm₂ hm₃, hm_init, wbIte_neg hle]

/-- **One real step of a translated
`core::intrinsics::write_bytes::<T>(dst, val, count)` call with explicit
post-step `allocMap'`.**

Covers:

1. `count * size_of::<T>() > isize::MAX` (`isizeMaxBytes`) reports UB in both
   machines;
2. `count * size_of::<T>() = 0` steps to `(targetBb, 0)` with no memory change
   and `StateRelLM3_1` preserved under `allocMap` (even on provenance-free,
   dangling, dead, or out-of-bounds pointers);
3. uninitialized or dead `dst` / `val` / `count`, provenance-free `.scalar`
   `dst` on positive size, or a dead target stack allocation on positive size
   reports UB in both machines;
4. `dst` holding a `PtrRel`-related `.ptr ptrVal 8` into an address-taken
   primitive integer local (`e ∈ allocMap`, `StackScalarAllocShape`):
   - out-of-bounds positive fill on a live target local
     (`targetBytes < offsetBytes + total`) reports UB in both machines across
     all borrow permissions;
   - whole-local in-bounds fill (`offsetBytes = 0`, `total = targetBytes`,
     `e.perm = .active ∨ e.perm = .reserved`) or partial in-bounds fill into an
     initialized scalar local (`∃ oldSc, get? locals e.localIdx = some (.init (.scalar oldSc))`,
     `e.perm = .active ∨ e.perm = .reserved`) writes `repeatByteBits` /
     `spliceRepeatedBytes` in both machines and preserves `StateRelLM3_1` under
     `writeBytesNextAllocMap` (activating `.reserved → .active` and disabling
     foreign borrows on `e.localIdx`). -/
theorem call_intrinsic_write_bytes_simulation_explicit
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {c : ConstOperand} {ptrIdx dstIdx : Local} {valOp countOp : MirAst.Operand}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {pointeeTy : Ty}
    (hterm : bb.terminator.kind =
      .call (.constant c) [.copy ⟨ptrIdx, []⟩, valOp, countOp] ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef AnnealIntrinsic.writeBytes.defPath [pointeeTy.kind])
    (hcallee : findCallee? s.memory.callees AnnealIntrinsic.writeBytes.defPath = none)
    (hprog : targetBb ≠ s.frame.blockIdx ∨ s.frame.stmtIdx ≠ 0)
    {ptrDecl : LocalDecl} {ptrMut : Mutability}
    (hptrDecl : get? body.localDecls ptrIdx = some ptrDecl)
    (hptrTy : ptrDecl.ty.kind = .rawPtr ptrMut pointeeTy.kind)
    (hptrImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf ptrIdx)
    {valTy countTy : Ty}
    (hvalInt : IsIntegralTy valTy .u8)
    (hvalOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf valOp valTy)
    (hcountInt : IsIntegralTy countTy .usize)
    (hcountOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf countOp countTy)
    {dstDecl : LocalDecl} (hdst : get? body.localDecls dstIdx = some dstDecl)
    {ptId : Miri.MIR.TyId} {elemBytes : Nat}
    (hpt : WriteBytesPointee body.layouts pointeeTy.kind ptId elemBytes)
    (htgt_int : ∀ ptrVal e tgtDecl,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      ∃ tgtKind, IsIntegralTy tgtDecl.ty tgtKind)
    (hlive_inbounds : ∀ ptrVal countSc e tgtDecl tgtKind,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      0 < countSc.bits * elemBytes →
      countSc.bits * elemBytes ≤ isizeMaxBytes →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      IsIntegralTy tgtDecl.ty tgtKind →
      get? s.frame.locals e.localIdx ≠ some .dead →
      ptrVal.offsetBytes + countSc.bits * elemBytes ≤ integerKindByteWidth tgtKind →
      (e.perm = .active ∨ e.perm = .reserved) ∧
        ((ptrVal.offsetBytes = 0 ∧ countSc.bits * elemBytes = integerKindByteWidth tgtKind) ∨
          ∃ oldSc, get? s.frame.locals e.localIdx = some (.init (.scalar oldSc)))) :
    StepRelLM3_1 body m
      (writeBytesNextAllocMap s.frame.locals allocMap ptrIdx countOp elemBytes)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases wbCall_writeBytes_core hstate hphase hbb hstmt_none hstmt_len hterm hc hcallee hprog
      hptrDecl hptrTy hptrImm hvalInt hvalOp hcountInt hcountOp hdst hpt htgt_int hlive_inbounds with
    ⟨ha, m', msg, hm⟩ |
    ⟨s', m', ha, hm, hnext, hst⟩ |
    ⟨s', m', ptrVal, countSc, e, _, _, _, _, _, _, _, _, _, _, _, _, ha, hm, hnext, hst⟩
  · rw [ha, hm]; exact .ub _ _
  · rw [ha, hm, hnext]; exact .step _ _ hst
  · rw [ha, hm, hnext]; exact .step _ _ hst

/-- **One real step of a translated
`core::intrinsics::write_bytes::<T>(dst, val, count)` call preserving
`allocMap`.**

Concludes `StepRelLM3_1 body m allocMap (stepMirFn body s)` against
`Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m`
directly. Covers both whole-local in-bounds fills (`offsetBytes = 0`,
`total = targetBytes`, whether previously `.uninit` or `.init`) and partial
in-bounds byte-splice fills (`0 < total`, `offsetBytes + total ≤ targetBytes` on
an initialized scalar local
`∃ oldSc, get? s.frame.locals e.localIdx = some (.init (.scalar oldSc))`).
On live in-bounds positive writes through `ptrVal`, requires `e.perm = .active`
and that any foreign borrow of `e.localIdx` in `allocMap` is already `.disabled`
(which holds automatically when `e` is the unique borrow of `e.localIdx`, e.g.,
`[⟨tag, localIdx, allocId, .active⟩]` from `_p = &raw mut _x`), so
`updateAllocMapOnWrite` leaves `allocMap` unchanged. No permission restriction
is imposed on zero-byte, overflow, dead-allocation, or out-of-bounds calls. -/
theorem call_intrinsic_write_bytes_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {c : ConstOperand} {ptrIdx dstIdx : Local} {valOp countOp : MirAst.Operand}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {pointeeTy : Ty}
    (hterm : bb.terminator.kind =
      .call (.constant c) [.copy ⟨ptrIdx, []⟩, valOp, countOp] ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef AnnealIntrinsic.writeBytes.defPath [pointeeTy.kind])
    (hcallee : findCallee? s.memory.callees AnnealIntrinsic.writeBytes.defPath = none)
    (hprog : targetBb ≠ s.frame.blockIdx ∨ s.frame.stmtIdx ≠ 0)
    {ptrDecl : LocalDecl} {ptrMut : Mutability}
    (hptrDecl : get? body.localDecls ptrIdx = some ptrDecl)
    (hptrTy : ptrDecl.ty.kind = .rawPtr ptrMut pointeeTy.kind)
    (hptrImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf ptrIdx)
    {valTy countTy : Ty}
    (hvalInt : IsIntegralTy valTy .u8)
    (hvalOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf valOp valTy)
    (hcountInt : IsIntegralTy countTy .usize)
    (hcountOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf countOp countTy)
    {dstDecl : LocalDecl} (hdst : get? body.localDecls dstIdx = some dstDecl)
    {ptId : Miri.MIR.TyId} {elemBytes : Nat}
    (hpt : WriteBytesPointee body.layouts pointeeTy.kind ptId elemBytes)
    (htgt_int : ∀ ptrVal e tgtDecl,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      ∃ tgtKind, IsIntegralTy tgtDecl.ty tgtKind)
    (hlive_inbounds : ∀ ptrVal countSc e tgtDecl tgtKind,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      0 < countSc.bits * elemBytes →
      countSc.bits * elemBytes ≤ isizeMaxBytes →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      IsIntegralTy tgtDecl.ty tgtKind →
      get? s.frame.locals e.localIdx ≠ some .dead →
      ptrVal.offsetBytes + countSc.bits * elemBytes ≤ integerKindByteWidth tgtKind →
      (∀ x ∈ allocMap, x.localIdx = e.localIdx →
        (x.tag = ptrVal.tag ∧ x.perm = .active) ∨ (x.tag ≠ ptrVal.tag ∧ x.perm = .disabled)) ∧
        ((ptrVal.offsetBytes = 0 ∧ countSc.bits * elemBytes = integerKindByteWidth tgtKind) ∨
          ∃ oldSc, get? s.frame.locals e.localIdx = some (.init (.scalar oldSc)))) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  have hlive_weak : ∀ ptrVal countSc e tgtDecl tgtKind,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      0 < countSc.bits * elemBytes →
      countSc.bits * elemBytes ≤ isizeMaxBytes →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      IsIntegralTy tgtDecl.ty tgtKind →
      get? s.frame.locals e.localIdx ≠ some .dead →
      ptrVal.offsetBytes + countSc.bits * elemBytes ≤ integerKindByteWidth tgtKind →
      (e.perm = .active ∨ e.perm = .reserved) ∧
        ((ptrVal.offsetBytes = 0 ∧ countSc.bits * elemBytes = integerKindByteWidth tgtKind) ∨
          ∃ oldSc, get? s.frame.locals e.localIdx = some (.init (.scalar oldSc))) := by
    intro ptrVal countSc e tgtDecl tgtKind hp hc_pre hpos hle he htag hd ht hnd hinb
    obtain ⟨hall, hinb_kind⟩ :=
      hlive_inbounds ptrVal countSc e tgtDecl tgtKind hp hc_pre hpos hle he htag hd ht hnd hinb
    rcases hall e he rfl with ⟨_, hact⟩ | ⟨hne, _⟩
    · exact ⟨Or.inl hact, hinb_kind⟩
    · exact absurd htag hne
  rcases wbCall_writeBytes_core hstate hphase hbb hstmt_none hstmt_len hterm hc hcallee hprog
      hptrDecl hptrTy hptrImm hvalInt hvalOp hcountInt hcountOp hdst hpt htgt_int hlive_weak with
    ⟨ha, m', msg, hm⟩ |
    ⟨s', m', ha, hm, _, hst⟩ |
    ⟨s', m', ptrVal, countSc, e, tgtDecl, tgtKind, hp, hc_pre, hpos, hle, he, htag, hd, ht,
      hnd, hinb, ha, hm, _, hst⟩
  · rw [ha, hm]; exact .ub _ _
  · rw [ha, hm]; exact .step _ _ hst
  · obtain ⟨hall, _⟩ :=
      hlive_inbounds ptrVal countSc e tgtDecl tgtKind hp hc_pre hpos hle he htag hd ht hnd hinb
    rw [updateAllocMapOnWrite_eq_self_of_active hall] at hst
    rw [ha, hm]
    exact .step _ _ hst

/-- **Characterized Tree Borrows permission divergence on `write_bytes`
(`LM-4.2` Case 5).**

When `dst` points to a live, in-bounds primitive integer stack local
(`offsetBytes = 0`, `total = targetBytes`, `0 < total ≤ isizeMaxBytes`) through
a borrow entry whose permission is `.frozen` or `.disabled`, Anneal's
`evalWriteBytesCall` rejects the write with `MirStepNode.fail .ub`, whereas
`lean-miri`'s `annealWriteRepeatedBytes` instantiation (which enforces
allocation liveness, bounds, and mutability via `checkAndDerefPtr` +
`Allocation.writeRepeatedByte` without Tree Borrows transition hooks) steps
normally to `(targetBb, 0)` with `.ok true`.

Note on alignment: neither Anneal's `evalWriteBytesCall` nor `lean-miri`'s
`annealWriteRepeatedBytes` (matching `write_bytes_intrinsic` in
`rustc_const_eval`) checks pointer alignment, which is a shared modeling gap
relative to Rust's library precondition on `core::intrinsics::write_bytes`. -/
theorem call_intrinsic_write_bytes_perm_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {c : ConstOperand} {ptrIdx dstIdx : Local} {valOp countOp : MirAst.Operand}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {pointeeTy : Ty}
    (hterm : bb.terminator.kind =
      .call (.constant c) [.copy ⟨ptrIdx, []⟩, valOp, countOp] ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef AnnealIntrinsic.writeBytes.defPath [pointeeTy.kind])
    (hcallee : findCallee? s.memory.callees AnnealIntrinsic.writeBytes.defPath = none)
    (hprog : targetBb ≠ s.frame.blockIdx ∨ s.frame.stmtIdx ≠ 0)
    {ptrDecl : LocalDecl} {ptrMut : Mutability}
    (hptrDecl : get? body.localDecls ptrIdx = some ptrDecl)
    (hptrTy : ptrDecl.ty.kind = .rawPtr ptrMut pointeeTy.kind)
    (hptrImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf ptrIdx)
    {valTy countTy : Ty}
    (hvalInt : IsIntegralTy valTy .u8)
    (hvalOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf valOp valTy)
    (hcountInt : IsIntegralTy countTy .usize)
    (hcountOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf countOp countTy)
    {dstDecl : LocalDecl} (hdst : get? body.localDecls dstIdx = some dstDecl)
    {ptId : Miri.MIR.TyId} {elemBytes : Nat}
    (hpt : WriteBytesPointee body.layouts pointeeTy.kind ptId elemBytes)
    {ptrVal : ProvenancePtr} {valSc countSc : MirAst.ScalarInt}
    {e : AllocMapEntry} {tgtDecl : LocalDecl} {tgtKind : Miri.MIR.IntegerKind}
    (hptr_slot : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (hval_pre : WriteBytesScalarPreVal s.frame.locals valOp valSc)
    (hcount_pre : WriteBytesScalarPreVal s.frame.locals countOp countSc)
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hdecl_tgt : get? body.localDecls e.localIdx = some tgtDecl)
    (htgtInt : IsIntegralTy tgtDecl.ty tgtKind)
    (ht_live : get? s.frame.locals e.localIdx ≠ some .dead)
    (hpos : 0 < countSc.bits * elemBytes)
    (hle : countSc.bits * elemBytes ≤ isizeMaxBytes)
    (hoff0 : ptrVal.offsetBytes = 0)
    (hfull : countSc.bits * elemBytes = integerKindByteWidth tgtKind)
    (hperm : e.perm = .frozen ∨ e.perm = .disabled) :
    stepMirFn body s = MirStepNode.fail .ub ∧
      ∃ m', Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, halloc, _⟩ := id hstate
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
  have hanneal_step : stepMirFn body s = evalTerminator s bb.terminator (some body) := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  have hanneal_term :=
    evalTerminator_inline_intrinsic_call (s := s) (body := body) hterm hc hcallee (by nofun)
  have ha₁ : evalOperand s.frame.locals (.copy ⟨ptrIdx, []⟩) s.memory.borrows s.memory.globals
      body.layouts s.memory.callerLocals = .ok (.ptr ptrVal 8) s.frame.locals := by
    rw [wbEvalOperand_copy_local_eq, hptr_slot]
  have ha₂ := hval_pre.evalOperand_ok s.memory.borrows s.memory.globals body.layouts
    s.memory.callerLocals
  have ha₃ := hcount_pre.evalOperand_ok s.memory.borrows s.memory.globals body.layouts
    s.memory.callerLocals
  have hevals : evalOperands s.frame.locals [.copy ⟨ptrIdx, []⟩, valOp, countOp]
      s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals =
      .ok [.ptr ptrVal 8, .scalar valSc, .scalar countSc] s.frame.locals := by
    simp only [evalOperands, ha₁, ha₂, ha₃]
  have hop_pt := operandPointeeBytes?_copy_rawPtr (layouts := body.layouts) hptrDecl hptrTy hpt.anneal_size
  have hbor_look : lookupBorrow s.memory.borrows ptrVal.tag =
      some { tag := e.tag, targetLocal := e.localIdx,
             targetProjection := [], perm := e.perm } := by
    rw [← htag]; exact (halloc.borrow_sync e he).2
  refine ⟨?_, ?_⟩
  · rw [hanneal_step, hanneal_term, hevals]; dsimp only
    rw [evalInlineIntrinsicCall?_writeBytes]
    dsimp only
    exact wbEvalWriteBytesCall_perm_ub hop_pt hpos hle hbor_look hperm
  · obtain ⟨_, _, _, hlt_mf, _, _, hdmls_eq, hdloc⟩ := hfr.lookup_local hdst
    have hcache_dst : ∀ l, (tf.locals[dstIdx]'hlt_mf).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      intro l hl; rw [hdmls_eq] at hl; exact hdloc.cachedLayout_eq l hl
    let tf₁ := cacheFrameLocalLayout tf dstIdx hlt_mf (translateTy dstDecl.ty body.layouts)
    have hstate₁ : StateRelLM3_1 body s { m with stack := ⟨#[tf₁]⟩ } allocMap :=
      hstate.cache_layout hframes hdst hlt_mf
    have himm₁ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₁ j :=
      fun j hj => hj.cache_layout hlt_mf _
    rcases wbEvalOperand_rawPtr_lm3_1 hstate₁ rfl hptrDecl hptrTy
        (himm₁ ptrIdx (hptrImm tf hframes)) with
      ⟨hd, _⟩ | ⟨_, hun, _⟩ | ⟨_, _, _, hsc, _⟩ | ⟨ptrVal', mptr, tf₂, hptr_ok, hptrRel, hm₁, hstate₂, hvals₂⟩
    · rw [hptr_slot] at hd; cases hd
    · rw [hptr_slot] at hun; cases hun
    · rw [hptr_slot] at hsc; cases hsc
    · rw [hptr_slot] at hptr_ok
      injection hptr_ok with hp_eq
      injection hp_eq with hp_eq'
      injection hp_eq' with hp_eq'' _; subst hp_eq''
      have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
        fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂ (himm₁ j hj)
      rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl ((hvalOp tf hframes).mono_immediate himm₂)
          hvalInt.prim with
        ⟨_, _, ha₂', _⟩ | ⟨_, ha₂', _⟩ | ⟨valSc', mval, tf₃, ha₂', hm₂, hstate₃, hrelI_val, hvals₃⟩
      · rw [ha₂] at ha₂'; cases ha₂'
      · rw [ha₂] at ha₂'; cases ha₂'
      · rw [ha₂] at ha₂'
        injection ha₂' with hv_eq _
        injection hv_eq with hv_eq'; subst hv_eq'
        obtain ⟨hrelV, hszV⟩ := wbImmediateRel_of_integral hvalInt hrelI_val
        have himm₃ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₃ j :=
          fun j hj => IsImmediateFrameLocal.of_values_eq hvals₃ (himm₂ j hj)
        rcases annealEvalOperand_scalar_lm3_1 hstate₃ rfl
            ((hcountOp tf hframes).mono_immediate himm₃) hcountInt.prim with
          ⟨_, _, ha₃', _⟩ | ⟨_, ha₃', _⟩ |
          ⟨countSc', mcount, tf₄, ha₃', hm₃, hstate₄, hrelI_cnt, _⟩
        · rw [ha₃] at ha₃'; cases ha₃'
        · rw [ha₃] at ha₃'; cases ha₃'
        · rw [ha₃] at ha₃'
          injection ha₃' with hc_eq _
          injection hc_eq with hc_eq'; subst hc_eq'
          obtain ⟨hrelC, hszC⟩ := wbImmediateRel_of_integral hcountInt hrelI_cnt
          rcases hptrRel with
            ⟨_, borTag, hprov_eq, hid_lt, hoff_lt, hmptr_off, ⟨e', he', htag', rfl⟩⟩
          have he_eq : e' = e := Option.some.inj
            ((wbLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he' htag').symm.trans
              (wbLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he htag))
          subst he_eq
          obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e' he'
          have hmptr_opt : mptr.withOptionalProvenance =
              ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId +
                  UInt64.ofNat ptrVal.offsetBytes),
                some (.concrete e'.allocId borTag)⟩ := by
            rcases mptr with ⟨off, prov⟩
            dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at hprov_eq hmptr_off ⊢
            subst hprov_eq hmptr_off; rfl
          rcases id hstate₄ with ⟨tf₀₄, hframes₄, _, _, hfr₄, _, _, _, _, _, halloc₄, _⟩
          injection hframes₄ with h1_tf
          injection h1_tf with h2_tf
          subst h2_tf
          obtain ⟨slot_t, _, _, _, hslot_t, _, _, _⟩ := hfr₄.lookup_local hdecl_tgt
          have ht_ne_dead : slot_t ≠ .dead := fun hd => ht_live (hslot_t.trans (congrArg some hd))
          obtain ⟨hlive_sync, _⟩ := halloc₄.local_alloc_sync tf₄ rfl e' he'
          obtain ⟨_, _, hshape_fn⟩ := hlive_sync slot_t hslot_t ht_ne_dead
          obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hshape_fn tgtDecl hdecl_tgt
          let targetBytes := integerKindByteWidth tgtKind
          have hlay_tgt_sz : (translateTy tgtDecl.ty body.layouts).layout.size =
              translateSizeBytes targetBytes := by
            rw [← htgtInt.prim.translateTy_layoutIdx body.layouts]
            rcases htgtInt with ⟨it, hk⟩ | ⟨ut, hk⟩
            · rw [hk]; cases it <;> rfl
            · rw [hk]; cases ut <;> rfl
          have halloc_bytes : localAlloc.allocation.byteSize.bytes.toNat = targetBytes := by
            rw [hshape_la.byteSize_eq, hlay_tgt_sz]
            cases tgtKind <;> rfl
          have hshape_tb : StackScalarAllocShape (translateSizeBytes targetBytes)
              localAlloc.allocation := hlay_tgt_sz ▸ hshape_la
          obtain ⟨alloc', _, hw_alloc, _, _, _, _, _⟩ :=
            hshape_tb.writeRepeatedByte_full (wbValidScalarBytes_integerKind tgtKind)
              (UInt8.ofNat valSc.bits)
          have hw_alloc' : Miri.Memory.Allocation.writeRepeatedByte
              (Miri.ABI.Size.ofBytes (UInt64.ofNat ptrVal.offsetBytes))
              (UInt8.ofNat valSc.bits) (UInt64.ofNat (countSc.bits * elemBytes))
              (Miri.ABI.Size.ofBytes 8) localAlloc.allocation = .ok () alloc' := by
            rw [hoff0, hfull]; exact hw_alloc
          have hinb_la : ptrVal.offsetBytes + countSc.bits * elemBytes ≤
              localAlloc.allocation.byteSize.bytes.toNat := by
            rw [halloc_bytes, hoff0, Nat.zero_add, hfull]
            exact Nat.le_refl _
          have hm_write := annealWriteRepeatedBytes_live_ok e'.allocId borTag ptrVal.offsetBytes
            localAlloc alloc' (UInt8.ofNat valSc.bits) hid_lt hoff_lt hbase hfind_la hpos hle
            hinb_la hw_alloc' (st := { m with stack := ⟨#[tf₄]⟩ })
          have hpt_m := annealPointeeTypeOf_rawPtr hptrTy hpt.encoded_eq
            (ly := body.layouts) { m with stack := ⟨#[tf₄]⟩ }
          have hm_init := wbAnnealWriteBytesEval_init { m with stack := ⟨#[tf₄]⟩ } hpt_m
            hpt.miri_size hpt.lt_u64
            (wbIntrinsicPointer_fromPointer mptr (translateTy ptrDecl.ty body.layouts) _)
            (valLay := translateTy valTy body.layouts)
            (countLay := translateTy countTy body.layouts) hrelV hszV hrelC hszC
          exact ⟨_, wbMiri_step_writeBytes_ok (tf₃ := tf₄) hframes hfr.body_eq hfr.location_eq hbb
            hstmt_none hterm hc hprog hdst hlt_mf hcache_dst ((hvalOp tf hframes).translate_ne_move)
            ((hcountOp tf hframes).translate_ne_move) (by
              rw [wbMiriBodyAction_eval_eq hm₁ hm₂ hm₃, hm_init, wbIte_pos hle, hmptr_opt]
              exact hm_write)⟩

end LeanMiriSpec.Correspondence
