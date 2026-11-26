/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.UnionLM2_4Step
import Miri.Interpreter.ValidityVisitor

/-!
# Padded Union with `[(); N]` ZST Array Arm (`LM-2.4`, `kani#5176` / `kani#5159`)

Extracted from `UnionLM2_4.lean` so every `LM-2.4` module stays strictly
`< 3,500` LOC.

Key architectural properties:
* No custom `isUninhabitedEncodedTyId` operand-evaluation override hook:
  `annealEvalOperandLM2_4PaddedZst` delegates non-ZST-array `[.Field j fty]`
  reads directly to `annealEvalOperandLM2_4`, projects `[(); N]` union arms
  through vendored `Miri.Interpreter.projectField` with
  `annealUnionPaddedZstProjectionCx` (preserving `.Array Size.ZERO N`), and
  routes `[.Field j fty, .ConstantIndex offset minLen false]` through vendored
  `Miri.Interpreter.projectField` + `Miri.Interpreter.projectConstantIndex`
  (`annealProjectList` + `annealLiftProjectionError`).
* Typed copies (`copyOp` / `copyOpAllowTransmute` in
  `annealRvalueHooksLM2_4PaddedZst`) validate the copied operand via vendored
  `Miri.Interpreter.ValidityVisitor.validatePlace` / `ValidityVisitor.visit`
  (`annealUnionValidityHooks`), so uninhabited union field reads (`VoidZst` /
  `!`) fault inside vendored `ValidityVisitor.visit`
  (`"validation: zero-variant enum value"` / `"validation: never value"`),
  while whole-union copies, `[(); N]` ZST arrays, and `()` unit reads succeed
  without reading uninitialized padding bytes.
* `annealStepHooksLM2_4` in `UnionLM2_4Core.lean` remains completely untouched.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 10. Padded Union with `[(); N]` ZST Array Arm (`kani#5176` / `kani#5159`)

When a `#[repr(C)] union` has a zero-sized `[(); N]` array arm (`N > 0`) alongside
a larger payload arm of size `S ∈ {1, 2, 4, 8, 16}`:
* Constructing or writing the `[(); N]` ZST arm (`_u = PU { z: [(); N] }` or
  `_u.z = [(); N]`) into an uninitialized union activates a 0-byte arm whose
  Anneal representation is `.init (.aggregate 0 (List.replicate n .unit))`
  (`unionActiveSlotIsZstPlaceholder = true`) with byte image `replicateUninitBytes S`
  (all `S` bytes `.uninit`), while `lean-miri` allocates an `S`-byte stack
  allocation with `InitMask.new (translateSizeBytes S) false`
  (`PaddedZstUnionUninitMemRel`).
* Overwriting an already-initialized union (holding scalar `sc` of width
  `k = sc.sizeBytes ≤ S`) with `_u.z = [(); N]` (`0` bytes) sets the typed
  slots to `List.replicate n .unit` and attaches the `D13a` raw-byte overlay
  retaining `[0, k)` initialized and `[k, S)` uninitialized in Anneal, while a
  0-byte `annealMemCopyOp` in `lean-miri` preserves `UnionMemRel` in place.
* Whole-union copies and moves (`_w = copy _u`, `_w = move _u`) of a ZST-initialized
  union preserve `InitMask.new (translateSizeBytes S) false` in `lean-miri`
  (`union_copy_uninit_alloc_spec`) and `.init (.aggregate 0 (List.replicate n .unit))`
  in Anneal.
* Reading the inhabited `[(); N]` ZST arm (`_r = copy _u.z`) or an in-bounds
  element (`_r = copy _u.z[i]`, `i < N`) succeeds on both all-uninit
  ZST-initialized unions and payload-initialized unions without reading any
  uninitialized padding bytes, whereas reading an out-of-bounds element (`i ≥ N`),
  an uninitialized scalar payload field (`w > 0`), or an uninhabited 0-byte field
  (`tyIsUninhabited = true`, `kani#5159`) is undefined behavior in both machines. -/

/-- The canonical Anneal value of `()` (`Value.unit`). -/
def zstUnitVal : Value := .unit

/-- The canonical Anneal value of `[(); N]`: `N` copies of `zstUnitVal`. -/
def zstArrayVal (N : Nat) : Value := .aggregate 0 (List.replicate N zstUnitVal)

/-- The `n`-slot all-`.unit` Anneal union field list produced when a union is
initialized via a zero-sized `[(); N]` placeholder arm (`unionActiveSlotIsZstPlaceholder`). -/
def unionAllUnitFields (n : Nat) : List Value := List.replicate n .unit

/-- A `#[repr(C)] union` of size `S ∈ {1, 2, 4, 8, 16}` with an inhabited
`[(); N]` ZST array arm at field `f_z < n` (layout index `zstFlIdx`). -/
structure WellTypedPaddedZstUnionTy
    (layouts : LayoutTable) (uTy : Ty) (S N f_z zstFlIdx : Nat) : Prop where
  size_valid : ValidScalarBytes S
  count_pos : 0 < N
  fields_union : ∃ n, (translateTy uTy layouts).layout.fields = .Union n ∧ f_z < n
  size_eq : (translateTy uTy layouts).layout.size = translateSizeBytes S
  sized : (translateTy uTy layouts).layout.isSized = true
  align_le : (translateTy uTy layouts).layout.align.abi.pow2 ≤ 29
  adt_spec : ∃ defPath args tl n zstTl,
    uTy.kind = .adt defPath args ∧
    0 < uTy.layoutIdx ∧
    uTy.layoutIdx < 900 ∧
    layouts.lookup uTy.layoutIdx = some tl ∧
    tl.fields = .union n ∧
    tl.variants = .single 0 ∧
    tl.isUninhabited = false ∧
    tl.size.bytes = S ∧
    tl.fieldLayouts.length = n ∧
    layouts.pointerBits = 64 ∧
    layouts.isLittleEndian = true ∧
    get? tl.fieldLayouts f_z = some zstFlIdx ∧
    0 < zstFlIdx ∧
    layouts.lookup zstFlIdx = some zstTl ∧
    zstTl.isUninhabited = false ∧
    zstTl.size.bytes = 0 ∧
    zstTl.fields = .array ⟨0⟩ N ∧
    zstTl.variants = .single 0 ∧
    zstTl.fieldLayouts = []

/-- A memory-backed `S`-byte union local `mp` initialized via a 0-byte ZST arm
(such as `[(); N]`): `mp` points at offset `0` of its own live mutable `S`-byte
stack allocation whose `initializationMask` is `InitMask.new (translateSizeBytes S) false`
(all `S` bytes uninitialized). -/
inductive PaddedZstUnionUninitMemRel
    (mach : AnnealMachine) (uTy : Ty) (layouts : LayoutTable) (S : Nat)
    (mp : Miri.Interpreter.MemPlace AnnealProv) : Prop where
  | mk
      (allocId : Miri.Memory.AllocId)
      (tag : Miri.Memory.BorTag)
      (baseAddr : UInt64)
      (localAlloc :
        Miri.Memory.LocalAllocation
          AnnealProv
          (Option Miri.TreeBorrows.BorrowTree)
          Miri.Memory.MiriMemoryKind)
      (ptr_prov : mp.ptr.provenance = some (.concrete allocId tag))
      (no_misalign : mp.misaligned = none)
      (thin_meta : mp.metadata = .none)
      (live_lookup : (allocId, localAlloc) ∈ mach.memory.live.toList)
      (base_lookup : mach.lookupBaseAddr allocId = some baseAddr)
      (ptr_addr_eq : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
      (addr_no_overflow : baseAddr.toNat + S < 2 ^ 64)
      (alloc_size : localAlloc.allocation.byteSize = translateSizeBytes S)
      (alloc_len : localAlloc.allocation.len = S)
      (alloc_mut : localAlloc.allocation.mutability = .Mut)
      (alloc_prov : localAlloc.allocation.provenanceMap = Miri.Memory.ProvenanceMap.new)
      (alloc_align : localAlloc.allocation.align = (translateTy uTy layouts).layout.align.abi)
      (alloc_extra : localAlloc.allocation.extra = none)
      (alloc_native : localAlloc.allocation.nativeBuffer = none)
      (mask_uninit :
        localAlloc.allocation.initializationMask =
          Miri.Memory.InitMask.new (translateSizeBytes S) false) :
      PaddedZstUnionUninitMemRel mach uTy layouts S mp

theorem PaddedZstUnionUninitMemRel.of_live_base
    {mach mach' : AnnealMachine} {uTy : Ty} {layouts : LayoutTable} {S : Nat}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : PaddedZstUnionUninitMemRel mach uTy layouts S mp)
    (hlive : ∀ a la, (a, la) ∈ mach.memory.live.toList → (a, la) ∈ mach'.memory.live.toList)
    (hbase : ∀ a b, mach.lookupBaseAddr a = some b → mach'.lookupBaseAddr a = some b) :
    PaddedZstUnionUninitMemRel mach' uTy layouts S mp := by
  cases h with
  | mk allocId tag baseAddr la hprov hmis hmeta hl hb hptr hovf hsz hlen hmut hp hal hex hnat hmask =>
    exact .mk allocId tag baseAddr la hprov hmis hmeta (hlive _ _ hl) (hbase _ _ hb)
      hptr hovf hsz hlen hmut hp hal hex hnat hmask

/-- Any scalar read of width `w ∈ {1, 2, 4, 8, 16}` (`w ≤ S`) from an all-uninit
ZST-initialized union allocation (`PaddedZstUnionUninitMemRel`) encounters an
uninitialized byte at offset `0` and fails with `AllocError.invalidUninitBytes`. -/
theorem PaddedZstUnionUninitMemRel.readScalar_uninit_error
    {mach : AnnealMachine} {uTy : Ty} {layouts : LayoutTable} {S w : Nat}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hS : ValidScalarBytes S) (hw : ValidScalarBytes w) (hwS : w ≤ S)
    (hmem : PaddedZstUnionUninitMemRel mach uTy layouts S mp) :
    ∃ allocId tag localAlloc badRange,
      mp.ptr.provenance = some (.concrete allocId tag) ∧
      (allocId, localAlloc) ∈ mach.memory.live.toList ∧
      localAlloc.allocation.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes w)) false =
          .error (.invalidUninitBytes badRange) := by
  cases hmem with
  | mk allocId tag baseAddr la hprov _ _ hlive _ _ _ hsz hlen _ _ _ _ _ hmask =>
    have hbad : la.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes w)) =
        .ok (.error (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes w))) := by
      rw [hmask]
      rcases hS with rfl | rfl | rfl | rfl | rfl <;>
        rcases hw with rfl | rfl | rfl | rfl | rfl <;>
        (try omega) <;>
        rfl
    exact ⟨allocId, tag, la, _, hprov, hlive, union_readScalar_uninit hbad⟩

/-- A 0-byte memory-backed ZST place `mp` (such as a `[(); N]` local): `mp`
points at offset `0` of a live mutable 0-byte allocation (`byteSize = Size.ZERO`,
`len = 0`). -/
inductive ZstZeroMemRel
    (mach : AnnealMachine)
    (mp : Miri.Interpreter.MemPlace AnnealProv) : Prop where
  | mk
      (allocId : Miri.Memory.AllocId)
      (tag : Miri.Memory.BorTag)
      (baseAddr : UInt64)
      (localAlloc :
        Miri.Memory.LocalAllocation
          AnnealProv
          (Option Miri.TreeBorrows.BorrowTree)
          Miri.Memory.MiriMemoryKind)
      (ptr_prov : mp.ptr.provenance = some (.concrete allocId tag))
      (no_misalign : mp.misaligned = none)
      (thin_meta : mp.metadata = .none)
      (live_lookup : (allocId, localAlloc) ∈ mach.memory.live.toList)
      (base_lookup : mach.lookupBaseAddr allocId = some baseAddr)
      (ptr_addr_eq : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
      (alloc_size : localAlloc.allocation.byteSize = Miri.ABI.Size.ZERO)
      (alloc_len : localAlloc.allocation.len = 0)
      (alloc_mut : localAlloc.allocation.mutability = .Mut) :
      ZstZeroMemRel mach mp

/-- Extended local relation covering `UnionLocalRel` plus padded unions whose
active arm is a 0-byte `[(); N]` ZST array (`zstUninit` on all-uninit storage,
`zstOverlay` when `[(); N]` overwrote a scalar-initialized union), pre-allocated
uninitialized unions (`uninitIndirect`), and initialized 0-byte `[(); N]` ZST
array locals (`zstArrayIndirect`).

Model boundary notes (`R-b`, `R-c`):
* **`zstArrayIndirect` (`R-c`)**: relates only an initialized Anneal slot
  `.init (zstArrayVal N)` to a live 0-byte `ZstZeroMemRel` allocation
  `⟨.live (.indirect mp), cachedLayout⟩`, so reading that `[(); N]` local
  succeeds in both Anneal and `lean-miri` (whereas an `.uninit` `[(); N]` local
  is represented via `ofUnionLocalRel (.base (.immediate .uninit .uninit ..))`
  and faults in both).
* **Never-written (`.uninit`) union 0-byte field reads (`R-b`)**: in rustc's
  interpreter / Miri (and MiniRust's `evalValue_load_union_zstArray_field`),
  `StorageLive` allocates `S` uninitialized bytes in memory and reading an
  inhabited 0-byte ZST arm succeeds even before any write to the union. By
  contrast, Anneal's `MirSemantics.evalOperand` requires `LocalSlot.init` before
  `readProjectedValueUnionAware`, and `lean-miri`'s `annealEvalUnionField` /
  `annealEvalOperandLM2_4PaddedZst` likewise faults on `.immediate .uninit`
  (as produced by `StorageLive`). Under `uninitIndirect` (a pre-allocated
  write/copy destination where Anneal holds `.uninit` and `lean-miri` already
  holds `.indirect mp`), `lean-miri` matches real Miri by accepting a 0-byte
  inhabited field read while Anneal faults on `LocalSlot.uninit`; once a ZST arm
  initializes the union (`zstUninit`), all `S` backing bytes remain `.uninit`
  and both Anneal and `lean-miri` accept inhabited 0-byte reads. -/
inductive PaddedZstUnionLocalRel
    (mach : AnnealMachine)
    (decl : LocalDecl)
    (layouts : LayoutTable) :
    LocalSlot →
    Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout →
    Prop where
  | ofUnionLocalRel (slot : LocalSlot)
      (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
      UnionLocalRel mach decl layouts slot mls →
      PaddedZstUnionLocalRel mach decl layouts slot mls
  | uninitIndirect (S n N f_z zstFlIdx : Nat)
      (mp : Miri.Interpreter.MemPlace AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      WellTypedPaddedZstUnionTy layouts decl.ty S N f_z zstFlIdx →
      (translateTy decl.ty layouts).layout.fields = .Union n →
      PaddedZstUnionUninitMemRel mach decl.ty layouts S mp →
      PaddedZstUnionLocalRel mach decl layouts
        .uninit
        ⟨.live (.indirect mp), cachedLayout⟩
  | zstArrayIndirect (N : Nat)
      (mp : Miri.Interpreter.MemPlace AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      decl.ty.kind = .array (.tuple []) N →
      (translateTy decl.ty layouts).layout.size = Miri.ABI.Size.ZERO →
      ZstZeroMemRel mach mp →
      PaddedZstUnionLocalRel mach decl layouts
        (.init (zstArrayVal N))
        ⟨.live (.indirect mp), cachedLayout⟩
  | zstUninit (S n N f_z zstFlIdx : Nat)
      (mp : Miri.Interpreter.MemPlace AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      WellTypedPaddedZstUnionTy layouts decl.ty S N f_z zstFlIdx →
      (translateTy decl.ty layouts).layout.fields = .Union n →
      PaddedZstUnionUninitMemRel mach decl.ty layouts S mp →
      PaddedZstUnionLocalRel mach decl layouts
        (.init (.aggregate 0 (List.replicate n .unit)))
        ⟨.live (.indirect mp), cachedLayout⟩
  | zstOverlay (S n N f_z zstFlIdx : Nat) (f0Ty : Ty) (sc : MirAst.ScalarInt)
      (mp : Miri.Interpreter.MemPlace AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      WellTypedPaddedZstUnionTy layouts decl.ty S N f_z zstFlIdx →
      (translateTy decl.ty layouts).layout.fields = .Union n →
      UnionMemRel mach decl.ty layouts S f0Ty sc mp →
      PaddedZstUnionLocalRel mach decl layouts
        (.init (.aggregate 0
          (List.replicate n .unit ++
            [.aggregate 0
              (encodeRawAbstractByteVals
                (encodeLittleEndianBytes sc.bits sc.sizeBytes none ++
                  replicateUninitBytes (S - sc.sizeBytes)))])))
        ⟨.live (.indirect mp), cachedLayout⟩

/-- `FrameRelLM2_4` extended with `PaddedZstUnionLocalRel`. -/
structure FrameRelLM2_4PaddedZst
    (body : CapturedMir)
    (mach : AnnealMachine)
    (af : StackFrame)
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) : Prop where
  body_eq : mf.body = translateBody body
  location_eq : mf.location = .mir ⟨af.blockIdx, af.stmtIdx⟩
  af_locals_len : af.locals.length = body.localDecls.length
  mf_locals_size : mf.locals.size = body.localDecls.length
  locals_rel :
    ∀ (i : Nat) (decl : LocalDecl) (slot : LocalSlot)
      (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout),
      get? body.localDecls i = some decl →
      get? af.locals i = some slot →
      mf.locals[i]? = some mls →
      PaddedZstUnionLocalRel mach decl body.layouts slot mls

/-- `StateRelLM2_4` extended with `FrameRelLM2_4PaddedZst`. -/
inductive StateRelLM2_4PaddedZst
    (body : CapturedMir)
    (s : MachineState)
    (m : AnnealStepState) : Prop where
  | mk
      (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (frames_eq : m.stack.frames = #[topFrame])
      (returnContinuation_eq : topFrame.returnContinuation = .stop false)
      (returnPlace_eq :
        ∃ retLay,
          topFrame.returnPlace =
            .frameLocal 0 0 none retLay topFrame.localsIdentity)
      (frame_rel : FrameRelLM2_4PaddedZst body m.machine s.frame topFrame)
      (activeCallee_none : s.memory.activeCallee = none)
      (callStack_nil : s.memory.callStack = .nil)
      (borrows_nil : s.memory.borrows = .nil)
      (activeProtectors_nil : s.memory.activeProtectors = .nil)
      (callerLocals_nil : s.memory.callerLocals = .nil)
      (memoryAllocDisjoint : MemoryAllocDisjoint topFrame) :
      StateRelLM2_4PaddedZst body s m

/-- Every `StateRelLM2_4` embeds into `StateRelLM2_4PaddedZst`. -/
theorem StateRelLM2_4.toPaddedZst {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : StateRelLM2_4 body s m) : StateRelLM2_4PaddedZst body s m := by
  rcases h with ⟨tf, hf, hrc, hrp, hfr, hcal, hst, hbor, hprot, hcaller, hdisj⟩
  exact ⟨tf, hf, hrc, hrp,
    ⟨hfr.body_eq, hfr.location_eq, hfr.af_locals_len, hfr.mf_locals_size,
      fun i d sl ml hd hs hm => .ofUnionLocalRel sl ml (hfr.locals_rel i d sl ml hd hs hm)⟩,
    hcal, hst, hbor, hprot, hcaller, hdisj⟩

/-- Every `StateRel` embeds into `StateRelLM2_4PaddedZst`. -/
theorem StateRel.toPaddedZst {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : StateRel body s m) : StateRelLM2_4PaddedZst body s m :=
  h.toLM2_4.toPaddedZst

/-- `StepRelLM2_4` extended with `StateRelLM2_4PaddedZst`. -/
inductive StepRelLM2_4PaddedZst (body : CapturedMir) (m : AnnealStepState) :
    MirStepNode →
    Miri.Interpreter.StepResult AnnealStepState Bool →
    Prop where
  | step (s' : MachineState) (m' : AnnealStepState) :
      StateRelLM2_4PaddedZst body s' m' →
      StepRelLM2_4PaddedZst body m (MirStepNode.step s') (m', .ok true)
  | ub (m' : AnnealStepState) (msg : String) :
      StepRelLM2_4PaddedZst body m (MirStepNode.fail .ub) (m', .error (.undefinedBehavior msg))

theorem StepRelLM2_4.toPaddedZst {body : CapturedMir} {m : AnnealStepState}
    {node : MirStepNode} {res : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelLM2_4 body m node res) : StepRelLM2_4PaddedZst body m node res := by
  cases h with
  | step s' m' hst => exact .step s' m' hst.toPaddedZst
  | ub m' msg => exact .ub m' msg

/-- For any `N > 0`, `zstArrayVal N` (`[(); N]`) lacks a layout-free byte image
(`unionSlotLacksLayoutFreeImage = true`), so when its field/operand type is
statically zero-sized (`tyByteSize = some 0`), `unionActiveSlotIsZstPlaceholder`
returns `true` (`kani#5176`). -/
theorem unionActiveSlotIsZstPlaceholder_zstArrayVal
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    {N : Nat} (hN : 0 < N) {zstArrTy : Ty}
    (hsz : tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts zstArrTy) = some 0)
    (fls : List Nat := []) :
    unionActiveSlotIsZstPlaceholder localDecls layouts (some zstArrTy) (zstArrayVal N) fls = true := by
  cases N with
  | zero => exact absurd hN (Nat.lt_irrefl 0)
  | succ k =>
    have hlacks : unionSlotLacksLayoutFreeImage layouts (zstArrayVal (k + 1)) = true := rfl
    unfold unionActiveSlotIsZstPlaceholder
    rw [hlacks]
    dsimp only
    rw [hsz]
    rfl

/-- Merging `k` `.unit` slots in `mergeUnionTypedSlotsAux` leaves `(buf, bufMask)`
unchanged. -/
theorem mergeUnionTypedSlotsAux_allUnits
    (layouts : LayoutTable)
    (encodeSlot : Nat → Value → Option (List AbstractByte))
    (fallbackLayoutIdx : Nat) (hasOverlay : Bool) (unionSize : Nat) :
    ∀ (k : Nat) (flIdxs : List Nat) (buf : List AbstractByte) (bufMask : List Bool),
      mergeUnionTypedSlotsAux layouts encodeSlot fallbackLayoutIdx hasOverlay unionSize
        flIdxs (List.replicate k .unit) buf bufMask = some buf
  | 0, _, buf, _ => rfl
  | k + 1, [], buf, bufMask => by
    simp only [List.replicate_succ, mergeUnionTypedSlotsAux]
    exact mergeUnionTypedSlotsAux_allUnits layouts encodeSlot fallbackLayoutIdx hasOverlay
      unionSize k [] buf bufMask
  | k + 1, _ :: flRest, buf, bufMask => by
    simp only [List.replicate_succ, mergeUnionTypedSlotsAux]
    exact mergeUnionTypedSlotsAux_allUnits layouts encodeSlot fallbackLayoutIdx hasOverlay
      unionSize k flRest buf bufMask

/-- Encoding an `n`-slot all-`.unit` union value `.aggregate 0 (List.replicate n .unit)`
at a well-typed padded ZST union layout (`WellTypedPaddedZstUnionTy`) produces
`some (replicateUninitBytes S)` (all `S` bytes `.uninit`). -/
theorem encodeByLayoutIdxAux_union_allUnits
    {layouts : LayoutTable} {uTy : Ty} {S N f_z zstFlIdx : Nat}
    (hwt : WellTypedPaddedZstUnionTy layouts uTy S N f_z zstFlIdx)
    {n : Nat} (hfields_u : (translateTy uTy layouts).layout.fields = .Union n)
    (fuel : Nat) :
    encodeByLayoutIdxAux (fuel + 1) layouts uTy.layoutIdx
      (.aggregate 0 (List.replicate n .unit)) = some (replicateUninitBytes S) := by
  obtain ⟨_, _, tl, n', _, hk, _, _, hlookup, hfu, _, huninh, htl_sz, hfl_len, _, _,
    hgf, _, _, _, _, _, _, _⟩ := hwt.adt_spec
  have hn_eq : n' = n := by
    unfold translateTy at hfields_u
    dsimp only at hfields_u
    rw [hk, hlookup] at hfields_u
    dsimp only [translateTypeLayout, translateFieldsShape] at hfields_u
    rw [hfu] at hfields_u
    cases hfields_u
    rfl
  subst hn_eq
  have hfls_ne : ∃ a as, tl.fieldLayouts = a :: as := by
    cases h : tl.fieldLayouts with
    | nil => rw [h] at hgf; cases hgf
    | cons a as => exact ⟨a, as, rfl⟩
  obtain ⟨a, as, hfls_eq⟩ := hfls_ne
  have hsplit : ∀ k : Nat,
      splitUnionTypedAndOverlay k (List.replicate k .unit) =
        some (List.replicate k .unit, none) := by
    intro k
    induction k with
    | zero => rfl
    | succ k' ih =>
      simp only [List.replicate_succ, splitUnionTypedAndOverlay, ih]
  unfold encodeByLayoutIdxAux encodeUnionSlotsIntoBufAux
  dsimp only
  rw [hlookup]
  dsimp only
  rw [huninh, hfu]
  dsimp only
  rw [hsplit n']
  dsimp only
  rw [hfls_eq]
  dsimp only
  rw [← hfls_eq, htl_sz]
  exact mergeUnionTypedSlotsAux_allUnits layouts _ _ false S n' tl.fieldLayouts
    (replicateUninitBytes S) (replicateBool S false)

/-- Reading a zero-sized `zstLayoutData` field from any live memory-backed union
operand `⟨.indirect mp, { ty := tyId, layout := zstLayoutData }⟩` via
`annealReadImmediateLM2_2` succeeds immediately with `Immediate.uninit` without
inspecting `mp`'s allocation bytes or initialization mask. -/
theorem annealReadImmediate_zstLayoutData
    {m : AnnealStepState} (hnodup : LiveAllocsNodup m.machine)
    {mp : Miri.Interpreter.MemPlace AnnealProv} {tyId : Miri.MIR.TyId}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag} {baseAddr : UInt64}
    {la : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hlive : (allocId, la) ∈ m.machine.memory.live.toList)
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr) :
    annealReadImmediateLM2_2 ⟨.indirect mp, { ty := tyId, layout := zstLayoutData }⟩ m =
      .ok ⟨.uninit, { ty := tyId, layout := zstLayoutData }⟩ m := by
  have hfind := array_find?_of_nodup_fst hnodup hlive
  rcases la with ⟨kind, alloc⟩
  unfold annealReadImmediateLM2_2 annealReadIndirectImmediate
  dsimp only [zstLayoutData]
  rw [hprov]
  dsimp only [Option.bind, Miri.Memory.Provenance.getAllocId, get, getThe, MonadStateOf.get,
    EStateM.get, bind, EStateM.bind]
  rw [hbase, hfind]
  rfl

/-- Writing a zero-sized source operand `⟨.indirect zMp, zLay⟩`
(`zLay.layout.size = Miri.ABI.Size.ZERO`) into a memory-backed union field place
`⟨.memory mp, fLay⟩` (`fLay.layout.size = Miri.ABI.Size.ZERO`) via
`annealMemCopyOp` when `mp` points to a live mutable `S`-byte allocation (`ValidScalarBytes S`,
either `PaddedZstUnionUninitMemRel` or `UnionMemRel`) succeeds as a no-op
(`.ok () m`), leaving `m`'s stack and memory state unchanged. -/
theorem annealMemCopyOp_zero_into_union_field
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    {m : AnnealStepState} (hnodup : LiveAllocsNodup m.machine)
    {S : Nat} (hS : ValidScalarBytes S)
    {mp zMp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId srcAllocId : Miri.Memory.AllocId} {tag srcTag : Miri.Memory.BorTag}
    {baseAddr srcBaseAddr : UInt64}
    {la srcLa : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hlive : (allocId, la) ∈ m.machine.memory.live.toList)
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
    (hsz : la.allocation.byteSize = translateSizeBytes S)
    (hlen : la.allocation.len = S)
    (hmut : la.allocation.mutability = .Mut)
    (hprov_src : zMp.ptr.provenance = some (.concrete srcAllocId srcTag))
    (hlive_src : (srcAllocId, srcLa) ∈ m.machine.memory.live.toList)
    (hbase_src : m.machine.lookupBaseAddr srcAllocId = some srcBaseAddr)
    (hptr_src : zMp.ptr.offset = Miri.ABI.Size.ofBytes srcBaseAddr)
    (hlen_src : srcLa.allocation.len = srcLa.allocation.byteSize.bytes.toNat)
    {zLay fLay : Miri.Interpreter.LocalLayout}
    (hf0 : fLay.layout.size = Miri.ABI.Size.ZERO) :
    annealMemCopyOp localDecls layouts ⟨.indirect zMp, zLay⟩ ⟨.memory mp, fLay⟩ m =
      .ok () m := by
  have hfind_src := array_find?_of_nodup_fst hnodup hlive_src
  obtain ⟨destIdx, _, hidx_dst, hget_dst, _⟩ := array_findIdx?_of_nodup_fst hnodup hlive
  have hrel_src : Miri.ABI.Size.ofBytes (zMp.ptr.offset.bytes - srcBaseAddr) = Miri.ABI.Size.ZERO := by
    have hb : zMp.ptr.offset.bytes = srcBaseAddr := by rw [hptr_src]; rfl
    rw [hb, UInt64.sub_self]; rfl
  have hrel_dst : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = Miri.ABI.Size.ZERO := by
    have hb : mp.ptr.offset.bytes = baseAddr := by rw [hptr]; rfl
    rw [hb, UInt64.sub_self]; rfl
  have hlen_dst_nat : la.allocation.len = la.allocation.byteSize.bytes.toNat := by
    rw [hlen, hsz, translateSizeBytes_toNat_of_valid hS]
  have hslice_src := getBytesUnchecked_at (A := srcLa.allocation) Miri.ABI.Size.ZERO Miri.ABI.Size.ZERO
    hlen_src (Nat.zero_le _)
  have hslice_dst := getBytesUnchecked_at (A := la.allocation) Miri.ABI.Size.ZERO Miri.ABI.Size.ZERO
    hlen_dst_nat (Nat.zero_le _)
  have hnz : (la.allocation.byteSize.bytes == 0) = false := by
    rw [hsz]
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have h0 : (Miri.ABI.Size.ZERO.bytes == 0) = true := rfl
  have hforce : annealForceUnionAllocation localDecls layouts ⟨.memory mp, fLay⟩ m =
      .ok ⟨mp, fLay⟩ m := rfl
  rcases la with ⟨kind_d, alloc_d⟩
  dsimp only at hsz hlen hmut hslice_dst hnz ⊢
  unfold annealMemCopyOp
  simp only [bind, EStateM.bind, hforce, get, getThe, MonadStateOf.get, EStateM.get,
    hprov_src, hprov, Option.bind, Miri.Memory.Provenance.getAllocId,
    hbase_src, hbase, hfind_src, hidx_dst, hget_dst, hrel_src, hrel_dst, hf0,
    h0, ↓reduceIte, hslice_src, hslice_dst, hmut, bne_self_eq_false,
    Bool.false_eq_true, hnz, pure, EStateM.pure]


/-! ### Padded-ZST Projection Context (`projectField` + `projectConstantIndex`) and Vendored `ValidityVisitor` Hooks -/

/-- Reconstruct a `Miri.Interpreter.LocalLayout` from an encoded `Miri.MIR.TyId`
for the padded-ZST union extension: for `tyId ≥ 1000` (array encoding
`1000 + flIdx * 100 + elemCode`), looks up `flIdx = (tyId - 1000) / 100` in
`layouts` so `[(); N]` arms retain `.Array Size.ZERO N`; for all `tyId < 1000`,
delegates to `layoutOfEncodedTyId`. -/
def layoutOfEncodedTyIdPaddedZst (tyId : Miri.MIR.TyId) (layouts : LayoutTable) :
    Miri.Interpreter.LocalLayout :=
  if tyId ≥ 1000 then
    let flIdx := (tyId - 1000) / 100
    match layouts.lookup flIdx with
    | some tl => { ty := tyId, layout := translateTypeLayout tl }
    | none => layoutOfEncodedTyId tyId layouts
  else
    layoutOfEncodedTyId tyId layouts

/-- `annealUnionProjectionCx` extended so `[(); N]` union arms (`fieldTy ≥ 1000`)
resolve to their `.Array Size.ZERO N` `LocalLayout` in `layouts`, allowing
vendored `Miri.Interpreter.projectField` followed by vendored
`Miri.Interpreter.projectConstantIndex` (`annealProjectList`) to check bounds
and project to the `()` element layout (`arrayElemLayoutOf`). -/
def annealUnionPaddedZstProjectionCx
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (layouts : LayoutTable) (mach : AnnealMachine) (fieldTy : Miri.MIR.TyId) :
    Miri.Interpreter.ProjectionCx AnnealProv :=
  let base := annealProjectionCx frame layouts mach
  { base with
    field := fun parent idx =>
      match parent.layout.fields with
      | .Union _ => .ok (layoutOfEncodedTyIdPaddedZst fieldTy layouts)
      | _ => base.field parent idx }

/-- Project a memory-backed union local through
`[.Field j fty, .ConstantIndex offset minLen fromEnd]` using vendored
`Miri.Interpreter.projectField` and `Miri.Interpreter.projectConstantIndex`
via `annealProjectList` and `annealLiftProjectionError`. -/
def annealEvalUnionZstElem (localDecls : List LocalDecl) (layouts : LayoutTable)
    (localId j : Nat) (fty : Miri.MIR.TyId)
    (offset minLen : Nat) (fromEnd : Bool) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) := do
  let st ← get
  if st.stack.currentFrame?.isNone then
    throw (.stack .emptyStack)
  let (frame', uLay) ← annealResolveAndCacheLocalLayout localDecls layouts localId none
  let operand ← match frame'.getLocalOperand localId with
    | .ok op => pure op
    | .error (.localExpectedLive _) => throw (.undefinedBehavior "read of dead local")
    | .error e => throw (.stack e)
  match operand with
  | .immediate .uninit =>
      throw (.undefinedBehavior "field read of uninitialized union")
  | .immediate _ =>
      throw (.unsupported "union local held as an initialized immediate")
  | .indirect mp =>
      let st ← get
      match annealProjectList
          (annealUnionPaddedZstProjectionCx frame' layouts st.machine fty)
          ⟨.indirect mp, uLay⟩
          [.Field j fty, .ConstantIndex offset minLen fromEnd] with
      | .ok projected => return projected
      | .error err => throw (annealLiftProjectionError err)

/-- Project a single union field `[.Field j fty]` for a `[(); N]` ZST array arm
(`fty ≥ 1000`) through vendored `Miri.Interpreter.projectField` with
`annealUnionPaddedZstProjectionCx`, so the resulting `OpTy` retains the
`.Array Size.ZERO N` layout needed by vendored `ValidityVisitor.visit`. -/
def annealEvalUnionZstArrayField (localDecls : List LocalDecl) (layouts : LayoutTable)
    (localId j : Nat) (fty : Miri.MIR.TyId) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) := do
  let st ← get
  if st.stack.currentFrame?.isNone then
    throw (.stack .emptyStack)
  let (frame', uLay) ← annealResolveAndCacheLocalLayout localDecls layouts localId none
  let operand ← match frame'.getLocalOperand localId with
    | .ok op => pure op
    | .error (.localExpectedLive _) => throw (.undefinedBehavior "read of dead local")
    | .error e => throw (.stack e)
  match operand with
  | .immediate .uninit =>
      throw (.undefinedBehavior "field read of uninitialized union")
  | .immediate _ =>
      throw (.unsupported "union local held as an initialized immediate")
  | .indirect mp =>
      let st ← get
      match Miri.Interpreter.projectField
          (annealUnionPaddedZstProjectionCx frame' layouts st.machine fty)
          ⟨.indirect mp, uLay⟩ j with
      | .ok projected => return projected
      | .error err => throw (annealLiftProjectionError err)

/-- Operand evaluation for padded-ZST unions:
* `[.Field j fty, .ConstantIndex offset minLen false]` on a union local runs
  vendored `Miri.Interpreter.projectField` + `Miri.Interpreter.projectConstantIndex`
  via `annealEvalUnionZstElem` (`annealUnionPaddedZstProjectionCx`);
* `[.Field j fty]` on a `[(); N]` union arm (`unionZstArrayElemCount? layouts fty = some _`)
  runs vendored `Miri.Interpreter.projectField` with `annealUnionPaddedZstProjectionCx`
  so the `[(); N]` layout preserves `.Array Size.ZERO N`;
* Every other operand — including `[.Field j fty]` for scalars, `()`, and
  uninhabited types (`VoidZst`, `!`), whole unions `[]`, and all non-union locals —
  delegates unchanged to `annealEvalOperandLM2_4` (no custom uninhabited-type
  override hook). -/
def annealEvalOperandLM2_4PaddedZst
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (op : Miri.MIR.Operand)
    (expectedLayout : Option Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) :=
  match op with
  | .Copy p | .Move p =>
    if isUnionLocal localDecls layouts p.localId then
      match p.projection.toList with
      | [.Field j fty] =>
        if (unionZstArrayElemCount? layouts fty).isSome then
          annealEvalUnionZstArrayField localDecls layouts p.localId j fty
        else
          annealEvalOperandLM2_4 localDecls layouts op expectedLayout
      | [.Field j fty, .ConstantIndex offset minLen false] =>
        if (unionZstArrayElemCount? layouts fty).isSome then
          annealEvalUnionZstElem localDecls layouts p.localId j fty offset minLen false
        else
          annealEvalOperandLM2_4 localDecls layouts op expectedLayout
      | _ => annealEvalOperandLM2_4 localDecls layouts op expectedLayout
    else
      annealEvalOperandLM2_4 localDecls layouts op expectedLayout
  | _ => annealEvalOperandLM2_4 localDecls layouts op expectedLayout
where
  /-- Extract `N` when `tyId` encodes `{ kind := .array (.tuple []) N, layoutIdx := zstFlIdx }`
  whose layout entry in `layouts` is a 0-byte inhabited `.array ⟨0⟩ N`. -/
  unionZstArrayElemCount? (layouts : LayoutTable) (tyId : Miri.MIR.TyId) : Option Nat :=
    if tyId ≥ 1000 && tyId % 100 == 51 then
      let flIdx := (tyId - 1000) / 100
      match layouts.lookup flIdx with
      | some tl =>
        if !tl.isUninhabited && tl.size.bytes == 0 then
          match tl.fields with
          | .array stride cnt => if stride.bytes == 0 then some cnt else none
          | _ => none
        else none
      | none => none
    else none

/-- `annealEvalOperandLM2_4PaddedZst` is `annealEvalOperandLM2_4` on every
operand that does not read a union local. -/
theorem annealEvalOperandLM2_4PaddedZst_eq_of_not_unionLocal
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (op : Miri.MIR.Operand) (expectedLayout : Option Miri.Interpreter.LocalLayout)
    (h : ∀ p, (op = .Copy p ∨ op = .Move p) → isUnionLocal localDecls layouts p.localId = false) :
    annealEvalOperandLM2_4PaddedZst localDecls layouts op expectedLayout =
      annealEvalOperandLM2_4 localDecls layouts op expectedLayout := by
  unfold annealEvalOperandLM2_4PaddedZst
  cases op with
  | Copy p => simp [h p (.inl rfl)]
  | Move p => simp [h p (.inr rfl)]
  | _ => rfl

/-- `annealEvalOperandLM2_4PaddedZst` is `annealEvalOperandLM2_4` on a
union-local operand whose projection is neither `[Field j fty]` nor
`[Field j fty, ConstantIndex ..]`. -/
theorem annealEvalOperandLM2_4PaddedZst_eq_of_projection
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (p : Miri.MIR.Place) (expectedLayout : Option Miri.Interpreter.LocalLayout)
    (hproj : ∀ j fty, p.projection.toList ≠ [.Field j fty])
    (hidx : ∀ j fty offset minLen,
      p.projection.toList ≠ [.Field j fty, .ConstantIndex offset minLen false]) :
    annealEvalOperandLM2_4PaddedZst localDecls layouts (.Copy p) expectedLayout =
        annealEvalOperandLM2_4 localDecls layouts (.Copy p) expectedLayout ∧
      annealEvalOperandLM2_4PaddedZst localDecls layouts (.Move p) expectedLayout =
        annealEvalOperandLM2_4 localDecls layouts (.Move p) expectedLayout := by
  unfold annealEvalOperandLM2_4PaddedZst
  constructor <;>
  · dsimp only
    split
    · split
      · rename_i j fty hp; exact absurd hp (hproj j fty)
      · rename_i j fty offset minLen hp; exact absurd hp (hidx j fty offset minLen)
      · rfl
    · rfl

/-- `annealEvalOperandLM2_4PaddedZst` is definitionally equal to
`annealEvalOperandLM2_4` on every non-ZST-array `[Field j fty]` union field
read (including scalars, `()`, and uninhabited fields such as `VoidZst` or `!`,
which are instead validated by vendored `Miri.Interpreter.ValidityVisitor` in
`copyOp`). -/
theorem annealEvalOperandLM2_4PaddedZst_eq_of_non_zstArray_field
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (p : Miri.MIR.Place) (j : Nat) (fty : Miri.MIR.TyId)
    (expectedLayout : Option Miri.Interpreter.LocalLayout)
    (hproj : p.projection.toList = [.Field j fty])
    (hnotArr : (annealEvalOperandLM2_4PaddedZst.unionZstArrayElemCount? layouts fty).isSome = false) :
    annealEvalOperandLM2_4PaddedZst localDecls layouts (.Copy p) expectedLayout =
        annealEvalOperandLM2_4 localDecls layouts (.Copy p) expectedLayout ∧
      annealEvalOperandLM2_4PaddedZst localDecls layouts (.Move p) expectedLayout =
        annealEvalOperandLM2_4 localDecls layouts (.Move p) expectedLayout := by
  unfold annealEvalOperandLM2_4PaddedZst
  constructor <;>
  · dsimp only
    split
    · rw [hproj]
      dsimp only
      rw [hnotArr]
      rfl
    · rfl

/-- Classify an encoded `TyId` for vendored `Miri.Interpreter.ValidityVisitor`
on typed union/ZST/scalar copies:
* scalars (`bool`, `char`, integers, floats) classify to their primitive kinds;
* `!` (`50`) classifies as `.never` -> UB `"validation: never value"`;
* `()` (`51`) classifies as `.aggregate false false false` (fieldless single variant);
* ADTs (`100 ≤ tyId < 1000`) look up `layouts.lookup (tyId - 100)`:
  - zero-variant (`VariantsShape.empty`) and multi-variant (`VariantsShape.multiple`)
    enums classify as `.aggregate false false true` (so `.Empty` faults inside
    vendored `ValidityVisitor.visit` with `"validation: zero-variant enum value"`);
  - unions and single-variant aggregates classify as `.aggregate false false false`
    (so unions skip uninitialized padding bytes under `ctfeMode = none`, `reset = false`,
    while structs recurse on their fields);
* arrays (`tyId ≥ 1000`) classify as `.sequence ((tyId - 1000) % 100)` (so `[(); N]`
  validates element `0` as `()` without reading memory bytes, while numeric arrays
  check initialization via `readBytes`). -/
def annealUnionValidityClassify (layouts : LayoutTable) (tyId : Miri.MIR.TyId) :
    EStateM Miri.Interpreter.StepError AnnealStepState
      Miri.Interpreter.ValidityVisitor.TypeKind :=
  match tyId with
  | 1 => pure .boolean
  | 2 => pure .character
  | 10 | 11 | 12 | 13 | 14 | 15 | 20 | 21 | 22 | 23 | 24 | 25 => pure .integer
  | 30 | 31 | 32 | 33 => pure .float
  | 40 | 60 | 61 | 62 | 63 | 64 | 65 | 66 | 67 | 68 | 69
  | 70 | 71 | 72 | 73 | 74 | 75 | 76 | 77 | 78 | 79 | 80 | 81 | 82 =>
    pure (.rawPointer tyId true)
  | 42 => pure .functionPointer
  | 50 => pure .never
  | 51 => pure (.aggregate false false false)
  | n =>
    if 100 ≤ n ∧ n < 1000 then
      match layouts.lookup (n - 100) with
      | some tl =>
        match tl.variants with
        | .empty | .multiple .. => pure (.aggregate false false true)
        | .single _ => pure (.aggregate false false false)
      | none => throw (.unsupported "union validity: unknown ADT layout")
    else if n ≥ 1000 then
      pure (.sequence ((n - 1000) % 100))
    else
      throw (.unsupported "union validity: unsupported TyId")

/-- Operational inhabitedness check for `ValidityVisitor.Hooks.opsemInhabited`. -/
def annealUnionValidityInhabited (layouts : LayoutTable) (tyId : Miri.MIR.TyId) : Bool :=
  if tyId == 50 then false
  else if 100 ≤ tyId && tyId < 1000 then
    match layouts.lookup (tyId - 100) with
    | some tl =>
      !tl.isUninhabited &&
        match tl.variants with
        | .empty => false
        | _ => true
    | none => true
  else if tyId ≥ 1000 then
    match layouts.lookup ((tyId - 1000) / 100) with
    | some tl => !tl.isUninhabited
    | none => true
  else true

/-- Minimal `PlaceHooks` for `annealUnionValidityHooks`: supports zero-offset
memory projections (used when `ValidityVisitor.visit` indexes element `0` of
`[(); N]` or offset-`0` fields of single-variant wrappers). -/
def annealUnionValidityPlaceHooks :
    Miri.Interpreter.PlaceHooks AnnealProv AnnealStepState (Miri.Interpreter.OpTy AnnealProv) Unit where
  getFrame := throw (.unsupported "union validity place: getFrame")
  setFrame := fun _ => throw (.unsupported "union validity place: setFrame")
  debugAssertions := false
  frameIndex := throw (.unsupported "union validity place: frameIndex")
  resolveLayout := fun _ _ => throw (.unsupported "union validity place: resolveLayout")
  localToOp := fun _ _ => throw (.unsupported "union validity place: localToOp")
  projection := fun _ => throw (.unsupported "union validity place: projection")
  deref := fun _ _ _ => throw (.unsupported "union validity place: deref")
  checkPlaceType := fun _ _ _ => throw (.unsupported "union validity place: checkPlaceType")
  allocateStack := fun _ _ => throw (.unsupported "union validity place: allocateStack")
  writeMemoryNoValidate := fun _ _ _ =>
    throw (.unsupported "union validity place: writeMemoryNoValidate")
  afterLocalMovedToMemory := fun _ _ _ =>
    throw (.unsupported "union validity place: afterLocalMovedToMemory")
  memoryOffset := fun _ mplace amount _ metaVal =>
    if amount == Miri.ABI.Size.ZERO then
      pure { mplace with metadata := metaVal }
    else
      throw (.unsupported "union validity place: nonzero memoryOffset")
  writeLocalImmediate := fun _ _ _ _ =>
    throw (.unsupported "union validity place: writeLocalImmediate")
  enforceValidity := fun _ _ => throw (.unsupported "union validity place: enforceValidity")
  validate := fun _ _ => throw (.unsupported "union validity place: validate")

/-- `PlaceProjectionHooks` for `annealUnionValidityHooks`: resolves `[(); N]`
element `0` via `arrayElemLayoutOf`, resolves single-variant wrapper fields via
`layouts`, and maps `layoutOf` through `layoutOfEncodedTyIdPaddedZst`. -/
def annealUnionValidityProjectionHooks (layouts : LayoutTable) :
    Miri.Interpreter.PlaceProjectionHooks
      AnnealProv AnnealStepState (Miri.Interpreter.OpTy AnnealProv) Unit where
  place := annealUnionValidityPlaceHooks
  target := annealTargetDataLayout
  maxSizeOfVal := Miri.ABI.Size.ofBytes 0x7fffffffffffffff
  dynamic :=
    { target := annealTargetDataLayout
      maxSizeOfVal := Miri.ABI.Size.ofBytes 0x7fffffffffffffff
      classify := fun _ _ => throw (.unsupported "union validity dynamic: classify")
      field := fun _ _ _ => throw (.unsupported "union validity dynamic: field")
      packedAlign := fun _ _ => throw (.unsupported "union validity dynamic: packedAlign")
      vtableSizeAndAlign := fun _ _ _ =>
        throw (.unsupported "union validity dynamic: vtableSizeAndAlign") }
  dynamicFuel := 0
  isSliceOrStr := fun _ _ => pure false
  field := fun _ baseLay idx =>
    match baseLay.layout.fields with
    | .Array stride _ => pure (arrayElemLayoutOf layouts baseLay stride)
    | .Arbitrary _ _ =>
      if 100 ≤ baseLay.ty ∧ baseLay.ty < 1000 then
        match layouts.lookup (baseLay.ty - 100) with
        | some tl =>
          match get? tl.fieldLayouts idx with
          | some fIdx =>
            match layouts.lookup fIdx with
            | some fTl => pure { ty := 100 + fIdx, layout := translateTypeLayout fTl }
            | none => throw (.unsupported "union validity projection: missing field layout")
          | none => throw (.unsupported "union validity projection: field index missing")
        | none => throw (.unsupported "union validity projection: unknown aggregate layout")
      else
        throw (.unsupported "union validity projection: non-ADT arbitrary field")
    | _ => throw (.unsupported "union validity projection: field")
  variant := fun _ _ _ => throw (.unsupported "union validity projection: variant")
  packedAlign := fun _ _ => pure none
  subsliceLayout := fun _ _ _ => throw (.unsupported "union validity projection: subsliceLayout")
  layoutOf := fun _ tyId => pure (layoutOfEncodedTyIdPaddedZst tyId layouts)
  localIndex := fun _ _ => throw (.unsupported "union validity projection: localIndex")

/-- Vendored `Miri.Interpreter.ValidityVisitor.Hooks` instantiated for
`LM-2.4` padded-ZST union copies (`copyOp` / `copyOpAllowTransmute`), running
`ValidityVisitor.validatePlace` directly against the copied `OpTy` (passed as
context `src`). -/
def annealUnionValidityHooks (layouts : LayoutTable) :
    Miri.Interpreter.ValidityVisitor.Hooks
      AnnealProv AnnealStepState (Miri.Interpreter.OpTy AnnealProv) Unit Unit Unit Unit where
  target := annealRuntimeDataLayout
  projection := annealUnionValidityProjectionHooks layouts
  vtable :=
    { target := annealTargetDataLayout
      isDynamic := fun _ _ => throw (.unsupported "union validity vtable: isDynamic")
      memoryOffset := fun _ _ _ _ _ => throw (.unsupported "union validity vtable: memoryOffset")
      resolvePointer := fun _ _ => throw (.unsupported "union validity vtable: resolvePointer")
      globalVTable := fun _ _ => throw (.unsupported "union validity vtable: globalVTable")
      globalFunction := fun _ _ => throw (.unsupported "union validity vtable: globalFunction")
      predicates := fun _ _ => throw (.unsupported "union validity vtable: predicates")
      normalizePredicate := fun _ _ => throw (.unsupported "union validity vtable: normalizePredicate")
      layoutOf := fun _ _ => throw (.unsupported "union validity vtable: layoutOf")
      eraseAndAnonymize := fun _ _ _ => throw (.unsupported "union validity vtable: eraseAndAnonymize")
      ensureMonomorphicType := fun _ _ => throw (.unsupported "union validity vtable: ensureMonomorphicType")
      ensureMonomorphicDyn := fun _ _ => throw (.unsupported "union validity vtable: ensureMonomorphicDyn")
      globalSalt := fun _ => throw (.unsupported "union validity vtable: globalSalt")
      reserveVTable := fun _ _ _ _ => throw (.unsupported "union validity vtable: reserveVTable")
      globalRootPointer := fun _ _ => throw (.unsupported "union validity vtable: globalRootPointer")
      entries := fun _ _ _ => throw (.unsupported "union validity vtable: entries")
      assertVirtualInstanceMatches := fun _ _ _ _ _ =>
        throw (.unsupported "union validity vtable: assertVirtualInstanceMatches") }
  discriminant :=
    { runtimeTarget := annealRuntimeDataLayout
      discriminantLayout := fun _ _ => throw (.unsupported "union validity discr: discriminantLayout")
      tagLayout := fun _ _ => throw (.unsupported "union validity discr: tagLayout")
      discriminantValue := fun _ _ _ => throw (.unsupported "union validity discr: discriminantValue")
      variantForDiscriminant := fun _ _ _ => throw (.unsupported "union validity discr: variantForDiscriminant")
      adtVariantCount := fun _ _ => throw (.unsupported "union validity discr: adtVariantCount")
      projectRead := fun _ _ _ => throw (.unsupported "union validity discr: projectRead")
      readImmediate := fun _ op => annealReadImmediateLM2_2 op
      destLayout := fun v => v.layout
      projectWrite := fun _ _ _ => throw (.unsupported "union validity discr: projectWrite")
      writeScalar := fun _ _ _ => throw (.unsupported "union validity discr: writeScalar")
      toOp := fun src place =>
        match place.ref with
        | .memory mp => pure ⟨.indirect mp, place.layout⟩
        | .local .. => pure ⟨src.op, place.layout⟩
      scalarMayBeNull := fun _ _ => throw (.unsupported "union validity discr: scalarMayBeNull") }
  debugAssertions := false
  classify := fun _ tyId => annealUnionValidityClassify layouts tyId
  unitLayout := fun _ => pure (translateTy { kind := .tuple .nil, layoutIdx := 0 })
  typeName := fun _ _ => pure ""
  opsemInhabited := fun _ tyId => pure (annealUnionValidityInhabited layouts tyId)
  isFreeze := fun _ _ => pure true
  fieldPath := fun _ _ _ _ => pure .enumTag
  variantPath := fun _ _ variant => pure (.variant (toString variant))
  projectBox := fun _ _ => throw (.unsupported "union validity: projectBox")
  toOp := fun src place =>
    match place.ref with
    | .memory mp => pure ⟨.indirect mp, place.layout⟩
    | .local .. => pure ⟨src.op, place.layout⟩
  readImmediate := fun src place _ => do
    let op : Miri.Interpreter.OpTy AnnealProv :=
      match place.ref with
      | .memory mp => ⟨.indirect mp, place.layout⟩
      | .local .. => ⟨src.op, place.layout⟩
    annealReadImmediateLM2_2 op
  clearProvenance := fun _ _ => pure ()
  writeNoValidate := fun _ _ _ => throw (.unsupported "union validity: writeNoValidate")
  sizeAndAlign := fun _ mpt => pure (some (mpt.layout.layout.size, mpt.layout.layout.align.abi))
  ptrToPlace := fun _ _ => throw (.unsupported "union validity: ptrToPlace")
  metadataTail := fun _ _ => throw (.unsupported "union validity: metadataTail")
  checkPointerAccess := fun _ _ _ => throw (.unsupported "union validity: checkPointerAccess")
  checkPointerAlign := fun _ _ _ => throw (.unsupported "union validity: checkPointerAlign")
  checkPointerAlignResult := fun _ _ _ => throw (.unsupported "union validity: checkPointerAlignResult")
  scalarMayBeNull := fun _ sc =>
    match sc.tryToScalarInt with
    | .ok (.integer integer) => pure integer.isNull
    | .ok _ => throw (.invalidProgram "absolute Miri pointer erased its address")
    | .error err => throw (Miri.Interpreter.ScalarOps.scalarError err)
  retagPointer := fun _ _ _ => pure none
  ctfePointerLookup := fun _ _ _ => throw (.unsupported "union validity: ctfePointerLookup")
  inMutableMemory := fun _ _ => pure true
  readBytes := fun _ mpt sz _ => do
    let st ← get
    match annealCheckIndirectInitialized st.machine mpt.mplace sz with
    | .ok () => pure ()
    | .error err => throw err
  clearBytesProvenance := fun _ _ _ => pure ()
  beginPadding := fun _ _ _ => pure none
  writePadding := fun _ _ _ => pure ()
  cachedUnionRanges := fun _ _ m => m
  withGhostValidation := fun m => m

/-- Validate a copied operand `src` using vendored
`Miri.Interpreter.ValidityVisitor.validatePlace` (with `recursive := false`,
`reset := false`, matching rustc Miri's `copy_op` -> `validate_operand`). -/
def annealValidateOpLM2_4PaddedZst (layouts : LayoutTable)
    (src : Miri.Interpreter.OpTy AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState Unit := do
  let place : Miri.Interpreter.RuntimePlace AnnealProv ←
    match src.op with
    | .indirect mp => pure ⟨.memory mp, src.layout⟩
    | .immediate _ =>
      let st ← get
      match st.stack.currentFrame? with
      | some frame => pure ⟨.local 0 0 none frame.localsIdentity, src.layout⟩
      | none => throw (.stack .emptyStack)
  Miri.Interpreter.ValidityVisitor.validatePlace
    (annealUnionValidityHooks layouts) src 4 place false false

/-- Additive aggregate hooks extending `annealAggregateHooksLM2_4` so zero-sized
array operands (`src.layout.layout.size.bytes == 0`, such as `[(); N]` in
`_u = PU { z: op_zst }`) succeed as a 0-byte copy into indirect union field
destinations instead of failing `annealReadImmediateLM2_2`'s `.Arbitrary #[] #[]` check. -/
def annealAggregateHooksLM2_4PaddedZst
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    Miri.Interpreter.AggregateHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealAggregateHooksLM2_4 localDecls layouts
  { base with
    evalOperand := fun _ op known => do
      let opTy ← annealEvalOperandLM2_4PaddedZst localDecls layouts op known
      if opTy.layout.layout.size.bytes == 0 then
        return ⟨.immediate .uninit, opTy.layout⟩
      else
        let imm ← annealReadImmediateLM2_2 opTy
        return ⟨.immediate imm.imm, imm.layout⟩
    evalOperandAt := fun _ _ op known => do
      let opTy ← annealEvalOperandLM2_4PaddedZst localDecls layouts op known
      if opTy.layout.layout.size.bytes == 0 then
        return ⟨.immediate .uninit, opTy.layout⟩
      else
        let imm ← annealReadImmediateLM2_2 opTy
        return ⟨.immediate imm.imm, imm.layout⟩
    copyOpNoValidate := fun c src dest b => do
      if src.layout.layout.size.bytes == 0 && dest.layout.layout.size.bytes == 0 then
        match dest.1 with
        | .memory mp =>
          let st ← get
          match mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
          | none => throw (.undefinedBehavior "zero-sized aggregate write without provenance")
          | some allocId =>
            match st.machine.memory.live.find? (fun (id, _) => id == allocId) with
            | none => throw (.undefinedBehavior "zero-sized aggregate write to dead allocation")
            | some (_, _) => pure ()
        | .local .. =>
          base.copyOpNoValidate c src dest b
      else
        base.copyOpNoValidate c src dest b }

/-- Additive rvalue hooks extending `annealRvalueHooksLM2_4` with:
1. `annealEvalOperandLM2_4PaddedZst` (vendored `projectField` +
   `projectConstantIndex` on `[(); N]` union arms; no custom uninhabited override);
2. `copyOp` / `copyOpAllowTransmute` validating `src` via vendored
   `Miri.Interpreter.ValidityVisitor.validatePlace` (`annealValidateOpLM2_4PaddedZst`)
   before copying, matching rustc Miri's `copy_op`;
3. `annealAggregateHooksLM2_4PaddedZst` for 0-byte `[(); N]` aggregate fields. -/
def annealRvalueHooksLM2_4PaddedZst
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    Miri.Interpreter.RvalueHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealRvalueHooksLM2_4 localDecls layouts
  { base with
    evalOperand := fun _ op known =>
      annealEvalOperandLM2_4PaddedZst localDecls layouts op known
    evalOperandAt := fun _ _ op known =>
      annealEvalOperandLM2_4PaddedZst localDecls layouts op known
    evalPlaceToOp := fun _ p known =>
      annealEvalOperandLM2_4PaddedZst localDecls layouts (.Copy p) known
    copyOp := fun _ src dest => do
      annealValidateOpLM2_4PaddedZst layouts src
      if usesMemCopy src then annealMemCopyOp localDecls layouts src dest
      else do
        let imm ← annealReadImmediateLM2_2 src
        annealWriteImmediateLM2_2 imm.imm dest
    copyOpAllowTransmute := fun _ src dest => do
      annealValidateOpLM2_4PaddedZst layouts src
      if usesMemCopy src then annealMemCopyOp localDecls layouts src dest
      else do
        let imm ← annealReadImmediateLM2_2 src
        annealWriteImmediateLM2_2 imm.imm dest
    writeAggregate := fun c k os d =>
      Miri.Interpreter.writeAggregate
        (annealAggregateHooksLM2_4PaddedZst localDecls layouts) c k os d }

/-- Additive step hooks extending `annealStepHooksLM2_4` with
`annealRvalueHooksLM2_4PaddedZst` for padded `[(); N]` union ZST array arms
(`kani#5176` / `kani#5159`). -/
def annealStepHooksLM2_4PaddedZst
    (localDecls : List LocalDecl := .nil) (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.StepHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      AnnealMachine
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealStepHooksLM2_4 localDecls layouts
  { base with
    assign := fun choice place rvalue state =>
      if lm24Assign localDecls layouts place rvalue then
        Miri.Interpreter.runRvalue
          (Miri.Interpreter.evalRvalueIntoPlace
            (annealRvalueHooksLM2_4PaddedZst localDecls layouts) choice rvalue place)
          state
      else
        base.assign choice place rvalue state }

/-- Whenever `annealEvalOperandLM2_4PaddedZst` agrees with `annealEvalOperandLM2_4`
and vendored `ValidityVisitor.validatePlace` accepts the evaluated source operand
without modifying state (`annealValidateOpLM2_4PaddedZst layouts src st = .ok () st`),
`StepHooks.assign` on `.Use op` under `annealStepHooksLM2_4PaddedZst` produces the
exact same result as `annealStepHooksLM2_4` (`G4`). -/
theorem annealStepHooksLM2_4PaddedZst_assign_use_eq
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (choice : Unit) (place : Miri.MIR.Place) (op : Miri.MIR.Operand)
    (retag : Miri.MIR.WithRetag) (state : AnnealStepState)
    (hop : ∀ known,
      annealEvalOperandLM2_4PaddedZst localDecls layouts op known =
        annealEvalOperandLM2_4 localDecls layouts op known)
    (hvalid : ∀ dest st1 src st2,
      (annealRvalueHooksLM2_4 localDecls layouts).evalPlace choice place true state = .ok dest st1 →
      annealEvalOperandLM2_4 localDecls layouts op (some dest.layout) st1 = .ok src st2 →
      annealValidateOpLM2_4PaddedZst layouts src st2 = .ok () st2) :
    (annealStepHooksLM2_4PaddedZst localDecls layouts).assign choice place (.Use op retag) state =
      (annealStepHooksLM2_4 localDecls layouts).assign choice place (.Use op retag) state := by
  unfold annealStepHooksLM2_4PaddedZst annealStepHooksLM2_4
  dsimp only
  split
  · unfold Miri.Interpreter.runRvalue Miri.Interpreter.evalRvalueIntoPlace
      annealRvalueHooksLM2_4PaddedZst annealRvalueHooksLM2_4
    dsimp only [annealRvalueHooksLM2_2, annealRvalueHooks]
    cases hp : annealEvalPlaceLM2_4 localDecls layouts place state with
    | error e st1 => simp [bind, EStateM.bind, hp]
    | ok dest st1 =>
      simp only [bind, EStateM.bind, hp]
      rw [hop]
      cases ho : annealEvalOperandLM2_4 localDecls layouts op (some dest.layout) st1 with
      | error e st2 => rfl
      | ok src st2 =>
        have hv := hvalid dest st1 src st2 hp ho
        simp only [hv]
  · rfl

@[simp] theorem annealStepHooksLM2_4PaddedZst_storageLive_eq
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    (annealStepHooksLM2_4PaddedZst localDecls layouts).storageLive =
      (annealStepHooksLM2_4 localDecls layouts).storageLive := rfl

@[simp] theorem annealStepHooksLM2_4PaddedZst_storageDead_eq
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    (annealStepHooksLM2_4PaddedZst localDecls layouts).storageDead =
      (annealStepHooksLM2_4 localDecls layouts).storageDead := rfl

end LeanMiriSpec.Correspondence
