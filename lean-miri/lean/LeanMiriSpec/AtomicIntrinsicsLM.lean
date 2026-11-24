/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Miri.Interpreter.IntrinsicAtomic
import Miri.Interpreter.AtomicMachine
import Miri.Interpreter.ExecutionIntrinsic
import LeanMiriSpec.Correspondence.TreeBorrowsRel

/-!
# Episode 2 Atomic Intrinsics Semantics (`LeanMiriSpec` Authority)

Canonical single-threaded wiring of vendored Miri atomic intrinsics
(`Miri.Interpreter.AtomicMachine.bind`, proved definitionally equal to
`Miri.Interpreter.ExecutionIntrinsic.Atomic.{access, dispatcher}`), universal
structural theorems (`allowDataRaces`, ordering conversion rejections,
`WeakCasPolicy` laws, vendored `BorrowTree.performBorrowAccessRange` bridge),
kernel-checked (`decide +kernel` / `rfl`, zero `native_decide`) single-threaded
execution witnesses across all Rust atomic intrinsics and fault modes
(misaligned, non-power-of-two, oversized `u128`, out-of-bounds, read-only
allocation `Mutability.Not`, and Tree Borrows `Frozen` mode sensitivity), and
the executable cross-root observation runner `lmAtomicObserve`
(`caseIdx ∈ 0..27`).

Strict import isolation: NEVER imports `MiniRustSpec.*` or `Anneal.*`
(enforced by the trailing `run_cmd` audit).
-/

namespace LeanMiriSpec.AtomicIntrinsicsLM

set_option Elab.async false
set_option linter.unusedSimpArgs false

open Miri.ABI
open Miri.Memory
open Miri.MIR
open Miri.Interpreter

/-! ## §0. Canonical `x86_64` Layout, Type IDs, & Helper Constructors -/

/-- Little-endian 64-bit `x86_64` `RuntimeTargetDataLayout` (overriding
`RuntimeTargetDataLayout.default`'s big-endian base and 32-bit i64 align). -/
def x86_64RuntimeLayout : RuntimeTargetDataLayout :=
  { RuntimeTargetDataLayout.default with
    base := ⟨.little, .w64⟩
    i64Align := Align.EIGHT
    i128Align := ⟨4⟩ }

/-- Canonical synthetic `MIR.TyId` constants for the atomic intrinsic harness. -/
def tyBool : Miri.MIR.TyId := 0
def tyU8 : Miri.MIR.TyId := 1
def tyU16 : Miri.MIR.TyId := 2
def tyU32 : Miri.MIR.TyId := 3
def tyU64 : Miri.MIR.TyId := 4
def tyUsize : Miri.MIR.TyId := 5
def tyI8 : Miri.MIR.TyId := 6
def tyI16 : Miri.MIR.TyId := 7
def tyI32 : Miri.MIR.TyId := 8
def tyI64 : Miri.MIR.TyId := 9
def tyIsize : Miri.MIR.TyId := 10
def tyU128 : Miri.MIR.TyId := 11
def tyPtr : Miri.MIR.TyId := 12
def tyNonPow2_3 : Miri.MIR.TyId := 13
def tyUnit : Miri.MIR.TyId := 14
def tyOrdering : Miri.MIR.TyId := 15

/-- Build a primitive scalar `LocalLayout` (`TyAndLayout MIR.TyId`). -/
def mkScalarLayout (ty : Miri.MIR.TyId) (widthBytes : UInt64) (align : Align)
    (prim : Primitive) (validRange : WrappingRange) : LocalLayout :=
  { ty := ty
    layout := {
      fields := .Primitive
      variants := .Single 0
      backendRepr := .Scalar (.Initialized (value := prim) (validRange := validRange))
      largestNiche := none
      uninhabited := false
      align := ⟨align⟩
      size := Size.ofBytes widthBytes
      maxReprAlign := none
      unadjustedAbiAlign := align
      reprC := false
      randomizationSeed := 0 } }

def layoutBool : LocalLayout :=
  mkScalarLayout tyBool 1 Align.ONE (.Int .I8 false) ⟨0, BitVec.ofNat 128 1⟩

def layoutU8 : LocalLayout :=
  mkScalarLayout tyU8 1 Align.ONE (.Int .I8 false) ⟨0, BitVec.ofNat 128 0xFF⟩

def layoutU16 : LocalLayout :=
  mkScalarLayout tyU16 2 ⟨1⟩ (.Int .I16 false) ⟨0, BitVec.ofNat 128 0xFFFF⟩

def layoutU32 : LocalLayout :=
  mkScalarLayout tyU32 4 ⟨2⟩ (.Int .I32 false) ⟨0, BitVec.ofNat 128 0xFFFFFFFF⟩

def layoutU64 : LocalLayout :=
  mkScalarLayout tyU64 8 Align.EIGHT (.Int .I64 false) ⟨0, BitVec.ofNat 128 0xFFFFFFFFFFFFFFFF⟩

def layoutUsize : LocalLayout :=
  mkScalarLayout tyUsize 8 Align.EIGHT (.Int .I64 false) ⟨0, BitVec.ofNat 128 0xFFFFFFFFFFFFFFFF⟩

def layoutI8 : LocalLayout :=
  mkScalarLayout tyI8 1 Align.ONE (.Int .I8 true) ⟨0, BitVec.ofNat 128 0xFF⟩

def layoutI16 : LocalLayout :=
  mkScalarLayout tyI16 2 ⟨1⟩ (.Int .I16 true) ⟨0, BitVec.ofNat 128 0xFFFF⟩

def layoutI32 : LocalLayout :=
  mkScalarLayout tyI32 4 ⟨2⟩ (.Int .I32 true) ⟨0, BitVec.ofNat 128 0xFFFFFFFF⟩

def layoutI64 : LocalLayout :=
  mkScalarLayout tyI64 8 Align.EIGHT (.Int .I64 true) ⟨0, BitVec.ofNat 128 0xFFFFFFFFFFFFFFFF⟩

def layoutIsize : LocalLayout :=
  mkScalarLayout tyIsize 8 Align.EIGHT (.Int .I64 true) ⟨0, BitVec.ofNat 128 0xFFFFFFFFFFFFFFFF⟩

def layoutU128 : LocalLayout :=
  mkScalarLayout tyU128 16 ⟨4⟩ (.Int .I128 false) ⟨0, BitVec.allOnes 128⟩

def layoutPtr : LocalLayout :=
  mkScalarLayout tyPtr 8 Align.EIGHT (.Pointer AddressSpace.ZERO)
    ⟨0, BitVec.ofNat 128 0xFFFFFFFFFFFFFFFF⟩

def layoutOrdering : LocalLayout :=
  mkScalarLayout tyOrdering 1 Align.ONE (.Int .I8 true) ⟨0, BitVec.ofNat 128 0xFF⟩

def layoutUnit : LocalLayout :=
  { ty := tyUnit
    layout := {
      fields := .Arbitrary #[] #[]
      variants := .Single 0
      backendRepr := .Memory (sized := true)
      largestNiche := none
      uninhabited := false
      align := ⟨Align.ONE⟩
      size := Size.ZERO
      maxReprAlign := none
      unadjustedAbiAlign := Align.ONE
      reprC := false
      randomizationSeed := 0 } }

/-- 3-byte non-power-of-two layout used to verify `Align.fromBytes` rejection
in `IntrinsicAtomic.access`. -/
def layoutNonPow2_3 : LocalLayout :=
  { ty := tyNonPow2_3
    layout := {
      fields := .Primitive
      variants := .Single 0
      backendRepr := .Memory (sized := true)
      largestNiche := none
      uninhabited := false
      align := ⟨Align.ONE⟩
      size := Size.ofBytes 3
      maxReprAlign := none
      unadjustedAbiAlign := Align.ONE
      reprC := false
      randomizationSeed := 0 } }

/-- `(T, bool)` `ScalarPair` destination layout for `atomic_cxchg` /
`atomic_cxchgweak`, with second field (`bool`) at `bOffset = T.size`. -/
def mkCasDestLayout (valLayout : LocalLayout) : LocalLayout :=
  let aScalar : Miri.ABI.Scalar :=
    match valLayout.layout.backendRepr with
    | .Scalar s => s
    | _ => .Initialized (value := .Int .I32 false) (validRange := ⟨0, BitVec.ofNat 128 0xFFFFFFFF⟩)
  let bScalar : Miri.ABI.Scalar :=
    .Initialized (value := .Int .I8 false) (validRange := ⟨0, BitVec.ofNat 128 1⟩)
  let bOff := valLayout.layout.size
  let totalSize := Size.ofBytes (bOff.bytes + bOff.bytes)
  { ty := 100 + valLayout.ty
    layout := {
      fields := .Arbitrary #[Size.ZERO, bOff] #[0, 1]
      variants := .Single 0
      backendRepr := .ScalarPair (a := aScalar) (b := bScalar) (bOffset := bOff)
      largestNiche := none
      uninhabited := false
      align := valLayout.layout.align
      size := totalSize
      maxReprAlign := none
      unadjustedAbiAlign := valLayout.layout.align.abi
      reprC := false
      randomizationSeed := 0 } }

/-- Unsigned scalar layout by width in bytes (`1, 2, 4, 8, 16`, or `3` for
non-power-of-two). -/
def unsignedLayoutOfWidth : Nat → LocalLayout
  | 1 => layoutU8
  | 2 => layoutU16
  | 3 => layoutNonPow2_3
  | 4 => layoutU32
  | 8 => layoutU64
  | 16 => layoutU128
  | _ => layoutU32

/-- Construct a `Miri.Memory.Scalar Provenance` for an integer of `widthBytes`
bytes from its unsigned bit pattern `bits`. -/
def mkIntScalar (widthBytes : Nat) (bits : Nat) : Miri.Memory.Scalar Provenance :=
  match widthBytes with
  | 1 => .fromScalarInt (ScalarInt.ofUInt8 (UInt8.ofNat bits))
  | 2 => .fromScalarInt (ScalarInt.ofUInt16 (UInt16.ofNat bits))
  | 4 => .fromScalarInt (ScalarInt.ofUInt32 (UInt32.ofNat bits))
  | 8 => .fromScalarInt (ScalarInt.ofUInt64 (UInt64.ofNat bits))
  | 16 => .fromScalarInt (ScalarInt.ofUInt128 (BitVec.ofNat 128 bits))
  | _ => .fromScalarInt (ScalarInt.ofUInt32 (UInt32.ofNat bits))

/-- Construct an immediate `OpTy Provenance` carrying an integer scalar. -/
def mkIntOp (layout : LocalLayout) (bits : Nat) : OpTy Provenance :=
  ⟨.immediate (.scalar (mkIntScalar layout.layout.size.bytes.toNat bits)), layout⟩

/-- Little-endian byte encoding of `bits` in `width` bytes (pure recursion for
fast kernel reduction under `decide +kernel`). -/
def natToLeBytesList : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, v => UInt8.ofNat (v % 256) :: natToLeBytesList k (v / 256)

def natToLeBytes (width : Nat) (v : Nat) : Array UInt8 :=
  (natToLeBytesList width v).toArray

/-- Pad `bytes` with trailing zero bytes up to `allocSize`. -/
def padZeroBytes (bytes : Array UInt8) (allocSize : Nat) : Array UInt8 :=
  if bytes.size < allocSize then
    bytes ++ Array.replicate (allocSize - bytes.size) (0 : UInt8)
  else
    bytes

/-! ## §1. Canonical `AtomicMachine.bind` & `ExecutionIntrinsic.Atomic` Wiring -/

/-- Access-tag permission configuration for the single-cell Tree Borrows check. -/
inductive CellTagMode where
  | rootUnique
  | frozenChild
  | reservedChild
  deriving DecidableEq, Repr

/-- Pure, kernel-reducible Tree Borrows permission check for local unprotected
accesses on `CellTagMode` (`write = false` is a read, `write = true` is a write).
Bridged to vendored `Miri.TreeBorrows.BorrowTree.performBorrowAccessRange` by
`atomic_tb_check_bridges_vendored_performBorrowAccessRange`. -/
def cellTagModeAllowsAccess (tagMode : CellTagMode) (write : Bool) : Bool :=
  match tagMode, write with
  | .frozenChild, true => false
  | _, _ => true

/-- Map `CellTagMode` to the corresponding `TreeBorrowPerm` child permission:
- `.rootUnique` ↦ `.unique`
- `.reservedChild` ↦ `.reservedFrz false`
- `.frozenChild` ↦ `.frozen`. -/
def cellTagModeToPerm : CellTagMode → Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowPerm
  | .rootUnique => .unique
  | .reservedChild => .reservedFrz false
  | .frozenChild => .frozen

/-- Map `PlaceMachine.memoryAccess`'s `write : Bool` flag to `TreeBorrowAccessKind`. -/
def writeBoolToAccessKind : Bool → Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowAccessKind
  | false => .read
  | true => .write

/-- Per-machine user payload combining `MemoryExtras.Registry Unit` with the
single-cell Tree Borrows configuration (`treeBorrows`, `tagMode`). -/
structure LmPayload where
  registry : MemoryExtras.Registry Unit
  treeBorrows : Bool := false
  tagMode : CellTagMode := .rootUnique

abbrev LmUser := ValidityMachine.UserState LmPayload
abbrev AtomicState := AtomicMachine.State Unit LmPayload
abbrev AtomicM := AtomicMachine.M Unit LmPayload

/-- Explicit per-call compiler/choice leaves for `IntrinsicAtomic.eval`. -/
structure LmAtomicChoice where
  ord0 : Miri.Concurrency.AtomicOrdering := .SeqCst
  ord1 : Miri.Concurrency.AtomicOrdering := .SeqCst
  ord2 : Miri.Concurrency.AtomicOrdering := .SeqCst
  pointeeLayout : LocalLayout := layoutU32
  weakSuccess : Bool := true
  loadRank : Nat := 0
  deriving DecidableEq, Repr

/-- Canonical allocation IDs and base addresses for the single-cell + dest
harness (`0x1000` and `0x2000` are 4096-byte aligned). -/
def cellAllocId : AllocId := ⟨1, by decide⟩
def destAllocId : AllocId := ⟨2, by decide⟩
def cellBaseAddr : UInt64 := 0x1000
def destBaseAddr : UInt64 := 0x2000

/-- Canonical Tree Borrows tags: root tag `1`, child tag `2` (for `Frozen` /
`Reserved` / active reborrows). -/
def rootTag : BorTag := BorTag.one
def childTag : BorTag := ⟨2, by decide⟩

/-- `MemoryExtras.Hooks` nested inside `ValidityMachine.UserState`. -/
def lmExtrasHooks : MemoryExtras.Hooks Unit LmUser Unit where
  get := fun u => u.payload.payload.registry
  put := fun u reg =>
    { u with payload := { u.payload with payload := { u.payload.payload with registry := reg } } }
  onAccess := fun _ _ => pure ()
  weakError := fun e => .invalidProgram s!"weak memory error: {reprStr e}"

/-- `PointerMachine.Hooks` using cached base addresses and 64-bit arithmetic. -/
def lmPointerHooks : PointerMachine.Hooks Unit (ValidityMachine.Control LmPayload) where
  arithmetic := ⟨Size.ofBytes 8⟩
  externalAddress := fun _ _ => throw (.unsupported "externalAddress unused in managed mode")
  ensureTreeExtra := fun _ => pure ()
  diagnosticIntToPtr := pure ()
  strictIntToPtr := .undefinedBehavior "strict int-to-ptr"
  classifyAddressError := fun e => .undefinedBehavior s!"address error: {reprStr e}"

/-- Classify `MemoryOperandError` preserving UB vs. program-invariant errors. -/
def lmMemoryError : MemoryOperandError → StepError
  | .pointerAccess e => .undefinedBehavior s!"pointer access: {reprStr e}"
  | .allocation e@(.invalidUninitBytes _) => .undefinedBehavior s!"allocation: {reprStr e}"
  | .allocation e@(.outOfBounds _ _) => .undefinedBehavior s!"allocation: {reprStr e}"
  | .allocation .readOnlyAllocation => .undefinedBehavior "readOnlyAllocation"
  | .allocation e@(.readPointerAsInt _) => .undefinedBehavior s!"allocation: {reprStr e}"
  | .allocation e@(.readPartialPointer _) => .undefinedBehavior s!"allocation: {reprStr e}"
  | .invalidUninitBytes => .undefinedBehavior "InvalidUninitBytes"
  | e => .invalidProgram s!"memory operand error: {reprStr e}"

/-- Address resolution callback matching `TypedMemoryProviders.resolvePointer`. -/
def lmResolvePointer
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree Unit)
    (pointer : Pointer (Option Provenance)) (size : Int) :
    PlaceMachine.MachineM Unit LmUser (Except UInt64 (ResolvedPointer ProvenanceExtra)) := do
  if size < -(2^63 : Int) || size >= 2^63 then
    throw (.invalidProgram "memory address resolution access size exceeds i64")
  let some provenance := pointer.provenance | return .error pointer.offset.bytes
  let lookup : Miri.Memory.AllocAddresses.AddressLookupHooks := {
    sizeOf := fun id => (memory.getAllocInfo id).toOption.map (·.size)
    isLive := fun id => some (memory.isAllocLive id) }
  let result := (← get).user.addresses.ptrGetAlloc (Pointer.new provenance pointer.offset)
    (Int64.ofInt size) lookup lmPointerHooks.arithmetic
  match result with
  | .error error => throw (lmPointerHooks.classifyAddressError error)
  | .ok none => pure (.error pointer.offset.bytes)
  | .ok (some (id, offset)) =>
    let extra := match provenance with
      | .concrete _ tag => ProvenanceExtra.concrete tag
      | .wildcard => ProvenanceExtra.wildcard
    pure (.ok ⟨id, offset, extra⟩)

def lmGlobalAllocHooks :
    GlobalAllocationHooks Provenance Miri.TreeBorrows.BorrowTree Unit
      (PlaceMachine.AccessState Unit LmUser) where
  synchronizeMemory := fun memory st => { st with machine := { st.machine with memory } }
  evaluateStaticInitializer := fun memory st _ => ⟨memory, st, .error "no static initializers"⟩
  beforeAccessGlobal := fun memory st _ _ _ _ => ⟨memory, st, .ok ()⟩
  adjustGlobalAllocation := fun memory st _ _ => ⟨memory, st, .error "no global allocations"⟩

/-- Total, kernel-reducible Tree Borrows permission check wired into
`PlaceMachine.AccessConfig.diagnostic` (invoked by `PlaceMachine.memoryAccess`
on every read and write). Bridged to vendored
`Miri.TreeBorrows.BorrowTree.performBorrowAccessRange` by
`atomic_tb_check_bridges_vendored_performBorrowAccessRange`. -/
def lmTreeBorrowsDiagnostic (write : Bool) (allocId : AllocId) (_range : AllocRange) :
    PlaceMachine.MachineM Unit LmUser Unit := fun m =>
  if m.user.payload.payload.treeBorrows && allocId == cellAllocId &&
      !cellTagModeAllowsAccess m.user.payload.payload.tagMode write then
    EStateM.Result.error (.undefinedBehavior "Tree Borrows: write through Frozen tag") m
  else
    EStateM.Result.ok () m

def lmAccessConfig : PlaceMachine.AccessConfig Unit LmUser where
  runtime := x86_64RuntimeLayout
  ghostMode := false
  globalKind := none
  globalHooks := lmGlobalAllocHooks
  dynamicLayout := fun memory st _ => ⟨memory, st, .ok none⟩
  resolvePointer := lmResolvePointer
  beforeAllocationAccess := fun _ => pure ()
  diagnostic := lmTreeBorrowsDiagnostic
  weakMemoryWrite := fun _ _ => pure ()
  syncAccess := fun _ _ _ => pure ()
  retainTouched := fun machine _ => machine
  memoryError := lmMemoryError

def lmAllocationConfig : PlaceMachine.AllocationConfig Unit LmUser where
  maximumObjectSize := Size.ofBytes (UInt64.ofNat (2^47))
  zeroedStorage := fun sz _ => some (Array.replicate sz.bytes.toNat (0 : UInt8))
  nativeStorage := none
  nativeDrop := none
  diagnostic := fun _ _ _ => pure ()
  allocationTail := fun _ _ _ => pure ()
  adjustRootAddress := fun _ _ => throw (.unsupported "stack allocation unused in atomic harness")

def lmCompilerHooks : PlaceMachine.CompilerHooks Unit LmUser LmAtomicChoice where
  debugAssertions := false
  layout := fun _ _ => throw (.unsupported "local layout unused")
  validationInProgress := ValidityMachine.validationInProgress
  projection := fun _ => throw (.unsupported "projection unused")
  deref := fun _ _ _ => throw (.unsupported "place deref unused")
  checkPlaceType := fun _ _ _ => pure ()
  memoryOffset := fun _ _ _ _ _ => throw (.unsupported "memoryOffset unused")
  debugAbiCheck := fun _ _ => pure ()
  localSpan := fun _ _ => throw (.unsupported "localSpan unused")
  enforceValidity := fun _ _ => pure false
  validate := fun _ _ => pure ()
  willValidateMemory := fun _ => false

def lmClassifyTy (ty : Miri.MIR.TyId) : RvalueM AtomicState ScalarTypeClass :=
  if ty == tyBool then pure .boolean
  else if ty == tyU8 then pure (.integer .u8)
  else if ty == tyU16 then pure (.integer .u16)
  else if ty == tyU32 then pure (.integer .u32)
  else if ty == tyU64 then pure (.integer .u64)
  else if ty == tyUsize then pure (.integer .usize)
  else if ty == tyI8 then pure (.integer .i8)
  else if ty == tyI16 then pure (.integer .i16)
  else if ty == tyI32 then pure (.integer .i32)
  else if ty == tyI64 then pure (.integer .i64)
  else if ty == tyIsize then pure (.integer .isize)
  else if ty == tyU128 then pure (.integer .u128)
  else if ty == tyPtr then pure .pointer
  else throw (.invalidProgram s!"unclassified atomic TyId {ty}")

def lmScalarOpsHooks : ScalarOpsHooks Provenance AtomicState LmAtomicChoice where
  classify := fun _ ty => lmClassifyTy ty
  boolLayout := fun _ => pure layoutBool
  orderingLayout := fun _ => pure layoutOrdering
  overflowLayout := fun _ l => pure l
  metadataLayout := fun _ _ => pure layoutUsize
  unitLayout := fun _ => pure layoutUnit
  floatBinary := fun _ _ _ _ => throw (.unsupported "float binary op unused in atomics")
  pointerBinary := fun _ _ _ _ => throw (.unsupported "pointer binary op unused in integer atomics")
  floatUnary := fun _ _ _ => throw (.unsupported "float unary op unused in atomics")
  derefValidity := fun _ _ => pure ()

def lmClassifyDispatchError : Miri.Concurrency.AtomicDispatchError → StepError
  | .validation .race | .syncClock .race => .undefinedBehavior "DataRace"
  | e => .invalidProgram s!"atomic dispatch error: {reprStr e}"

def lmClassifyGlobalError (e : Miri.Concurrency.GlobalStateError) : StepError :=
  .invalidProgram s!"atomic global state error: {reprStr e}"

def lmOrderingConst (c : LmAtomicChoice) : Nat → AtomicM Miri.Concurrency.AtomicOrdering
  | 0 => pure c.ord0
  | 1 => pure c.ord1
  | 2 => pure c.ord2
  | idx => throw (.invalidProgram s!"unexpected ordering generic index {idx}")

def lmVolatileConst (_c : LmAtomicChoice) (_idx : Nat) : AtomicM Unit := pure ()

def lmDerefPointer (access : PlaceMachine.AccessConfig Unit LmUser)
    (choice : LmAtomicChoice) (op : OpTy Provenance) : AtomicM (RuntimePlace Provenance) := do
  let imm ← PlaceMachine.readImmediate access op
  let sc ← match imm.imm.toScalar with
    | .ok s => pure s
    | .error e => throw (ScalarOps.immediateError e)
  let ptr ← match sc.toPointer x86_64RuntimeLayout.base with
    | .ok p => pure p
    | .error e => throw (ScalarOps.scalarError e)
  pure ⟨.memory ⟨ptr, .none, none⟩, choice.pointeeLayout⟩

def lmAtomicAccessLeaves (weakPolicy : WeakCasPolicy) :
    ExecutionIntrinsic.Atomic.AccessLeaves Provenance AtomicState LmAtomicChoice
      (RuntimePlace Provenance) where
  loadChoiceRank := fun c _ => pure c.loadRank
  weakPolicy := weakPolicy
  weakSuccessChoice := fun c => pure c.weakSuccess
  diagnostic := fun _ _ => pure ()
  classifyDispatchError := lmClassifyDispatchError
  classifyGlobalError := lmClassifyGlobalError

/-- Base dictionary supplied to `AtomicMachine.bind`; every physical, race, TB,
alignment, resolution, and mutability hook is replaced canonically by `bind`. -/
def lmBaseAtomicHooks (weakPolicy : WeakCasPolicy)
    (accessBound : PlaceMachine.AccessConfig Unit LmUser) :
    IntrinsicAtomicHooks Provenance AtomicState LmAtomicChoice (RuntimePlace Provenance) where
  target := x86_64RuntimeLayout.base
  getGlobal := fun _ => none
  setGlobal := fun s _ => s
  threads := fun s => s.machine.threads
  getAtomic := fun _ _ => .error (.invalidProgram "unbound getAtomic")
  setAtomic := fun _ _ => throw (.invalidProgram "unbound setAtomic")
  placeLayout := RuntimePlace.layout
  placePointer := fun _ => .error (.invalidProgram "unbound placePointer")
  physicalRead := fun _ _ => throw (.invalidProgram "unbound physicalRead")
  physicalWrite := fun _ _ _ => throw (.invalidProgram "unbound physicalWrite")
  ghostRead := fun _ _ => pure none
  checkPointerAlign := fun _ _ _ => pure ()
  resolveAllocation := fun _ _ => throw (.invalidProgram "unbound resolveAllocation")
  mutability := fun _ _ => throw (.invalidProgram "unbound mutability")
  scalarOps := lmScalarOpsHooks
  loadChoiceRank := fun c _ => pure c.loadRank
  weakPolicy := weakPolicy
  weakSuccessChoice := fun c => pure c.weakSuccess
  diagnostic := fun _ _ => pure ()
  classifyDispatchError := lmClassifyDispatchError
  classifyGlobalError := lmClassifyGlobalError
  orderingConst := lmOrderingConst
  volatileConst := lmVolatileConst
  derefPointer := lmDerefPointer accessBound
  readImmediate := fun _ _ => throw (.invalidProgram "unbound readImmediate")
  writeImmediate := fun _ _ _ => throw (.invalidProgram "unbound writeImmediate")
  returnToBlock := fun _ _ => pure ()

/-- Canonical `IntrinsicAtomicHooks` constructed via `AtomicMachine.bind`. -/
def lmAtomicHooksBind (weakPolicy : WeakCasPolicy := .neverFail) :
    IntrinsicAtomicHooks Provenance AtomicState LmAtomicChoice (RuntimePlace Provenance) :=
  let accessBound := MemoryExtras.bindAccess lmExtrasHooks lmAccessConfig
  AtomicMachine.bind
    (lmBaseAtomicHooks weakPolicy accessBound)
    lmAccessConfig lmAllocationConfig lmCompilerHooks lmPointerHooks lmExtrasHooks

/-- Direct construction via `ExecutionIntrinsic.Atomic.{access, dispatcher}`. -/
def lmAtomicHooksExec (weakPolicy : WeakCasPolicy := .neverFail) :
    IntrinsicAtomicHooks Provenance AtomicState LmAtomicChoice (RuntimePlace Provenance) :=
  let accessBound := MemoryExtras.bindAccess lmExtrasHooks lmAccessConfig
  let places := PlaceMachine.placeHooks accessBound lmAllocationConfig lmCompilerHooks
  let physical := ExecutionIntrinsic.Atomic.access
    (lmAtomicAccessLeaves weakPolicy) lmScalarOpsHooks lmAccessConfig places
    lmPointerHooks lmExtrasHooks
  ExecutionIntrinsic.Atomic.dispatcher physical
    lmOrderingConst lmVolatileConst (lmDerefPointer accessBound)
    accessBound places (fun _ _ => pure ())

/-- **Canonical wiring agreement**: `AtomicMachine.bind` produces the exact same
`IntrinsicAtomicHooks` dictionary as `ExecutionIntrinsic.Atomic.{access, dispatcher}`. -/
theorem lmAtomicHooks_bind_eq_exec (weakPolicy : WeakCasPolicy) :
    lmAtomicHooksBind weakPolicy = lmAtomicHooksExec weakPolicy := rfl

/-! ## §2. Single-Cell State Builder (`mkSingleCellState`) & Borrow-Tree Bridge -/

private def isExceptOk {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

private theorem fallbackAlloc_isOk :
    isExceptOk (Allocation.fromBytes (Prov := Provenance)
      #[0, 0, 0, 0, 0, 0, 0, 0] Align.EIGHT .Mut) = true := by
  decide +kernel

/-- Fallback valid 8-byte allocation (used only in provably unreachable `error`
branches of `Allocation.fromBytes`, avoiding `Inhabited`/`unreachable!`). -/
def fallbackAlloc : Allocation Provenance Unit :=
  match h : Allocation.fromBytes (Prov := Provenance)
      #[0, 0, 0, 0, 0, 0, 0, 0] Align.EIGHT .Mut with
  | .ok a => a
  | .error _ => False.elim (Bool.noConfusion (h ▸ fallbackAlloc_isOk))

/-- Construct an `Allocation Provenance BorrowTree` from bytes, align,
mutability, and Tree Borrows extra. -/
def mkCellAllocation (bytes : Array UInt8) (align : Align) (mutability : Miri.Memory.Mutability)
    (tree : Miri.TreeBorrows.BorrowTree) : Allocation Provenance Miri.TreeBorrows.BorrowTree :=
  match Allocation.fromBytes (Prov := Provenance) bytes align mutability with
  | .ok a => a.withExtra tree
  | .error _ => fallbackAlloc.withExtra tree

/-- **Vendored `BorrowTree.performBorrowAccessRange` bridge theorem**:
for every `tagMode : CellTagMode` (`.rootUnique` ↦ `.unique`, `.reservedChild` ↦
`.reservedFrz false`, `.frozenChild` ↦ `.frozen`) and every access direction
`write : Bool` (`false` ↦ `.read`, `true` ↦ `.write`), unmodified vendored
`Miri.TreeBorrows.BorrowTree.performBorrowAccessRange` on the two-node tree
`hooksTwoNodeTree (cellTagModeToPerm tagMode)` at `.localAccess` with
`isProtected = false` completes (`.status = .Completed`) **if and only if**
`cellTagModeAllowsAccess tagMode write = true`, which in turn holds **if and
only if** `lmTreeBorrowsDiagnostic` (wired into `PlaceMachine.AccessConfig.diagnostic`)
succeeds on `cellAllocId` when `treeBorrows = true`. -/
theorem atomic_tb_check_bridges_vendored_performBorrowAccessRange
    (tagMode : CellTagMode) (write : Bool) :
    (((LeanMiriSpec.Correspondence.hooksTwoNodeTree (cellTagModeToPerm tagMode)).performBorrowAccessRange
        (.concrete (LeanMiriSpec.Correspondence.hooksAccessTag .localAccess))
        Size.ZERO (Size.ofBytes 8)
        (LeanMiriSpec.Correspondence.annealAccessKindToMiri (writeBoolToAccessKind write))
        (LeanMiriSpec.Correspondence.hooksForChildProtected false).protectedTags
        .VisitChildrenOfAccessed).status = .Completed ↔
      cellTagModeAllowsAccess tagMode write = true) ∧
    (∀ (m : PlaceMachine.Machine Unit LmUser) (range : AllocRange),
      m.user.payload.payload.treeBorrows = true →
      m.user.payload.payload.tagMode = tagMode →
      (lmTreeBorrowsDiagnostic write cellAllocId range m = EStateM.Result.ok () m ↔
        cellTagModeAllowsAccess tagMode write = true)) := by
  constructor
  · have hSim :=
      (LeanMiriSpec.Correspondence.borrowTree_performBorrowAccessRange_simulation
        (writeBoolToAccessKind write) .localAccess (cellTagModeToPerm tagMode) false).1
    rw [hSim]
    cases tagMode <;> cases write <;> decide +kernel
  · intro m range hTb hMode
    have hId : (cellAllocId == cellAllocId) = true := by decide +kernel
    unfold lmTreeBorrowsDiagnostic
    simp only [hTb, hMode, hId, Bool.true_and]
    cases tagMode <;> cases write <;> simp [cellTagModeAllowsAccess]

def accessTagOfMode : CellTagMode → BorTag
  | .rootUnique => rootTag
  | .frozenChild => childTag
  | .reservedChild => childTag

/-- Build a single-threaded `VClockAlloc` via `GlobalState.activeThreadState`
matching `PlaceMachine.initStackExtra`. -/
def mkSingleThreadRaceAlloc (global : Miri.Concurrency.GlobalState)
    (threads : Miri.Concurrency.ThreadManager) (allocSize : Size) :
    Option Miri.Concurrency.VClockAlloc :=
  match global.activeThreadState threads with
  | .ok (index, clocks) =>
    let length := Miri.Concurrency.ByteSize.ofU64 allocSize.bytes.toNat
      (by have h := UInt64.toNat_lt allocSize.bytes; omega)
    some (Miri.Concurrency.VClockAlloc.newAllocation length (clocks.clock.index index) index)
  | .error _ => none

/-- Configuration for `mkSingleCellState`. -/
structure SingleCellConfig where
  widthBytes : Nat := 4
  initBits : Nat := 0
  allocSize : Nat := 8
  allocAlign : Align := Align.EIGHT
  mutability : Miri.Memory.Mutability := .Mut
  ptrOffset : Nat := 0
  treeBorrows : Bool := false
  tagMode : CellTagMode := .rootUnique
  useDataRaceFastPath : Bool := false
  alignmentCheck : ValidityMachine.AlignmentCheck := .Int
  deriving DecidableEq, Repr

/-- Build a canonical `AtomicState` containing:
- `cellAllocId` (`1`) at `0x1000` holding `initBits` (little-endian, zero-padded
  to `allocSize`), with `allocAlign`, `mutability`, and a pure root `BorrowTree`;
- `destAllocId` (`2`) at `0x2000` (16-byte, 8-aligned, mutable) for writing
  return values of `IntrinsicAtomic.eval`;
- `LmPayload` carrying `MemoryExtras.Registry` entries for both live allocations
  plus `(cfg.treeBorrows, cfg.tagMode)` for `lmTreeBorrowsDiagnostic` (bridged
  to vendored `BorrowTree.performBorrowAccessRange` by
  `atomic_tb_check_bridges_vendored_performBorrowAccessRange`);
- `borrowTracker = none` so `PlaceMachine.memoryAccess` stays 100% kernel-reducible
  under `decide +kernel` without hitting `partial` `repeatM.impl`;
- `dataRace = some (GlobalState.initial false false)` (single-threaded fast path
  with `raceDetecting = false`) iff `cfg.useDataRaceFastPath = true`. -/
def mkSingleCellState (cfg : SingleCellConfig) : AtomicState :=
  let cellBytes := padZeroBytes (natToLeBytes cfg.widthBytes cfg.initBits) cfg.allocSize
  let cellSize := Size.ofBytes (UInt64.ofNat cellBytes.size)
  let cellTree := Miri.TreeBorrows.BorrowTree.new rootTag cellSize
  let cellAlloc := mkCellAllocation cellBytes cfg.allocAlign cfg.mutability cellTree
  let destTree := Miri.TreeBorrows.BorrowTree.new rootTag (Size.ofBytes 16)
  let destAlloc := mkCellAllocation (Array.replicate 16 (0 : UInt8)) Align.EIGHT .Mut destTree
  let mem : MemoryState Provenance Miri.TreeBorrows.BorrowTree Unit :=
    { (MemoryState.empty : MemoryState Provenance Miri.TreeBorrows.BorrowTree Unit) with
      nextAllocId := 3
      live := #[(cellAllocId, ⟨.stack, cellAlloc⟩), (destAllocId, ⟨.stack, destAlloc⟩)] }
  let threads := Miri.Concurrency.ThreadManager.initial true
  let dataRace : Option Miri.Concurrency.GlobalState :=
    if cfg.useDataRaceFastPath then some (Miri.Concurrency.GlobalState.initial false false)
    else none
  let raceAllocs : Array (AllocId × Miri.Concurrency.VClockAlloc) :=
    match dataRace with
    | none => #[]
    | some g =>
      let cellRace := match mkSingleThreadRaceAlloc g threads cellSize with
        | some a => #[(cellAllocId, a)]
        | none => #[]
      let destRace := match mkSingleThreadRaceAlloc g threads (Size.ofBytes 16) with
        | some a => #[(destAllocId, a)]
        | none => #[]
      cellRace ++ destRace
  let addresses : Miri.Memory.AllocAddresses.GlobalAddressState := {
    intToPtrMap := #[]
    baseAddr := #[⟨cellAllocId, cellBaseAddr⟩, ⟨destAllocId, destBaseAddr⟩]
    exposed := #[]
    provenanceMode := .default
    addressMode := .managed
    generation := none
    preparedNativeBytes := #[] }
  let registry : MemoryExtras.Registry Unit := {
    allocations := #[(cellAllocId, ⟨none, #[]⟩), (destAllocId, ⟨none, #[]⟩)] }
  let payload : LmPayload := {
    registry := registry
    treeBorrows := cfg.treeBorrows
    tagMode := cfg.tagMode }
  let user : LmUser := {
    addresses := addresses
    payload := {
      payload := payload
      validation := .No
      alignment := cfg.alignmentCheck
      ghost := false
      unionDataRanges := #[] }
    symbolicAlignment := #[] }
  { stack := Stack.empty
    machine := {
      memory := mem
      borrowTracker := none
      dataRace := dataRace
      threads := threads
      raceAllocations := raceAllocs
      allocationSpans := #[]
      user := user } }

/-- Pointer `OpTy` pointing into `cellAllocId` at `cellBaseAddr + ptrOffset`
carrying `accessTagOfMode cfg.tagMode`. -/
def mkCellPtrOp (cfg : SingleCellConfig) : OpTy Provenance :=
  let ptr := Pointer.new (Provenance.concrete cellAllocId (accessTagOfMode cfg.tagMode))
    (Size.ofBytes (cellBaseAddr + UInt64.ofNat cfg.ptrOffset))
  ⟨.immediate (.scalar (Miri.Memory.Scalar.fromPointer x86_64RuntimeLayout.base ptr)), layoutPtr⟩

/-- Destination `RuntimePlace` pointing to `destAllocId` (`0x2000`) with
`rootTag` and the supplied `destLayout`. -/
def mkDestPlace (destLayout : LocalLayout) : RuntimePlace Provenance :=
  let ptr := Pointer.new (some (Provenance.concrete destAllocId rootTag))
    (Size.ofBytes destBaseAddr)
  ⟨.memory ⟨ptr, .none, none⟩, destLayout⟩

/-- Read an unsigned `widthBytes`-byte scalar at `offset` inside `allocId` from
`state.machine.memory`. -/
def readAllocBits (state : AtomicState) (allocId : AllocId) (offset widthBytes : Nat) :
    Option Nat := do
  let (_, loc) ← state.machine.memory.live.find? (fun entry => entry.1 == allocId)
  let sz := Size.ofBytes (UInt64.ofNat widthBytes)
  let sc ← (loc.allocation.readScalar x86_64RuntimeLayout.base
    ⟨Size.ofBytes (UInt64.ofNat offset), sz⟩ false).toOption
  let bits ← (sc.toBits sz).toOption
  pure bits.toNat

/-- Read a 1-byte `bool` scalar at `offset` inside `allocId` from
`state.machine.memory`. -/
def readAllocBool (state : AtomicState) (allocId : AllocId) (offset : Nat) : Option Bool := do
  let (_, loc) ← state.machine.memory.live.find? (fun entry => entry.1 == allocId)
  let sc ← (loc.allocation.readScalar x86_64RuntimeLayout.base
    ⟨Size.ofBytes (UInt64.ofNat offset), Size.ofBytes 1⟩ false).toOption
  sc.toBool.toOption

/-! ## §3. Universal & Structural Theorems (Zero `sorry`, Zero `native_decide`) -/

/-! ### §3.1 `IntrinsicAtomic.allowDataRaces` Bracket & Error-Restoration Laws -/

/-- When no vector-clock global state is installed, `allowDataRaces` runs
`action` directly without overhead. -/
theorem allowDataRaces_none {P S C V A : Type}
    (h : AtomicAccessHooks P S C V) (action : RvalueM S A) (s : S)
    (hNone : h.getGlobal s = none) :
    IntrinsicAtomic.allowDataRaces h action s = action s := by
  unfold IntrinsicAtomic.allowDataRaces
  rw [hNone]

/-- Nested `allowDataRaces` is rejected immediately with `invalidProgram`
without executing `action` or mutating state. -/
theorem allowDataRaces_rejects_nested {P S C V A : Type}
    (h : AtomicAccessHooks P S C V) (action : RvalueM S A) (s : S)
    (g : Miri.Concurrency.GlobalState)
    (hSome : h.getGlobal s = some g) (hNested : g.ongoingActionDataRaceFree = true) :
    IntrinsicAtomic.allowDataRaces h action s =
      .error (.invalidProgram "cannot nest allow_data_races") s := by
  unfold IntrinsicAtomic.allowDataRaces
  rw [hSome]
  simp only [hNested, ↓reduceIte]

/-- On normal completion of `action`, `allowDataRaces` sets
`ongoingActionDataRaceFree = true` for `action` and restores it to `false` on
return. -/
theorem allowDataRaces_ok_restores {P S C V A : Type}
    (h : AtomicAccessHooks P S C V) (action : RvalueM S A) (s s' : S)
    (res : A) (g g' : Miri.Concurrency.GlobalState)
    (hSome : h.getGlobal s = some g) (hNotNested : g.ongoingActionDataRaceFree = false)
    (hAct : action (h.setGlobal s (Miri.Concurrency.GlobalState.withDataRaceFreeAction g true)) =
      EStateM.Result.ok res s')
    (hPost : h.getGlobal s' = some g') (hFlag : g'.ongoingActionDataRaceFree = true) :
    IntrinsicAtomic.allowDataRaces h action s =
      EStateM.Result.ok res
        (h.setGlobal s' (Miri.Concurrency.GlobalState.withDataRaceFreeAction g' false)) := by
  unfold IntrinsicAtomic.allowDataRaces
  rw [hSome]
  simp only [hNotNested, Bool.false_eq_true, ↓reduceIte]
  have hMatch :
      (match action (h.setGlobal s (Miri.Concurrency.GlobalState.withDataRaceFreeAction g true)) with
       | EStateM.Result.ok result state =>
         match (match h.getGlobal state with
           | none => Except.error (StepError.invalidProgram "atomic action removed vector-clock handler")
           | some global =>
             if !global.ongoingActionDataRaceFree then
               Except.error (StepError.invalidProgram "atomic data-race-free action flag was cleared")
             else Except.ok (h.setGlobal state (Miri.Concurrency.GlobalState.withDataRaceFreeAction global false))) with
         | Except.ok state => EStateM.Result.ok result state
         | Except.error error => EStateM.Result.error error state
       | EStateM.Result.error error state =>
         match (match h.getGlobal state with
           | none => Except.error (StepError.invalidProgram "atomic action removed vector-clock handler")
           | some global =>
             if !global.ongoingActionDataRaceFree then
               Except.error (StepError.invalidProgram "atomic data-race-free action flag was cleared")
             else Except.ok (h.setGlobal state (Miri.Concurrency.GlobalState.withDataRaceFreeAction global false))) with
         | Except.ok state => EStateM.Result.error error state
         | Except.error restoreError => EStateM.Result.error restoreError state) =
      EStateM.Result.ok res
        (h.setGlobal s' (Miri.Concurrency.GlobalState.withDataRaceFreeAction g' false)) := by
    rw [hAct]
    simp only [hPost, hFlag, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact hMatch

/-- On error completion of `action`, `allowDataRaces` still restores
`ongoingActionDataRaceFree = false` while propagating the original error. -/
theorem allowDataRaces_error_restores {P S C V A : Type}
    (h : AtomicAccessHooks P S C V) (action : RvalueM S A) (s s' : S)
    (err : StepError) (g g' : Miri.Concurrency.GlobalState)
    (hSome : h.getGlobal s = some g) (hNotNested : g.ongoingActionDataRaceFree = false)
    (hAct : action (h.setGlobal s (Miri.Concurrency.GlobalState.withDataRaceFreeAction g true)) =
      EStateM.Result.error err s')
    (hPost : h.getGlobal s' = some g') (hFlag : g'.ongoingActionDataRaceFree = true) :
    IntrinsicAtomic.allowDataRaces h action s =
      EStateM.Result.error err
        (h.setGlobal s' (Miri.Concurrency.GlobalState.withDataRaceFreeAction g' false)) := by
  unfold IntrinsicAtomic.allowDataRaces
  rw [hSome]
  simp only [hNotNested, Bool.false_eq_true, ↓reduceIte]
  have hMatch :
      (match action (h.setGlobal s (Miri.Concurrency.GlobalState.withDataRaceFreeAction g true)) with
       | EStateM.Result.ok result state =>
         match (match h.getGlobal state with
           | none => Except.error (StepError.invalidProgram "atomic action removed vector-clock handler")
           | some global =>
             if !global.ongoingActionDataRaceFree then
               Except.error (StepError.invalidProgram "atomic data-race-free action flag was cleared")
             else Except.ok (h.setGlobal state (Miri.Concurrency.GlobalState.withDataRaceFreeAction global false))) with
         | Except.ok state => EStateM.Result.ok result state
         | Except.error error => EStateM.Result.error error state
       | EStateM.Result.error error state =>
         match (match h.getGlobal state with
           | none => Except.error (StepError.invalidProgram "atomic action removed vector-clock handler")
           | some global =>
             if !global.ongoingActionDataRaceFree then
               Except.error (StepError.invalidProgram "atomic data-race-free action flag was cleared")
             else Except.ok (h.setGlobal state (Miri.Concurrency.GlobalState.withDataRaceFreeAction global false))) with
         | Except.ok state => EStateM.Result.error error state
         | Except.error restoreError => EStateM.Result.error restoreError state) =
      EStateM.Result.error err
        (h.setGlobal s' (Miri.Concurrency.GlobalState.withDataRaceFreeAction g' false)) := by
    rw [hAct]
    simp only [hPost, hFlag, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact hMatch

/-- The restored global state from `withDataRaceFreeAction g' false` has
`ongoingActionDataRaceFree = false` (and `withDataRaceFreeAction g true` sets it
to `true`). -/
theorem withDataRaceFreeAction_flag (g : Miri.Concurrency.GlobalState) (b : Bool) :
    (Miri.Concurrency.GlobalState.withDataRaceFreeAction g b).ongoingActionDataRaceFree = b :=
  rfl

/-! ### §3.2 Ordering Conversion & Rejection Theorems -/

/-- `AtomicReadOrd.ofOrdering` accepts `Relaxed`/`Acquire`/`SeqCst` and rejects
`Release`/`AcqRel`. -/
theorem atomicReadOrd_ofOrdering_laws :
    Miri.Concurrency.AtomicReadOrd.ofOrdering .Relaxed = .ok .Relaxed ∧
    Miri.Concurrency.AtomicReadOrd.ofOrdering .Acquire = .ok .Acquire ∧
    Miri.Concurrency.AtomicReadOrd.ofOrdering .SeqCst = .ok .SeqCst ∧
    Miri.Concurrency.AtomicReadOrd.ofOrdering .Release = .error (.invalidRead .Release) ∧
    Miri.Concurrency.AtomicReadOrd.ofOrdering .AcqRel = .error (.invalidRead .AcqRel) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `AtomicWriteOrd.ofOrdering` accepts `Relaxed`/`Release`/`SeqCst` and rejects
`Acquire`/`AcqRel`. -/
theorem atomicWriteOrd_ofOrdering_laws :
    Miri.Concurrency.AtomicWriteOrd.ofOrdering .Relaxed = .ok .Relaxed ∧
    Miri.Concurrency.AtomicWriteOrd.ofOrdering .Release = .ok .Release ∧
    Miri.Concurrency.AtomicWriteOrd.ofOrdering .SeqCst = .ok .SeqCst ∧
    Miri.Concurrency.AtomicWriteOrd.ofOrdering .Acquire = .error (.invalidWrite .Acquire) ∧
    Miri.Concurrency.AtomicWriteOrd.ofOrdering .AcqRel = .error (.invalidWrite .AcqRel) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `prepareAtomicFence` rejects `Relaxed` for multi-thread fences, accepts
`Acquire`/`Release`/`AcqRel`/`SeqCst`, and treats every single-thread fence as
a NOP (`.ok none`). -/
theorem prepareAtomicFence_laws (ord : Miri.Concurrency.AtomicOrdering) :
    Miri.Concurrency.prepareAtomicFence .Relaxed false = .error (.invalidFence .Relaxed) ∧
    Miri.Concurrency.prepareAtomicFence .Acquire false = .ok (some .Acquire) ∧
    Miri.Concurrency.prepareAtomicFence .Release false = .ok (some .Release) ∧
    Miri.Concurrency.prepareAtomicFence .AcqRel false = .ok (some .AcqRel) ∧
    Miri.Concurrency.prepareAtomicFence .SeqCst false = .ok (some .SeqCst) ∧
    Miri.Concurrency.prepareAtomicFence ord true = .ok none :=
  ⟨rfl, rfl, rfl, rfl, rfl, by cases ord <;> rfl⟩

/-- `IntrinsicAtomic.load` rejects `Release` and `AcqRel` for every hook
dictionary and state before touching memory. -/
theorem load_rejects_invalid_ordering {P S C V : Type}
    (h : AtomicAccessHooks P S C V) (choice : C) (place : V) (s : S) :
    IntrinsicAtomic.load h choice place .Release s =
      .error (.invalidProgram
        s!"{repr (Miri.Concurrency.AtomicOrderingError.invalidRead .Release)}") s ∧
    IntrinsicAtomic.load h choice place .AcqRel s =
      .error (.invalidProgram
        s!"{repr (Miri.Concurrency.AtomicOrderingError.invalidRead .AcqRel)}") s :=
  ⟨rfl, rfl⟩

/-- `IntrinsicAtomic.store` rejects `Acquire` and `AcqRel` for every hook
dictionary, scalar value, and state before touching memory. -/
theorem store_rejects_invalid_ordering {P S C V : Type}
    (h : AtomicAccessHooks P S C V) (choice : C) (place : V)
    (sc : Miri.Memory.Scalar P) (lay : LocalLayout) (s : S) :
    IntrinsicAtomic.store h choice place ⟨.scalar sc, lay⟩ .Acquire s =
      .error (.invalidProgram
        s!"{repr (Miri.Concurrency.AtomicOrderingError.invalidWrite .Acquire)}") s ∧
    IntrinsicAtomic.store h choice place ⟨.scalar sc, lay⟩ .AcqRel s =
      .error (.invalidProgram
        s!"{repr (Miri.Concurrency.AtomicOrderingError.invalidWrite .AcqRel)}") s :=
  ⟨rfl, rfl⟩

/-- `IntrinsicAtomic.compareExchange` rejects failure orderings `Release` and
`AcqRel` for every hook dictionary, scalar `newValue`, success ordering, and
state before touching memory. -/
theorem compareExchange_rejects_invalid_failure_ordering {P S C V : Type} [PointerProvenance P]
    (h : AtomicAccessHooks P S C V) (choice : C) (place : V)
    (expected : RvalueImmTy P) (newSc : Miri.Memory.Scalar P) (lay : LocalLayout)
    (weak : Bool) (success : Miri.Concurrency.AtomicOrdering) (s : S) :
    IntrinsicAtomic.compareExchange h choice place expected ⟨.scalar newSc, lay⟩
        weak success .Release s =
      .error (.invalidProgram
        s!"{repr (Miri.Concurrency.AtomicOrderingError.invalidRead .Release)}") s ∧
    IntrinsicAtomic.compareExchange h choice place expected ⟨.scalar newSc, lay⟩
        weak success .AcqRel s =
      .error (.invalidProgram
        s!"{repr (Miri.Concurrency.AtomicOrderingError.invalidRead .AcqRel)}") s :=
  ⟨rfl, rfl⟩

/-- `IntrinsicAtomic.fence` rejects `Relaxed` when `singlethread = false` and is
an unconditional state-preserving NOP when `singlethread = true`. -/
theorem fence_rejects_relaxed_and_singlethread_noop {P S C V : Type}
    (h : AtomicAccessHooks P S C V) (ord : Miri.Concurrency.AtomicOrdering) (s : S) :
    IntrinsicAtomic.fence h .Relaxed false s =
      .error (.invalidProgram
        s!"{repr (Miri.Concurrency.AtomicOrderingError.invalidFence .Relaxed)}") s ∧
    IntrinsicAtomic.fence h ord true s = .ok () s :=
  ⟨rfl, by cases ord <;> rfl⟩

/-! ### §3.3 Universal `rmwValue` & `fence` Laws (ALL Hook Dictionaries & States) -/

/-- **Universal `rmwValue` laws**: `atomic_xchg` (`.swap`) returns `right` touching no hook or
state; every `.mir op negate` is exactly `ScalarOps.binary op` followed by `ScalarOps.unary .Not`
iff `negate`; hence `atomic_nand` (`.mir .BitAnd true`) is `Not ∘ BitAnd`. -/
theorem rmwValue_universal_laws {P S C V : Type} [PointerProvenance P]
    (h : AtomicAccessHooks P S C V) (choice : C) (left right : RvalueImmTy P) :
    (∀ s : S, IntrinsicAtomic.rmwValue h choice .swap left right s = .ok right s) ∧
    (∀ (op : Miri.MIR.BinOp) (negate : Bool),
      IntrinsicAtomic.rmwValue h choice (.mir op negate) left right =
        (ScalarOps.binary h.scalarOps choice op left right >>= fun value =>
          if negate then ScalarOps.unary h.scalarOps choice .Not value else pure value)) ∧
    IntrinsicAtomic.rmwValue h choice (.mir .BitAnd true) left right =
      (ScalarOps.binary h.scalarOps choice .BitAnd left right >>=
        ScalarOps.unary h.scalarOps choice .Not) :=
  ⟨fun _ => rfl, fun _ _ => rfl, rfl⟩

/-- **Fence without a vector-clock backend** (`getGlobal = fun _ => none`): for every hook
dictionary, state, and non-`Relaxed` ordering, a multi-thread fence is a state-preserving NOP. -/
theorem fence_without_global_noop {P S C V : Type} (h : AtomicAccessHooks P S C V)
    (ord : Miri.Concurrency.AtomicOrdering) (s : S) (hOrd : ord ≠ .Relaxed) :
    IntrinsicAtomic.fence ({ h with getGlobal := fun _ => none } : AtomicAccessHooks P S C V)
      ord false s = .ok () s := by
  cases ord <;> first | rfl | exact absurd rfl hOrd

/-! ## §4. Executable Observation Type (`LmAtomicObs`) & `IntrinsicAtomic.eval` Runner -/

/-- Authority-typed observation returned by `lmAtomicObserve`. -/
inductive LmAtomicObs : Type where
  | okStore (postBits : Nat)
  | okScalar (retBits : Nat) (postBits : Nat)
  | okCas (retBits : Nat) (succeeded : Bool) (postBits : Nat)
  | ub
  | invalidOrUnsupported
  deriving DecidableEq, Repr

/-- Classify a `StepError` from `IntrinsicAtomic.eval` into `LmAtomicObs`. -/
def classifyStepError : StepError → LmAtomicObs
  | .undefinedBehavior _ => .ub
  | _ => .invalidOrUnsupported

/-- Execute an `atomic_load` through `IntrinsicAtomic.eval` over
`AtomicMachine.bind` and observe `(retBits, postBits)`. -/
def runEvalLoad (cfg : SingleCellConfig) (valLayout : LocalLayout)
    (ord : Miri.Concurrency.AtomicOrdering := .SeqCst) : LmAtomicObs :=
  let st := mkSingleCellState cfg
  let choice : LmAtomicChoice := { ord1 := ord, pointeeLayout := valLayout }
  let dest := mkDestPlace valLayout
  let width := valLayout.layout.size.bytes.toNat
  match IntrinsicAtomic.eval (lmAtomicHooksBind .neverFail) choice
      "atomic_load" #[mkCellPtrOp cfg] dest none st with
  | .error e _ => classifyStepError e
  | .ok false _ => .invalidOrUnsupported
  | .ok true st' =>
    match readAllocBits st' destAllocId 0 width, readAllocBits st' cellAllocId 0 width with
    | some retBits, some postBits => .okScalar retBits postBits
    | _, _ => .invalidOrUnsupported

/-- Execute an `atomic_store` through `IntrinsicAtomic.eval` over
`AtomicMachine.bind` and observe `postBits`. -/
def runEvalStore (cfg : SingleCellConfig) (valLayout : LocalLayout) (valBits : Nat)
    (ord : Miri.Concurrency.AtomicOrdering := .SeqCst) : LmAtomicObs :=
  let st := mkSingleCellState cfg
  let choice : LmAtomicChoice := { ord1 := ord, pointeeLayout := valLayout }
  let dest := mkDestPlace layoutUnit
  let width := valLayout.layout.size.bytes.toNat
  match IntrinsicAtomic.eval (lmAtomicHooksBind .neverFail) choice
      "atomic_store" #[mkCellPtrOp cfg, mkIntOp valLayout valBits] dest none st with
  | .error e _ => classifyStepError e
  | .ok false _ => .invalidOrUnsupported
  | .ok true st' =>
    match readAllocBits st' cellAllocId 0 width with
    | some postBits => .okStore postBits
    | none => .invalidOrUnsupported

/-- Execute a store-then-load round-trip through `IntrinsicAtomic.eval` over
`AtomicMachine.bind` on a single cell. -/
def runEvalStoreThenLoad (cfg : SingleCellConfig) (valLayout : LocalLayout) (valBits : Nat)
    (storeOrd : Miri.Concurrency.AtomicOrdering := .Release)
    (loadOrd : Miri.Concurrency.AtomicOrdering := .Acquire) : LmAtomicObs :=
  let st0 := mkSingleCellState cfg
  let choiceStore : LmAtomicChoice := { ord1 := storeOrd, pointeeLayout := valLayout }
  let choiceLoad : LmAtomicChoice := { ord1 := loadOrd, pointeeLayout := valLayout }
  let width := valLayout.layout.size.bytes.toNat
  match IntrinsicAtomic.eval (lmAtomicHooksBind .neverFail) choiceStore
      "atomic_store" #[mkCellPtrOp cfg, mkIntOp valLayout valBits]
      (mkDestPlace layoutUnit) none st0 with
  | .error e _ => classifyStepError e
  | .ok false _ => .invalidOrUnsupported
  | .ok true st1 =>
    match IntrinsicAtomic.eval (lmAtomicHooksBind .neverFail) choiceLoad
        "atomic_load" #[mkCellPtrOp cfg] (mkDestPlace valLayout) none st1 with
    | .error e _ => classifyStepError e
    | .ok false _ => .invalidOrUnsupported
    | .ok true st2 =>
      match readAllocBits st2 destAllocId 0 width, readAllocBits st2 cellAllocId 0 width with
      | some retBits, some postBits => .okScalar retBits postBits
      | _, _ => .invalidOrUnsupported

/-- Execute an RMW intrinsic (`atomic_xadd`, `atomic_xsub`, `atomic_and`,
`atomic_or`, `atomic_xor`, `atomic_nand`, `atomic_min`, `atomic_umin`,
`atomic_max`, `atomic_umax`, `atomic_xchg`) through `IntrinsicAtomic.eval` over
`AtomicMachine.bind`. -/
def runEvalRmw (name : String) (cfg : SingleCellConfig) (valLayout : LocalLayout)
    (rhsBits : Nat) (ord : Miri.Concurrency.AtomicOrdering := .SeqCst) : LmAtomicObs :=
  let st := mkSingleCellState cfg
  let choice : LmAtomicChoice := { ord1 := ord, ord2 := ord, pointeeLayout := valLayout }
  let dest := mkDestPlace valLayout
  let width := valLayout.layout.size.bytes.toNat
  match IntrinsicAtomic.eval (lmAtomicHooksBind .neverFail) choice
      name #[mkCellPtrOp cfg, mkIntOp valLayout rhsBits] dest none st with
  | .error e _ => classifyStepError e
  | .ok false _ => .invalidOrUnsupported
  | .ok true st' =>
    match readAllocBits st' destAllocId 0 width, readAllocBits st' cellAllocId 0 width with
    | some retBits, some postBits => .okScalar retBits postBits
    | _, _ => .invalidOrUnsupported

/-- Execute `atomic_cxchg` or `atomic_cxchgweak` through `IntrinsicAtomic.eval`
over `AtomicMachine.bind`. -/
def runEvalCas (weak : Bool) (cfg : SingleCellConfig) (valLayout : LocalLayout)
    (expectedBits newBits : Nat)
    (successOrd : Miri.Concurrency.AtomicOrdering := .SeqCst)
    (failureOrd : Miri.Concurrency.AtomicOrdering := .Relaxed)
    (weakPolicy : WeakCasPolicy := .neverFail) (weakSuccess : Bool := true) : LmAtomicObs :=
  let st := mkSingleCellState cfg
  let choice : LmAtomicChoice := {
    ord1 := successOrd
    ord2 := failureOrd
    pointeeLayout := valLayout
    weakSuccess := weakSuccess }
  let dest := mkDestPlace (mkCasDestLayout valLayout)
  let width := valLayout.layout.size.bytes.toNat
  let name := if weak then "atomic_cxchgweak" else "atomic_cxchg"
  match IntrinsicAtomic.eval (lmAtomicHooksBind weakPolicy) choice
      name #[mkCellPtrOp cfg, mkIntOp valLayout expectedBits, mkIntOp valLayout newBits]
      dest none st with
  | .error e _ => classifyStepError e
  | .ok false _ => .invalidOrUnsupported
  | .ok true st' =>
    match readAllocBits st' destAllocId 0 width,
          readAllocBool st' destAllocId width,
          readAllocBits st' cellAllocId 0 width with
    | some retBits, some ok, some postBits => .okCas retBits ok postBits
    | _, _, _ => .invalidOrUnsupported

/-- Execute `atomic_fence` or `atomic_singlethreadfence` through
`IntrinsicAtomic.eval` over `AtomicMachine.bind`, returning `some true` if
handled cleanly, `some false` if unhandled, or `none` on error. -/
def runEvalFence (singlethread : Bool) (ord : Miri.Concurrency.AtomicOrdering)
    (useDataRaceFastPath : Bool := false) : Except StepError Bool :=
  let st := mkSingleCellState { useDataRaceFastPath := useDataRaceFastPath }
  let choice : LmAtomicChoice := { ord0 := ord }
  let name := if singlethread then "atomic_singlethreadfence" else "atomic_fence"
  match IntrinsicAtomic.eval (lmAtomicHooksBind .neverFail) choice
      name #[] (mkDestPlace layoutUnit) none st with
  | .ok handled _ => .ok handled
  | .error e _ => .error e

/-! ## §5. Canonical `WeakCasPolicy` Laws & Concrete Kernel-Checked Execution Witnesses -/

/-- **Strong CAS (`weak = false`) with matching `expected` succeeds for ALL
`policy : WeakCasPolicy` and ALL `weakChoice : Bool`** through unmodified
`IntrinsicAtomic.eval` + `AtomicMachine.bind` (`runEvalCas`), committing the
write (`5 → 9`) and returning `.okCas 5 true 9`. -/
theorem compareExchange_strong_matches_all_policies
    (policy : WeakCasPolicy) (weakChoice : Bool) :
    runEvalCas false { widthBytes := 4, initBits := 5 } layoutU32 5 9
      .SeqCst .Relaxed policy weakChoice = .okCas 5 true 9 := by
  cases policy <;> cases weakChoice <;> decide +kernel

/-- **Mismatched CAS (`expected ≠ current`) skips the write and preserves memory**
for ALL `weak : Bool`, ALL `policy : WeakCasPolicy`, ALL `weakChoice : Bool`,
and both `treeBorrows : Bool` modes — even through a `Frozen` Tree Borrows tag
(confirming no write access reaches `PlaceMachine.memoryAccess` on mismatch). -/
theorem compareExchange_mismatch_skips_write
    (weak : Bool) (policy : WeakCasPolicy) (weakChoice : Bool) (treeBorrows : Bool) :
    runEvalCas weak
      { widthBytes := 4, initBits := 5, allocSize := 4, allocAlign := ⟨2⟩,
        treeBorrows := treeBorrows, tagMode := .frozenChild }
      layoutU32 6 9 .SeqCst .Relaxed policy weakChoice = .okCas 5 false 5 := by
  cases weak <;> cases policy <;> cases weakChoice <;> cases treeBorrows <;> decide +kernel

/-- **Weak CAS (`weak = true`) with matching `expected` under `.neverFail`**
commits the write (`5 → 9`) and returns `.okCas 5 true 9` for ALL
`weakChoice : Bool` and all valid failure orderings (`Relaxed`, `Acquire`,
`SeqCst`) through unmodified `IntrinsicAtomic.eval` + `AtomicMachine.bind`. -/
theorem compareExchange_weak_neverFail_succeeds
    (weakChoice : Bool) (failureOrd : Miri.Concurrency.AtomicOrdering)
    (hFail : failureOrd = .Relaxed ∨ failureOrd = .Acquire ∨ failureOrd = .SeqCst) :
    runEvalCas true { widthBytes := 4, initBits := 5 } layoutU32 5 9
      .SeqCst failureOrd .neverFail weakChoice = .okCas 5 true 9 := by
  rcases hFail with rfl | rfl | rfl <;> cases weakChoice <;> decide +kernel

/-- **Weak CAS (`weak = true`) with matching `expected` under `.alwaysFail`**
fails spuriously, preserves memory (`5`), and skips the write (even under
`treeBorrows = true` with `.frozenChild`) for ALL `weakChoice : Bool` and all
valid failure orderings (`Relaxed`, `Acquire`, `SeqCst`). -/
theorem compareExchange_weak_alwaysFail_spurious
    (weakChoice : Bool) (treeBorrows : Bool)
    (failureOrd : Miri.Concurrency.AtomicOrdering)
    (hFail : failureOrd = .Relaxed ∨ failureOrd = .Acquire ∨ failureOrd = .SeqCst) :
    runEvalCas true
      { widthBytes := 4, initBits := 5, allocSize := 4, allocAlign := ⟨2⟩,
        treeBorrows := treeBorrows, tagMode := .frozenChild }
      layoutU32 5 9 .SeqCst failureOrd .alwaysFail weakChoice = .okCas 5 false 5 := by
  rcases hFail with rfl | rfl | rfl <;> cases weakChoice <;> cases treeBorrows <;> decide +kernel

/-- **Weak CAS (`weak = true`) with matching `expected` under `.mayFail`**
follows `weakSuccess`: `true` commits the write (`5 → 9`, returning
`.okCas 5 true 9`), while `false` fails spuriously, skips the write (even under
`treeBorrows = true` with `.frozenChild`), and returns `.okCas 5 false 5`,
across all valid failure orderings (`Relaxed`, `Acquire`, `SeqCst`). -/
theorem compareExchange_weak_mayFail_follows_choice
    (failureOrd : Miri.Concurrency.AtomicOrdering)
    (hFail : failureOrd = .Relaxed ∨ failureOrd = .Acquire ∨ failureOrd = .SeqCst) :
    runEvalCas true { widthBytes := 4, initBits := 5 } layoutU32 5 9
      .SeqCst failureOrd .mayFail true = .okCas 5 true 9 ∧
    runEvalCas true
      { widthBytes := 4, initBits := 5, allocSize := 4, allocAlign := ⟨2⟩,
        treeBorrows := true, tagMode := .frozenChild }
      layoutU32 5 9 .SeqCst failureOrd .mayFail false = .okCas 5 false 5 := by
  rcases hFail with rfl | rfl | rfl <;> decide +kernel

/-- Store-then-load round-trips through `IntrinsicAtomic.eval` + `AtomicMachine.bind`
across `u8`, `u16`, `u32`, `u64`, and `usize`. -/
theorem eval_store_load_roundtrip_all_widths :
    runEvalStoreThenLoad { widthBytes := 1 } layoutU8 200 = .okScalar 200 200 ∧
    runEvalStoreThenLoad { widthBytes := 2 } layoutU16 48879 = .okScalar 48879 48879 ∧
    runEvalStoreThenLoad { widthBytes := 4 } layoutU32 3735928559 = .okScalar 3735928559 3735928559 ∧
    runEvalStoreThenLoad { widthBytes := 8 } layoutU64 81985529216486895 =
      .okScalar 81985529216486895 81985529216486895 ∧
    runEvalStoreThenLoad { widthBytes := 8 } layoutUsize 18446744073709551615 =
      .okScalar 18446744073709551615 18446744073709551615 := by
  decide +kernel

/-- Complete coverage of all RMW intrinsics through `IntrinsicAtomic.eval` +
`AtomicMachine.bind`: `xadd`, `xsub`, `and`, `or`, `xor`, `nand`, signed `min`/
`max` (`i32`: `-5 = 0xFFFFFFFB` vs `3`), unsigned `umin`/`umax` (`u32`:
`0xFFFFFFFF` vs `3`), and `xchg`. -/
theorem eval_all_rmw_intrinsics :
    runEvalRmw "atomic_xadd" { widthBytes := 4, initBits := 5 } layoutU32 3 = .okScalar 5 8 ∧
    runEvalRmw "atomic_xsub" { widthBytes := 4, initBits := 5 } layoutU32 2 = .okScalar 5 3 ∧
    runEvalRmw "atomic_and" { widthBytes := 4, initBits := 5 } layoutU32 4 = .okScalar 5 4 ∧
    runEvalRmw "atomic_or" { widthBytes := 4, initBits := 5 } layoutU32 2 = .okScalar 5 7 ∧
    runEvalRmw "atomic_xor" { widthBytes := 4, initBits := 5 } layoutU32 1 = .okScalar 5 4 ∧
    runEvalRmw "atomic_nand" { widthBytes := 1, initBits := 0x0F } layoutU8 0x33 =
      .okScalar 0x0F 0xFC ∧
    runEvalRmw "atomic_min" { widthBytes := 4, initBits := 0xFFFFFFFB } layoutI32 3 =
      .okScalar 0xFFFFFFFB 0xFFFFFFFB ∧
    runEvalRmw "atomic_max" { widthBytes := 4, initBits := 0xFFFFFFFB } layoutI32 3 =
      .okScalar 0xFFFFFFFB 3 ∧
    runEvalRmw "atomic_umin" { widthBytes := 4, initBits := 0xFFFFFFFF } layoutU32 3 =
      .okScalar 0xFFFFFFFF 3 ∧
    runEvalRmw "atomic_umax" { widthBytes := 4, initBits := 0xFFFFFFFF } layoutU32 3 =
      .okScalar 0xFFFFFFFF 0xFFFFFFFF ∧
    runEvalRmw "atomic_xchg" { widthBytes := 4, initBits := 5 } layoutU32 99 =
      .okScalar 5 99 := by
  decide +kernel

/-- Wrapping two's-complement overflow on `atomic_xadd` (`u32::MAX + 1 -> 0`)
and `atomic_xsub` (`0u32 - 1 -> u32::MAX`), matching Rust atomic semantics. -/
theorem eval_rmw_wrapping_overflow :
    runEvalRmw "atomic_xadd" { widthBytes := 4, initBits := 4294967295 } layoutU32 1 =
      .okScalar 4294967295 0 ∧
    runEvalRmw "atomic_xsub" { widthBytes := 4, initBits := 0 } layoutU32 1 =
      .okScalar 0 4294967295 := by
  decide +kernel

/-- `atomic_cxchg` and `atomic_cxchgweak` across `.neverFail`, `.alwaysFail`,
and `.mayFail` (`weakSuccess = true` vs `false`). -/
theorem eval_cxchg_and_cxchgweak :
    runEvalCas false { widthBytes := 4, initBits := 5 } layoutU32 5 9 .SeqCst .Relaxed .neverFail =
      .okCas 5 true 9 ∧
    runEvalCas false { widthBytes := 4, initBits := 5 } layoutU32 5 9 .SeqCst .Relaxed .alwaysFail =
      .okCas 5 true 9 ∧
    runEvalCas false { widthBytes := 4, initBits := 5 } layoutU32 6 9 .SeqCst .Relaxed .neverFail =
      .okCas 5 false 5 ∧
    runEvalCas true { widthBytes := 4, initBits := 5 } layoutU32 5 9 .SeqCst .Relaxed .neverFail =
      .okCas 5 true 9 ∧
    runEvalCas true { widthBytes := 4, initBits := 5 } layoutU32 5 9 .SeqCst .Relaxed .alwaysFail =
      .okCas 5 false 5 ∧
    runEvalCas true { widthBytes := 4, initBits := 5 } layoutU32 5 9 .SeqCst .Relaxed .mayFail true =
      .okCas 5 true 9 ∧
    runEvalCas true { widthBytes := 4, initBits := 5 } layoutU32 5 9 .SeqCst .Relaxed .mayFail false =
      .okCas 5 false 5 := by
  decide +kernel

/-- `atomic_fence` and `atomic_singlethreadfence` through `IntrinsicAtomic.eval`
(both with `dataRace = none` and single-threaded `GlobalState.initial false false`). -/
theorem eval_fences_and_unknown_name :
    runEvalFence false .Acquire false = .ok true ∧
    runEvalFence false .Release false = .ok true ∧
    runEvalFence false .AcqRel false = .ok true ∧
    runEvalFence false .SeqCst true = .ok true ∧
    (match runEvalFence false .Relaxed false with | .error (.invalidProgram _) => true | _ => false) = true ∧
    runEvalFence true .Relaxed false = .ok true ∧
    runEvalFence true .SeqCst true = .ok true ∧
    (match IntrinsicAtomic.eval (lmAtomicHooksBind .neverFail) {} "not_an_atomic" #[]
        (mkDestPlace layoutUnit) none (mkSingleCellState {}) with
      | .ok false _ => true | _ => false) = true := by
  decide +kernel

/-- Single-threaded `GlobalState` fast path (`raceDetecting = false`): load,
store, RMW, succeeding CAS, AND failing CAS (which enters `dispatch` ->
`atomicCompareExchangeFailureState` whenever `dataRace.isSome`) all succeed. -/
theorem eval_single_thread_global_fast_path :
    runEvalLoad { widthBytes := 4, initBits := 5, useDataRaceFastPath := true } layoutU32 =
      .okScalar 5 5 ∧
    runEvalStore { widthBytes := 4, initBits := 5, useDataRaceFastPath := true } layoutU32 9 =
      .okStore 9 ∧
    runEvalRmw "atomic_xadd" { widthBytes := 4, initBits := 5, useDataRaceFastPath := true } layoutU32 3 =
      .okScalar 5 8 ∧
    runEvalCas false { widthBytes := 4, initBits := 5, useDataRaceFastPath := true } layoutU32 5 9 =
      .okCas 5 true 9 ∧
    runEvalCas false { widthBytes := 4, initBits := 5, useDataRaceFastPath := true } layoutU32 6 9 =
      .okCas 5 false 5 := by
  decide +kernel

/-- Comprehensive fault witnesses through `IntrinsicAtomic.eval` +
`AtomicMachine.bind`:
1. Misaligned pointer UB (`ptrOffset = 1` for `u32`).
2. Non-power-of-two size (`size = 3`) rejection in `IntrinsicAtomic.access`.
3. Oversized `u128` (`size = 16 > 8`) UB on an 8-byte cell AND on a 16-byte
   16-aligned read-only allocation (`ReadOnlyAtomicViolation.oversizedLoad`).
4. Out-of-bounds pointer UB (`ptrOffset = 8` on 8-byte cell).
5. Read-only allocation (`Mutability.Not`): `Relaxed` load succeeds; `SeqCst`
   load (`nonRelaxedLoad`), `atomic_store`, `atomic_xadd`, AND even failing
   `atomic_cxchg` (`storeOrRmw`) all fault with UB! -/
theorem eval_fault_witnesses :
    runEvalLoad { widthBytes := 4, initBits := 5, ptrOffset := 1 } layoutU32 = .ub ∧
    runEvalLoad { widthBytes := 3, initBits := 5 } layoutNonPow2_3 = .invalidOrUnsupported ∧
    runEvalLoad { widthBytes := 8, initBits := 5, allocSize := 8 } layoutU128 .Relaxed = .ub ∧
    runEvalLoad { widthBytes := 16, initBits := 5, allocSize := 16, allocAlign := ⟨4⟩,
                  mutability := .Not } layoutU128 .Relaxed = .ub ∧
    runEvalLoad { widthBytes := 4, initBits := 5, ptrOffset := 8 } layoutU32 = .ub ∧
    runEvalLoad { widthBytes := 4, initBits := 5, mutability := .Not } layoutU32 .Relaxed =
      .okScalar 5 5 ∧
    runEvalLoad { widthBytes := 4, initBits := 5, mutability := .Not } layoutU32 .SeqCst = .ub ∧
    runEvalStore { widthBytes := 4, initBits := 5, mutability := .Not } layoutU32 9 .Relaxed = .ub ∧
    runEvalRmw "atomic_xadd" { widthBytes := 4, initBits := 5, mutability := .Not } layoutU32 1 .Relaxed = .ub ∧
    runEvalCas false { widthBytes := 4, initBits := 5, mutability := .Not } layoutU32 6 9 .Relaxed .Relaxed = .ub := by
  decide +kernel

/-- Tree Borrows `Frozen` mode sensitivity through unmodified vendored
`PlaceMachine.memoryAccess` -> `lmTreeBorrowsDiagnostic` (bridged to vendored
`BorrowTree.performBorrowAccessRange` by
`atomic_tb_check_bridges_vendored_performBorrowAccessRange`):
- With `treeBorrows = false`, all 5 operations succeed.
- With `treeBorrows = true` and `tagMode = .frozenChild`, `atomic_load` and
  failing `atomic_cxchg` succeed while `atomic_store`, `atomic_xadd`, and
  succeeding `atomic_cxchg` fault with UB. -/
theorem eval_tb_frozen_mode_sensitivity :
    let mkCfg (tb : Bool) : SingleCellConfig :=
      { widthBytes := 4, initBits := 5, allocSize := 4, allocAlign := ⟨2⟩,
        treeBorrows := tb, tagMode := .frozenChild }
    runEvalLoad (mkCfg false) layoutU32 = .okScalar 5 5 ∧
    runEvalLoad (mkCfg true) layoutU32 = .okScalar 5 5 ∧
    runEvalCas false (mkCfg false) layoutU32 6 9 = .okCas 5 false 5 ∧
    runEvalCas false (mkCfg true) layoutU32 6 9 = .okCas 5 false 5 ∧
    runEvalStore (mkCfg false) layoutU32 9 = .okStore 9 ∧
    runEvalStore (mkCfg true) layoutU32 9 = .ub ∧
    runEvalRmw "atomic_xadd" (mkCfg false) layoutU32 1 = .okScalar 5 6 ∧
    runEvalRmw "atomic_xadd" (mkCfg true) layoutU32 1 = .ub ∧
    runEvalCas false (mkCfg false) layoutU32 5 9 = .okCas 5 true 9 ∧
    runEvalCas false (mkCfg true) layoutU32 5 9 = .ub := by
  decide +kernel

/-- **Third (previously undocumented) authority divergence — `u128` atomics**: vendored
`atomicAccessCheck` restricts oversized atomics only on read-only allocations, so a 16-byte
`atomic_load` on an in-bounds *mutable* cell is NOT UB (MiniRust: UB above `MAX_ATOMIC_SIZE = 8`,
`atomicLoad_size_too_big_ub`); case `18`'s `.ub` is merely its out-of-bounds 16-byte read. -/
theorem eval_u128_in_bounds_mutable_load_not_ub :
    runEvalLoad { widthBytes := 16, initBits := 5, allocSize := 16, allocAlign := ⟨4⟩ }
      layoutU128 .Relaxed ≠ .ub := by
  decide +kernel

/-! ## §6. Executable Cross-Root Observation Runner (`lmAtomicObserve`, Cases `0..27`) -/

/-- Canonical 28-case (`0..27`) executable observation runner through vendored
`IntrinsicAtomic.eval` over `AtomicMachine.bind` (`fastPath` selects `dataRace = some _`):
- `0..7`: `u8`/`u16`/`u32`/`u64` atomic load & store
- `8..9`: `atomic_cxchg` equal (`(5, 9)`) and unequal (`(6, 9)`) on `u32`
- `10..14`: `atomic_xadd`/`xsub`/`and`/`or`/`xor` in-range on `u32`
- `15..16`: wrapping overflow on `atomic_xadd` (`u32::MAX + 1`) and `atomic_xsub` (`0 - 1`)
- `17..19`: misaligned UB, oversized `u128` UB on 8B cell, OOB UB
- `20..22`: read-only allocation (`Mutability.Not`): `Relaxed` load ok, `store` UB, failing `cxchg` UB
- `23..27`: Tree Borrows `Frozen` tag: `load` & failing `cxchg` ok in both modes;
  `store`, `xadd`, and succeeding `cxchg` ok when `treeBorrows = false` and UB when `treeBorrows = true`. -/
def lmAtomicObserveWith (fastPath treeBorrows : Bool) (caseIdx : Nat) : LmAtomicObs :=
  let frozenCfg : SingleCellConfig :=
    { widthBytes := 4, initBits := 5, allocSize := 4, allocAlign := ⟨2⟩,
      treeBorrows := treeBorrows, useDataRaceFastPath := fastPath, tagMode := .frozenChild }
  let roCfg : SingleCellConfig :=
    { widthBytes := 4, initBits := 5, allocSize := 8, allocAlign := Align.EIGHT,
      mutability := .Not, treeBorrows := treeBorrows, useDataRaceFastPath := fastPath }
  let base : SingleCellConfig := { treeBorrows := treeBorrows, useDataRaceFastPath := fastPath }
  match caseIdx with
  | 0 => runEvalLoad { base with widthBytes := 1, initBits := 200 } layoutU8
  | 1 => runEvalStore { base with widthBytes := 1, initBits := 0 } layoutU8 200
  | 2 => runEvalLoad { base with widthBytes := 2, initBits := 48879 } layoutU16
  | 3 => runEvalStore { base with widthBytes := 2, initBits := 0 } layoutU16 48879
  | 4 => runEvalLoad { base with widthBytes := 4, initBits := 3735928559 } layoutU32
  | 5 => runEvalStore { base with widthBytes := 4, initBits := 0 } layoutU32 3735928559
  | 6 => runEvalLoad { base with widthBytes := 8, initBits := 81985529216486895 } layoutU64
  | 7 => runEvalStore { base with widthBytes := 8, initBits := 0 } layoutU64 81985529216486895
  | 8 => runEvalCas false { base with widthBytes := 4, initBits := 5 } layoutU32 5 9
  | 9 => runEvalCas false { base with widthBytes := 4, initBits := 5 } layoutU32 6 9
  | 10 => runEvalRmw "atomic_xadd" { base with widthBytes := 4, initBits := 5 } layoutU32 3
  | 11 => runEvalRmw "atomic_xsub" { base with widthBytes := 4, initBits := 5 } layoutU32 2
  | 12 => runEvalRmw "atomic_and" { base with widthBytes := 4, initBits := 5 } layoutU32 4
  | 13 => runEvalRmw "atomic_or" { base with widthBytes := 4, initBits := 5 } layoutU32 2
  | 14 => runEvalRmw "atomic_xor" { base with widthBytes := 4, initBits := 5 } layoutU32 1
  | 15 => runEvalRmw "atomic_xadd" { base with widthBytes := 4, initBits := 4294967295 } layoutU32 1
  | 16 => runEvalRmw "atomic_xsub" { base with widthBytes := 4, initBits := 0 } layoutU32 1
  | 17 => runEvalLoad { base with widthBytes := 4, initBits := 5, ptrOffset := 1 } layoutU32
  | 18 => runEvalLoad { base with widthBytes := 8, initBits := 5, allocSize := 8 } layoutU128 .Relaxed
  | 19 => runEvalLoad { base with widthBytes := 4, initBits := 5, ptrOffset := 8 } layoutU32
  | 20 => runEvalLoad roCfg layoutU32 .Relaxed
  | 21 => runEvalStore roCfg layoutU32 9 .Relaxed
  | 22 => runEvalCas false roCfg layoutU32 6 9 .Relaxed .Relaxed
  | 23 => runEvalLoad frozenCfg layoutU32
  | 24 => runEvalCas false frozenCfg layoutU32 6 9
  | 25 => runEvalStore frozenCfg layoutU32 9
  | 26 => runEvalRmw "atomic_xadd" frozenCfg layoutU32 1
  | 27 => runEvalCas false frozenCfg layoutU32 5 9
  | _ => .invalidOrUnsupported

/-- Canonical cross-root runner (`dataRace = none`; see `lmAtomicObserve_fastPath_invariant`). -/
def lmAtomicObserve (treeBorrows : Bool) (caseIdx : Nat) : LmAtomicObs :=
  lmAtomicObserveWith false treeBorrows caseIdx

/-- Expected output table for `lmAtomicObserve` across all 28 cases (`0..27`). -/
def lmExpectedObs (tb : Bool) : Nat → LmAtomicObs
  | 0 => .okScalar 200 200
  | 1 => .okStore 200
  | 2 => .okScalar 48879 48879
  | 3 => .okStore 48879
  | 4 => .okScalar 3735928559 3735928559
  | 5 => .okStore 3735928559
  | 6 => .okScalar 81985529216486895 81985529216486895
  | 7 => .okStore 81985529216486895
  | 8 => .okCas 5 true 9
  | 9 => .okCas 5 false 5
  | 10 => .okScalar 5 8
  | 11 => .okScalar 5 3
  | 12 => .okScalar 5 4
  | 13 => .okScalar 5 7
  | 14 => .okScalar 5 4
  | 15 => .okScalar 4294967295 0
  | 16 => .okScalar 0 4294967295
  | 17 => .ub
  | 18 => .ub
  | 19 => .ub
  | 20 => .okScalar 5 5
  | 21 => .ub
  | 22 => .ub
  | 23 => .okScalar 5 5
  | 24 => .okCas 5 false 5
  | 25 => if tb then .ub else .okStore 9
  | 26 => if tb then .ub else .okScalar 5 6
  | 27 => if tb then .ub else .okCas 5 true 9
  | _ => .invalidOrUnsupported

private theorem lmAtomicObserve_table_aux :
    ([false, true].all fun tb =>
      (List.range 28).all fun idx =>
        decide (lmAtomicObserve tb idx = lmExpectedObs tb idx)) = true := by
  decide +kernel

/-- **Kernel-checked 56-cell observation table** (`2 modes × 28 cases`) proving
that every case of `lmAtomicObserve` through vendored `IntrinsicAtomic.eval` +
`AtomicMachine.bind` matches `lmExpectedObs` (zero `native_decide`). -/
theorem lmAtomicObserve_table (tb : Bool) (idx : Nat) (hIdx : idx < 28) :
    lmAtomicObserve tb idx = lmExpectedObs tb idx := by
  have hTb : tb ∈ [false, true] := by cases tb <;> simp
  have hMem : idx ∈ List.range 28 := List.mem_range.mpr hIdx
  have h1 := List.all_eq_true.mp lmAtomicObserve_table_aux tb hTb
  have h2 := List.all_eq_true.mp h1 idx hMem
  exact of_decide_eq_true h2

private theorem lmAtomicObserve_fastPath_aux :
    ([false, true].all fun tb =>
      (List.range 28).all fun idx =>
        decide (lmAtomicObserveWith true tb idx = lmExpectedObs tb idx)) = true := by
  decide +kernel

/-- **Fast-path invariance of the entire corpus**: with `dataRace = some (GlobalState.initial
false false)` every case takes the `some global` bracket of `IntrinsicAtomic.allowDataRaces` and
every failing `compareExchange` its `isSome` VClock tail, yet all observations are unchanged. -/
theorem lmAtomicObserve_fastPath_invariant (fastPath tb : Bool) (idx : Nat) (hIdx : idx < 28) :
    lmAtomicObserveWith fastPath tb idx = lmAtomicObserve tb idx := by
  have hTb : tb ∈ [false, true] := by cases tb <;> simp
  have h1 := List.all_eq_true.mp lmAtomicObserve_fastPath_aux tb hTb
  have hFast : lmAtomicObserveWith true tb idx = lmExpectedObs tb idx :=
    of_decide_eq_true (List.all_eq_true.mp h1 idx (List.mem_range.mpr hIdx))
  cases fastPath
  · rfl
  · exact hFast.trans (lmAtomicObserve_table tb idx hIdx).symm

/-! ## §7. Exhaustive Axiom & Import-Isolation Audit -/

section AxiomAudit
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for modName in env.header.moduleNames do
    if (`MiniRustSpec).isPrefixOf modName || (`Anneal).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported in LeanMiriSpec.AtomicIntrinsicsLM"
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      if a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
        throwError "{c} depends on {a} (compiler-trusting evaluation)"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    checked := checked + 1
    if (`LeanMiriSpec.AtomicIntrinsicsLM).isPrefixOf c then
      if let .thmInfo _ := info then theorems := theorems + 1
  if theorems < 32 then
    throwError "axiom audit is vacuous: only {theorems} theorems of LeanMiriSpec.AtomicIntrinsicsLM seen"
  logInfo m!"LeanMiriSpec.AtomicIntrinsicsLM: verified {checked} declarations ({theorems} theorems) depend only on propext, Quot.sound, Classical.choice (sorry_free=true, ofReduceBool_free=true, import_isolated=true)"

end AxiomAudit

end LeanMiriSpec.AtomicIntrinsicsLM
