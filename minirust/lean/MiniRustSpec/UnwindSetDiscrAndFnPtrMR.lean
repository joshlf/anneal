/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import MiniRustSpec.Correspondence.WideSliceDst

/-!
# Episode 2 Correspondence: Unwind, `SetDiscriminant`, Function Pointers,
# `Subtype`, `UnwrapUnsafeBinder`, and Closures (`MiniRustSpec`)

Operational correspondence between Anneal's trusted MIR semantics
(`Trusted.Rustc.V2026_06_01.MirSemantics`) and MiniRust's operational semantics
(`MiniRustSpec.Interp` over both `BasicMemory<x86_64>` (`Mach`) and
`TreeBorrowsMemory<x86_64>` (`MachTB`)) for ten constructs (`C1`–`C10`):

1. **`C1` (`StatementKind.setDiscriminant`)**: universal step simulation across
   `Mach` and `MachTB` (direct-tagged enum tag writes preserving payload bytes,
   deref writes, misaligned/dead/OOB/frozen-borrow UB equivalence, explicit
   `.uninit` shell behavior `setDiscriminant_uninit_shell_behavior`, and the
   `translateStatement = none` boundary).
2. **`C2` (`TerminatorKind.unwindResume`)**: universal simulations across all
   five unwind regimes on `Mach` and `MachTB`: `.cleanup` (with callee borrow
   disabling and `MachTB` `end_call` protector release), `.continue_`
   multi-frame
   big-step (`1` Trusted step) vs. `k + 1` MiniRust `ResumeUnwind` steps,
   `.unreachable` UB, `.terminate` abort, and the explicit root-frame divergence
   `unwindResume_root_panic_vs_ub_divergence` (Trusted `.halted .panic` vs.
   MiniRust `BottomOfStack` UB), plus `StartUnwind -> ResumeUnwind ->
   StopUnwind`
   composition on `Mach` and `MachTB`.
3. **`C3` (`TerminatorKind.unwindTerminate`)**: lockstep `.abort` simulation
   against `buildAbort` (`IntrinsicOp.Abort`, `Stop.abort`) on `Mach` and
   `MachTB`, plus the `translateTerminator = none` boundary.
4. **`C4` (`StatementKind.coverage`)**: stuttering PC-advance equivalence
   (`1` Trusted `stepMirFn` step ↔ `0` MiniRust steps on `Mach` and `MachTB`)
   plus the `translateStatement = none` boundary.
5. **`C5` (`StatementKind.backwardIncompatibleDropHint`)**: unconditional
   stuttering PC-advance equivalence (never reading or faulting even on dead or
   uninitialized places) plus the `translateStatement = none` boundary.
6. **`C6` (`CastKind.fnPtrToPtr`)**: `evalFnPtrToPtr` ↔ MiniRust
   `CastOp.Transmute (.Ptr (.Raw .None))` on `Mach` and `MachTB` preserving
   function-pointer provenance, dead/uninit UB equivalence, and exact
   characterization of Trusted's extra checks (`offsetBytes = 0`,
   non-`rustIntrinsic` ABI, `lookupBorrow = none`) vs. MiniRust `Transmute`.
7. **`C7` (`CastKind.subtype`)**: `evalByteCast` identity with `.transmute`,
   `Classical.choice`-free integer/pointer byte-codec and `transmuteM` lemmas on
   `Mach` and `MachTB`, and invalid-bit-pattern UB equivalence (`bool` byte `2`,
   `NonZeroU8` byte `0`).
8. **`C8` (Non-`Unsize` `CastKind.pointerCoercion`)**: exhaustive five-coercion
   characterization: `ReifyFnPointer`, `ClosureFnPointer`, `UnsafeFnPointer`
   (which `Trusted` executes via `evalUnsafeFnPointer` when safe-to-unsafe
   signatures match, alongside exact strict-check divergence vs. MiniRust
   type-erased `Transmute` and `.unsupported` on unrecognized coercion tags),
   `MutToConstPointer` (thin, scalar, wide slice, and wide dyn-vtable pointers +
   shape-mismatch UB), and `ArrayToPointer` (global/raw, stack-borrow
   `deriveStackElemThinPtr`, and scalar-address preservation).
9. **`C9` (`ProjectionElem.unwrapUnsafeBinder`)**: transparent wrapper
   projection
   across reads, writes, deref chains, and `Rvalue.len` (`splitLastDeref?`),
   matched by MiniRust zero-offset field-0 wrapper projection and `Transmute` on
   `Mach` and `MachTB`, plus `translatePlace = none` and dead-local UB.
10. **`C10` (`AggregateKind.closure`)**: 0-capture ZST closures and
    multi-capture
    scalar/pointer closures relating Trusted `.aggregate 0 vals` to MiniRust
    `ValueExpr.Tuple` on `Mach` and `MachTB`, including left-to-right operand
    evaluation and dead/uninit upvar UB propagation.
-/

namespace MiniRustSpec.UnwindSetDiscrAndFnPtrMR

set_option Elab.async false
set_option linter.unusedSimpArgs false

open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open MiniRustSpec
open MiniRustSpec.Gen
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp
open MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.Witness
open MiniRustSpec.Correspondence.PointerWitness
open MiniRustSpec.Correspondence.RefWitness
open MiniRustSpec.Correspondence.TbWitness
open MiniRustSpec.Correspondence.WideSliceDst

/-! ## §0. Shared Types, Builders, and `Classical.choice`-Free Polymorphic
Codecs -/

@[reducible] def dummySpan : String := "ep2.rs:1:1"
@[reducible] def mkSt (k : MirAst.StatementKind) : MirAst.Statement :=
  { kind := k, span := dummySpan }
@[reducible] def mkTm (k : MirAst.TerminatorKind) : MirAst.Terminator :=
  { kind := k, span := dummySpan }
@[reducible] def mkBb (stmts : List MirAst.Statement) (term : MirAst.TerminatorKind)
    (isCleanup : Bool := false) : MirAst.BasicBlockData :=
  { statements := stmts, terminator := mkTm term, isCleanup := isCleanup }

@[reducible] def u8MirTy : MirAst.Ty := { kind := .uint .u8, layoutIdx := 0 }
@[reducible] def u32MirTy : MirAst.Ty := { kind := .uint .u32, layoutIdx := 0 }
@[reducible] def i32MirTy : MirAst.Ty := { kind := .int .i32, layoutIdx := 0 }
@[reducible] def u64MirTy : MirAst.Ty := { kind := .uint .u64, layoutIdx := 0 }
@[reducible] def usizeMirTy : MirAst.Ty := { kind := .uint .usize, layoutIdx := 0 }
@[reducible] def boolMirTy : MirAst.Ty := { kind := .bool, layoutIdx := 0 }
@[reducible] def unitMirTy : MirAst.Ty := { kind := .tuple [], layoutIdx := 0 }
@[reducible] def rawConstUnitMirTy : MirAst.Ty :=
  { kind := .rawPtr .not (.tuple []), layoutIdx := 0 }
@[reducible] def rawConstU32MirTy : MirAst.Ty :=
  { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 }
@[reducible] def rawMutU32MirTy : MirAst.Ty :=
  { kind := .rawPtr .mut (.uint .u32), layoutIdx := 0 }
@[reducible] def refMutU32MirTy : MirAst.Ty :=
  { kind := .ref .mut (.uint .u32), layoutIdx := 0 }
@[reducible] def arr2U32MirTy : MirAst.Ty :=
  { kind := .array (.uint .u32) 2, layoutIdx := 0 }
@[reducible] def rawMutArr2U32MirTy : MirAst.Ty :=
  { kind := .rawPtr .mut (.array (.uint .u32) 2), layoutIdx := 0 }
@[reducible] def rawConstArr2U32MirTy : MirAst.Ty :=
  { kind := .rawPtr .not (.array (.uint .u32) 2), layoutIdx := 0 }
@[reducible] def rawMutSliceU32MirTy : MirAst.Ty :=
  { kind := .rawPtr .mut (.slice (.uint .u32)), layoutIdx := 0 }
@[reducible] def rawConstSliceU32MirTy : MirAst.Ty :=
  { kind := .rawPtr .not (.slice (.uint .u32)), layoutIdx := 0 }
@[reducible] def rawMutDynMirTy : MirAst.Ty :=
  { kind := .rawPtr .mut (.dynamic "ep2::Tr"), layoutIdx := 0 }
@[reducible] def rawConstDynMirTy : MirAst.Ty :=
  { kind := .rawPtr .not (.dynamic "ep2::Tr"), layoutIdx := 0 }

@[reducible] def fnPtrSafeU32MirTy : MirAst.Ty :=
  { kind := .fnPtr [.uint .u32] (.uint .u32) .safe .rust, layoutIdx := 0 }
@[reducible] def fnPtrUnsafeU32MirTy : MirAst.Ty :=
  { kind := .fnPtr [.uint .u32] (.uint .u32) .unsafe_ .rust, layoutIdx := 0 }
@[reducible] def fnPtrIntrinsicU32MirTy : MirAst.Ty :=
  { kind := .fnPtr [.uint .u32] (.uint .u32) .safe .rustIntrinsic, layoutIdx := 0 }
@[reducible] def fnDefU32MirTy (dp : String) : MirAst.Ty :=
  { kind := .fnDef dp [], layoutIdx := 0 }
@[reducible] def closureZstMirTy (dp : String) : MirAst.Ty :=
  { kind := .closure dp [], layoutIdx := 0 }
@[reducible] def closureCapMirTy (dp : String) : MirAst.Ty :=
  { kind := .closure dp [.uint .u32, .rawPtr .not (.uint .u32)], layoutIdx := 0 }

@[reducible] def mkDecl (ty : MirAst.Ty) : MirAst.LocalDecl :=
  { mutability := .mut, ty := ty, debugName := none }

@[reducible] def locPlace (i : Nat) (proj : List MirAst.ProjectionElem := []) :
    MirAst.Place :=
  { local_ := i, projection := proj }

@[reducible] def constU8 (n : Nat) : MirAst.Operand :=
  .constant { ty := u8MirTy, val := .scalar (.int ⟨n, 1⟩) }
@[reducible] def constU32 (n : Nat) : MirAst.Operand :=
  .constant { ty := u32MirTy, val := .scalar (.int ⟨n, 4⟩) }
@[reducible] def constZst (ty : MirAst.Ty) : MirAst.Operand :=
  .constant { ty := ty, val := .zeroSized }

@[reducible] def u8MrTy : Gen.Type := .Int ⟨.Unsigned, ⟨1⟩⟩
@[reducible] def u32MrTy : Gen.Type := .Int u32
@[reducible] def i32MrTy : Gen.Type := .Int ⟨.Signed, ⟨4⟩⟩
@[reducible] def u64MrTy : Gen.Type := .Int ⟨.Unsigned, ⟨8⟩⟩
@[reducible] def usizeMrTy : Gen.Type := .Int IntType.usize_ty
@[reducible] def wideSlicePtrMrTy : Gen.Type := .Ptr (.Raw .ElementCount)
@[reducible] def traitNameOf (idx : Nat) : Gen.TraitName := ⟨⟨idx⟩⟩
@[reducible] def wideDynPtrMrTy (idx : Nat := 0) : Gen.Type :=
  .Ptr (.Raw (.VTablePointer (traitNameOf idx)))

/-- Dummy non-null return-value pointer placeholder for frames whose caller
ignores the return place during unwind tests. -/
@[reducible] def dummyRetPtr : Ptr := { addr := 1, provenance := none }

/-- Build a minimal `CapturedMir` body in `Runtime(PostCleanup)` phase. -/
def mkMirBody (defPath : String) (decls : List MirAst.LocalDecl) (argCount : Nat)
    (blocks : List MirAst.BasicBlockData) (layouts : LayoutTable := emptyLayoutTable) :
    MirAst.CapturedMir :=
  { defPath := defPath
    phase := .runtimePostCleanup
    role := .subject
    argCount := argCount
    localDecls := decls
    basicBlocks := blocks
    fnAbi := { args := [], ret := { layout := i8Layout, mode := .direct },
               conv := .rust, canUnwind := true }
    layouts := layouts
    allocations := [] }

/-- Build a MiniRust `Gen.Function` with `minimize`'s default `implicit_writes
:= true`. -/
def mkMrFn (locals : List (Gen.LocalName × Gen.Type)) (args : List Gen.LocalName)
    (ret : Gen.LocalName) (blocks : List (Gen.BbName × Gen.BasicBlock))
    (start : Gen.BbName := bbName 0) : Gen.Function :=
  { locals := ⟨locals⟩
    args := args
    ret := ret
    calling_convention := .Rust
    blocks := ⟨blocks⟩
    start := start
    implicit_writes := true }

/-- Build a minimal `Gen.Program` from an association list of functions. -/
def mkMrProg (fns : List (Gen.FnName × Gen.Function)) (start : Gen.FnName := fnName 0) :
    Gen.Program :=
  { functions := ⟨fns⟩
    start := start
    globals := ⟨[]⟩
    traits := ⟨[]⟩
    vtables := ⟨[]⟩ }

/-- Build a single-thread `BasicMemory` MiniRust machine (`Mach`). -/
def mkMrMach (prog : Gen.Program) (allocs : List Gen.Allocation) (stack : List Frame)
    (fnPtrs : List (Gen.FnName × Ptr) := [])
    (globalPtrs : List (Gen.GlobalName × Ptr) := [])
    (unwindPayloads : List Ptr := []) : Mach :=
  { prog := prog
    mem := { memory := { allocations := allocs, _phantom := {} }, accesses := [] }
    intptrcast := ⟨⟨[]⟩⟩
    threads := [{ stack := stack, state := .Enabled, unwind_payloads := unwindPayloads }]
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨globalPtrs⟩
    fn_ptrs := ⟨fnPtrs⟩
    vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

/-- Build a `BasicMemory` stack allocation at `addr` with initial byte contents
`data`. -/
def mkStackAlloc (addr : Int) (data : List Byte) (align : Nat := 8) : Gen.Allocation :=
  { addr := addr
    data := data
    align := ⟨align⟩
    kind := .Stack
    live := true
    extra := () }

/-- Build a `BasicMemory` function allocation at `addr` (size `0`, align `1`).
-/
def mkFnAlloc (addr : Int) : Gen.Allocation :=
  { addr := addr
    data := []
    align := ⟨1⟩
    kind := .Function
    live := true
    extra := () }

/-- Extract the return value of a clean event-free `runA` execution. -/
def runAVal (body : CapturedMir) (fuel : Nat) (s : MachineState) : Option MirSemantics.Value :=
  match runA body fuel s with
  | some ([], .normal (v, _)) => some v
  | _ => none

/-- Decidable UB-message projection for `Interp α`. -/
def interpUbMsg {α : Type} : Interp α → Option String
  | .error (.ub msg) => some msg
  | _ => none

/-- Decidable `.abort` check for `Interp α`. -/
def interpIsAbort {α : Type} : Interp α → Bool
  | .error .abort => true
  | _ => false

theorem eq_error_ub_of_interpUbMsg {α : Type} {r : Interp α} {msg : String}
    (h : interpUbMsg r = some msg) : r = .error (.ub msg) := by
  cases r with
  | ok _ => simp [interpUbMsg] at h
  | error e =>
    cases e <;> simp [interpUbMsg] at h
    subst h; rfl

theorem eq_error_abort_of_interpIsAbort {α : Type} {r : Interp α}
    (h : interpIsAbort r = true) : r = .error .abort := by
  cases r with
  | ok _ => simp [interpIsAbort] at h
  | error e =>
    cases e <;> simp [interpIsAbort] at h
    rfl

theorem ok_of_map_toOption {α β : Type} {r : Interp α} {f : α → β} {b : β}
    (h : r.toOption.map f = some b) : ∃ a, r = .ok a ∧ f a = b := by
  cases r with
  | error _ => simp [Except.toOption] at h
  | ok a => simp [Except.toOption] at h; exact ⟨a, rfl, h⟩

private theorem size_ne_self_ite_local {α : Type} (s : LibSpecr.Size) (a b : α) :
    (if s ≠ s then a else b) = b := by
  simp

/-- Polymorphic helper: `evalPlaceM` on `unitPlace` succeeds on any `Machine M`,
returning the aligned pointer at address `1` with `unitType`. -/
theorem evalPlaceM_unitPlace {M : Type} [Gen.Memory M] [MemoryOps M] (m : Machine M) :
    evalPlaceM m unitPlace =
      .ok (({ ptr := ThinPointer.widen { addr := 1, provenance := none } none,
              aligned := true }, Interp.unitType), m) :=
  rfl

/-- Polymorphic helper (`Classical.choice`-free): `encodePtrBytesM` data round-
trip. -/
theorem encodePtrBytesM_data {M : Type} [Gen.Memory M]
    (prov : Option (Gen.Memory.Provenance M)) (i : Nat) (data : List UInt8) :
    (encodePtrBytesM (M := M) prov i data).mapM AbstractByte.dataM = some data := by
  induction data generalizing i with
  | nil => rfl
  | cons b rest ih => simp [encodePtrBytesM, AbstractByte.dataM, ih]

/-- Polymorphic helper (`Classical.choice`-free): `decodePtrProvenanceM`
recovers
consistent provenance fragments across `encodePtrBytesM`. -/
theorem decodePtrProvenanceM_encode {M : Type} [Gen.Memory M] [MemoryOps M]
    (prov : Option (Gen.Memory.Provenance M)) (i : Nat) (data : List UInt8) :
    decodePtrProvenanceM (M := M) i prov (encodePtrBytesM (M := M) prov i data) = prov := by
  induction data generalizing i with
  | nil => rfl
  | cons b rest ih =>
    cases prov with
    | none =>
      simp [encodePtrBytesM, decodePtrProvenanceM, AbstractByte.provenance_fragM, ih]
    | some p =>
      simp [encodePtrBytesM, decodePtrProvenanceM, AbstractByte.provenance_fragM, ih]

/-- Polymorphic helper (`Classical.choice`-free): `firstProvenanceM` on
`encodePtrBytesM` recovers `prov`. -/
theorem firstProvenanceM_encode {M : Type} [Gen.Memory M]
    (prov : Option (Gen.Memory.Provenance M)) (b : UInt8) (rest : List UInt8) :
    firstProvenanceM (M := M) (encodePtrBytesM (M := M) prov 0 (b :: rest)) = prov := by
  cases prov <;> simp [encodePtrBytesM, firstProvenanceM, AbstractByte.provenance_fragM]

/-- Polymorphic helper (`Classical.choice`-free): length of `encodePtrBytesM`.
-/
theorem encodePtrBytesM_length {M : Type} [Gen.Memory M]
    (prov : Option (Gen.Memory.Provenance M)) (i : Nat) (data : List UInt8) :
    (encodePtrBytesM (M := M) prov i data).length = data.length := by
  induction data generalizing i with
  | nil => rfl
  | cons _ _ ih => simp [encodePtrBytesM, ih]

/-- `Classical.choice`-free helper: `(2 ^ n : Nat)` coerced to `Int` equals
`(2 : Int) ^ n`. -/
theorem two_pow_int_cf (n : Nat) : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [Nat.pow_succ, Int.natCast_mul, Int.pow_succ, ih]
    rfl

/-- `Classical.choice`-free `inBounds` proof for `addr < 2 ^ 64` at `usize`. -/
theorem inBounds_usize_cf (addr : Nat) (h : addr < 2 ^ 64) :
    inBounds (addr : Int) .Unsigned x86_64.PTR_SIZE = true := by
  rw [inBounds_usize, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact ⟨Int.natCast_nonneg addr, lt_two_pow_64_int h⟩

/-- `Classical.choice`-free `Endianness.encode` for 64-bit unsigned pointers. -/
theorem encode_usize_cf (addr : Nat) (h : addr < 2 ^ 64) :
    Endianness.encode x86_64.ENDIANNESS .Unsigned x86_64.PTR_SIZE (addr : Int) =
      some (leBytes addr 8) := by
  have hlt := lt_two_pow_64_int h
  have h0 : (0 : Int) ≤ (addr : Int) := Int.natCast_nonneg addr
  have hin := inBounds_usize_cf addr h
  have hmod : ((addr : Int) % (2 : Int) ^ Interp.Size.bits x86_64.PTR_SIZE).toNat = addr := by
    rw [two_pow_ptrBits, Int.emod_eq_of_lt h0 hlt]
    exact Int.toNat_natCast addr
  unfold Endianness.encode
  rw [hin]
  dsimp only [↓reduceIte]
  rw [hmod]
  rfl

/-- `Classical.choice`-free little-endian decode/encode round-trip. -/
theorem leValue_leBytes_cf (v : Nat) : ∀ n, leValue (leBytes v n) = v % 256 ^ n
  | 0 => by simp [leBytes, leValue, Nat.mod_one]
  | n + 1 => by
    simp only [leBytes, leValue, UInt8.toNat_ofNat', leValue_leBytes_cf (v / 256) n]
    have h256 : (2 : Nat) ^ 8 = 256 := by decide
    rw [h256, Nat.mod_mod, Nat.pow_succ']
    have h1 := Nat.mod_add_div v 256
    have h2 := Nat.mod_add_div (v / 256) (256 ^ n)
    have hlt1 : v % 256 < 256 := Nat.mod_lt v (by decide)
    have hlt2 : v / 256 % 256 ^ n < 256 ^ n := Nat.mod_lt _ (Nat.pow_pos (by decide))
    have hlt : v % 256 + 256 * (v / 256 % 256 ^ n) < 256 * 256 ^ n := by
      have hmul : 256 * (v / 256 % 256 ^ n + 1) ≤ 256 * 256 ^ n :=
        Nat.mul_le_mul_left 256 hlt2
      have hmul' : 256 * (v / 256 % 256 ^ n) + 256 ≤ 256 * 256 ^ n := by
        simpa [Nat.mul_add] using hmul
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right hlt1 _) (by
        rw [Nat.add_comm]; exact hmul')
    have heq :
        v = (v % 256 + 256 * (v / 256 % 256 ^ n)) +
          (256 * 256 ^ n) * (v / 256 / 256 ^ n) := by
      calc v = v % 256 + 256 * (v / 256) := h1.symm
        _ = v % 256 + 256 * (v / 256 % 256 ^ n + 256 ^ n * (v / 256 / 256 ^ n)) := by
          rw [h2]
        _ = (v % 256 + 256 * (v / 256 % 256 ^ n)) +
            (256 * 256 ^ n) * (v / 256 / 256 ^ n) := by
          rw [Nat.mul_add, ← Nat.add_assoc, ← Nat.mul_assoc]
    conv => rhs; rw [heq]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- `Classical.choice`-free `inBounds` proof for `intFromBits bits it`. -/
theorem inBounds_intFromBits_cf (it : Gen.IntType) (hsz : 0 < it.size.bytes)
    (bits : Nat) (hb : bits < 2 ^ (8 * it.size.bytes)) :
    inBounds (intFromBits bits it) it.signed it.size = true := by
  rcases it with ⟨signed, sz⟩
  cases signed with
  | Unsigned =>
    unfold inBounds intFromBits
    dsimp only []
    rw [Bool.and_eq_true]
    refine ⟨decide_eq_true (Int.natCast_nonneg bits), decide_eq_true ?_⟩
    change (bits : Int) < (2 : Int) ^ (8 * sz.bytes)
    rw [← two_pow_int_cf]
    exact Int.ofNat_lt.mpr hb
  | Signed =>
    unfold inBounds intFromBits
    dsimp only []
    have hn : 0 < 8 * sz.bytes := Nat.mul_pos (by decide) hsz
    have hsplit : 2 ^ (8 * sz.bytes) = 2 ^ (8 * sz.bytes - 1) + 2 ^ (8 * sz.bytes - 1) := by
      have h1 : 8 * sz.bytes = (8 * sz.bytes - 1) + 1 := (Nat.sub_add_cancel hn).symm
      conv => lhs; rw [h1]
      rw [Nat.pow_succ, Nat.mul_two]
    split
    · next hlt =>
      rw [Bool.and_eq_true]
      refine ⟨decide_eq_true ?_, decide_eq_true ?_⟩
      · change -((2 : Int) ^ (8 * sz.bytes - 1)) ≤ (bits : Int)
        exact Int.le_trans
          (Int.neg_nonpos_of_nonneg (by rw [← two_pow_int_cf]; exact Int.natCast_nonneg _))
          (Int.natCast_nonneg bits)
      · change (bits : Int) < (2 : Int) ^ (8 * sz.bytes - 1)
        rw [← two_pow_int_cf]
        exact Int.ofNat_lt.mpr hlt
    · next hge =>
      have hge' : 2 ^ (8 * sz.bytes - 1) ≤ bits := Nat.le_of_not_lt hge
      rw [Bool.and_eq_true]
      refine ⟨decide_eq_true ?_, decide_eq_true ?_⟩
      · change -((2 : Int) ^ (8 * sz.bytes - 1)) ≤ (bits : Int) - (2 : Int) ^ (8 * sz.bytes)
        rw [← two_pow_int_cf, ← two_pow_int_cf]
        have hsum : 2 ^ (8 * sz.bytes) ≤ 2 ^ (8 * sz.bytes - 1) + bits := by
          rw [hsplit]
          exact Nat.add_le_add_left hge' _
        have hsumI : ((2 ^ (8 * sz.bytes) : Nat) : Int) ≤
            ((2 ^ (8 * sz.bytes - 1) : Nat) : Int) + (bits : Int) := by
          rw [← Int.natCast_add]; exact Int.ofNat_le.mpr hsum
        have h1 := Int.add_le_add_left hsumI (-((2 ^ (8 * sz.bytes - 1) : Nat) : Int))
        rw [← Int.add_assoc, Int.add_left_neg, Int.zero_add] at h1
        have h2 := Int.sub_le_sub_right h1 ((2 ^ (8 * sz.bytes) : Nat) : Int)
        rw [Int.add_sub_cancel] at h2
        exact h2
      · change (bits : Int) - (2 : Int) ^ (8 * sz.bytes) < (2 : Int) ^ (8 * sz.bytes - 1)
        rw [← two_pow_int_cf, ← two_pow_int_cf]
        have hltI : (bits : Int) < ((2 ^ (8 * sz.bytes) : Nat) : Int) := Int.ofNat_lt.mpr hb
        have hsub_neg : (bits : Int) - ((2 ^ (8 * sz.bytes) : Nat) : Int) < 0 := by
          have := Int.sub_lt_sub_right hltI ((2 ^ (8 * sz.bytes) : Nat) : Int)
          rwa [Int.sub_self] at this
        exact Int.lt_of_lt_of_le hsub_neg (Int.natCast_nonneg _)

/-- Polymorphic helper (`Classical.choice`-free): `encodePtrM` from an explicit
`Endianness.encode` witness (avoids unfolding `2 ^ 64` in the kernel). -/
theorem encodePtrM_of_encode {M : Type} [Gen.Memory M]
    (ptr : ThinPointer (Gen.Memory.Provenance M)) (data : List UInt8)
    (henc : Endianness.encode x86_64.ENDIANNESS .Unsigned x86_64.PTR_SIZE ptr.addr = some data) :
    encodePtrM (M := M) ptr = .ok (encodePtrBytesM (M := M) ptr.provenance 0 data) := by
  unfold encodePtrM
  rw [henc]
  rfl

/-- Polymorphic thin-pointer encode (`Classical.choice`-free) across any `Memory
M`
(`BasicMemory` and `TreeBorrowsMemory`). -/
theorem encodePtrM_eq {M : Type} [Gen.Memory M]
    (addr : Nat) (h : addr < 2 ^ 64) (prov : Option (Gen.Memory.Provenance M)) :
    encodePtrM (M := M) { addr := addr, provenance := prov } =
      .ok (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) :=
  encodePtrM_of_encode { addr := addr, provenance := prov } (leBytes addr 8)
    (encode_usize_cf addr h)

/-- Polymorphic thin-pointer decode (`Classical.choice`-free) across any `Memory
M`
(`BasicMemory` and `TreeBorrowsMemory`). -/
theorem decodePtrM_encodePtrBytesM {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr : Nat) (h : addr < 2 ^ 64) (prov : Option (Gen.Memory.Provenance M)) :
    decodePtrM (M := M) (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) =
      .ok (some { addr := addr, provenance := prov }) := by
  have hlen : (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)).length =
      x86_64.PTR_SIZE.bytes := by
    rw [encodePtrBytesM_length, leBytes_length]; rfl
  have h256 : addr < 256 ^ 8 := by
    have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    rw [this]; exact h
  have hval : Endianness.decode x86_64.ENDIANNESS .Unsigned (leBytes addr 8) = (addr : Int) := by
    simp only [Endianness.decode, x86_64.ENDIANNESS, leValue_leBytes_cf, Nat.mod_eq_of_lt h256]
  have hfirst :
      firstProvenanceM (M := M) (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) = prov := by
    have hcons : leBytes addr 8 = UInt8.ofNat (addr % 256) :: leBytes (addr / 256) 7 := rfl
    rw [hcons]; exact firstProvenanceM_encode prov _ _
  unfold decodePtrM
  rw [ite_eq_right_iff.mpr (fun hn => absurd hlen hn)]
  rw [encodePtrBytesM_data]
  dsimp only
  rw [hval, hfirst, decodePtrProvenanceM_encode]
  rfl

/-- Polymorphic helper (`Classical.choice`-free): `transmuteM` on `thinRawPtrTy`
from explicit `inBounds`, `encodeM`, and `decodeM` witnesses. -/
theorem transmuteM_thinRawPtr_of_codec {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr : Int) (prov : Option (Gen.Memory.Provenance M))
    (bs : List (AbstractByte (Gen.Memory.Provenance M))) (m : Option (Machine M))
    (hin : inBounds addr .Unsigned x86_64.PTR_SIZE = true)
    (henc : Type.encodeM (M := M) thinRawPtrTy
      (.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)) = .ok bs)
    (hdec : Type.decodeM (M := M) thinRawPtrTy bs =
      .ok (some (.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)))) :
    let p : Gen.Pointer (Gen.Memory.Provenance M) :=
      ThinPointer.widen { addr := addr, provenance := prov } none
    transmuteM (M := M) (.Ptr p) thinRawPtrTy thinRawPtrTy m = .ok (.Ptr p) := by
  intro p
  unfold transmuteM
  rw [layout_thinRawPtr]
  simp only [ok_bind, expect_size_sized, size_ne_self_ite_local]
  rw [show Type.encodeM (M := M) thinRawPtrTy (.Ptr p) = .ok bs from henc, ok_bind,
    show Type.decodeM (M := M) thinRawPtrTy bs = .ok (some (.Ptr p)) from hdec, ok_bind]
  dsimp only []
  unfold checkValueM checkPtrM
  simp only [thinRawPtrTy, p, ThinPointer.widen, ensureElseUb, hin, ↓reduceIte,
    PtrType.meta_kind, checkPtrMetadataM, PtrType.safe_pointee,
    pure, Except.pure, bind, Except.bind]
  rfl

/-- Polymorphic `transmuteM` identity for thin raw pointers (`*const T` / `*mut
T` /
fn pointers) across EVERY `Memory M` (`BasicMemory` and `TreeBorrowsMemory`),
proved completely `Classical.choice`-free. -/
theorem transmuteM_thinRawPtr_id {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr : Nat) (h : addr < 2 ^ 64) (prov : Option (Gen.Memory.Provenance M))
    (m : Option (Machine M)) :
    let p : Gen.Pointer (Gen.Memory.Provenance M) :=
      ThinPointer.widen { addr := addr, provenance := prov } none
    transmuteM (M := M) (.Ptr p) thinRawPtrTy thinRawPtrTy m = .ok (.Ptr p) := by
  intro p
  have hin := inBounds_usize_cf addr h
  have henc : Type.encodeM (M := M) thinRawPtrTy (.Ptr p) =
      .ok (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) := by
    simp only [thinRawPtrTy, Type.encodeM, PtrType.as_wide_pair, PtrType.meta_kind,
      p, ThinPointer.widen]
    exact encodePtrM_eq addr h prov
  have hdec : Type.decodeM (M := M) thinRawPtrTy
      (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) = .ok (some (.Ptr p)) := by
    simp only [thinRawPtrTy, Type.decodeM, PtrType.as_wide_pair, PtrType.meta_kind,
      p, ThinPointer.widen]
    rw [decodePtrM_encodePtrBytesM addr h prov, ok_bind]
    rfl
  exact transmuteM_thinRawPtr_of_codec (addr : Int) prov _ m hin henc hdec

/-- Polymorphic helper (`Classical.choice`-free): `evalCastOpM` from an explicit
`transmuteM` witness on `thinRawPtrTy`. -/
theorem evalCastOpM_transmute_thinRawPtr_of_transmute {M : Type} [Gen.Memory M] [MemoryOps M]
    (p : Gen.Pointer (Gen.Memory.Provenance M)) (m : Option (Machine M))
    (ht : transmuteM (M := M) (.Ptr p) thinRawPtrTy thinRawPtrTy m = .ok (.Ptr p)) :
    evalCastOpM (M := M) (.Transmute thinRawPtrTy) (.Ptr p, thinRawPtrTy) m =
      .ok (.Ptr p, thinRawPtrTy) := by
  unfold evalCastOpM
  dsimp only []
  rw [layout_thinRawPtr]
  simp only [ok_bind, expect_size_sized, size_ne_self_ite_local, ht, pure, Except.pure,
    bind, Except.bind]

/-- Polymorphic `evalCastOpM` identity for thin raw pointers across `Mach` and
`MachTB` (`Classical.choice`-free). -/
theorem evalCastOpM_transmute_thinRawPtr_id {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr : Nat) (h : addr < 2 ^ 64) (prov : Option (Gen.Memory.Provenance M))
    (m : Option (Machine M)) :
    let p : Gen.Pointer (Gen.Memory.Provenance M) :=
      ThinPointer.widen { addr := addr, provenance := prov } none
    evalCastOpM (M := M) (.Transmute thinRawPtrTy) (.Ptr p, thinRawPtrTy) m =
      .ok (.Ptr p, thinRawPtrTy) :=
  evalCastOpM_transmute_thinRawPtr_of_transmute _ m (transmuteM_thinRawPtr_id addr h prov m)

/-- `Classical.choice`-free helper for `BasicMemory` `evalCastOp` on
`thinRawPtrTy`. -/
theorem evalCastOp_transmute_thinRawPtr_of_codec
    (addr : Int) (prov : Option Prov) (bs : List Byte) (m : Option Mach)
    (hin : inBounds addr .Unsigned x86_64.PTR_SIZE = true)
    (henc : Type.encode thinRawPtrTy
      (.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)) = .ok bs)
    (hdec : Type.decode thinRawPtrTy bs =
      .ok (some (.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)))) :
    let p : Gen.Pointer Prov := ThinPointer.widen { addr := addr, provenance := prov } none
    evalCastOp (.Transmute thinRawPtrTy) (.Ptr p, thinRawPtrTy) m =
      .ok (.Ptr p, thinRawPtrTy) := by
  intro p
  unfold evalCastOp transmute
  dsimp only []
  rw [layout_thinRawPtr]
  simp only [ok_bind, expect_size_sized, size_ne_self_ite_local]
  rw [show Type.encode thinRawPtrTy (.Ptr p) = .ok bs from henc, ok_bind,
    show Type.decode thinRawPtrTy bs = .ok (some (.Ptr p)) from hdec, ok_bind]
  dsimp only []
  unfold checkValue checkPtr
  simp only [thinRawPtrTy, p, ThinPointer.widen, ensureElseUb, hin, ↓reduceIte,
    PtrType.meta_kind, checkPtrMetadata, PtrType.safe_pointee,
    pure, Except.pure, bind, Except.bind]
  rfl

/-- `Classical.choice`-free `BasicMemory` thin-pointer encode. -/
theorem encode_thinRawPtr_cf (addr : Nat) (h : addr < 2 ^ 64) (prov : Option Prov) :
    Type.encode thinRawPtrTy
      (.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)) =
      .ok (ptrBytes addr prov) := by
  simp only [thinRawPtrTy, Type.encode, PtrType.as_wide_pair, PtrType.meta_kind,
    ThinPointer.widen]
  exact encodePtr_of_encode { addr := addr, provenance := prov } (leBytes addr 8)
    (encode_usize_cf addr h)

/-- `Classical.choice`-free `BasicMemory` thin-pointer decode. -/
theorem decode_thinRawPtr_cf (addr : Nat) (h : addr < 2 ^ 64) (prov : Option Prov) :
    Type.decode thinRawPtrTy (ptrBytes addr prov) =
      .ok (some (.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none))) := by
  have hdata := encodePtrBytes_data prov 0 (leBytes addr 8)
  have h256 : addr < 256 ^ 8 := by
    have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    rw [this]; exact h
  have hval : Endianness.decode x86_64.ENDIANNESS .Unsigned (leBytes addr 8) = (addr : Int) := by
    simp only [Endianness.decode, x86_64.ENDIANNESS, leValue_leBytes_cf, Nat.mod_eq_of_lt h256]
  have hlen : (ptrBytes addr prov).length = x86_64.PTR_SIZE.bytes := ptrBytes_length addr prov
  have hfirst : firstProvenance (ptrBytes addr prov) = prov := by
    have hcons : leBytes addr 8 = UInt8.ofNat (addr % 256) :: leBytes (addr / 256) 7 := rfl
    unfold ptrBytes; rw [hcons]; exact firstProvenance_encodePtrBytes prov _ _
  simp only [thinRawPtrTy, Type.decode, PtrType.as_wide_pair, PtrType.meta_kind]
  unfold decodePtr
  rw [ite_eq_right_iff.mpr (fun hn => absurd hlen hn), hfirst]
  unfold ptrBytes
  rw [hdata]
  simp only [hval, decodePtrProvenance_encode]
  rfl

/-- `Classical.choice`-free `BasicMemory` specialization of
`evalCastOp_transmute_thinRawPtr_id`. -/
theorem evalCastOp_transmute_thinRawPtr_id
    (addr : Nat) (h : addr < 2 ^ 64) (prov : Option Prov) (m : Option Mach) :
    let p : Gen.Pointer Prov := ThinPointer.widen { addr := addr, provenance := prov } none
    evalCastOp (.Transmute thinRawPtrTy) (.Ptr p, thinRawPtrTy) m =
      .ok (.Ptr p, thinRawPtrTy) :=
  evalCastOp_transmute_thinRawPtr_of_codec (addr : Int) prov (ptrBytes addr prov) m
    (inBounds_usize_cf addr h) (encode_thinRawPtr_cf addr h prov)
    (decode_thinRawPtr_cf addr h prov)

/-- `Classical.choice`-free polymorphic little-endian integer encode bridge:
for any `it : IntType` with `0 < it.size.bytes` and `bits < 2^(8 *
it.size.bytes)`,
`Type.encodeIntM it (.Int (intFromBits bits it))` emits `leBytes bits
it.size.bytes`
with `none` provenance. -/
theorem encodeIntM_intFromBits {M : Type} [Gen.Memory M]
    (it : Gen.IntType) (hsz : 0 < it.size.bytes)
    (bits : Nat) (hb : bits < 2 ^ (8 * it.size.bytes)) :
    Type.encodeIntM (M := M) it (.Int (intFromBits bits it)) =
      .ok ((leBytes bits it.size.bytes).map (fun b => .Init b none)) := by
  have hbits : Interp.Size.bits it.size = 8 * it.size.bytes := rfl
  have hin := inBounds_intFromBits_cf it hsz bits hb
  have hmod : (intFromBits bits it % (2 : Int) ^ Interp.Size.bits it.size).toNat = bits := by
    rw [hbits, intFromBits_emod bits it hb]; rfl
  unfold Type.encodeIntM Endianness.encode
  simp only [hin, ↓reduceIte, hmod, x86_64.ENDIANNESS, pure, Except.pure]

/-- `Classical.choice`-free helper: `mapM AbstractByte.dataM` over no-provenance
initialized bytes recovers the underlying byte list. -/
theorem mapM_dataM_initNone {M : Type} [Gen.Memory M] (bs : List UInt8) :
    (bs.map (fun b => (AbstractByte.Init b none : AbstractByte (Gen.Memory.Provenance M)))).mapM
      AbstractByte.dataM = some bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih => simp [AbstractByte.dataM, ih]

/-- `Classical.choice`-free polymorphic integer decode of `leBytes bits
it.size.bytes`. -/
theorem decodeIntM_leBytes {M : Type} [Gen.Memory M]
    (it : Gen.IntType) (hsz : 0 < it.size.bytes)
    (bits : Nat) (hb : bits < 2 ^ (8 * it.size.bytes)) :
    Type.decodeIntM (M := M) it ((leBytes bits it.size.bytes).map (fun b => .Init b none)) =
      .ok (some (.Int (intFromBits bits it))) := by
  rcases it with ⟨signed, sz⟩
  have hlen : ((leBytes bits sz.bytes).map
      (fun b => (AbstractByte.Init b none : AbstractByte (Gen.Memory.Provenance M)))).length =
      sz.bytes := by
    simp [leBytes_length]
  have h256 : 256 ^ sz.bytes = 2 ^ (8 * sz.bytes) := by
    rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]
  have hle : leValue (leBytes bits sz.bytes) = bits := by
    rw [leValue_leBytes_cf, h256, Nat.mod_eq_of_lt hb]
  have hdec : Endianness.decode x86_64.ENDIANNESS signed (leBytes bits sz.bytes) =
      intFromBits bits ⟨signed, sz⟩ := by
    cases signed with
    | Unsigned =>
      simp only [Endianness.decode, x86_64.ENDIANNESS, hle, intFromBits]
    | Signed =>
      have hlenNat : (leBytes bits sz.bytes).length = sz.bytes := leBytes_length bits _
      simp only [Endianness.decode, x86_64.ENDIANNESS, hle, intFromBits, hlenNat]
      if hlt : bits < 2 ^ (8 * sz.bytes - 1) then
        have hltI : (bits : Int) < (2 : Int) ^ (8 * sz.bytes - 1) := by
          rw [← two_pow_int_cf]; exact Int.ofNat_lt.mpr hlt
        rw [ite_eq_left_iff.mpr (fun hn => absurd hlt hn),
            ite_eq_left_iff.mpr (fun hn => absurd hltI hn)]
      else
        have hgeI : ¬ ((bits : Int) < (2 : Int) ^ (8 * sz.bytes - 1)) := by
          rw [← two_pow_int_cf]; intro hlt'; exact hlt (Int.ofNat_lt.mp hlt')
        rw [ite_eq_right_iff.mpr (fun hy => absurd hy hlt),
            ite_eq_right_iff.mpr (fun hy => absurd hy hgeI)]
  unfold Type.decodeIntM
  dsimp only []
  rw [ite_eq_right_iff.mpr (fun hn => absurd hlen hn), mapM_dataM_initNone]
  dsimp only
  rw [hdec]
  rfl

/-- `Classical.choice`-free polymorphic `transmuteM` between any two same-size
integer types (`u32 ↔ i32`, `u64 ↔ i64`, `u8 ↔ i8`, etc.) across BOTH `Mach`
and `MachTB`! -/
theorem transmuteM_int_sameSize {M : Type} [Gen.Memory M] [MemoryOps M]
    (srcIt dstIt : Gen.IntType) (hEq : srcIt.size = dstIt.size)
    (hsz : 0 < srcIt.size.bytes)
    (al : LibSpecr.Align)
    (hlay1 : Type.layout (.Int srcIt) = .ok (.Sized srcIt.size al))
    (hlay2 : Type.layout (.Int dstIt) = .ok (.Sized dstIt.size al))
    (bits : Nat) (hb : bits < 2 ^ (8 * srcIt.size.bytes))
    (m : Option (Machine M)) :
    transmuteM (M := M) (.Int (intFromBits bits srcIt)) (.Int srcIt) (.Int dstIt) m =
      .ok (.Int (intFromBits bits dstIt)) := by
  have hdstSz : 0 < dstIt.size.bytes := by rw [← hEq]; exact hsz
  have hdstBits : bits < 2 ^ (8 * dstIt.size.bytes) := by rw [← hEq]; exact hb
  have hwinDst := inBounds_intFromBits_cf dstIt hdstSz bits hdstBits
  unfold transmuteM
  rw [hlay1, ok_bind, expect_size_sized, ok_bind, hlay2, ok_bind, expect_size_sized, ok_bind,
    hEq, size_ne_self_ite_local]
  simp only [Type.encodeM, Type.decodeM]
  rw [encodeIntM_intFromBits srcIt hsz bits hb, ok_bind, hEq,
    decodeIntM_leBytes dstIt hdstSz bits hdstBits, ok_bind]
  simp only [checkValueM, IntType.can_represent, ensureElseUb, hwinDst, ↓reduceIte,
    pure, Except.pure, bind, Except.bind]
  rfl

/-! ## §1 (`C1`): `StatementKind.setDiscriminant` (`Mach` & `MachTB`) -/

/-- Variant table of `twoVarEnumMrTy`. -/
def twoVarEnumVariants : Map Int Gen.Variant :=
  let vTy : Gen.Type := .Tuple [(⟨4⟩, u32MrTy)] ⟨⟨8⟩, ⟨4⟩, none⟩ none
  ⟨[(0, ⟨vTy, ⟨[(⟨0⟩, (⟨.Unsigned, ⟨1⟩⟩, 0))]⟩⟩),
    (1, ⟨vTy, ⟨[(⟨0⟩, (⟨.Unsigned, ⟨1⟩⟩, 1))]⟩⟩)]⟩

/-- Direct-tagged two-variant Rust enum layout
(`#[repr(u8)] enum TwoVar { A(u32) = 0, B(u32) = 1 }`): 8 bytes, align 4,
tag `u8` at offset 0 (`0 | 1`), payload `u32` at offset 4. -/
def twoVarEnumMrTy : Gen.Type :=
  .Enum twoVarEnumVariants ⟨.Unsigned, ⟨1⟩⟩
    (.Branch ⟨0⟩ ⟨.Unsigned, ⟨1⟩⟩ .Invalid
      ⟨[((0, 1), .Known 0), ((1, 2), .Known 1)]⟩)
    ⟨8⟩ ⟨4⟩

/-- Anneal MIR type for `TwoVar` (`RigidTy.adt "ep2::TwoVar" []`). -/
@[reducible] def twoVarMirTy : MirAst.Ty := { kind := .adt "ep2::TwoVar" [], layoutIdx := 0 }

/-- Anneal `TypeLayout` for `TwoVar` (8 bytes, align 4, direct `u8` tag). -/
def twoVarMirLayout : TypeLayout :=
  { size := ⟨8⟩
    align := ⟨4⟩
    backendRepr := .memory
    fields := .arbitrary [⟨0⟩] [0]
    variants := .multiple (.initialized (.int 8 false) ⟨0, 1⟩) 0 []
    isUninhabited := false }

def twoVarLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [twoVarMirLayout] }

/-- **C1 Universal Fragment Boundary
(`translateStatement_setDiscriminant_none`)**:
`Translate.translateStatement` returns `none` for every
`StatementKind.setDiscriminant`. -/
theorem translateStatement_setDiscriminant_none
    (decls : List MirAst.LocalDecl) (p : MirAst.Place) (v : Nat)
    (span : String) (layouts : LayoutTable) :
    translateStatement decls { kind := .setDiscriminant p v, span := span } layouts = none :=
  rfl

/-- **C1 Trusted Local Step Law
(`trusted_setDiscriminant_local_preserves_payload`)**:
Executing `StatementKind.setDiscriminant ⟨loc, []⟩ newVar` on an initialized
enum local `.aggregate oldVar fields` (with no active protectors) updates ONLY
the variant tag to `newVar`, preserves every payload field `fields` verbatim,
advances `stmtIdx` by 1, and invalidates conflicting borrows of `loc`. -/
theorem trusted_setDiscriminant_local_preserves_payload
    (s : MachineState) (loc oldVar newVar : Nat) (fields : List MirSemantics.Value)
    (locals' : List LocalSlot) (span : String)
    (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (hget : get? s.frame.locals loc = some (.init (.aggregate oldVar fields)))
    (hset : set? s.frame.locals loc (.init (.aggregate newVar fields)) = some locals')
    (hprot : s.memory.activeProtectors = []) :
    evalStmt s { kind := .setDiscriminant (locPlace loc) newVar, span := span } decls layouts =
      MirStepNode.step
        (advanceStmt s locals'
          { s.memory with
            borrows := invalidateConflictingBorrows s.memory.borrows loc .none
              (length s.memory.callStack) }) := by
  simp only [evalStmt, locPlace, hget, evalSetDiscriminantLocal, hset, hprot]

/-- **C1 Trusted Dead/OOB Local UB Law
(`trusted_setDiscriminant_dead_or_oob_ub`)**:
Executing `StatementKind.setDiscriminant ⟨loc, []⟩ v` on a `.dead` or
out-of-bounds local faults with `MirStepNode.fail .ub`. -/
theorem trusted_setDiscriminant_dead_or_oob_ub
    (s : MachineState) (loc v : Nat) (span : String)
    (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (hdead : get? s.frame.locals loc = some .dead ∨ get? s.frame.locals loc = none) :
    evalStmt s { kind := .setDiscriminant (locPlace loc) v, span := span } decls layouts =
      MirStepNode.fail .ub := by
  rcases hdead with h | h <;> simp [evalStmt, locPlace, h]

/-- **C1 Trusted `.uninit` Shell Behavior
(`setDiscriminant_uninit_shell_behavior`)**:
On an `.uninit` whole local `loc`:
1. When `setDiscriminantUninitDeclOk decls loc = true` (e.g., an `.adt` decl),
   Trusted initializes `loc` to the payload-free tag shell
   `.init (.aggregate newVar .nil)` (preserving uninitialized payload absence).
2. When `setDiscriminantUninitDeclOk decls loc = false` (e.g., a scalar `u32`
   decl), Trusted fails closed with `MirStepNode.unsupported`. -/
theorem setDiscriminant_uninit_shell_behavior
    (s : MachineState) (loc newVar : Nat) (span : String)
    (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (huninit : get? s.frame.locals loc = some .uninit) :
    (setDiscriminantUninitDeclOk decls loc = true →
      evalStmt s { kind := .setDiscriminant (locPlace loc) newVar, span := span } decls layouts =
        evalSetDiscriminantLocal s loc newVar .nil) ∧
    (setDiscriminantUninitDeclOk decls loc = false →
      evalStmt s { kind := .setDiscriminant (locPlace loc) newVar, span := span } decls layouts =
        MirStepNode.unsupported) := by
  constructor <;> intro h <;> simp [evalStmt, locPlace, huninit, h]

/-- **C1 MiniRust Polymorphic Dead-Local & Misaligned-Pointer UB Laws** across
BOTH `BasicMemory` (`Mach`) and `TreeBorrowsMemory` (`MachTB`). -/
theorem minirust_setDiscriminantM_dead_local_ub
    {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Machine M) (fr : StackFrame M) (ln : Gen.LocalName) (ty : Gen.Type) (v : Int)
    (hcur : curFrameM m = .ok fr)
    (hty : mapIndex fr.func.locals ln "self.cur_frame().func.locals[name]" = .ok ty)
    (hdead : mapGet fr.locals ln = none) :
    evalSetDiscriminantM m (.Local ln) v = .error (.ub "access to a dead local") := by
  unfold evalSetDiscriminantM evalPlaceM
  simp only [hcur, hty, hdead, bind, Except.bind, ub]

theorem minirust_setDiscriminantM_misaligned_ub
    {M : Type} [Gen.Memory M] [MemoryOps M]
    (m m1 : Machine M) (dst : Gen.PlaceExpr) (place : Gen.Place M)
    (variants : Map Int Gen.Variant) (dty : Gen.IntType) (disc : Gen.Discriminator)
    (sz : LibSpecr.Size) (al : LibSpecr.Align) (v : Int)
    (hp : evalPlaceM m dst = .ok ((place, .Enum variants dty disc sz al), m1))
    (hmis : place.aligned = false) :
    evalSetDiscriminantM m dst v =
      .error (.ub "setting the discriminant of a place based on a misaligned pointer") := by
  unfold evalSetDiscriminantM
  simp only [hp, hmis, Bool.not_false, ↓reduceIte, bind, Except.bind, ub]

/-- **C1 Polymorphic Direct-Tagged `twoVarEnumMrTy` Tag-Write Law (`Mach` &
`MachTB`)**:
For any `tag ∈ {0, 1}`, `evalSetDiscriminantM` on `twoVarEnumMrTy` performs a
single 1-byte store of `[.Init (UInt8.ofNat tag) none]` at offset `0`, leaving
offsets `1..7` (including the `u32` payload at `4..8`) untouched. By
`evalStatementM_bm_eq` and `evalStatementM_tb_wfLive`, this covers both `Mach`
and `MachTB` (preserving `MachTB.wfLive`). -/
theorem minirust_setDiscriminantM_twoVar_tagStore
    {M : Type} [Gen.Memory M] [MemoryOps M]
    (m m1 : Machine M) (dst : Gen.PlaceExpr) (place : Gen.Place M)
    (tag : Nat) (htag : tag = 0 ∨ tag = 1)
    (hp : evalPlaceM m dst = .ok ((place, twoVarEnumMrTy), m1))
    (hal : place.aligned = true)
    (ptr0 : ThinPointer (Gen.Memory.Provenance M))
    (hoff : ptrOffsetInboundsM m1 place.ptr.thin_pointer 0 = .ok ptr0)
    (cm' : Gen.ConcurrentMemory M)
    (hst : ConcurrentMemory.store m1.mem ptr0 [.Init (UInt8.ofNat tag) none] ⟨1⟩ .None = .ok cm') :
    evalSetDiscriminantM m dst (Int.ofNat tag) = .ok { m1 with mem := cm' } := by
  rcases htag with rfl | rfl
  · have hEnc0 : Type.encodeIntM (M := M) ⟨.Unsigned, ⟨1⟩⟩ (.Int 0) =
        .ok [.Init (UInt8.ofNat 0) none] := rfl
    have hMap0 : mapGet twoVarEnumVariants (Int.ofNat 0) =
        some ⟨.Tuple [(⟨4⟩, u32MrTy)] ⟨⟨8⟩, ⟨4⟩, none⟩ none,
              ⟨[(⟨0⟩, (⟨.Unsigned, ⟨1⟩⟩, 0))]⟩⟩ := rfl
    unfold evalSetDiscriminantM
    rw [hp, ok_bind]
    dsimp only [twoVarEnumMrTy]
    rw [hal]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [hMap0]
    simp only [encodeDiscriminantM, List.foldlM_cons, List.foldlM_nil, ok_bind, pure, Except.pure,
      bind, Except.bind]
    rw [hEnc0]
    dsimp only []
    rw [show ((0 : Nat) : Int) = 0 from rfl, hoff]
    dsimp only []
    rw [hst]
  · have hEnc1 : Type.encodeIntM (M := M) ⟨.Unsigned, ⟨1⟩⟩ (.Int 1) =
        .ok [.Init (UInt8.ofNat 1) none] := rfl
    have hMap1 : mapGet twoVarEnumVariants (Int.ofNat 1) =
        some ⟨.Tuple [(⟨4⟩, u32MrTy)] ⟨⟨8⟩, ⟨4⟩, none⟩ none,
              ⟨[(⟨0⟩, (⟨.Unsigned, ⟨1⟩⟩, 1))]⟩⟩ := rfl
    unfold evalSetDiscriminantM
    rw [hp, ok_bind]
    dsimp only [twoVarEnumMrTy]
    rw [hal]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [hMap1]
    simp only [encodeDiscriminantM, List.foldlM_cons, List.foldlM_nil, ok_bind, pure, Except.pure,
      bind, Except.bind]
    rw [hEnc1]
    dsimp only []
    rw [show ((0 : Nat) : Int) = 0 from rfl, hoff]
    dsimp only []
    rw [hst]

/-! ### C1 Concrete Positive, Deref, `.uninit`, and Fault Witnesses (`Mach` &
`MachTB`) -/

def c1SetDiscrLocalMir : MirAst.CapturedMir :=
  mkMirBody "ep2::c1_set_discr_local"
    [mkDecl twoVarMirTy, mkDecl twoVarMirTy] 1
    [mkBb [mkSt (.setDiscriminant (locPlace 1) 1)] .return_]
    twoVarLayouts

def c1SetDiscrLocalMrFn : Gen.Function :=
  mkMrFn [(localName 0, twoVarEnumMrTy), (localName 1, twoVarEnumMrTy)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[.SetDiscriminant (.Local (localName 1)) 1], .Return, .Regular⟩)]

def c1SetDiscrLocalProg : Gen.Program :=
  mkMrProg [(fnName 0, c1SetDiscrLocalMrFn)]

def c1LocalInitBytes : List Byte :=
  [.Init 0 none, .Uninit, .Uninit, .Uninit,
   .Init 42 none, .Init 0 none, .Init 0 none, .Init 0 none]

def c1LocalExpectedBytes : List Byte :=
  [.Init 1 none, .Uninit, .Uninit, .Uninit,
   .Init 42 none, .Init 0 none, .Init 0 none, .Init 0 none]

def c1LocalMach : Mach :=
  let alloc0 := mkStackAlloc 128 (List.replicate 8 .Uninit) 4
  let alloc1 := mkStackAlloc 256 c1LocalInitBytes 4
  let fr : Frame :=
    { func := c1SetDiscrLocalMrFn
      locals := ⟨[(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
                  (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]⟩
      stack_pop_action := .BottomOfStack
      next_block := bbName 0, next_stmt := 0, extra := () }
  mkMrMach c1SetDiscrLocalProg [alloc0, alloc1] [fr]

/-- **C1 Concrete Positive Witness
(`c1_setDiscriminant_local_three_way_witness`)**:
On `stepMirFn`, `Interp.step` (`Mach`), and `Interp.stepTB` (`MachTB`),
`SetDiscriminant` updates ONLY the tag (`0 → 1`) while preserving payload `42`.
-/
theorem c1_setDiscriminant_local_three_way_witness :
    let s0 : MachineState :=
      initMachineState c1SetDiscrLocalMir [.aggregate 0 [.scalar ⟨42, 4⟩]]
    (match stepMirFn c1SetDiscrLocalMir s0 with
     | .tau (.running s1) =>
       s1.frame.stmtIdx = 1 ∧
       get? s1.frame.locals 1 = some (.init (.aggregate 1 [.scalar ⟨42, 4⟩]))
     | _ => False) ∧
    (∃ m1, Interp.step c1LocalMach = .ok m1 ∧
      (m1.mem.memory.allocations[1]?.map (·.data),
       m1.threads[0]?.bind (fun t => t.stack[0]?.map (·.next_stmt))) =
      (some c1LocalExpectedBytes, some 1)) ∧
    (∃ m1, Interp.stepTB (liftMachToTB c1LocalMach) = .ok m1 ∧
      (m1.mem.memory.mem.allocations[1]?.map (fun a => a.data.map projByteTB),
       m1.threads[0]?.bind (fun t => t.stack[0]?.map (·.next_stmt))) =
      (some (c1LocalExpectedBytes.map (projByteTB ∘ liftByteTB)), some 1)) :=
  ⟨⟨rfl, rfl⟩,
   ok_of_map_toOption (by decide +kernel),
   ok_of_map_toOption (by decide +kernel)⟩

/-- Concrete deref `SetDiscriminant` witness (`(*_2) = variant 1`) across
Trusted,
`Mach`, and `MachTB` (verifying payload preservation through a pointer deref).
-/
def c1DerefMir : MirAst.CapturedMir :=
  let ptrDecl := mkDecl { kind := .rawPtr .mut twoVarMirTy.kind, layoutIdx := 0 }
  mkMirBody "ep2::c1_set_discr_deref"
    [mkDecl twoVarMirTy, mkDecl twoVarMirTy, ptrDecl] 1
    [mkBb
      [mkSt (.storageLive 2),
       mkSt (.assign (locPlace 2) (.rawPtr .mut (locPlace 1))),
       mkSt (.setDiscriminant (locPlace 2 [.deref]) 1)]
      .return_]
    twoVarLayouts

def c1DerefMrFn : Gen.Function :=
  mkMrFn [(localName 0, twoVarEnumMrTy), (localName 1, twoVarEnumMrTy),
          (localName 2, thinRawPtrTy)]
    [localName 1] (localName 0)
    [(bbName 0,
      ⟨[.Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (.Raw .None)),
        .SetDiscriminant (.Deref (.Load (.Local (localName 2))) twoVarEnumMrTy) 1],
       .Return, .Regular⟩)]

def c1DerefMach : Mach :=
  let prog := mkMrProg [(fnName 0, c1DerefMrFn)]
  let alloc0 := mkStackAlloc 128 (List.replicate 8 .Uninit) 4
  let alloc1 := mkStackAlloc 256 c1LocalInitBytes 4
  let alloc2 := mkStackAlloc 384 (List.replicate 8 .Uninit) 8
  let fr : Frame :=
    { func := c1DerefMrFn
      locals := ⟨[(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
                  (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) }),
                  (localName 2, { addr := 384, provenance := some (⟨2⟩, ()) })]⟩
      stack_pop_action := .BottomOfStack, next_block := bbName 0, next_stmt := 0, extra := () }
  mkMrMach prog [alloc0, alloc1, alloc2] [fr]

theorem c1_setDiscriminant_deref_three_way_witness :
    let s0 := initMachineState c1DerefMir [.aggregate 0 [.scalar ⟨42, 4⟩]]
    (match stepMirFn c1DerefMir s0 with
     | .tau (.running s1) =>
       match stepMirFn c1DerefMir s1 with
       | .tau (.running s2) =>
         match stepMirFn c1DerefMir s2 with
         | .tau (.running s3) =>
           s3.frame.stmtIdx = 3 ∧
           get? s3.frame.locals 1 = some (.init (.aggregate 1 [.scalar ⟨42, 4⟩]))
         | _ => False
       | _ => False
     | _ => False) ∧
    (∃ m2, Interp.steps 2 c1DerefMach = .ok m2 ∧
      m2.mem.memory.allocations[1]?.map (·.data) = some c1LocalExpectedBytes) ∧
    (∃ m2, Interp.stepsTB 2 (liftMachToTB c1DerefMach) = .ok m2 ∧
      m2.mem.memory.mem.allocations[1]?.map (fun a => a.data.map projByteTB) =
        some (c1LocalExpectedBytes.map (projByteTB ∘ liftByteTB))) :=
  ⟨⟨rfl, rfl⟩,
   ok_of_map_toOption (by decide +kernel),
   ok_of_map_toOption (by decide +kernel)⟩

/-- Concrete `.uninit` shell witness for C1 across Trusted, `Mach`, and
`MachTB`. -/
def c1UninitMach : Mach :=
  let alloc0 := mkStackAlloc 128 (List.replicate 8 .Uninit) 4
  let alloc1 := mkStackAlloc 256 (List.replicate 8 .Uninit) 4
  let fr : Frame :=
    { func := c1SetDiscrLocalMrFn
      locals := ⟨[(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
                  (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]⟩
      stack_pop_action := .BottomOfStack, next_block := bbName 0, next_stmt := 0, extra := () }
  mkMrMach c1SetDiscrLocalProg [alloc0, alloc1] [fr]

theorem c1_setDiscriminant_uninit_shell_witness :
    let s0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] }
        memory := (initMachineState c1SetDiscrLocalMir []).memory }
    (match stepMirFn c1SetDiscrLocalMir s0 with
     | .tau (.running s1) => get? s1.frame.locals 1 = some (.init (.aggregate 1 []))
     | _ => False) ∧
    (∃ m1, Interp.step c1UninitMach = .ok m1 ∧
      m1.mem.memory.allocations[1]?.map (·.data) =
        some (.Init 1 none :: List.replicate 7 .Uninit)) ∧
    Type.decode twoVarEnumMrTy (.Init 1 none :: List.replicate 7 .Uninit) = .ok none ∧
    (∃ m1, Interp.stepTB (liftMachToTB c1UninitMach) = .ok m1 ∧
      m1.mem.memory.mem.allocations[1]?.map (fun a => a.data.map projByteTB) =
        some (TBByteOutcome.initNoProv 1 :: List.replicate 7 TBByteOutcome.uninit)) :=
  ⟨rfl,
   ok_of_map_toOption (by decide +kernel),
   rfl,
   ok_of_map_toOption (by decide +kernel)⟩

/-- Concrete dead-local UB witness for C1 across Trusted, `Mach`, and `MachTB`.
-/
def c1DeadLocalMach : Mach :=
  let alloc0 := mkStackAlloc 128 (List.replicate 8 .Uninit) 4
  let fr : Frame :=
    { func := c1SetDiscrLocalMrFn
      locals := ⟨[(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]⟩
      stack_pop_action := .BottomOfStack, next_block := bbName 0, next_stmt := 0, extra := () }
  mkMrMach c1SetDiscrLocalProg [alloc0] [fr]

theorem c1_setDiscriminant_dead_local_ub_witness :
    let s0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .dead] }
        memory := (initMachineState c1SetDiscrLocalMir []).memory }
    stepMirFn c1SetDiscrLocalMir s0 = MirStepNode.fail .ub ∧
    Interp.step c1DeadLocalMach = .error (.ub "access to a dead local") ∧
    Interp.stepTB (liftMachToTB c1DeadLocalMach) = .error (.ub "access to a dead local") :=
  ⟨rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel)⟩

/-- Concrete misaligned-pointer & frozen-borrow UB witness for C1 across
Trusted,
`Mach`, and `MachTB`. -/
def c1MisalignedMach : Mach :=
  let fn := mkMrFn [(localName 0, twoVarEnumMrTy), (localName 1, thinRawPtrTy)]
    [] (localName 0)
    [(bbName 0,
      ⟨[.SetDiscriminant (.Deref (.Constant (.PointerWithoutProvenance 257) thinRawPtrTy)
          twoVarEnumMrTy) 1], .Return, .Regular⟩)]
  let alloc0 := mkStackAlloc 128 (List.replicate 8 .Uninit) 4
  let alloc1 := mkStackAlloc 256 c1LocalInitBytes 4
  let fr : Frame :=
    { func := fn
      locals := ⟨[(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]⟩
      stack_pop_action := .BottomOfStack, next_block := bbName 0, next_stmt := 0, extra := () }
  mkMrMach (mkMrProg [(fnName 0, fn)]) [alloc0, alloc1] [fr]

theorem c1_setDiscriminant_misaligned_and_frozen_ub_witness :
    let sFrozen : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 2,
                   locals := [.uninit, .init (.aggregate 0 [.scalar ⟨42, 4⟩]),
                              .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] }
        memory :=
          { (initMachineState c1DerefMir []).memory with
            borrows := [{ tag := 1, targetLocal := 1, targetProjection := [],
                          perm := .frozen, targetFrameDepth := 0 }] } }
    stepMirFn c1DerefMir sFrozen = MirStepNode.fail .ub ∧
    Interp.step c1MisalignedMach =
      .error (.ub "setting the discriminant of a place based on a misaligned pointer") ∧
    Interp.stepTB (liftMachToTB c1MisalignedMach) =
      .error (.ub "setting the discriminant of a place based on a misaligned pointer") :=
  ⟨rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel)⟩

/-! ## §2 (`C2`): `TerminatorKind.unwindResume` (`Mach` & `MachTB`) -/

/-- **C2 Fragment Boundary (`translateTerminator_unwindResume_none`)**:
`Translate.translateTerminator` rejects `.unwindResume`. -/
theorem translateTerminator_unwindResume_none
    (layouts : LayoutTable) (decls : List MirAst.LocalDecl) (span : String) :
    translateTerminator layouts decls { kind := .unwindResume, span := span } = none :=
  rfl

/-- **C2a Trusted `.cleanup` Step Law**: popping a callee whose caller
registered
`.cleanup cleanupBb` restores `caller.frame` at `(cleanupBb, 0)`, restores
`caller`'s protectors, and disables callee-frame borrows above `length rest`. -/
theorem trusted_unwindResume_cleanup_step
    (s : MachineState) (caller : SavedCallerFrame) (rest : List SavedCallerFrame)
    (cleanupBb : Nat) (span : String) (curBody : Option CapturedMir)
    (hStack : s.memory.callStack = caller :: rest)
    (hAction : caller.returnUnwind = .cleanup cleanupBb) :
    MirSemantics.evalTerminator s { kind := .unwindResume, span := span } curBody =
      MirStepNode.step {
        frame := { caller.frame with blockIdx := cleanupBb, stmtIdx := 0 }
        memory := {
          s.memory with
          callStack := rest
          activeCallee := .some caller.callerBody
          activeProtectors := restoreCallerProtectors caller
          borrows := disableFramesAbove s.memory.borrows (length rest)
        }
      } := by
  simp only [MirSemantics.evalTerminator, hStack, unwindFromCallStack, hAction]

/-- **C2b Trusted `.continue_` Multi-Frame Big-Step Law**: skipping `k`
intermediate `.continue_` caller frames in `unwindFromCallStack` reduces in ONE
Trusted step to `unwindFromCallStack` on the remaining stack. -/
theorem trusted_unwindFromCallStack_continue_chain :
    ∀ (conts : List SavedCallerFrame) (tail : List SavedCallerFrame) (mem : MirSemantics.Memory),
      (∀ c ∈ conts, c.returnUnwind = .continue_) →
      ∃ mem',
        mem'.callStack = tail ∧
        unwindFromCallStack (conts ++ tail) mem = unwindFromCallStack tail mem'
  | [], tail, mem, _ =>
    ⟨{ mem with callStack := tail }, rfl, by
      cases tail <;> simp [unwindFromCallStack]⟩
  | c :: cs, tail, mem, hcont => by
    have hc : c.returnUnwind = .continue_ := hcont c (List.mem_cons_self ..)
    have hcs : ∀ x ∈ cs, x.returnUnwind = .continue_ :=
      fun x hx => hcont x (List.mem_cons_of_mem c hx)
    simp only [List.cons_append, unwindFromCallStack, hc]
    exact trusted_unwindFromCallStack_continue_chain cs tail _ hcs

/-- **C2c Trusted `.unreachable` UB Law**: unwinding into `.unreachable` faults
with `MirStepNode.fail .ub`. -/
theorem trusted_unwindResume_unreachable_ub
    (s : MachineState) (caller : SavedCallerFrame) (rest : List SavedCallerFrame)
    (span : String) (curBody : Option CapturedMir)
    (hStack : s.memory.callStack = caller :: rest)
    (hAction : caller.returnUnwind = .unreachable) :
    MirSemantics.evalTerminator s { kind := .unwindResume, span := span } curBody =
      MirStepNode.fail .ub := by
  simp only [MirSemantics.evalTerminator, hStack, unwindFromCallStack, hAction]

/-- **C2d Trusted `.terminate` Abort Law**: unwinding into `.terminate` halts
with
`MirStepNode.retOutcome .abort`. -/
theorem trusted_unwindResume_terminate_abort
    (s : MachineState) (caller : SavedCallerFrame) (rest : List SavedCallerFrame)
    (span : String) (curBody : Option CapturedMir)
    (hStack : s.memory.callStack = caller :: rest)
    (hAction : caller.returnUnwind = .terminate) :
    MirSemantics.evalTerminator s { kind := .unwindResume, span := span } curBody =
      MirStepNode.retOutcome .abort := by
  simp only [MirSemantics.evalTerminator, hStack, unwindFromCallStack, hAction]

/-- **C2e Root-Frame Explicit Divergence
(`unwindResume_root_panic_vs_ub_divergence`)**:
At the root frame (`callStack = []` in Trusted; `stack_pop_action =
.BottomOfStack`
in MiniRust):
1. Trusted `evalTerminator ... .unwindResume` returns `MirStepNode.retOutcome
   .panic`
   (halted panic, NOT `.fail .ub`).
2. MiniRust `evalResumeUnwindM` (covering BOTH `Mach` and `MachTB` via
   `stepM_bm_eq`)
   raises `.error (.ub "the function at the bottom of the stack must not
   unwind")`. -/
theorem unwindResume_root_panic_vs_ub_divergence
    {M : Type} [Gen.Memory M] [MemoryOps M]
    (s : MachineState) (span : String) (curBody : Option CapturedMir)
    (hRoot : s.memory.callStack = [])
    (m : Machine M) (t : Gen.Thread M) (fr fr1 : StackFrame M)
    (threads' : List (Gen.Thread M)) (cm1 cm2 : Gen.ConcurrentMemory M)
    (ht : activeThreadM m = .ok t)
    (hlast : t.stack.getLast? = some fr)
    (hset : listSet m.threads m.active_thread { t with stack := t.stack.dropLast } "pop" =
      .ok threads')
    (hdealloc : deallocAllM fr.locals.entries.length fr m.mem = .ok (fr1, cm1))
    (hend : ConcurrentMemory.end_call cm1 fr1.extra = .ok cm2)
    (hbot : fr1.stack_pop_action = .BottomOfStack) :
    MirSemantics.evalTerminator s { kind := .unwindResume, span := span } curBody =
      MirStepNode.retOutcome .panic ∧
    evalResumeUnwindM m =
      .error (.ub "the function at the bottom of the stack must not unwind") := by
  constructor
  · simp only [MirSemantics.evalTerminator, hRoot, unwindFromCallStack]
  · unfold evalResumeUnwindM
    simp only [ht, hlast, hset, hdealloc, hend, hbot,
      pure, Except.pure, bind, Except.bind, ub]

/-- **C2 MiniRust Polymorphic `BackToCaller` Law (`Mach` & `MachTB`)**:
When popping a callee frame with `BackToCaller nextBlock unwindBlock retPtr`:
1. `unwindBlock = some ubBb` jumps to `ubBb` in the caller (preserving
   `thread.unwind_payloads`, and on `MachTB` releasing the callee's protectors
   and preserving `MachTB.wfLive`).
2. `unwindBlock = none` raises UB
   (`"unwinding from a function where the caller did not specify an
   unwind_block"`). -/
theorem minirust_evalResumeUnwindM_backToCaller
    {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Machine M) (t : Gen.Thread M) (fr fr1 : StackFrame M)
    (threads' : List (Gen.Thread M)) (cm1 cm2 : Gen.ConcurrentMemory M)
    (nextBlock : Option Gen.BbName) (unwindBlock : Option Gen.BbName)
    (retPtr : ThinPointer (Gen.Memory.Provenance M))
    (ht : activeThreadM m = .ok t)
    (hlast : t.stack.getLast? = some fr)
    (hset : listSet m.threads m.active_thread { t with stack := t.stack.dropLast } "pop" =
      .ok threads')
    (hdealloc : deallocAllM fr.locals.entries.length fr m.mem = .ok (fr1, cm1))
    (hend : ConcurrentMemory.end_call cm1 fr1.extra = .ok cm2)
    (hact : fr1.stack_pop_action = .BackToCaller nextBlock unwindBlock retPtr) :
    (∀ ubBb, unwindBlock = some ubBb →
      evalResumeUnwindM m = jumpToBlockM { { m with threads := threads' } with mem := cm2 } ubBb) ∧
    (unwindBlock = none →
      evalResumeUnwindM m =
        .error (.ub "unwinding from a function where the caller did not specify an unwind_block")) := by
  constructor
  · intro ubBb hEq
    unfold evalResumeUnwindM
    simp only [ht, hlast, hset, hdealloc, hend, hact, hEq,
      pure, Except.pure, bind, Except.bind]
  · intro hEq
    unfold evalResumeUnwindM
    simp only [ht, hlast, hset, hdealloc, hend, hact, hEq,
      pure, Except.pure, bind, Except.bind, ub]

/-- **`Translate.translateUnwindAction` Lowering Spec**: connects every MIR
`UnwindAction` constructor directly to its MiniRust cleanup-block terminator. -/
theorem translateUnwindAction_cases (nextCleanup : Nat) (cb : Nat) :
    translateUnwindAction nextCleanup .continue_ =
      (bbName nextCleanup, nextCleanup + 1,
        [(bbName nextCleanup, ⟨[], .ResumeUnwind, .Cleanup⟩)]) ∧
    translateUnwindAction nextCleanup .unreachable =
      (bbName nextCleanup, nextCleanup + 1,
        [(bbName nextCleanup, ⟨[], .Unreachable, .Cleanup⟩)]) ∧
    translateUnwindAction nextCleanup .terminate =
      (bbName nextCleanup, nextCleanup + 1,
        [(bbName nextCleanup, ⟨[], buildAbort, .Cleanup⟩)]) ∧
    translateUnwindAction nextCleanup (.cleanup cb) = (bbName cb, nextCleanup, []) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### C2 Concrete Witnesses: `.cleanup`, `.continue_` Multi-Frame,
`.unreachable`,
### `.terminate`, Root Divergence, `StartUnwind -> ResumeUnwind -> StopUnwind`,
### and
### `MachTB` Protector Release -/

def c2LeafMir : MirAst.CapturedMir :=
  mkMirBody "ep2::c2_leaf" [mkDecl unitMirTy] 0 [mkBb [] .unwindResume true]

def c2CallerMir : MirAst.CapturedMir :=
  mkMirBody "ep2::c2_caller" [mkDecl u32MirTy] 0
    [mkBb [] (.goto 1),
     mkBb [mkSt (.assign (locPlace 0) (.use (constU32 77)))] .return_ true]

def c2LeafMrFn : Gen.Function :=
  mkMrFn [] [] (localName 0) [(bbName 0, ⟨[], .ResumeUnwind, .Cleanup⟩)]

def c2MidContinueMrFn : Gen.Function :=
  mkMrFn [] [] (localName 0) [(bbName 0, ⟨[], .ResumeUnwind, .Cleanup⟩)]

def c2CallerMrFn : Gen.Function :=
  mkMrFn [(localName 0, u32MrTy)] [] (localName 0)
    [(bbName 0, ⟨[], .Goto (bbName 1), .Regular⟩),
     (bbName 1, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 77) u32MrTy)],
                 .Return, .Cleanup⟩),
     (bbName 2, ⟨[], .Unreachable, .Cleanup⟩),
     (bbName 3, ⟨[], buildAbort, .Cleanup⟩)]

def c2Prog : Gen.Program :=
  mkMrProg [(fnName 0, c2CallerMrFn), (fnName 1, c2MidContinueMrFn), (fnName 2, c2LeafMrFn)]

def c2MkStackMach (unwindActionBb : Option Gen.BbName) (withMidContinue : Bool := false)
    (payloads : List Ptr := []) : Mach :=
  let alloc0 := mkStackAlloc 128 (List.replicate 4 .Uninit) 4
  let rootFr : Frame :=
    { func := c2CallerMrFn
      locals := ⟨[(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]⟩
      stack_pop_action := .BottomOfStack, next_block := bbName 0, next_stmt := 0, extra := () }
  let midFr : Frame :=
    { func := c2MidContinueMrFn, locals := ⟨[]⟩
      stack_pop_action := .BackToCaller none unwindActionBb dummyRetPtr
      next_block := bbName 0, next_stmt := 0, extra := () }
  let leafFr : Frame :=
    { func := c2LeafMrFn, locals := ⟨[]⟩
      stack_pop_action :=
        if withMidContinue then .BackToCaller none (some (bbName 0)) dummyRetPtr
        else .BackToCaller none unwindActionBb dummyRetPtr
      next_block := bbName 0, next_stmt := 0, extra := () }
  let stack := if withMidContinue then [rootFr, midFr, leafFr] else [rootFr, leafFr]
  mkMrMach c2Prog [alloc0] stack [] [] payloads

/-- **C2 Concrete Witness covering ALL 5 regimes on Trusted, `Mach`, and
`MachTB`**. -/
theorem c2_unwindResume_all_five_regimes_witness :
    let callerBase (ua : UnwindAction) : SavedCallerFrame :=
      { callerBody := c2CallerMir
        frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }
        destination := locPlace 0
        returnTarget := 0
        returnUnwind := ua }
    let sWith (cs : List SavedCallerFrame) : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }
        memory := { (initMachineState c2LeafMir []).memory with callStack := cs } }
    let rootLeafMach :=
      mkMrMach c2Prog []
        [{ func := c2LeafMrFn, locals := ⟨[]⟩, stack_pop_action := .BottomOfStack,
           next_block := bbName 0, next_stmt := 0, extra := () }]
    -- (a) .cleanup 1
    (match stepMirFn c2LeafMir (sWith [callerBase (.cleanup 1)]) with
     | .tau (.running s1) => s1.frame.blockIdx = 1 ∧ s1.memory.callStack = []
     | _ => False) ∧
    (∃ m1, Interp.step (c2MkStackMach (some (bbName 1))) = .ok m1 ∧
      m1.threads[0]?.map (fun t => (t.stack.length, t.stack[0]?.map (·.next_block))) =
        some (1, some (bbName 1))) ∧
    (∃ m1, Interp.stepTB (liftMachToTB (c2MkStackMach (some (bbName 1)))) = .ok m1 ∧
      m1.threads[0]?.map (fun t => (t.stack.length, t.stack[0]?.map (·.next_block))) =
        some (1, some (bbName 1))) ∧
    -- (b) .continue_ chain (1 Trusted step ↔ 2 MiniRust steps)
    (match stepMirFn c2LeafMir (sWith [callerBase .continue_, callerBase (.cleanup 1)]) with
     | .tau (.running s1) => s1.frame.blockIdx = 1 ∧ s1.memory.callStack = []
     | _ => False) ∧
    (∃ m2, Interp.steps 2 (c2MkStackMach (some (bbName 1)) true) = .ok m2 ∧
      m2.threads[0]?.map (fun t => (t.stack.length, t.stack[0]?.map (·.next_block))) =
        some (1, some (bbName 1))) ∧
    (∃ m2, Interp.stepsTB 2 (liftMachToTB (c2MkStackMach (some (bbName 1)) true)) = .ok m2 ∧
      m2.threads[0]?.map (fun t => (t.stack.length, t.stack[0]?.map (·.next_block))) =
        some (1, some (bbName 1))) ∧
    -- (c) .unreachable UB (direct none & synthetic Unreachable block)
    stepMirFn c2LeafMir (sWith [callerBase .unreachable]) = MirStepNode.fail .ub ∧
    Interp.step (c2MkStackMach none) =
      .error (.ub "unwinding from a function where the caller did not specify an unwind_block") ∧
    Interp.stepTB (liftMachToTB (c2MkStackMach none)) =
      .error (.ub "unwinding from a function where the caller did not specify an unwind_block") ∧
    Interp.steps 2 (c2MkStackMach (some (bbName 2))) = .error (.ub "reached unreachable code") ∧
    Interp.stepsTB 2 (liftMachToTB (c2MkStackMach (some (bbName 2)))) =
      .error (.ub "reached unreachable code") ∧
    -- (d) .terminate abort
    stepMirFn c2LeafMir (sWith [callerBase .terminate]) = MirStepNode.retOutcome .abort ∧
    Interp.steps 2 (c2MkStackMach (some (bbName 3))) = .error .abort ∧
    Interp.stepsTB 2 (liftMachToTB (c2MkStackMach (some (bbName 3)))) = .error .abort ∧
    -- (e) Root-frame divergence: Trusted .panic vs MiniRust BottomOfStack UB
    stepMirFn c2LeafMir (sWith []) = MirStepNode.retOutcome .panic ∧
    Interp.step rootLeafMach =
      .error (.ub "the function at the bottom of the stack must not unwind") ∧
    Interp.stepTB (liftMachToTB rootLeafMach) =
      .error (.ub "the function at the bottom of the stack must not unwind") :=
  ⟨⟨rfl, rfl⟩,
   ok_of_map_toOption (by decide +kernel),
   ok_of_map_toOption (by decide +kernel),
   ⟨rfl, rfl⟩,
   ok_of_map_toOption (by decide +kernel),
   ok_of_map_toOption (by decide +kernel),
   rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   rfl,
   eq_error_abort_of_interpIsAbort (by decide +kernel),
   eq_error_abort_of_interpIsAbort (by decide +kernel),
   rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel)⟩

/-- **C2 `StartUnwind -> ResumeUnwind -> StopUnwind` Composition Witness** on
both
`Mach` and `MachTB` (plus empty-stack `StopUnwind` UB witness). -/
def c2UnwindLifecycleMach : Mach :=
  let calleeFn := mkMrFn [] [] (localName 0)
    [(bbName 0,
      ⟨[], .StartUnwind (.Constant (.PointerWithoutProvenance 4096) thinRawPtrTy) (bbName 1),
       .Regular⟩),
     (bbName 1, ⟨[], .ResumeUnwind, .Cleanup⟩)]
  let callerFn := mkMrFn [] [] (localName 0)
    [(bbName 0, ⟨[], .Goto (bbName 0), .Regular⟩),
     (bbName 1, ⟨[], .StopUnwind (bbName 2), .Cleanup⟩),
     (bbName 2, ⟨[], .Return, .Regular⟩)]
  let prog := mkMrProg [(fnName 0, callerFn), (fnName 1, calleeFn)]
  let callerFr : Frame :=
    { func := callerFn, locals := ⟨[]⟩, stack_pop_action := .BottomOfStack,
      next_block := bbName 0, next_stmt := 0, extra := () }
  let calleeFr : Frame :=
    { func := calleeFn, locals := ⟨[]⟩,
      stack_pop_action := .BackToCaller (some (bbName 0)) (some (bbName 1)) dummyRetPtr,
      next_block := bbName 0, next_stmt := 0, extra := () }
  mkMrMach prog [] [callerFr, calleeFr]

def c2StopUnwindEmptyMach : Mach :=
  let fn := mkMrFn [] [] (localName 0)
    [(bbName 0, ⟨[], .StopUnwind (bbName 1), .Cleanup⟩),
     (bbName 1, ⟨[], .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)]) []
    [{ func := fn, locals := ⟨[]⟩, stack_pop_action := .BottomOfStack,
       next_block := bbName 0, next_stmt := 0, extra := () }]

theorem c2_start_resume_stop_unwind_composition_witness :
    (∃ m1, Interp.step c2UnwindLifecycleMach = .ok m1 ∧
      m1.threads[0]?.map (fun t => (t.stack.length, t.unwind_payloads.map (·.addr))) =
        some (2, [4096])) ∧
    (∃ m2, Interp.steps 2 c2UnwindLifecycleMach = .ok m2 ∧
      m2.threads[0]?.map (fun t =>
        (t.stack.length, t.stack[0]?.map (·.next_block), t.unwind_payloads.map (·.addr))) =
        some (1, some (bbName 1), [4096])) ∧
    (∃ m3, Interp.steps 3 c2UnwindLifecycleMach = .ok m3 ∧
      m3.threads[0]?.map (fun t =>
        (t.stack.length, t.stack[0]?.map (·.next_block), t.unwind_payloads.length)) =
        some (1, some (bbName 2), 0)) ∧
    (∃ m3, Interp.stepsTB 3 (liftMachToTB c2UnwindLifecycleMach) = .ok m3 ∧
      m3.threads[0]?.map (fun t =>
        (t.stack.length, t.stack[0]?.map (·.next_block), t.unwind_payloads.length)) =
        some (1, some (bbName 2), 0)) ∧
    Interp.step c2StopUnwindEmptyMach = .error (.ub "StopUnwind: the payload stack is empty") ∧
    Interp.stepTB (liftMachToTB c2StopUnwindEmptyMach) =
      .error (.ub "StopUnwind: the payload stack is empty") :=
  ⟨ok_of_map_toOption (by decide +kernel),
   ok_of_map_toOption (by decide +kernel),
   ok_of_map_toOption (by decide +kernel),
   ok_of_map_toOption (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel)⟩

/-- **C2 `MachTB` Protector Release on `ResumeUnwind` Witness**:
Callee runs `Validate (.Local 1) true` (installing a Tree Borrows protector on
the caller's `u32` allocation via `&mut u32` arg `_1`), then unwinds via
`ResumeUnwind`; `end_call` releases the callee's protector so caller cleanup
writes `99` without protector UB. -/
def c2TbProtectorUnwindMach : Mach :=
  let refMutU32MrTy : Gen.Type := refTy .mut u32
  let calleeFn := mkMrFn [(localName 0, unitType), (localName 1, refMutU32MrTy)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[.Validate (.Local (localName 1)) true], .ResumeUnwind, .Regular⟩)]
  let callerFn := mkMrFn [(localName 0, u32MrTy)] [] (localName 0)
    [(bbName 0, ⟨[], .Goto (bbName 1), .Regular⟩),
     (bbName 1,
       ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 99) u32MrTy)], .Return, .Cleanup⟩)]
  let prog := mkMrProg [(fnName 0, callerFn), (fnName 1, calleeFn)]
  let alloc0 := mkStackAlloc 128 (scalarBytes u32 5) 4
  let alloc1 := mkStackAlloc 256 (ptrBytes 128 (some (⟨0⟩, ()))) 8
  let callerFr : Frame :=
    { func := callerFn
      locals := ⟨[(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]⟩
      stack_pop_action := .BottomOfStack, next_block := bbName 0, next_stmt := 0, extra := () }
  let calleeFr : Frame :=
    { func := calleeFn
      locals := ⟨[(localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]⟩
      stack_pop_action := .BackToCaller (some (bbName 0)) (some (bbName 1)) dummyRetPtr
      next_block := bbName 0, next_stmt := 0, extra := () }
  mkMrMach prog [alloc0, alloc1] [callerFr, calleeFr]

theorem c2_machTB_protector_release_on_resumeUnwind_witness :
    ∃ m3, Interp.stepsTB 3 (liftMachToTB c2TbProtectorUnwindMach) = .ok m3 ∧
      (m3.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB)),
       m3.mem.memory.mem.allocations[1]?.map (·.live)) =
      (some (true, (scalarBytes u32 99).map (projByteTB ∘ liftByteTB)), some false) :=
  ok_of_map_toOption (by decide +kernel)

/-! ## §3 (`C3`): `TerminatorKind.unwindTerminate` (`Mach` & `MachTB`) -/

/-- **C3 Fragment Boundary (`translateTerminator_unwindTerminate_none`)**:
`Translate.translateTerminator` rejects `.unwindTerminate`. -/
theorem translateTerminator_unwindTerminate_none
    (layouts : LayoutTable) (decls : List MirAst.LocalDecl) (span : String) :
    translateTerminator layouts decls { kind := .unwindTerminate, span := span } = none :=
  rfl

/-- **C3 Universal Lockstep Abort Simulation (`Mach` & `MachTB`)**:
For EVERY Trusted state `s` and EVERY MiniRust `Machine M` (covering both `Mach`
and `MachTB` unconditionally):
- Trusted `evalTerminator s ⟨.unwindTerminate, span⟩` returns
  `MirStepNode.retOutcome .abort`.
- MiniRust `evalTerminatorM m buildAbort` returns `.error .abort`
  (`Stop.abort`). -/
theorem unwindTerminate_lockstep_abort_M
    {M : Type} [Gen.Memory M] [MemoryOps M]
    (s : MachineState) (span : String) (curBody : Option CapturedMir) (m : Machine M) :
    MirSemantics.evalTerminator s { kind := .unwindTerminate, span := span } curBody =
      MirStepNode.retOutcome .abort ∧
    evalTerminatorM m buildAbort = .error .abort := by
  refine ⟨rfl, ?_⟩
  unfold evalTerminatorM buildAbort abortTerminator
  dsimp only []
  rw [evalPlaceM_unitPlace, ok_bind]
  rfl

/-- **C3 `BasicMemory` (`Mach`) & `TreeBorrowsMemory` (`MachTB`)
Specialization**. -/
theorem unwindTerminate_lockstep_abort_mach_and_tb
    (s : MachineState) (span : String) (curBody : Option CapturedMir)
    (m : Mach) (mtb : MachTB) :
    MirSemantics.evalTerminator s { kind := .unwindTerminate, span := span } curBody =
      MirStepNode.retOutcome .abort ∧
    Interp.evalTerminator m buildAbort = .error .abort ∧
    evalTerminatorM mtb buildAbort = .error .abort := by
  refine ⟨rfl, ?_, (unwindTerminate_lockstep_abort_M s span curBody mtb).2⟩
  rw [← evalTerminatorM_bm_eq]
  exact (unwindTerminate_lockstep_abort_M s span curBody m).2

/-- Concrete C3 witness across `stepMirFn`, `Interp.step`, and `Interp.stepTB`.
-/
def c3UnwindTerminateMir : MirAst.CapturedMir :=
  mkMirBody "ep2::c3_unwind_terminate" [mkDecl unitMirTy] 0
    [mkBb [] .unwindTerminate true]

def c3AbortMach : Mach :=
  let fn := mkMrFn [] [] (localName 0) [(bbName 0, ⟨[], buildAbort, .Cleanup⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)]) []
    [{ func := fn, locals := ⟨[]⟩, stack_pop_action := .BottomOfStack,
       next_block := bbName 0, next_stmt := 0, extra := () }]

theorem c3_unwindTerminate_three_way_witness :
    stepMirFn c3UnwindTerminateMir (initMachineState c3UnwindTerminateMir []) =
      MirStepNode.retOutcome .abort ∧
    Interp.step c3AbortMach = .error .abort ∧
    Interp.stepTB (liftMachToTB c3AbortMach) = .error .abort :=
  ⟨rfl,
   eq_error_abort_of_interpIsAbort (by decide +kernel),
   eq_error_abort_of_interpIsAbort (by decide +kernel)⟩

/-! ## §4 (`C4`): `StatementKind.coverage` (Stuttering Equivalence on `Mach` &
`MachTB`) -/

/-- **C4 Fragment Boundary (`translateStatement_coverage_none`)**:
`Translate.translateStatement` returns `none` on `StatementKind.coverage`. -/
theorem translateStatement_coverage_none
    (decls : List MirAst.LocalDecl) (span : String) (layouts : LayoutTable) :
    translateStatement decls { kind := .coverage, span := span } layouts = none :=
  rfl

/-- **C4 Universal Stuttering Equivalence (`coverage_stuttering_step`)**:
`minimize` drops `StatementKind::Coverage` (`0` MiniRust statements emitted).
Trusted advances ONLY `stmtIdx` by `1` with identical `locals` and `memory`,
matching `0` MiniRust steps on `Mach` and `MachTB`. -/
theorem coverage_stuttering_step
    (s : MachineState) (span : String) (decls : List MirAst.LocalDecl)
    (layouts : LayoutTable) (m : Mach) (mtb : MachTB) :
    evalStmt s { kind := .coverage, span := span } decls layouts =
      MirStepNode.step (advanceStmt s s.frame.locals) ∧
    (advanceStmt s s.frame.locals).frame.locals = s.frame.locals ∧
    (advanceStmt s s.frame.locals).memory = s.memory ∧
    Interp.steps 0 m = .ok m ∧
    Interp.stepsTB 0 mtb = .ok mtb :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

def c4CoverageMir : MirAst.CapturedMir :=
  mkMirBody "ep2::c4_coverage" [mkDecl u32MirTy] 0
    [mkBb [mkSt .coverage, mkSt (.assign (locPlace 0) (.use (constU32 17)))] .return_]

def c4ErasedMir : MirAst.CapturedMir :=
  mkMirBody "ep2::c4_erased" [mkDecl u32MirTy] 0
    [mkBb [mkSt (.assign (locPlace 0) (.use (constU32 17)))] .return_]

theorem c4_coverage_stuttering_three_way_witness :
    let s0 := initMachineState c4CoverageMir []
    (match stepMirFn c4CoverageMir s0 with
     | .tau (.running s1) =>
       s1.frame.stmtIdx = 1 ∧ s1.frame.locals = s0.frame.locals ∧ s1.memory = s0.memory ∧
       runAVal c4CoverageMir 4 s0 = some (.scalar ⟨17, 4⟩)
     | _ => False) ∧
    retAfter c4ErasedMir [] 3 = some (some (mkStackAlloc 64 (scalarBytes u32 17) 4), [1]) ∧
    retAfterTB c4ErasedMir [] 3 = tbRetU32 17 := by
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

/-! ## §5 (`C5`): `StatementKind.backwardIncompatibleDropHint` (`Mach` &
`MachTB`) -/

/-- **C5 Fragment Boundary
(`translateStatement_backwardIncompatibleDropHint_none`)**:
`Translate.translateStatement` returns `none` on `backwardIncompatibleDropHint`.
-/
theorem translateStatement_backwardIncompatibleDropHint_none
    (decls : List MirAst.LocalDecl) (p : MirAst.Place)
    (span : String) (layouts : LayoutTable) :
    translateStatement decls { kind := .backwardIncompatibleDropHint p, span := span } layouts =
      none :=
  rfl

/-- **C5 Universal Unconditional Stuttering Equivalence**:
`evalStmt` on `.backwardIncompatibleDropHint p` unconditionally advances
`stmtIdx`
with identical `locals` and `memory` without ever reading, dereferencing, or
checking `p` (even on `.dead`, `.uninit`, or OOB places), matching `0` MiniRust
steps on `Mach` and `MachTB`. -/
theorem backwardIncompatibleDropHint_stuttering_step
    (s : MachineState) (p : MirAst.Place) (span : String)
    (decls : List MirAst.LocalDecl) (layouts : LayoutTable) (m : Mach) (mtb : MachTB) :
    evalStmt s { kind := .backwardIncompatibleDropHint p, span := span } decls layouts =
      MirStepNode.step (advanceStmt s s.frame.locals) ∧
    (advanceStmt s s.frame.locals).frame.locals = s.frame.locals ∧
    (advanceStmt s s.frame.locals).memory = s.memory ∧
    Interp.steps 0 m = .ok m ∧
    Interp.stepsTB 0 mtb = .ok mtb :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

def c5DropHintMir : MirAst.CapturedMir :=
  mkMirBody "ep2::c5_drop_hint" [mkDecl u32MirTy, mkDecl rawMutU32MirTy] 0
    [mkBb
      [mkSt (.storageDead 1),
       mkSt (.backwardIncompatibleDropHint (locPlace 1 [.deref])),
       mkSt (.backwardIncompatibleDropHint (locPlace 99)),
       mkSt (.assign (locPlace 0) (.use (constU32 23)))]
      .return_]

def c5ErasedMir : MirAst.CapturedMir :=
  mkMirBody "ep2::c5_erased" [mkDecl u32MirTy] 0
    [mkBb [mkSt (.assign (locPlace 0) (.use (constU32 23)))] .return_]

theorem c5_backwardIncompatibleDropHint_dead_place_no_ub_witness :
    let s0 := initMachineState c5DropHintMir []
    runAVal c5DropHintMir 6 s0 = some (.scalar ⟨23, 4⟩) ∧
    retAfter c5ErasedMir [] 3 = some (some (mkStackAlloc 64 (scalarBytes u32 23) 4), [1]) ∧
    retAfterTB c5ErasedMir [] 3 = tbRetU32 23 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

/-! ## §6 (`C6`): `CastKind.fnPtrToPtr` (`Mach` & `MachTB`) -/

/-- **C6 Fragment Boundary (`translateRvalue_fnPtrToPtr_none`)**:
`Translate.translateRvalue` rejects `.cast .fnPtrToPtr`. -/
theorem translateRvalue_fnPtrToPtr_none
    (layouts : LayoutTable) (decls : List MirAst.LocalDecl) (targetTy : Option MirAst.Ty)
    (op : MirAst.Operand) (dstTy : MirAst.Ty) :
    translateRvalue layouts decls targetTy (.cast .fnPtrToPtr op dstTy) = none :=
  rfl

/-- **C6 Universal Lockstep Simulation (`fnPtrToPtr_lockstep_mach_and_tb`)**:
When Trusted evaluates a valid 8-byte function pointer at `offsetBytes = 0`
(non-stack, non-`rustIntrinsic` ABI) cast via `CastKind.fnPtrToPtr` to a thin
raw pointer `dstTy`:
1. Trusted `evalRvalue` preserves `.ptr p 8` and `mem` unchanged.
2. MiniRust `evalCastOp` (`Mach`) and `evalCastOpM` (`MachTB`) on
   `CastOp.Transmute thinRawPtrTy` preserve `thin` / `thinTB` and their
   function-pointer provenance identically. -/
theorem fnPtrToPtr_lockstep_mach_and_tb
    (locals locals' : List LocalSlot) (op : MirAst.Operand) (dstTy : MirAst.Ty)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr) (addr : Nat) (hAddr : addr < 2 ^ 64)
    (provBM : Option Prov) (provTB : Option TreeBorrowsProvenance)
    (mBM : Option Mach) (mTB : Option MachTB)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.ptr p 8) locals')
    (hDst : isThinRawPtrTy dstTy = true)
    (hSrc : (match operandTy decls layouts op with
             | .none => true
             | .some { kind := .fnPtr _ _ _ abi, .. } => Bool.not (callConvEq abi .rustIntrinsic)
             | .some _ => false) = true)
    (hOff : p.offsetBytes = 0)
    (hNoBorrow : lookupBorrow mem.borrows p.tag = none)
    (hFnAlloc : (match mem.fnPtrs with
                 | .nil => isFnPtrAllocId p.allocId
                 | _ :: _ =>
                   match lookupFnPtr mem.fnPtrs p.allocId with
                   | .some entry =>
                     match entry.fnSig with
                     | .none => true
                     | .some (.fnPtr _ _ _ sigAbi) => Bool.not (callConvEq sigAbi .rustIntrinsic)
                     | .some _ => false
                   | .none => false) = true) :
    evalRvalue locals (.cast .fnPtrToPtr op dstTy) mem decls layouts =
      .ok (.ptr p 8) locals' mem ∧
    evalCastOp (.Transmute thinRawPtrTy)
      (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) mBM =
      .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) ∧
    evalCastOpM (M := TBM) (.Transmute thinRawPtrTy)
      (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) mTB =
      .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) := by
  refine ⟨?_,
    evalCastOp_transmute_thinRawPtr_id addr hAddr provBM mBM,
    evalCastOpM_transmute_thinRawPtr_id (M := TBM) addr hAddr provTB mTB⟩
  show evalFnPtrToPtr locals op dstTy mem decls layouts = _
  unfold evalFnPtrToPtr
  simp only [hOp, hDst, hOff, hNoBorrow, Nat.beq_refl]
  have hBool : ∀ (a b : Bool), a = true → b = true →
      (match Bool.and true (Bool.and a (Bool.and true (Bool.and true b))) with
       | true => RvalueEvalResult.ok (.ptr p 8) locals' mem
       | false => .ub) = .ok (.ptr p 8) locals' mem := by
    intro a b ha hb; subst ha; subst hb; rfl
  exact hBool _ _ hSrc hFnAlloc

/-- **C6 Explicit Characterization of Trusted Extra Checks vs. MiniRust
`Transmute`
(`fnPtrToPtr_extra_checks_divergence`)**:
Unlike MiniRust's type-erased `CastOp.Transmute (.Ptr (.Raw .None))` (which
preserves any in-bounds thin pointer on both `Mach` and `MachTB`), Trusted
`evalFnPtrToPtr` faults with `.ub` whenever:
1. `p.offsetBytes ≠ 0` (nonzero offset on a function pointer),
2. `lookupBorrow mem.borrows p.tag = some entry` (stack-borrowed pointer), or
3. `operandTy` has `CallConv.rustIntrinsic` ABI. -/
theorem fnPtrToPtr_extra_checks_divergence
    (locals locals' : List LocalSlot) (op : MirAst.Operand) (dstTy : MirAst.Ty)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr) (addr : Nat) (hAddr : addr < 2 ^ 64)
    (provBM : Option Prov) (provTB : Option TreeBorrowsProvenance)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.ptr p 8) locals') :
    (p.offsetBytes ≠ 0 →
      evalRvalue locals (.cast .fnPtrToPtr op dstTy) mem decls layouts = .ub) ∧
    (∀ entry, lookupBorrow mem.borrows p.tag = some entry →
      evalRvalue locals (.cast .fnPtrToPtr op dstTy) mem decls layouts = .ub) ∧
    (∀ ins out saf, operandTy decls layouts op =
        some { kind := .fnPtr ins out saf .rustIntrinsic, layoutIdx := 0 } →
      evalRvalue locals (.cast .fnPtrToPtr op dstTy) mem decls layouts = .ub) ∧
    evalCastOp (.Transmute thinRawPtrTy)
      (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) none =
      .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) ∧
    evalCastOpM (M := TBM) (.Transmute thinRawPtrTy)
      (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) none =
      .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) := by
  refine ⟨?_, ?_, ?_,
    evalCastOp_transmute_thinRawPtr_id addr hAddr provBM none,
    evalCastOpM_transmute_thinRawPtr_id (M := TBM) addr hAddr provTB none⟩
  · intro hNe
    have hBeq : Nat.beq p.offsetBytes 0 = false := by
      cases ho : p.offsetBytes with
      | zero => exact absurd ho hNe
      | succ _ => rfl
    show evalFnPtrToPtr locals op dstTy mem decls layouts = .ub
    unfold evalFnPtrToPtr
    simp [hOp, hBeq]
  · intro entry hB
    show evalFnPtrToPtr locals op dstTy mem decls layouts = .ub
    unfold evalFnPtrToPtr
    simp [hOp, hB]
  · intro ins out saf hIntr
    show evalFnPtrToPtr locals op dstTy mem decls layouts = .ub
    unfold evalFnPtrToPtr
    simp [hOp, hIntr, callConvEq]

/-- Concrete C6 positive, dead-operand UB, and extra-check divergence witnesses
across `stepMirFn`, `Interp.step`, and `Interp.stepTB`. -/
def c6FnPtrToPtrMir : MirAst.CapturedMir :=
  mkMirBody "ep2::c6_fn_ptr_to_ptr"
    [mkDecl rawConstUnitMirTy, mkDecl fnPtrSafeU32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.cast .fnPtrToPtr (.copy (locPlace 1)) rawConstUnitMirTy))]
      .return_]

def c6FnPtrToPtrMrFn : Gen.Function :=
  mkMrFn [(localName 0, thinRawPtrTy), (localName 1, thinRawPtrTy)]
    [localName 1] (localName 0)
    [(bbName 0,
      ⟨[.Assign (.Local (localName 0))
          (.UnOp (.Cast (.Transmute thinRawPtrTy)) (.Load (.Local (localName 1))))],
       .Return, .Regular⟩)]

def c6FnPtrMach (local1Live : Bool := true) : Mach :=
  let prog := mkMrProg [(fnName 0, c6FnPtrToPtrMrFn)]
  let fnAlloc := mkFnAlloc 4096
  let alloc0 := mkStackAlloc 128 (List.replicate 8 .Uninit) 8
  let alloc1 := mkStackAlloc 256 (ptrBytes 4096 (some (⟨0⟩, ()))) 8
  let locs : List (Gen.LocalName × Ptr) :=
    if local1Live then
      [(localName 0, { addr := 128, provenance := some (⟨1⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨2⟩, ()) })]
    else
      [(localName 0, { addr := 128, provenance := some (⟨1⟩, ()) })]
  let fr : Frame :=
    { func := c6FnPtrToPtrMrFn, locals := ⟨locs⟩, stack_pop_action := .BottomOfStack,
      next_block := bbName 0, next_stmt := 0, extra := () }
  mkMrMach prog [fnAlloc, alloc0, alloc1] [fr]
    [(fnName 0, { addr := 4096, provenance := some (⟨0⟩, ()) })]

theorem c6_fnPtrToPtr_three_way_and_ub_witness :
    let fnPtr : ProvenancePtr := { allocId := fnPtrAllocBase, offsetBytes := 0 }
    let sOk := initMachineState c6FnPtrToPtrMir [.ptr fnPtr 8]
    let sDead : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .dead] }
        memory := (initMachineState c6FnPtrToPtrMir []).memory }
    let sNonzero : MachineState :=
      initMachineState c6FnPtrToPtrMir [.ptr { allocId := fnPtrAllocBase, offsetBytes := 1 } 8]
    (match stepMirFn c6FnPtrToPtrMir sOk with
     | .tau (.running s1) => get? s1.frame.locals 0 = some (.init (.ptr fnPtr 8))
     | _ => False) ∧
    (∃ m1, Interp.step (c6FnPtrMach true) = .ok m1 ∧
      m1.mem.memory.allocations[1]?.map (·.data) =
        some (ptrBytes 4096 (some (⟨0⟩, ())))) ∧
    (∃ m1, Interp.stepTB (liftMachToTB (c6FnPtrMach true)) = .ok m1 ∧
      m1.mem.memory.mem.allocations[1]?.map (fun a => a.data.map projByteTB) =
        some ((ptrBytes 4096 (some (⟨0⟩, ()))).map (projByteTB ∘ liftByteTB))) ∧
    stepMirFn c6FnPtrToPtrMir sDead = MirStepNode.fail .ub ∧
    Interp.step (c6FnPtrMach false) = .error (.ub "access to a dead local") ∧
    Interp.stepTB (liftMachToTB (c6FnPtrMach false)) = .error (.ub "access to a dead local") ∧
    stepMirFn c6FnPtrToPtrMir sNonzero = MirStepNode.fail .ub :=
  ⟨rfl,
   ok_of_map_toOption (by decide +kernel),
   ok_of_map_toOption (by decide +kernel),
   rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   rfl⟩

/-! ## §7 (`C7`): `CastKind.subtype` (`Mach` & `MachTB`) -/

/-- **C7 Fragment Boundary (`translateRvalue_subtype_none`)**:
`Translate.translateRvalue` rejects `.cast .subtype` (even though it accepts
`.cast .transmute` on fragment types). -/
theorem translateRvalue_subtype_none
    (layouts : LayoutTable) (decls : List MirAst.LocalDecl) (targetTy : Option MirAst.Ty)
    (op : MirAst.Operand) (dstTy : MirAst.Ty) :
    translateRvalue layouts decls targetTy (.cast .subtype op dstTy) = none :=
  rfl

/-- **C7 Trusted Identity with `.transmute`
(`evalRvalue_subtype_eq_transmute`)**:
In `Trusted.MirSemantics`, `CastKind.subtype` and `CastKind.transmute` both
reduce definitionally to `evalByteCast`. -/
theorem evalRvalue_subtype_eq_transmute
    (locals : List LocalSlot) (op : MirAst.Operand) (dstTy : MirAst.Ty)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals (.cast .subtype op dstTy) mem decls layouts =
      evalRvalue locals (.cast .transmute op dstTy) mem decls layouts ∧
    evalRvalue locals (.cast .subtype op dstTy) mem decls layouts =
      evalByteCast locals op dstTy mem decls layouts :=
  ⟨rfl, rfl⟩

/-- `Classical.choice`-free polymorphic `u32 ↔ i32` transmute (`Mach` &
`MachTB`). -/
theorem transmuteM_u32_to_i32 {M : Type} [Gen.Memory M] [MemoryOps M]
    (bits : Nat) (hb : bits < 2 ^ 32) (m : Option (Machine M)) :
    transmuteM (M := M) (.Int (intFromBits bits u32)) u32MrTy i32MrTy m =
      .ok (.Int (intFromBits bits ⟨.Signed, ⟨4⟩⟩)) :=
  transmuteM_int_sameSize u32 ⟨.Signed, ⟨4⟩⟩ rfl (by decide) ⟨4⟩ rfl rfl bits hb m

/-- `Classical.choice`-free polymorphic `u8 → bool` transmute characterization
across `Mach` and `MachTB`:
- `0 ↦ false`, `1 ↦ true`
- every `b ∈ [2, 255]` faults with UB `"transmuted value is not valid at new
  type"`. -/
theorem transmuteM_u8_to_bool {M : Type} [Gen.Memory M] [MemoryOps M]
    (b : Nat) (hb : b < 256) (m : Option (Machine M)) :
    (b = 0 → transmuteM (M := M) (.Int 0) u8MrTy .Bool m = .ok (.Bool false)) ∧
    (b = 1 → transmuteM (M := M) (.Int 1) u8MrTy .Bool m = .ok (.Bool true)) ∧
    (2 ≤ b → transmuteM (M := M) (.Int (Int.ofNat b)) u8MrTy .Bool m =
      .error (.ub "transmuted value is not valid at new type")) := by
  refine ⟨?_, ?_, ?_⟩
  · intro _; rfl
  · intro _; rfl
  · intro hge
    have hlt256 : b < 2 ^ (8 * (⟨.Unsigned, ⟨1⟩⟩ : Gen.IntType).size.bytes) := by
      simpa using hb
    have hInt : intFromBits b ⟨.Unsigned, ⟨1⟩⟩ = Int.ofNat b := rfl
    have hU8Ne0 : UInt8.ofNat (b % 256) ≠ 0 := by
      intro h0
      have := congrArg UInt8.toNat h0
      simp only [UInt8.toNat_ofNat', UInt8.toNat_zero, Nat.mod_eq_of_lt hb,
        show (2 : Nat) ^ 8 = 256 by decide] at this
      exact Nat.not_le_of_lt (by decide : 0 < 2) (by rw [← this]; exact hge)
    have hU8Ne1 : UInt8.ofNat (b % 256) ≠ 1 := by
      intro h1
      have := congrArg UInt8.toNat h1
      simp only [UInt8.toNat_ofNat', UInt8.toNat_one, Nat.mod_eq_of_lt hb,
        show (2 : Nat) ^ 8 = 256 by decide] at this
      exact Nat.not_le_of_lt (by decide : 1 < 2) (by rw [← this]; exact hge)
    unfold transmuteM
    have hlay1 : Type.layout u8MrTy = .ok (.Sized ⟨1⟩ ⟨1⟩) := rfl
    have hlay2 : Type.layout .Bool = .ok (.Sized ⟨1⟩ ⟨1⟩) := rfl
    rw [hlay1, ok_bind, expect_size_sized, ok_bind, hlay2, ok_bind, expect_size_sized, ok_bind,
      size_ne_self_ite_local]
    have henc : Type.encodeM (M := M) u8MrTy (.Int (Int.ofNat b)) =
        .ok [.Init (UInt8.ofNat (b % 256)) none] := by
      simpa [u8MrTy, Type.encodeM, hInt, leBytes] using
        encodeIntM_intFromBits (M := M) ⟨.Unsigned, ⟨1⟩⟩ (by decide) b hlt256
    have hDecNone : ∀ (x : UInt8), x ≠ 0 → x ≠ 1 →
        Type.decodeM (M := M) .Bool [.Init x none] = .ok none := by
      intro x hx0 hx1
      unfold Type.decodeM
      simp only [List.length, ne_eq, not_true_eq_false, ↓reduceIte]
      split
      · rename_i heq; cases heq; exact absurd rfl hx0
      · rename_i heq; cases heq; exact absurd rfl hx1
      · rfl
    rw [henc, ok_bind, hDecNone _ hU8Ne0 hU8Ne1, ok_bind]
    rfl

/-- `NonZeroU8` MiniRust `Type.Enum` rejecting byte `0` (modeled identically to
`Translate.orderingTy` with `.Invalid` fallback at `0`). -/
def nonZeroU8MrTy : Gen.Type :=
  let unitV : Gen.Type := .Tuple [] ⟨⟨1⟩, ⟨1⟩, none⟩ none
  .Enum
    ⟨[(1, ⟨unitV, ⟨[(⟨0⟩, (⟨.Unsigned, ⟨1⟩⟩, 1))]⟩⟩),
      (7, ⟨unitV, ⟨[(⟨0⟩, (⟨.Unsigned, ⟨1⟩⟩, 7))]⟩⟩)]⟩
    ⟨.Unsigned, ⟨1⟩⟩
    (.Branch ⟨0⟩ ⟨.Unsigned, ⟨1⟩⟩ .Invalid
      ⟨[((1, 2), .Known 1), ((7, 8), .Known 7)]⟩)
    ⟨1⟩ ⟨1⟩

/-- `NonZeroU8` Anneal `TypeLayout` (1-field struct enforcing `validRange := ⟨1,
255⟩`). -/
def nonZeroU8MirLayout : TypeLayout :=
  { size := ⟨1⟩
    align := ⟨1⟩
    backendRepr := .scalar (.initialized (.int 8 false) ⟨1, 255⟩)
    fields := .arbitrary [⟨0⟩] [0]
    variants := .single 0
    isUninhabited := false }

def nonZeroU8Layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [nonZeroU8MirLayout] }

@[reducible] def nonZeroU8MirTy : MirAst.Ty :=
  { kind := .adt "core::num::nonzero::NonZero" [.uint .u8], layoutIdx := 0 }

def c7SubtypeU32ToI32Mir : MirAst.CapturedMir :=
  mkMirBody "ep2::c7_subtype_u32_i32" [mkDecl i32MirTy, mkDecl u32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.cast .subtype (.copy (locPlace 1)) i32MirTy))] .return_]

def c7SubtypeU8ToBoolMir : MirAst.CapturedMir :=
  mkMirBody "ep2::c7_subtype_u8_bool" [mkDecl boolMirTy, mkDecl u8MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.cast .subtype (.copy (locPlace 1)) boolMirTy))] .return_]

def c7SubtypeU8ToNzMir : MirAst.CapturedMir :=
  mkMirBody "ep2::c7_subtype_u8_nz" [mkDecl nonZeroU8MirTy, mkDecl u8MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.cast .subtype (.copy (locPlace 1)) nonZeroU8MirTy))]
      .return_]
    nonZeroU8Layouts

def c7MkTransmuteMach (srcTy dstTy : Gen.Type) (srcBytes : List Byte) (sz : Nat) : Mach :=
  let fn := mkMrFn [(localName 0, dstTy), (localName 1, srcTy)]
    [localName 1] (localName 0)
    [(bbName 0,
      ⟨[.Assign (.Local (localName 0))
          (.UnOp (.Cast (.Transmute dstTy)) (.Load (.Local (localName 1))))],
       .Return, .Regular⟩)]
  let alloc0 := mkStackAlloc 128 (List.replicate sz .Uninit) sz
  let alloc1 := mkStackAlloc 256 srcBytes sz
  let fr : Frame :=
    { func := fn
      locals := ⟨[(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
                  (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]⟩
      stack_pop_action := .BottomOfStack, next_block := bbName 0, next_stmt := 0, extra := () }
  mkMrMach (mkMrProg [(fnName 0, fn)]) [alloc0, alloc1] [fr]

/-- **C7 Concrete Positive & Invalid-Bit-Pattern UB Witness (`Mach` &
`MachTB`)**:
- `u32(42) → i32(42)` via `CastKind.subtype` ↔ MiniRust `Transmute i32`.
- `u8(1) → bool(true)` valid lockstep vs. `u8(2) → bool` **lockstep UB**.
- `u8(7) → NonZeroU8` valid lockstep vs. `u8(0) → NonZeroU8` **lockstep UB**. -/
theorem c7_subtype_positive_and_invalid_ub_three_way_witness :
    runAVal c7SubtypeU32ToI32Mir 4 (initMachineState c7SubtypeU32ToI32Mir [.scalar ⟨42, 4⟩]) =
      some (.scalar ⟨42, 4⟩) ∧
    (∃ m1, Interp.step (c7MkTransmuteMach u32MrTy i32MrTy (scalarBytes u32 42) 4) = .ok m1 ∧
      m1.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes u32 42)) ∧
    (∃ m1, Interp.stepTB (liftMachToTB (c7MkTransmuteMach u32MrTy i32MrTy (scalarBytes u32 42) 4)) =
      .ok m1 ∧
      m1.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes u32 42).map (projByteTB ∘ liftByteTB))) ∧
    runAVal c7SubtypeU8ToBoolMir 4 (initMachineState c7SubtypeU8ToBoolMir [.scalar ⟨1, 1⟩]) =
      some (.scalar ⟨1, 1⟩) ∧
    stepMirFn c7SubtypeU8ToBoolMir (initMachineState c7SubtypeU8ToBoolMir [.scalar ⟨2, 1⟩]) =
      MirStepNode.fail .ub ∧
    Interp.step (c7MkTransmuteMach u8MrTy .Bool [.Init 2 none] 1) =
      .error (.ub "transmuted value is not valid at new type") ∧
    Interp.stepTB (liftMachToTB (c7MkTransmuteMach u8MrTy .Bool [.Init 2 none] 1)) =
      .error (.ub "transmuted value is not valid at new type") ∧
    runAVal c7SubtypeU8ToNzMir 4 (initMachineState c7SubtypeU8ToNzMir [.scalar ⟨7, 1⟩]) =
      some (.aggregate 0 [.scalar ⟨7, 1⟩]) ∧
    (∃ m1, Interp.step (c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 7 none] 1) = .ok m1 ∧
      m1.mem.memory.allocations[0]?.map (·.data) = some [.Init 7 none]) ∧
    (∃ m1, Interp.stepTB (liftMachToTB (c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 7 none] 1)) =
      .ok m1 ∧
      m1.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some [.initNoProv 7]) ∧
    stepMirFn c7SubtypeU8ToNzMir (initMachineState c7SubtypeU8ToNzMir [.scalar ⟨0, 1⟩]) =
      MirStepNode.fail .ub ∧
    Interp.step (c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 0 none] 1) =
      .error (.ub "transmuted value is not valid at new type") ∧
    Interp.stepTB (liftMachToTB (c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 0 none] 1)) =
      .error (.ub "transmuted value is not valid at new type") :=
  ⟨rfl,
   ok_of_map_toOption (by decide +kernel),
   ok_of_map_toOption (by decide +kernel),
   rfl, rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   rfl,
   ok_of_map_toOption (by decide +kernel),
   ok_of_map_toOption (by decide +kernel),
   rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel)⟩

/-! ## §8 (`C8`): Exhaustive 5 Non-`Unsize` `CastKind.pointerCoercion` Kinds -/

/-- **C8 Universal Fragment Boundary (`translateRvalue_pointerCoercion_none`)**:
`Translate.translateRvalue` returns `none` for EVERY `CastKind.pointerCoercion`.
-/
theorem translateRvalue_pointerCoercion_none
    (layouts : LayoutTable) (decls : List MirAst.LocalDecl) (targetTy : Option MirAst.Ty)
    (coercionKind : String) (op : MirAst.Operand) (dstTy : MirAst.Ty) :
    translateRvalue layouts decls targetTy (.cast (.pointerCoercion coercionKind) op dstTy) =
      none :=
  rfl

/-- **C8.1 & C8.2 (`ReifyFnPointer` & `ClosureFnPointer`) Universal Lockstep
Law**:
On MiniRust (`Mach` & `MachTB`), `evalConstantM` on `Constant.FnPointer fnName`
loads `m.fn_ptrs[fnName]` as a thin pointer preserving function-pointer
provenance, matching Trusted's `internFnPtr` allocation creation/lookup. -/
theorem reify_and_closure_fnPointer_lockstep_M
    {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Machine M) (fnNm : Gen.FnName) (mrPtr : ThinPointer (Gen.Memory.Provenance M))
    (hLookup : mapIndex m.fn_ptrs fnNm "self.fn_ptrs[fn_name]" = .ok mrPtr) :
    evalConstantM m (.FnPointer fnNm) = .ok (.Ptr (ThinPointer.widen mrPtr none)) ∧
    evalValueM m (.Constant (.FnPointer fnNm) thinRawPtrTy) =
      .ok ((.Ptr (ThinPointer.widen mrPtr none), thinRawPtrTy), m) := by
  unfold evalValueM evalConstantM
  simp only [hLookup, bind, Except.bind, pure, Except.pure, and_self]

/-- **C8.3 (`UnsafeFnPointer`) Ground-Truth Characterization & Exact
Divergences**:
Inspecting `Trusted.MirSemantics.Places` directly (`isReifyFnPointerCoercion` &
`evalReifyFnPointer`):
1. **`Trusted` EXECUTES `"UnsafeFnPointer"`** via `evalUnsafeFnPointer`
   (`isReifyFnPointerCoercion "UnsafeFnPointer" = true`) — NOT `.unsupported`.
2. **Exact Strict-Check Divergence
   (`unsafeFnPointer_strict_checks_divergence`)**:
   `Trusted` faults with `.ub` when coercing to a `.safe` target, coercing an
   already-`unsafe` fn pointer, `rustIntrinsic` ABI, nonzero `offsetBytes`, or
   stack pointers — whereas MiniRust erases function-pointer safety/ABI into
   `PtrType.Raw .None` so `Transmute thinRawPtrTy` succeeds on `Mach` &
   `MachTB`.
3. **Unrecognized Coercion Tag (`.unsupported`)**: any tag outside the 6
   recognized coercion families (e.g., `"UnsafeFnPointer(Unsafe)"`) returns
   `.unsupported` in `Trusted`. -/
theorem unsafeFnPointer_ground_truth_and_divergences
    (locals locals' : List LocalSlot) (op : MirAst.Operand)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr) (addr : Nat) (hAddr : addr < 2 ^ 64)
    (provBM : Option Prov) (provTB : Option TreeBorrowsProvenance)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.ptr p 8) locals') :
    isReifyFnPointerCoercion "UnsafeFnPointer" = true ∧
    evalRvalue locals (.cast (.pointerCoercion "UnsafeFnPointer") op fnPtrUnsafeU32MirTy)
      mem decls layouts =
      evalUnsafeFnPointer locals op fnPtrUnsafeU32MirTy mem decls layouts ∧
    evalRvalue locals (.cast (.pointerCoercion "UnsafeFnPointer") op fnPtrSafeU32MirTy)
      mem decls layouts = .ub ∧
    evalCastOp (.Transmute thinRawPtrTy)
      (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) none =
      .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) ∧
    evalCastOpM (M := TBM) (.Transmute thinRawPtrTy)
      (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) none =
      .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) ∧
    evalRvalue locals (.cast (.pointerCoercion "UnsafeFnPointer(Unsafe)") op fnPtrUnsafeU32MirTy)
      mem decls layouts = .unsupported := by
  refine ⟨rfl, rfl, ?_,
    evalCastOp_transmute_thinRawPtr_id addr hAddr provBM none,
    evalCastOpM_transmute_thinRawPtr_id (M := TBM) addr hAddr provTB none, rfl⟩
  show evalUnsafeFnPointer locals op fnPtrSafeU32MirTy mem decls layouts = .ub
  unfold evalUnsafeFnPointer
  simp [hOp, fnPtrSafeU32MirTy]

private theorem mutToConst_dispatch_flags :
    isReifyFnPointerCoercion "MutToConstPointer" = false ∧
    stringEq "MutToConstPointer" "Unsize" = false ∧
    stringEq "MutToConstPointer" "ArrayToPointer" = false ∧
    stringEq "MutToConstPointer" "MutToConstPointer" = true :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem arrayToPtr_dispatch_flags :
    isReifyFnPointerCoercion "ArrayToPointer" = false ∧
    stringEq "ArrayToPointer" "Unsize" = false ∧
    stringEq "ArrayToPointer" "ArrayToPointer" = true :=
  ⟨rfl, rfl, rfl⟩

/-- **C8.4 (`MutToConstPointer`) Universal 4-Shape Preservation & Shape-Mismatch
UB**:
Covers thin provenance pointers, thin scalar addresses, wide slice pointers
(`*mut [T] → *const [T]`), and wide dyn-vtable pointers
(`*mut dyn Tr → *const dyn Tr`) on Trusted, paired with MiniRust's
mutability-erased
raw pointer representation and explicit `checkPtrMetadataM` `.VTablePointer`
boundary. -/
theorem mutToConstPointer_all_shapes_and_ub
    (locals locals' : List LocalSlot) (op : MirAst.Operand)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl)
    (p vt : ProvenancePtr) (addr len : Nat) :
    -- (a) Thin pointer preservation (*mut u32 -> *const u32)
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls
        mem.callStack = .ok (.ptr p 8) locals' →
      operandTy decls emptyLayoutTable op = some rawMutU32MirTy →
      evalRvalue locals (.cast (.pointerCoercion "MutToConstPointer") op rawConstU32MirTy)
        mem decls emptyLayoutTable = .ok (.ptr p 8) locals' mem) ∧
    -- (b) Thin scalar address preservation
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls
        mem.callStack = .ok (.scalar ⟨addr, 8⟩) locals' →
      operandTy decls emptyLayoutTable op = some rawMutU32MirTy →
      evalRvalue locals (.cast (.pointerCoercion "MutToConstPointer") op rawConstU32MirTy)
        mem decls emptyLayoutTable =
        .ok (.scalar ⟨wrapScalarBits addr (scalarModulus 8), 8⟩) locals' mem) ∧
    -- (c) Wide slice pointer preservation (*mut [u32] -> *const [u32])
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls
        mem.callStack = .ok (annealWidePtrVal p len 8) locals' →
      operandTy decls emptyLayoutTable op = some rawMutSliceU32MirTy →
      evalRvalue locals (.cast (.pointerCoercion "MutToConstPointer") op rawConstSliceU32MirTy)
        mem decls emptyLayoutTable = .ok (annealWidePtrVal p len 8) locals' mem) ∧
    -- (d) Wide dyn-vtable pointer preservation (*mut dyn Tr -> *const dyn Tr)
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls
        mem.callStack = .ok (.aggregate 0 [.ptr p 8, .ptr vt 8]) locals' →
      operandTy decls emptyLayoutTable op = some rawMutDynMirTy →
      evalRvalue locals (.cast (.pointerCoercion "MutToConstPointer") op rawConstDynMirTy)
        mem decls emptyLayoutTable =
        .ok (.aggregate 0 [.ptr p 8, .ptr vt 8]) locals' mem) ∧
    -- (e) Shape mismatch UB (thin pointer value with wide slice target)
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls
        mem.callStack = .ok (.ptr p 8) locals' →
      evalRvalue locals (.cast (.pointerCoercion "MutToConstPointer") op rawConstSliceU32MirTy)
        mem decls emptyLayoutTable = .ub) ∧
    -- (f) MiniRust wide dyn-vtable PtrType.as_wide_pair & checkPtrMetadataM
    -- boundary
    (PtrType.as_wide_pair (.Raw (.VTablePointer (traitNameOf 0))) =
      some (.Tuple [(⟨0⟩, thinRawPtrTy), (x86_64.PTR_SIZE, .Ptr (.VTablePtr (traitNameOf 0)))]
        ⟨⟨16⟩, ⟨8⟩, none⟩ none) ∧
     ∀ (vtThin : ThinPointer TreeBorrowsProvenance),
      checkPtrMetadataM (some (.VTablePointer vtThin)) (.VTablePointer (traitNameOf 0)) =
        .error (.unsupported
          "check_ptr_metadata for vtable pointer metadata (Machine::vtable_from_ptr)")) := by
  obtain ⟨h1, h2, h3, h4⟩ := mutToConst_dispatch_flags
  have hL8 : layoutPointerBytes emptyLayoutTable = 8 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨rfl, fun _ => rfl⟩⟩
  · intro hOp hTy
    have hSh : mutToConstTargetShape? (some rawMutU32MirTy) rawConstU32MirTy = some none := rfl
    show evalReifyFnPointer locals op rawConstU32MirTy mem decls emptyLayoutTable "MutToConstPointer" = _
    unfold evalReifyFnPointer
    simp only [h1, h2, h3, h4, hL8, hOp, hTy, hSh, Nat.beq_refl]
  · intro hOp hTy
    have hSh : mutToConstTargetShape? (some rawMutU32MirTy) rawConstU32MirTy = some none := rfl
    show evalReifyFnPointer locals op rawConstU32MirTy mem decls emptyLayoutTable "MutToConstPointer" = _
    unfold evalReifyFnPointer
    simp only [h1, h2, h3, h4, hL8, hOp, hTy, hSh, Nat.beq_refl]
  · intro hOp hTy
    have hSh : mutToConstTargetShape? (some rawMutSliceU32MirTy) rawConstSliceU32MirTy =
        some (some false) := rfl
    show evalReifyFnPointer locals op rawConstSliceU32MirTy mem decls emptyLayoutTable "MutToConstPointer" = _
    unfold evalReifyFnPointer
    simp only [h1, h2, h3, h4, hL8, hOp, hTy, hSh, annealWidePtrVal, Nat.beq_refl, Bool.and_self]
  · intro hOp hTy
    have hSh : mutToConstTargetShape? (some rawMutDynMirTy) rawConstDynMirTy =
        some (some true) := rfl
    show evalReifyFnPointer locals op rawConstDynMirTy mem decls emptyLayoutTable "MutToConstPointer" = _
    unfold evalReifyFnPointer
    simp only [h1, h2, h3, h4, hL8, hOp, hTy, hSh, Nat.beq_refl, Bool.and_self]
  · intro hOp
    have hShape : ∀ s, mutToConstTargetShape? s rawConstSliceU32MirTy ≠ some none := by
      intro s
      cases s with
      | none => decide
      | some ty =>
        cases ty with
        | mk kind lidx =>
          cases kind <;> simp [mutToConstTargetShape?, rawConstSliceU32MirTy, isWideRawPtrTy]
          all_goals split <;> simp
    show evalReifyFnPointer locals op rawConstSliceU32MirTy mem decls emptyLayoutTable "MutToConstPointer" = .ub
    unfold evalReifyFnPointer
    simp only [h1, h2, h3, h4, hL8, hOp]
    cases hS : mutToConstTargetShape? (operandTy decls emptyLayoutTable op) rawConstSliceU32MirTy with
    | none => rfl
    | some o =>
      cases o with
      | none => exact absurd hS (hShape _)
      | some _ => rfl

/-- **C8.5 (`ArrayToPointer`) Universal Preservation (Global, Stack-Borrow,
Scalar) & UB**. -/
theorem arrayToPointer_global_stack_scalar_and_ub
    (locals locals' : List LocalSlot) (op : MirAst.Operand)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl)
    (p : ProvenancePtr) (addr : Nat) :
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls
        mem.callStack = .ok (.ptr p 8) locals' →
      operandTy decls emptyLayoutTable op = some rawMutArr2U32MirTy →
      lookupBorrow mem.borrows p.tag = none →
      evalRvalue locals (.cast (.pointerCoercion "ArrayToPointer") op rawMutU32MirTy)
        mem decls emptyLayoutTable = .ok (.ptr p 8) locals' mem) ∧
    (∀ parentEntry,
      evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls
        mem.callStack = .ok (.ptr p 8) locals' →
      operandTy decls emptyLayoutTable op = some rawMutArr2U32MirTy →
      lookupBorrow mem.borrows p.tag = some parentEntry →
      evalRvalue locals (.cast (.pointerCoercion "ArrayToPointer") op rawMutU32MirTy)
        mem decls emptyLayoutTable =
        deriveStackElemThinPtr locals' mem p parentEntry (some 2) 8) ∧
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls
        mem.callStack = .ok (.scalar ⟨addr, 8⟩) locals' →
      operandTy decls emptyLayoutTable op = some rawMutArr2U32MirTy →
      evalRvalue locals (.cast (.pointerCoercion "ArrayToPointer") op rawMutU32MirTy)
        mem decls emptyLayoutTable =
        .ok (.scalar ⟨wrapScalarBits addr (scalarModulus 8), 8⟩) locals' mem) ∧
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls
        mem.callStack = .ok (.ptr p 8) locals' →
      operandTy decls emptyLayoutTable op = some rawConstArr2U32MirTy →
      evalRvalue locals (.cast (.pointerCoercion "ArrayToPointer") op rawMutU32MirTy)
        mem decls emptyLayoutTable = .ub) := by
  obtain ⟨h1, h2, h3⟩ := arrayToPtr_dispatch_flags
  have hL8 : layoutPointerBytes emptyLayoutTable = 8 := rfl
  have hArrOk : arrayToPointerElemLen? (some rawMutArr2U32MirTy) rawMutU32MirTy = some (some 2) := rfl
  have hArrBad : arrayToPointerElemLen? (some rawConstArr2U32MirTy) rawMutU32MirTy = none := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hOp hTy hNoB
    show evalReifyFnPointer locals op rawMutU32MirTy mem decls emptyLayoutTable "ArrayToPointer" = _
    unfold evalReifyFnPointer
    simp only [h1, h2, h3, hL8, hOp, hTy, hArrOk, hNoB, Nat.beq_refl]
  · intro parentEntry hOp hTy hB
    show evalReifyFnPointer locals op rawMutU32MirTy mem decls emptyLayoutTable "ArrayToPointer" = _
    unfold evalReifyFnPointer
    simp only [h1, h2, h3, hL8, hOp, hTy, hArrOk, hB, Nat.beq_refl]
  · intro hOp hTy
    show evalReifyFnPointer locals op rawMutU32MirTy mem decls emptyLayoutTable "ArrayToPointer" = _
    unfold evalReifyFnPointer
    simp only [h1, h2, h3, hL8, hOp, hTy, hArrOk, Nat.beq_refl]
  · intro hOp hTy
    show evalReifyFnPointer locals op rawMutU32MirTy mem decls emptyLayoutTable "ArrayToPointer" = .ub
    unfold evalReifyFnPointer
    simp only [h1, h2, h3, hL8, hOp, hTy, hArrBad, Nat.beq_refl]

/-! ### C8 Concrete End-to-End Witnesses covering ALL 5 Coercion Kinds (`Mach` &
`MachTB`) -/

def c8AllFiveMir : MirAst.CapturedMir :=
  mkMirBody "ep2::c8_all_five"
    [mkDecl rawConstU32MirTy,
     mkDecl fnPtrSafeU32MirTy,
     mkDecl fnPtrSafeU32MirTy,
     mkDecl fnPtrUnsafeU32MirTy,
     mkDecl arr2U32MirTy,
     mkDecl rawMutArr2U32MirTy,
     mkDecl rawMutU32MirTy] 0
    [mkBb
      [mkSt (.storageLive 1), mkSt (.storageLive 2), mkSt (.storageLive 3),
       mkSt (.storageLive 4), mkSt (.storageLive 5), mkSt (.storageLive 6),
       mkSt (.assign (locPlace 1)
         (.cast (.pointerCoercion "ReifyFnPointer")
           (constZst (fnDefU32MirTy "ep2::target_fn")) fnPtrSafeU32MirTy)),
       mkSt (.assign (locPlace 2)
         (.cast (.pointerCoercion "ClosureFnPointer")
           (constZst (closureZstMirTy "ep2::zst_closure")) fnPtrSafeU32MirTy)),
       mkSt (.assign (locPlace 3)
         (.cast (.pointerCoercion "UnsafeFnPointer")
           (.copy (locPlace 1)) fnPtrUnsafeU32MirTy)),
       mkSt (.assign (locPlace 4) (.aggregate (.array u32MirTy) [constU32 10, constU32 20])),
       mkSt (.assign (locPlace 5) (.rawPtr .mut (locPlace 4))),
       mkSt (.assign (locPlace 6)
         (.cast (.pointerCoercion "ArrayToPointer") (.copy (locPlace 5)) rawMutU32MirTy)),
       mkSt (.assign (locPlace 0)
         (.cast (.pointerCoercion "MutToConstPointer") (.copy (locPlace 6)) rawConstU32MirTy))]
      .return_]

def c8MrFn : Gen.Function :=
  mkMrFn
    [(localName 0, thinRawPtrTy),
     (localName 1, thinRawPtrTy),
     (localName 2, thinRawPtrTy),
     (localName 3, thinRawPtrTy),
     (localName 4, .Array u32MrTy 2),
     (localName 5, thinRawPtrTy),
     (localName 6, thinRawPtrTy)]
    [] (localName 0)
    [(bbName 0,
      ⟨[.Assign (.Local (localName 1)) (.Constant (.FnPointer (fnName 1)) thinRawPtrTy),
        .Assign (.Local (localName 2)) (.Constant (.FnPointer (fnName 2)) thinRawPtrTy),
        .Assign (.Local (localName 3))
          (.UnOp (.Cast (.Transmute thinRawPtrTy)) (.Load (.Local (localName 1)))),
        .Assign (.Local (localName 4))
          (.Tuple [.Constant (.Int 10) u32MrTy, .Constant (.Int 20) u32MrTy]
            (.Array u32MrTy 2)),
        .Assign (.Local (localName 5)) (.AddrOf (.Local (localName 4)) (.Raw .None)),
        .Assign (.Local (localName 6))
          (.UnOp (.Cast (.Transmute thinRawPtrTy)) (.Load (.Local (localName 5)))),
        .Assign (.Local (localName 0))
          (.UnOp (.Cast (.Transmute thinRawPtrTy)) (.Load (.Local (localName 6))))],
       .Return, .Regular⟩)]

def c8AllFiveMach : Mach :=
  let dummyTargetFn := mkMrFn [] [] (localName 0) [(bbName 0, ⟨[], .Return, .Regular⟩)]
  let prog := mkMrProg [(fnName 0, c8MrFn), (fnName 1, dummyTargetFn), (fnName 2, dummyTargetFn)]
  let fnAlloc1 := mkFnAlloc 4096
  let fnAlloc2 := mkFnAlloc 8192
  let a0 := mkStackAlloc 128 (List.replicate 8 .Uninit) 8
  let a1 := mkStackAlloc 256 (List.replicate 8 .Uninit) 8
  let a2 := mkStackAlloc 384 (List.replicate 8 .Uninit) 8
  let a3 := mkStackAlloc 512 (List.replicate 8 .Uninit) 8
  let a4 := mkStackAlloc 640 (List.replicate 8 .Uninit) 4
  let a5 := mkStackAlloc 768 (List.replicate 8 .Uninit) 8
  let a6 := mkStackAlloc 896 (List.replicate 8 .Uninit) 8
  let fr : Frame :=
    { func := c8MrFn
      locals := ⟨[(localName 0, { addr := 128, provenance := some (⟨2⟩, ()) }),
                  (localName 1, { addr := 256, provenance := some (⟨3⟩, ()) }),
                  (localName 2, { addr := 384, provenance := some (⟨4⟩, ()) }),
                  (localName 3, { addr := 512, provenance := some (⟨5⟩, ()) }),
                  (localName 4, { addr := 640, provenance := some (⟨6⟩, ()) }),
                  (localName 5, { addr := 768, provenance := some (⟨7⟩, ()) }),
                  (localName 6, { addr := 896, provenance := some (⟨8⟩, ()) })]⟩
      stack_pop_action := .BottomOfStack, next_block := bbName 0, next_stmt := 0, extra := () }
  mkMrMach prog [fnAlloc1, fnAlloc2, a0, a1, a2, a3, a4, a5, a6] [fr]
    [(fnName 1, { addr := 4096, provenance := some (⟨0⟩, ()) }),
     (fnName 2, { addr := 8192, provenance := some (⟨1⟩, ()) })]

theorem c8_all_five_pointer_coercions_three_way_witness :
    runAVal c8AllFiveMir 16 (initMachineState c8AllFiveMir []) =
      some (.ptr { allocId := 2, offsetBytes := 0 } 8) ∧
    (∃ m7, Interp.steps 7 c8AllFiveMach = .ok m7 ∧
      ([3, 4, 5, 2].map (fun i => m7.mem.memory.allocations[i]?.map (fun a => a.data.map (projByteTB ∘ liftByteTB)))) =
      [some ((ptrBytes 4096 (some (⟨0⟩, ()))).map (projByteTB ∘ liftByteTB)),
       some ((ptrBytes 8192 (some (⟨1⟩, ()))).map (projByteTB ∘ liftByteTB)),
       some ((ptrBytes 4096 (some (⟨0⟩, ()))).map (projByteTB ∘ liftByteTB)),
       some ((ptrBytes 640 (some (⟨6⟩, ()))).map (projByteTB ∘ liftByteTB))]) ∧
    (∃ m7, Interp.stepsTB 7 (liftMachToTB c8AllFiveMach) = .ok m7 ∧
      ([3, 4, 5, 2].map (fun i => m7.mem.memory.mem.allocations[i]?.map (fun a => a.data.map projByteTB))) =
      [some ((ptrBytes 4096 (some (⟨0⟩, ()))).map (projByteTB ∘ liftByteTB)),
       some ((ptrBytes 8192 (some (⟨1⟩, ()))).map (projByteTB ∘ liftByteTB)),
       some ((ptrBytes 4096 (some (⟨0⟩, ()))).map (projByteTB ∘ liftByteTB)),
       some ((ptrBytes 640 (some (⟨6⟩, ()))).map (projByteTB ∘ liftByteTB))]) :=
  ⟨rfl,
   ok_of_map_toOption (by decide +kernel),
   ok_of_map_toOption (by decide +kernel)⟩

/-- Concrete C8 negative witness: capturing closure rejected by
`ClosureFnPointer`
(`.ub`) and unrecognized coercion tag returns `.unsupported` in Trusted. -/
theorem c8_capturing_closure_ub_and_unknown_tag_unsupported_witness :
    let capDecls := [mkDecl fnPtrSafeU32MirTy, mkDecl (closureCapMirTy "ep2::cap_cl")]
    let mem0 := (initMachineState c8AllFiveMir []).memory
    evalRvalue [.uninit, .init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨0, 8⟩])]
      (.cast (.pointerCoercion "ClosureFnPointer") (.copy (locPlace 1)) fnPtrSafeU32MirTy)
      mem0 capDecls emptyLayoutTable = .ub ∧
    evalRvalue [.uninit, .init (.ptr { allocId := fnPtrAllocBase, offsetBytes := 0 } 8)]
      (.cast (.pointerCoercion "UnknownCoercion") (.copy (locPlace 1)) fnPtrUnsafeU32MirTy)
      mem0 [mkDecl fnPtrUnsafeU32MirTy, mkDecl fnPtrSafeU32MirTy] emptyLayoutTable =
      .unsupported :=
  ⟨rfl, rfl⟩

/-! ## §9 (`C9`): `ProjectionElem.unwrapUnsafeBinder` (`Mach` & `MachTB`) -/

/-- **C9 Fragment Boundary (`translatePlace_unwrapUnsafeBinder_none`)**:
`Translate.translatePlace` and `Translate.translateFieldPlace` both reject
`.unwrapUnsafeBinder`. -/
theorem translatePlace_unwrapUnsafeBinder_none
    (decls : List MirAst.LocalDecl) (loc : Nat) (innerTy : MirAst.Ty)
    (rest : List MirAst.ProjectionElem) (base : Gen.PlaceExpr) :
    translatePlace decls ⟨loc, .unwrapUnsafeBinder innerTy :: rest⟩ = none ∧
    translateFieldPlace base (.unwrapUnsafeBinder innerTy :: rest) = none :=
  ⟨rfl, rfl⟩

/-- **C9 Trusted Universal Transparency Laws**:
`ProjectionElem.unwrapUnsafeBinder` is definitionally transparent across
`readProjectedValue`, `writeProjectedValue`, `splitLastDeref?`,
`isScalarCompatibleProj`, and `stripTransparentProjections`. -/
theorem trusted_unwrapUnsafeBinder_transparent
    (locals : List LocalSlot) (val newVal : MirSemantics.Value)
    (innerTy : MirAst.Ty) (rest : List MirAst.ProjectionElem) :
    readProjectedValue locals val (.unwrapUnsafeBinder innerTy :: rest) =
      readProjectedValue locals val rest ∧
    writeProjectedValue locals val (.unwrapUnsafeBinder innerTy :: rest) newVal =
      writeProjectedValue locals val rest newVal ∧
    splitLastDeref? (.unwrapUnsafeBinder innerTy :: rest) = splitLastDeref? rest ∧
    splitLastDeref? [.deref, .unwrapUnsafeBinder innerTy] = some [] ∧
    isScalarCompatibleProj (.unwrapUnsafeBinder innerTy :: rest) =
      isScalarCompatibleProj rest ∧
    stripTransparentProjections (.unwrapUnsafeBinder innerTy :: rest) =
      stripTransparentProjections rest :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- MiniRust transparent single-field wrapper `#[repr(transparent)] struct
Binder(T)`:
offset-0 field 0 with identical size and alignment to `inner`. -/
@[reducible] def mrBinderWrapperTy (inner : Gen.Type)
    (sz : LibSpecr.Size) (al : LibSpecr.Align) : Gen.Type :=
  .Tuple [(⟨0⟩, inner)] ⟨sz, al, none⟩ none

/-- **C9 MiniRust Polymorphic Field-0 Wrapper Place Identity (`Mach` &
`MachTB`)**:
Projecting `.Field base 0` through `mrBinderWrapperTy inner sz al` (for a sized
`inner`) evaluates to the exact same pointer and alignment (offset `0`) on EVERY
`Machine M` (`Mach` and `MachTB`)! -/
theorem minirust_evalPlaceM_binderWrapper_field0
    {M : Type} [Gen.Memory M] [MemoryOps M]
    (m m1 : Machine M) (base : Gen.PlaceExpr) (place : Gen.Place M)
    (inner : Gen.Type) (sz : LibSpecr.Size) (al : LibSpecr.Align)
    (hBase : evalPlaceM m base = .ok ((place, mrBinderWrapperTy inner sz al), m1))
    (hMeta : place.ptr.metadata = none)
    (hInnerLay : Type.layout inner = .ok (.Sized sz al))
    (hHead : TupleHeadLayout.head_size_and_align ⟨sz, al, none⟩ = (sz, al))
    (hPtr0 : ptrOffsetInboundsM m1 place.ptr.thin_pointer 0 = .ok place.ptr.thin_pointer) :
    evalPlaceM m (.Field base 0) =
      .ok (({ place with ptr := ThinPointer.widen place.ptr.thin_pointer none }, inner), m1) := by
  have hCond : (0 : Int) ≤ 0 ∧ (0 : Int) < ([(({ bytes := 0 } : LibSpecr.Size), inner)].length : Int) := by
    simp
  have hIdx : listIndex [(({ bytes := 0 } : LibSpecr.Size), inner)] 0 "sized_fields[field]" =
      .ok (({ bytes := 0 } : LibSpecr.Size), inner) := rfl
  have hLayWrap : Type.layout (mrBinderWrapperTy inner sz al) = .ok (.Sized sz al) := by
    simp only [mrBinderWrapperTy, Type.layout, hHead, pure, Except.pure]
  have hSzWrap : computeSizeM m1 (.Sized sz al) place.ptr.metadata = .ok sz := by
    simp only [computeSizeM, LayoutStrategy.compute_size_and_align, hMeta,
      pure, Except.pure, bind, Except.bind]
  unfold evalPlaceM
  rw [hBase, ok_bind]
  dsimp only [mrBinderWrapperTy]
  rw [ite_eq_left_iff.mpr (fun hn => absurd hCond hn), hIdx, ok_bind]
  dsimp only []
  rw [show Type.layout (.Tuple [(⟨0⟩, inner)] ⟨sz, al, none⟩ none) = .ok (.Sized sz al) from hLayWrap,
    ok_bind, hSzWrap, ok_bind]
  have hLe : (!decide (({ bytes := 0 } : LibSpecr.Size).bytes ≤ sz.bytes)) = false := by
    simp
  rw [hLe]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (({ bytes := 0 } : LibSpecr.Size).bytes : Int) = 0 from rfl, hPtr0, ok_bind,
    hInnerLay, ok_bind]
  rfl

def c9BinderReadWriteMir : MirAst.CapturedMir :=
  mkMirBody "ep2::c9_binder_rw"
    [mkDecl u32MirTy, mkDecl u32MirTy, mkDecl rawMutU32MirTy, mkDecl usizeMirTy,
     mkDecl rawConstSliceU32MirTy] 1
    [mkBb
      [mkSt (.storageLive 2),
       mkSt (.assign (locPlace 1 [.unwrapUnsafeBinder u32MirTy]) (.use (constU32 55))),
       mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1 [.unwrapUnsafeBinder u32MirTy])))),
       mkSt (.assign (locPlace 2) (.rawPtr .mut (locPlace 1))),
       mkSt (.assign (locPlace 2 [.deref, .unwrapUnsafeBinder u32MirTy]) (.use (constU32 88))),
       mkSt (.assign (locPlace 0)
         (.use (.copy (locPlace 2 [.deref, .unwrapUnsafeBinder u32MirTy]))))]
      .return_]

def c9BinderMrFn : Gen.Function :=
  let wrapU32 := mrBinderWrapperTy u32MrTy ⟨4⟩ ⟨4⟩
  let wrapPtr := mrBinderWrapperTy thinRawPtrTy ⟨8⟩ ⟨8⟩
  mkMrFn [(localName 0, u32MrTy), (localName 1, wrapU32), (localName 2, wrapPtr)]
    [localName 1] (localName 0)
    [(bbName 0,
      ⟨[.Assign (.Field (.Local (localName 1)) 0) (.Constant (.Int 55) u32MrTy),
        .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 0)),
        .Assign (.Field (.Local (localName 2)) 0)
          (.AddrOf (.Field (.Local (localName 1)) 0) (.Raw .None)),
        .Assign (.Deref (.Load (.Field (.Local (localName 2)) 0)) u32MrTy)
          (.Constant (.Int 88) u32MrTy),
        .Assign (.Local (localName 0))
          (.Load (.Deref (.Load (.Field (.Local (localName 2)) 0)) u32MrTy))],
       .Return, .Regular⟩)]

def c9BinderMach (local1Live : Bool := true) : Mach :=
  let prog := mkMrProg [(fnName 0, c9BinderMrFn)]
  let a0 := mkStackAlloc 128 (List.replicate 4 .Uninit) 4
  let a1 := mkStackAlloc 256 (scalarBytes u32 10) 4
  let a2 := mkStackAlloc 384 (List.replicate 8 .Uninit) 8
  let locs : List (Gen.LocalName × Ptr) :=
    if local1Live then
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) }),
       (localName 2, { addr := 384, provenance := some (⟨2⟩, ()) })]
    else
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 2, { addr := 384, provenance := some (⟨2⟩, ()) })]
  let fr : Frame :=
    { func := c9BinderMrFn, locals := ⟨locs⟩, stack_pop_action := .BottomOfStack,
      next_block := bbName 0, next_stmt := 0, extra := () }
  mkMrMach prog [a0, a1, a2] [fr]

/-- Concrete C9 positive witness (read, write, deref chain `*p` +
`.unwrapUnsafeBinder`,
`Rvalue.len` via `splitLastDeref?`) and dead-local UB witness across Trusted,
`Mach`, and `MachTB`. -/
theorem c9_unwrapUnsafeBinder_three_way_len_and_ub_witness :
    let sliceLenPlace : MirAst.Place :=
      locPlace 0 [.deref, .unwrapUnsafeBinder { kind := .slice (.uint .u32), layoutIdx := 0 }]
    let sliceMem := (initMachineState c9BinderReadWriteMir []).memory
    let sliceLocs : List LocalSlot :=
      [.init (annealWidePtrVal { allocId := 9, offsetBytes := 0 } 4 8)]
    runAVal c9BinderReadWriteMir 10 (initMachineState c9BinderReadWriteMir [.scalar ⟨10, 4⟩]) =
      some (.scalar ⟨88, 4⟩) ∧
    (∃ m5, Interp.steps 5 (c9BinderMach true) = .ok m5 ∧
      m5.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes u32 88)) ∧
    (∃ m5, Interp.stepsTB 5 (liftMachToTB (c9BinderMach true)) = .ok m5 ∧
      m5.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes u32 88).map (projByteTB ∘ liftByteTB))) ∧
    evalRvalue sliceLocs (.len sliceLenPlace) sliceMem [mkDecl rawConstSliceU32MirTy]
      emptyLayoutTable = .ok (.scalar ⟨4, 8⟩) sliceLocs sliceMem ∧
    stepMirFn c9BinderReadWriteMir
      { frame := { blockIdx := 0, stmtIdx := 1,
                   locals := [.uninit, .dead, .uninit, .uninit, .uninit] }
        memory := sliceMem } = MirStepNode.fail .ub ∧
    Interp.step (c9BinderMach false) = .error (.ub "access to a dead local") ∧
    Interp.stepTB (liftMachToTB (c9BinderMach false)) = .error (.ub "access to a dead local") :=
  ⟨rfl,
   ok_of_map_toOption (by decide +kernel),
   ok_of_map_toOption (by decide +kernel),
   rfl, rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel)⟩

/-! ## §10 (`C10`): `AggregateKind.closure` (`Mach` & `MachTB`) -/

/-- **C10 Fragment Boundary (`translateRvalue_closure_none`)**:
`Translate.translateRvalue` returns `none` for every `AggregateKind.closure`. -/
theorem translateRvalue_closure_none
    (layouts : LayoutTable) (decls : List MirAst.LocalDecl) (targetTy : Option MirAst.Ty)
    (dp : DefPath) (ops : List MirAst.Operand) :
    translateRvalue layouts decls targetTy (.aggregate (.closure dp) ops) = none :=
  rfl

/-- **C10.1 Universal 0-Capture ZST Closure Step Law (`Mach` & `MachTB`)**:
Evaluating `.aggregate (.closure dp) []` produces `.aggregate 0 []` leaving
`locals` and `mem` untouched; MiniRust `ValueExpr.Tuple [] unitType` produces
`(.Tuple [], unitType)` leaving `m` untouched on EVERY `Machine M` (`Mach` &
`MachTB`). -/
theorem closure_zst_lockstep_M
    {M : Type} [Gen.Memory M] [MemoryOps M]
    (locals : List LocalSlot) (dp : DefPath) (mem : MirSemantics.Memory)
    (decls : List MirAst.LocalDecl) (layouts : LayoutTable) (m : Machine M) :
    evalRvalue locals (.aggregate (.closure dp) []) mem decls layouts =
      .ok (.aggregate 0 []) locals mem ∧
    evalValueM m (.Tuple [] unitType) = .ok ((.Tuple [], unitType), m) :=
  ⟨rfl, rfl⟩

/-- **C10.2 Universal Multi-Capture Closure Left-to-Right Evaluation & UB Law
(`Mach` & `MachTB`)**. -/
theorem closure_two_capture_ltr_and_ub_M
    {M : Type} [Gen.Memory M] [MemoryOps M]
    (locals locals1 locals2 : List LocalSlot) (dp : DefPath) (op0 op1 : MirAst.Operand)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (m m1 m2 : Machine M) (e0 e1 : Gen.ValueExpr) (mrClTy : Gen.Type) :
    (∀ v0 v1 mv0 mv1 t0 t1,
      evalOperand locals op0 mem.borrows mem.globals layouts mem.callerLocals decls
        mem.callStack = .ok v0 locals1 →
      evalOperand locals1 op1 mem.borrows mem.globals layouts mem.callerLocals decls
        mem.callStack = .ok v1 locals2 →
      evalValueM m e0 = .ok ((mv0, t0), m1) →
      evalValueM m1 e1 = .ok ((mv1, t1), m2) →
      evalRvalue locals (.aggregate (.closure dp) [op0, op1]) mem decls layouts =
        .ok (.aggregate 0 [v0, v1]) locals2 mem ∧
      evalValueM m (.Tuple [e0, e1] mrClTy) = .ok ((.Tuple [mv0, mv1], mrClTy), m2)) ∧
    (∀ msg,
      evalOperand locals op0 mem.borrows mem.globals layouts mem.callerLocals decls
        mem.callStack = .ub →
      evalValueM m e0 = .error (.ub msg) →
      evalRvalue locals (.aggregate (.closure dp) [op0, op1]) mem decls layouts = .ub ∧
      evalValueM m (.Tuple [e0, e1] mrClTy) = .error (.ub msg)) ∧
    (∀ v0 mv0 t0 msg,
      evalOperand locals op0 mem.borrows mem.globals layouts mem.callerLocals decls
        mem.callStack = .ok v0 locals1 →
      evalOperand locals1 op1 mem.borrows mem.globals layouts mem.callerLocals decls
        mem.callStack = .ub →
      evalValueM m e0 = .ok ((mv0, t0), m1) →
      evalValueM m1 e1 = .error (.ub msg) →
      evalRvalue locals (.aggregate (.closure dp) [op0, op1]) mem decls layouts = .ub ∧
      evalValueM m (.Tuple [e0, e1] mrClTy) = .error (.ub msg)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v0 v1 mv0 mv1 t0 t1 h0 h1 hm0 hm1
    constructor
    · simp only [evalRvalue, evalOperands, h0, h1]
    · simp only [evalValueM, evalValuesM, hm0, hm1, bind, Except.bind, pure, Except.pure]
  · intro msg h0 hm0
    constructor
    · simp only [evalRvalue, evalOperands, h0]
    · simp only [evalValueM, evalValuesM, hm0, bind, Except.bind]
  · intro v0 mv0 t0 msg h0 h1 hm0 hm1
    constructor
    · simp only [evalRvalue, evalOperands, h0, h1]
    · simp only [evalValueM, evalValuesM, hm0, hm1, bind, Except.bind]

/-- MiniRust 16-byte closure tuple type capturing `(u32, *const u32)`:
field 0 (`u32`) at offset 0, field 1 (`*const u32`) at offset 8, align 8. -/
def mrClosureCapTy : Gen.Type :=
  .Tuple [(⟨0⟩, u32MrTy), (⟨8⟩, thinRawPtrTy)] ⟨⟨16⟩, ⟨8⟩, none⟩ none

def c10ZstClosureMir : MirAst.CapturedMir :=
  mkMirBody "ep2::c10_zst_closure" [mkDecl (closureZstMirTy "ep2::zst")] 0
    [mkBb [mkSt (.assign (locPlace 0) (.aggregate (.closure "ep2::zst") []))] .return_]

def c10CapClosureMir : MirAst.CapturedMir :=
  mkMirBody "ep2::c10_cap_closure"
    [mkDecl (closureCapMirTy "ep2::cap"), mkDecl u32MirTy, mkDecl rawConstU32MirTy] 1
    [mkBb
      [mkSt (.storageLive 2),
       mkSt (.assign (locPlace 2) (.rawPtr .not (locPlace 1))),
       mkSt (.assign (locPlace 0)
         (.aggregate (.closure "ep2::cap") [.copy (locPlace 1), .copy (locPlace 2)]))]
      .return_]

def c10CapMrFn : Gen.Function :=
  mkMrFn [(localName 0, mrClosureCapTy), (localName 1, u32MrTy), (localName 2, thinRawPtrTy)]
    [localName 1] (localName 0)
    [(bbName 0,
      ⟨[.Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (.Raw .None)),
        .Assign (.Local (localName 0))
          (.Tuple [.Load (.Local (localName 1)), .Load (.Local (localName 2))] mrClosureCapTy)],
       .Return, .Regular⟩)]

def c10CapMach (local2Live : Bool := true) : Mach :=
  let prog := mkMrProg [(fnName 0, c10CapMrFn)]
  let a0 := mkStackAlloc 128 (List.replicate 16 .Uninit) 8
  let a1 := mkStackAlloc 256 (scalarBytes u32 7) 4
  let a2 := mkStackAlloc 384 (List.replicate 8 .Uninit) 8
  let locs : List (Gen.LocalName × Ptr) :=
    if local2Live then
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) }),
       (localName 2, { addr := 384, provenance := some (⟨2⟩, ()) })]
    else
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]
  let fr : Frame :=
    { func := c10CapMrFn, locals := ⟨locs⟩, stack_pop_action := .BottomOfStack,
      next_block := bbName 0, next_stmt := if local2Live then 0 else 1, extra := () }
  mkMrMach prog [a0, a1, a2] [fr]

def c10ZstMach : Mach :=
  let fn := mkMrFn [(localName 0, unitType)] [] (localName 0)
    [(bbName 0, ⟨[.Assign (.Local (localName 0)) (.Tuple [] unitType)], .Return, .Regular⟩)]
  let a0 := mkStackAlloc 128 [] 1
  let fr : Frame :=
    { func := fn
      locals := ⟨[(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]⟩
      stack_pop_action := .BottomOfStack, next_block := bbName 0, next_stmt := 0, extra := () }
  mkMrMach (mkMrProg [(fnName 0, fn)]) [a0] [fr]

def c10ExpectedCapBytes : List Byte :=
  scalarBytes u32 7 ++ List.replicate 4 .Uninit ++ ptrBytes 256 (some (⟨1⟩, ()))

/-- Concrete C10 witnesses across Trusted, `Mach`, and `MachTB`:
1. 0-capture ZST closure (`[]`).
2. 2-capture `(u32(7), &raw const _1)` closure preserving scalar + provenance.
3. Dead-upvar UB propagation on the 2nd captured operand. -/
theorem c10_closure_zst_capture_and_ub_three_way_witness :
    runAVal c10ZstClosureMir 4 (initMachineState c10ZstClosureMir []) =
      some (.aggregate 0 []) ∧
    (∃ m1, Interp.step c10ZstMach = .ok m1 ∧
      m1.mem.memory.allocations[0]?.map (·.data) = some []) ∧
    (∃ m1, Interp.stepTB (liftMachToTB c10ZstMach) = .ok m1 ∧
      m1.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) = some []) ∧
    runAVal c10CapClosureMir 6 (initMachineState c10CapClosureMir [.scalar ⟨7, 4⟩]) =
      some (.aggregate 0 [.scalar ⟨7, 4⟩, .ptr { allocId := 1, offsetBytes := 0 } 8]) ∧
    (∃ m2, Interp.steps 2 (c10CapMach true) = .ok m2 ∧
      m2.mem.memory.allocations[0]?.map (·.data) = some c10ExpectedCapBytes) ∧
    (∃ m2, Interp.stepsTB 2 (liftMachToTB (c10CapMach true)) = .ok m2 ∧
      m2.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some (c10ExpectedCapBytes.map (projByteTB ∘ liftByteTB))) ∧
    stepMirFn c10CapClosureMir
      { frame := { blockIdx := 0, stmtIdx := 2,
                   locals := [.uninit, .init (.scalar ⟨7, 4⟩), .dead] }
        memory := (initMachineState c10CapClosureMir []).memory } = MirStepNode.fail .ub ∧
    Interp.step (c10CapMach false) = .error (.ub "access to a dead local") ∧
    Interp.stepTB (liftMachToTB (c10CapMach false)) = .error (.ub "access to a dead local") :=
  ⟨rfl,
   ok_of_map_toOption (by decide +kernel),
   ok_of_map_toOption (by decide +kernel),
   rfl,
   ok_of_map_toOption (by decide +kernel),
   ok_of_map_toOption (by decide +kernel),
   rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel)⟩

/-! ## §11. Exhaustive Axiom, Import-Isolation, & `Classical.choice`-Free Codec
Audit -/

section AxiomAudit

open Lean Elab Command

/-- Exhaustively verify that:
1. Every declaration defined in `MiniRustSpec.UnwindSetDiscrAndFnPtrMR`
   (`env.constants.map₂`) depends ONLY on Lean's standard axioms (`propext`,
   `Quot.sound`, `Classical.choice`) with zero `sorryAx` and zero
   `Lean.ofReduceBool` / `Lean.trustCompiler`.
2. The module import graph satisfies `MiniRustSpec` import isolation (zero
   `Anneal.*`, zero `DeinitBridge`, zero `IntrinsicBoundary` imports).
3. Core integer/pointer byte-codec and `transmuteM` theorems are strictly
   `Classical.choice`-free. -/
elab "#assert_unwind_setdiscr_mr_standard_axioms" : command => do
  let env ← getEnv
  for modName in env.header.moduleNames do
    if (`Anneal).isPrefixOf modName ||
        modName == `MiniRustSpec.Correspondence.DeinitBridge ||
        modName == `MiniRustSpec.Correspondence.IntrinsicBoundary then
      throwError "import-isolation violation: {modName} must not be imported"
  let mut checked : Nat := 0
  for (c, _) in env.constants.map₂.toList do
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then
        throwError "{c} depends on sorryAx"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    checked := checked + 1
  let choiceFreeCodecs : List Lean.Name :=
    [``encodePtrM_eq,
     ``decodePtrM_encodePtrBytesM,
     ``transmuteM_thinRawPtr_id,
     ``evalCastOpM_transmute_thinRawPtr_id,
     ``evalCastOp_transmute_thinRawPtr_id,
     ``encodeIntM_intFromBits,
     ``decodeIntM_leBytes,
     ``transmuteM_int_sameSize,
     ``transmuteM_u32_to_i32,
     ``transmuteM_u8_to_bool]
  for c in choiceFreeCodecs do
    let axs ← liftCoreM <| Lean.collectAxioms c
    if axs.contains ``Classical.choice then
      throwError "byte-codec theorem {c} unexpectedly depends on Classical.choice"
  logInfo m!"MiniRustSpec.UnwindSetDiscrAndFnPtrMR: verified standard axioms for {checked} declarations (sorry_free=true, import_isolated=true, choice_free_codecs={choiceFreeCodecs.length})"

#assert_unwind_setdiscr_mr_standard_axioms

end AxiomAudit

end MiniRustSpec.UnwindSetDiscrAndFnPtrMR
